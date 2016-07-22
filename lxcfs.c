/* lxcfs
 *
 * Copyright © 2014-2016 Canonical, Inc
 * Author: Serge Hallyn <serge.hallyn@ubuntu.com>
 *
 * See COPYING file for details.
 */

#define FUSE_USE_VERSION 26

#include <errno.h>
#include <dirent.h>
#include <dlfcn.h>
#include <fcntl.h>
#include <fuse.h>
#include <libgen.h>
#include <pthread.h>
#include <sched.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <wait.h>
#include <linux/sched.h>
#include <sys/epoll.h>
#include <sys/mount.h>
#include <sys/socket.h>
#include <sys/syscall.h>

#include "config.h" // for VERSION
#include "bindings.h"

/* Define pivot_root() if missing from the C library */
#ifndef HAVE_PIVOT_ROOT
static int pivot_root(const char * new_root, const char * put_old)
{
#ifdef __NR_pivot_root
return syscall(__NR_pivot_root, new_root, put_old);
#else
errno = ENOSYS;
return -1;
#endif
}
#else
extern int pivot_root(const char * new_root, const char * put_old);
#endif

/*
 * ns_fd[INIT_MNTNS]	--> initial       mnt ns
 * ns_fd[LXCFS_MNTNS]	--> private lxcfs mnt ns
 * active_ns		--> currently active mnt ns == one of ns_fd[MNT_NS_MAX]
 */
#define INIT_MNTNS 0
#define LXCFS_MNTNS 1
#define MNT_NS_MAX 2
static struct preserved_ns {
	int ns_fd[MNT_NS_MAX];
	int active_ns;
} preserved_ns = {
    .ns_fd = {-1, -1},
    .active_ns = -1,
};

// int preserved_ns[MNT_NS_MAX] = {-1, -1};

void *dlopen_handle;

/* Functions to keep track of number of threads using the library */

static int users_count;
static pthread_mutex_t user_count_mutex = PTHREAD_MUTEX_INITIALIZER;
static void lock_mutex(pthread_mutex_t *l)
{
	int ret;

	if ((ret = pthread_mutex_lock(l)) != 0) {
		fprintf(stderr, "pthread_mutex_lock returned:%d %s\n", ret, strerror(ret));
		exit(1);
	}
}

static void unlock_mutex(pthread_mutex_t *l)
{
	int ret;

	if ((ret = pthread_mutex_unlock(l)) != 0) {
		fprintf(stderr, "pthread_mutex_unlock returned:%d %s\n", ret, strerror(ret));
		exit(1);
	}
}

static void users_lock(void)
{
	lock_mutex(&user_count_mutex);
}

static void users_unlock(void)
{
	unlock_mutex(&user_count_mutex);
}

/*
 * Simple functions to preserve and switch mount namespaces.
 */

/* Close all open file descriptors refering to a namespace. */
static void close_ns(struct preserved_ns *ns) {
	int i;
	for (i = 0; i < MNT_NS_MAX; i++) {
		if (ns->ns_fd[i] > -1) {
			close(ns->ns_fd[i]);
			ns->ns_fd[i] = -1;
		}
	}
	ns->active_ns = -1;
}

/* Open /proc/PID/ns/mnt and save open fd to preserve the mount namespace.
 * if @is_caller_pid is set to true it is assumed that @pid is the callers pid
 * and that we are attached to the namespace identified by which_ns.
 */
static bool preserve_ns(struct preserved_ns *ns, int which_ns, int pid, bool is_caller_pid)
{
	int ret;
	size_t len = 5 /* /proc */ + 21 /* /int_as_str */ + 7 /* /ns/mnt */ + 1 /* \0 */;
	char path[len];

	ret = snprintf(path, len, "/proc/%d/ns/mnt", pid);
	if (ret < 0 || (size_t)ret >= len)
		return false;

	ns->ns_fd[which_ns] = open(path, O_RDONLY | O_CLOEXEC);
	if (ns->ns_fd[which_ns] < 0)
		goto error;

	if (is_caller_pid)
		ns->active_ns = ns->ns_fd[which_ns];

	return true;

error:
	close_ns(ns);
	return false;
}

/* Switch caller to namespace identified by the fd retrieved via @which_ns and
 * set the active namespace to the switched namespace. */
static bool switch_ns(struct preserved_ns *ns, int which_ns) {
	int ret = setns(ns->ns_fd[which_ns], 0);
	if (ret < 0)
		ns->active_ns = ns->ns_fd[which_ns] = ret;
	else
		ns->active_ns = ns->ns_fd[which_ns];

	return ret == 0;
}

/*
 * Functions and types used to reload dynamic library.
 */
static volatile sig_atomic_t need_reload;

/* do_reload - reload the dynamic library.  Done under
 * lock and when we know the user_count was 0 */
static void do_reload(struct preserved_ns *ns)
{
	if (ns->active_ns != -1) {
		if (ns->active_ns == ns->ns_fd[INIT_MNTNS])
			;
		else
			/* What do we want to do if switch_ns() fails here?
			 * Fail? */
			if (!switch_ns(ns, INIT_MNTNS))
				goto bad;
	}

	if (dlopen_handle)
		dlclose(dlopen_handle);

	/* First try loading using ld.so */
	dlopen_handle = dlopen("liblxcfs.so", RTLD_LAZY);
	if (dlopen_handle)
		goto good;

	dlopen_handle = dlopen("/usr/lib/lxcfs/liblxcfs.so", RTLD_LAZY);
	if (!dlopen_handle)
		goto bad;

good:
	if (need_reload)
		fprintf(stderr, "lxcfs: reloaded\n");
	if (ns->active_ns != -1)
		if (!switch_ns(ns, LXCFS_MNTNS))
			goto bad;
	need_reload = 0;
	return;

bad:
	fprintf(stderr, "Failed to open liblxcfs\n");
	_exit(1);
}

static void up_users(void)
{
	users_lock();
	if (users_count == 0 && need_reload)
		do_reload(&preserved_ns);
	users_count++;
	users_unlock();
}

static void down_users(void)
{
	users_lock();
	users_count--;
	users_unlock();
}

static void reload_handler(int sig)
{
	need_reload = 1;
}

/*
 * Functions to run the library methods.
 */
static int do_cg_getattr(const char *path, struct stat *sb)
{
	int (*cg_getattr)(const char *path, struct stat *sb);
	char *error;
	dlerror();    /* Clear any existing error */
	cg_getattr = (int (*)(const char *, struct stat *)) dlsym(dlopen_handle, "cg_getattr");
	error = dlerror();
	if (error != NULL) {
		fprintf(stderr, "cg_getattr: %s\n", error);
		return -1;
	}

	return cg_getattr(path, sb);
}

static int do_proc_getattr(const char *path, struct stat *sb)
{
	int (*proc_getattr)(const char *path, struct stat *sb);
	char *error;
	dlerror();    /* Clear any existing error */
	proc_getattr = (int (*)(const char *, struct stat *)) dlsym(dlopen_handle, "proc_getattr");
	error = dlerror();
	if (error != NULL) {
		fprintf(stderr, "proc_getattr: %s\n", error);
		return -1;
	}

	return proc_getattr(path, sb);
}

static int do_cg_read(const char *path, char *buf, size_t size, off_t offset,
		struct fuse_file_info *fi)
{
	int (*cg_read)(const char *path, char *buf, size_t size, off_t offset,
		struct fuse_file_info *fi);
	char *error;

	dlerror();    /* Clear any existing error */
	cg_read = (int (*)(const char *, char *, size_t, off_t, struct fuse_file_info *)) dlsym(dlopen_handle, "cg_read");
	error = dlerror();
	if (error != NULL) {
		fprintf(stderr, "cg_read: %s\n", error);
		return -1;
	}

	return cg_read(path, buf, size, offset, fi);
}

static int do_proc_read(const char *path, char *buf, size_t size, off_t offset,
		struct fuse_file_info *fi)
{
	int (*proc_read)(const char *path, char *buf, size_t size, off_t offset,
		struct fuse_file_info *fi);
	char *error;

	dlerror();    /* Clear any existing error */
	proc_read = (int (*)(const char *, char *, size_t, off_t, struct fuse_file_info *)) dlsym(dlopen_handle, "proc_read");
	error = dlerror();
	if (error != NULL) {
		fprintf(stderr, "proc_read: %s\n", error);
		return -1;
	}

	return proc_read(path, buf, size, offset, fi);
}

static int do_cg_write(const char *path, const char *buf, size_t size, off_t offset,
	     struct fuse_file_info *fi)
{
	int (*cg_write)(const char *path, const char *buf, size_t size, off_t offset,
	     struct fuse_file_info *fi);
	char *error;
	dlerror();    /* Clear any existing error */
	cg_write = (int (*)(const char *, const char *, size_t, off_t, struct fuse_file_info *)) dlsym(dlopen_handle, "cg_write");
	error = dlerror();
	if (error != NULL) {
		fprintf(stderr, "cg_write: %s\n", error);
		return -1;
	}

	return cg_write(path, buf, size, offset, fi);
}

static int do_cg_mkdir(const char *path, mode_t mode)
{
	int (*cg_mkdir)(const char *path, mode_t mode);
	char *error;
	dlerror();    /* Clear any existing error */
	cg_mkdir = (int (*)(const char *, mode_t)) dlsym(dlopen_handle, "cg_mkdir");
	error = dlerror();
	if (error != NULL) {
		fprintf(stderr, "cg_mkdir: %s\n", error);
		return -1;
	}

	return cg_mkdir(path, mode);
}

static int do_cg_chown(const char *path, uid_t uid, gid_t gid)
{
	int (*cg_chown)(const char *path, uid_t uid, gid_t gid);
	char *error;
	dlerror();    /* Clear any existing error */
	cg_chown = (int (*)(const char *, uid_t, gid_t)) dlsym(dlopen_handle, "cg_chown");
	error = dlerror();
	if (error != NULL) {
		fprintf(stderr, "cg_chown: %s\n", error);
		return -1;
	}

	return cg_chown(path, uid, gid);
}

static int do_cg_rmdir(const char *path)
{
	int (*cg_rmdir)(const char *path);
	char *error;
	dlerror();    /* Clear any existing error */
	cg_rmdir = (int (*)(const char *path)) dlsym(dlopen_handle, "cg_rmdir");
	error = dlerror();
	if (error != NULL) {
		fprintf(stderr, "cg_rmdir: %s\n", error);
		return -1;
	}

	return cg_rmdir(path);
}

static int do_cg_chmod(const char *path, mode_t mode)
{
	int (*cg_chmod)(const char *path, mode_t mode);
	char *error;
	dlerror();    /* Clear any existing error */
	cg_chmod = (int (*)(const char *, mode_t)) dlsym(dlopen_handle, "cg_chmod");
	error = dlerror();
	if (error != NULL) {
		fprintf(stderr, "cg_chmod: %s\n", error);
		return -1;
	}

	return cg_chmod(path, mode);
}

static int do_cg_readdir(const char *path, void *buf, fuse_fill_dir_t filler, off_t offset,
		struct fuse_file_info *fi)
{
	int (*cg_readdir)(const char *path, void *buf, fuse_fill_dir_t filler, off_t offset,
		struct fuse_file_info *fi);
	char *error;

	dlerror();    /* Clear any existing error */
	cg_readdir = (int (*)(const char *, void *, fuse_fill_dir_t, off_t, struct fuse_file_info *)) dlsym(dlopen_handle, "cg_readdir");
	error = dlerror();
	if (error != NULL) {
		fprintf(stderr, "cg_readdir: %s\n", error);
		return -1;
	}

	return cg_readdir(path, buf, filler, offset, fi);
}

static int do_proc_readdir(const char *path, void *buf, fuse_fill_dir_t filler, off_t offset,
		struct fuse_file_info *fi)
{
	int (*proc_readdir)(const char *path, void *buf, fuse_fill_dir_t filler, off_t offset,
		struct fuse_file_info *fi);
	char *error;

	dlerror();    /* Clear any existing error */
	proc_readdir = (int (*)(const char *, void *, fuse_fill_dir_t, off_t, struct fuse_file_info *)) dlsym(dlopen_handle, "proc_readdir");
	error = dlerror();
	if (error != NULL) {
		fprintf(stderr, "proc_readdir: %s\n", error);
		return -1;
	}

	return proc_readdir(path, buf, filler, offset, fi);
}

static int do_cg_open(const char *path, struct fuse_file_info *fi)
{
	int (*cg_open)(const char *path, struct fuse_file_info *fi);
	char *error;
	dlerror();    /* Clear any existing error */
	cg_open = (int (*)(const char *, struct fuse_file_info *)) dlsym(dlopen_handle, "cg_open");
	error = dlerror();
	if (error != NULL) {
		fprintf(stderr, "cg_open: %s\n", error);
		return -1;
	}

	return cg_open(path, fi);
}

static int do_cg_access(const char *path, int mode)
{
	int (*cg_access)(const char *path, int mode);
	char *error;
	dlerror();    /* Clear any existing error */
	cg_access = (int (*)(const char *, int mode)) dlsym(dlopen_handle, "cg_access");
	error = dlerror();
	if (error != NULL) {
		fprintf(stderr, "cg_access: %s\n", error);
		return -1;
	}

	return cg_access(path, mode);
}

static int do_proc_open(const char *path, struct fuse_file_info *fi)
{
	int (*proc_open)(const char *path, struct fuse_file_info *fi);
	char *error;
	dlerror();    /* Clear any existing error */
	proc_open = (int (*)(const char *path, struct fuse_file_info *fi)) dlsym(dlopen_handle, "proc_open");
	error = dlerror();
	if (error != NULL) {
		fprintf(stderr, "proc_open: %s\n", error);
		return -1;
	}

	return proc_open(path, fi);
}

static int do_proc_access(const char *path, int mode)
{
	int (*proc_access)(const char *path, int mode);
	char *error;
	dlerror();    /* Clear any existing error */
	proc_access = (int (*)(const char *, int mode)) dlsym(dlopen_handle, "proc_access");
	error = dlerror();
	if (error != NULL) {
		fprintf(stderr, "proc_access: %s\n", error);
		return -1;
	}

	return proc_access(path, mode);
}

static int do_cg_release(const char *path, struct fuse_file_info *fi)
{
	int (*cg_release)(const char *path, struct fuse_file_info *fi);
	char *error;
	dlerror();    /* Clear any existing error */
	cg_release = (int (*)(const char *path, struct fuse_file_info *)) dlsym(dlopen_handle, "cg_release");
	error = dlerror();
	if (error != NULL) {
		fprintf(stderr, "cg_release: %s\n", error);
		return -1;
	}

	return cg_release(path, fi);
}

static int do_proc_release(const char *path, struct fuse_file_info *fi)
{
	int (*proc_release)(const char *path, struct fuse_file_info *fi);
	char *error;
	dlerror();    /* Clear any existing error */
	proc_release = (int (*)(const char *path, struct fuse_file_info *)) dlsym(dlopen_handle, "proc_release");
	error = dlerror();
	if (error != NULL) {
		fprintf(stderr, "proc_release: %s\n", error);
		return -1;
	}

	return proc_release(path, fi);
}

static int do_cg_opendir(const char *path, struct fuse_file_info *fi)
{
	int (*cg_opendir)(const char *path, struct fuse_file_info *fi);
	char *error;
	dlerror();    /* Clear any existing error */
	cg_opendir = (int (*)(const char *path, struct fuse_file_info *fi)) dlsym(dlopen_handle, "cg_opendir");
	error = dlerror();
	if (error != NULL) {
		fprintf(stderr, "cg_opendir: %s\n", error);
		return -1;
	}

	return cg_opendir(path, fi);
}

static int do_cg_releasedir(const char *path, struct fuse_file_info *fi)
{
	int (*cg_releasedir)(const char *path, struct fuse_file_info *fi);
	char *error;
	dlerror();    /* Clear any existing error */
	cg_releasedir = (int (*)(const char *path, struct fuse_file_info *)) dlsym(dlopen_handle, "cg_releasedir");
	error = dlerror();
	if (error != NULL) {
		fprintf(stderr, "cg_releasedir: %s\n", error);
		return -1;
	}

	return cg_releasedir(path, fi);
}

/*
 * FUSE ops for /
 * these just delegate to the /proc and /cgroup ops as
 * needed
 */

static int lxcfs_getattr(const char *path, struct stat *sb)
{
	int ret;
	if (strcmp(path, "/") == 0) {
		sb->st_mode = S_IFDIR | 00755;
		sb->st_nlink = 2;
		return 0;
	}
	if (strncmp(path, "/cgroup", 7) == 0) {
		up_users();
		ret = do_cg_getattr(path, sb);
		down_users();
		return ret;
	}
	if (strncmp(path, "/proc", 5) == 0) {
		up_users();
		ret = do_proc_getattr(path, sb);
		down_users();
		return ret;
	}
	return -EINVAL;
}

static int lxcfs_opendir(const char *path, struct fuse_file_info *fi)
{
	int ret;
	if (strcmp(path, "/") == 0)
		return 0;

	if (strncmp(path, "/cgroup", 7) == 0) {
		up_users();
		ret = do_cg_opendir(path, fi);
		down_users();
		return ret;
	}
	if (strcmp(path, "/proc") == 0)
		return 0;
	return -ENOENT;
}

static int lxcfs_readdir(const char *path, void *buf, fuse_fill_dir_t filler, off_t offset,
		struct fuse_file_info *fi)
{
	int ret;
	if (strcmp(path, "/") == 0) {
		if (filler(buf, "proc", NULL, 0) != 0 ||
				filler(buf, "cgroup", NULL, 0) != 0)
			return -EINVAL;
		return 0;
	}
	if (strncmp(path, "/cgroup", 7) == 0) {
		up_users();
		ret = do_cg_readdir(path, buf, filler, offset, fi);
		down_users();
		return ret;
	}
	if (strcmp(path, "/proc") == 0) {
		up_users();
		ret = do_proc_readdir(path, buf, filler, offset, fi);
		down_users();
		return ret;
	}
	return -EINVAL;
}

static int lxcfs_access(const char *path, int mode)
{
	int ret;
	if (strncmp(path, "/cgroup", 7) == 0) {
		up_users();
		ret = do_cg_access(path, mode);
		down_users();
		return ret;
	}
	if (strncmp(path, "/proc", 5) == 0) {
		up_users();
		ret = do_proc_access(path, mode);
		down_users();
		return ret;
	}

	return -EINVAL;
}

static int lxcfs_releasedir(const char *path, struct fuse_file_info *fi)
{
	int ret;
	if (strcmp(path, "/") == 0)
		return 0;
	if (strncmp(path, "/cgroup", 7) == 0) {
		up_users();
		ret = do_cg_releasedir(path, fi);
		down_users();
		return ret;
	}
	if (strcmp(path, "/proc") == 0)
		return 0;
	return -EINVAL;
}

static int lxcfs_open(const char *path, struct fuse_file_info *fi)
{
	int ret;
	if (strncmp(path, "/cgroup", 7) == 0) {
		up_users();
		ret = do_cg_open(path, fi);
		down_users();
		return ret;
	}
	if (strncmp(path, "/proc", 5) == 0) {
		up_users();
		ret = do_proc_open(path, fi);
		down_users();
		return ret;
	}

	return -EINVAL;
}

static int lxcfs_read(const char *path, char *buf, size_t size, off_t offset,
		struct fuse_file_info *fi)
{
	int ret;
	if (strncmp(path, "/cgroup", 7) == 0) {
		up_users();
		ret = do_cg_read(path, buf, size, offset, fi);
		down_users();
		return ret;
	}
	if (strncmp(path, "/proc", 5) == 0) {
		up_users();
		ret = do_proc_read(path, buf, size, offset, fi);
		down_users();
		return ret;
	}

	return -EINVAL;
}

int lxcfs_write(const char *path, const char *buf, size_t size, off_t offset,
	     struct fuse_file_info *fi)
{
	int ret;
	if (strncmp(path, "/cgroup", 7) == 0) {
		up_users();
		ret = do_cg_write(path, buf, size, offset, fi);
		down_users();
		return ret;
	}

	return -EINVAL;
}

static int lxcfs_flush(const char *path, struct fuse_file_info *fi)
{
	return 0;
}

static int lxcfs_release(const char *path, struct fuse_file_info *fi)
{
	int ret;
	if (strncmp(path, "/cgroup", 7) == 0) {
		up_users();
		ret = do_cg_release(path, fi);
		down_users();
		return ret;
	}
	if (strncmp(path, "/proc", 5) == 0) {
		up_users();
		ret = do_proc_release(path, fi);
		down_users();
		return ret;
	}

	return -EINVAL;
}

static int lxcfs_fsync(const char *path, int datasync, struct fuse_file_info *fi)
{
	return 0;
}

int lxcfs_mkdir(const char *path, mode_t mode)
{
	int ret;
	if (strncmp(path, "/cgroup", 7) == 0) {
		up_users();
		ret = do_cg_mkdir(path, mode);
		down_users();
		return ret;
	}

	return -EINVAL;
}

int lxcfs_chown(const char *path, uid_t uid, gid_t gid)
{
	int ret;
	if (strncmp(path, "/cgroup", 7) == 0) {
		up_users();
		ret = do_cg_chown(path, uid, gid);
		down_users();
		return ret;
	}

	return -EINVAL;
}

/*
 * cat first does a truncate before doing ops->write.  This doesn't
 * really make sense for cgroups.  So just return 0 always but do
 * nothing.
 */
int lxcfs_truncate(const char *path, off_t newsize)
{
	if (strncmp(path, "/cgroup", 7) == 0)
		return 0;
	return -EINVAL;
}

int lxcfs_rmdir(const char *path)
{
	int ret;
	if (strncmp(path, "/cgroup", 7) == 0) {
		up_users();
		ret = do_cg_rmdir(path);
		down_users();
		return ret;
	}
	return -EINVAL;
}

int lxcfs_chmod(const char *path, mode_t mode)
{
	int ret;
	if (strncmp(path, "/cgroup", 7) == 0) {
		up_users();
		ret = do_cg_chmod(path, mode);
		down_users();
		return ret;
	}
	return -EINVAL;
}

const struct fuse_operations lxcfs_ops = {
	.getattr = lxcfs_getattr,
	.readlink = NULL,
	.getdir = NULL,
	.mknod = NULL,
	.mkdir = lxcfs_mkdir,
	.unlink = NULL,
	.rmdir = lxcfs_rmdir,
	.symlink = NULL,
	.rename = NULL,
	.link = NULL,
	.chmod = lxcfs_chmod,
	.chown = lxcfs_chown,
	.truncate = lxcfs_truncate,
	.utime = NULL,

	.open = lxcfs_open,
	.read = lxcfs_read,
	.release = lxcfs_release,
	.write = lxcfs_write,

	.statfs = NULL,
	.flush = lxcfs_flush,
	.fsync = lxcfs_fsync,

	.setxattr = NULL,
	.getxattr = NULL,
	.listxattr = NULL,
	.removexattr = NULL,

	.opendir = lxcfs_opendir,
	.readdir = lxcfs_readdir,
	.releasedir = lxcfs_releasedir,

	.fsyncdir = NULL,
	.init = NULL,
	.destroy = NULL,
	.access = lxcfs_access,
	.create = NULL,
	.ftruncate = NULL,
	.fgetattr = NULL,
};

static void usage(const char *me)
{
	fprintf(stderr, "Usage:\n");
	fprintf(stderr, "\n");
	fprintf(stderr, "%s [-p pidfile] mountpoint\n", me);
	fprintf(stderr, "  Default pidfile is %s/lxcfs.pid\n", RUNTIME_PATH);
	fprintf(stderr, "%s -h\n", me);
	exit(1);
}

static bool is_help(char *w)
{
	if (strcmp(w, "-h") == 0 ||
			strcmp(w, "--help") == 0 ||
			strcmp(w, "-help") == 0 ||
			strcmp(w, "help") == 0)
		return true;
	return false;
}

void swallow_arg(int *argcp, char *argv[], char *which)
{
	int i;

	for (i = 1; argv[i]; i++) {
		if (strcmp(argv[i], which) != 0)
			continue;
		for (; argv[i]; i++) {
			argv[i] = argv[i+1];
		}
		(*argcp)--;
		return;
	}
}

bool swallow_option(int *argcp, char *argv[], char *opt, char **v)
{
	int i;

	for (i = 1; argv[i]; i++) {
		if (!argv[i+1])
			continue;
		if (strcmp(argv[i], opt) != 0)
			continue;
		do {
			*v = strdup(argv[i+1]);
		} while (!*v);
		for (; argv[i+1]; i++) {
			argv[i] = argv[i+2];
		}
		(*argcp) -= 2;
		return true;
	}
	return false;
}

static bool mkdir_p(const char *dir, mode_t mode)
{
	const char *tmp = dir;
	const char *orig = dir;
	char *makeme;

	do {
		dir = tmp + strspn(tmp, "/");
		tmp = dir + strcspn(dir, "/");
		makeme = strndup(orig, dir - orig);
		if (!makeme)
			return false;
		if (mkdir(makeme, mode) && errno != EEXIST) {
			fprintf(stderr, "failed to create directory '%s': %s",
				makeme, strerror(errno));
			free(makeme);
			return false;
		}
		free(makeme);
	} while(tmp != dir);

	return true;
}

static bool umount_if_mounted(void)
{
	if (umount2(BASEDIR, MNT_DETACH) < 0 && errno != EINVAL) {
		fprintf(stderr, "failed to umount %s: %s\n", BASEDIR,
			strerror(errno));
		return false;
	}
	return true;
}

static bool setup_cgfs_dir(void)
{
	if (!mkdir_p(BASEDIR, 0700)) {
		fprintf(stderr, "Failed to create lxcfs cgdir\n");
		return false;
	}
	if (!umount_if_mounted()) {
		fprintf(stderr, "Failed to clean up old lxcfs cgdir\n");
		return false;
	}
	if (mount("tmpfs", BASEDIR, "tmpfs", 0, "size=100000,mode=700") < 0) {
		fprintf(stderr, "Failed to mount tmpfs for private controllers\n");
		return false;
	}
	return true;
}

static bool do_mount_cgroup(char *controller)
{
	char *target;
	size_t len;
	int ret;

	len = strlen(BASEDIR) + strlen(controller) + 2;
	target = alloca(len);
	ret = snprintf(target, len, "%s/%s", BASEDIR, controller);
	if (ret < 0 || ret >= len)
		return false;
	if (mkdir(target, 0755) < 0 && errno != EEXIST)
		return false;
	if (mount(controller, target, "cgroup", 0, controller) < 0) {
		fprintf(stderr, "Failed mounting cgroup %s\n", controller);
		return false;
	}
	return true;
}

static int pivot_enter(void) {
	int oldroot = -1, newroot = -1;

	oldroot = open("/", O_DIRECTORY | O_RDONLY);
	if (oldroot < 0) {
		fprintf(stderr, "%s: Failed to open old root for fchdir.\n", __func__);
		return -1;
	}

	newroot = open(ROOTDIR, O_DIRECTORY | O_RDONLY);
	if (newroot < 0) {
		fprintf(stderr, "%s: Failed to open new root for fchdir.\n", __func__);
		goto err;
	}

	/* change into new root fs */
	if (fchdir(newroot)) {
		fprintf(stderr, "%s: Failed to change directory to new rootfs: %s.\n", __func__, ROOTDIR);
		goto err;
	}

	/* pivot_root into our new root fs */
	if (pivot_root(".", ".")) {
		fprintf(stderr, "%s: pivot_root() syscall failed: %s.\n", __func__, strerror(errno));
		goto err;
	}

	/*
	 * At this point the old-root is mounted on top of our new-root.
	 * To unmounted it we must not be chdir'd into it, so escape back
	 * to the old-root.
	 */
	if (fchdir(oldroot) < 0) {
		fprintf(stderr, "%s: Failed to enter old root.\n", __func__);
		goto err;
	}
	if (umount2(".", MNT_DETACH) < 0) {
		fprintf(stderr, "%s: Failed to detach old root.\n", __func__);
		goto err;
	}

	if (fchdir(newroot) < 0) {
		fprintf(stderr, "%s: Failed to re-enter new root.\n", __func__);
		goto err;
	}

	close(oldroot);
	close(newroot);
	return 0;

err:
	if (oldroot != -1)
		close(oldroot);
	if (newroot != -1)
		close(newroot);
	return -1;
}

/*
 * Prepare our new root: We need to mount everything that fuse needs to
 * correctly work in our minimal chroot:
 *	- /var/lib/lxcfs		<-- the fuse mount
 *	- /dev				<-- because of /dev/fuse
 * 	- /sys				<-- because we want to mount /sys/fs/connections/fuse
 * 	- /sys/fs/connections/fuse	<-- because of fuse
 * 	- /proc				<-- where we read info from
 * (Is that all we need? Did we not pin any unnecessary mounts?)
 */
static int pivot_prepare(void)
{
	if (mkdir(ROOTDIR, 0755) < 0 && errno != EEXIST) {
		fprintf(stderr, "%s: Failed to create directory for new root.\n", __func__);
		return -1;
	}

	if (mount("/", ROOTDIR, NULL, MS_BIND, 0) < 0) {
		fprintf(stderr, "%s: Failed to bind-mount / for new root: %s.\n", __func__, strerror(errno));
		return -1;
	}

	if (mount("/proc", ROOTDIR "/proc", NULL, MS_REC|MS_MOVE, 0) < 0) {
		fprintf(stderr, "%s: Failed to move /proc into new root: %s.\n", __func__, strerror(errno));
		return -1;
	}

	if (mount(RUNTIME_PATH, ROOTDIR RUNTIME_PATH, NULL, MS_BIND, 0) < 0) {
		fprintf(stderr, "%s: Failed to bind-mount /run into new root: %s.\n", __func__, strerror(errno));
		return -1;
	}

	if (mount("/dev", ROOTDIR "/dev", NULL, MS_BIND, 0) < 0) {
		printf("%s: Failed to bind-mount /dev into new root: %s.\n", __func__, strerror(errno));
		return -1;
	}

	if (mount("/sys", ROOTDIR "/sys", NULL, MS_BIND, 0) < 0) {
		printf("%s: failed to bind-mount /sys into new root: %s.\n", __func__, strerror(errno));
		return -1;
	}

	if (mount("/sys/fs/fuse/connections", ROOTDIR "/sys/fs/fuse/connections", NULL, MS_BIND, 0) < 0) {
		printf("%s: failed to bind-mount /sys/fs/fuse/connections into new root: %s.\n", __func__, strerror(errno));
		return -1;
	}

	if (mount(BASEDIR, ROOTDIR BASEDIR, NULL, MS_REC|MS_MOVE, 0) < 0) {
		printf("%s: failed to move " BASEDIR " into new root: %s.\n", __func__, strerror(errno));
		return -1;
	}

	return 0;
}

static int pivot_new_root(void)
{
	/* Prepare new root. */
	if (pivot_prepare() < 0)
		return -1;

	/* Pivot into new root. */
	if (pivot_enter() < 0)
		return -1;

	return 0;
}

static bool do_mount_cgroups(void)
{
	bool ret = false;
	FILE *f;
	char *line = NULL;
	size_t len = 0;

	if ((f = fopen("/proc/self/cgroup", "r")) == NULL) {
		fprintf(stderr, "Error opening /proc/self/cgroup: %s\n", strerror(errno));
		return false;
	}

	while (getline(&line, &len, f) != -1) {
		char *p, *p2;

		p = strchr(line, ':');
		if (!p)
			goto out;
		*(p++) = '\0';

		p2 = strrchr(p, ':');
		if (!p2)
			goto out;
		*p2 = '\0';

		/* With cgroupv2 /proc/self/cgroup can contain entries of the
		 * form: 0::/ This will cause lxcfs to fail the cgroup mounts
		 * because it parses out the empty string "" and later on passes
		 * it to mount(). Let's skip such entries.
		 */
		if (!strcmp(p, ""))
			continue;

		if (!do_mount_cgroup(p))
			goto out;
	}

	if (pivot_new_root() < 0)
		goto out;

	ret = true;

out:
	free(line);
	fclose(f);
	return ret;
}

static bool cgfs_setup_controllers(void)
{
	if (!setup_cgfs_dir()) {
		return false;
	}

	if (!do_mount_cgroups()) {
		fprintf(stderr, "Failed to set up cgroup mounts\n");
		return false;
	}

	return true;
}

static int set_pidfile(char *pidfile)
{
	int fd;
	char buf[50];
	struct flock fl;

	fl.l_type = F_WRLCK;
	fl.l_whence = SEEK_SET;
	fl.l_start = 0;
	fl.l_len = 0;

	fd = open(pidfile, O_RDWR | O_CREAT, S_IRUSR | S_IWUSR);
	if (fd == -1) {
		fprintf(stderr, "Could not open pidfile %s: %m", pidfile);
		return -1;
	}

	if (fcntl(fd, F_SETLK, &fl) == -1) {
		if (errno  == EAGAIN || errno == EACCES) {
			fprintf(stderr, "PID file '%s' is already locked.\n", pidfile);
			close(fd);
			return -1;
		}
		fprintf(stderr, "Warning; unable to lock PID file, proceeding.\n");
	}

	if (ftruncate(fd, 0) == -1) {
		fprintf(stderr, "Error truncating PID file '%s': %m", pidfile);
		close(fd);
		return -1;
	}

	snprintf(buf, 50, "%ld\n", (long) getpid());
	if (write(fd, buf, strlen(buf)) != strlen(buf)) {
		fprintf(stderr, "Error writing to PID file '%s': %m", pidfile);
		close(fd);
		return -1;
	}

	return fd;
}

static struct fuse *fuse_prepare(int argc, char *argv[],
				 const struct fuse_operations *op,
				 size_t op_size, char **mountpoint,
				 int *multithreaded, void *user_data)
{
	struct fuse_args args = FUSE_ARGS_INIT(argc, argv);
	struct fuse_chan *ch;
	struct fuse *fuse = NULL;
	int foreground;
	int res;

	res = fuse_parse_cmdline(&args, mountpoint, multithreaded, &foreground);
	if (res == -1)
		return NULL;

	ch = fuse_mount(*mountpoint, &args);
	if (!ch) {
		fuse_opt_free_args(&args);
		goto err_free;
	}

	/* Switch to new mount namespace for lxcfs and setup private mounts for
	 * fuse.
	 */
	if (unshare(CLONE_NEWNS) < 0) {
		fprintf(stderr, "%s: Failed to unshare the mount namespace: %s.\n", __func__, strerror(errno));
		goto err_free;
	}

	if (mount(NULL, "/", NULL, MS_REC|MS_PRIVATE, 0) < 0) {
		fprintf(stderr, "%s: Failed to re-mount / private: %s.\n", __func__, strerror(errno));
		goto err_free;
	}

	/* Preserve lxcfs private mount namespace so we can switch to it when we
	 * need to.
	 */
	if (!preserve_ns(&preserved_ns, LXCFS_MNTNS, getpid(), true))
		goto err_unmount;

	if (!cgfs_setup_controllers())
		goto err_unmount;

	fuse = fuse_new(ch, &args, op, op_size, user_data);
	fuse_opt_free_args(&args);
	if (fuse == NULL)
		goto err_unmount;

	res = fuse_daemonize(foreground);
	if (res == -1)
		goto err_unmount;

	res = fuse_set_signal_handlers(fuse_get_session(fuse));
	if (res == -1)
		goto err_unmount;

	return fuse;

err_unmount:
	/* fuse_umount() should be done in the initial mount namespace because
	 * we did our fuse_mount() there. So attach back to host ns here. We do
	 * not check for error since we can't do anything anyway if it fails.
	 * TODO: What should we do if we fail? (Probably nothing.(?))
	 */
	(void)switch_ns(&preserved_ns, INIT_MNTNS);

	fuse_unmount(*mountpoint, ch);
	if (fuse)
		fuse_destroy(fuse);
err_free:
	free(*mountpoint);
	return NULL;
}

int fuse_init(int argc, char *argv[], const struct fuse_operations *op,
	      size_t op_size, void *user_data)
{
	struct fuse *fuse;
	char *mountpoint;
	int multithreaded;
	int res;

	/* We are in our private mount namespace here! */
	fuse = fuse_prepare(argc, argv, op, op_size, &mountpoint,
			    &multithreaded, user_data);
	if (fuse == NULL)
		return -1;

	if (multithreaded)
		res = fuse_loop_mt(fuse);
	else
		res = fuse_loop(fuse);

	/* fuse_teardown() should be done in the initial mount namespace because
	 * we did fuse_new() + fuse_mount() there. So attach back to the initial
	 * mount namespace here. We do not check for error since we can't do
	 * anything anyway if it fails.
	 */
	(void)switch_ns(&preserved_ns, INIT_MNTNS);

	fuse_teardown(fuse, mountpoint);
	if (res == -1)
		return -1;

	return 0;
}

/* Note that lxcfs creates a private mount namespace (actually rather a minimal
 * chroot) to hide its cgroup mounts under BASEDIR/ from other processes that
 * would get confused by it. However, the fuse mount usually placed under
 * /var/lib/lxcfs (or whatever the user gives us via argv[1]) needs to be
 * visible in the initial namespace.
 * Hence, we place these mounts in different namespaces. This requires some
 * coordination. fuse_mount() needs to be called in the initial namespace.
 * Afterwards we can unshare(CLONE_NEWNS), setup the cgroup mounts and create
 * our minimal chroot. On failure we need to switch back to the initial
 * mount namespace or fuse_umount() to succeed.
 * Also, when we are asked to reload our dynamic library, we also need to switch
 * to the initial mount namespace.
 */
int main(int argc, char *argv[])
{
	int ret = -1, pidfd;
	char *pidfile = NULL, *v = NULL;
	size_t pidfile_len;
	/*
	 * what we pass to fuse_main is:
	 * argv[0] -s -f -o allow_other,directio argv[1] NULL
	 */
	int nargs = 5, cnt = 0;
	char *newargv[6];

	/* accomodate older init scripts */
	swallow_arg(&argc, argv, "-s");
	swallow_arg(&argc, argv, "-f");
	if (swallow_option(&argc, argv, "-o", &v)) {
		if (strcmp(v, "allow_other") != 0) {
			fprintf(stderr, "Warning: unexpected fuse option %s\n", v);
			exit(1);
		}
		free(v);
		v = NULL;
	}
	if (swallow_option(&argc, argv, "-p", &v))
		pidfile = v;

	if (argc == 2  && strcmp(argv[1], "--version") == 0) {
		fprintf(stderr, "%s\n", VERSION);
		exit(0);
	}
	if (argc != 2 || is_help(argv[1]))
		usage(argv[0]);

	do_reload(&preserved_ns);
	if (signal(SIGUSR1, reload_handler) == SIG_ERR) {
		fprintf(stderr, "Error setting USR1 signal handler: %m\n");
		exit(1);
	}

	newargv[cnt++] = argv[0];
	newargv[cnt++] = "-f";
	newargv[cnt++] = "-o";
	newargv[cnt++] = "allow_other,direct_io,entry_timeout=0.5,attr_timeout=0.5";
	newargv[cnt++] = argv[1];
	newargv[cnt++] = NULL;

	if (!pidfile) {
		pidfile_len = strlen(RUNTIME_PATH) + strlen("/lxcfs.pid") + 1;
		pidfile = alloca(pidfile_len);
		snprintf(pidfile, pidfile_len, "%s/lxcfs.pid", RUNTIME_PATH);
	}
	if ((pidfd = set_pidfile(pidfile)) < 0)
		goto out;

	/* Preserve initial mount namespace so we can switch to it when we need
	 * to (For example, when we reload our dynamic library.).
	 */
	if (!preserve_ns(&preserved_ns, INIT_MNTNS, getpid(), true))
		goto out;

	ret = fuse_init(nargs, newargv, &lxcfs_ops, sizeof(lxcfs_ops), NULL);

	dlclose(dlopen_handle);
	unlink(pidfile);
	close(pidfd);

out:
	return ret;
}
