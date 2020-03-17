/* SPDX-License-Identifier: LGPL-2.1+ */

#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif

#ifndef FUSE_USE_VERSION
#define FUSE_USE_VERSION 26
#endif

#define _FILE_OFFSET_BITS 64

#include <errno.h>
#include <fcntl.h>
#include <fuse.h>
#include <inttypes.h>
#include <sched.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/epoll.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

#include "bindings.h"
#include "config.h"
#include "macro.h"
#include "memory_utils.h"
#include "utils.h"

/*
 * append the given formatted string to *src.
 * src: a pointer to a char* in which to append the formatted string.
 * sz: the number of characters printed so far, minus trailing \0.
 * asz: the allocated size so far
 * format: string format. See printf for details.
 * ...: varargs. See printf for details.
 */
/*
 * append the given formatted string to *src.
 * src: a pointer to a char* in which to append the formatted string.
 * sz: the number of characters printed so far, minus trailing \0.
 * asz: the allocated size so far
 * format: string format. See printf for details.
 * ...: varargs. See printf for details.
 */
char *must_strcat(char **src, size_t *sz, size_t *asz, const char *format, ...)
{
	char tmp[BUF_RESERVE_SIZE];
	va_list args;
	int tmplen;

	va_start (args, format);
	tmplen = vsnprintf(tmp, BUF_RESERVE_SIZE, format, args);
	va_end(args);

	if (!*src || tmplen + *sz + 1 >= *asz) {
		char *str;
		do {
			str = realloc(*src, *asz + BUF_RESERVE_SIZE);
		} while (!str);
		*src = str;
		*asz += BUF_RESERVE_SIZE;
	}
	memcpy((*src) +*sz , tmp, tmplen+1); /* include the \0 */
	*sz += tmplen;

	return *src;
}

/**
 * in_same_namespace - Check whether two processes are in the same namespace.
 * @pid1 - PID of the first process.
 * @pid2 - PID of the second process.
 * @ns   - Name of the namespace to check. Must correspond to one of the names
 *         for the namespaces as shown in /proc/<pid/ns/
 *
 * If the two processes are not in the same namespace returns an fd to the
 * namespace of the second process identified by @pid2. If the two processes are
 * in the same namespace returns -EINVAL, -1 if an error occurred.
 */
static int in_same_namespace(pid_t pid1, pid_t pid2, const char *ns)
{
	__do_close int ns_fd1 = -1, ns_fd2 = -1;
	int ret = -1;
	struct stat ns_st1, ns_st2;

	ns_fd1 = preserve_ns(pid1, ns);
	if (ns_fd1 < 0) {
		/* The kernel does not support this namespace. This is not an
		 * error.
		 */
		if (errno == ENOENT)
			return -EINVAL;

		return -1;
	}

	ns_fd2 = preserve_ns(pid2, ns);
	if (ns_fd2 < 0)
		return -1;

	ret = fstat(ns_fd1, &ns_st1);
	if (ret < 0)
		return -1;

	ret = fstat(ns_fd2, &ns_st2);
	if (ret < 0)
		return -1;

	/* processes are in the same namespace */
	if ((ns_st1.st_dev == ns_st2.st_dev) && (ns_st1.st_ino == ns_st2.st_ino))
		return -EINVAL;

	/* processes are in different namespaces */
	return move_fd(ns_fd2);
}

bool is_shared_pidns(pid_t pid)
{
	if (pid != 1)
		return false;

	if (in_same_namespace(pid, getpid(), "pid") == -EINVAL)
		return true;

	return false;
}

int preserve_ns(const int pid, const char *ns)
{
	int ret;
/* 5 /proc + 21 /int_as_str + 3 /ns + 20 /NS_NAME + 1 \0 */
#define __NS_PATH_LEN 50
	char path[__NS_PATH_LEN];

	/* This way we can use this function to also check whether namespaces
	 * are supported by the kernel by passing in the NULL or the empty
	 * string.
	 */
	ret = snprintf(path, __NS_PATH_LEN, "/proc/%d/ns%s%s", pid,
		       !ns || strcmp(ns, "") == 0 ? "" : "/",
		       !ns || strcmp(ns, "") == 0 ? "" : ns);
	if (ret < 0 || (size_t)ret >= __NS_PATH_LEN) {
		errno = EFBIG;
		return -1;
	}

	return open(path, O_RDONLY | O_CLOEXEC);
}

void do_release_file_info(struct fuse_file_info *fi)
{
	struct file_info *f;

	f = INTTYPE_TO_PTR(fi->fh);
	if (!f)
		return;

	fi->fh = 0;

	free_disarm(f->controller);
	free_disarm(f->cgroup);
	free_disarm(f->file);
	free_disarm(f->buf);
	free_disarm(f);
}

#define POLLIN_SET ( EPOLLIN | EPOLLHUP | EPOLLRDHUP )

bool wait_for_sock(int sock, int timeout)
{
	__do_close int epfd = -EBADF;
	struct epoll_event ev;
	int ret, now, starttime, deltatime;

	if ((starttime = time(NULL)) < 0)
		return false;

	epfd = epoll_create(1);
	if (epfd < 0)
		return log_error(false, "%s\n", "Failed to create epoll socket: %m");

	ev.events = POLLIN_SET;
	ev.data.fd = sock;
	if (epoll_ctl(epfd, EPOLL_CTL_ADD, sock, &ev) < 0)
		return log_error(false, "Failed adding socket to epoll: %m");

again:
	if ((now = time(NULL)) < 0)
		return false;

	deltatime = (starttime + timeout) - now;
	if (deltatime < 0)
		return false;

	ret = epoll_wait(epfd, &ev, 1, 1000*deltatime + 1);
	if (ret < 0 && errno == EINTR)
		goto again;

	if (ret <= 0)
		return false;

	return true;
}

bool recv_creds(int sock, struct ucred *cred, char *v)
{
	struct msghdr msg = { 0 };
	struct iovec iov;
	struct cmsghdr *cmsg;
	char cmsgbuf[CMSG_SPACE(sizeof(*cred))];
	char buf[1];
	int ret;
	int optval = 1;

	*v = '1';

	cred->pid = -1;
	cred->uid = -1;
	cred->gid = -1;

	if (setsockopt(sock, SOL_SOCKET, SO_PASSCRED, &optval, sizeof(optval)) == -1)
		return log_error(false, "Failed to set passcred: %s\n", strerror(errno));

	buf[0] = '1';
	if (write(sock, buf, 1) != 1)
		return log_error(false, "Failed to start write on scm fd: %s\n", strerror(errno));

	msg.msg_name = NULL;
	msg.msg_namelen = 0;
	msg.msg_control = cmsgbuf;
	msg.msg_controllen = sizeof(cmsgbuf);

	iov.iov_base = buf;
	iov.iov_len = sizeof(buf);
	msg.msg_iov = &iov;
	msg.msg_iovlen = 1;

	if (!wait_for_sock(sock, 2))
		return log_error(false, "Timed out waiting for scm_cred: %s\n", strerror(errno));

	ret = recvmsg(sock, &msg, MSG_DONTWAIT);
	if (ret < 0)
		return log_error(false, "Failed to receive scm_cred: %s\n", strerror(errno));

	cmsg = CMSG_FIRSTHDR(&msg);

	if (cmsg && cmsg->cmsg_len == CMSG_LEN(sizeof(struct ucred)) &&
			cmsg->cmsg_level == SOL_SOCKET &&
			cmsg->cmsg_type == SCM_CREDENTIALS) {
		memcpy(cred, CMSG_DATA(cmsg), sizeof(*cred));
	}
	*v = buf[0];

	return true;
}

static int msgrecv(int sockfd, void *buf, size_t len)
{
	if (!wait_for_sock(sockfd, 2))
		return -1;

	return recv(sockfd, buf, len, MSG_DONTWAIT);
}

int send_creds(int sock, struct ucred *cred, char v, bool pingfirst)
{
	struct msghdr msg = { 0 };
	struct iovec iov;
	struct cmsghdr *cmsg;
	char cmsgbuf[CMSG_SPACE(sizeof(*cred))];
	char buf[1];
	buf[0] = 'p';

	if (pingfirst && msgrecv(sock, buf, 1) != 1)
		return log_error(SEND_CREDS_FAIL, "%s - Failed getting reply from server over socketpair: %d",
				 strerror(errno), SEND_CREDS_FAIL);

	msg.msg_control = cmsgbuf;
	msg.msg_controllen = sizeof(cmsgbuf);

	cmsg = CMSG_FIRSTHDR(&msg);
	cmsg->cmsg_len = CMSG_LEN(sizeof(struct ucred));
	cmsg->cmsg_level = SOL_SOCKET;
	cmsg->cmsg_type = SCM_CREDENTIALS;
	memcpy(CMSG_DATA(cmsg), cred, sizeof(*cred));

	msg.msg_name = NULL;
	msg.msg_namelen = 0;

	buf[0] = v;
	iov.iov_base = buf;
	iov.iov_len = sizeof(buf);
	msg.msg_iov = &iov;
	msg.msg_iovlen = 1;

	if (sendmsg(sock, &msg, 0) < 0) {
		if (errno == 3)
			return log_error(SEND_CREDS_NOTSK, "%s - Failed at sendmsg: %d", strerror(errno), SEND_CREDS_NOTSK);

		return log_error(SEND_CREDS_FAIL, "%s - Failed at sendmsg: %d", strerror(errno), SEND_CREDS_FAIL);
	}

	return SEND_CREDS_OK;
}

int read_file_fuse(const char *path, char *buf, size_t size, struct file_info *d)
{
	__do_free char *line = NULL;
	__do_fclose FILE *f = NULL;
	size_t linelen = 0, total_len = 0;
	char *cache = d->buf;
	size_t cache_size = d->buflen;

	f = fopen(path, "re");
	if (!f)
		return 0;

	while (getline(&line, &linelen, f) != -1) {
		ssize_t l = snprintf(cache, cache_size, "%s", line);
		if (l < 0)
			return log_error(0, "Failed to write cache");
		if (l >= cache_size)
			return log_error(0, "Write to cache was truncated");

		cache += l;
		cache_size -= l;
		total_len += l;
	}

	d->size = total_len;
	if (total_len > size)
		total_len = size;

	/* read from off 0 */
	memcpy(buf, d->buf, total_len);

	if (d->size > total_len)
		d->cached = d->size - total_len;

	return total_len;
}

int read_file_fuse_with_offset(const char *path, char *buf, size_t size,
			       off_t offset, struct file_info *d)
{
	if (offset) {
		ssize_t total_len = 0;
		char *cache = d->buf;
		int left;

		if (offset > d->size)
			return -EINVAL;

		if (!d->cached)
			return 0;

		left = d->size - offset;
		total_len = left > size ? size : left;
		memcpy(buf, cache + offset, total_len);

		return total_len;
	}

	return read_file_fuse(path, buf, size, d);
}

#define INITSCOPE "/init.scope"
void prune_init_slice(char *cg)
{
	char *point;
	size_t cg_len = strlen(cg), initscope_len = strlen(INITSCOPE);

	if (cg_len < initscope_len)
		return;

	point = cg + cg_len - initscope_len;
	if (strcmp(point, INITSCOPE) == 0) {
		if (point == cg)
			*(point + 1) = '\0';
		else
			*point = '\0';
	}
}

int wait_for_pid(pid_t pid)
{
	int status, ret;

	if (pid <= 0)
		return -1;

again:
	ret = waitpid(pid, &status, 0);
	if (ret == -1) {
		if (errno == EINTR)
			goto again;
		return -1;
	}
	if (ret != pid)
		goto again;
	if (!WIFEXITED(status) || WEXITSTATUS(status) != 0)
		return -1;
	return 0;
}

static void *must_realloc(void *orig, size_t sz)
{
	void *ret;

	do {
		ret = realloc(orig, sz);
	} while (!ret);

	return ret;
}

static char *fd_to_buf(int fd, size_t *length)
{
	__do_free char *copy = NULL;

	if (!length)
		return NULL;

	*length = 0;
	for (;;) {
		ssize_t bytes_read;
		char buf[4096];
		char *old = copy;

		bytes_read = read_nointr(fd, buf, sizeof(buf));
		if (bytes_read < 0)
			return NULL;

		if (!bytes_read)
			break;

		copy = must_realloc(old, (*length + bytes_read) * sizeof(*old));
		memcpy(copy + *length, buf, bytes_read);
		*length += bytes_read;
	}

	return move_ptr(copy);
}

static char *file_to_buf(const char *path, size_t *length)
{
	__do_close int fd = -EBADF;

	if (!length)
		return NULL;

	fd = open(path, O_RDONLY | O_CLOEXEC);
	if (fd < 0)
		return NULL;

	return fd_to_buf(fd, length);
}

FILE *fopen_cached(const char *path, const char *mode, void **caller_freed_buffer)
{
	__do_free char *buf = NULL;
	size_t len = 0;
	FILE *f;

	buf = file_to_buf(path, &len);
	if (!buf)
		return NULL;

	f = fmemopen(buf, len, mode);
	if (!f)
		return NULL;
	*caller_freed_buffer = move_ptr(buf);
	return f;
}

FILE *fdopen_cached(int fd, const char *mode, void **caller_freed_buffer)
{
	__do_free char *buf = NULL;
	size_t len = 0;
	FILE *f;

	buf = fd_to_buf(fd, &len);
	if (!buf)
		return NULL;

	f = fmemopen(buf, len, mode);
	if (!f)
		return NULL;

	*caller_freed_buffer = move_ptr(buf);
	return f;
}

ssize_t read_nointr(int fd, void *buf, size_t count)
{
	ssize_t ret;

	do {
		ret = read(fd, buf, count);
	} while (ret < 0 && errno == EINTR);

	return ret;
}

ssize_t write_nointr(int fd, const void *buf, size_t count)
{
	ssize_t ret;

	do {
		ret = write(fd, buf, count);
	} while (ret < 0 && errno == EINTR);

	return ret;
}

/*
 * Let's use the "standard stack limit" (i.e. glibc thread size default) for
 * stack sizes: 8MB.
 */
#define __LXCFS_STACK_SIZE (8 * 1024 * 1024)
pid_t lxcfs_clone(int (*fn)(void *), void *arg, int flags)
{
	pid_t ret;
	void *stack;

	stack = malloc(__LXCFS_STACK_SIZE);
	if (!stack)
		return ret_errno(ENOMEM);

#ifdef __ia64__
	ret = __clone2(fn, stack, __LXCFS_STACK_SIZE, flags | SIGCHLD, arg, NULL);
#else
	ret = clone(fn, stack + __LXCFS_STACK_SIZE, flags | SIGCHLD, arg, NULL);
#endif
	return ret;
}
