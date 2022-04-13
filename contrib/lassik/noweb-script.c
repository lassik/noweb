/*
 * noweb-script -- runner for self-executing noweb scripts
 *
 * This program lets you type:
 *
 *     #! /usr/bin/env noweb-script
 *
 * at the top of a noweb program. If you then `chmod +x` the file on a
 * Unix-like operating system, you get an executable script written as
 * a literate program.
 *
 * noweb-script works by calling upon notangle to get the
 * <<noweb-script>> chunk of the program. The tangled chunk must
 * itself start with a `#!` line specifying the interpreter to use.
 *
 * The tangled program is written into a temporary directory. To avoid
 * littering the temp dir with numerous copies of the same script as
 * you edit it, the name of the temp file is a cryptographic hash of
 * the realpath of the source file name. To help ensure the contents
 * of the temp file have not been tampered with after it was written,
 * noweb-script tangles the script afresh on each run even if a
 * tempfile by the same name already exists. The new tempfile is
 * atomically moved in place of the old tempfile using rename().
 *
 * Temp files are not deleted automatically. Use a general-purpose
 * temp directory cleaner to do that. Many systems automatically clear
 * /tmp using a cron job or at boot time. Per-user temp directories
 * can be cleared similarly.
 *
 * Why doesn't noweb-script run the script as a subprocess and stick
 * around to clean up the tempfile after the script is done? Because
 * forking introduces some complications in the Unix process model.
 * For example, the subprocess gets a different process ID than the
 * parent and reliably sending signals to the subprocess is not as
 * simple as sending them to the parent. It's better to leave a few
 * small temp files around than to impose this complexity on the user.
 *
 * We could pass the tangled program to the Unix kernel to execute
 * directly. But since the program is tangled into a temporary
 * directory, noweb-script actually interprets the `#!` line itself
 * and emulates what the kernel would do. We do this because some
 * systems place temporary directories on a file system that is
 * mounted without execute permission (`mount -o noexec`).
 *
 * Copyright 2022 Lassi Kortela
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <sys/stat.h>

#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "sha256.h"

#ifndef PROGNAME
#define PROGNAME "noweb-script"
#endif

#ifndef ROOTCHUNK
#define ROOTCHUNK "noweb-script"
#endif

#ifndef NOTANGLE
#define NOTANGLE "notangle"
#endif

#ifndef O_NOFOLLOW
#define O_NOFOLLOW 0
#endif

#define STRING_MAX 2000

struct string {
    char bytes[STRING_MAX];
};

static struct string path;
static struct string newpath;
static struct string shebang;

static void generic_usage(FILE *stream, int status)
{
    fprintf(stream, "usage: %s script [arg ...]\n", PROGNAME);
    exit(status);
}

static void usage() { generic_usage(stderr, 3); }

static void fatal(const char *msg)
{
    fprintf(stderr, "%s: %s\n", PROGNAME, msg);
    exit(3);
}

static void fatal_memory(void) { fatal("out of memory"); }

static void fatal_errno(const char *msg)
{
    fprintf(stderr, "%s: %s: %s\n", PROGNAME, msg, strerror(errno));
    exit(3);
}

static void fatal_errno_string(const char *msg, const char *str)
{
    fprintf(stderr, "%s: %s %s: %s\n", PROGNAME, msg, str, strerror(errno));
    exit(3);
}

static void string_set(struct string *dst, struct string *src)
{
    memcpy(dst->bytes, src->bytes, STRING_MAX);
}

static char *string_resb(struct string *string, size_t n)
{
    size_t len = strlen(string->bytes);
    if (len + n >= STRING_MAX)
        fatal_memory();
    return string->bytes + len;
}

static void string_putc(struct string *string, int ch)
{
    string_resb(string, 1)[0] = ch;
}

static void string_puts(struct string *string, const char *str)
{
    size_t len = strlen(str);
    memcpy(string_resb(string, len), str, len);
}

static void string_remove_final_slash(struct string *string)
{
    char *limit = strchr(string->bytes, '\0');
    while (limit > string->bytes + 1) { /* Don't remove an initial slash. */
        if (limit[-1] != '/')
            break;
        *--limit = '\0';
    }
}

static void string_fill_from_fd(struct string *string, int from_fd)
{
    char *place;
    ssize_t room, nread;

    place = string->bytes;
    room = STRING_MAX - 1;
    do {
        do {
            nread = read(from_fd, place, room);
        } while ((nread == -1) && (errno == EINTR));
        if (nread == -1)
            fatal_errno("cannot read from file");
        place += nread;
        room -= nread;
    } while (room && nread);
}

static void notangle(int web_fd, int tangle_fd)
{
    char *argv[] = { NOTANGLE, "-R" ROOTCHUNK, NULL };
    pid_t child;
    int status;

    if ((child = fork()) == -1) {
        fatal_errno("cannot fork");
    }
    if (!child) {
        dup2(web_fd, STDIN_FILENO);
        close(web_fd);
        dup2(tangle_fd, STDOUT_FILENO);
        close(tangle_fd);
        execvp(argv[0], argv);
        fprintf(stderr, "%s: cannot run %s: %s\n", PROGNAME, argv[0],
            strerror(errno));
        _exit(127);
    }
    if (waitpid(child, &status, 0) == -1) {
        fatal_errno("cannot wait for notangle");
    }
    if (!WIFEXITED(status)) {
        fatal("notangle crashed");
    }
    if (WEXITSTATUS(status) != 0) {
        fatal("notangle failed");
    }
}

static const char *get_tmpdir(void)
{
    const char *dir;

    if ((dir = getenv("TMPDIR"))) {
        if (dir[0] == '/')
            return dir;
    }
    return "/tmp";
}

#define MULTIBASE_BASE32 "b"
#define MULTIHASH_SHA256 0x12

static unsigned char multihash[2 + 32]
    = { MULTIHASH_SHA256, SHA256_BLOCK_SIZE };
static unsigned char *const hash = &multihash[2];

static void compute_hash(void *bytes, size_t nbyte)
{
    SHA256_CTX ctx;

    sha256_init(&ctx);
    sha256_update(&ctx, bytes, nbyte);
    sha256_final(&ctx, hash);
}

static void string_puts_base32(
    struct string *out, unsigned char *bytes, size_t nbyte)
{
    static const char alphabet[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZ234567";
    const uint64_t low5 = (1 << 5) - 1;
    uint64_t shift;

    while (nbyte) {
        uint64_t word = 0;
        uint64_t nnow = 5;
        if (nnow > nbyte)
            nnow = nbyte;
        if (nnow > 4) {
            word |= bytes[4];
            word <<= 8;
        }
        if (nnow > 3) {
            word |= bytes[3];
            word <<= 8;
        }
        if (nnow > 2) {
            word |= bytes[2];
            word <<= 8;
        }
        if (nnow > 1) {
            word |= bytes[1];
            word <<= 8;
        }
        word |= bytes[0];
        shift = 40;
        do {
            shift -= 5;
            string_putc(out, alphabet[low5 & (word >> shift)]);
        } while (shift > 0);
        bytes += nnow;
        nbyte -= nnow;
    }
}

static int shebang_is_space(int ch) { return (ch == ' ') || (ch == '\t'); }

static int shebang_is_nonspace(int ch)
{
    return ch && (ch != '\n') && !shebang_is_space(ch);
}

static void read_shebang_line(char **out_interpreter, char **out_argument)
{
    char *s;

    *out_argument = NULL;
    s = shebang.bytes;
    if ((s[0] != '#') || (s[1] != '!'))
        fatal("tangled script does not start with #!");
    s = &s[2];
    while (shebang_is_space(*s))
        s++;
    *out_interpreter = s;
    while (shebang_is_nonspace(*s))
        s++;
    if (*out_interpreter == s)
        fatal("blank #! line");
    if (*s == '\n') {
        *s = '\0';
        return;
    }
    *s++ = '\0';
    while (shebang_is_space(*s))
        s++;
    *out_argument = s;
    while (*s && (*s != '\n'))
        s++;
    if (!*s)
        fatal("end of #! line not found");
    while (shebang_is_space(s[-1]))
        s--;
    *s = '\0';
    if (*out_argument == s)
        *out_argument = NULL;
}

static void script(int argc, char **argv)
{
    int web_fd, tangle_fd, i;
    char *web_real;
    char **newargv;
    char **place;
    char *interpreter;
    char *argument;

    if (!(web_real = realpath(argv[0], NULL)))
        fatal_errno_string("cannot resolve web path", argv[0]);
    if ((web_fd = open(web_real, O_RDONLY)) == -1)
        fatal_errno_string("cannot open web file", web_real);
    compute_hash(web_real, strlen(web_real));
    string_puts(&path, get_tmpdir());
    string_remove_final_slash(&path);
    string_puts(&path, "/" PROGNAME "-");
    string_puts(&path, MULTIBASE_BASE32);
    string_puts_base32(&path, multihash, sizeof(multihash));
    string_set(&newpath, &path);
    string_puts(&newpath, ".new");
    if ((tangle_fd = open(
             newpath.bytes, O_RDWR | O_CREAT | O_TRUNC | O_NOFOLLOW, 0600))
        == -1)
        fatal_errno_string("cannot open temporary file", newpath.bytes);
    notangle(web_fd, tangle_fd);
    if (fchmod(tangle_fd, 0400) == -1)
        fatal_errno("cannot chmod temp file");
    if (rename(newpath.bytes, path.bytes) == -1)
        fatal_errno("cannot rename temp file");
    if (lseek(tangle_fd, 0, SEEK_SET) == -1)
        fatal_errno("cannot rewind file");
    string_fill_from_fd(&shebang, tangle_fd);
    read_shebang_line(&interpreter, &argument);
    if (!(newargv = calloc(argc + 3, sizeof(*newargv))))
        fatal_memory();
    place = newargv;
    *place++ = interpreter;
    if (argument)
        *place++ = argument;
    *place++ = path.bytes;
    for (i = 1; i < argc; i++)
        *place++ = argv[i];
    argv = newargv;
    execv(argv[0], argv);
    fprintf(stderr, "%s: cannot run %s: %s\n", PROGNAME, argv[0],
        strerror(errno));
    exit(127);
}

int main(int argc, char **argv)
{
    if (argc < 2) {
        usage();
    }
    script(argc - 1, argv + 1);
    return 0;
}
