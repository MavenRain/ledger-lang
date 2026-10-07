/* ledgerc: compiles one ledger-lang program to JSON.

   ledgerc PROGRAM.ledger  writes the JSON document and a newline to stdout,
                           or "PROGRAM.ledger: byte N: message" to stderr.
   ledgerc --stdin         reads the source from stdin and writes the exact
                           compiler output (a document or an error) to stdout. */
#include <errno.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "ledger.h"

#define SOURCE_LIMIT 65536
#define OUTPUT_LIMIT ((Nat)4 * 1024 * 1024)
/* The compiler recurses once per nested term and per list item. */
#define STACK_SIZE ((size_t)1 << 30)

typedef struct {
  Text source;
  int ok;
  Text output;
  Failure failure;
} Job;

static void *run_job(void *argument) {
  Job *job = argument;
  job->ok = compile_program(job->source, &job->output, &job->failure);
  return NULL;
}

static int compile_on_big_stack(Job *job) {
  pthread_attr_t attributes;
  pthread_t thread;
  if (pthread_attr_init(&attributes) != 0) return 0;
  if (pthread_attr_setstacksize(&attributes, STACK_SIZE) != 0) return 0;
  if (pthread_create(&thread, &attributes, run_job, job) != 0) return 0;
  pthread_attr_destroy(&attributes);
  return pthread_join(thread, NULL) == 0;
}

/* Reads at most SOURCE_LIMIT + 1 bytes. Returns the byte count, or -1 when
   the read fails. */
static long read_source(FILE *file, unsigned char *bytes) {
  size_t size = 0;
  size_t got;
  while (size < SOURCE_LIMIT + 1 && (got = fread(bytes + size, 1, SOURCE_LIMIT + 1 - size, file)) > 0) size += got;
  return ferror(file) ? -1 : (long)size;
}

/* Writes the output bytes, or a message for an output the bridge rejects. */
static int write_output(Text output, const char *suffix) {
  if (output.size > OUTPUT_LIMIT) {
    fprintf(stderr, "compiler output exceeds %u bytes\n", (unsigned)OUTPUT_LIMIT);
    return 2;
  }
  unsigned char *bytes = malloc((size_t)output.size + 1);
  if (bytes == NULL) {
    fputs("ledgerc: out of memory\n", stderr);
    return 70;
  }
  for (Nat index = 0; index < output.size; index++) {
    if (output.items[index] > 255) {
      fputs("compiler emitted a non-byte\n", stderr);
      free(bytes);
      return 2;
    }
    bytes[index] = (unsigned char)output.items[index];
  }
  size_t written = fwrite(bytes, 1, output.size, stdout);
  free(bytes);
  if (written != output.size || fputs(suffix, stdout) == EOF || fflush(stdout) != 0) return 2;
  return 0;
}

static void print_bytes(FILE *file, Text text) {
  for (Nat index = 0; index < text.size; index++) fputc((int)(text.items[index] & 255), file);
}

static int compile_stdin(void) {
  static unsigned char bytes[SOURCE_LIMIT + 1];
  long size = read_source(stdin, bytes);
  if (size < 0) {
    fputs("ledgerc: cannot read stdin\n", stderr);
    return 2;
  }
  if (size > SOURCE_LIMIT) {
    fprintf(stderr, "source exceeds %d bytes\n", SOURCE_LIMIT);
    return 2;
  }
  Job job = {text_of_bytes(bytes, (size_t)size), 0, {NULL, 0}, {0, {NULL, 0}}};
  if (!compile_on_big_stack(&job)) {
    fputs("ledgerc: cannot start the compiler thread\n", stderr);
    return 70;
  }
  return write_output(job.ok ? job.output : error_text(job.failure.position, job.failure.message), "");
}

static int compile_file(const char *path) {
  static unsigned char bytes[SOURCE_LIMIT + 1];
  FILE *file = fopen(path, "rb");
  if (file == NULL) {
    fprintf(stderr, "%s: %s\n", path, strerror(errno));
    return 1;
  }
  long size = read_source(file, bytes);
  fclose(file);
  if (size < 0) {
    fprintf(stderr, "%s: cannot read the file\n", path);
    return 1;
  }
  if (size > SOURCE_LIMIT) {
    fprintf(stderr, "%s: source exceeds %d bytes\n", path, SOURCE_LIMIT);
    return 1;
  }
  Job job = {text_of_bytes(bytes, (size_t)size), 0, {NULL, 0}, {0, {NULL, 0}}};
  if (!compile_on_big_stack(&job)) {
    fprintf(stderr, "%s: cannot start the compiler thread\n", path);
    return 70;
  }
  if (job.ok) return write_output(job.output, "\n");
  fprintf(stderr, "%s: byte %u: ", path, (unsigned)job.failure.position);
  print_bytes(stderr, job.failure.message);
  fputc('\n', stderr);
  return 1;
}

int main(int argc, char **argv) {
  if (argc == 2 && strcmp(argv[1], "--stdin") == 0) return compile_stdin();
  if (argc == 2 && strncmp(argv[1], "--", 2) != 0) return compile_file(argv[1]);
  fputs("usage: bin/ledgerc PROGRAM.ledger\n", stderr);
  return 1;
}
