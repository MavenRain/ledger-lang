#include <assert.h>
#include <string.h>
#include <unistd.h>

/* Exercise the CLI writer before the C program driver is available. */
#define main ledgerc_main
#include "../compiler/main.c"
#undef main

int compile_program(Text source, Text *output, Failure *failure) {
  (void)source;
  (void)output;
  (void)failure;
  return 0;
}

Text error_text(Nat position, Text message) {
  (void)position;
  return message;
}

Nat same_term(const Term *left, const Term *right) {
  (void)left;
  (void)right;
  return 0;
}

Text term_text(const Term *term) {
  (void)term;
  return text_end();
}

int main(void) {
  assert(freopen("/dev/null", "r", stdout) != NULL);
  assert(setvbuf(stdout, NULL, _IONBF, 0) == 0);
  Text output = text_of_bytes((const unsigned char *)"{}", 2);
  /* fflush alone succeeds even though fwrite failed on this stream. */
  assert(write_output(output, "") == 2);
  assert(ferror(stdout));
  /* M5 item 0c: the size check of write_output is at OUTPUT_LIMIT. An output
     of OUTPUT_LIMIT bytes passes it and stops at its first item, a non-byte;
     one more byte gets the refusal before any allocation. */
  Nat non_byte[1] = {256};
  Text at_limit = {non_byte, OUTPUT_LIMIT};
  Text over_limit = {non_byte, OUTPUT_LIMIT + 1};
  int ends[2];
  assert(pipe(ends) == 0);
  int saved = dup(2);
  assert(saved >= 0 && dup2(ends[1], 2) == 2);
  int over = write_output(over_limit, "");
  int at = write_output(at_limit, "");
  assert(dup2(saved, 2) == 2 && close(saved) == 0 && close(ends[1]) == 0);
  char said[128] = {0};
  assert(read(ends[0], said, sizeof said - 1) > 0 && close(ends[0]) == 0);
  assert(over == 2 && at == 2);
  assert(strcmp(said, "compiler output exceeds 67108864 bytes\ncompiler emitted a non-byte\n") == 0);
  fputs("C output regression passed\n", stderr);
  return 0;
}
