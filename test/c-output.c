#include <assert.h>

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

int main(void) {
  assert(freopen("/dev/null", "r", stdout) != NULL);
  assert(setvbuf(stdout, NULL, _IONBF, 0) == 0);
  Text output = text_of_bytes((const unsigned char *)"{}", 2);
  /* fflush alone succeeds even though fwrite failed on this stream. */
  assert(write_output(output, "") == 2);
  assert(ferror(stdout));
  fputs("C output regression passed\n", stderr);
  return 0;
}
