#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

#include "../compiler/ledger.h"

static Text text(const char *value) {
  return text_of_bytes((const unsigned char *)value, strlen(value));
}

static void check_module(const char *kernel, Text module, unsigned row, int expected) {
  char path[128], log[128];
  snprintf(path, sizeof path, "build/cert/regression-%u.mech", row);
  snprintf(log, sizeof log, "build/cert/regression-%u.log", row);
  FILE *file = fopen(path, "wb");
  assert(file != NULL);
  for (Nat at = 0; at < module.size; at++) {
    assert(module.items[at] <= 255);
    assert(fputc(module.items[at], file) != EOF);
  }
  assert(fclose(file) == 0);
  pid_t child = fork();
  assert(child >= 0);
  if (child == 0) {
    if (freopen(log, "w", stdout) == NULL || dup2(STDOUT_FILENO, STDERR_FILENO) < 0) _exit(126);
    execl(kernel, kernel, "check", path, (char *)NULL);
    _exit(127);
  }
  int status;
  assert(waitpid(child, &status, 0) == child);
  if (!WIFEXITED(status) || WEXITSTATUS(status) != expected) {
    fprintf(stderr, "certificate regression %u: expected %d, status %d, see %s\n", row, expected, status, log);
    exit(1);
  }
}

int main(int argc, char **argv) {
  assert(argc == 2);
  static const char *const programs[] = {
    "",
    "def n : Nat := 7\n",
    "def zero : Nat := 0\ndef max : Nat := 1073741823\ndef leading : Nat := 0007\n",
    "def s : Text := \"a\\n\\t\\b\\f\\r\\\"\\\\\"\n",
    "def xs : List Nat := cons 1 (cons 2 nil)\n",
    "def o : Option (Option Nat) := some none\ndef v : Option Value := some valueNull\n",
    "def a : Attrs := attrsField \"k\" (valueItems (valuesItem (valueNat 3) valuesEnd)) attrsEnd\n",
    "def a : Account := accountParty (refTo (hashOf \"p\"))\n",
    "def i : Identifier := makeIdentifier systemEmail \"me\" none\n",
    "def certificate : Nat := 3\n",
    "def certificateRender : Nat := 3\ndef certificateBytes0 : Nat := certificateRender\n",
    "def renderLit1 : Nat := 3\ndef renderLit2 : Nat := renderLit1\n",
    "def encodeNat : Nat := 3\ndef encodeAccount : Nat := encodeNat\n",
    "def MechEq : Nat := 3\ndef mechRefl : Nat := MechEq\ndef mechReflCtor : Nat := mechRefl\n",
    "def tenPowers : Nat := 3\ndef digitAt : Nat := tenPowers\n",
    "def case : Nat := 1\ndef return : Nat := case\ndef in : Nat := return\n",
    "def Prop : Nat := 4\ndef natAdd : Nat := Prop\n",
    "def ledgerUser_n : Nat := 1\ndef n : Nat := ledgerUser_n\n",
    "def f : (encodeNat : Nat) -> Nat := fun (encodeNat : Nat) => encodeNat\ndef n : Nat := f 6\n",
    "def id : (A : Type 0) -> (x : A) -> A := fun (A : Type 0) (x : A) => x\ndef n : Nat := id Nat 7\n",
    "def T : Type 0 := Nat\ndef n : T := 5\n",
    "-- comment\rdef n : Text := \"hi\"\r",
    "def n : Nat := 1 -- trailing comment\rdef s : Text := \"hi\"\r",
    "-- comment\r\ndef n : Text := \"hi\" -- final comment"
  };
  unsigned count = sizeof programs / sizeof programs[0];
  for (unsigned row = 0; row < count; row++) {
    Text source = text(programs[row]), output, module, refusal;
    Failure failure;
    assert(compile_program(source, &output, &failure));
    assert(certificate_module(source, output, &module, &refusal));
    check_module(argv[1], module, row, 0);
  }

  /* The kernel must reject a claim whose output disagrees with the source. */
  Text source = text("def n : Nat := 7\n"), output, other, module, refusal;
  Failure failure;
  assert(compile_program(source, &output, &failure));
  assert(compile_program(text("def n : Nat := 8\n"), &other, &failure));
  assert(certificate_module(source, other, &module, &refusal));
  check_module(argv[1], module, count++, 1);

  /* A refusal remains a refusal, including unsupported names after CR. */
  source = text("-- comment\rdef p : Prod Nat Nat := pair 1 2\n");
  assert(compile_program(source, &output, &failure));
  assert(!certificate_module(source, output, &module, &refusal));
  assert(same_text(refusal, text("the certificate does not cover Prod yet")));
  source = text("def s : Text := \"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789abc\"\n");
  assert(compile_program(source, &output, &failure));
  assert(!certificate_module(source, output, &module, &refusal));
  assert(same_text(refusal, text("the certificate does not cover a text longer than 64 bytes yet")));
  printf("C certificate tests passed (%u kernel checks)\n", count);
  return 0;
}
