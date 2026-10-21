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

/* The module must define qh0 as the textByte chain of the hex digest. */
static int holds_digest(Text module, const char *hex) {
  char line[2048];
  int size = snprintf(line, sizeof line, "\ndef qh0 : Text := ");
  for (const char *digit = hex; *digit != '\0'; digit++) size += snprintf(line + size, sizeof line - size, "(textByte %d ", *digit);
  size += snprintf(line + size, sizeof line - size, "textEnd");
  for (const char *digit = hex; *digit != '\0'; digit++) line[size++] = ')';
  line[size++] = '\n';
  Text want = text_of_bytes((const unsigned char *)line, (size_t)size);
  for (Nat start = 0; start + want.size <= module.size; start++)
    if (same_text((Text){module.items + start, want.size}, want)) return 1;
  return 0;
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
    "-- comment\r\ndef n : Text := \"hi\" -- final comment",
    /* Builtin read references follow lexical scope and nonrecursive defs. */
    "def read : ReadPath := read\ndef full : Log := read Log nil (queryReplay momentNow)\n",
    "def read : ReadPath := fun (A : Type 0) (log : Log) (q : Query A) => read A log q\n"
    "def full : Log := read Log nil (queryReplay momentNow)\n",
    "def f : (read : ReadPath) -> Log := fun (r : ReadPath) => read Log nil (queryReplay momentNow)\n"
    "def full : Log := f read\n",
    "def f : (read : ReadPath) -> Log := fun (read : ReadPath) => read Log nil (queryReplay momentNow)\n"
    "def full : Log := f read\n",
    "def f : (read : Type 0) -> (x : read) -> read := fun (read : Type 0) (x : read) => x\n"
    "def n : Nat := f Nat 7\n",
    "def f : (read : ReadPath) -> ReadPath := "
    "fun (read : ReadPath) (A : Type 0) (log : Log) (q : Query A) => read A log q\n"
    "def g : ReadPath := read\n"
  };
  unsigned count = sizeof programs / sizeof programs[0];
  for (unsigned row = 0; row < count; row++) {
    Text source = text(programs[row]), output, module, refusal;
    Failure failure;
    assert(compile_program(source, &output, &failure));
    assert(certificate_module(source, output, NULL, &module, &refusal));
    check_module(argv[1], module, row, 0);
  }

  /* A non-text stage payload leaves the projected Commercial stage intact
     in both the evaluator and the certificate. */
  {
    Text source = text(
        "def acme : Ref kindParty := refTo (hashOf \"p\")\n"
        "def deal0 : Commercial := makeCommercial commercialDeal \"D\" acme \"q\" none \"U\" none statusOpen attrsEnd none\n"
        "def e1 : Entry := makeEntry none (actorAgent \"a\") (createsCommercial deal0)\n"
        "def deal : Ref kindCommercial := refTo (hashOf \"5cc8d104daa8f9c0746007c2a86128b3a8b2b84a42a8da69fde1f23aa72920dc\")\n"
        "def event : Event := makeEvent eventStageChanged (subjectCommercial deal) none none "
        "(attrsField \"after\" (valueNat 7) attrsEnd) none\n"
        "def e2 : Entry := makeEntry none (actorAgent \"a\") (createsEvent event)\n"
        "def book : Log := cons e1 (cons e2 nil)\n");
    Text output, module, refusal;
    Failure failure;
    Hashed collected = {builder_new(), builder_new(), builder_new()};
    assert(compile_collect(source, &output, &collected, &failure));
    assert(certificate_module(source, output, &collected, &module, &refusal));
    check_module(argv[1], module, count++, 0);
  }

  /* Free Identifier payloads have the same projection in C and the kernel,
     including malformed fields and explicit empty text. */
  {
    static const char *const payloads[] = {
        "attrsField \"system\" (valueText \"unknown\") (attrsField \"value\" (valueText \"id\") attrsEnd)",
        "attrsField \"system\" (valueText \"systemOther\") (attrsField \"value\" (valueText \"id\") attrsEnd)",
        "attrsField \"system\" (valueText \"systemOther\") (attrsField \"name\" (valueNat 7) "
        "(attrsField \"value\" (valueText \"id\") attrsEnd))",
        "attrsField \"system\" (valueText \"systemEmail\") attrsEnd",
        "attrsField \"system\" (valueText \"systemEmail\") (attrsField \"value\" (valueNat 7) attrsEnd)",
        "attrsField \"system\" (valueText \"systemEmail\") (attrsField \"value\" (valueText \"\") attrsEnd)",
        "attrsField \"system\" (valueText \"systemOther\") (attrsField \"name\" (valueText \"\") "
        "(attrsField \"value\" (valueText \"id\") attrsEnd))"};
    for (unsigned verify = 0; verify < 2; verify++)
      for (unsigned row = 0; row < sizeof payloads / sizeof payloads[0]; row++) {
        char bytes[2048];
        int size = snprintf(bytes, sizeof bytes,
            "def org : Party := makeParty partyOrg \"A\" none (cons (makeIdentifier systemEmail \"\" none) "
            "(cons (makeIdentifier (systemOther \"\") \"id\" none) nil)) attrsEnd none none\n"
            "def pe : Entry := makeEntry none (actorAgent \"a\") (createsParty org)\n"
            "def p : Ref kindParty := refTo (hashOf \"ecfefbfd7e68d070e66b541ded4b7168b1a283ceeddc9621b3e3d93831ac62eb\")\n"
            "def ev : Event := makeEvent %s (subjectParty p) none none (%s) none\n"
            "def ee : Entry := makeEntry none (actorAgent \"a\") (createsEvent ev)\n"
            "def book : Log := cons pe (cons ee nil)\n"
            "def answer : Account360 := read Account360 book (queryAccount360 p momentNow)\n",
            verify == 1 ? "eventIdentifierVerified" : "eventFieldsChanged", payloads[row]);
        assert(size >= 0 && (size_t)size < sizeof bytes);
        Text output, module, refusal;
        Failure failure;
        Hashed collected = {builder_new(), builder_new(), builder_new()};
        assert(compile_collect(text(bytes), &output, &collected, &failure));
        assert(certificate_module(text(bytes), output, &collected, &module, &refusal));
        check_module(argv[1], module, count++, 0);
      }
  }

  /* Parentheses in a type comment must not select another log's hashes. */
  {
    Text source = text(
        "def e : Entry := makeEntry none (actorAgent \"a\") "
        "(createsEvent (makeEvent eventNoteAdded (subjectParty (refTo (hashOf \"p\"))) none none attrsEnd none))\n"
        "def empty : Log := nil\ndef book : Log := cons e nil\n"
        "def a : List (Ref kindEvent) := read (List (Ref kindEvent) -- ) ledgerUser_empty\n"
        ") book (queryAuditByActor (actorAgent \"a\"))\n"
        "def custom : ReadPath := fun (A : Type 0) (log : Log) (q : Query A) => read A nil q\n"
        "def run : (read : ReadPath) -> Log := fun (read :-- ) ignored\n"
        "ReadPath) => read Log book (queryReplay momentNow)\n"
        "def answer : Log := run custom\n");
    Text output, module, refusal;
    Failure failure;
    Hashed collected = {builder_new(), builder_new(), builder_new()};
    assert(compile_collect(source, &output, &collected, &failure));
    assert(certificate_module(source, output, &collected, &module, &refusal));
    check_module(argv[1], module, count++, 0);
  }

  Text source = text("def n : Nat := 7\n"), output, other, module, refusal;
  Failure failure;
  /* A direct write keeps its head across lexer whitespace and comments. */
  static const char *const layouts[] = {
    "def s : Step :=\twrite history request\n",
    "def s : Step := -- body comment\n write history request\n",
    "-- def ledgerUser_s : Step := makeStep nil (outcomeDenied none nil)\n"
    "def s : Step := write history request\n",
    "def\t-- definition comment\n s : Step -- := ignored\n := write history request\n"
  };
  for (unsigned layout = 0; layout < sizeof layouts / sizeof layouts[0]; layout++) {
    TextBuilder program = builder_new();
    builder_append(&program, text("def acme : Ref kindParty := refTo (hashOf \"party-acme\")\n"
                                 "def history : Log := nil\n"
                                 "def request : Write := makeWrite (actorHuman acme) none (commandDeleteParty acme)\n"));
    builder_append(&program, text(layouts[layout]));
    Hashed collected = {builder_new(), builder_new(), builder_new()};
    Text formatted = builder_text(&program);
    assert(compile_collect(formatted, &output, &collected, &failure));
    assert(certificate_module(formatted, output, &collected, &module, &refusal));
    check_module(argv[1], module, count++, 0);
  }
  /* The kernel must reject a claim whose output disagrees with the source. */
  assert(compile_program(source, &output, &failure));
  assert(compile_program(text("def n : Nat := 8\n"), &other, &failure));
  assert(certificate_module(source, other, NULL, &module, &refusal));
  check_module(argv[1], module, count++, 1);

  /* A refusal remains a refusal, including unsupported names after CR. */
  source = text("-- comment\rdef p : Prod Nat Nat := pair 1 2\n");
  assert(compile_program(source, &output, &failure));
  assert(!certificate_module(source, output, NULL, &module, &refusal));
  assert(same_text(refusal, text("the certificate does not cover Prod yet")));
  /* Only the name check refuses a checker name outside the instance types. */
  source = text("def T : Type 0 := Prod Nat Nat\ndef n : Nat := 5\n");
  assert(compile_program(source, &output, &failure));
  assert(!certificate_module(source, output, NULL, &module, &refusal));
  assert(same_text(refusal, text("the certificate does not cover Prod yet")));
  source = text("def refuse : WritePath :=\n  fun (log : Log) (write : Write) => makeStep log (outcomeDenied none nil)\n");
  assert(compile_program(source, &output, &failure));
  assert(certificate_module(source, output, NULL, &module, &refusal));
  check_module(argv[1], module, count++, 0);
  /* The sum rule: two texts of 760 bytes take 13 blocks each. */
  Hashed many = {builder_new(), builder_new(), builder_new()};
  for (Nat index = 0; index < 1520; index++) builder_push(&many.bytes, 97);
  builder_push(&many.ends, 760);
  builder_push(&many.ends, 1520);
  source = text("def n : Nat := 8\n");
  assert(compile_program(source, &output, &failure));
  assert(!certificate_module(source, output, &many, &module, &refusal));
  assert(same_text(refusal, text("the certificate does not cover more than 24 hash blocks yet")));
  /* The sum rule on a source with a read (the d3 cases 81 to 85 and 108). */
  source = text("def book : Log := nil\ndef full : Log := read Log book (queryReplay momentNow)\n");
  assert(compile_program(source, &output, &failure));
  assert(!certificate_module(source, output, &many, &module, &refusal));
  assert(same_text(refusal, text("the certificate does not cover more than 24 hash blocks yet")));
  /* The "abc" and "" vectors: the kernel checks each block step, and qh0 is the published digest. */
  static const char *const vectors[][2] = {
    {"abc", "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"},
    {"", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"}
  };
  for (unsigned vector = 0; vector < 2; vector++) {
    Hashed one = {builder_new(), builder_new(), builder_new()};
    for (const char *byte = vectors[vector][0]; *byte != '\0'; byte++) builder_push(&one.bytes, (unsigned char)*byte);
    builder_push(&one.ends, one.bytes.size);
    assert(certificate_module(source, output, &one, &module, &refusal));
    assert(holds_digest(module, vectors[vector][1]));
    check_module(argv[1], module, count++, 0);
  }
  /* A Step that write gives under another head: its written mark is 1. */
  Hashed marks = {builder_new(), builder_new(), builder_new()};
  source = text("def acme : Ref kindParty := refTo (hashOf \"party-acme\")\ndef history : Log := nil\n"
                "def note : Event := makeEvent eventNoteAdded (subjectParty acme) none none attrsEnd none\n"
                "def noted : Write := makeWrite (actorHuman acme) none (commandRecord note)\n"
                "def w : WritePath := write\ndef s : Step := w history noted\n");
  assert(compile_collect(source, &output, &marks, &failure));
  assert(!certificate_module(source, output, &marks, &module, &refusal));
  assert(same_text(refusal, text("the certificate does not cover this step yet")));
  source = text("def s : Text := \"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789abc\"\n");
  assert(compile_program(source, &output, &failure));
  assert(!certificate_module(source, output, NULL, &module, &refusal));
  assert(same_text(refusal, text("the certificate does not cover a text longer than 64 bytes yet")));
  printf("C certificate tests passed (%u kernel checks)\n", count);
  return 0;
}
