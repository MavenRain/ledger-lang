/* The certificate core (M5 design items 8 and 9, delta B-1): the rows of
   core/schema.def and then core/ops.def as one mechanism-lang module. Each
   line is the stringify text of its rows, in row order:
   CARRIER and FAMILY  mu NAME HEADER with
   AND                 and NAME HEADER with
   CONSTRUCTOR         | NAME : (F1 : T1) -> ... -> RESULT, with the FIELD rows after it
   DEFINE              def NAME REST
   A blank line comes before each mu and def line except the first. */
#include "ledger.h"

typedef enum {
  ROW_CARRIER,
  ROW_FAMILY,
  ROW_AND,
  ROW_CONSTRUCTOR,
  ROW_FIELD,
  ROW_DEFINE
} RowKind;

/* One row of core/schema.def or core/ops.def. arg keeps the second argument
   as written. */
typedef struct {
  RowKind kind;
  const char *name;
  const char *arg;
} Row;

#define CARRIER(name, header) {ROW_CARRIER, #name, #header},
#define FAMILY(name, header) {ROW_FAMILY, #name, #header},
#define AND(name, header) {ROW_AND, #name, #header},
#define CONSTRUCTOR(name, result) {ROW_CONSTRUCTOR, #name, #result},
#define FIELD(name, type) {ROW_FIELD, #name, #type},
#define DEFINE(name, rest) {ROW_DEFINE, #name, #rest},
static const Row rows[] = {
#include "../core/schema.def"
#include "../core/ops.def"
};
#undef CARRIER
#undef FAMILY
#undef AND
#undef CONSTRUCTOR
#undef FIELD
#undef DEFINE

#define ROW_COUNT ((Nat)(sizeof rows / sizeof rows[0]))

static void append_string(TextBuilder *builder, const char *string) {
  for (const char *byte = string; *byte != 0; byte++) builder_push(builder, (unsigned char)*byte);
}

static void append_named(TextBuilder *builder, const char *word, const Row *line, const char *end) {
  append_string(builder, word);
  append_string(builder, line->name);
  append_string(builder, " ");
  append_string(builder, line->arg);
  append_string(builder, end);
}

/* The fields of the constructor at row: the FIELD rows that follow it. */
static void append_fields(TextBuilder *builder, Nat row) {
  for (Nat index = row + 1; index < ROW_COUNT && rows[index].kind == ROW_FIELD; index++) {
    append_string(builder, "(");
    append_string(builder, rows[index].name);
    append_string(builder, " : ");
    append_string(builder, rows[index].arg);
    append_string(builder, ") -> ");
  }
}

static void append_row(TextBuilder *builder, Nat row) {
  const Row *line = &rows[row];
  switch (line->kind) {
    case ROW_CARRIER:
    case ROW_FAMILY:
      if (row > 0) append_string(builder, "\n");
      append_named(builder, "mu ", line, " with\n");
      return;
    case ROW_AND:
      append_named(builder, "and ", line, " with\n");
      return;
    case ROW_CONSTRUCTOR:
      append_string(builder, "| ");
      append_string(builder, line->name);
      append_string(builder, " : ");
      append_fields(builder, row);
      append_string(builder, line->arg);
      append_string(builder, "\n");
      return;
    case ROW_FIELD:
      return;
    case ROW_DEFINE:
      if (row > 0) append_string(builder, "\n");
      append_named(builder, "def ", line, "\n");
      return;
  }
}

Text certificate_core(void) {
  TextBuilder builder = builder_new();
  for (Nat row = 0; row < ROW_COUNT; row++) append_row(&builder, row);
  return builder_text(&builder);
}
