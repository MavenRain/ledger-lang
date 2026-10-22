/* The certificate (M5 design items 8 and 9, deltas B-1 and C-1).
   certificate_core gives the rows of core/schema.def and then core/ops.def
   as one mechanism-lang module. certificate_module gives the module of
   ledgerc --certificate PROGRAM.ledger, in this order: the MechEq rows of
   core/certificate.def, the core rows, the other certificate.def rows,
   encodeKind, encodeRef and one encoder for each schema.def FAMILY row, the
   lowered program, the renderLitN defs and the render, the claim chunks and
   the claim. Each row line is the stringify text of its row:
   CARRIER and FAMILY  mu NAME HEADER with
   AND                 and NAME HEADER with
   CONSTRUCTOR         | NAME : (F1 : T1) -> ... -> RESULT, with the FIELD rows after it
   DEFINE              def NAME REST
   DEFINE_REC          def rec NAME REST
   DEFINE_AND          and NAME REST
   A blank line comes before each mu and def line except the first. */
#include <stdarg.h>
#include <stdio.h>
#include <string.h>

#include "ledger.h"

typedef enum {
  ROW_CARRIER,
  ROW_FAMILY,
  ROW_AND,
  ROW_CONSTRUCTOR,
  ROW_FIELD,
  ROW_DEFINE,
  ROW_DEFINE_REC,
  ROW_DEFINE_AND
} RowKind;

/* One row of a .def file. arg keeps the second argument as written. */
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
#define DEFINE_REC(name, rest) {ROW_DEFINE_REC, #name, #rest},
#define DEFINE_AND(name, rest) {ROW_DEFINE_AND, #name, #rest},
static const Row schema_rows[] = {
#include "../core/schema.def"
};
static const Row ops_rows[] = {
#include "../core/ops.def"
};
static const Row fixed_rows[] = {
#include "../core/certificate.def"
};
#undef CARRIER
#undef FAMILY
#undef AND
#undef CONSTRUCTOR
#undef FIELD
#undef DEFINE
#undef DEFINE_REC
#undef DEFINE_AND

typedef struct {
  const Row *rows;
  Nat count;
} Table;

#define TABLE(array) ((Table){(array), (Nat)(sizeof(array) / sizeof((array)[0]))})
#define SCHEMA_COUNT ((Nat)(sizeof schema_rows / sizeof schema_rows[0]))
/* A row number below ALL_COUNT names a schema.def row, then an ops.def row. */
#define ALL_COUNT (SCHEMA_COUNT + (Nat)(sizeof ops_rows / sizeof ops_rows[0]))

static const Row *row_at(Nat row) {
  return row < SCHEMA_COUNT ? &schema_rows[row] : &ops_rows[row - SCHEMA_COUNT];
}

/* CHUNK is the byte count of a literal, a renderLitN def and a claim chunk.
   TERM bounds an encoder term and a type text. */
enum { CHUNK = 64, TERM = 1024 };

/* Every non-reserved source name gets this prefix, including names that
   already start with it. This is injective and disjoint from core names,
   certificate helpers and mechanism-lang keywords. */
static const char user_prefix[] = "ledgerUser_";

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
static void append_fields(TextBuilder *builder, Table table, Nat row) {
  for (Nat index = row + 1; index < table.count && table.rows[index].kind == ROW_FIELD; index++) {
    append_string(builder, "(");
    append_string(builder, table.rows[index].name);
    append_string(builder, " : ");
    append_string(builder, table.rows[index].arg);
    append_string(builder, ") -> ");
  }
}

/* lead 0 drops the blank line before a mu or def line. */
static void append_row(TextBuilder *builder, Table table, Nat row, int lead) {
  const Row *line = &table.rows[row];
  switch (line->kind) {
    case ROW_CARRIER:
    case ROW_FAMILY:
      if (lead) append_string(builder, "\n");
      append_named(builder, "mu ", line, " with\n");
      return;
    case ROW_AND:
      append_named(builder, "and ", line, " with\n");
      return;
    case ROW_CONSTRUCTOR:
      append_string(builder, "| ");
      append_string(builder, line->name);
      append_string(builder, " : ");
      append_fields(builder, table, row);
      append_string(builder, line->arg);
      append_string(builder, "\n");
      return;
    case ROW_FIELD:
      return;
    case ROW_DEFINE:
      if (lead) append_string(builder, "\n");
      append_named(builder, "def ", line, "\n");
      return;
    case ROW_DEFINE_REC:
      if (lead) append_string(builder, "\n");
      append_named(builder, "def rec ", line, "\n");
      return;
    case ROW_DEFINE_AND:
      append_named(builder, "and ", line, "\n");
      return;
  }
}

/* The rows from row from to row end; lead 0 drops the blank line before the first. */
static void append_rows(TextBuilder *builder, Table table, Nat from, Nat end, int lead) {
  for (Nat row = from; row < end; row++) append_row(builder, table, row, lead || row > from);
}

static void append_core(TextBuilder *builder, int lead) {
  append_rows(builder, TABLE(schema_rows), 0, TABLE(schema_rows).count, lead);
  append_rows(builder, TABLE(ops_rows), 0, TABLE(ops_rows).count, 1);
}

Text certificate_core(void) {
  TextBuilder builder = builder_new();
  append_core(&builder, 0);
  return builder_text(&builder);
}

/* The rows of certificate.def through its first DEFINE (MechEq and mechRefl). */
static Nat eq_rows(Table fixed) {
  Nat row = 0;
  while (row < fixed.count && fixed.rows[row].kind != ROW_DEFINE) row++;
  return row < fixed.count ? row + 1 : row;
}

static void append_items(TextBuilder *builder, const Nat *items, Nat size) {
  for (Nat index = 0; index < size; index++) builder_push(builder, items[index]);
}

static void append_nat(TextBuilder *builder, Nat number) {
  if (number >= 10) append_nat(builder, number / 10);
  builder_push(builder, 48 + number % 10);
}

/* The openings "(textByte B " of a textByte chain. close_chain closes it. */
static void open_items(TextBuilder *builder, const Nat *items, Nat size) {
  for (Nat index = 0; index < size; index++) {
    append_string(builder, "(textByte ");
    append_nat(builder, items[index]);
    append_string(builder, " ");
  }
}

static void open_bytes(TextBuilder *builder, const char *bytes) {
  for (const char *byte = bytes; *byte != 0; byte++) {
    append_string(builder, "(textByte ");
    append_nat(builder, (unsigned char)*byte);
    append_string(builder, " ");
  }
}

static void close_chain(TextBuilder *builder, Nat size) {
  for (Nat index = 0; index < size; index++) builder_push(builder, 41);
}

/* The textByte chain of bytes, with textEnd at its end. */
static void append_literal(TextBuilder *builder, const char *bytes) {
  open_bytes(builder, bytes);
  append_string(builder, "textEnd");
  close_chain(builder, strlen(bytes));
}

/* Sets the refusal "the certificate does not cover SUBJECT yet" and gives 0. */
static int refuse(Text *refusal, const char *subject) {
  TextBuilder builder = builder_new();
  append_string(&builder, "the certificate does not cover ");
  append_string(&builder, subject);
  append_string(&builder, " yet");
  *refusal = builder_text(&builder);
  return 0;
}

/* 1 when text holds the bytes of word at [at, at + size). */
static int same_word(Text text, Nat at, Nat size, const char *word) {
  if (strlen(word) != size || at + size > text.size) return 0;
  for (Nat index = 0; index < size; index++)
    if (text.items[at + index] != (unsigned char)word[index]) return 0;
  return 1;
}

/* The checker names that the module does not bind (Q-M5-26 (c)). */
static const char *const unbound_names[] = {
  "Prod", "Sum", "pair", "inl", "inr", "Sigma", "pack", "witness", "payload", "Eq", "refl", "transport",
  "symm", "trans", "cong", "first", "second", "either", "pure", "map", "bind", "fold", "unfold", "filter"};

static int name_byte(Nat byte) {
  return (byte >= 97 && byte <= 122) || (byte >= 65 && byte <= 90) || (byte >= 48 && byte <= 57) || byte == 95;
}

/* 0 with a refusal when the module does not cover the source name at [at, at + size). */
static int covered_name(Text source, Nat at, Nat size, Text *refusal) {
  for (size_t index = 0; index < sizeof unbound_names / sizeof unbound_names[0]; index++)
    if (same_word(source, at, size, unbound_names[index])) return refuse(refusal, unbound_names[index]);
  return 1;
}

/* The byte of the escape backslash c (lexer.c escape_byte), or 256 for none. */
static Nat literal_escape(Nat c) {
  switch (c) {
    case 34: case 92: case 47: return c;
    case 110: return 10;
    case 114: return 13;
    case 116: return 9;
    case 98: return 8;
    case 102: return 12;
    default: return 256;
  }
}

/* The source with literals as textByte chains and user names prefixed.
   Normalize carriage returns to newlines so comments end as in lexer.c.
   Gives 0 with a refusal for an unbound checker name and a literal
   longer than CHUNK bytes. */
static int lower_source(Text source, TextBuilder *lowered, Text *refusal) {
  Nat at = 0;
  while (at < source.size) {
    Nat byte = source.items[at];
    if (byte == 45 && at + 1 < source.size && source.items[at + 1] == 45) {
      while (at < source.size && source.items[at] != 10 && source.items[at] != 13)
        builder_push(lowered, source.items[at++]);
      continue;
    }
    if (name_byte(byte)) {
      Nat start = at;
      while (at < source.size && name_byte(source.items[at])) at++;
      if (!covered_name(source, start, at - start, refusal)) return 0;
      Text name = {source.items + start, at - start};
      /* Source binders carry no quantities. Keep user ReadPath lambdas
         compatible with ordinary Type binders through the adapter. */
      if (same_word(source, start, at - start, "ReadPath")) {
        append_string(lowered, "ledgerReadPath");
        continue;
      }
      if (!(byte >= 48 && byte <= 57) && !reserved_name(name)) append_string(lowered, user_prefix);
      append_items(lowered, source.items + start, at - start);
      continue;
    }
    if (byte != 34) {
      builder_push(lowered, byte == 13 ? 10 : byte);
      at++;
      continue;
    }
    Nat literal[CHUNK];
    Nat used = 0;
    at++;
    while (at < source.size && source.items[at] != 34) {
      int escaped = source.items[at] == 92;
      Nat decoded = escaped ? (at + 1 < source.size ? literal_escape(source.items[at + 1]) : 256) : source.items[at];
      if (decoded > 255) return refuse(refusal, "this text escape");
      if (used == CHUNK) return refuse(refusal, "a text longer than 64 bytes");
      literal[used++] = decoded;
      at += escaped ? 2 : 1;
    }
    if (at >= source.size) return refuse(refusal, "this text literal");
    at++;
    open_items(lowered, literal, used);
    append_string(lowered, "textEnd");
    close_chain(lowered, used);
  }
  return 1;
}

static const char json_head[] = "{\"ledger-lang\":1,\"instances\":[";

static int expect_word(Text json, Nat *at, const char *word) {
  if (!same_word(json, *at, strlen(word), word)) return 0;
  *at += strlen(word);
  return 1;
}

/* The span from *at to the next quote, and the quote. */
static int quoted_span(Text json, Nat *at, TextBuilder *spans) {
  Nat start = *at;
  while (*at < json.size && json.items[*at] != 34 && json.items[*at] != 92) *at += 1;
  if (*at >= json.size || json.items[*at] != 34) return 0;
  builder_push(spans, start);
  builder_push(spans, *at - start);
  *at += 1;
  return 1;
}

/* The name and type spans of the instances of the JSON document (four items
   for each instance: name at, name size, type at, type size; the part C s8
   gen.c render port). 0 with a refusal when the document holds more than the
   instances. */
static int read_instances(Text json, TextBuilder *spans, Text *refusal) {
  Nat at = 0, depth = 2;
  int quoted = 0;
  if (!expect_word(json, &at, json_head)) return refuse(refusal, "this document");
  while (at < json.size && depth > 1) {
    Nat byte = json.items[at];
    if (quoted) {
      quoted = byte != 34;
      at += byte == 92 ? 2 : 1;
      continue;
    }
    if (byte == 123 && depth == 2) {
      if (!expect_word(json, &at, "{\"name\":\"") || !quoted_span(json, &at, spans) ||
          !expect_word(json, &at, ",\"type\":\"") || !quoted_span(json, &at, spans) || !expect_word(json, &at, ",\"value\":"))
        return refuse(refusal, "this instance form");
      depth = 3;
      continue;
    }
    quoted = byte == 34;
    depth = depth + (byte == 123 || byte == 91) - (byte == 125 || byte == 93);
    at++;
  }
  /* M5 delta D-1 (b): the records tail ,"records":[...] (program.c:1272). */
  if (depth == 1 && expect_word(json, &at, ",\"records\":[")) {
    for (depth = 2; at < json.size && depth > 1; at++) {
      Nat byte = json.items[at];
      if (quoted) {
        quoted = byte != 34;
        at += byte == 92;
        continue;
      }
      quoted = byte == 34;
      depth = depth + (byte == 123 || byte == 91) - (byte == 125 || byte == 93);
    }
  }
  if (depth != 1 || at + 1 != json.size || json.items[at] != 125) return refuse(refusal, "the records");
  return 1;
}

static int is_head_row(const Row *line) {
  return line->kind == ROW_CARRIER || line->kind == ROW_FAMILY || line->kind == ROW_AND;
}

static int same_name(const char *name, const char *word, size_t size) {
  return strlen(name) == size && strncmp(name, word, size) == 0;
}

/* The schema.def or ops.def row of the family or carrier named word[0, size),
   or ALL_COUNT. */
static Nat family_row(const char *word, size_t size) {
  Nat row = 0;
  while (row < ALL_COUNT && !(is_head_row(row_at(row)) && same_name(row_at(row)->name, word, size))) row++;
  return row;
}

/* The row after the constructor and field rows of the family at row, in the
   same .def file. */
static Nat family_end(Nat row) {
  Nat end = row + 1, limit = row < SCHEMA_COUNT ? SCHEMA_COUNT : ALL_COUNT;
  while (end < limit && !is_head_row(row_at(end))) end++;
  return end;
}

static int is_kind(const char *word, size_t size) {
  Nat kind = family_row("Kind", 4);
  for (Nat row = kind + 1; row < family_end(kind); row++)
    if (schema_rows[row].kind == ROW_CONSTRUCTOR && same_name(schema_rows[row].name, word, size)) return 1;
  return 0;
}

/* [*from, *end) without outer spaces and one pair of outer parentheses. */
static void bare(const char *type, size_t *from, size_t *end) {
  while (*from < *end && type[*from] == ' ') *from += 1;
  while (*end > *from && type[*end - 1] == ' ') *end -= 1;
  if (*end - *from < 2 || type[*from] != '(' || type[*end - 1] != ')') return;
  *from += 1;
  *end -= 1;
  while (*from < *end && type[*from] == ' ') *from += 1;
  while (*end > *from && type[*end - 1] == ' ') *end -= 1;
}

static const char *const base_encoders[][2] = {
  {"Text", "encodeText"}, {"Nat", "encodeNat"}, {"Flag", "encodeFlag"}, {"Hash", "encodeHash"},
  {"Kind", "encodeKind"}, {"Value", "encodeValue"}, {"Values", "encodeValues"}, {"Attrs", "encodeAttrs"}};

/* The encoder term (T -> Text -> Text) of the type text type[from, end) in
   to, or 0 with the name that has no encoder in missing (the part C s8 gen.c
   enc_of port). made marks the schema.def FAMILY rows that have an encoder. */
static int encoder(const unsigned char *made, const char *type, size_t from, size_t end, char *to, char *missing) {
  static const char *const forms[] = {"encodeOptionBare", "encodeOptionSome", "encodeList", "encodeList"};
  bare(type, &from, &end);
  size_t head = from;
  while (head < end && type[head] != ' ') head++;
  size_t rest = head;
  while (rest < end && type[rest] == ' ') rest++;
  snprintf(missing, TERM, "%.*s", (int)(head - from), type + from);
  if (rest == end) {
    /* ops.def:5: Log is a DEFINE of List Entry, not a FAMILY. */
    if (same_name("Log", type + from, head - from)) return encoder(made, "List Entry", 0, 10, to, missing);
    for (size_t index = 0; index < sizeof base_encoders / sizeof base_encoders[0]; index++)
      if (same_name(base_encoders[index][0], type + from, head - from))
        return snprintf(to, TERM, "%s", base_encoders[index][1]) < TERM;
    Nat row = family_row(type + from, head - from);
    if (row == ALL_COUNT || row_at(row)->kind != ROW_FAMILY || !made[row]) return 0;
    return snprintf(to, TERM, "encode%s", row_at(row)->name) < TERM;
  }
  size_t a = rest, b = end;
  bare(type, &a, &b);
  if (same_name("Ref", type + from, head - from))
    return is_kind(type + a, b - a) && snprintf(to, TERM, "(encodeRef %.*s)", (int)(b - a), type + a) < TERM;
  int list = same_name("List", type + from, head - from);
  if (!list && !same_name("Option", type + from, head - from)) return 0;
  char inner[TERM];
  if (!encoder(made, type, a, b, inner, missing)) return 0;
  /* types.c:14 encodes_null: of the types with an encoder, Option and Value. */
  size_t word = a;
  while (word < b && type[word] != ' ') word++;
  int nullable = same_name("Option", type + a, word - a) || same_name("Value", type + a, word - a);
  int spaced = word < b;
  return snprintf(to, TERM, "(%s %s%.*s%s %s)", forms[list * 2 + nullable], spaced ? "(" : "", (int)(b - a), type + a,
                  spaced ? ")" : "", inner) < TERM;
}

static void append_kinds(TextBuilder *builder) {
  Nat kind = family_row("Kind", 4);
  append_string(builder, "\ndef encodeKind : Kind -> Text -> Text := fun (k : Kind) (tail : Text) =>\n"
                         "  case k as self in Kind return Text with\n");
  for (Nat row = kind + 1; row < family_end(kind); row++) {
    if (schema_rows[row].kind != ROW_CONSTRUCTOR) continue;
    append_string(builder, "  | ");
    append_string(builder, schema_rows[row].name);
    append_string(builder, " => encodeText ");
    append_literal(builder, schema_rows[row].name);
    append_string(builder, " tail\n");
  }
  append_string(builder, "\ndef encodeRef : (k : Kind) -> Ref k -> Text -> Text := fun (k : Kind) (r : Ref k) (tail : Text) =>\n"
                         "  case r as self in Ref return Text with\n  | refTo (h : Hash) => ");
  open_bytes(builder, "{\"kind\":");
  append_string(builder, "(encodeKind k ");
  open_bytes(builder, ",\"hash\":");
  append_string(builder, "(encodeHash h (textByte 125 tail))");
  close_chain(builder, 8);
  append_string(builder, ")");
  close_chain(builder, 8);
  append_string(builder, "\n");
}

/* 1 when each field type of the family at row has an encoder. */
static int fields_covered(const unsigned char *made, Nat row) {
  char term[TERM], missing[TERM];
  for (Nat at = row + 1; at < family_end(row); at++)
    if (row_at(at)->kind == ROW_FIELD && !encoder(made, row_at(at)->arg, 0, strlen(row_at(at)->arg), term, missing))
      return 0;
  return 1;
}

/* The arm of the constructor at row: only constants gives the name string,
   one constructor the object, else "tag" first and then the fields. */
static void append_arm(TextBuilder *builder, const unsigned char *made, Nat row, int constants, int tagged) {
  const Row *ctor = row_at(row);
  Nat end = row + 1;
  while (end < ALL_COUNT && row_at(end)->kind == ROW_FIELD) end++;
  append_string(builder, "  | ");
  append_string(builder, ctor->name);
  for (Nat at = row + 1; at < end; at++) {
    append_string(builder, " (x");
    append_nat(builder, at - row - 1);
    append_string(builder, " : ");
    append_string(builder, row_at(at)->arg);
    append_string(builder, ")");
  }
  append_string(builder, " => ");
  if (constants) {
    append_string(builder, "encodeText ");
    append_literal(builder, ctor->name);
    append_string(builder, " tail\n");
    return;
  }
  char key[TERM], term[TERM], missing[TERM];
  Nat closers = 0;
  if (tagged) {
    snprintf(key, TERM, "{\"tag\":\"%s\"", ctor->name);
    open_bytes(builder, key);
    closers += strlen(key);
  }
  for (Nat at = row + 1; at < end; at++) {
    snprintf(key, TERM, "%s\"%s\":", at == row + 1 && !tagged ? "{" : ",", row_at(at)->name);
    open_bytes(builder, key);
    encoder(made, row_at(at)->arg, 0, strlen(row_at(at)->arg), term, missing);
    append_string(builder, "(");
    append_string(builder, term);
    append_string(builder, " x");
    append_nat(builder, at - row - 1);
    append_string(builder, " ");
    closers += strlen(key) + 1;
  }
  append_string(builder, "(textByte 125 tail)");
  close_chain(builder, closers);
  append_string(builder, "\n");
}

/* The encoder of the family at row; made marks it. */
static void append_family(TextBuilder *builder, unsigned char *made, Nat row) {
  const char *name = row_at(row)->name;
  Nat end = family_end(row), ctors = 0;
  int constants = 1;
  for (Nat at = row + 1; at < end; at++) {
    ctors += row_at(at)->kind == ROW_CONSTRUCTOR;
    constants = constants && row_at(at)->kind != ROW_FIELD;
  }
  append_string(builder, "\ndef encode");
  append_string(builder, name);
  append_string(builder, " : ");
  append_string(builder, name);
  append_string(builder, " -> Text -> Text := fun (x : ");
  append_string(builder, name);
  append_string(builder, ") (tail : Text) =>\n  case x as self in ");
  append_string(builder, name);
  append_string(builder, " return Text with\n");
  for (Nat at = row + 1; at < end; at++)
    if (row_at(at)->kind == ROW_CONSTRUCTOR) append_arm(builder, made, at, constants, !constants && ctors > 1);
  made[row] = 1;
}

/* One encoder for each schema.def FAMILY row whose field types all have one,
   in row order, then the same for the ops.def families of deltas D-1 (b) and
   E-1 (e) in the order of ops_families (each one cites only earlier ones);
   made marks them. */
static void append_families(TextBuilder *builder, unsigned char *made) {
  static const char *const ops_families[] = {"Missing", "Outcome", "Command", "Write", "Step",
                                             "Bucket", "StageStat", "Renewal", "Account360", "Verdict"};
  for (Nat row = 0; row < SCHEMA_COUNT; row++)
    if (schema_rows[row].kind == ROW_FAMILY && fields_covered(made, row)) append_family(builder, made, row);
  for (size_t index = 0; index < sizeof ops_families / sizeof ops_families[0]; index++) {
    Nat row = family_row(ops_families[index], strlen(ops_families[index]));
    if (row < ALL_COUNT && row_at(row)->kind == ROW_FAMILY && fields_covered(made, row)) append_family(builder, made, row);
  }
}

/* The encoder of the instance type json[at, at + size) in to, or 0 with a
   refusal that names the family with no encoder. Each schema.def family and
   each ops.def family of ops_families has one, so of the FAMILY rows the
   refusal can name only Moment, PipelineKey and Query. */
static int instance_encoder(const unsigned char *made, Text json, Nat at, Nat size, char *to, Text *refusal) {
  char type[TERM], missing[TERM];
  if (size >= TERM) return refuse(refusal, "a type text this long");
  for (Nat index = 0; index < size; index++) type[index] = (char)json.items[at + index];
  type[size] = 0;
  return encoder(made, type, 0, size, to, missing) || refuse(refusal, missing);
}

/* The renderLitN defs of piece (CHUNK bytes each) into module, and their
   textThen openings into render. Gives the opening count. */
static Nat append_lits(TextBuilder *module, TextBuilder *render, Text piece, Nat *lits) {
  Nat opens = 0;
  for (Nat at = 0; at < piece.size; at += CHUNK) {
    Nat take = piece.size - at < CHUNK ? piece.size - at : CHUNK;
    *lits += 1;
    append_string(module, "\ndef renderLit");
    append_nat(module, *lits);
    append_string(module, " : Text := ");
    open_items(module, piece.items + at, take);
    append_string(module, "textEnd");
    close_chain(module, take);
    append_string(module, "\n");
    append_string(render, "(textThen renderLit");
    append_nat(render, *lits);
    append_string(render, " ");
    opens++;
  }
  return opens;
}

/* The bytes as defs certificateBytes0, 1, ... of CHUNK bytes each, the last
   chunk first (no forward names). */
static void append_chunks(TextBuilder *builder, const char *name, Text bytes) {
  Nat count = bytes.size == 0 ? 1 : (bytes.size + CHUNK - 1) / CHUNK;
  for (Nat chunk = count; chunk > 0; chunk--) {
    Nat at = (chunk - 1) * CHUNK;
    Nat take = bytes.size - at < CHUNK ? bytes.size - at : CHUNK;
    append_string(builder, "\ndef ");
    append_string(builder, name);
    append_nat(builder, chunk - 1);
    append_string(builder, " : Text :=\n  ");
    open_items(builder, bytes.items + at, take);
    if (chunk < count) {
      append_string(builder, name);
      append_nat(builder, chunk);
    } else {
      append_string(builder, "textEnd");
    }
    close_chain(builder, take);
    append_string(builder, "\n");
  }
}

/* M5 delta D-1 (b): the rows of the write path and the records. A Line is
   a short name or claim side. */
typedef struct {
  char items[2048];
  size_t size;
} Line;

static void put_line(Line *line, const char *format, ...) {
  va_list args;
  va_start(args, format);
  int wrote = vsnprintf(line->items + line->size, sizeof line->items - line->size, format, args);
  va_end(args);
  size_t room = sizeof line->items - 1 - line->size;
  line->size += wrote < 0 ? 0 : ((size_t)wrote < room ? (size_t)wrote : room);
}

/* "(cons qwKxBxLOW ... nil)" up to qwKxBx(HIGH - 1). */
static void put_names(Line *line, Nat text, Nat block, Nat low, Nat high) {
  for (Nat index = low; index < high; index++) put_line(line, "(cons qw%ux%ux%u ", text, block, index);
  put_line(line, "nil");
  for (Nat index = low; index < high; index++) put_line(line, ")");
}

/* A word as 32 bits, the most significant bit first. */
static void append_bits(TextBuilder *builder, Nat word) {
  for (Nat bit = 0; bit < 32; bit++) append_string(builder, (word >> (31 - bit)) & 1 ? "(cons 1 " : "(cons 0 ");
  append_string(builder, "nil");
  close_chain(builder, 32);
}

static void append_state(TextBuilder *builder, const Nat *words) {
  for (Nat word = 0; word < 8; word++) {
    append_string(builder, "(cons ");
    append_bits(builder, words[word]);
    append_string(builder, " ");
  }
  append_string(builder, "nil");
  close_chain(builder, 8);
}

static void append_head(TextBuilder *builder, const char *name, const char *type) {
  const char *parts[] = {"\ndef ", name, " : ", type, " := "};
  for (Nat index = 0; index < sizeof parts / sizeof parts[0]; index++) append_string(builder, parts[index]);
}

static void append_claim(TextBuilder *builder, const char *name, const char *type, const Line *left, const Line *right) {
  const char *parts[] = {"\ndef ", name, " : MechEq (", type, ") ", left->items, " ", right->items,
                         " := mechRefl (", type, ") ", left->items, "\n"};
  for (Nat index = 0; index < sizeof parts / sizeof parts[0]; index++) append_string(builder, parts[index]);
}

/* The rows of the hashed text K: qmsgK (chunks), the sha256_trace literals,
   per block 48 shaNext, 8 shaRounds and 1 shaAddState claims, then the parse
   claim qcpK and the hex claim qchK to qhK. */
static int append_hashed(TextBuilder *builder, Text message, Nat text, Text *refusal) {
  Sha256Block blocks[24];
  Nat count = 0;
  char name[64];
  if (!sha256_trace(message, blocks, 24, &count)) return refuse(refusal, "more than 24 hash blocks");
  snprintf(name, sizeof name, "qmsg%ux", text);
  append_chunks(builder, name, message);
  snprintf(name, sizeof name, "qs%ux0x0", text);
  append_head(builder, name, "List (List Nat)");
  append_string(builder, "shaH\n");
  for (Nat block = 0; block < count; block++) {
    const Sha256Block *trace = &blocks[block];
    for (Nat index = 0; index < 64; index++) {
      snprintf(name, sizeof name, "qw%ux%ux%u", text, block, index);
      append_head(builder, name, "List Nat");
      append_bits(builder, trace->schedule[index]);
      append_string(builder, "\n");
    }
    for (Nat index = 16; index < 64; index++) {
      Line left = {0}, right = {0};
      put_line(&left, "(shaNext ");
      put_names(&left, text, block, index - 16, index);
      put_line(&left, ")");
      put_line(&right, "qw%ux%ux%u", text, block, index);
      snprintf(name, sizeof name, "qcw%ux%ux%u", text, block, index);
      append_claim(builder, name, "List Nat", &left, &right);
    }
    /* The trace has no state after round 64: it is after - before[0]. */
    for (Nat group = 1; group <= 8; group++) {
      Nat words[8];
      for (Nat word = 0; word < 8; word++)
        words[word] = group < 8 ? trace->before[group][word] : (Nat)(trace->after[word] - trace->before[0][word]);
      snprintf(name, sizeof name, "qs%ux%ux%u", text, block, 8 * group);
      append_head(builder, name, "List (List Nat)");
      append_state(builder, words);
      append_string(builder, "\n");
    }
    for (Nat group = 0; group < 8; group++) {
      Line left = {0}, right = {0};
      put_line(&left, "(shaRounds shaKg%u ", group);
      put_names(&left, text, block, 8 * group, 8 * group + 8);
      put_line(&left, " qs%ux%ux%u)", text, block, 8 * group);
      put_line(&right, "qs%ux%ux%u", text, block, 8 * group + 8);
      snprintf(name, sizeof name, "qcr%ux%ux%u", text, block, 8 * group);
      append_claim(builder, name, "List (List Nat)", &left, &right);
    }
    snprintf(name, sizeof name, "qs%ux%ux0", text, block + 1);
    append_head(builder, name, "List (List Nat)");
    append_state(builder, trace->after);
    append_string(builder, "\n");
    Line left = {0}, right = {0};
    put_line(&left, "(shaAddState qs%ux%ux0 qs%ux%ux64)", text, block, text, block);
    put_line(&right, "qs%ux%ux0", text, block + 1);
    snprintf(name, sizeof name, "qca%ux%u", text, block);
    append_claim(builder, name, "List (List Nat)", &left, &right);
  }
  snprintf(name, sizeof name, "qblocks%u", text);
  append_head(builder, name, "List (List (List Nat))");
  for (Nat block = 0; block < count; block++) {
    Line list = {0};
    put_names(&list, text, block, 0, 16);
    append_string(builder, "(cons ");
    append_string(builder, list.items);
    append_string(builder, " ");
  }
  append_string(builder, "nil");
  close_chain(builder, count);
  append_string(builder, "\n");
  Line parse = {0}, blocks_name = {0};
  put_line(&parse, "(shaBlocks (shaWords (shaBytes qmsg%ux0 (cons 128 (shaPadZeros shaIdx (shaPadCount (shaLenMod qmsg%ux0 0)) nil)))"
                   " (cons shaC32 (cons (shaBits shaPow32 (natMul 8 (shaLen qmsg%ux0 0))) nil))))", text, text, text);
  put_line(&blocks_name, "qblocks%u", text);
  snprintf(name, sizeof name, "qcp%u", text);
  append_claim(builder, name, "List (List (List Nat))", &parse, &blocks_name);
  char hex[65];
  for (Nat index = 0; index < 64; index++) {
    Nat digit = (blocks[count - 1].after[index / 8] >> (28 - 4 * (index % 8))) & 15;
    hex[index] = (char)(digit < 10 ? 48 + digit : 87 + digit);
  }
  hex[64] = 0;
  snprintf(name, sizeof name, "qh%u", text);
  append_head(builder, name, "Text");
  append_literal(builder, hex);
  append_string(builder, "\n");
  Line left = {0}, right = {0};
  put_line(&left, "(shaHexWords qs%ux%ux0 textEnd)", text, count);
  put_line(&right, "qh%u", text);
  snprintf(name, sizeof name, "qch%u", text);
  append_claim(builder, name, "Text", &left, &right);
  return 1;
}

/* The Body payloads (schema.def:272 to :280): createsX carries an X. */
static const char *const bodies[] = {"Party", "Membership", "Commercial", "Commitment",
                                     "Artifact", "Event", "Assignment", "Policy"};

/* The lastEvent setter (schema.def:123 and :153: field 6 of 7 of makeParty,
   field 10 of 10 of makeCommercial). M7 design item 5 (delta A-4): on a
   Commercial, first the stage from the after payload of the event Body e
   (stageAfter, as program.c projection_moved). M7 parts B1 and B2a (deltas
   MB-6 and MB-9, Q-M7-15 (a)): on a Party, the displayName, legalName,
   identifiers, attrs and deletedBy after e (partyName, partyLegal,
   partyIdents, partyAttrs and partyDeleted, as program.c projection_party).
   M7 part B2b (MB-11): this setter changes the subject record only. The
   Merge repoint of the other records is recordsMerged (certificate.def),
   which recordsAdd runs after this setter. */
static const char last_event[] =
    "\ndef ledgerLastEvent : Text -> Body -> Body -> Body := fun (h : Text) (e : Body) (b : Body) => case b as s1 in Body return Body with"
    " | createsParty (m : Party) => createsParty (case m as s2 in Party return Party with | makeParty (x0 : KindParty)"
    " (x1 : Text) (x2 : Option Text) (x3 : List Identifier) (x4 : Attrs) (x5 : Option (Ref kindEvent))"
    " (x6 : Option (Ref kindEvent)) => makeParty x0 (partyName e x1) (partyLegal e x2) (partyIdents h e x3) (partyAttrs e x4)"
    " (some (refTo (hashOf h))) (partyDeleted h e x6))"
    " | createsMembership (m : Membership) => createsMembership m"
    " | createsCommercial (m : Commercial) => createsCommercial (case m as s2 in Commercial return Commercial with"
    " | makeCommercial (x0 : KindCommercial) (x1 : Text) (x2 : Ref kindParty) (x3 : Text) (x4 : Option Nat) (x5 : Text)"
    " (x6 : Option Text) (x7 : CommercialStatus) (x8 : Attrs) (x9 : Option (Ref kindEvent))"
    " => makeCommercial x0 x1 x2 (stageAfter e x3) x4 x5 x6 x7 x8 (some (refTo (hashOf h))))"
    " | createsCommitment (m : Commitment) => createsCommitment m | createsArtifact (m : Artifact) => createsArtifact m"
    " | createsEvent (m : Event) => createsEvent m | createsAssignment (m : Assignment) => createsAssignment m"
    " | createsPolicy (m : Policy) => createsPolicy m\n";

/* The rows that ledgerUser_write cites, before the lowered source: the rows
   of each hashed text, ledgerHashOf (a hit gives qhK, the miss arm is not
   taken), ledgerHs, ledgerUser_write, ledgerLastEvent and the record
   encoder ledgerPut ({"ref":"H","type":"X","value":V}, program.c:1202). */
static int append_write_rows(TextBuilder *builder, const Hashed *hashed, Text *refusal) {
  Text bytes = {0}, ends = {0};
  if (hashed != NULL) {
    bytes = builder_text(&hashed->bytes);
    ends = builder_text(&hashed->ends);
  }
  /* The sum rule: the text K takes (len + 8) / 64 + 1 blocks (FIPS 180-4 padding). */
  Nat blocks = 0;
  for (Nat text = 0, start = 0; text < ends.size; start = ends.items[text], text++)
    blocks += (ends.items[text] - start + 8) / 64 + 1;
  if (blocks > 24) return refuse(refusal, "more than 24 hash blocks");
  for (Nat text = 0, start = 0; text < ends.size; start = ends.items[text], text++) {
    Text message = {0};
    message.items = bytes.items + start;
    message.size = ends.items[text] - start;
    if (!append_hashed(builder, message, text, refusal)) return 0;
  }
  append_string(builder, "\ndef ledgerHashOf : Text -> Text := fun (m : Text) => ");
  for (Nat text = 0; text < ends.size; text++) {
    append_string(builder, "(case (textSame m qmsg");
    append_nat(builder, text);
    append_string(builder, "x0) as s");
    append_nat(builder, text + 1);
    append_string(builder, " in Flag return Text with | flagNo => ");
  }
  append_string(builder, "sha256Hex m textEnd");
  for (Nat text = ends.size; text > 0; text--) {
    append_string(builder, " | flagYes => qh");
    append_nat(builder, text - 1);
    append_string(builder, ")");
  }
  append_string(builder, "\n\ndef ledgerHs : Entry -> Text := fun (e : Entry) => ledgerHashOf (encodeEntry e textEnd)\n");
  append_string(builder, last_event);
  append_string(builder, "\ndef ledgerUser_write : Log -> Write -> Step := writeWith ledgerLastEvent ledgerHs\n");
  /* M5 delta E-1 (c), Ruling Q-M5-42 (a): the builtin read under its own
     name. A user def of read lowers to ledgerUser_read, and the kernel
     refuses a second def of a name. */
  append_string(builder, "\ndef ledgerReadPath : Type 1 := (answer : Type 0) -> Log -> Query answer -> answer\n");
  append_string(builder, "\ndef ledgerRead : ledgerReadPath := fun (answer : Type 0) (log : Log) (query : Query answer) => "
                         "readWithH ledgerLastEvent (hsMap ledgerHs log) answer log query\n");
  append_string(builder, "\ndef ledgerPut : Text -> Body -> Text -> Text := fun (h : Text) (b : Body) (tail : Text) => ");
  open_bytes(builder, "{\"ref\":\"");
  append_string(builder, "(textThen h ");
  open_bytes(builder, "\",\"type\":\"");
  append_string(builder, "(case b as s1 in Body return Text with");
  for (Nat body = 0; body < sizeof bodies / sizeof bodies[0]; body++) {
    char value[64];
    snprintf(value, sizeof value, "%s\",\"value\":", bodies[body]);
    const char *parts[] = {" | creates", bodies[body], " (m : ", bodies[body], ") => "};
    for (Nat index = 0; index < sizeof parts / sizeof parts[0]; index++) append_string(builder, parts[index]);
    open_bytes(builder, value);
    append_string(builder, "(encode");
    append_string(builder, bodies[body]);
    append_string(builder, " m (textByte 125 tail))");
    close_chain(builder, strlen(value));
  }
  append_string(builder, "))");
  close_chain(builder, strlen("{\"ref\":\"") + strlen("\",\"type\":\""));
  append_string(builder, "\n");
  return 1;
}

static int text_has(Text text, Nat at, const char *word) {
  Nat size = strlen(word);
  if (at + size > text.size) return 0;
  for (Nat index = 0; index < size; index++)
    if (text.items[at + index] != (unsigned char)word[index]) return 0;
  return 1;
}

/* The lexer whitespace and line comments between lowered source tokens. */
static Nat skip_trivia(Text source, Nat at) {
  while (at < source.size) {
    Nat byte = source.items[at];
    if (byte == 32 || byte == 9 || byte == 10 || byte == 13) {
      at++;
    } else if (text_has(source, at, "--")) {
      while (at < source.size && source.items[at] != 10 && source.items[at] != 13) at++;
    } else {
      break;
    }
  }
  return at;
}

/* The end of the name token at at: at itself when no name byte is there. */
static Nat name_end(Text text, Nat at) {
  while (at < text.size && name_byte(text.items[at])) at++;
  return at;
}

/* 1 when text holds the size items of other from from at at. */
static int same_items(Text text, Nat at, Text other, Nat from, Nat size) {
  if (at + size > text.size || from + size > other.size) return 0;
  for (Nat index = 0; index < size; index++)
    if (text.items[at + index] != other.items[from + index]) return 0;
  return 1;
}

/* The start of the body after := of the lowered def of the instance NAME,
   or lowered.size when there is none. lower_source replaces string
   literals, so only comments can hide tokens. */
static Nat def_body(Text lowered, Text name) {
  Nat prefix = strlen(user_prefix);
  for (Nat at = 0; at < lowered.size; at++) {
    at = skip_trivia(lowered, at);
    if (!text_has(lowered, at, "def") ||
        (at > 0 && name_byte(lowered.items[at - 1])) ||
        (at + 3 < lowered.size && name_byte(lowered.items[at + 3]))) continue;
    Nat start = skip_trivia(lowered, at + 3);
    if (!text_has(lowered, start, user_prefix) || start + prefix + name.size > lowered.size) continue;
    Nat end = start + prefix, index = 0;
    while (index < name.size && lowered.items[end + index] == name.items[index]) index++;
    if (index < name.size || (end + index < lowered.size && name_byte(lowered.items[end + index]))) continue;
    Nat body = end + index;
    while (body < lowered.size) {
      body = skip_trivia(lowered, body);
      if (text_has(lowered, body, ":=")) break;
      if (body < lowered.size) body++;
    }
    return body == lowered.size ? body : skip_trivia(lowered, body + 2);
  }
  return lowered.size;
}

/* 1 when the lowered def of the instance NAME has the head ledgerUser_write. */
static int writes_head(Text lowered, Text name) {
  Nat body = def_body(lowered, name);
  return text_has(lowered, body, "ledgerUser_write") && (body + 16 >= lowered.size || !name_byte(lowered.items[body + 16]));
}

/* The start of the first def token at or after at, or text.size. */
static Nat next_def(Text text, Nat at) {
  for (at = skip_trivia(text, at); at < text.size; at = skip_trivia(text, at)) {
    Nat stop = name_end(text, at);
    if (stop > at && same_word(text, at, stop - at, "def")) return at;
    at = stop > at ? stop : at + 1;
  }
  return text.size;
}

/* 1 when a name token in [at, end) of text is word. */
static int has_token(Text text, Nat at, Nat end, const char *word) {
  for (at = skip_trivia(text, at); at < end; at = skip_trivia(text, at)) {
    Nat stop = name_end(text, at);
    if (stop > at && same_word(text, at, stop - at, word)) return 1;
    at = stop > at ? stop : at + 1;
  }
  return 0;
}

/* 1 when [from, end) of text holds a binder of word: a name token equal to
   word, with a colon that is not := after it and no def before it. */
static int binder_in(Text text, Nat from, Nat end, Text word) {
  int head = 0;
  for (Nat at = skip_trivia(text, from); at < end; at = skip_trivia(text, at)) {
    Nat stop = name_end(text, at), next = skip_trivia(text, stop);
    int colon = next < text.size && text.items[next] == 58 && (next + 1 == text.size || text.items[next + 1] != 61);
    if (stop - at == word.size && !head && colon && same_items(text, at, word, 0, word.size)) return 1;
    head = stop > at && same_word(text, at, stop - at, "def");
    at = stop > at ? stop : at + 1;
  }
  return 0;
}

/* A local binder is in scope after its closing parenthesis, until the
   enclosing group ends or the definition's type annotation ends at :=.
   The binder's own name is a declaration, rather than a builtin site. */
static int bound_at(Text text, Nat from, Nat at, Text word) {
  Nat after = skip_trivia(text, at + word.size);
  if (after < text.size && text.items[after] == 58 && !text_has(text, after, ":=")) return 1;
  for (Nat start = skip_trivia(text, from); start < at; start = skip_trivia(text, start)) {
    Nat stop = name_end(text, start), colon = skip_trivia(text, stop);
    if (stop - start == word.size && text_has(text, colon, ":") && !text_has(text, colon, ":=") &&
        same_items(text, start, word, 0, word.size)) {
      Nat end = skip_trivia(text, colon + 1), depth = 0;
      for (; end < text.size; end = skip_trivia(text, end + 1)) {
        if (text.items[end] == 40) depth++;
        if (text.items[end] == 41) {
          if (depth == 0) break;
          depth--;
        }
        if (text_has(text, end, ":=")) break;
      }
      if (end < at && text.items[end] == 41) {
        depth = 0;
        for (end = skip_trivia(text, end + 1); end < at; end = skip_trivia(text, end + 1)) {
          if (text_has(text, end, ":=")) break;
          if (text.items[end] == 40) depth++;
          if (text.items[end] == 41) {
            if (depth == 0) break;
            depth--;
          }
        }
        if (end == at) return 1;
      }
    }
    start = stop > start ? stop : start + 1;
  }
  return 0;
}

/* The ledgerLogs kind of the instance at found[at] (program.c:1030 to
   :1038): 1 for the type text List (Entry), 2 for a Step with the head
   ledgerUser_write (its stepLog), else 0. */
static Nat log_kind(Text output, Text found, Nat at, Text lowered) {
  Text name = {0};
  name.items = output.items + found.items[at];
  name.size = found.items[at + 1];
  Nat type = found.items[at + 2], size = found.items[at + 3];
  if (size == 12 && text_has(output, type, "List (Entry)")) return 1;
  return size == 4 && text_has(output, type, "Step") && writes_head(lowered, name) ? 2 : 0;
}

/* The ledgerLogs index K of the log argument of the read site that ends at
   at: after one type argument (a parenthesized group or one name), a name
   token before end that names a kind 1 log with no binder but its def.
   found.size when there is none. */
static Nat site_log(Text lowered, Nat at, Nat end, Text output, Text found) {
  Nat type = skip_trivia(lowered, at), name = type < end ? name_end(lowered, type) : end;
  if (type < end && lowered.items[type] == 40) {
    Nat depth = 0;
    for (name = type; name < end; name = skip_trivia(lowered, name + 1)) {
      if (lowered.items[name] == 40) depth++;
      if (lowered.items[name] == 41) depth--;
      if (depth == 0) break;
    }
    name++;
  }
  name = skip_trivia(lowered, name);
  Nat stop = name < end ? name_end(lowered, name) : name, prefix = strlen(user_prefix);
  if (stop == name || !text_has(lowered, name, user_prefix)) return found.size;
  Text word = {0};
  word.items = lowered.items + name;
  word.size = stop - name;
  if (binder_in(lowered, 0, lowered.size, word)) return found.size;
  for (Nat entry = 0, logs = 0; entry + 4 <= found.size; entry += 4) {
    Nat kind = log_kind(output, found, entry, lowered);
    if (kind == 1 && found.items[entry + 1] + prefix == word.size &&
        same_items(lowered, name + prefix, output, found.items[entry], found.items[entry + 1])) return logs;
    if (kind != 0) logs++;
  }
  return found.size;
}

/* The lowered source with its builtin read sites named (M5 delta E-1 (c),
   Ruling Q-M5-42 (a)). A ledgerUser_read reference before the end of the
   first def of ledgerUser_read, outside a local binder's scope, is the
   builtin (definitions are nonrecursive). At an application whose log
   argument names a kind 1 log of ledgerLogs with no binder but its def, the
   site becomes readWithH ledgerLastEvent ledgerHsK (the bind row ties
   ledgerHsK to that log); any other builtin site becomes ledgerRead. */
static Text read_sites(Text lowered, Text output, Text found) {
  TextBuilder sites = builder_new();
  Nat user = lowered.size, from = 0, last = 0;
  for (Nat at = next_def(lowered, 0); at < lowered.size && user == lowered.size; at = next_def(lowered, at + 3)) {
    Nat head = skip_trivia(lowered, at + 3);
    if (same_word(lowered, head, name_end(lowered, head) - head, "ledgerUser_read")) user = next_def(lowered, head);
  }
  for (Nat at = 0; at < lowered.size;) {
    Nat start = skip_trivia(lowered, at), stop = name_end(lowered, start);
    append_items(&sites, lowered.items + at, start - at);
    if (start == lowered.size) break;
    if (stop == start) {
      last = lowered.items[start];
      builder_push(&sites, last);
      at = start + 1;
      continue;
    }
    Text word = {0};
    word.items = lowered.items + start;
    word.size = stop - start;
    if (same_word(lowered, start, word.size, "def")) from = start;
    int site = start < user && same_word(lowered, start, word.size, "ledgerUser_read");
    Nat end = site ? next_def(lowered, stop) : stop;
    if (site && !bound_at(lowered, from, start, word)) {
      int head = !name_byte(last) && last != 41;
      Nat log = head ? site_log(lowered, stop, end, output, found) : found.size;
      append_string(&sites, log < found.size ? "readWithH ledgerLastEvent ledgerHs" : "ledgerRead");
      if (log < found.size) append_nat(&sites, log);
    } else {
      append_items(&sites, word.items, word.size);
    }
    last = lowered.items[stop - 1];
    at = stop;
  }
  return builder_text(&sites);
}

/* The end of the JSON string whose first byte after the quote is at at. */
static Nat string_end(Text json, Nat at) {
  while (at < json.size && json.items[at] != 34) at += json.items[at] == 92 ? 2 : 1;
  return at < json.size ? at + 1 : json.size;
}

/* The end of the JSON value at at: a string, a nested array or object, or a
   scalar that runs to , } or ]. */
static Nat value_end(Text json, Nat at) {
  Nat depth = 0;
  while (at < json.size) {
    Nat byte = json.items[at++];
    if (byte == 34) at = string_end(json, at);
    if (byte == 91 || byte == 123) depth++;
    if ((byte == 44 || byte == 93 || byte == 125) && depth == 0) return at - 1;
    if (byte == 93 || byte == 125) depth--;
    if (depth == 0 && (byte == 34 || byte == 93 || byte == 125)) return at;
  }
  return at;
}

/* The hashed text whose bytes output holds at at, with , or ] after them,
   or ends.size when there is none. An entry text is not empty. */
static Nat hashed_at(Text output, Nat at, Text bytes, Text ends) {
  for (Nat text = 0, start = 0; text < ends.size; start = ends.items[text], text++) {
    Nat size = ends.items[text] - start;
    if (size > 0 && at + size < output.size && (output.items[at + size] == 44 || output.items[at + size] == 93) &&
        same_items(output, at, bytes, start, size)) return text;
  }
  return ends.size;
}

/* def ledgerHsK for each log K of ledgerLogs (M5 delta E-1 (b)): the hashed
   text of each item of its JSON array, in log order. Each item has the bytes
   of one hashed text (json.c:153), and the texts are in first-hash order, so
   the match is by bytes. No match ends the list: the bind row ledgerBindK
   then fails in the kernel. */
static void append_hash_lists(TextBuilder *builder, Text output, Text found, Text lowered, const Hashed *hashed) {
  Text bytes = {0}, ends = {0};
  if (hashed != NULL) {
    bytes = builder_text(&hashed->bytes);
    ends = builder_text(&hashed->ends);
  }
  for (Nat at = 0, logs = 0; at + 4 <= found.size; at += 4) {
    Nat kind = log_kind(output, found, at, lowered), items = 0;
    if (kind == 0) continue;
    Nat item = found.items[at + 2] + found.items[at + 3] + strlen("\",\"value\":[") + (kind == 2 ? strlen("{\"log\":") : 0);
    append_string(builder, "\ndef ledgerHs");
    append_nat(builder, logs++);
    append_string(builder, " : List Text := ");
    for (Nat text = hashed_at(output, item, bytes, ends); text < ends.size; text = hashed_at(output, item, bytes, ends)) {
      append_string(builder, "(cons qh");
      append_nat(builder, text);
      append_string(builder, " ");
      item += ends.items[text] - (text > 0 ? ends.items[text - 1] : 0) + 1;
      items++;
      if (output.items[item - 1] == 93) break;
    }
    append_string(builder, "nil");
    close_chain(builder, items);
    append_string(builder, "\n");
  }
}

/* The small read claim of the instance at found[at] (Ruling Q-M5-41 (a)):
   ledgerText_N, the bytes of its JSON value, and ledgerRead_N, the claim
   that its encoder TERM gives them. */
static void append_read_claim(TextBuilder *claims, Text output, Text found, Nat at, const char *term) {
  Nat from = found.items[at + 2] + found.items[at + 3] + strlen("\",\"value\":");
  Nat size = value_end(output, from) - from;
  const Nat *name = output.items + found.items[at];
  Nat length = found.items[at + 1];
  TextBuilder left = builder_new();
  append_string(&left, "(");
  append_string(&left, term);
  append_string(&left, " ");
  append_string(&left, user_prefix);
  append_items(&left, name, length);
  append_string(&left, " textEnd)");
  append_string(claims, "\ndef ledgerText_");
  append_items(claims, name, length);
  append_string(claims, " : Text := ");
  open_items(claims, output.items + from, size);
  append_string(claims, "textEnd");
  close_chain(claims, size);
  append_string(claims, "\n\ndef ledgerRead_");
  append_items(claims, name, length);
  append_string(claims, " : MechEq Text ");
  builder_append(claims, builder_text(&left));
  append_string(claims, " ledgerText_");
  append_items(claims, name, length);
  append_string(claims, " := mechRefl Text ");
  builder_append(claims, builder_text(&left));
  append_string(claims, "\n");
}

/* 1 when the lowered def of the instance NAME reads (ledgerRead or
   readWithH) before the next def: it gets a small read claim. */
static int reads_in(Text sites, Text name) {
  Nat body = def_body(sites, name), end = next_def(sites, body);
  return has_token(sites, body, end, "ledgerRead") || has_token(sites, body, end, "readWithH");
}

/* 0 with a refusal when the instance at found[at] is a Step whose written
   mark (Hashed written) and the writes_head rule differ: the JSON and
   ledgerLogs would not agree on its log. With no marks, the mark is 0. */
static int step_covered(Text output, Text found, Nat at, Text lowered, Text marks, Text *refusal) {
  Text name = {0};
  name.items = output.items + found.items[at];
  name.size = found.items[at + 1];
  if (found.items[at + 3] != 4 || !text_has(output, found.items[at + 2], "Step")) return 1;
  Nat mark = at / 4 < marks.size ? marks.items[at / 4] : 0;
  return (mark == 1) == writes_head(lowered, name) || refuse(refusal, "this step");
}

/* def ledgerLogs, the feeding logs in definition order (program.c:1030 to
   :1038): an instance of type text List (Entry) gives itself; a Step
   instance with the head ledgerUser_write gives its stepLog. Then (M5 delta
   E-1 (b)) ledgerLogHs, the hash lists ledgerHsK in the same order, and for
   each log the bind row ledgerBindK: hsMap ledgerHs of the log is
   ledgerHsK. Gives the log count. */
static Nat append_logs(TextBuilder *builder, Text output, Text found, Text lowered) {
  Nat logs = 0;
  TextBuilder list = builder_new();
  TextBuilder hashes = builder_new();
  TextBuilder binds = builder_new();
  for (Nat at = 0; at + 4 <= found.size; at += 4) {
    Nat kind = log_kind(output, found, at, lowered);
    if (kind == 0) continue;
    TextBuilder log = builder_new();
    append_string(&log, kind == 2 ? "(stepLog " : "");
    append_string(&log, user_prefix);
    append_items(&log, output.items + found.items[at], found.items[at + 1]);
    append_string(&log, kind == 2 ? ")" : "");
    append_string(&list, "(cons ");
    builder_append(&list, builder_text(&log));
    append_string(&list, " ");
    append_string(&hashes, "(cons ledgerHs");
    append_nat(&hashes, logs);
    append_string(&hashes, " ");
    append_string(&binds, "\ndef ledgerBind");
    append_nat(&binds, logs);
    append_string(&binds, " : MechEq (List Text) (hsMap ledgerHs ");
    builder_append(&binds, builder_text(&log));
    append_string(&binds, ") ledgerHs");
    append_nat(&binds, logs);
    append_string(&binds, " := mechRefl (List Text) ledgerHs");
    append_nat(&binds, logs);
    append_string(&binds, "\n");
    logs++;
  }
  append_string(builder, "\ndef ledgerLogs : List Log := ");
  builder_append(builder, builder_text(&list));
  append_string(builder, "nil");
  close_chain(builder, logs);
  append_string(builder, "\n\ndef ledgerLogHs : List (List Text) := ");
  builder_append(builder, builder_text(&hashes));
  append_string(builder, "nil");
  close_chain(builder, logs);
  append_string(builder, "\n");
  builder_append(builder, builder_text(&binds));
  return logs;
}

int certificate_module(Text source, Text output, const Hashed *hashed, Text *module, Text *refusal) {
  TextBuilder lowered = builder_new();
  TextBuilder spans = builder_new();
  TextBuilder encoders = builder_new();
  unsigned char made[ALL_COUNT];
  char term[TERM];
  memset(made, 0, sizeof made);
  if (!lower_source(source, &lowered, refusal) || !read_instances(output, &spans, refusal)) return 0;
  append_kinds(&encoders);
  append_families(&encoders, made);
  Text found = builder_text(&spans);
  Text sites = read_sites(builder_text(&lowered), output, found);
  Text marks = {0};
  if (hashed != NULL) marks = builder_text(&hashed->written);
  for (Nat at = 0; at + 4 <= found.size; at += 4)
    if (!instance_encoder(made, output, found.items[at + 2], found.items[at + 3], term, refusal) ||
        !step_covered(output, found, at, sites, marks, refusal))
      return 0;

  TextBuilder builder = builder_new();
  TextBuilder render = builder_new();
  TextBuilder claims = builder_new();
  Table fixed = TABLE(fixed_rows);
  Nat eq = eq_rows(fixed), lits = 0, opens = 0;
  append_rows(&builder, fixed, 0, eq, 0);
  append_core(&builder, 1);
  append_rows(&builder, fixed, eq, fixed.count, 1);
  builder_append(&builder, builder_text(&encoders));
  append_string(&builder, "\n");
  if (!append_write_rows(&builder, hashed, refusal)) return 0;
  append_hash_lists(&builder, output, found, sites, hashed);
  builder_append(&builder, sites);
  append_string(&builder, "\n");
  Nat logs = append_logs(&builder, output, found, sites);
  for (Nat at = 0; at + 4 <= found.size; at += 4) {
    TextBuilder piece = builder_new();
    append_string(&piece, at == 0 ? json_head : "},");
    append_string(&piece, "{\"name\":\"");
    append_items(&piece, output.items + found.items[at], found.items[at + 1]);
    append_string(&piece, "\",\"type\":\"");
    append_items(&piece, output.items + found.items[at + 2], found.items[at + 3]);
    append_string(&piece, "\",\"value\":");
    opens += append_lits(&builder, &render, builder_text(&piece), &lits);
    instance_encoder(made, output, found.items[at + 2], found.items[at + 3], term, refusal);
    Text name = {0};
    name.items = output.items + found.items[at];
    name.size = found.items[at + 1];
    if (reads_in(sites, name)) append_read_claim(&claims, output, found, at, term);
    append_string(&render, "(");
    append_string(&render, term);
    append_string(&render, " ");
    append_string(&render, user_prefix);
    append_items(&render, output.items + found.items[at], found.items[at + 1]);
    append_string(&render, " ");
    opens++;
  }
  TextBuilder end = builder_new();
  append_string(&end, found.size > 0 ? "}]" : json_head);
  if (found.size == 0) append_string(&end, "]}\n");
  if (found.size > 0 && logs == 0) append_string(&end, "}\n");
  opens += append_lits(&builder, &render, builder_text(&end), &lits);
  /* M5 delta D-1 (b): the records (program.c:1300), then the TAIL }LF. The
     hash lists of delta E-1 (b) give the record hashes. */
  if (logs > 0) {
    TextBuilder tail = builder_new();
    append_string(&render, "(recordsThen ledgerPut (recordsLogsH ledgerLogs ledgerLogHs ledgerLastEvent nil) ");
    opens++;
    append_string(&tail, "}\n");
    opens += append_lits(&builder, &render, builder_text(&tail), &lits);
  }
  builder_append(&builder, builder_text(&claims));
  append_string(&builder, "\ndef certificateRender : Text := ");
  builder_append(&builder, builder_text(&render));
  append_string(&builder, "textEnd");
  close_chain(&builder, opens);
  append_string(&builder, "\n");
  TextBuilder bytes = builder_new();
  builder_append(&bytes, output);
  builder_push(&bytes, 10);
  append_chunks(&builder, "certificateBytes", builder_text(&bytes));
  append_string(&builder, "\ndef certificate : MechEq Text certificateRender certificateBytes0 := "
                          "mechRefl Text certificateRender\n");
  *module = builder_text(&builder);
  return 1;
}
