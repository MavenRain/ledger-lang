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
  if (same_word(source, at, size, "WritePath")) return refuse(refusal, "the write path");
  if (same_word(source, at, size, "ReadPath")) return refuse(refusal, "the read path");
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
   Gives 0 with a refusal for an unbound checker name, a write or read path
   and a literal longer than CHUNK bytes. */
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
  if (depth != 1 || at + 1 != json.size || json.items[at] != 125) return refuse(refusal, "the records");
  return 1;
}

static int is_head_row(const Row *line) {
  return line->kind == ROW_CARRIER || line->kind == ROW_FAMILY || line->kind == ROW_AND;
}

static int same_name(const char *name, const char *word, size_t size) {
  return strlen(name) == size && strncmp(name, word, size) == 0;
}

/* The schema.def row of the family or carrier named word[0, size), or SCHEMA_COUNT. */
static Nat family_row(const char *word, size_t size) {
  Nat row = 0;
  while (row < SCHEMA_COUNT && !(is_head_row(&schema_rows[row]) && same_name(schema_rows[row].name, word, size))) row++;
  return row;
}

/* The row after the constructor and field rows of the family at row. */
static Nat family_end(Nat row) {
  Nat end = row + 1;
  while (end < SCHEMA_COUNT && !is_head_row(&schema_rows[end])) end++;
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
    for (size_t index = 0; index < sizeof base_encoders / sizeof base_encoders[0]; index++)
      if (same_name(base_encoders[index][0], type + from, head - from))
        return snprintf(to, TERM, "%s", base_encoders[index][1]) < TERM;
    Nat row = family_row(type + from, head - from);
    if (row == SCHEMA_COUNT || schema_rows[row].kind != ROW_FAMILY || !made[row]) return 0;
    return snprintf(to, TERM, "encode%s", schema_rows[row].name) < TERM;
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
    if (schema_rows[at].kind == ROW_FIELD &&
        !encoder(made, schema_rows[at].arg, 0, strlen(schema_rows[at].arg), term, missing))
      return 0;
  return 1;
}

/* The arm of the constructor at row: only constants gives the name string,
   one constructor the object, else "tag" first and then the fields. */
static void append_arm(TextBuilder *builder, const unsigned char *made, Nat row, int constants, int tagged) {
  const Row *ctor = &schema_rows[row];
  Nat end = row + 1;
  while (end < SCHEMA_COUNT && schema_rows[end].kind == ROW_FIELD) end++;
  append_string(builder, "  | ");
  append_string(builder, ctor->name);
  for (Nat at = row + 1; at < end; at++) {
    append_string(builder, " (x");
    append_nat(builder, at - row - 1);
    append_string(builder, " : ");
    append_string(builder, schema_rows[at].arg);
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
    snprintf(key, TERM, "%s\"%s\":", at == row + 1 && !tagged ? "{" : ",", schema_rows[at].name);
    open_bytes(builder, key);
    encoder(made, schema_rows[at].arg, 0, strlen(schema_rows[at].arg), term, missing);
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

/* One encoder for each schema.def FAMILY row whose field types all have one,
   in row order; made marks them. */
static void append_families(TextBuilder *builder, unsigned char *made) {
  for (Nat row = 0; row < SCHEMA_COUNT; row++) {
    if (schema_rows[row].kind != ROW_FAMILY || !fields_covered(made, row)) continue;
    const char *name = schema_rows[row].name;
    Nat end = family_end(row), ctors = 0;
    int constants = 1;
    for (Nat at = row + 1; at < end; at++) {
      ctors += schema_rows[at].kind == ROW_CONSTRUCTOR;
      constants = constants && schema_rows[at].kind != ROW_FIELD;
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
      if (schema_rows[at].kind == ROW_CONSTRUCTOR) append_arm(builder, made, at, constants, !constants && ctors > 1);
    made[row] = 1;
  }
}

/* The encoder of the instance type json[at, at + size) in to, or 0 with a
   refusal that names the family with no encoder. */
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
static void append_chunks(TextBuilder *builder, Text bytes) {
  Nat count = bytes.size == 0 ? 1 : (bytes.size + CHUNK - 1) / CHUNK;
  for (Nat chunk = count; chunk > 0; chunk--) {
    Nat at = (chunk - 1) * CHUNK;
    Nat take = bytes.size - at < CHUNK ? bytes.size - at : CHUNK;
    append_string(builder, "\ndef certificateBytes");
    append_nat(builder, chunk - 1);
    append_string(builder, " : Text :=\n  ");
    open_items(builder, bytes.items + at, take);
    if (chunk < count) {
      append_string(builder, "certificateBytes");
      append_nat(builder, chunk);
    } else {
      append_string(builder, "textEnd");
    }
    close_chain(builder, take);
    append_string(builder, "\n");
  }
}

int certificate_module(Text source, Text output, Text *module, Text *refusal) {
  TextBuilder lowered = builder_new();
  TextBuilder spans = builder_new();
  TextBuilder encoders = builder_new();
  unsigned char made[SCHEMA_COUNT];
  char term[TERM];
  memset(made, 0, sizeof made);
  if (!lower_source(source, &lowered, refusal) || !read_instances(output, &spans, refusal)) return 0;
  append_kinds(&encoders);
  append_families(&encoders, made);
  Text found = builder_text(&spans);
  for (Nat at = 0; at + 4 <= found.size; at += 4)
    if (!instance_encoder(made, output, found.items[at + 2], found.items[at + 3], term, refusal)) return 0;

  TextBuilder builder = builder_new();
  TextBuilder render = builder_new();
  Table fixed = TABLE(fixed_rows);
  Nat eq = eq_rows(fixed), lits = 0, opens = 0;
  append_rows(&builder, fixed, 0, eq, 0);
  append_core(&builder, 1);
  append_rows(&builder, fixed, eq, fixed.count, 1);
  builder_append(&builder, builder_text(&encoders));
  append_string(&builder, "\n");
  builder_append(&builder, builder_text(&lowered));
  append_string(&builder, "\n");
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
    append_string(&render, "(");
    append_string(&render, term);
    append_string(&render, " ");
    append_string(&render, user_prefix);
    append_items(&render, output.items + found.items[at], found.items[at + 1]);
    append_string(&render, " ");
    opens++;
  }
  TextBuilder end = builder_new();
  append_string(&end, found.size > 0 ? "}]}\n" : json_head);
  if (found.size == 0) append_string(&end, "]}\n");
  opens += append_lits(&builder, &render, builder_text(&end), &lits);
  append_string(&builder, "\ndef certificateRender : Text := ");
  builder_append(&builder, builder_text(&render));
  append_string(&builder, "textEnd");
  close_chain(&builder, opens);
  append_string(&builder, "\n");
  TextBuilder bytes = builder_new();
  builder_append(&bytes, output);
  builder_push(&bytes, 10);
  append_chunks(&builder, builder_text(&bytes));
  append_string(&builder, "\ndef certificate : MechEq Text certificateRender certificateBytes0 := "
                          "mechRefl Text certificateRender\n");
  *module = builder_text(&builder);
  return 1;
}
