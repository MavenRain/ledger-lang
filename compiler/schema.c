/* The schema: the families of core/schema.def. The carriers (Text to Ref)
   are built into the compiler. The families from Account on are the added
   families. They give the record types, the constructor plans and the
   reserved names. */
#include <string.h>

#include "ledger.h"

typedef enum {
  ROW_CARRIER,
  ROW_FAMILY,
  ROW_AND,
  ROW_CONSTRUCTOR,
  ROW_FIELD,
  ROW_DEFINE
} RowKind;

/* One row of core/schema.def. arg keeps the second argument as written. */
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
};
#undef CARRIER
#undef FAMILY
#undef AND
#undef CONSTRUCTOR
#undef FIELD
#undef DEFINE

#define ROW_COUNT ((Nat)(sizeof rows / sizeof rows[0]))

/* The plan mode of a constructor in a family of nullary constructors. */
#define TAG_MODE 14

static Nat text_is(Text text, const char *string) {
  size_t size = strlen(string);
  if (text.size != size) return 0;
  for (Nat index = 0; index < text.size; index++) {
    if (text.items[index] != (unsigned char)string[index]) return 0;
  }
  return 1;
}

static Text text_of(const char *string) {
  return text_of_bytes((const unsigned char *)string, strlen(string));
}

static Nat is_family(Nat row) {
  RowKind kind = rows[row].kind;
  return kind == ROW_CARRIER || kind == ROW_FAMILY || kind == ROW_AND;
}

/* The class of the mu group at row, from the class before it: 1 for an
   added family. An AND row and the rows under a family keep the class. */
static Nat added_at(Nat row, Nat added) {
  switch (rows[row].kind) {
    case ROW_CARRIER: return 0;
    case ROW_FAMILY: return 1;
    case ROW_AND:
    case ROW_CONSTRUCTOR:
    case ROW_FIELD:
    case ROW_DEFINE: return added;
  }
  return added;
}

/* Returns 1 and writes the row of the added family called name. */
static int find_family(Text name, Nat *found) {
  Nat added = 0;
  for (Nat row = 0; row < ROW_COUNT; row++) {
    added = added_at(row, added);
    if (added && is_family(row) && text_is(name, rows[row].name)) {
      *found = row;
      return 1;
    }
  }
  return 0;
}

static const LType *make_type(LTypeTag tag, Text name, const LType *left) {
  LType *type = arena_alloc(sizeof *type);
  *type = (LType){.tag = tag, .name = name, .left = left};
  return type;
}

static const struct {
  const char *name;
  LTypeTag tag;
} carriers[] = {
  {"Nat", TY_NAT}, {"Text", TY_TEXT}, {"Flag", TY_FLAG}, {"Value", TY_VALUE},
  {"Values", TY_VALUES}, {"Attrs", TY_ATTRS}, {"Hash", TY_HASH}};

/* A type word without arguments: a carrier, else a family of the schema. */
static const LType *base_type(Text word) {
  for (Nat index = 0; index < sizeof carriers / sizeof carriers[0]; index++) {
    if (text_is(word, carriers[index].name)) return make_type(carriers[index].tag, text_end(), NULL);
  }
  return make_type(TY_SCHEMA, word, NULL);
}

static Nat word_char(char c) {
  return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') || c == '_';
}

static const char *skip_spaces(const char *at) {
  while (*at == ' ') at++;
  return at;
}

/* Reads one word of a field type and moves *at past it. */
static Text read_word(const char **at) {
  const char *start = skip_spaces(*at);
  const char *end = start;
  while (word_char(*end)) end++;
  *at = end;
  return text_of_bytes((const unsigned char *)start, (size_t)(end - start));
}

static const LType *read_type(const char **at);

/* A type argument: a word, or a type in parentheses. */
static const LType *read_atom(const char **at) {
  const char *start = skip_spaces(*at);
  if (*start != '(') {
    *at = start;
    return base_type(read_word(at));
  }
  *at = start + 1;
  const LType *inner = read_type(at);
  *at = skip_spaces(*at) + 1;
  return inner;
}

/* A field type: Ref k, Option T, List T or a word. */
static const LType *read_type(const char **at) {
  Text word = read_word(at);
  if (text_is(word, "Ref")) return make_type(TY_REF, read_word(at), NULL);
  if (text_is(word, "Option")) return make_type(TY_OPTION, text_end(), read_atom(at));
  if (text_is(word, "List")) return make_type(TY_LIST, text_end(), read_atom(at));
  return base_type(word);
}

/* The types of the FIELD rows from row on. */
static const LTypes *field_types(Nat row) {
  if (row >= ROW_COUNT || rows[row].kind != ROW_FIELD) return NULL;
  LTypes *list = arena_alloc(sizeof *list);
  const char *at = rows[row].arg;
  const LType *head = read_type(&at);
  *list = (LTypes){head, field_types(row + 1)};
  return list;
}

/* The names of the FIELD rows from row on. */
static const Texts *field_names(Nat row) {
  if (row >= ROW_COUNT || rows[row].kind != ROW_FIELD) return NULL;
  Texts *list = arena_alloc(sizeof *list);
  *list = (Texts){text_of(rows[row].name), field_names(row + 1)};
  return list;
}

/* A family of only nullary constructors gives each constructor a tag plan.
   Otherwise a constructor gets a record plan, with a tag when the family
   has more than one constructor. */
int schema_constructor_plan(Text family, Text name, Plan *plan) {
  Nat start;
  if (!find_family(family, &start)) return 0;
  Nat constructors = 0;
  Nat fields = 0;
  Nat found = 0;
  Nat at = 0;
  for (Nat row = start + 1; row < ROW_COUNT && !is_family(row) && rows[row].kind != ROW_DEFINE; row++) {
    if (rows[row].kind == ROW_FIELD) fields++;
    if (rows[row].kind != ROW_CONSTRUCTOR) continue;
    constructors++;
    if (!found && text_is(name, rows[row].name)) {
      found = 1;
      at = row;
    }
  }
  if (!found) return 0;
  Text label = text_of(rows[at].name);
  Nat record = fields > 0;
  Nat tagged = record && constructors > 1;
  *plan = (Plan){
      .kind = record ? PLAN_RECORD : PLAN_TAG,
      .arguments = field_types(at + 1),
      .mode = record ? 0 : TAG_MODE,
      .label = record ? text_end() : label,
      .fields = field_names(at + 1),
      .has_tag = tagged,
      .tag = tagged ? label : text_end()};
  return 1;
}

int schema_type(Text name, const LType **type) {
  Nat row;
  if (text_is(name, "Hash")) {
    *type = make_type(TY_HASH, text_end(), NULL);
    return 1;
  }
  if (!find_family(name, &row)) return 0;
  *type = make_type(TY_SCHEMA, text_of(rows[row].name), NULL);
  return 1;
}

/* 1 for Hash, Ref, hashOf, refTo and the names of the added families and
   their constructors. Field names are not reserved. */
Nat schema_reserved_name(Text name) {
  if (text_is(name, "Hash") || text_is(name, "Ref") || text_is(name, "hashOf") || text_is(name, "refTo")) return 1;
  Nat added = 0;
  for (Nat row = 0; row < ROW_COUNT; row++) {
    added = added_at(row, added);
    if (added && (is_family(row) || rows[row].kind == ROW_CONSTRUCTOR) && text_is(name, rows[row].name)) return 1;
  }
  return 0;
}
