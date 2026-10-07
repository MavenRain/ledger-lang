/* The operations: the families of core/ops.def. Load after schema.def. The
   Type 0 families give the record types and the constructor plans. Query is
   the indexed family: its constructors give query plans and answer types. A
   Type 0 definition that is not a function type (Log) is an alias. */
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

/* One row of core/ops.def. arg keeps the second argument as written. */
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
#include "../core/ops.def"
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

/* The header of a family that is not indexed. */
#define PLAIN_HEADER ": Type 0"

/* The text before the body of an alias definition. */
#define ALIAS_HEAD ": Type 0 := "

/* The definition that belongs to a later milestone. The type parser refuses it. */
#define LATER_NAME "ReadPath"

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

static Nat is_plain(Nat row) {
  return strcmp(rows[row].arg, PLAIN_HEADER) == 0;
}

/* Returns 1 and writes the row of the family called name whose class is
   plain (1 for a Type 0 family, 0 for the indexed family). */
static int find_family(Text name, Nat plain, Nat *found) {
  for (Nat row = 0; row < ROW_COUNT; row++) {
    if (is_family(row) && is_plain(row) == plain && text_is(name, rows[row].name)) {
      *found = row;
      return 1;
    }
  }
  return 0;
}

/* Returns the body of the alias called word, or NULL. */
static const char *alias_body(Text word) {
  size_t head = strlen(ALIAS_HEAD);
  for (Nat row = 0; row < ROW_COUNT; row++) {
    const char *rest = rows[row].arg;
    if (rows[row].kind != ROW_DEFINE || !text_is(word, rows[row].name)) continue;
    if (strncmp(rest, ALIAS_HEAD, head) != 0 || strstr(rest, "->") != NULL) return NULL;
    return rest + head;
  }
  return NULL;
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

static const LType *read_type(const char **at);

/* A type word without arguments: a carrier, an alias (its body) or a family. */
static const LType *base_type(Text word) {
  for (Nat index = 0; index < sizeof carriers / sizeof carriers[0]; index++) {
    if (text_is(word, carriers[index].name)) return make_type(carriers[index].tag, text_end(), NULL);
  }
  const char *body = alias_body(word);
  if (body != NULL) return read_type(&body);
  return make_type(TY_SCHEMA, word, NULL);
}

static Nat word_char(char c) {
  return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') || c == '_';
}

static const char *skip_spaces(const char *at) {
  while (*at == ' ') at++;
  return at;
}

/* Reads one word of a type and moves *at past it. */
static Text read_word(const char **at) {
  const char *start = skip_spaces(*at);
  const char *end = start;
  while (word_char(*end)) end++;
  *at = end;
  return text_of_bytes((const unsigned char *)start, (size_t)(end - start));
}

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

/* A type: Ref k, Option T, List T or a word. */
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

/* Returns 1 and writes the row of the constructor called name in the family
   at start, and the counts of the constructors and fields of the family. */
static int find_constructor(Nat start, Text name, Nat *found, Nat *constructors, Nat *fields) {
  Nat matched = 0;
  *constructors = 0;
  *fields = 0;
  for (Nat row = start + 1; row < ROW_COUNT && !is_family(row) && rows[row].kind != ROW_DEFINE; row++) {
    if (rows[row].kind == ROW_FIELD) (*fields)++;
    if (rows[row].kind != ROW_CONSTRUCTOR) continue;
    (*constructors)++;
    if (!matched && text_is(name, rows[row].name)) {
      matched = 1;
      *found = row;
    }
  }
  return matched;
}

/* A family of only nullary constructors gives each constructor a tag plan.
   Otherwise a constructor gets a record plan, with a tag when the family
   has more than one constructor. */
static int family_plan(Nat start, Text name, Plan *plan) {
  Nat at;
  Nat constructors;
  Nat fields;
  if (!find_constructor(start, name, &at, &constructors, &fields)) return 0;
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

int ops_constructor_plan(Text family, Text name, Plan *plan) {
  Nat start;
  if (!find_family(family, 1, &start)) return 0;
  return family_plan(start, name, plan);
}

/* A Query value is tagged with its constructor. It is not an instance. */
int ops_query_plan(Text name, Plan *plan) {
  Nat start;
  if (!find_family(text_of("Query"), 0, &start)) return 0;
  return family_plan(start, name, plan);
}

/* The answer type is the index of the Query type that the constructor gives. */
int ops_query_answer(Text name, const LType **type) {
  Nat start;
  Nat at;
  Nat constructors;
  Nat fields;
  if (!find_family(text_of("Query"), 0, &start)) return 0;
  if (!find_constructor(start, name, &at, &constructors, &fields)) return 0;
  const char *result = rows[at].arg;
  read_word(&result);
  *type = read_atom(&result);
  return 1;
}

/* Log is an alias. The parser gives its definition, so the alias has no own
   name in the output. */
int ops_type(Text name, const LType **type) {
  Nat row;
  const char *body = alias_body(name);
  if (body != NULL) {
    *type = read_type(&body);
    return 1;
  }
  if (!find_family(name, 1, &row)) return 0;
  *type = make_type(TY_SCHEMA, text_of(rows[row].name), NULL);
  return 1;
}

Nat ops_later_type(Text name) {
  return text_is(name, LATER_NAME);
}

/* 1 for the names of the definitions, the families and their constructors.
   Field names are not reserved. */
Nat ops_reserved_name(Text name) {
  for (Nat row = 0; row < ROW_COUNT; row++) {
    if ((is_family(row) || rows[row].kind == ROW_CONSTRUCTOR || rows[row].kind == ROW_DEFINE) && text_is(name, rows[row].name)) return 1;
  }
  return 0;
}
