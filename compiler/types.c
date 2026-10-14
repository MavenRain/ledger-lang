/* Types: JSON null forms, canonical names, levels, constructor plans,
   function types and reserved names (port of types.mech, no fuel). */
#include "ledger.h"

static const LType nat_type = {.tag = TY_NAT};
static const LType text_type = {.tag = TY_TEXT};
static const LType flag_type = {.tag = TY_FLAG};
static const LType value_type = {.tag = TY_VALUE};
static const LType values_type = {.tag = TY_VALUES};
static const LType attrs_type = {.tag = TY_ATTRS};
static const LType hash_type = {.tag = TY_HASH};

/* Option and Value are the only types whose JSON form can be null. */
Nat encodes_null(const LType *ty) {
  switch (ty->tag) {
    case TY_NAT: case TY_TEXT: case TY_FLAG: case TY_VALUES: case TY_ATTRS:
    case TY_KIND: case TY_HASH: case TY_REF: case TY_SCHEMA: case TY_LIST:
    case TY_PROD: case TY_SUM: case TY_UNIVERSE: case TY_QUERY: case TY_ARROW:
    case TY_SIGMA:
      return 0;
    case TY_VALUE: case TY_OPTION: case TY_EQ:
      return 1;
  }
  return 0;
}

Nat has_arguments(const LTypes *types) { return types != NULL; }

const LTypes *plan_arguments(const Plan *selected) { return selected->arguments; }

static Text unary_type_name(Text head, Text arg) {
  return append_text(head, text_byte(32, text_byte(40, append_text(arg, text_one(41)))));
}

static Text binary_type_name(Text head, Text a, Text b) {
  return append_text(unary_type_name(head, a), text_byte(32, text_byte(40, append_text(b, text_one(41)))));
}

typedef struct SigmaKey SigmaKey;
struct SigmaKey {
  Nat marker;
  Nat depth;
  Text name;
  const SigmaKey *outer;
};

/* Bound markers use a three-item name, distinct from a free marker's two
   items. Their lexical depth is independent of the surrounding signature. */
static Text bound_key(Nat depth) { return text_byte(0, text_byte(depth, text_one(0))); }

/* The key form names a bound marker by its depth; the type name uses the
   binder name of its Sigma. */
static Text marker_key(Nat key, Nat marker, const SigmaKey *scope) {
  for (; scope != NULL; scope = scope->outer)
    if (scope->marker == marker) return key ? bound_key(scope->depth) : scope->name;
  return marker_name(marker);
}

/* Key 2 is the key of the declared-type check (D-C1): a side that is a group
   around a variable is the variable. */
static Val bare_side(Val side) {
  if (side.kind != VAL_TERM) return side;
  const Term *node = bare_term(side.node);
  return node->tag == TERM_VAR ? (Val){.kind = VAL_VAR, .index = node->index} : (Val){.kind = VAL_TERM, .node = node};
}

/* The letter that the lexer reads after a backslash for this byte, or 0. */
static Nat escape_letter(Nat byte) {
  switch (byte) {
    case 34: case 92: return byte;
    case 10: return 110;
    case 13: return 114;
    case 9: return 116;
    case 8: return 98;
    case 12: return 102;
  }
  return 0;
}

static Text string_source(Text text) {
  TextBuilder builder = builder_new();
  builder_push(&builder, 34);
  for (; !text_is_end(text); text = text_tail(text)) {
    Nat letter = escape_letter(text_head(text));
    if (letter != 0) builder_push(&builder, 92);
    builder_push(&builder, letter != 0 ? letter : text_head(text));
  }
  builder_push(&builder, 34);
  return builder_text(&builder);
}

/* The lexer gives `:=` as 61, `->` as 62 and `=>` as 63. */
static Text mark_source(Nat mark) {
  switch (mark) {
    case 61: return text_byte(58, text_one(61));
    case 62: return text_byte(45, text_one(62));
    case 63: return text_byte(61, text_one(62));
  }
  return text_one(mark);
}

/* One token of token_text in source form (2 identifier, 3 number, 4 string,
   5 mark). */
static Text token_source(Nat kind, Nat item, Text word) {
  switch (kind) {
    case 2: return word;
    case 3: return number_text(item);
    case 4: return string_source(word);
  }
  return mark_source(item);
}

/* The display text of an open side (key 0) is its term in source form
   (USER rulings 2 and 3): the term_text tokens, decoded, with a space between
   two tokens but not after `(` and not before `)`. */
static Text side_source(const Term *node) {
  TextBuilder builder = builder_new();
  Nat open = 1;
  Text rest = term_text(node);
  while (!text_is_end(rest)) {
    Nat kind = text_head(rest);
    Nat item = text_head(text_tail(rest));
    Nat size = kind == 2 || kind == 4 ? item : 0;
    if (!open && !(kind == 5 && item == 41)) builder_push(&builder, 32);
    builder_append(&builder, token_source(kind, item, text_take(text_drop(rest, 2), size)));
    open = kind == 5 && item == 40;
    rest = text_drop(rest, 2 + size);
  }
  return builder_text(&builder);
}

static Text side_key(Nat key, Val given, const SigmaKey *scope) {
  Val side = key == 2 ? bare_side(given) : given;
  if (scope == NULL || side.kind == VAL_CLOSED) return val_text(side);
  if (side.kind == VAL_VAR) return marker_key(key, side.index, scope);
  Nat size = term_marker_bound(side.node);
  const Term **table = arena_alloc(sizeof *table * (size + 1));
  for (Nat index = 0; index < size; index++) {
    const Term *first = term_marker_first(side.node, index);
    table[index] = first == NULL ? NULL : term_var(first->position, 0, marker_key(key, index, scope), index);
  }
  const Term *marked = term_with_markers(side.node, table, size);
  return key == 0 ? side_source(marked) : val_text((Val){.kind = VAL_TERM, .node = marked});
}

/* `Sigma (x : A) (B)`, and `Sigma (A) (B)` for the short form. */
static Text sigma_type_name(const LType *ty, Text a, Text b) {
  if (ty->name.size == 0) return binary_type_name(sSigma, a, b);
  return binary_type_name(sSigma, append_text(ty->name, text_byte(32, text_byte(58, text_byte(32, a)))), b);
}

typedef struct TypeKey TypeKey;
struct TypeKey {
  Text name;
  Nat depth;
  const TypeKey *outer;
};

/* A bound type name uses a delimited depth, distinct from every source name. */
static Text type_name_key(Text name, const TypeKey *scope) {
  for (; scope != NULL; scope = scope->outer)
    if (same_text(name, scope->name))
      return text_byte(0, append_text(number_text(scope->depth), text_one(0)));
  return name;
}

static Text type_text(Nat key, const LType *ty, const SigmaKey *scope, const TypeKey *types) {
  switch (ty->tag) {
    case TY_NAT: return sNat;
    case TY_TEXT: return sText;
    case TY_FLAG: return sFlag;
    case TY_VALUE: return sValue;
    case TY_VALUES: return sValues;
    case TY_ATTRS: return sAttrs;
    case TY_KIND: return sKind;
    case TY_HASH: return sHash();
    case TY_REF: return unary_type_name(sRef(), ty->name);
    case TY_SCHEMA: return key ? type_name_key(ty->name, types) : ty->name;
    case TY_OPTION: return unary_type_name(sOption, type_text(key, ty->left, scope, types));
    case TY_LIST: return unary_type_name(sList, type_text(key, ty->left, scope, types));
    case TY_PROD: return binary_type_name(sProd, type_text(key, ty->left, scope, types), type_text(key, ty->right, scope, types));
    case TY_SUM: return binary_type_name(sSum, type_text(key, ty->left, scope, types), type_text(key, ty->right, scope, types));
    case TY_UNIVERSE: return ty->level == 0 ? sType0 : sType1;
    case TY_EQ:
      return append_text(unary_type_name(sEq, type_text(key, ty->left, scope, types)),
        text_byte(32, text_byte(40, append_text(side_key(key, ty->lhs, scope),
          text_byte(41, text_byte(32, text_byte(40,
            append_text(side_key(key, ty->rhs, scope), text_one(41)))))))));
    case TY_QUERY: return unary_type_name(opsTextQuery(), type_text(key, ty->left, scope, types));
    case TY_ARROW: {
      TypeKey inner = {ty->name, types == NULL ? 0 : types->depth + 1, types};
      const TypeKey *body = ty->name.size == 0 ? types : &inner;
      return text_byte(40, append_text(type_text(key, ty->left, scope, types), text_byte(41, text_byte(32,
        text_byte(45, text_byte(62, text_byte(32, type_text(key, ty->right, scope, body))))))));
    }
    case TY_SIGMA: {
      SigmaKey inner = {ty->level, scope == NULL ? 0 : scope->depth + 1, ty->name, scope};
      Text a = type_text(key, ty->left, scope, types);
      Text b = type_text(key, ty->right, &inner, types);
      if (!key) return sigma_type_name(ty, a, b);
      return binary_type_name(sSigma, append_text(bound_key(inner.depth),
                              text_byte(32, text_byte(58, text_byte(32, a)))), b);
    }
  }
  return text_end();
}

Text type_name(const LType *ty) { return type_text(0, ty, NULL, NULL); }

/* Data types have level 0. Type 0 has level 1 and Type 1 has level 2.
   A Query type is in Type 1, so it has level 1. */
Nat type_level(const LType *ty) {
  switch (ty->tag) {
    case TY_NAT: case TY_TEXT: case TY_FLAG: case TY_VALUE: case TY_VALUES:
    case TY_ATTRS: case TY_KIND: case TY_HASH: case TY_REF: case TY_SCHEMA:
    case TY_OPTION: case TY_LIST: case TY_PROD: case TY_SUM: case TY_EQ:
    case TY_SIGMA:
      return 0;
    case TY_UNIVERSE: return ty->level + 1;
    case TY_QUERY: case TY_ARROW: return 1;
  }
  return 0;
}

/* The type grammar has unique canonical names, so equality of the names is
   structural type equality for this subset. Sigma keys retain free markers
   and compare bound markers by lexical depth. Function keys compare bound
   type names by lexical depth while preserving free type names. */
Nat same_type(const LType *a, const LType *b) {
  return same_text(type_text(1, a, NULL, NULL), type_text(1, b, NULL, NULL));
}

/* D-C1 (USER ruling 3): the declared-type check. A side that is a group
   around a variable compares as the variable, and so does such a group in a
   node. refl keeps the strict equality (same_val). */
Nat same_declared_type(const LType *a, const LType *b) {
  return same_text(type_text(2, a, NULL, NULL), type_text(2, b, NULL, NULL));
}

static const LTypes *cons_type(const LType *head, const LTypes *tail) {
  LTypes *list = arena_alloc(sizeof *list);
  *list = (LTypes){head, tail};
  return list;
}

static int tag_plan(const LTypes *arguments, Nat mode, Text label, Plan *plan) {
  *plan = (Plan){.kind = PLAN_TAG, .arguments = arguments, .mode = mode, .label = label};
  return 1;
}

/* A constructor of a carrier: its name, mode and up to three arguments. */
typedef struct {
  const Text *name;
  Nat mode;
  const LType *a;
  const LType *b;
  const LType *c;
} Carrier;

static const LTypes *carrier_arguments(const Carrier *ctor) {
  return ctor->a == NULL ? NULL : cons_type(ctor->a, ctor->b == NULL ? NULL
    : cons_type(ctor->b, ctor->c == NULL ? NULL : cons_type(ctor->c, NULL)));
}

/* The first constructor whose name equals name, as mech's select chain. */
static int pick(const Carrier *ctors, Nat count, Text name, Plan *plan) {
  for (Nat at = 0; at < count; at++) {
    if (same_text(name, *ctors[at].name)) {
      return tag_plan(carrier_arguments(&ctors[at]), ctors[at].mode, *ctors[at].name, plan);
    }
  }
  return 0;
}

static const Carrier text_ctors[] = {
  {&stextEnd, 3, NULL, NULL, NULL}, {&stextByte, 4, &nat_type, &text_type, NULL}};
static const Carrier flag_ctors[] = {{&sflagNo, 1, NULL, NULL, NULL}, {&sflagYes, 2, NULL, NULL, NULL}};
static const Carrier value_ctors[] = {
  {&svalueNull, 0, NULL, NULL, NULL}, {&svalueFlag, 5, &flag_type, NULL, NULL},
  {&svalueNat, 5, &nat_type, NULL, NULL}, {&svalueText, 5, &text_type, NULL, NULL},
  {&svalueItems, 5, &values_type, NULL, NULL}, {&svalueAttrs, 5, &attrs_type, NULL, NULL}};
static const Carrier values_ctors[] = {
  {&svaluesEnd, 6, NULL, NULL, NULL}, {&svaluesItem, 7, &value_type, &values_type, NULL}};
static const Carrier attrs_ctors[] = {
  {&sattrsEnd, 8, NULL, NULL, NULL}, {&sattrsField, 9, &text_type, &value_type, &attrs_type}};
static const Carrier kind_ctors[] = {
  {&skindParty, 14, NULL, NULL, NULL}, {&skindMembership, 14, NULL, NULL, NULL},
  {&skindCommercial, 14, NULL, NULL, NULL}, {&skindCommitment, 14, NULL, NULL, NULL},
  {&skindArtifact, 14, NULL, NULL, NULL}, {&skindEvent, 14, NULL, NULL, NULL},
  {&skindAssignment, 14, NULL, NULL, NULL}, {&skindPolicy, 14, NULL, NULL, NULL}};

#define COUNT(table) ((Nat)(sizeof table / sizeof table[0]))

int constructor_plan(const LType *ty, Text name, Plan *plan) {
  const LType *index;
  switch (ty->tag) {
    case TY_NAT: case TY_UNIVERSE: case TY_EQ: case TY_ARROW: case TY_SIGMA:
      return 0;
    case TY_HASH:
      return same_text(name, sHashOf()) ? tag_plan(cons_type(&text_type, NULL), 5, sHashOf(), plan) : 0;
    case TY_REF:
      return same_text(name, sRefTo()) ? tag_plan(cons_type(&hash_type, NULL), 15, ty->name, plan) : 0;
    case TY_SCHEMA:
      return schema_constructor_plan(ty->name, name, plan) || ops_constructor_plan(ty->name, name, plan);
    case TY_TEXT: return pick(text_ctors, COUNT(text_ctors), name, plan);
    case TY_FLAG: return pick(flag_ctors, COUNT(flag_ctors), name, plan);
    case TY_VALUE: return pick(value_ctors, COUNT(value_ctors), name, plan);
    case TY_VALUES: return pick(values_ctors, COUNT(values_ctors), name, plan);
    case TY_ATTRS: return pick(attrs_ctors, COUNT(attrs_ctors), name, plan);
    case TY_KIND: return pick(kind_ctors, COUNT(kind_ctors), name, plan);
    case TY_OPTION:
      return same_text(name, snone) ? tag_plan(NULL, 0, snone, plan)
        : same_text(name, ssome) ? tag_plan(cons_type(ty->left, NULL), encodes_null(ty->left) ? 13 : 5, ssome, plan)
        : 0;
    case TY_LIST:
      return same_text(name, snil) ? tag_plan(NULL, 6, snil, plan)
        : same_text(name, scons) ? tag_plan(cons_type(ty->left, cons_type(ty, NULL)), 7, scons, plan)
        : 0;
    case TY_PROD:
      return same_text(name, spair) ? tag_plan(cons_type(ty->left, cons_type(ty->right, NULL)), 10, spair, plan) : 0;
    case TY_SUM:
      return same_text(name, s_inl) ? tag_plan(cons_type(ty->left, NULL), 11, s_inl, plan)
        : same_text(name, sinr) ? tag_plan(cons_type(ty->right, NULL), 12, sinr, plan)
        : 0;
    case TY_QUERY:
      return ops_query_answer(name, &index) && same_type(index, ty->left) ? ops_query_plan(name, plan) : 0;
  }
  return 0;
}

/* A definition of a Query type is a term, but a Query type is not a data
   type. */
Nat is_query_type(const LType *ty) { return ty->tag == TY_QUERY; }

/* A function type is a chain of TY_ARROW. The result of a function type is
   not a function type, so the chain gives the parameter types in order. A
   parameter of this chain has a name that the source cannot contain. A type
   parameter keeps its name, because the later types use it (step D7b). */
const Params *arrow_params(const LType *ty) {
  if (ty->tag != TY_ARROW) return NULL;
  Params *params = arena_alloc(sizeof *params);
  *params = (Params){{ty->name.size != 0 ? ty->name : text_one(32), ty->left}, arrow_params(ty->right)};
  return params;
}

const LType *arrow_result(const LType *ty) {
  return ty->tag == TY_ARROW ? arrow_result(ty->right) : ty;
}

Nat is_arrow_type(const LType *ty) { return arrow_params(ty) != NULL; }

const LType *arrow_type(const Params *params, const LType *result) {
  if (params == NULL) return result;
  LType *arrow = arena_alloc(sizeof *arrow);
  *arrow = (LType){.tag = TY_ARROW,
                   .name = is_type_param(params->head) ? params->head.name : (Text){0},
                   .left = params->head.type,
                   .right = arrow_type(params->tail, result)};
  return arrow;
}

/* A definition of a data type or of a Query type is a term. */
Nat is_term_type(const LType *ty) { return type_level(ty) == 0 || is_query_type(ty); }

/* A Query constructor does not check against a Query type of another
   answer. */
Text unknown_name(const LType *expected, Text name) {
  const LType *index;
  return ops_query_answer(name, &index) && is_query_type(expected) ? eQueryIndex() : eUnknown;
}

static Nat any_text(const Text *const *texts, Nat count, Text name) {
  for (Nat at = 0; at < count; at++) {
    if (same_text(name, *texts[at])) return 1;
  }
  return 0;
}

static const Text *const primitive_names[] = {
  &sNat, &sText, &sFlag, &sValue, &sValues, &sAttrs, &sKind, &sOption, &sList, &sProd, &sSum,
  &sdef, &srec, &smu, &saxiom, &spoly, &sspecialize, &stextEnd, &stextByte, &sflagNo, &sflagYes,
  &snone, &ssome, &snil, &scons, &svalueNull, &svalueFlag, &svalueNat, &svalueText, &svalueItems,
  &svalueAttrs, &svaluesEnd, &svaluesItem, &sattrsEnd, &sattrsField, &spair, &s_inl, &sinr,
  &skindParty, &skindMembership, &skindCommercial, &skindCommitment, &skindArtifact, &skindEvent,
  &skindAssignment, &skindPolicy};

/* Forms of SPEC.md are reserved, also the forms that later slices
   implement. */
static const Text *const form_names[] = {
  &sType, &sfun, &sSigma, &spack, &switness, &spayload, &sEq, &srefl, &stransport, &ssymm, &strans,
  &scong, &sfirst, &ssecond, &seither, &spure, &smap, &sbind, &sfold, &sunfold, &sfilter};

Nat primitive_reserved_name(Text name) { return any_text(primitive_names, COUNT(primitive_names), name); }

Nat form_reserved_name(Text name) { return any_text(form_names, COUNT(form_names), name); }

Nat reserved_name(Text name) {
  return schema_reserved_name(name) || ops_reserved_name(name) || primitive_reserved_name(name)
    || form_reserved_name(name);
}
