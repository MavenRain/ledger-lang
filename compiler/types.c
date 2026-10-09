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

Text type_name(const LType *ty) {
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
    case TY_SCHEMA: return ty->name;
    case TY_OPTION: return unary_type_name(sOption, type_name(ty->left));
    case TY_LIST: return unary_type_name(sList, type_name(ty->left));
    case TY_PROD: return binary_type_name(sProd, type_name(ty->left), type_name(ty->right));
    case TY_SUM: return binary_type_name(sSum, type_name(ty->left), type_name(ty->right));
    case TY_UNIVERSE: return ty->level == 0 ? sType0 : sType1;
    case TY_EQ:
      return append_text(unary_type_name(sEq, type_name(ty->left)),
        text_byte(32, text_byte(40, append_text(val_text(ty->lhs), text_byte(41, text_byte(32,
          text_byte(40, append_text(val_text(ty->rhs), text_one(41)))))))));
    case TY_QUERY: return unary_type_name(opsTextQuery(), type_name(ty->left));
    case TY_ARROW:
      return text_byte(40, append_text(type_name(ty->left), text_byte(41, text_byte(32,
        text_byte(45, text_byte(62, text_byte(32, type_name(ty->right))))))));
  }
  return text_end();
}

/* Data types have level 0. Type 0 has level 1 and Type 1 has level 2.
   A Query type is in Type 1, so it has level 1. */
Nat type_level(const LType *ty) {
  switch (ty->tag) {
    case TY_NAT: case TY_TEXT: case TY_FLAG: case TY_VALUE: case TY_VALUES:
    case TY_ATTRS: case TY_KIND: case TY_HASH: case TY_REF: case TY_SCHEMA:
    case TY_OPTION: case TY_LIST: case TY_PROD: case TY_SUM: case TY_EQ:
      return 0;
    case TY_UNIVERSE: return ty->level + 1;
    case TY_QUERY: case TY_ARROW: return 1;
  }
  return 0;
}

/* The type grammar has unique canonical names, so equality of the names is
   structural type equality for this subset. */
Nat same_type(const LType *a, const LType *b) { return same_text(type_name(a), type_name(b)); }

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
    case TY_NAT: case TY_UNIVERSE: case TY_EQ: case TY_ARROW:
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
   parameter of this chain has a name that the source cannot contain. */
const Params *arrow_params(const LType *ty) {
  if (ty->tag != TY_ARROW) return NULL;
  Params *params = arena_alloc(sizeof *params);
  *params = (Params){{text_one(32), ty->left}, arrow_params(ty->right)};
  return params;
}

const LType *arrow_result(const LType *ty) {
  return ty->tag == TY_ARROW ? arrow_result(ty->right) : ty;
}

Nat is_arrow_type(const LType *ty) { return arrow_params(ty) != NULL; }

const LType *arrow_type(const Params *params, const LType *result) {
  if (params == NULL) return result;
  LType *arrow = arena_alloc(sizeof *arrow);
  *arrow = (LType){.tag = TY_ARROW, .left = params->head.type, .right = arrow_type(params->tail, result)};
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
