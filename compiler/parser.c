/* parser.c: the marks, the kind indexes and the types of a definition.
   A port of parser.mech. parse_kind_index and parse_type take one unit of
   fuel per call and fail with eFuel at the first token position when no
   fuel is left. */
#include "ledger.h"

static const LType nat_type = {.tag = TY_NAT};
static const LType text_type = {.tag = TY_TEXT};
static const LType flag_type = {.tag = TY_FLAG};
static const LType value_type = {.tag = TY_VALUE};
static const LType values_type = {.tag = TY_VALUES};
static const LType attrs_type = {.tag = TY_ATTRS};
static const LType kind_type = {.tag = TY_KIND};

static Tokens tokens_rest(Tokens tokens) { return (Tokens){tokens.items + 1, tokens.size - 1}; }

static const LType *make_type(LTypeTag tag, Text name, Nat level, const LType *left, const LType *right) {
  LType *type = arena_alloc(sizeof *type);
  *type = (LType){.tag = tag, .name = name, .level = level, .left = left, .right = right};
  return type;
}

static const LType *unary_type(LTypeTag tag, const LType *left) { return make_type(tag, text_end(), 0, left, NULL); }

static const LType *binary_type(LTypeTag tag, const LType *left, const LType *right) {
  return make_type(tag, text_end(), 0, left, right);
}

static int parsed_type(const LType *value, Tokens after, const LType **type, Tokens *rest) {
  *type = value;
  *rest = after;
  return 1;
}

int expect_mark(Nat mark, Tokens tokens, Tokens *rest, Failure *failure) {
  if (tokens.size == 0) return fail_at(failure, 0, eDef);
  Token head = tokens.items[0];
  if (head.kind != TOKEN_PUNCTUATION || head.number != mark) return fail_at(failure, head.position, eDef);
  *rest = tokens_rest(tokens);
  return 1;
}

int close_parsed(Tokens tokens, Tokens *rest, Failure *failure) {
  if (tokens.size == 0) return fail_at(failure, 0, eClose);
  Token head = tokens.items[0];
  if (head.kind != TOKEN_PUNCTUATION || head.number != 41) return fail_at(failure, head.position, eClose);
  *rest = tokens_rest(tokens);
  return 1;
}

Nat type_former(Text name) {
  return same_text(name, sOption) == 1 || same_text(name, sList) == 1 || same_text(name, sProd) == 1
    || same_text(name, sSum) == 1 || same_text(name, sRef()) == 1 || same_text(name, opsTextQuery()) == 1
    || same_text(name, sType) == 1;
}

/* Only Kind constants and checked earlier Kind bindings can index Ref. */
int kind_binding(const Binding *item, Text *kind) {
  switch (item->kind) {
  case BIND_VALUE: return same_type(item->type, &kind_type) == 1 && as_text(item->value, kind);
  case BIND_TYPE:
  case BIND_ARROW:
  case BIND_FUN:
  case BIND_CLOSURE: return 0;
  }
  return 0;
}

int parse_kind_index(Fuel fuel, const Bindings *environment, Tokens tokens, Text *kind, Tokens *rest,
                     Failure *failure) {
  const Binding *found;
  Plan selected;
  Tokens after;
  if (fuel == 0) return fail_at(failure, first_position(tokens), eFuel);
  if (tokens.size == 0) return fail_at(failure, 0, eIndex());
  Token head = tokens.items[0];
  Tokens tail = tokens_rest(tokens);
  switch (head.kind) {
  case TOKEN_NUMBER:
  case TOKEN_STRING: return fail_at(failure, head.position, eIndex());
  case TOKEN_PUNCTUATION:
    if (head.number != 40) return fail_at(failure, head.position, eIndex());
    return parse_kind_index(fuel - 1, environment, tail, kind, &after, failure) && close_parsed(after, rest, failure);
  case TOKEN_IDENTIFIER: break;
  }
  if (lookup(head.text, environment, &found)) {
    if (!kind_binding(found, kind)) return fail_at(failure, head.position, eIndex());
    *rest = tail;
    return 1;
  }
  if (!constructor_plan(&kind_type, head.text, &selected)) return fail_at(failure, head.position, eIndex());
  *kind = head.text;
  *rest = tail;
  return 1;
}

/* A universe is Type 0 or Type 1. An earlier type definition stands for its
   type. The name of a function type is not a data type. */
int named_type(Nat position, Text name, const Bindings *environment, Tokens tokens, const LType **type, Tokens *rest,
               Failure *failure) {
  const Binding *found;
  if (same_text(name, sType) == 1) {
    if (tokens.size == 0) return fail_at(failure, position, eType);
    Token head = tokens.items[0];
    if (head.kind != TOKEN_NUMBER || head.number >= 2) return fail_at(failure, head.position, eType);
    return parsed_type(make_type(TY_UNIVERSE, text_end(), head.number, NULL, NULL), tokens_rest(tokens), type, rest);
  }
  if (lookup(name, environment, &found)) {
    switch (found->kind) {
    case BIND_TYPE: return parsed_type(found->defined, tokens, type, rest);
    case BIND_ARROW: return fail_at(failure, position, eData);
    case BIND_VALUE:
    case BIND_FUN:
    case BIND_CLOSURE: return fail_at(failure, position, eType);
    }
  }
  if (schema_type(name, type) || ops_type(name, type)) {
    *rest = tokens;
    return 1;
  }
  return fail_at(failure, position,
                 ops_later_type(name) == 1 ? eLaterType() : same_text(name, opsTextWritePath()) == 1 ? eData : eType);
}

/* Type formers take data types only, so a universe or a Query type is not an
   argument. */
int data_type(Nat position, const LType *argument, const LType *result, Tokens tokens, const LType **type,
              Tokens *rest, Failure *failure) {
  if (type_level(argument) != 0) return fail_at(failure, position, eData);
  return parsed_type(result, tokens, type, rest);
}

int data_types(Nat at, const LType *a, Nat bt, const LType *b, const LType *result, Tokens tokens, const LType **type,
               Tokens *rest, Failure *failure) {
  if (type_level(a) != 0) return fail_at(failure, at, eData);
  return data_type(bt, b, result, tokens, type, rest, failure);
}

static int former_one(Fuel more, LTypeTag tag, const Bindings *environment, Tokens tail, const LType **type,
                      Tokens *rest, Failure *failure) {
  const LType *a;
  Tokens after;
  return parse_type(more, 1, environment, tail, &a, &after, failure)
    && data_type(first_position(tail), a, unary_type(tag, a), after, type, rest, failure);
}

static int former_two(Fuel more, LTypeTag tag, const Bindings *environment, Tokens tail, const LType **type,
                      Tokens *rest, Failure *failure) {
  const LType *a;
  const LType *b;
  Tokens after;
  Tokens second;
  return parse_type(more, 1, environment, tail, &a, &after, failure)
    && parse_type(more, 1, environment, after, &b, &second, failure)
    && data_types(first_position(tail), a, first_position(after), b, binary_type(tag, a, b), second, type, rest,
                  failure);
}

/* An argument (atom = 1) is a nullary type name or a parenthesized type. */
int parse_type(Fuel fuel, Nat atom, const Bindings *environment, Tokens tokens, const LType **type, Tokens *rest,
               Failure *failure) {
  Tokens after;
  Text kind;
  if (fuel == 0) return fail_at(failure, first_position(tokens), eFuel);
  Fuel more = fuel - 1;
  if (tokens.size == 0) return fail_at(failure, 0, eType);
  Token head = tokens.items[0];
  Tokens tail = tokens_rest(tokens);
  switch (head.kind) {
  case TOKEN_NUMBER:
  case TOKEN_STRING: return fail_at(failure, head.position, eType);
  case TOKEN_PUNCTUATION:
    if (head.number != 40) return fail_at(failure, head.position, eType);
    return parse_type(more, 0, environment, tail, type, &after, failure) && close_parsed(after, rest, failure);
  case TOKEN_IDENTIFIER: break;
  }
  Text name = head.text;
  if (atom == 1 && type_former(name) == 1) return fail_at(failure, head.position, eParen);
  if (same_text(name, sNat) == 1) return parsed_type(&nat_type, tail, type, rest);
  if (same_text(name, sText) == 1) return parsed_type(&text_type, tail, type, rest);
  if (same_text(name, sFlag) == 1) return parsed_type(&flag_type, tail, type, rest);
  if (same_text(name, sValue) == 1) return parsed_type(&value_type, tail, type, rest);
  if (same_text(name, sValues) == 1) return parsed_type(&values_type, tail, type, rest);
  if (same_text(name, sAttrs) == 1) return parsed_type(&attrs_type, tail, type, rest);
  if (same_text(name, sKind) == 1) return parsed_type(&kind_type, tail, type, rest);
  if (same_text(name, sOption) == 1) return former_one(more, TY_OPTION, environment, tail, type, rest, failure);
  if (same_text(name, sList) == 1) return former_one(more, TY_LIST, environment, tail, type, rest, failure);
  if (same_text(name, sProd) == 1) return former_two(more, TY_PROD, environment, tail, type, rest, failure);
  if (same_text(name, sSum) == 1) return former_two(more, TY_SUM, environment, tail, type, rest, failure);
  if (same_text(name, sRef()) == 1)
    return parse_kind_index(more, environment, tail, &kind, &after, failure)
      && parsed_type(make_type(TY_REF, kind, 0, NULL, NULL), after, type, rest);
  if (same_text(name, opsTextQuery()) == 1) return former_one(more, TY_QUERY, environment, tail, type, rest, failure);
  return named_type(head.position, name, environment, tail, type, rest, failure);
}
