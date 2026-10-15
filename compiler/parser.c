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
    || same_text(name, sType) == 1 || same_text(name, sSigma) == 1;
}

/* Only Kind constants and checked earlier Kind bindings can index Ref. */
int kind_binding(const Binding *item, Text *kind) {
  switch (item->kind) {
  case BIND_VALUE: return same_type(item->type, &kind_type) == 1 && as_text(item->value, kind);
  case BIND_FAMILY:
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
   type, with its markers moved into the scope of done. The name of a function
   type is not a data type. A type family with one argument gives its reduced
   type (D12 part B), and with no argument it is not a data type. */
int named_type(Fuel fuel, Nat budget, Nat position, Text name, const Bindings *environment, const Params *done,
               Tokens tokens, const LType **type, Tokens *rest, Nat *left, Failure *failure) {
  const Binding *found;
  if (same_text(name, sType) == 1) {
    if (tokens.size == 0) return fail_at(failure, position, eType);
    Token head = tokens.items[0];
    if (head.kind != TOKEN_NUMBER || head.number >= 2) return fail_at(failure, head.position, eType);
    return parsed_type(make_type(TY_UNIVERSE, text_end(), head.number, NULL, NULL), tokens_rest(tokens), type, rest);
  }
  if (lookup(name, environment, &found)) {
    switch (found->kind) {
    case BIND_TYPE: {
      Nat offset = 0;
      for (const Params *cell = done; cell != NULL; cell = cell->tail) offset++;
      return parsed_type(shift_type_markers(offset, found->defined), tokens, type, rest);
    }
    case BIND_FAMILY:
      return family_application(fuel, budget, position, found->type, environment, done, tokens, type, rest, left,
                                failure);
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
                 same_text(name, opsTextWritePath()) == 1 || same_text(name, opsTextReadPath()) == 1 ? eData : eType);
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

static int former_one(Fuel more, Nat budget, LTypeTag tag, const Bindings *environment, const Params *done,
                      Tokens tail, const LType **type, Tokens *rest, Nat *left, Failure *failure) {
  const LType *a;
  Tokens after;
  return parse_type_in(more, budget, 1, environment, done, tail, &a, &after, left, failure)
    && data_type(first_position(tail), a, unary_type(tag, a), after, type, rest, failure);
}

static int former_two(Fuel more, Nat budget, LTypeTag tag, const Bindings *environment, const Params *done,
                      Tokens tail, const LType **type, Tokens *rest, Nat *left, Failure *failure) {
  const LType *a;
  const LType *b;
  Tokens after;
  Tokens second;
  Nat spent;
  return parse_type_in(more, budget, 1, environment, done, tail, &a, &after, &spent, failure)
    && parse_type_in(more, spent, 1, environment, done, after, &b, &second, left, failure)
    && data_types(first_position(tail), a, first_position(after), b, binary_type(tag, a, b), second, type, rest,
                  failure);
}

/* Type arguments and inline annotations in a checked body can name its
   parameters. Slots retain their marker positions, including shadowed names. */
const Params *body_params(const Bindings *environment) {
  if (checking_body(environment) != 1) return NULL;
  Nat count = 0;
  for (const Bindings *cell = environment; cell != NULL; cell = cell->tail)
    if (cell->head.slot > count) count = cell->head.slot;
  if (count == 0) return NULL;
  Params *params = arena_alloc(sizeof *params * count);
  for (Nat index = 0; index < count; index++)
    params[index] = (Params){.head = {text_end(), &nat_type}, .tail = index == 0 ? NULL : &params[index - 1]};
  for (const Bindings *cell = environment; cell != NULL; cell = cell->tail) {
    Nat slot = cell->head.slot;
    if (slot != 0 && params[slot - 1].head.name.size == 0)
      params[slot - 1].head = (Param){cell->head.name, cell->head.type};
  }
  return &params[count - 1];
}

int parse_type(Fuel fuel, Nat budget, Nat atom, const Bindings *environment, Tokens tokens, const LType **type,
               Tokens *rest, Nat *left, Failure *failure) {
  return parse_type_in(fuel, budget, atom, environment, body_params(environment), tokens, type, rest, left, failure);
}

/* An argument (atom = 1) is a nullary type name or a parenthesized type.
   done holds the earlier parameters of a signature. A Sigma binder gets the
   next marker after them. D10: a Sigma side runs on the work budget, and
   left gets the rest. */
int parse_type_in(Fuel fuel, Nat budget, Nat atom, const Bindings *environment, const Params *done, Tokens tokens,
                  const LType **type, Tokens *rest, Nat *left, Failure *failure) {
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
    return parse_type_in(more, budget, 0, environment, done, tail, type, &after, left, failure)
      && close_parsed(after, rest, failure);
  case TOKEN_IDENTIFIER: break;
  }
  Text name = head.text;
  const Binding *found;
  if (atom == 1 && (type_former(name) == 1 ||
                    (lookup(name, environment, &found) && found->kind == BIND_FAMILY)))
    return fail_at(failure, head.position, eParen);
  *left = budget;
  if (same_text(name, sNat) == 1) return parsed_type(&nat_type, tail, type, rest);
  if (same_text(name, sText) == 1) return parsed_type(&text_type, tail, type, rest);
  if (same_text(name, sFlag) == 1) return parsed_type(&flag_type, tail, type, rest);
  if (same_text(name, sValue) == 1) return parsed_type(&value_type, tail, type, rest);
  if (same_text(name, sValues) == 1) return parsed_type(&values_type, tail, type, rest);
  if (same_text(name, sAttrs) == 1) return parsed_type(&attrs_type, tail, type, rest);
  if (same_text(name, sKind) == 1) return parsed_type(&kind_type, tail, type, rest);
  if (same_text(name, sOption) == 1)
    return former_one(more, budget, TY_OPTION, environment, done, tail, type, rest, left, failure);
  if (same_text(name, sList) == 1)
    return former_one(more, budget, TY_LIST, environment, done, tail, type, rest, left, failure);
  if (same_text(name, sProd) == 1)
    return former_two(more, budget, TY_PROD, environment, done, tail, type, rest, left, failure);
  if (same_text(name, sSum) == 1)
    return former_two(more, budget, TY_SUM, environment, done, tail, type, rest, left, failure);
  if (same_text(name, sSigma) == 1) return sigma_type(more, budget, environment, done, tail, type, rest, left, failure);
  if (same_text(name, sRef()) == 1)
    return parse_kind_index(more, environment, tail, &kind, &after, failure)
      && parsed_type(make_type(TY_REF, kind, 0, NULL, NULL), after, type, rest);
  if (same_text(name, opsTextQuery()) == 1)
    return former_one(more, budget, TY_QUERY, environment, done, tail, type, rest, left, failure);
  return named_type(more, budget, head.position, name, environment, done, tail, type, rest, left, failure);
}
