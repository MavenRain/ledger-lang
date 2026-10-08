#include "ledger.h"

/* checker.c: the checks of checker.mech. S4 ports lines 1..614: the
   projections, the proofs, the type parameters and type arguments, the
   closures, the inline function values, the bound arguments and the unary
   function arguments. A List Value is a Values list, so listOfValues and
   valuesOfList are the identity. A Parsed answer follows parser.c. An
   Option answer is int 1 with the value written, or 0 for none. */

static const Value null_value = {.kind = VALUE_NULL};
static const LType nat_type = {.tag = TY_NAT};
static const LType universe_zero = {.tag = TY_UNIVERSE, .level = 0};

static const Value *make_value(Value value) {
  Value *made = arena_alloc(sizeof *made);
  *made = value;
  return made;
}

static const Value *nat_value(Nat number) { return make_value((Value){.kind = VALUE_NAT, .number = number}); }
static const Value *text_value(Text text) { return make_value((Value){.kind = VALUE_TEXT, .text = text}); }
static const Value *items_value(const Values *items) { return make_value((Value){.kind = VALUE_ITEMS, .items = items}); }

static const Values *values_item(const Value *head, const Values *tail) {
  Values *item = arena_alloc(sizeof *item);
  item->head = head;
  item->tail = tail;
  return item;
}

static const LType *make_type(LType ty) {
  LType *made = arena_alloc(sizeof *made);
  *made = ty;
  return made;
}

static const LType *schema_of(Text name) { return make_type((LType){.tag = TY_SCHEMA, .name = name}); }

static const LType *eq_type(const LType *a, Val lhs, Val rhs) {
  return make_type((LType){.tag = TY_EQ, .left = a, .lhs = lhs, .rhs = rhs});
}

static const LTypes *types_item(const LType *head, const LTypes *tail) {
  LTypes *item = arena_alloc(sizeof *item);
  item->head = head;
  item->tail = tail;
  return item;
}

static const Params *params_item(Param head, const Params *tail) {
  Params *item = arena_alloc(sizeof *item);
  item->head = head;
  item->tail = tail;
  return item;
}

static const Bindings *bindings_item(Binding head, const Bindings *tail) {
  Bindings *item = arena_alloc(sizeof *item);
  item->head = head;
  item->tail = tail;
  return item;
}

static Binding value_binding(Text name, const LType *ty, const Value *value) {
  return (Binding){.kind = BIND_VALUE, .name = name, .type = ty, .value = value};
}

static Binding type_binding(Text name, const LType *universe, const LType *defined) {
  return (Binding){.kind = BIND_TYPE, .name = name, .type = universe, .defined = defined};
}

static Binding closure_binding(Text name, const Params *params, const LType *result, Tokens body,
                               const Bindings *scope) {
  return (Binding){.kind = BIND_CLOSURE, .name = name, .type = result, .params = params, .body = body, .scope = scope};
}

static Nat params_length(const Params *params) {
  Nat count = 0;
  for (; params != NULL; params = params->tail) count++;
  return count;
}

static Nat values_length(const Values *items) {
  Nat count = 0;
  for (; items != NULL; items = items->tail) count++;
  return count;
}

/* takeCount and dropCount split a list at the length of another list. */
static const Params *take_params(Nat count, const Params *items) {
  if (count == 0 || items == NULL) return NULL;
  return params_item(items->head, take_params(count - 1, items->tail));
}

static const Params *drop_params(Nat count, const Params *items) {
  for (; count > 0; count--) {
    if (items == NULL) return NULL;
    items = items->tail;
  }
  return items;
}

static const Params *reverse_params_onto(const Params *onto, const Params *items) {
  for (; items != NULL; items = items->tail) onto = params_item(items->head, onto);
  return onto;
}

static const Bindings *reverse_bindings_onto(const Bindings *onto, const Bindings *items) {
  for (; items != NULL; items = items->tail) onto = bindings_item(items->head, onto);
  return onto;
}

Nat projection_index(Text name) {
  if (same_text(name, sfirst)) return 1;
  if (same_text(name, ssecond)) return 2;
  return 0;
}

/* A checked product value is the object with the fields first and second. */
const Value *project_value(Nat index, const Value *value) {
  if (value->kind != VALUE_ATTRS || value->attrs == NULL) return &null_value;
  if (index == 1) return value->attrs->value;
  if (value->attrs->rest == NULL) return &null_value;
  return value->attrs->rest->value;
}

int project(Nat position, Nat index, Typed found, Tokens tokens, Typed *result, Tokens *rest, Failure *failure) {
  if (found.type->tag != TY_PROD) return fail_at(failure, position, eProduct);
  *result = index == 1 ? (Typed){found.type->left, project_value(1, found.value)}
                       : (Typed){found.type->right, project_value(2, found.value)};
  *rest = tokens;
  return 1;
}

int check_synthesized(Nat position, const LType *expected, Typed found, Tokens tokens, const Value **value,
                      Tokens *rest, Failure *failure) {
  if (!same_type(expected, found.type)) return fail_at(failure, position, eTerm);
  *value = found.value;
  *rest = tokens;
  return 1;
}

/* Forms that synthesize a type from one argument: 1 first, 2 second,
   3 symm. The form 4 trans takes two arguments, and 5 either takes three. */
Nat synth_form(Text name) {
  if (same_text(name, seither)) return 5;
  if (same_text(name, ssymm)) return 3;
  if (same_text(name, strans)) return 4;
  return projection_index(name);
}

/* Forms that check against a declared structure type: 1 pure, 2 map,
   3 bind, 4 filter, 5 fold, 6 unfold. */
Nat structure_form(Text name) {
  if (same_text(name, spure)) return 1;
  if (same_text(name, smap)) return 2;
  if (same_text(name, sbind)) return 3;
  if (same_text(name, sfilter)) return 4;
  if (same_text(name, sfold)) return 5;
  if (same_text(name, sunfold)) return 6;
  return 0;
}

int sides_of(const LType *ty, const LType **a, Val *lhs, Val *rhs) {
  if (ty->tag != TY_EQ) return 0;
  *a = ty->left;
  *lhs = ty->lhs;
  *rhs = ty->rhs;
  return 1;
}

/* A neutral equality side belongs to the parameters of one signature. */
Nat is_neutral_side(Val side) { return side.kind == VAL_CLOSED ? 0 : 1; }

Nat dependent_result(const LType *ty) {
  const LType *a;
  Val lhs, rhs;
  if (!sides_of(ty, &a, &lhs, &rhs)) return 0;
  return is_neutral_side(lhs) || is_neutral_side(rhs);
}

Nat dependent_params(const Params *params) {
  for (; params != NULL; params = params->tail)
    if (dependent_result(params->head.type)) return 1;
  return 0;
}

/* A proof has no runtime content. Its value is null. */
int refl_check(Nat position, const LType *expected, Tokens tokens, const Value **value, Tokens *rest,
               Failure *failure) {
  const LType *a;
  Val x, y;
  if (!sides_of(expected, &a, &x, &y)) return fail_at(failure, position, eTerm);
  if (!same_val(x, y)) return fail_at(failure, position, eRefl);
  *value = &null_value;
  *rest = tokens;
  return 1;
}

int symm_proof(Nat position, Typed found, Tokens tokens, Typed *result, Tokens *rest, Failure *failure) {
  const LType *a;
  Val x, y;
  if (!sides_of(found.type, &a, &x, &y)) return fail_at(failure, position, eProof);
  *result = (Typed){eq_type(a, y, x), &null_value};
  *rest = tokens;
  return 1;
}

int trans_proof(Nat position, Typed left, Typed right, Tokens tokens, Typed *result, Tokens *rest,
                Failure *failure) {
  const LType *a, *b;
  Val x, y, u, z;
  if (!sides_of(left.type, &a, &x, &y)) return fail_at(failure, position, eProof);
  if (!sides_of(right.type, &b, &u, &z)) return fail_at(failure, position, eProof);
  if (!(same_type(a, b) && same_val(y, u))) return fail_at(failure, position, eTrans);
  *result = (Typed){eq_type(a, x, z), &null_value};
  *rest = tokens;
  return 1;
}

/* The definition of a function checks its body once, with null for each
   parameter. An unnamed binding marks this check. */
Binding check_marker(void) { return value_binding((Text){0}, &nat_type, &null_value); }

Nat checking_body(const Bindings *environment) {
  const Binding *found;
  return lookup((Text){0}, environment, &found) ? 1 : 0;
}

const LTypes *param_types(const Params *params) {
  if (params == NULL) return NULL;
  return types_item(params->head.type, param_types(params->tail));
}

/* A type parameter has the type `Type 0`. */
Nat is_type_param(Param item) { return same_type(item.type, &universe_zero); }

Nat has_type_param(const Params *params) {
  for (; params != NULL; params = params->tail)
    if (is_type_param(params->head)) return 1;
  return 0;
}

Nat has_value_param(const Params *params) {
  for (; params != NULL; params = params->tail)
    if (!is_type_param(params->head)) return 1;
  return 0;
}

/* A name that the list of type bindings does not hold stays opaque. */
const LType *type_argument(Text name, const Bindings *chosen) {
  const Binding *item;
  if (lookup(name, chosen, &item) && item->kind == BIND_TYPE) return item->defined;
  return schema_of(name);
}

/* The substitution replaces all names in one step. */
const LType *subst_type(const Bindings *chosen, const LType *ty) {
  switch (ty->tag) {
  case TY_NAT:
  case TY_TEXT:
  case TY_FLAG:
  case TY_VALUE:
  case TY_VALUES:
  case TY_ATTRS:
  case TY_KIND:
  case TY_HASH:
  case TY_REF:
  case TY_UNIVERSE:
    return ty;
  case TY_SCHEMA:
    return type_argument(ty->name, chosen);
  case TY_OPTION:
  case TY_LIST:
  case TY_QUERY:
    return make_type((LType){.tag = ty->tag, .left = subst_type(chosen, ty->left)});
  case TY_EQ:
    return eq_type(subst_type(chosen, ty->left), ty->lhs, ty->rhs);
  case TY_PROD:
  case TY_SUM:
  case TY_ARROW:
    return make_type(
        (LType){.tag = ty->tag, .left = subst_type(chosen, ty->left), .right = subst_type(chosen, ty->right)});
  }
  return ty;
}

/* The value parameters of a function, with the type arguments in place of
   the type parameters. */
const Params *value_params(const Bindings *chosen, const Params *params) {
  if (params == NULL) return NULL;
  if (is_type_param(params->head)) return value_params(chosen, params->tail);
  return params_item((Param){params->head.name, subst_type(chosen, params->head.type)},
                     value_params(chosen, params->tail));
}

/* One type argument for each leading type parameter. The fuel goes to
   parse_type unchanged, as in the mech. */
int type_arguments(Fuel fuel, const Params *params, const Bindings *environment, const Bindings *chosen,
                   Tokens tokens, const Bindings **result, Tokens *rest, Failure *failure) {
  for (; params != NULL && is_type_param(params->head); params = params->tail) {
    const LType *given;
    Tokens after;
    if (!parse_type(fuel, 1, environment, tokens, &given, &after, failure)) return 0;
    if (type_level(given) != 0) return fail_at(failure, first_position(tokens), eData);
    chosen = bindings_item(type_binding(params->head.name, params->head.type, given), chosen);
    tokens = after;
  }
  *result = chosen;
  *rest = tokens;
  return 1;
}

/* The scope of a definition is the part of the environment that is older
   than the definition. */
const Bindings *definition_scope(Text name, const Bindings *environment) {
  for (; environment != NULL; environment = environment->tail)
    if (same_text(name, environment->head.name)) return environment->tail;
  return NULL;
}

Binding opaque_closure(Text name, const LType *ty) {
  return closure_binding(name, arrow_params(ty), arrow_result(ty), (Tokens){0}, NULL);
}

Binding closure_of_name(Text name, const LType *ty, Text target, const Bindings *caller) {
  const Binding *item;
  if (!lookup(target, caller, &item)) return opaque_closure(name, ty);
  switch (item->kind) {
  case BIND_VALUE:
  case BIND_TYPE:
  case BIND_ARROW:
    return opaque_closure(name, ty);
  case BIND_FUN:
    return closure_binding(name, item->params, item->type, item->body, definition_scope(item->name, caller));
  case BIND_CLOSURE:
    return closure_binding(name, item->params, item->type, item->body, item->scope);
  }
  return opaque_closure(name, ty);
}

/* An inline function argument is a value: the names of its binders, then
   the tokens of its body. A token is its kind, its position and its payload. */
const Value *inline_item(Nat kind, Nat position, const Value *payload) {
  return items_value(values_item(nat_value(kind), values_item(nat_value(position), values_item(payload, NULL))));
}

const Value *inline_token_value(Token token) {
  switch (token.kind) {
  case TOKEN_IDENTIFIER:
    return inline_item(0, token.position, text_value(token.text));
  case TOKEN_NUMBER:
    return inline_item(1, token.position, nat_value(token.number));
  case TOKEN_STRING:
    return inline_item(2, token.position, text_value(token.text));
  case TOKEN_PUNCTUATION:
    return inline_item(3, token.position, nat_value(token.number));
  }
  return &null_value;
}

const Values *inline_token_values(Tokens tokens) {
  const Values *items = NULL;
  for (Nat i = tokens.size; i > 0; i--) items = values_item(inline_token_value(tokens.items[i - 1]), items);
  return items;
}

const Values *inline_names(const Params *params) {
  if (params == NULL) return NULL;
  return values_item(text_value(params->head.name), inline_names(params->tail));
}

const Value *inline_value(const Params *params, Tokens body) {
  return items_value(values_item(items_value(inline_names(params)), inline_token_values(body)));
}

Nat inline_nat(const Value *value) {
  Nat number;
  return as_nat(value, &number) ? number : 0;
}

Text inline_text(const Value *value) {
  Text text;
  return as_text(value, &text) ? text : (Text){0};
}

Token inline_token(Nat kind, Nat position, const Value *payload) {
  if (kind == 0) return (Token){.kind = TOKEN_IDENTIFIER, .position = position, .text = inline_text(payload)};
  if (kind == 1) return (Token){.kind = TOKEN_NUMBER, .position = position, .number = inline_nat(payload)};
  if (kind == 2) return (Token){.kind = TOKEN_STRING, .position = position, .text = inline_text(payload)};
  return (Token){.kind = TOKEN_PUNCTUATION, .position = position, .number = inline_nat(payload)};
}

const Values *inline_parts(const Value *value) {
  const Values *parts;
  return as_values(value, &parts) ? parts : NULL;
}

Token inline_token_of(const Values *parts) {
  return inline_token(inline_nat(argument_head(parts)), inline_nat(argument_head(argument_tail(parts))),
                      argument_head(argument_tail(argument_tail(parts))));
}

Tokens inline_tokens(const Values *items) {
  Nat size = values_length(items);
  Token *made = size == 0 ? NULL : arena_alloc(size * sizeof *made);
  for (Nat i = 0; i < size; i++, items = items->tail) made[i] = inline_token_of(inline_parts(items->head));
  return (Tokens){made, size};
}

/* The binders of an inline argument take the parameter types of the
   function type that the checker matched at the argument. */
const Params *inline_params(const Values *names, const Params *params) {
  if (names == NULL || params == NULL) return NULL;
  return params_item((Param){inline_text(names->head), params->head.type}, inline_params(names->tail, params->tail));
}

/* An inline argument keeps the scope of the application. */
Binding inline_closure(Text name, const LType *ty, const Value *names, const Values *body, const Bindings *caller) {
  return closure_binding(name, inline_params(inline_parts(names), arrow_params(ty)), arrow_result(ty),
                         inline_tokens(body), caller);
}

Fuel type_fuel(Tokens tokens) { return (Fuel)tokens.size + 1; }

Tokens type_tokens_of(const Value *types) {
  const Values *items;
  return as_values(types, &items) ? inline_tokens(items) : (Tokens){0};
}

/* A partial application of a function with type parameters keeps the tokens
   of its type arguments (tokens less rest) as its first bound value. */
const Values *typed_bound(const Params *params, Tokens tokens, Tokens rest, const Values *values) {
  if (!has_type_param(params)) return values;
  Nat used = tokens.size > rest.size ? tokens.size - rest.size : 0;
  return values_item(items_value(inline_token_values((Tokens){tokens.items, used})), values);
}

static Binding typed_closure(const Values *rest, Text name, const LType *ty, Text other, const Params *params,
                             const LType *result, Tokens body, const Bindings *caller);

/* A partial application `(g a1 .. ak)` binds the first k parameters of g in
   the scope of the closure. Recursion follows the checked values. */
Binding bound_binding(const Value *value, Text name, const LType *ty, const Bindings *caller) {
  const Binding *item;
  Text target;
  if (value->kind == VALUE_TEXT) return closure_of_name(name, ty, value->text, caller);
  if (value->kind != VALUE_ITEMS || value->items == NULL) return opaque_closure(name, ty);
  const Value *head = value->items->head;
  const Values *rest = value->items->tail;
  if (!as_text(head, &target)) return inline_closure(name, ty, head, rest, caller);
  if (!lookup(target, caller, &item)) return opaque_closure(name, ty);
  switch (item->kind) {
  case BIND_VALUE:
  case BIND_TYPE:
  case BIND_ARROW:
    return opaque_closure(name, ty);
  case BIND_FUN:
    if (has_type_param(item->params))
      return typed_closure(rest, name, ty, item->name, item->params, item->type, item->body, caller);
    return closure_binding(name, drop_params(values_length(rest), item->params), item->type, item->body,
                           bind_bound(rest, item->params, caller, definition_scope(item->name, caller)));
  case BIND_CLOSURE:
    return closure_binding(name, drop_params(values_length(rest), item->params), item->type, item->body,
                           bind_bound(rest, item->params, caller, item->scope));
  }
  return opaque_closure(name, ty);
}

const Bindings *bind_bound(const Values *values, const Params *params, const Bindings *caller,
                           const Bindings *scope) {
  for (; values != NULL && params != NULL; values = values->tail, params = params->tail) {
    Param head = params->head;
    if (!is_arrow_type(head.type))
      scope = bindings_item(value_binding(head.name, head.type, values->head), scope);
    else
      scope = bindings_item(bound_binding(values->head, head.name, head.type, caller), scope);
  }
  return scope;
}

/* The closure of a function with type parameters binds the type arguments
   in front of the definition scope, as an application does. */
static Binding typed_closure(const Values *rest, Text name, const LType *ty, Text other, const Params *params,
                             const LType *result, Tokens body, const Bindings *caller) {
  const Bindings *chosen;
  Tokens after;
  Failure ignored;
  if (rest == NULL) return opaque_closure(name, ty);
  Tokens types = type_tokens_of(rest->head);
  const Values *values = rest->tail;
  if (!type_arguments(type_fuel(types), params, caller, NULL, types, &chosen, &after, &ignored))
    return opaque_closure(name, ty);
  const Params *formal = value_params(chosen, params);
  return closure_binding(name, drop_params(values_length(values), formal), subst_type(chosen, result), body,
                         bind_bound(values, formal, caller,
                                    reverse_bindings_onto(definition_scope(other, caller), chosen)));
}

Binding partial_closure(Text name, const LType *ty, Text target, const Values *bound, const Bindings *caller) {
  return bound_binding(items_value(values_item(text_value(target), bound)), name, ty, caller);
}

Binding bind_param(Text name, const LType *ty, const Value *value, const Bindings *caller) {
  if (is_arrow_type(ty)) return bound_binding(value, name, ty, caller);
  if (same_type(ty, &universe_zero)) return type_binding(name, ty, schema_of(name));
  return value_binding(name, ty, value);
}

/* The caller is the environment of the application, which holds the
   function arguments. */
const Bindings *bind_arguments(const Bindings *caller, const Params *params, const Values *values,
                               const Bindings *environment) {
  for (; params != NULL; params = params->tail, values = argument_tail(values))
    environment =
        bindings_item(bind_param(params->head.name, params->head.type, argument_head(values), caller), environment);
  return environment;
}

const Bindings *bind_params(const Params *params, const Values *values, const Bindings *environment) {
  return bind_arguments(NULL, params, values, environment);
}

/* 1 when each bound argument of a function type is a name or a list. */
Nat bound_functions(const Params *params, const Values *values) {
  for (; params != NULL; params = params->tail, values = argument_tail(values)) {
    Text target;
    const Values *items;
    if (is_arrow_type(params->head.type) && !as_text(argument_head(values), &target) &&
        !as_values(argument_head(values), &items))
      return 0;
  }
  return 1;
}

/* closesNext is 1 when the next token is a closing parenthesis. */
Nat closes_next(Tokens tokens) {
  if (tokens.size == 0 || tokens.items[0].kind != TOKEN_PUNCTUATION) return 0;
  return tokens.items[0].number == 41 ? 1 : 0;
}

/* The front parameters of a function are all but the last one. */
const Params *front_params(const Params *params) {
  if (params == NULL) return NULL;
  return take_params(params_length(params->tail), params);
}

/* The parameters that a partial application binds: all but the last ones,
   as many as the expected function type has. */
const Params *bound_params(const Params *params, const Params *expected) {
  return reverse_params_onto(NULL, drop_params(params_length(expected), reverse_params_onto(NULL, params)));
}

const LType *unary_param(Unary op) { return op.type; }
const LType *unary_result(Unary op) { return op.result; }
Tokens unary_body(Unary op) { return op.body; }

const Bindings *unary_environment(Unary op, const Value *value) {
  return bindings_item(value_binding(op.name, op.type, value), op.scope);
}

int unary_from(const Bindings *scope, const Params *params, const LType *result, Tokens body, Unary *op) {
  if (params == NULL || params->tail != NULL || is_type_param(params->head)) return 0;
  *op = (Unary){params->head.name, params->head.type, result, body, scope};
  return 1;
}

/* A function parameter keeps the scope of its function argument. */
int unary_of(const Bindings *scope, const Binding *item, Unary *op) {
  switch (item->kind) {
  case BIND_VALUE:
  case BIND_TYPE:
  case BIND_ARROW:
    return 0;
  case BIND_FUN:
    return unary_from(scope, item->params, item->type, item->body, op);
  case BIND_CLOSURE:
    return unary_from(item->scope, item->params, item->type, item->body, op);
  }
  return 0;
}

int unary_argument(const Bindings *environment, Tokens tokens, Unary *op, Tokens *rest, Failure *failure) {
  const Binding *item;
  if (tokens.size == 0) return fail_at(failure, 0, eUnary);
  Token head = tokens.items[0];
  if (head.kind != TOKEN_IDENTIFIER) return fail_at(failure, head.position, eUnary);
  if (!lookup(head.text, environment, &item)) return fail_at(failure, head.position, eUnary);
  if (!unary_of(definition_scope(head.text, environment), item, op)) return fail_at(failure, head.position, eUnary);
  *rest = (Tokens){tokens.items + 1, tokens.size - 1};
  return 1;
}

/* S5a1 ports checker.mech lines 615..1012: the shapes of the structure
   forms, the steppers of fold and unfold, the elements of a carrier, the
   rebuild of a carrier and the value algebra. */

static const LType text_type = {.tag = TY_TEXT};
static const LType flag_type = {.tag = TY_FLAG};
static const LType value_type = {.tag = TY_VALUE};
static const LType attrs_type = {.tag = TY_ATTRS};

static const LType *type_one(LTypeTag tag, const LType *left) { return make_type((LType){.tag = tag, .left = left}); }

static const LType *type_two(LTypeTag tag, const LType *left, const LType *right) {
  return make_type((LType){.tag = tag, .left = left, .right = right});
}

static const Values *reverse_values_onto(const Values *onto, const Values *items) {
  for (; items != NULL; items = items->tail) onto = values_item(items->head, onto);
  return onto;
}

Shape shape_of(const LType *ty) {
  switch (ty->tag) {
  case TY_TEXT: return (Shape){.kind = SHAPE_SEQUENCE, .element = &nat_type};
  case TY_VALUES: return (Shape){.kind = SHAPE_SEQUENCE, .element = &value_type};
  case TY_ATTRS: return (Shape){.kind = SHAPE_SEQUENCE, .element = type_two(TY_PROD, &text_type, &value_type)};
  case TY_OPTION: return (Shape){.kind = SHAPE_OPTION, .element = ty->left};
  case TY_LIST: return (Shape){.kind = SHAPE_LIST, .element = ty->left};
  case TY_SUM: return (Shape){.kind = SHAPE_SUM, .error = ty->left, .element = ty->right};
  default: return (Shape){.kind = SHAPE_NONE};
  }
}

/* 0 no instance, 1 Option, 2 List, 3 Sum E, 4 Text, Values or Attrs. Filter
   has no Sum instance, and the sequences have only filter. */
Nat shape_code(Nat form, const LType *ty) {
  switch (shape_of(ty).kind) {
  case SHAPE_OPTION: return 1;
  case SHAPE_LIST: return 2;
  case SHAPE_SUM: return form == 4 ? 0 : 3;
  case SHAPE_SEQUENCE: return form == 4 ? 4 : 0;
  case SHAPE_NONE: return 0;
  }
  return 0;
}

const LType *shape_element(const LType *ty) {
  Shape shape = shape_of(ty);
  return shape.kind == SHAPE_NONE ? ty : shape.element;
}

const LType *shape_with(const LType *ty, const LType *element) {
  Shape shape = shape_of(ty);
  switch (shape.kind) {
  case SHAPE_OPTION: return type_one(TY_OPTION, element);
  case SHAPE_LIST: return type_one(TY_LIST, element);
  case SHAPE_SUM: return type_two(TY_SUM, shape.error, element);
  case SHAPE_SEQUENCE: return ty;
  case SHAPE_NONE: return ty;
  }
  return ty;
}

const Value *some_value(const LType *ty, const Value *value) {
  return encodes_null(ty) ? object_one(kSome, value) : value;
}

/* pure x is some x, the list with the one item x, or inr x. */
const Value *pure_value(const LType *ty, const Value *value) {
  Shape shape = shape_of(ty);
  switch (shape.kind) {
  case SHAPE_OPTION: return some_value(shape.element, value);
  case SHAPE_LIST: return items_value(values_item(value, NULL));
  case SHAPE_SUM: return object_one(kInr, value);
  case SHAPE_SEQUENCE: return value;
  case SHAPE_NONE: return value;
  }
  return value;
}

Nat is_null(const Value *value) { return value->kind == VALUE_NULL; }

Nat is_yes(const Value *value) { return value->kind == VALUE_FLAG && value->flag == FLAG_YES; }

Nat sum_left(const Value *value) {
  return value->kind == VALUE_ATTRS && value->attrs != NULL ? same_text(value->attrs->key, kInl) : 0;
}

const Values *items_of(const Value *value) { return value->kind == VALUE_ITEMS ? value->items : NULL; }

const Values *append_values(const Values *front, const Values *back) {
  return reverse_values_onto(back, reverse_values_onto(NULL, front));
}

/* The payload of some x or of inr x. The values none and inl e have none. */
int payload_of(const LType *ty, const LType *element, const Value *value, const Value **payload) {
  switch (shape_of(ty).kind) {
  case SHAPE_OPTION:
    if (is_null(value)) return 0;
    *payload = encodes_null(element) ? project_value(1, value) : value;
    return 1;
  case SHAPE_SUM:
    if (sum_left(value)) return 0;
    *payload = project_value(1, value);
    return 1;
  case SHAPE_LIST: return 0;
  case SHAPE_SEQUENCE: return 0;
  case SHAPE_NONE: return 0;
  }
  return 0;
}

/* Join a source value and the result of one application: 2 map wraps the
   result again, 3 bind keeps it, 4 filter keeps the source or gives none. */
const Value *step_one(Nat form, const LType *ty, const Value *source, const Value *result) {
  if (form == 3) return result;
  if (form == 4) return is_yes(result) ? source : &null_value;
  return pure_value(ty, result);
}

const Values *step_items(Nat form, const Value *item, const Value *result, const Values *rest) {
  if (form == 3) return append_values(items_of(result), rest);
  if (form == 4) return is_yes(result) ? values_item(item, rest) : rest;
  return values_item(result, rest);
}

/* map takes A -> B for F B, bind takes A -> F B, filter takes A -> Flag. */
Nat structure_fits(Nat form, const LType *ty, Unary op) {
  if (form == 2) return same_type(unary_result(op), shape_element(ty));
  if (form == 3) return same_type(unary_result(op), ty);
  return same_type(unary_result(op), &flag_type) ? same_type(unary_param(op), shape_element(ty)) : 0;
}

/* map and bind read F A for the parameter type A. Filter reads F A itself. */
const LType *structure_source(Nat form, const LType *ty, Unary op) {
  return form == 4 ? ty : shape_with(ty, unary_param(op));
}

/* The result type of an inline function: B for map into F B, F B for bind,
   Flag for filter. */
const LType *structure_result(Nat form, const LType *ty) {
  return form == 2 ? shape_element(ty) : form == 3 ? ty : &flag_type;
}

const Params *stepper_params(Stepper op) { return op.params; }

const LType *stepper_result(Stepper op) { return op.result; }

Tokens stepper_body(Stepper op) { return op.body; }

const Bindings *stepper_environment(Stepper op, const Values *values) {
  return bind_params(op.params, values, op.scope);
}

int stepper_argument(const Bindings *environment, Tokens tokens, Stepper *op, Tokens *rest, Failure *failure) {
  if (tokens.size == 0) return fail_at(failure, 0, eStep);
  Token head = tokens.items[0];
  const Binding *item;
  if (head.kind != TOKEN_IDENTIFIER || !lookup(head.text, environment, &item)) return fail_at(failure, head.position, eStep);
  switch (item->kind) {
  case BIND_FUN:
    if (has_type_param(item->params)) return fail_at(failure, head.position, eStep);
    *op = (Stepper){item->params, item->type, item->body, definition_scope(item->name, environment)};
    break;
  case BIND_CLOSURE: *op = (Stepper){item->params, item->type, item->body, item->scope}; break;
  case BIND_VALUE: return fail_at(failure, head.position, eStep);
  case BIND_TYPE: return fail_at(failure, head.position, eStep);
  case BIND_ARROW: return fail_at(failure, head.position, eStep);
  }
  *rest = (Tokens){tokens.items + 1, tokens.size - 1};
  return 1;
}

Nat same_types(const LTypes *left, const LTypes *right) {
  for (; left != NULL && right != NULL; left = left->tail, right = right->tail)
    if (!same_type(left->head, right->head)) return 0;
  return left == NULL && right == NULL;
}

/* Algebra carriers: 1 Nat, 2 a sequence (List A, Text, Values or Attrs),
   0 no instance. */
Nat carrier_code(const LType *ty) {
  switch (shape_of(ty).kind) {
  case SHAPE_OPTION: return 0;
  case SHAPE_LIST: return 2;
  case SHAPE_SUM: return 0;
  case SHAPE_SEQUENCE: return 2;
  case SHAPE_NONE: return same_type(ty, &nat_type) ? 1 : 0;
  }
  return 0;
}

const Values *text_elements(Text text) {
  const Values *items = NULL;
  for (Nat index = text.size; index > 0; index--) items = values_item(nat_value(text.items[index - 1]), items);
  return items;
}

const Values *field_elements(const Attrs *attrs) {
  const Values *reversed = NULL;
  for (; attrs != NULL; attrs = attrs->rest)
    reversed = values_item(object_two(kFirst, text_value(attrs->key), kSecond, attrs->value), reversed);
  return reverse_values_onto(NULL, reversed);
}

const Values *sequence_elements(const Value *value) {
  switch (value->kind) {
  case VALUE_TEXT: return text_elements(value->text);
  case VALUE_ITEMS: return value->items;
  case VALUE_ATTRS: return field_elements(value->attrs);
  case VALUE_NULL: return NULL;
  case VALUE_FLAG: return NULL;
  case VALUE_NAT: return NULL;
  }
  return NULL;
}

/* A fold over the number n applies its function n times, once for each of n
   null items. The fuel bounds n: the items exist when n <= fuel. */
int unit_items(Fuel fuel, Nat count, const Values **items) {
  if ((Fuel)count > fuel) return 0;
  const Values *made = NULL;
  for (Nat index = 0; index < count; index++) made = values_item(&null_value, made);
  *items = made;
  return 1;
}

int elements_of(Fuel fuel, const Value *value, const Values **items) {
  Nat count;
  if (!as_nat(value, &count)) {
    *items = sequence_elements(value);
    return 1;
  }
  return unit_items(fuel, count, items);
}

Nat count_of(const Value *value) {
  Nat count;
  return as_nat(value, &count) ? count : 0;
}

Nat count_values(const Values *items) { return values_length(items); }

int text_of_elements(const Values *items, Text *text) {
  Nat size = values_length(items);
  Nat *bytes = arena_alloc((size + 1) * sizeof *bytes);
  Nat index = 0;
  for (; items != NULL; items = items->tail) {
    Nat number;
    if (!as_nat(items->head, &number) || number >= 256) return 0;
    bytes[index++] = number;
  }
  *text = (Text){bytes, size};
  return 1;
}

Text key_of(const Value *item) {
  Text text;
  return as_text(project_value(1, item), &text) ? text : text_end();
}

/* The fields of the items from the last one back, so a key that comes again
   fails at position 0. */
int fields_of(const Values *items, const Attrs **attrs, Failure *failure) {
  const Attrs *built = NULL;
  for (const Values *rest = reverse_values_onto(NULL, items); rest != NULL; rest = rest->tail) {
    Text key = key_of(rest->head);
    if (has_field(key, built)) return fail_at(failure, 0, eField);
    Attrs *field = arena_alloc(sizeof *field);
    *field = (Attrs){key, project_value(2, rest->head), built};
    built = field;
  }
  *attrs = built;
  return 1;
}

/* Build a carrier value from its elements: the count for Nat, the bytes for
   Text, the fields for Attrs, and the items otherwise. Reject invalid bytes
   and duplicate attribute keys before the value can be consumed or printed. */
int rebuild(const LType *ty, const Values *items, const Value **value, Failure *failure) {
  if (same_type(ty, &text_type)) {
    Text bytes;
    if (!text_of_elements(items, &bytes)) return fail_at(failure, 0, eByte);
    *value = text_value(bytes);
    return 1;
  }
  if (same_type(ty, &attrs_type)) {
    const Attrs *fields;
    if (!fields_of(items, &fields, failure)) return 0;
    *value = make_value((Value){.kind = VALUE_ATTRS, .attrs = fields});
    return 1;
  }
  *value = same_type(ty, &nat_type) ? nat_value(count_values(items)) : items_value(items);
  return 1;
}

/* fold over Nat takes C -> C. Over a sequence of E it takes E -> C -> C. */
Nat fold_fits(const LType *ty, const LType *result, Stepper op) {
  const LTypes *expected = same_type(ty, &nat_type) ? types_item(result, NULL)
                                                    : types_item(shape_element(ty), types_item(result, NULL));
  return same_type(stepper_result(op), result) ? same_types(param_types(stepper_params(op)), expected) : 0;
}

/* The seed of unfold is the type of the first parameter. */
const LType *param_seed(const Params *params) {
  const LTypes *types = param_types(params);
  return types == NULL ? &nat_type : types->head;
}

const LType *unfold_seed(Stepper op) { return param_seed(stepper_params(op)); }

/* unfold into Nat takes S -> Option S. Into a sequence of E it takes
   S -> Option (Prod E S). */
Nat unfold_fits(const LType *ty, Stepper op) {
  const LType *step = same_type(ty, &nat_type) ? unfold_seed(op) : type_two(TY_PROD, shape_element(ty), unfold_seed(op));
  return same_types(param_types(stepper_params(op)), types_item(unfold_seed(op), NULL))
             ? same_type(stepper_result(op), type_one(TY_OPTION, step))
             : 0;
}

/* The algebra of a fold over Value: 1 valueNat, 2 valueFlag, 3 valueText,
   4 valueItems, and valueAttrs otherwise. */
Stepper algebra_step(Nat index, ValueAlgebra ops) {
  return index == 1 ? ops.on_nat : index == 2 ? ops.on_flag : index == 3 ? ops.on_text : index == 4 ? ops.on_items : ops.on_attrs;
}

/* 0 valueNull, 1 valueNat, 2 valueFlag, 3 valueText, 4 valueItems,
   5 valueAttrs. */
Nat value_index(const Value *value) {
  switch (value->kind) {
  case VALUE_NULL: return 0;
  case VALUE_NAT: return 1;
  case VALUE_FLAG: return 2;
  case VALUE_TEXT: return 3;
  case VALUE_ITEMS: return 4;
  case VALUE_ATTRS: return 5;
  }
  return 0;
}

/* For the result type C the functions take Nat, Flag, Text, List C and
   List (Prod Text C). */
const LType *algebra_param(Nat index, const LType *result) {
  if (index == 1) return &nat_type;
  if (index == 2) return &flag_type;
  if (index == 3) return &text_type;
  if (index == 4) return type_one(TY_LIST, result);
  return type_one(TY_LIST, type_two(TY_PROD, &text_type, result));
}

/* A second function name after the first selects the fold over Value. */
Nat names_function(const Bindings *environment, Tokens tokens) {
  Stepper op;
  Tokens rest;
  Failure failure;
  return stepper_argument(environment, tokens, &op, &rest, &failure) ? 1 : 0;
}

/* The children of a Value: its items, or its fields as pairs of key and value. */
const Values *child_elements(const Value *value) {
  switch (value->kind) {
  case VALUE_ITEMS: return value->items;
  case VALUE_ATTRS: return field_elements(value->attrs);
  case VALUE_NULL: return NULL;
  case VALUE_NAT: return NULL;
  case VALUE_FLAG: return NULL;
  case VALUE_TEXT: return NULL;
  }
  return NULL;
}

/* A scalar gives its payload to its function. Items and fields give the list
   of the results of their children. */
const Value *algebra_input(const Value *value, const Values *results) {
  return value_index(value) < 4 ? value : items_value(results);
}

/* The layer of a seed of type S: none for valueNull, or a number, a flag, a
   text, the seeds of the items, or the keys and seeds of the fields. */
const LType *value_layer(const LType *seed) {
  const LType *fields = type_one(TY_LIST, type_two(TY_PROD, &text_type, seed));
  const LType *inner = type_two(TY_SUM, type_one(TY_LIST, seed), fields);
  return type_one(TY_OPTION,
                  type_two(TY_SUM, &nat_type, type_two(TY_SUM, &flag_type, type_two(TY_SUM, &text_type, inner))));
}

Nat unfold_value_fits(Stepper op) {
  return same_types(param_types(stepper_params(op)), types_item(unfold_seed(op), NULL))
             ? same_type(stepper_result(op), value_layer(unfold_seed(op)))
             : 0;
}

/* S5a2 ports checker.mech lines 1013..1363: the binders of an inline
   function, the layers of an unfold into Value, Grown, Worked, the
   parameter levels of a body check and the instantiation of a dependent
   result. Only inline_binders checks fuel; the other fuel arguments go to
   parse_type or print_value unchanged. */

const LType *inline_result(Nat mode, const LType *expected, const Params *params) {
  if (mode == 0) return expected;
  if (mode == 1)
    return type_one(TY_OPTION, same_type(expected, &nat_type)
                                   ? param_seed(params)
                                   : type_two(TY_PROD, shape_element(expected), param_seed(params)));
  return value_layer(param_seed(params));
}

int inline_binder(Fuel fuel, const Bindings *environment, const Bindings *seen, Tokens tokens, Param *binder,
                  Tokens *rest, Failure *failure) {
  Tokens after_open;
  if (!expect_mark(40, tokens, &after_open, failure)) return fail_at(failure, failure->position, eFun);
  if (after_open.size == 0) return fail_at(failure, first_position(tokens), eFun);
  Token head = after_open.items[0];
  Tokens after_name = {after_open.items + 1, after_open.size - 1};
  if (head.kind != TOKEN_IDENTIFIER) return fail_at(failure, head.position, eFun);
  if (reserved_name(head.text) == 1) return fail_at(failure, head.position, eReserved);
  const Binding *previous;
  if (lookup(head.text, seen, &previous)) return fail_at(failure, head.position, eDuplicate);
  Tokens after_colon;
  if (!expect_mark(58, after_name, &after_colon, failure)) return fail_at(failure, failure->position, eFun);
  const LType *ty;
  Tokens after_type;
  if (!parse_type(fuel, 0, environment, after_colon, &ty, &after_type, failure)) return 0;
  if (type_level(ty) != 0) return fail_at(failure, first_position(after_colon), eData);
  if (!expect_mark(41, after_type, rest, failure)) return fail_at(failure, failure->position, eFun);
  *binder = (Param){head.text, ty};
  return 1;
}

/* Each binder takes one unit of fuel (fuelMore), and the binder itself
   parses its type with the fuel that remains. */
int inline_binders(Fuel fuel, const Bindings *environment, const Bindings *seen, Tokens tokens, const Params **binders,
                   Tokens *body, Failure *failure) {
  const Params *done = NULL;
  for (;;) {
    if (fuel == 0) return fail_at(failure, first_position(tokens), eFuel);
    Fuel more = fuel - 1;
    Param binder;
    Tokens after_binder;
    if (!inline_binder(more, environment, seen, tokens, &binder, &after_binder, failure)) return 0;
    done = params_item(binder, done);
    Failure ignored;
    if (expect_mark(63, after_binder, body, &ignored)) {
      *binders = reverse_params_onto(NULL, done);
      return 1;
    }
    environment = bind_params(params_item(binder, NULL), NULL, environment);
    seen = bindings_item(value_binding(binder.name, binder.type, &null_value), seen);
    tokens = after_binder;
    fuel = more;
  }
}

Nat layer_index(const Value *layer) {
  if (is_null(layer)) return 0;
  if (sum_left(layer)) return 1;
  const Value *second = project_value(1, layer);
  if (sum_left(second)) return 2;
  const Value *third = project_value(1, second);
  if (sum_left(third)) return 3;
  return sum_left(project_value(1, third)) ? 4 : 5;
}

const Value *layer_payload(const Value *layer) {
  Nat index = layer_index(layer);
  const Value *second = project_value(1, layer);
  if (index == 1) return second;
  const Value *third = project_value(1, second);
  if (index == 2) return third;
  const Value *fourth = project_value(1, third);
  if (index == 3) return fourth;
  return project_value(1, fourth);
}

const Values *grown_items(Grown built) { return built.items; }

Nat grown_limit(Grown built) { return built.limit; }

const Value *grown_head(Grown built) { return built.items == NULL ? &null_value : built.items->head; }

Grown grown_leaf(const Value *value, Nat limit) { return (Grown){values_item(value, NULL), limit}; }

int lift_parsed(Nat budget, int parsed, Nat *left) {
  if (parsed) *left = budget;
  return parsed;
}

int check_worked(Nat position, const LType *expected, Typed found, Tokens tokens, Nat budget, const Value **value,
                 Tokens *rest, Nat *left, Failure *failure) {
  return lift_parsed(budget, check_synthesized(position, expected, found, tokens, value, rest, failure), left);
}

Binding body_marker(Nat count) { return value_binding(text_end(), &nat_type, nat_value(count)); }

/* A punctuation other than ( or ) does not end an atom at depth 0. */
Tokens skip_atom(Nat depth, Tokens tokens) {
  for (; tokens.size > 0; tokens = (Tokens){tokens.items + 1, tokens.size - 1}) {
    Token head = tokens.items[0];
    Tokens tail = {tokens.items + 1, tokens.size - 1};
    if (head.kind != TOKEN_PUNCTUATION) {
      if (depth == 0) return tail;
      continue;
    }
    if (head.number == 40) {
      depth = depth + 1;
      continue;
    }
    if (head.number == 41 && depth == 1) return tail;
    if (head.number == 41) depth = depth == 0 ? 0 : depth - 1;
  }
  return tokens;
}

/* Option (Option Nat): the int is the outer some, found the inner some. */
int param_level(Text name, Nat count, const Bindings *environment, Nat *found, Nat *index) {
  for (; environment != NULL && count != 0; environment = environment->tail, count = count - 1) {
    if (same_text(name, environment->head.name) == 1) {
      *found = 1;
      *index = count - 1;
      return 1;
    }
  }
  *found = 0;
  return 1;
}

int body_level(Text name, const Bindings *environment, Nat *found, Nat *index) {
  if (environment == NULL || environment->head.kind != BIND_VALUE) return 0;
  Nat total;
  if (!as_nat(environment->head.value, &total)) return 0;
  if (same_text(environment->head.name, text_end()) != 1) return 0;
  return param_level(name, total, environment->tail, found, index);
}

Nat proof_in_scope(Text name, const LType *ty, const Bindings *environment) {
  if (dependent_result(ty) != 1) return 1;
  Nat found = 0;
  Nat index = 0;
  return body_level(name, environment, &found, &index) && found == 1 ? 1 : 0;
}

int printed_side(Fuel fuel, const Value *value, Val *side) {
  Printer printer = {fuel, {0}};
  Failure ignored;
  if (!print_value(&printer, value, &ignored)) return 0;
  *side = (Val){.kind = VAL_CLOSED, .text = builder_text(&printer.output)};
  return 1;
}

int argument_text(Fuel fuel, const Bindings *environment, const Value *value, Tokens tokens, Val *side) {
  if (checking_body(environment) != 1) return printed_side(fuel, value, side);
  if (tokens.size == 0) return 0;
  Token head = tokens.items[0];
  switch (head.kind) {
  case TOKEN_NUMBER:
  case TOKEN_STRING: return printed_side(fuel, value, side);
  case TOKEN_PUNCTUATION: return 0;
  case TOKEN_IDENTIFIER: {
    Nat found = 0;
    Nat index = 0;
    if (!body_level(head.text, environment, &found, &index)) return 0;
    if (found == 0) return printed_side(fuel, value, side);
    *side = (Val){.kind = VAL_VAR, .index = index};
    return 1;
  }
  }
  return 0;
}

int argument_side(Fuel fuel, Nat index, const Bindings *environment, const Params *params, const Values *values,
                  Tokens tokens, Val *side) {
  for (; params != NULL; params = params->tail, index = index - 1) {
    if (is_type_param(params->head) == 1) {
      if (index == 0) return 0;
      continue;
    }
    if (index == 0) return argument_text(fuel, environment, argument_head(values), tokens, side);
    values = argument_tail(values);
    tokens = skip_atom(0, tokens);
  }
  return 0;
}

int argument_token(Nat index, const Params *params, Tokens tokens, Token *token) {
  for (; params != NULL; params = params->tail, index = index - 1) {
    if (is_type_param(params->head) == 1) {
      if (index == 0) return 0;
      continue;
    }
    if (index == 0) {
      if (tokens.size == 0) return 0;
      *token = tokens.items[0];
      return 1;
    }
    tokens = skip_atom(0, tokens);
  }
  return 0;
}

/* The mech recursion renames the tail first, but a none anywhere gives
   none and nothing else depends on the order, so the loop goes forward. */
int rename_markers(Fuel fuel, const Bindings *environment, const Params *params, const Values *values, Tokens tokens,
                   Tokens term, Tokens *renamed) {
  Token *items = arena_alloc(sizeof(Token) * (term.size + 1));
  for (Nat at = 0; at < term.size; at++) {
    Token head = term.items[at];
    Nat index = 0;
    items[at] = head;
    if (head.kind != TOKEN_IDENTIFIER || !marker_index(head.text, &index)) continue;
    Val side;
    if (!argument_side(fuel, index, environment, params, values, tokens, &side)) return 0;
    if (side.kind == VAL_TERM) return 0;
    if (side.kind == VAL_VAR) {
      items[at] = (Token){TOKEN_IDENTIFIER, head.position, 0, marker_name(side.index)};
      continue;
    }
    if (!argument_token(index, params, tokens, &items[at])) return 0;
  }
  *renamed = (Tokens){items, term.size};
  return 1;
}

Nat kept_side(Val side) {
  switch (side.kind) {
  case VAL_CLOSED:
  case VAL_VAR: return 1;
  case VAL_TERM: return has_marker(side.term);
  }
  return 0;
}

int instantiate_side(Fuel fuel, const Bindings *environment, const Params *params, const Values *values, Tokens tokens,
                     Val side, Val *result) {
  switch (side.kind) {
  case VAL_CLOSED: *result = side; return 1;
  case VAL_VAR: return argument_side(fuel, side.index, environment, params, values, tokens, result);
  case VAL_TERM: {
    if (checking_body(environment) != 1) {
      *result = side;
      return 1;
    }
    Tokens renamed;
    if (!rename_markers(fuel, environment, params, values, tokens, side.term, &renamed)) return 0;
    *result = (Val){.kind = VAL_TERM, .term = renamed};
    return 1;
  }
  }
  return 0;
}

int instantiate_result(Fuel fuel, const Bindings *environment, const Params *params, const Values *values,
                       Tokens tokens, const LType *result, const LType **instantiated) {
  const LType *a;
  Val lhs;
  Val rhs;
  if (!sides_of(result, &a, &lhs, &rhs)) {
    *instantiated = result;
    return 1;
  }
  Val x;
  Val y;
  if (!instantiate_side(fuel, environment, params, values, tokens, lhs, &x)) return 0;
  if (!instantiate_side(fuel, environment, params, values, tokens, rhs, &y)) return 0;
  *instantiated = eq_type(a, x, y);
  return 1;
}

const Params *instantiate_params(Fuel fuel, const Bindings *environment, const Params *params, const Values *values,
                                 Tokens tokens, const Params *remaining) {
  const Params *done = NULL;
  for (; remaining != NULL; remaining = remaining->tail) {
    Param head = remaining->head;
    const LType *found;
    done = params_item(instantiate_result(fuel, environment, params, values, tokens, head.type, &found)
                           ? (Param){head.name, found}
                           : head,
                       done);
  }
  return reverse_params_onto(NULL, done);
}

const Bindings *argument_bindings(Nat index, const Params *params, const Values *values,
                                  const Bindings *environment) {
  const Bindings *done = NULL;
  for (; params != NULL; params = params->tail, index = index + 1) {
    if (is_type_param(params->head) == 1) continue;
    done = bindings_item(value_binding(marker_name(index), params->head.type, argument_head(values)), done);
    values = argument_tail(values);
  }
  return reverse_bindings_onto(environment, done);
}
