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
