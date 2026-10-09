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

static const LType *term_type_identity(const LType *type, const Bindings *environment);

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

static Binding closure_binding(Text name, const Params *params, const LType *result, const Term *term,
                               const Bindings *scope) {
  return (Binding){.kind = BIND_CLOSURE, .name = name, .type = result, .params = params, .term = term, .scope = scope};
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
                   Tokens tokens, const Bindings **result, Tokens *rest, const TermTypes **types, Failure *failure) {
  const TermTypes *done = NULL;
  for (; params != NULL && is_type_param(params->head); params = params->tail) {
    const LType *given;
    Tokens after;
    if (!parse_type(fuel, 1, environment, tokens, &given, &after, failure)) return 0;
    if (type_level(given) != 0) return fail_at(failure, first_position(tokens), eData);
    chosen = bindings_item(type_binding(params->head.name, params->head.type, given), chosen);
    if (types != NULL)
      done = term_types_item((TermType){.position = first_position(tokens),
                                        .type = given,
                                        .source = taken_tokens(tokens, after),
                                        .identity = term_type_identity(given, environment)},
                            done);
    tokens = after;
  }
  *result = chosen;
  *rest = tokens;
  if (types != NULL) {
    const TermTypes *ordered = NULL;
    for (; done != NULL; done = done->tail) ordered = term_types_item(done->head, ordered);
    *types = ordered;
  }
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
  return closure_binding(name, arrow_params(ty), arrow_result(ty), NULL, NULL);
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
    return closure_binding(name, item->params, item->type, item->term, definition_scope(item->name, caller));
  case BIND_CLOSURE:
    return closure_binding(name, item->params, item->type, item->term, item->scope);
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

const Value *inline_value(const Params *params, Tokens body, const Term *carrier) {
  return make_value((Value){.kind = VALUE_ITEMS,
                            .items = values_item(items_value(inline_names(params)), inline_token_values(body)),
                            .term = carrier});
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

/* An inline argument keeps the scope of the application. The closure term is
   the TERM_BODY of the argument Value. The run-time path builds no term, thus
   a Value with no term gives a TERM_BODY of the decoded tokens. */
Binding inline_closure(Text name, const LType *ty, const Value *value, const Bindings *caller) {
  const Term *term = value->term != NULL ? value->term : term_body(inline_tokens(value->items->tail), NULL);
  return closure_binding(name, inline_params(inline_parts(value->items->head), arrow_params(ty)), arrow_result(ty),
                         term, caller);
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
                             const LType *result, const Term *term, const Bindings *caller);

/* A partial application `(g a1 .. ak)` binds the first k parameters of g in
   the scope of the closure. Recursion follows the checked values. */
Binding bound_binding(const Value *value, Text name, const LType *ty, const Bindings *caller) {
  const Binding *item;
  Text target;
  if (value->kind == VALUE_TEXT) return closure_of_name(name, ty, value->text, caller);
  if (value->kind != VALUE_ITEMS || value->items == NULL) return opaque_closure(name, ty);
  const Value *head = value->items->head;
  const Values *rest = value->items->tail;
  if (!as_text(head, &target)) return inline_closure(name, ty, value, caller);
  if (!lookup(target, caller, &item)) return opaque_closure(name, ty);
  switch (item->kind) {
  case BIND_VALUE:
  case BIND_TYPE:
  case BIND_ARROW:
    return opaque_closure(name, ty);
  case BIND_FUN:
    if (has_type_param(item->params))
      return typed_closure(rest, name, ty, item->name, item->params, item->type, item->term, caller);
    return closure_binding(name, drop_params(values_length(rest), item->params), item->type, item->term,
                           bind_bound(rest, item->params, caller, definition_scope(item->name, caller)));
  case BIND_CLOSURE:
    return closure_binding(name, drop_params(values_length(rest), item->params), item->type, item->term,
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
                             const LType *result, const Term *term, const Bindings *caller) {
  const Bindings *chosen;
  Tokens after;
  Failure ignored;
  if (rest == NULL) return opaque_closure(name, ty);
  Tokens types = type_tokens_of(rest->head);
  const Values *values = rest->tail;
  if (!type_arguments(type_fuel(types), params, caller, NULL, types, &chosen, &after, NULL, &ignored))
    return opaque_closure(name, ty);
  const Params *formal = value_params(chosen, params);
  return closure_binding(name, drop_params(values_length(values), formal), subst_type(chosen, result), term,
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
    return unary_from(scope, item->params, item->type, term_tokens(item->term), op);
  case BIND_CLOSURE:
    return unary_from(item->scope, item->params, item->type, term_tokens(item->term), op);
  }
  return 0;
}

static int with_term(int ok, const Term **term, const Term *made);
static const Term *reference_term(Nat position, Text name, const Bindings *environment);

/* A name gives reference_term: TERM_VAR for a parameter or an inline binder. */
int unary_argument(const Bindings *environment, Tokens tokens, Unary *op, Tokens *rest, const Term **term,
                   Failure *failure) {
  const Binding *item;
  if (tokens.size == 0) return fail_at(failure, 0, eUnary);
  Token head = tokens.items[0];
  if (head.kind != TOKEN_IDENTIFIER) return fail_at(failure, head.position, eUnary);
  if (!lookup(head.text, environment, &item)) return fail_at(failure, head.position, eUnary);
  if (!unary_of(definition_scope(head.text, environment), item, op)) return fail_at(failure, head.position, eUnary);
  *rest = (Tokens){tokens.items + 1, tokens.size - 1};
  return with_term(1, term, term != NULL ? reference_term(head.position, head.text, environment) : NULL);
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

/* A name gives reference_term, as unary_argument does. */
int stepper_argument(const Bindings *environment, Tokens tokens, Stepper *op, Tokens *rest, const Term **term,
                     Failure *failure) {
  if (tokens.size == 0) return fail_at(failure, 0, eStep);
  Token head = tokens.items[0];
  const Binding *item;
  if (head.kind != TOKEN_IDENTIFIER || !lookup(head.text, environment, &item)) return fail_at(failure, head.position, eStep);
  switch (item->kind) {
  case BIND_FUN:
    if (has_type_param(item->params)) return fail_at(failure, head.position, eStep);
    *op = (Stepper){item->params, item->type, term_tokens(item->term), definition_scope(item->name, environment)};
    break;
  case BIND_CLOSURE: *op = (Stepper){item->params, item->type, term_tokens(item->term), item->scope}; break;
  case BIND_VALUE: return fail_at(failure, head.position, eStep);
  case BIND_TYPE: return fail_at(failure, head.position, eStep);
  case BIND_ARROW: return fail_at(failure, head.position, eStep);
  }
  *rest = (Tokens){tokens.items + 1, tokens.size - 1};
  return with_term(1, term, term != NULL ? reference_term(head.position, head.text, environment) : NULL);
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
  return stepper_argument(environment, tokens, &op, &rest, NULL, &failure) ? 1 : 0;
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

/* S5b1: checker.mech lines 1364..1869 (synthTerm to partialStepper), the
   first half of the mutual group. A def that matches on Fuel fails (or
   gives none) at fuel 0 and passes fuel - 1 on. */
static int worked_typed(Typed found, Tokens after, Nat budget, Typed *typed, Tokens *rest, Nat *left) {
  *typed = found;
  *rest = after;
  *left = budget;
  return 1;
}

static int worked_value(const Value *found, Tokens after, Nat budget, const Value **value, Tokens *rest, Nat *left) {
  *value = found;
  *rest = after;
  *left = budget;
  return 1;
}

/* takeCount (dropCount rest body) body: the body tokens before rest. */
Tokens taken_tokens(Tokens body, Tokens rest) { return (Tokens){body.items, nat_sub(body.size, rest.size)}; }

/* The Term of a checked body (D3-s2). A helper with a NULL out parameter
   builds no node. with_term writes made when ok is 1. A NULL item in a
   list of terms is a form that is not built yet, and its parent is NULL. */
static int with_term(int ok, const Term **term, const Term *made) {
  if (ok == 1 && term != NULL) *term = made;
  return ok;
}

static const Term **want_term(const void *wanted, const Term **slot) { return wanted != NULL ? slot : NULL; }
static const Terms **want_terms(const void *wanted, const Terms **slot) { return wanted != NULL ? slot : NULL; }
static const TermTypes **want_types(const void *wanted, const TermTypes **slot) { return wanted != NULL ? slot : NULL; }

static Nat terms_built(const Terms *terms) {
  for (; terms != NULL; terms = terms->tail)
    if (terms->head == NULL) return 0;
  return 1;
}

static const Terms *reverse_terms_onto(const Terms *done, const Terms *terms) {
  for (; terms != NULL; terms = terms->tail) done = terms_item(terms->head, done);
  return done;
}

static const Term *named_term(TermTag tag, Nat position, Text name, const TermTypes *types, const Terms *args,
                              const Bindings *environment) {
  if (terms_built(args) != 1) return NULL;
  if (tag == TERM_APPLY || tag == TERM_PARTIAL)
    return term_call(tag, position, 0, reference_term(position, name, environment), types, args);
  return term_named(tag, position, 0, name, types, args);
}

static const Term *form_term(TermTag tag, Nat position, const Terms *args) {
  return terms_built(args) == 1 ? term_form(tag, position, 0, args) : NULL;
}

/* The tag of the structure form 2 map, 3 bind or 4 filter. */
static TermTag structure_tag(Nat form) {
  switch (form) {
  case 2: return TERM_MAP;
  case 3: return TERM_BIND;
  }
  return TERM_FILTER;
}

/* The scope of a body from the head: the binders of each inline fun with a
   check_marker below them, the body_marker with the count n, the n
   parameters (the last one first) and the definitions. A parameter has
   its position, 0 to n - 1. An inline binder has n plus the count of the
   inline binders below it. */
static int param_index(const Binding *item, const Bindings *params, Nat count, Nat *index) {
  for (Nat at = 0; at < count && params != NULL; at++, params = params->tail)
    if (&params->head == item) {
      *index = count - 1 - at;
      return 1;
    }
  return 0;
}

static int binder_index(const Binding *item, const Bindings *environment, Nat *index) {
  Nat seen = 0;
  Nat below = 0;
  for (; environment != NULL; environment = environment->tail) {
    const Binding *cell = &environment->head;
    Nat count;
    if (cell->kind == BIND_VALUE && cell->name.size == 0) {
      if (!as_nat(cell->value, &count)) continue;
      if (seen == 0) return param_index(item, environment->tail, count, index);
      *index = count + below;
      return 1;
    }
    if (cell == item) seen = 1;
    else if (seen == 1) below = below + 1;
  }
  return 0;
}

/* A type parameter has a structural name based on its binder position.
   Source identifiers cannot contain #, so these identities cannot alias
   nominal schema names. Keep the resolved type and source text unchanged. */
static const LType *term_type_identity(const LType *type, const Bindings *environment) {
  const Bindings *chosen = NULL;
  for (const Bindings *at = environment; at != NULL; at = at->tail) {
    const Binding *item = &at->head;
    const Binding *ignored;
    Nat index;
    if (item->kind != BIND_TYPE || lookup(item->name, chosen, &ignored) ||
        binder_index(item, environment, &index) != 1)
      continue;
    const LType *identity = schema_of(append_text(text_one(35), number_text(index)));
    chosen = bindings_item(type_binding(item->name, item->type, identity), chosen);
  }
  return chosen != NULL ? subst_type(chosen, type) : type;
}

/* A value name: TERM_VAR for a parameter or an inline binder, TERM_NAME
   for a definition. */
static const Term *value_term(Nat position, const Binding *item, const Bindings *environment) {
  Nat index;
  if (binder_index(item, environment, &index) == 1) return term_var(position, 0, item->name, index);
  return term_named(TERM_NAME, position, 0, item->name, NULL, NULL);
}

static const Term *reference_term(Nat position, Text name, const Bindings *environment) {
  const Binding *item;
  if (lookup(name, environment, &item)) return value_term(position, item, environment);
  return term_named(TERM_NAME, position, 0, name, NULL, NULL);
}

/* The binders of an inline fun as term types; tokens holds ( name : type )
   for each binder. */
static const TermTypes *binder_types(const Params *params, Tokens tokens, const Bindings *environment) {
  if (params == NULL || tokens.size < 4) return NULL;
  Nat depth = 0;
  Nat at = 3;
  for (; at < tokens.size; at++) {
    Token token = tokens.items[at];
    if (token.kind != TOKEN_PUNCTUATION) continue;
    if (token.number == 40) depth = depth + 1;
    if (token.number == 41) {
      if (depth == 0) break;
      depth = depth - 1;
    }
  }
  Token name = tokens.items[1];
  TermType head = {.name = name.text,
                   .position = name.position,
                   .type = params->head.type,
                   .source = (Tokens){tokens.items + 3, at - 3},
                   .identity = term_type_identity(params->head.type, environment)};
  Nat next = at + 1 < tokens.size ? at + 1 : tokens.size;
  return term_types_item(head, binder_types(params->tail, (Tokens){tokens.items + next, tokens.size - next}, environment));
}

int synth_term(Fuel fuel, Nat budget, Nat atom, const Bindings *environment, Tokens tokens, Typed *typed, Tokens *rest,
               Nat *left, const Term **term, Failure *failure) {
  if (fuel == 0) return fail_at(failure, first_position(tokens), eFuel);
  Fuel more = fuel - 1;
  if (tokens.size == 0) return fail_at(failure, 0, eInfer);
  Token head = tokens.items[0];
  Tokens tail = {tokens.items + 1, tokens.size - 1};
  Typed found;
  Tokens after;
  Nat spent;
  switch (head.kind) {
  case TOKEN_NUMBER:
  case TOKEN_STRING: return fail_at(failure, head.position, eInfer);
  case TOKEN_PUNCTUATION:
    if (head.number != 40) return fail_at(failure, head.position, eInfer);
    const Term *inner = NULL;
    if (!synth_term(more, budget, 0, environment, tail, &found, &after, &spent, want_term(term, &inner), failure))
      return 0;
    *typed = found;
    return with_term(lift_parsed(spent, close_parsed(after, rest, failure), left), term,
                     inner != NULL ? term_form(TERM_GROUP, head.position, 0, terms_item(inner, NULL)) : NULL);
  case TOKEN_IDENTIFIER: {
    const Binding *item;
    if (lookup(head.text, environment, &item)) {
      switch (item->kind) {
      case BIND_VALUE:
        if (proof_in_scope(item->name, item->type, environment))
          return with_term(worked_typed((Typed){item->type, item->value}, tail, budget, typed, rest, left), term,
                           term != NULL ? value_term(head.position, item, environment) : NULL);
        return fail_at(failure, head.position, eTerm);
      case BIND_TYPE:
      case BIND_ARROW: return fail_at(failure, head.position, eInfer);
      case BIND_FUN: {
        if (atom == 1) return fail_at(failure, head.position, eParen);
        const Bindings *chosen;
        Tokens after_types;
        const TermTypes *types = NULL;
        if (!type_arguments(more, item->params, environment, NULL, tail, &chosen, &after_types,
                            want_types(term, &types), failure))
          return 0;
        const Values *values;
        const Terms *args = NULL;
        if (!dependent_arguments(more, budget, chosen, environment, item->params, item->params, NULL, after_types,
                                 after_types, &values, &after, &spent, want_terms(term, &args), failure))
          return 0;
        const Term *applied_term =
            term != NULL ? named_term(TERM_APPLY, head.position, head.text, types, args, environment) : NULL;
        const LType *instantiated = NULL;
        int resolved = instantiate_result(more, environment, item->params, values, after_types,
                                          subst_type(chosen, item->type), &instantiated);
        const LType *applied;
        if (!close_result(more, environment, item->params, values, resolved, instantiated, &applied))
          return fail_at(failure, head.position, eTerm);
        if (checking_body(environment) == 1)
          return with_term(worked_typed((Typed){applied, &null_value}, after, spent, typed, rest, left), term,
                           applied_term);
        const Params *closed =
            close_params(more, environment, item->params, values,
                         instantiate_params(more, environment, item->params, values, after_types, item->params));
        const Bindings *scope = bind_arguments(environment, value_params(chosen, closed), values,
                                               reverse_bindings_onto(definition_scope(item->name, environment), chosen));
        const Value *value;
        Tokens ignored;
        Nat used;
        if (item->term != NULL && eval_term(more, nat_sub(spent, 1), applied, scope, item->term, &value, &used))
          return with_term(worked_typed((Typed){applied, value}, after, used, typed, rest, left), term, applied_term);
        /* The evaluator gave 0: the token path gives the value or the failure. */
        if (!parse_term(more, nat_sub(spent, 1), 0, applied, scope, term_tokens(item->term), &value, &ignored, &used,
                        NULL, failure))
          return 0;
        return with_term(worked_typed((Typed){applied, value}, after, used, typed, rest, left), term, applied_term);
      }
      case BIND_CLOSURE: {
        if (dependent_result(item->type) == 1 || dependent_params(item->params) == 1)
          return fail_at(failure, head.position, eTerm);
        if (atom == 1) return fail_at(failure, head.position, eParen);
        const Values *values;
        const Terms *args = NULL;
        if (!parse_arguments(more, budget, 1, param_types(item->params), environment, tail, &values, &after, &spent,
                             want_terms(term, &args), failure))
          return 0;
        const Term *applied_term =
            term != NULL ? named_term(TERM_APPLY, head.position, head.text, NULL, args, environment) : NULL;
        if (checking_body(environment) == 1)
          return with_term(worked_typed((Typed){item->type, &null_value}, after, spent, typed, rest, left), term,
                           applied_term);
        const Bindings *scope = bind_arguments(environment, item->params, values, item->scope);
        const Value *value;
        Tokens ignored;
        Nat used;
        if (item->term != NULL && eval_term(more, nat_sub(spent, 1), item->type, scope, item->term, &value, &used))
          return with_term(worked_typed((Typed){item->type, value}, after, used, typed, rest, left), term,
                           applied_term);
        /* The evaluator gave 0: the token path gives the value or the failure. */
        if (!parse_term(more, nat_sub(spent, 1), 0, item->type, scope, term_tokens(item->term), &value, &ignored,
                        &used, NULL, failure))
          return 0;
        return with_term(worked_typed((Typed){item->type, value}, after, used, typed, rest, left), term,
                         applied_term);
      }
      }
      return 0;
    }
    Nat form = synth_form(head.text);
    if (form == 0) return fail_at(failure, head.position, eInfer);
    if (atom == 1) return fail_at(failure, head.position, eParen);
    if (form == 5)
      return either_term(more, budget, head.position, environment, tail, typed, rest, left, term, failure);
    const Term *first = NULL;
    if (!synth_term(more, budget, 1, environment, tail, &found, &after, &spent, want_term(term, &first), failure))
      return 0;
    if (form < 3)
      return with_term(lift_parsed(spent, project(head.position, form, found, after, typed, rest, failure), left), term,
                       term != NULL ? form_term(form == 1 ? TERM_FIRST : TERM_SECOND, head.position,
                                                terms_item(first, NULL))
                                    : NULL);
    if (form == 3)
      return with_term(lift_parsed(spent, symm_proof(head.position, found, after, typed, rest, failure), left), term,
                       term != NULL ? form_term(TERM_SYMM, head.position, terms_item(first, NULL)) : NULL);
    Typed other;
    Tokens later;
    Nat used;
    const Term *second = NULL;
    if (!synth_term(more, spent, 1, environment, after, &other, &later, &used, want_term(term, &second), failure))
      return 0;
    return with_term(
        lift_parsed(used, trans_proof(head.position, found, other, later, typed, rest, failure), left), term,
        term != NULL ? form_term(TERM_TRANS, head.position, terms_item(first, terms_item(second, NULL))) : NULL);
  }
  }
  return 0;
}

/* checkWorked position expected (synthTerm fuel budget atom environment tokens). */
static int checked_synth(Fuel fuel, Nat budget, Nat atom, Nat position, const LType *expected,
                         const Bindings *environment, Tokens tokens, const Value **value, Tokens *rest, Nat *left,
                         const Term **term, Failure *failure) {
  Typed found;
  Tokens after;
  Nat spent;
  const Term *made = NULL;
  if (!synth_term(fuel, budget, atom, environment, tokens, &found, &after, &spent, want_term(term, &made), failure))
    return 0;
  return with_term(check_worked(position, expected, found, after, spent, value, rest, left, failure), term, made);
}

int parse_term(Fuel fuel, Nat budget, Nat atom, const LType *expected, const Bindings *environment, Tokens tokens,
               const Value **value, Tokens *rest, Nat *left, const Term **term, Failure *failure) {
  if (fuel == 0) return fail_at(failure, first_position(tokens), eFuel);
  Fuel more = fuel - 1;
  if (budget == 0) return fail_at(failure, first_position(tokens), eBudget);
  if (tokens.size == 0) return fail_at(failure, 0, eTerm);
  Token head = tokens.items[0];
  Tokens tail = {tokens.items + 1, tokens.size - 1};
  switch (head.kind) {
  case TOKEN_NUMBER:
    if (same_type(expected, &nat_type))
      return with_term(worked_value(nat_value(head.number), tail, budget, value, rest, left), term,
                       term != NULL ? term_number(head.position, 0, head.number) : NULL);
    return fail_at(failure, head.position, eTerm);
  case TOKEN_STRING:
    if (same_type(expected, &text_type))
      return with_term(worked_value(text_value(head.text), tail, budget, value, rest, left), term,
                       term != NULL ? term_string(head.position, 0, head.text) : NULL);
    return fail_at(failure, head.position, eTerm);
  case TOKEN_PUNCTUATION: {
    if (head.number != 40) return fail_at(failure, head.position, eTerm);
    const Value *inside;
    Tokens after;
    Nat spent;
    const Term *inner = NULL;
    if (!parse_term(more, budget, 0, expected, environment, tail, &inside, &after, &spent, want_term(term, &inner),
                    failure))
      return 0;
    *value = inside;
    return with_term(lift_parsed(spent, close_parsed(after, rest, failure), left), term,
                     inner != NULL ? term_form(TERM_GROUP, head.position, 0, terms_item(inner, NULL)) : NULL);
  }
  case TOKEN_IDENTIFIER: {
    if (same_text(head.text, sfun) == 1 && is_arrow_type(expected) == 1) {
      if (atom == 1) return fail_at(failure, head.position, eParen);
      return inline_argument(more, budget, head.position, expected, environment, tail, value, rest, left, term,
                             failure);
    }
    const Binding *item;
    if (lookup(head.text, environment, &item)) {
      switch (item->kind) {
      case BIND_VALUE:
        if (proof_in_scope(item->name, item->type, environment) && same_type(expected, item->type))
          return with_term(worked_value(item->value, tail, budget, value, rest, left), term,
                           term != NULL ? value_term(head.position, item, environment) : NULL);
        return fail_at(failure, head.position, eTerm);
      case BIND_TYPE:
      case BIND_ARROW: return fail_at(failure, head.position, eTerm);
      case BIND_FUN:
      case BIND_CLOSURE:
        if (is_arrow_type(expected) == 1)
          return partial_argument(more, budget, atom, head.position, expected, head.text, item->params, item->type,
                                  environment, tail, value, rest, left, term, failure);
        return checked_synth(more, budget, atom, head.position, expected, environment, tokens, value, rest, left,
                             term, failure);
      }
      return 0;
    }
    Plan selected;
    if (!constructor_plan(expected, head.text, &selected)) {
      if (synth_form(head.text) != 0)
        return checked_synth(more, budget, atom, head.position, expected, environment, tokens, value, rest, left,
                             term, failure);
      Nat form = structure_form(head.text);
      if (form == 0) {
        if (same_text(head.text, srefl))
          return with_term(lift_parsed(budget, refl_check(head.position, expected, tail, value, rest, failure), left),
                           term, term != NULL ? term_form(TERM_REFL, head.position, 0, NULL) : NULL);
        return fail_at(failure, head.position, unknown_name(expected, head.text));
      }
      if (form < 5)
        return structure_term(more, budget, head.position, form, atom, expected, environment, tail, value, rest, left,
                              term, failure);
      if (form == 5)
        return fold_term(more, budget, head.position, atom, expected, environment, tail, value, rest, left, term,
                         failure);
      return unfold_term(more, budget, head.position, atom, expected, environment, tail, value, rest, left, term,
                         failure);
    }
    if (atom == 1 && has_arguments(plan_arguments(&selected)) == 1) return fail_at(failure, head.position, eParen);
    const Values *values;
    Tokens after;
    Nat spent;
    const Terms *args = NULL;
    if (!parse_arguments(more, budget, 1, plan_arguments(&selected), environment, tail, &values, &after, &spent,
                         want_terms(term, &args), failure))
      return 0;
    const Term *built =
        term != NULL ? named_term(TERM_CONSTRUCT, head.position, head.text, NULL, args, environment) : NULL;
    const Value *made;
    Failure refused;
    if (evaluate_plan(&selected, values, &made, &refused))
      return with_term(worked_value(made, after, spent, value, rest, left), term, built);
    if (checking_body(environment))
      return with_term(worked_value(&null_value, after, spent, value, rest, left), term, built);
    return fail_at(failure, head.position, refused.message);
  }
  }
  return 0;
}

/* D3-s3 part A: the evaluator of a checked body term. It is parse_term and
   synth_term with a Term in place of the tokens: the same helpers, the same
   fuel steps and the same work charges in the same order. It reports no
   failure. It gives 0 (the caller replays the tokens) when the budget is 0
   at the entry of a node, for an arrow expected type other than a FUN or
   PARTIAL argument (Q-S4-4), for a dependent callee, at the fuel margin of
   the type arguments (Q-S3-3) and for the keyword forms (part B). */
static const Tokens no_tokens = {NULL, 0};

static int eval_worked(const Value *found, Nat budget, const Value **value, Nat *left) {
  *value = found;
  *left = budget;
  return 1;
}

static int eval_typed(Typed found, Nat budget, Typed *typed, Nat *left) {
  *typed = found;
  *left = budget;
  return 1;
}

static const Term *first_arg(const Term *term) { return term->args != NULL ? term->args->head : NULL; }

static const Term *second_arg(const Term *term) {
  return term->args != NULL && term->args->tail != NULL ? term->args->tail->head : NULL;
}

/* parse_arguments on the argument terms. */
static int eval_arguments(Fuel fuel, Nat budget, const LTypes *types, const Bindings *environment, const Terms *args,
                          const Values **values, Nat *left) {
  const Values *done = NULL;
  for (;; types = types->tail, args = args->tail) {
    if (fuel == 0) return 0;
    fuel = fuel - 1;
    if (types == NULL) {
      if (args != NULL) return 0;
      *values = reverse_values_onto(NULL, done);
      *left = budget;
      return 1;
    }
    if (args == NULL) return 0;
    const Value *value;
    if (!eval_term(fuel, budget, types->head, environment, args->head, &value, &budget)) return 0;
    done = values_item(value, done);
  }
}

/* dependent_arguments on the argument terms. The callee is not dependent,
   thus instantiate_result reads no argument token. */
static int eval_dependent(Fuel fuel, Nat budget, const Bindings *chosen, const Bindings *environment,
                          const Params *params, const Params *remaining, const Values *seen, const Terms *args,
                          const Values **values, Nat *left) {
  for (;; remaining = remaining->tail) {
    if (fuel == 0) return 0;
    fuel = fuel - 1;
    if (remaining == NULL) {
      if (args != NULL) return 0;
      *values = reverse_values_onto(NULL, seen);
      *left = budget;
      return 1;
    }
    Param head = remaining->head;
    if (is_type_param(head) == 1) continue;
    if (args == NULL) return 0;
    const Values *earlier = reverse_values_onto(NULL, seen);
    const LType *instantiated = NULL;
    int resolved =
        instantiate_result(fuel, environment, params, earlier, no_tokens, subst_type(chosen, head.type), &instantiated);
    const LType *expected;
    if (!close_result(fuel, environment, params, earlier, resolved, instantiated, &expected)) return 0;
    const Value *value;
    if (!eval_term(fuel, budget, expected, environment, args->head, &value, &budget)) return 0;
    seen = values_item(value, seen);
    args = args->tail;
  }
}

/* Q-S3-3: type_arguments without the type tokens. Each type argument is the
   checked type with the type bindings of the run-time scope. */
static int eval_type_arguments(const Params *params, const Bindings *environment, const TermTypes *types,
                               const Bindings **result) {
  const Bindings *chosen = NULL;
  for (; params != NULL && is_type_param(params->head) == 1; params = params->tail, types = types->tail) {
    if (types == NULL) return 0;
    const LType *given = subst_type(environment, types->head.type);
    if (type_level(given) != 0) return 0;
    chosen = bindings_item(type_binding(params->head.name, params->head.type, given), chosen);
  }
  if (types != NULL) return 0;
  *result = chosen;
  return 1;
}

/* synth_term on an application: fuel is the fuel of the callee step. */
static int eval_apply(Fuel fuel, Nat budget, const Bindings *environment, const Term *term, Typed *typed, Nat *left) {
  const Binding *item;
  if (!lookup(term->name, environment, &item)) return 0;
  if (dependent_result(item->type) == 1 || dependent_params(item->params) == 1) return 0;
  switch (item->kind) {
  case BIND_VALUE:
  case BIND_TYPE:
  case BIND_ARROW: return 0;
  case BIND_FUN: {
    /* The margin bounds the parse_type depth that the evaluator skips. */
    if (term->types != NULL && fuel <= term_text(term).size + 1) return 0;
    const Bindings *chosen;
    if (!eval_type_arguments(item->params, environment, term->types, &chosen)) return 0;
    const Values *values;
    Nat spent;
    if (!eval_dependent(fuel, budget, chosen, environment, item->params, item->params, NULL, term->args, &values,
                        &spent))
      return 0;
    const LType *instantiated = NULL;
    int resolved = instantiate_result(fuel, environment, item->params, values, no_tokens,
                                      subst_type(chosen, item->type), &instantiated);
    const LType *applied;
    if (!close_result(fuel, environment, item->params, values, resolved, instantiated, &applied)) return 0;
    if (checking_body(environment) == 1) return eval_typed((Typed){applied, &null_value}, spent, typed, left);
    if (item->term == NULL) return 0;
    const Params *closed =
        close_params(fuel, environment, item->params, values,
                     instantiate_params(fuel, environment, item->params, values, no_tokens, item->params));
    const Bindings *scope = bind_arguments(environment, value_params(chosen, closed), values,
                                           reverse_bindings_onto(definition_scope(item->name, environment), chosen));
    const Value *value;
    Nat used;
    if (!eval_term(fuel, nat_sub(spent, 1), applied, scope, item->term, &value, &used)) return 0;
    return eval_typed((Typed){applied, value}, used, typed, left);
  }
  case BIND_CLOSURE: {
    const Values *values;
    Nat spent;
    if (!eval_arguments(fuel, budget, param_types(item->params), environment, term->args, &values, &spent)) return 0;
    if (checking_body(environment) == 1) return eval_typed((Typed){item->type, &null_value}, spent, typed, left);
    const Bindings *scope = bind_arguments(environment, item->params, values, item->scope);
    const Value *value;
    Nat used;
    /* The closure body term first. A 0 there runs the body tokens here, as the
       application site does (Q-S4-3). */
    if (item->term != NULL && eval_term(fuel, nat_sub(spent, 1), item->type, scope, item->term, &value, &used))
      return eval_typed((Typed){item->type, value}, used, typed, left);
    Tokens ignored;
    Failure failure;
    if (!parse_term(fuel, nat_sub(spent, 1), 0, item->type, scope, term_tokens(item->term), &value, &ignored, &used,
                    NULL, &failure))
      return 0;
    return eval_typed((Typed){item->type, value}, used, typed, left);
  }
  }
  return 0;
}

static int apply_body(Fuel fuel, Nat budget, const LType *expected, const Bindings *environment, Tokens body,
                      const Term *term, const Value **value, Tokens *rest, Nat *left, Failure *failure);

static const Term *third_arg(const Term *term) {
  return term->args != NULL && term->args->tail != NULL && term->args->tail->tail != NULL
             ? term->args->tail->tail->head
             : NULL;
}

/* unary_argument on a name term. A function or a closure gives its body term
   (D3-s4). A closure with dependent params keeps the body tokens. */
static int eval_unary_argument(const Bindings *environment, const Term *term, Unary *op) {
  const Binding *item;
  if (term == NULL || !lookup(term->name, environment, &item)) return 0;
  if (!unary_of(definition_scope(term->name, environment), item, op)) return 0;
  switch (item->kind) {
  case BIND_VALUE:
  case BIND_TYPE:
  case BIND_ARROW: return 0;
  case BIND_FUN:
    op->term = item->term;
    return dependent_params(item->params) == 0;
  case BIND_CLOSURE:
    op->term = dependent_params(item->params) == 0 ? item->term : NULL;
    return 1;
  }
  return 0;
}

static int eval_partial_unary(Fuel fuel, Nat budget, const LType *wanted, const Bindings *environment,
                              const Term *term, Unary *op, Nat *left);

/* unary_term on the head term of a keyword form. */
static int eval_unary(Fuel fuel, Nat budget, const LType *wanted, const Bindings *environment, const Term *term,
                      Unary *op, Nat *left) {
  if (term == NULL || fuel == 0) return 0;
  Fuel more = fuel - 1;
  switch (term->tag) {
  case TERM_VAR:
  case TERM_NAME:
    if (!eval_unary_argument(environment, term, op)) return 0;
    *left = budget;
    return 1;
  case TERM_GROUP: return eval_partial_unary(more, budget, wanted, environment, first_arg(term), op, left);
  case TERM_NUMBER:
  case TERM_STRING:
  case TERM_APPLY:
  case TERM_PARTIAL:
  case TERM_FUN:
  case TERM_CONSTRUCT:
  case TERM_REFL:
  case TERM_FIRST:
  case TERM_SECOND:
  case TERM_SYMM:
  case TERM_TRANS:
  case TERM_EITHER:
  case TERM_PURE:
  case TERM_MAP:
  case TERM_BIND:
  case TERM_FILTER:
  case TERM_FOLD:
  case TERM_FOLD_VALUE:
  case TERM_UNFOLD:
  case TERM_UNFOLD_VALUE:
  case TERM_BODY: return 0;
  }
  return 0;
}

/* inline_unary on a FUN term. The token path checks the body here in check
   mode with no charge. The evaluator does not, thus it gives 0 at budget 0
   and at fuel at or below the margin (finding a, Q-S3-3). */
static int eval_inline_unary(Fuel fuel, Nat budget, const LType *wanted, const Bindings *environment,
                             const Term *term, Unary *op, Nat *left) {
  if (fuel == 0 || budget == 0 || term->types == NULL || term->types->tail != NULL || first_arg(term) == NULL)
    return 0;
  if (fuel <= term_text(term).size + 2) return 0;
  TermType binder = term->types->head;
  const LType *ty = subst_type(environment, binder.type);
  if (type_level(ty) != 0) return 0;
  *op = (Unary){binder.name, ty, wanted, (Tokens){0}, environment, first_arg(term)};
  *left = budget;
  return 1;
}

/* 1 when partial_unary makes a bound_unary op from the binding. */
static Nat partial_callee(const Binding *item) {
  switch (item->kind) {
  case BIND_VALUE:
  case BIND_TYPE:
  case BIND_ARROW: return 0;
  case BIND_FUN: return dependent_params(item->params) == 1 ? 0 : 1;
  case BIND_CLOSURE: return 1;
  }
  return 0;
}

/* bound_unary on a PARTIAL term. A callee with type params gives 0, because
   typed_bound keeps the type tokens (finding b). A function callee gives its
   body term in the closure scope; a closure callee keeps the body tokens. */
static int eval_bound_unary(Fuel fuel, Nat budget, const Bindings *environment, const Term *term, Unary *op,
                            Nat *left) {
  const Binding *item;
  if (fuel == 0 || !lookup(term->name, environment, &item) || partial_callee(item) == 0) return 0;
  if (has_type_param(item->params) == 1) return 0;
  Fuel more = fuel - 1;
  const Params *formal = value_params(NULL, item->params);
  const Params *front = front_params(formal);
  const Values *values;
  Nat spent;
  if (!eval_arguments(more, budget, param_types(front), environment, term->args, &values, &spent)) return 0;
  if (bound_functions(front, values) == 0) return 0;
  Binding closure = partial_closure(
      term->name, arrow_type(drop_params(params_length(front), formal), subst_type(NULL, item->type)), term->name,
      values, environment);
  if (!unary_of(environment, &closure, op)) return 0;
  op->term = closure.term;
  *left = spent;
  return 1;
}

/* partial_unary on the inner term of a GROUP head. */
static int eval_partial_unary(Fuel fuel, Nat budget, const LType *wanted, const Bindings *environment,
                              const Term *term, Unary *op, Nat *left) {
  if (term == NULL || fuel == 0) return 0;
  Fuel more = fuel - 1;
  switch (term->tag) {
  case TERM_GROUP: return eval_unary(more, budget, wanted, environment, term, op, left);
  case TERM_FUN: return eval_inline_unary(more, budget, wanted, environment, term, op, left);
  case TERM_PARTIAL: return eval_bound_unary(more, budget, environment, term, op, left);
  case TERM_NUMBER:
  case TERM_STRING:
  case TERM_VAR:
  case TERM_NAME:
  case TERM_APPLY:
  case TERM_CONSTRUCT:
  case TERM_REFL:
  case TERM_FIRST:
  case TERM_SECOND:
  case TERM_SYMM:
  case TERM_TRANS:
  case TERM_EITHER:
  case TERM_PURE:
  case TERM_MAP:
  case TERM_BIND:
  case TERM_FILTER:
  case TERM_FOLD:
  case TERM_FOLD_VALUE:
  case TERM_UNFOLD:
  case TERM_UNFOLD_VALUE:
  case TERM_BODY: return 0;
  }
  return 0;
}

/* structure_term on a PURE, MAP, BIND or FILTER term: fuel is the fuel of
   structure_term. The steps and the charges are those of structure_term. */
static int eval_structure(Fuel fuel, Nat budget, Nat form, const LType *expected, const Bindings *environment,
                          const Term *term, const Value **value, Nat *left) {
  if (fuel == 0 || shape_code(form, expected) == 0) return 0;
  Fuel more = fuel - 1;
  if (form == 1) {
    const Value *lifted;
    Nat spent;
    if (!eval_term(more, budget, shape_element(expected), environment, first_arg(term), &lifted, &spent)) return 0;
    return eval_worked(pure_value(expected, lifted), spent, value, left);
  }
  Unary op;
  Nat spent;
  if (!eval_unary(more, budget, structure_result(form, expected), environment, first_arg(term), &op, &spent))
    return 0;
  if (structure_fits(form, expected, op) != 1) return 0;
  const Value *source;
  Nat used;
  if (!eval_term(more, spent, structure_source(form, expected, op), environment, second_arg(term), &source, &used))
    return 0;
  if (checking_body(environment) == 1) return eval_worked(&null_value, used, value, left);
  Tokens ignored;
  Failure failure;
  if (carrier_code(expected) == 2) {
    const Values *items;
    Nat mapped_left;
    if (!map_items(more, used, term->position, form, op, sequence_elements(source), &items, &ignored, &mapped_left,
                   &failure))
      return 0;
    const Value *rebuilt;
    if (!rebuild(expected, items, &rebuilt, &failure)) return 0;
    return eval_worked(rebuilt, mapped_left, value, left);
  }
  const Value *item;
  if (!payload_of(expected, unary_param(op), source, &item)) return eval_worked(source, used, value, left);
  const Value *applied;
  Nat applied_left;
  if (!apply_body(more, nat_sub(used, 1), unary_result(op), unary_environment(op, item), unary_body(op), op.term,
                  &applied, &ignored, &applied_left, &failure))
    return 0;
  return eval_worked(step_one(form, expected, source, applied), applied_left, value, left);
}

/* either_term on an EITHER term: fuel is the fuel of either_term. */
static int eval_either(Fuel fuel, Nat budget, const Bindings *environment, const Term *term, Typed *typed,
                       Nat *left) {
  if (fuel == 0) return 0;
  Fuel more = fuel - 1;
  Unary on_left;
  Unary on_right;
  if (!eval_unary_argument(environment, first_arg(term), &on_left) ||
      !eval_unary_argument(environment, second_arg(term), &on_right))
    return 0;
  const LType *result = unary_result(on_left);
  if (!(dependent_result(result) == 0 && same_type(result, unary_result(on_right)) == 1)) return 0;
  const Value *source;
  Nat spent;
  if (!eval_term(more, budget, type_two(TY_SUM, unary_param(on_left), unary_param(on_right)), environment,
                 third_arg(term), &source, &spent))
    return 0;
  if (checking_body(environment) == 1) return eval_typed((Typed){result, &null_value}, spent, typed, left);
  Unary chosen = sum_left(source) != 0 ? on_left : on_right;
  const Value *applied;
  Tokens ignored;
  Nat applied_left;
  Failure failure;
  if (!apply_body(more, nat_sub(spent, 1), result, unary_environment(chosen, project_value(1, source)),
                  unary_body(chosen), chosen.term, &applied, &ignored, &applied_left, &failure))
    return 0;
  return eval_typed((Typed){result, applied}, applied_left, typed, left);
}

static Nat terms_count(const Terms *terms) { return terms == NULL ? 0 : 1 + terms_count(terms->tail); }

static const Term *nth_term(const Terms *terms, Nat index) {
  if (terms == NULL) return NULL;
  if (index == 0) return terms->head;
  return nth_term(terms->tail, index - 1);
}

/* stepper_argument on a VAR or NAME head. A function gives its body term (0
   for dependent params); a closure gives its body term (the body tokens for
   dependent params). */
static int eval_stepper_argument(const Bindings *environment, const Term *term, Stepper *op) {
  const Binding *item;
  if (term == NULL || !lookup(term->name, environment, &item)) return 0;
  switch (item->kind) {
  case BIND_VALUE:
  case BIND_TYPE:
  case BIND_ARROW: return 0;
  case BIND_FUN:
    if (has_type_param(item->params) == 1 || dependent_params(item->params) == 1) return 0;
    *op = (Stepper){item->params, item->type, term_tokens(item->term), definition_scope(item->name, environment),
                    item->term};
    return 1;
  case BIND_CLOSURE:
    *op = (Stepper){item->params, item->type, term_tokens(item->term), item->scope,
                    dependent_params(item->params) == 0 ? item->term : NULL};
    return 1;
  }
  return 0;
}

static int eval_partial_stepper(Fuel fuel, Nat budget, Nat mode, const LType *expected, const Bindings *environment,
                                const Term *term, Stepper *op, Nat *left);

/* stepper_term on the function term of fold or unfold. */
static int eval_stepper(Fuel fuel, Nat budget, Nat mode, const LType *expected, const Bindings *environment,
                        const Term *term, Stepper *op, Nat *left) {
  if (term == NULL || fuel == 0) return 0;
  Fuel more = fuel - 1;
  switch (term->tag) {
  case TERM_VAR:
  case TERM_NAME:
    if (!eval_stepper_argument(environment, term, op)) return 0;
    *left = budget;
    return 1;
  case TERM_GROUP: return eval_partial_stepper(more, budget, mode, expected, environment, first_arg(term), op, left);
  case TERM_NUMBER:
  case TERM_STRING:
  case TERM_APPLY:
  case TERM_PARTIAL:
  case TERM_FUN:
  case TERM_CONSTRUCT:
  case TERM_REFL:
  case TERM_FIRST:
  case TERM_SECOND:
  case TERM_SYMM:
  case TERM_TRANS:
  case TERM_EITHER:
  case TERM_PURE:
  case TERM_MAP:
  case TERM_BIND:
  case TERM_FILTER:
  case TERM_FOLD:
  case TERM_FOLD_VALUE:
  case TERM_UNFOLD:
  case TERM_UNFOLD_VALUE:
  case TERM_BODY: return 0;
  }
  return 0;
}

/* The params of an inline fun from its binder types, or 0 when a binder type
   is not a type of level 0. */
static int binder_params(const Bindings *environment, const TermTypes *types, const Params **params) {
  if (types == NULL) {
    *params = NULL;
    return 1;
  }
  const LType *ty = subst_type(environment, types->head.type);
  const Params *later;
  if (type_level(ty) != 0 || !binder_params(environment, types->tail, &later)) return 0;
  *params = params_item((Param){types->head.name, ty}, later);
  return 1;
}

/* inline_stepper on a FUN term, with the margin rule of eval_inline_unary
   (finding a): 0 at budget 0 and at fuel at or below the margin. */
static int eval_inline_stepper(Fuel fuel, Nat budget, Nat mode, const LType *expected, const Bindings *environment,
                               const Term *term, Stepper *op, Nat *left) {
  if (fuel == 0 || budget == 0 || term->types == NULL || first_arg(term) == NULL) return 0;
  if (fuel <= term_text(term).size + 2) return 0;
  const Params *params;
  if (!binder_params(environment, term->types, &params)) return 0;
  const LType *result = inline_result(mode, expected, params);
  if (result == NULL) return 0;
  *op = (Stepper){params, result, (Tokens){0}, environment, first_arg(term)};
  *left = budget;
  return 1;
}

/* bound_arguments on the argument terms: one fuel step per parameter, then
   parse_arguments on one argument. */
static int eval_bound_arguments(Fuel fuel, Nat budget, const Params *params, const Bindings *environment,
                                const Terms *args, const Values **values, Nat *left) {
  if (fuel == 0) return 0;
  Fuel more = fuel - 1;
  if (params == NULL && args != NULL) return 0;
  if (params == NULL || args == NULL) {
    *values = NULL;
    *left = budget;
    return 1;
  }
  const Values *found;
  Nat spent;
  if (!eval_arguments(more, budget, param_types(params_item(params->head, NULL)), environment,
                      terms_item(args->head, NULL), &found, &spent))
    return 0;
  const Values *later;
  Nat used;
  if (!eval_bound_arguments(more, spent, params->tail, environment, args->tail, &later, &used)) return 0;
  *values = reverse_values_onto(later, reverse_values_onto(NULL, found));
  *left = used;
  return 1;
}

/* bound_stepper on a PARTIAL term. A callee with type params gives 0
   (finding b). A function or a closure callee gives its body term in the
   closure scope (D3-s4). */
static int eval_bound_stepper(Fuel fuel, Nat budget, const Bindings *environment, const Term *term, Stepper *op,
                              Nat *left) {
  const Binding *item;
  if (fuel == 0 || !lookup(term->name, environment, &item) || partial_callee(item) == 0) return 0;
  if (has_type_param(item->params) == 1) return 0;
  Fuel more = fuel - 1;
  const Params *formal = value_params(NULL, item->params);
  const Params *front = take_params(terms_count(term->args), formal);
  const Values *values;
  Nat spent;
  if (!eval_bound_arguments(more, budget, front, environment, term->args, &values, &spent)) return 0;
  if (bound_functions(front, values) == 0) return 0;
  Binding made = partial_closure(
      term->name, arrow_type(drop_params(params_length(front), formal), subst_type(NULL, item->type)), term->name,
      values, environment);
  const Term *body = made.term;
  switch (made.kind) {
  case BIND_VALUE:
  case BIND_TYPE:
  case BIND_ARROW: return 0;
  case BIND_FUN:
    *op = (Stepper){made.params, made.type, term_tokens(made.term), definition_scope(made.name, environment), body};
    break;
  case BIND_CLOSURE: *op = (Stepper){made.params, made.type, term_tokens(made.term), made.scope, body}; break;
  }
  *left = spent;
  return 1;
}

/* partial_stepper on the inner term of a GROUP head. */
static int eval_partial_stepper(Fuel fuel, Nat budget, Nat mode, const LType *expected, const Bindings *environment,
                                const Term *term, Stepper *op, Nat *left) {
  if (term == NULL || fuel == 0) return 0;
  Fuel more = fuel - 1;
  switch (term->tag) {
  case TERM_GROUP: return eval_stepper(more, budget, mode, expected, environment, term, op, left);
  case TERM_FUN: return eval_inline_stepper(more, budget, mode, expected, environment, term, op, left);
  case TERM_PARTIAL: return eval_bound_stepper(more, budget, environment, term, op, left);
  case TERM_NUMBER:
  case TERM_STRING:
  case TERM_VAR:
  case TERM_NAME:
  case TERM_APPLY:
  case TERM_CONSTRUCT:
  case TERM_REFL:
  case TERM_FIRST:
  case TERM_SECOND:
  case TERM_SYMM:
  case TERM_TRANS:
  case TERM_EITHER:
  case TERM_PURE:
  case TERM_MAP:
  case TERM_BIND:
  case TERM_FILTER:
  case TERM_FOLD:
  case TERM_FOLD_VALUE:
  case TERM_UNFOLD:
  case TERM_UNFOLD_VALUE:
  case TERM_BODY: return 0;
  }
  return 0;
}

/* fold_term on a FOLD term [f, start, source]: fuel is the fuel of
   fold_term. The token path selected FOLD because second_function gave 0.
   At lower fuel it gives 0 again, thus FOLD has no guard (finding c). */
static int eval_fold(Fuel fuel, Nat budget, const LType *expected, const Bindings *environment, const Term *term,
                     const Value **value, Nat *left) {
  if (fuel == 0) return 0;
  Fuel more = fuel - 1;
  Stepper op;
  Nat spent;
  if (!eval_stepper(more, budget, 0, expected, environment, first_arg(term), &op, &spent)) return 0;
  const Value *start;
  Nat used;
  if (!eval_term(more, spent, expected, environment, second_arg(term), &start, &used)) return 0;
  Typed found;
  Nat found_left;
  if (!eval_synth(more, used, environment, third_arg(term), &found, &found_left)) return 0;
  if (carrier_code(found.type) == 0 || fold_fits(found.type, expected, op) != 1) return 0;
  if (checking_body(environment) == 1) return eval_worked(&null_value, found_left, value, left);
  const Values *items;
  if (!elements_of(more, found.value, &items)) return 0;
  const Value *result;
  Tokens ignored;
  Nat folded_left;
  Failure failure;
  if (!fold_items(more, found_left, term->position, op, carrier_code(found.type), items, start, &result, &ignored,
                  &folded_left, &failure))
    return 0;
  return eval_worked(result, folded_left, value, left);
}

/* algebra_term on one of f2 to f5 of a FOLD_VALUE term. */
static int eval_algebra_term(Fuel fuel, Nat budget, Nat index, const LType *result, const Bindings *environment,
                             const Term *term, Stepper *op, Nat *left) {
  if (fuel == 0) return 0;
  Stepper found;
  Nat spent;
  if (!eval_stepper(fuel - 1, budget, 0, result, environment, term, &found, &spent)) return 0;
  if (same_type(stepper_result(found), result) == 0 ||
      same_types(param_types(stepper_params(found)), types_item(algebra_param(index, result), NULL)) == 0)
    return 0;
  *op = found;
  *left = spent;
  return 1;
}

/* algebra_terms on [f2, f3, f4, f5, ...] of a FOLD_VALUE term. */
static int eval_algebra_terms(Fuel fuel, Nat budget, const LType *result, Stepper on_nat,
                              const Bindings *environment, const Terms *terms, ValueAlgebra *ops, Nat *left) {
  if (fuel == 0) return 0;
  Fuel more = fuel - 1;
  Stepper on_flag, on_text, on_items, on_attrs;
  Nat flag_left, text_left, items_left, attrs_left;
  if (!eval_algebra_term(more, budget, 2, result, environment, nth_term(terms, 0), &on_flag, &flag_left) ||
      !eval_algebra_term(more, flag_left, 3, result, environment, nth_term(terms, 1), &on_text, &text_left) ||
      !eval_algebra_term(more, text_left, 4, result, environment, nth_term(terms, 2), &on_items, &items_left) ||
      !eval_algebra_term(more, items_left, 5, result, environment, nth_term(terms, 3), &on_attrs, &attrs_left))
    return 0;
  *ops = (ValueAlgebra){on_nat, on_flag, on_text, on_items, on_attrs};
  *left = attrs_left;
  return 1;
}

/* fold_term on a FOLD_VALUE term [f1, f2, f3, f4, f5, start, source]: fuel
   is the fuel of fold_term. The token path selects FOLD_VALUE with
   second_function, a trial parse of f2 at fuel - 2. The evaluator runs that
   trial first and gives 0 when it gives 0 (finding c). Then the steps of
   fold_value_term at fuel - 1. */
static int eval_fold_value(Fuel fuel, Nat budget, const LType *expected, const Bindings *environment,
                           const Term *term, const Value **value, Nat *left) {
  if (fuel <= 2) return 0;
  Fuel more = fuel - 1;
  Fuel inner = more - 1;
  Stepper on_nat;
  Nat spent;
  if (!eval_stepper(more, budget, 0, expected, environment, first_arg(term), &on_nat, &spent)) return 0;
  Stepper trial;
  Nat trial_left;
  if (!eval_algebra_term(inner, spent, 2, expected, environment, second_arg(term), &trial, &trial_left)) return 0;
  if (same_type(stepper_result(on_nat), expected) != 1 ||
      same_types(param_types(stepper_params(on_nat)), types_item(&nat_type, NULL)) != 1)
    return 0;
  ValueAlgebra ops;
  Nat functions_left;
  if (!eval_algebra_terms(inner, spent, expected, on_nat, environment, term->args->tail, &ops, &functions_left))
    return 0;
  const Value *start;
  Nat used;
  if (!eval_term(inner, functions_left, expected, environment, nth_term(term->args, 5), &start, &used)) return 0;
  Typed found;
  Nat found_left;
  if (!eval_synth(inner, used, environment, nth_term(term->args, 6), &found, &found_left)) return 0;
  if (same_type(found.type, &value_type) != 1) return 0;
  if (checking_body(environment) == 1) return eval_worked(&null_value, found_left, value, left);
  const Value *result;
  Tokens ignored;
  Nat folded_left;
  Failure failure;
  if (!fold_value(inner, found_left, term->position, ops, start, found.value, &result, &ignored, &folded_left,
                  &failure))
    return 0;
  return eval_worked(result, folded_left, value, left);
}

/* unfold_term on an UNFOLD term [g, n, seed]: fuel is the fuel of
   unfold_term. */
static int eval_unfold(Fuel fuel, Nat budget, const LType *expected, const Bindings *environment, const Term *term,
                       const Value **value, Nat *left) {
  if (fuel == 0 || carrier_code(expected) == 0) return 0;
  Fuel more = fuel - 1;
  Stepper op;
  Nat spent;
  if (!eval_stepper(more, budget, 1, expected, environment, first_arg(term), &op, &spent)) return 0;
  if (unfold_fits(expected, op) != 1) return 0;
  const Value *limit;
  Nat limit_left;
  if (!eval_term(more, spent, &nat_type, environment, second_arg(term), &limit, &limit_left)) return 0;
  const Value *seed;
  Nat seed_left;
  if (!eval_term(more, limit_left, unfold_seed(op), environment, third_arg(term), &seed, &seed_left)) return 0;
  if (checking_body(environment) == 1) return eval_worked(&null_value, seed_left, value, left);
  const Values *items;
  Tokens ignored;
  Nat built_left;
  Failure failure;
  if (!unfold_items(more, seed_left, term->position, op, carrier_code(expected), count_of(limit), seed, &items,
                    &ignored, &built_left, &failure))
    return 0;
  const Value *rebuilt;
  if (!rebuild(expected, items, &rebuilt, &failure)) return 0;
  return eval_worked(rebuilt, built_left, value, left);
}

/* unfold_term on an UNFOLD_VALUE term [g, n, seed]: fuel is the fuel of
   unfold_term, which calls unfold_value_term at fuel - 1. */
static int eval_unfold_value(Fuel fuel, Nat budget, const LType *expected, const Bindings *environment,
                             const Term *term, const Value **value, Nat *left) {
  if (fuel <= 2 || carrier_code(expected) != 0 || same_type(expected, &value_type) != 1) return 0;
  Fuel more = fuel - 2;
  Stepper op;
  Nat spent;
  if (!eval_stepper(more, budget, 2, &value_type, environment, first_arg(term), &op, &spent)) return 0;
  if (unfold_value_fits(op) != 1) return 0;
  const Value *limit;
  Nat limit_left;
  if (!eval_term(more, spent, &nat_type, environment, second_arg(term), &limit, &limit_left)) return 0;
  const Value *seed;
  Nat seed_left;
  if (!eval_term(more, limit_left, unfold_seed(op), environment, third_arg(term), &seed, &seed_left)) return 0;
  if (checking_body(environment) == 1) return eval_worked(&null_value, seed_left, value, left);
  Grown node;
  Tokens ignored;
  Nat built_left;
  Failure failure;
  if (!unfold_node(more, seed_left, term->position, op, count_of(limit), seed, &node, &ignored, &built_left,
                   &failure))
    return 0;
  return eval_worked(grown_head(node), built_left, value, left);
}

int eval_synth(Fuel fuel, Nat budget, const Bindings *environment, const Term *term, Typed *typed, Nat *left) {
  if (term == NULL || fuel == 0 || budget == 0) return 0;
  Fuel more = fuel - 1;
  Typed found;
  Nat spent;
  Tokens rest;
  Failure failure;
  switch (term->tag) {
  case TERM_GROUP: return eval_synth(more, budget, environment, first_arg(term), typed, left);
  case TERM_VAR:
  case TERM_NAME: {
    const Binding *item;
    if (!lookup(term->name, environment, &item) || item->kind != BIND_VALUE) return 0;
    if (!proof_in_scope(item->name, item->type, environment)) return 0;
    return eval_typed((Typed){item->type, item->value}, budget, typed, left);
  }
  case TERM_APPLY: return eval_apply(more, budget, environment, term, typed, left);
  case TERM_FIRST:
  case TERM_SECOND:
    if (!eval_synth(more, budget, environment, first_arg(term), &found, &spent)) return 0;
    return lift_parsed(spent,
                       project(term->position, term->tag == TERM_FIRST ? 1 : 2, found, no_tokens, typed, &rest,
                               &failure),
                       left);
  case TERM_SYMM:
    if (!eval_synth(more, budget, environment, first_arg(term), &found, &spent)) return 0;
    return lift_parsed(spent, symm_proof(term->position, found, no_tokens, typed, &rest, &failure), left);
  case TERM_TRANS: {
    if (!eval_synth(more, budget, environment, first_arg(term), &found, &spent)) return 0;
    Typed other;
    Nat used;
    if (!eval_synth(more, spent, environment, second_arg(term), &other, &used)) return 0;
    return lift_parsed(used, trans_proof(term->position, found, other, no_tokens, typed, &rest, &failure), left);
  }
  case TERM_NUMBER:
  case TERM_STRING:
  case TERM_PARTIAL:
  case TERM_FUN:
  case TERM_CONSTRUCT:
  case TERM_REFL:
  case TERM_PURE:
  case TERM_MAP:
  case TERM_BIND:
  case TERM_FILTER:
  case TERM_FOLD:
  case TERM_FOLD_VALUE:
  case TERM_UNFOLD:
  case TERM_UNFOLD_VALUE: return 0;
  case TERM_EITHER: return eval_either(more, budget, environment, term, typed, left);
  /* A TERM_BODY takes no fuel step and no charge (the token path has no node for it). */
  case TERM_BODY: return eval_synth(fuel, budget, environment, term->callee, typed, left);
  }
  return 0;
}

/* 1 for the tags that eval_term takes at an arrow expected type: a FUN or a
   PARTIAL argument and the GROUP around it (the atom rule). NAME and VAR
   give 0 (Q-S4-4). */
static Nat arrow_tag(const Term *term) {
  switch (term->tag) {
  case TERM_GROUP:
  case TERM_FUN:
  case TERM_PARTIAL: return 1;
  case TERM_NUMBER:
  case TERM_STRING:
  case TERM_VAR:
  case TERM_NAME:
  case TERM_APPLY:
  case TERM_CONSTRUCT:
  case TERM_REFL:
  case TERM_FIRST:
  case TERM_SECOND:
  case TERM_SYMM:
  case TERM_TRANS:
  case TERM_EITHER:
  case TERM_PURE:
  case TERM_MAP:
  case TERM_BIND:
  case TERM_FILTER:
  case TERM_FOLD:
  case TERM_FOLD_VALUE:
  case TERM_UNFOLD:
  case TERM_UNFOLD_VALUE:
  case TERM_BODY: return 0;
  }
  return 0;
}

/* inline_argument on a FUN term. The token path reads the binder tokens with
   fuel, thus the margin rule of eval_inline_unary. The body walk is in check
   mode with its charge. The Value keeps the TERM_BODY of the FUN node. */
static int eval_inline_argument(Fuel fuel, Nat budget, const LType *expected, const Bindings *environment,
                                const Term *term, const Value **value, Nat *left) {
  if (fuel == 0 || fuel <= term_text(term).size + 2) return 0;
  Fuel more = fuel - 1;
  const Term *body = first_arg(term);
  const Params *params;
  if (body == NULL || body->tag != TERM_BODY || !binder_params(environment, term->types, &params)) return 0;
  if (same_type(expected, arrow_type(params, arrow_result(expected))) != 1) return 0;
  const Value *checked;
  Nat spent;
  if (!eval_term(more, budget, arrow_result(expected),
                 bind_params(params, NULL, bindings_item(check_marker(), environment)), body, &checked, &spent))
    return 0;
  return eval_worked(inline_value(params, term_tokens(body), body), spent, value, left);
}

/* partial_argument and prefix_argument on a PARTIAL term: one fuel step
   each, then eval_arguments (parse_arguments in mode 1). */
static int eval_partial_argument(Fuel fuel, Nat budget, const LType *expected, const Bindings *environment,
                                 const Term *term, const Value **value, Nat *left) {
  const Binding *item;
  if (fuel <= 1 || !lookup(term->name, environment, &item) || partial_callee(item) == 0) return 0;
  const Params *params = item->params;
  const LType *result = item->type;
  if (same_type(expected, arrow_type(params, result)) == 1 || dependent_result(result) == 1 ||
      dependent_params(params) == 1 || has_type_param(params) == 1)
    return 0;
  const Params *bound = bound_params(params, arrow_params(expected));
  if (same_type(expected, arrow_type(drop_params(params_length(bound), params), result)) != 1) return 0;
  const Values *values;
  Nat spent;
  if (!eval_arguments(fuel - 2, budget, param_types(bound), environment, term->args, &values, &spent)) return 0;
  if (bound_functions(bound, values) == 0) return 0;
  return eval_worked(make_value((Value){.kind = VALUE_ITEMS, .items = values_item(text_value(term->name), values)}),
                     spent, value, left);
}

int eval_term(Fuel fuel, Nat budget, const LType *expected, const Bindings *environment, const Term *term,
              const Value **value, Nat *left) {
  if (term == NULL || fuel == 0 || budget == 0 || (is_arrow_type(expected) == 1 && arrow_tag(term) == 0)) return 0;
  Fuel more = fuel - 1;
  Tokens rest;
  Failure failure;
  switch (term->tag) {
  case TERM_NUMBER:
    return same_type(expected, &nat_type) == 1 && eval_worked(nat_value(term->number), budget, value, left);
  case TERM_STRING:
    return same_type(expected, &text_type) == 1 && eval_worked(text_value(term->name), budget, value, left);
  case TERM_GROUP: return eval_term(more, budget, expected, environment, first_arg(term), value, left);
  case TERM_VAR:
  case TERM_NAME: {
    const Binding *item;
    if (!lookup(term->name, environment, &item) || item->kind != BIND_VALUE) return 0;
    if (!proof_in_scope(item->name, item->type, environment) || same_type(expected, item->type) != 1) return 0;
    return eval_worked(item->value, budget, value, left);
  }
  case TERM_CONSTRUCT: {
    const Binding *item;
    Plan selected;
    if (lookup(term->name, environment, &item) || !constructor_plan(expected, term->name, &selected)) return 0;
    const Values *values;
    Nat spent;
    if (!eval_arguments(more, budget, plan_arguments(&selected), environment, term->args, &values, &spent)) return 0;
    const Value *made;
    if (evaluate_plan(&selected, values, &made, &failure)) return eval_worked(made, spent, value, left);
    return checking_body(environment) == 1 && eval_worked(&null_value, spent, value, left);
  }
  case TERM_REFL:
    return lift_parsed(budget, refl_check(term->position, expected, no_tokens, value, &rest, &failure), left);
  case TERM_APPLY:
  case TERM_FIRST:
  case TERM_SECOND:
  case TERM_SYMM:
  case TERM_TRANS:
  case TERM_EITHER: {
    /* checked_synth: synth_term at fuel - 1, then the check of the type. */
    Typed found;
    Nat spent;
    if (!eval_synth(more, budget, environment, term, &found, &spent)) return 0;
    return check_worked(term->position, expected, found, no_tokens, spent, value, &rest, left, &failure);
  }
  case TERM_PURE: return eval_structure(more, budget, 1, expected, environment, term, value, left);
  case TERM_MAP: return eval_structure(more, budget, 2, expected, environment, term, value, left);
  case TERM_BIND: return eval_structure(more, budget, 3, expected, environment, term, value, left);
  case TERM_FILTER: return eval_structure(more, budget, 4, expected, environment, term, value, left);
  case TERM_FOLD: return eval_fold(more, budget, expected, environment, term, value, left);
  case TERM_FOLD_VALUE: return eval_fold_value(more, budget, expected, environment, term, value, left);
  case TERM_UNFOLD: return eval_unfold(more, budget, expected, environment, term, value, left);
  case TERM_UNFOLD_VALUE: return eval_unfold_value(more, budget, expected, environment, term, value, left);
  case TERM_PARTIAL:
    return is_arrow_type(expected) == 1 && eval_partial_argument(more, budget, expected, environment, term, value, left);
  case TERM_FUN:
    return is_arrow_type(expected) == 1 && eval_inline_argument(more, budget, expected, environment, term, value, left);
  /* A TERM_BODY takes no fuel step and no charge (the token path has no node for it). */
  case TERM_BODY: return eval_term(fuel, budget, expected, environment, term->callee, value, left);
  }
  return 0;
}

int partial_argument(Fuel fuel, Nat budget, Nat atom, Nat position, const LType *expected, Text name,
                     const Params *params, const LType *result, const Bindings *environment, Tokens tokens,
                     const Value **value, Tokens *rest, Nat *left, const Term **term, Failure *failure) {
  if (fuel == 0) return fail_at(failure, position, eFuel);
  Fuel more = fuel - 1;
  if (same_type(expected, arrow_type(params, result)) == 1)
    return with_term(worked_value(text_value(name), tokens, budget, value, rest, left), term,
                     term != NULL ? reference_term(position, name, environment) : NULL);
  if (dependent_result(result) == 1 || dependent_params(params) == 1) return fail_at(failure, position, eTerm);
  if (has_type_param(params) != 1)
    return prefix_argument(more, budget, atom, position, expected, name, params, params, result, environment, tokens,
                           tokens, value, rest, left, term, failure);
  if (atom == 1) return fail_at(failure, position, eTerm);
  const Bindings *chosen;
  Tokens after_types;
  const TermTypes *types = NULL;
  if (!type_arguments(more, params, environment, NULL, tokens, &chosen, &after_types, want_types(term, &types), failure))
    return 0;
  const Term *partial = NULL;
  int ok = prefix_argument(more, budget, atom, position, expected, name, params, value_params(chosen, params),
                           subst_type(chosen, result), environment, tokens, after_types, value, rest, left,
                           want_term(term, &partial), failure);
  return with_term(ok, term,
                   partial != NULL ? term_call(TERM_PARTIAL, position, 0, partial->callee, types, partial->args) : NULL);
}

int prefix_argument(Fuel fuel, Nat budget, Nat atom, Nat position, const LType *expected, Text name,
                    const Params *params, const Params *formal, const LType *result, const Bindings *environment,
                    Tokens tokens, Tokens after_types, const Value **value, Tokens *rest, Nat *left, const Term **term, Failure *failure) {
  if (fuel == 0) return fail_at(failure, position, eFuel);
  Fuel more = fuel - 1;
  const Params *bound = bound_params(formal, arrow_params(expected));
  if (same_type(expected, arrow_type(drop_params(params_length(bound), formal), result)) == 0)
    return fail_at(failure, position, eTerm);
  if (atom == 1) return fail_at(failure, position, eParen);
  const Values *values;
  Tokens after;
  Nat spent;
  const Terms *args = NULL;
  if (!parse_arguments(more, budget, 1, param_types(bound), environment, after_types, &values, &after, &spent,
                       want_terms(term, &args), failure))
    return 0;
  if (bound_functions(bound, values))
    return with_term(worked_value(
        make_value((Value){.kind = VALUE_ITEMS,
                           .items = values_item(text_value(name), typed_bound(params, tokens, after_types, values))}),
                         after, spent, value, rest, left),
                     term, term != NULL ? named_term(TERM_PARTIAL, position, name, NULL, args, environment) : NULL);
  return fail_at(failure, position, eTerm);
}

int inline_argument(Fuel fuel, Nat budget, Nat position, const LType *expected, const Bindings *environment,
                    Tokens tokens, const Value **value, Tokens *rest, Nat *left, const Term **term, Failure *failure) {
  if (fuel == 0) return fail_at(failure, position, eFuel);
  Fuel more = fuel - 1;
  const Params *params;
  Tokens body;
  if (!inline_binders(more, environment, NULL, tokens, &params, &body, failure)) return 0;
  if (same_type(expected, arrow_type(params, arrow_result(expected))) != 1) return fail_at(failure, position, eTerm);
  const Value *checked;
  Tokens after;
  Nat spent;
  const Term *inner = NULL;
  if (!parse_term(more, budget, 0, arrow_result(expected),
                  bind_params(params, NULL, bindings_item(check_marker(), environment)), body, &checked, &after,
                  &spent, want_term(term, &inner), failure))
    return 0;
  /* The FUN node, the argument Value and its closure share one TERM_BODY. */
  const Term *carrier = term != NULL ? term_body(taken_tokens(body, after), inner) : NULL;
  const Term *made = inner != NULL
                         ? term_fun(position, 0, binder_types(params, taken_tokens(tokens, body), environment), carrier)
                         : NULL;
  return with_term(
      worked_value(inline_value(params, taken_tokens(body, after), carrier), after, spent, value, rest, left), term, made);
}

/* Each step takes one unit of fuel, as each recursive call of the mech def. */
int parse_arguments(Fuel fuel, Nat budget, Nat atom, const LTypes *types, const Bindings *environment, Tokens tokens,
                    const Values **values, Tokens *rest, Nat *left, const Terms **terms, Failure *failure) {
  const Values *done = NULL;
  const Terms *built = NULL;
  for (;; types = types->tail) {
    if (fuel == 0) return fail_at(failure, first_position(tokens), eFuel);
    fuel = fuel - 1;
    if (types == NULL) {
      *values = reverse_values_onto(NULL, done);
      if (terms != NULL) *terms = reverse_terms_onto(NULL, built);
      *rest = tokens;
      *left = budget;
      return 1;
    }
    const Value *value;
    const Term *made = NULL;
    if (!parse_term(fuel, budget, atom, types->head, environment, tokens, &value, &tokens, &budget,
                    want_term(terms, &made), failure))
      return 0;
    done = values_item(value, done);
    if (terms != NULL) built = terms_item(made, built);
  }
}

/* seen holds the earlier argument values, the latest first. */
int dependent_arguments(Fuel fuel, Nat budget, const Bindings *chosen, const Bindings *environment,
                        const Params *params, const Params *remaining, const Values *seen, Tokens start,
                        Tokens tokens, const Values **values, Tokens *rest, Nat *left, const Terms **terms, Failure *failure) {
  const Terms *built = NULL;
  for (;; remaining = remaining->tail) {
    if (fuel == 0) return fail_at(failure, first_position(tokens), eFuel);
    fuel = fuel - 1;
    if (remaining == NULL) {
      *values = reverse_values_onto(NULL, seen);
      if (terms != NULL) *terms = reverse_terms_onto(NULL, built);
      *rest = tokens;
      *left = budget;
      return 1;
    }
    Param head = remaining->head;
    if (is_type_param(head) == 1) continue;
    const Values *earlier = reverse_values_onto(NULL, seen);
    const LType *instantiated = NULL;
    int resolved =
        instantiate_result(fuel, environment, params, earlier, start, subst_type(chosen, head.type), &instantiated);
    const LType *expected;
    if (!close_result(fuel, environment, params, earlier, resolved, instantiated, &expected))
      return fail_at(failure, first_position(tokens), eTerm);
    const Value *value;
    const Term *made = NULL;
    if (!parse_term(fuel, budget, 1, expected, environment, tokens, &value, &tokens, &budget, want_term(terms, &made),
                    failure))
      return 0;
    seen = values_item(value, seen);
    if (terms != NULL) built = terms_item(made, built);
  }
}

int close_side(Fuel fuel, const Bindings *bound, const LType *a, Val side, Val *closed) {
  if (fuel == 0) return 0;
  Fuel more = fuel - 1;
  switch (side.kind) {
  case VAL_CLOSED:
  case VAL_VAR: *closed = side; return 1;
  case VAL_TERM: {
    const Value *value;
    Tokens rest;
    Nat left;
    Failure failure;
    if (!parse_term(more, 1, 1, a, bound, side.term, &value, &rest, &left, NULL, &failure)) return 0;
    return printed_side(more, value, closed);
  }
  }
  return 0;
}

int close_body_side(Fuel fuel, const Bindings *environment, const LType *a, Val side, Val *closed) {
  if (fuel == 0) return 0;
  if (kept_side(side) == 1) {
    *closed = side;
    return 1;
  }
  return close_side(fuel - 1, environment, a, side, closed);
}

int close_result(Fuel fuel, const Bindings *environment, const Params *params, const Values *values, int resolved,
                 const LType *result, const LType **closed) {
  if (fuel == 0) return 0;
  Fuel more = fuel - 1;
  if (!resolved) return 0;
  const LType *a;
  Val lhs;
  Val rhs;
  if (!sides_of(result, &a, &lhs, &rhs)) {
    *closed = result;
    return 1;
  }
  Val x;
  Val y;
  if (checking_body(environment) == 1) {
    if (!close_body_side(more, environment, a, lhs, &x)) return 0;
    if (!close_body_side(more, environment, a, rhs, &y)) return 0;
    *closed = eq_type(a, x, y);
    return 1;
  }
  const Bindings *bound = argument_bindings(0, params, values, environment);
  if (!close_side(more, bound, a, lhs, &x)) return 0;
  if (!close_side(more, bound, a, rhs, &y)) return 0;
  *closed = eq_type(a, x, y);
  return 1;
}

/* At fuel 0 the params not yet closed are kept as they are. */
const Params *close_params(Fuel fuel, const Bindings *environment, const Params *params, const Values *values,
                           const Params *remaining) {
  const Params *done = NULL;
  for (; remaining != NULL; remaining = remaining->tail) {
    if (fuel == 0) return reverse_params_onto(remaining, done);
    fuel = fuel - 1;
    Param head = remaining->head;
    const LType *found;
    done = params_item(close_result(fuel, environment, params, values, 1, head.type, &found)
                           ? (Param){head.name, found}
                           : head,
                       done);
  }
  return reverse_params_onto(NULL, done);
}

int unary_term(Fuel fuel, Nat budget, const LType *wanted, const Bindings *environment, Tokens tokens, Unary *op,
               Tokens *rest, Nat *left, const Term **term, Failure *failure) {
  if (fuel == 0) return fail_at(failure, first_position(tokens), eFuel);
  Fuel more = fuel - 1;
  if (tokens.size == 0) return lift_parsed(budget, unary_argument(environment, tokens, op, rest, term, failure), left);
  Token head = tokens.items[0];
  switch (head.kind) {
  case TOKEN_NUMBER:
  case TOKEN_STRING:
  case TOKEN_IDENTIFIER: return lift_parsed(budget, unary_argument(environment, tokens, op, rest, term, failure), left);
  case TOKEN_PUNCTUATION: {
    if (head.number != 40) return fail_at(failure, head.position, eUnary);
    Unary inside;
    Tokens after;
    Nat spent;
    const Term *inner = NULL;
    if (!partial_unary(more, budget, wanted, environment, (Tokens){tokens.items + 1, tokens.size - 1}, &inside,
                       &after, &spent, want_term(term, &inner), failure))
      return 0;
    *op = inside;
    return with_term(lift_parsed(spent, close_parsed(after, rest, failure), left), term,
                     inner != NULL ? term_form(TERM_GROUP, head.position, 0, terms_item(inner, NULL)) : NULL);
  }
  }
  return 0;
}

int partial_unary(Fuel fuel, Nat budget, const LType *wanted, const Bindings *environment, Tokens tokens, Unary *op,
                  Tokens *rest, Nat *left, const Term **term, Failure *failure) {
  if (fuel == 0) return fail_at(failure, first_position(tokens), eFuel);
  Fuel more = fuel - 1;
  if (tokens.size == 0) return fail_at(failure, 0, eUnary);
  Token head = tokens.items[0];
  Tokens tail = {tokens.items + 1, tokens.size - 1};
  switch (head.kind) {
  case TOKEN_NUMBER:
  case TOKEN_STRING: return fail_at(failure, head.position, eUnary);
  case TOKEN_PUNCTUATION:
    if (head.number != 40) return fail_at(failure, head.position, eUnary);
    return unary_term(more, budget, wanted, environment, tokens, op, rest, left, term, failure);
  case TOKEN_IDENTIFIER: {
    if (same_text(head.text, sfun) == 1)
      return inline_unary(more, budget, head.position, wanted, environment, tail, op, rest, left, term, failure);
    const Binding *item;
    if (!lookup(head.text, environment, &item)) return fail_at(failure, head.position, eUnary);
    switch (item->kind) {
    case BIND_VALUE:
    case BIND_TYPE:
    case BIND_ARROW: return fail_at(failure, head.position, eUnary);
    case BIND_FUN:
      if (dependent_params(item->params) == 1) return fail_at(failure, head.position, eUnary);
      return bound_unary(more, budget, head.position, head.text, item->params, item->type, environment, tail, op,
                         rest, left, term, failure);
    case BIND_CLOSURE:
      return bound_unary(more, budget, head.position, head.text, item->params, item->type, environment, tail, op,
                         rest, left, term, failure);
    }
    return 0;
  }
  }
  return 0;
}

/* A parse error of a mark gives eFun at its position. */
int inline_unary(Fuel fuel, Nat budget, Nat position, const LType *wanted, const Bindings *environment, Tokens tokens,
                 Unary *op, Tokens *rest, Nat *left, const Term **term, Failure *failure) {
  if (fuel == 0) return fail_at(failure, position, eFuel);
  Fuel more = fuel - 1;
  Tokens after_open;
  Failure refused;
  if (!expect_mark(40, tokens, &after_open, &refused)) return fail_at(failure, refused.position, eFun);
  if (after_open.size == 0) return fail_at(failure, position, eFun);
  Token head = after_open.items[0];
  Tokens after_name = {after_open.items + 1, after_open.size - 1};
  switch (head.kind) {
  case TOKEN_NUMBER:
  case TOKEN_STRING:
  case TOKEN_PUNCTUATION: return fail_at(failure, head.position, eFun);
  case TOKEN_IDENTIFIER: {
    if (reserved_name(head.text) == 1) return fail_at(failure, head.position, eReserved);
    Tokens after_colon;
    if (!expect_mark(58, after_name, &after_colon, &refused)) return fail_at(failure, refused.position, eFun);
    const LType *ty;
    Tokens after_type;
    if (!parse_type(more, 0, environment, after_colon, &ty, &after_type, failure)) return 0;
    if (type_level(ty) != 0) return fail_at(failure, first_position(after_colon), eData);
    Tokens after_binder;
    if (!expect_mark(41, after_type, &after_binder, &refused)) return fail_at(failure, refused.position, eFun);
    Tokens body;
    if (!expect_mark(63, after_binder, &body, &refused)) return fail_at(failure, refused.position, eFun);
    const Value *value;
    Tokens after;
    Nat spent;
    const Term *inner = NULL;
    if (!parse_term(more, budget, 0, wanted,
                    bindings_item(value_binding(head.text, ty, &null_value), bindings_item(check_marker(), environment)),
                    body, &value, &after, &spent, want_term(term, &inner), failure))
      return 0;
    *op = (Unary){head.text, ty, wanted, taken_tokens(body, after), environment};
    *rest = after;
    *left = spent;
    return with_term(1, term,
                     inner != NULL ? term_fun(position, 0,
                                              binder_types(params_item((Param){head.text, ty}, NULL),
                                                           taken_tokens(tokens, body), environment),
                                              inner)
                                   : NULL);
  }
  }
  return 0;
}

int bound_unary(Fuel fuel, Nat budget, Nat position, Text name, const Params *params, const LType *result,
                const Bindings *environment, Tokens tokens, Unary *op, Tokens *rest, Nat *left, const Term **term,
                Failure *failure) {
  if (fuel == 0) return fail_at(failure, position, eFuel);
  Fuel more = fuel - 1;
  const Bindings *chosen;
  Tokens after_types;
  const TermTypes *types = NULL;
  if (!type_arguments(more, params, environment, NULL, tokens, &chosen, &after_types, want_types(term, &types), failure))
    return 0;
  const Params *formal = value_params(chosen, params);
  const Params *front = front_params(formal);
  const Values *values;
  Tokens after;
  Nat spent;
  const Terms *args = NULL;
  if (!parse_arguments(more, budget, 1, param_types(front), environment, after_types, &values, &after, &spent,
                       want_terms(term, &args), failure))
    return 0;
  if (bound_functions(front, values) == 0) return fail_at(failure, position, eTerm);
  Binding closure =
      partial_closure(name, arrow_type(drop_params(params_length(front), formal), subst_type(chosen, result)), name,
                      typed_bound(params, tokens, after_types, values), environment);
  Unary shaped;
  if (!unary_of(environment, &closure, &shaped)) return fail_at(failure, position, eUnary);
  *op = shaped;
  *rest = after;
  *left = spent;
  return with_term(1, term, term != NULL ? named_term(TERM_PARTIAL, position, name, types, args, environment) : NULL);
}

int stepper_term(Fuel fuel, Nat budget, Nat mode, const LType *expected, const Bindings *environment, Tokens tokens,
                 Stepper *op, Tokens *rest, Nat *left, const Term **term, Failure *failure) {
  if (fuel == 0) return fail_at(failure, first_position(tokens), eFuel);
  Fuel more = fuel - 1;
  if (tokens.size == 0)
    return lift_parsed(budget, stepper_argument(environment, tokens, op, rest, term, failure), left);
  Token head = tokens.items[0];
  switch (head.kind) {
  case TOKEN_NUMBER:
  case TOKEN_STRING:
  case TOKEN_IDENTIFIER:
    return lift_parsed(budget, stepper_argument(environment, tokens, op, rest, term, failure), left);
  case TOKEN_PUNCTUATION: {
    if (head.number != 40) return fail_at(failure, head.position, eStep);
    Stepper inside;
    Tokens after;
    Nat spent;
    const Term *inner = NULL;
    if (!partial_stepper(more, budget, mode, expected, environment, (Tokens){tokens.items + 1, tokens.size - 1},
                         &inside, &after, &spent, want_term(term, &inner), failure))
      return 0;
    *op = inside;
    return with_term(lift_parsed(spent, close_parsed(after, rest, failure), left), term,
                     inner != NULL ? term_form(TERM_GROUP, head.position, 0, terms_item(inner, NULL)) : NULL);
  }
  }
  return 0;
}

int partial_stepper(Fuel fuel, Nat budget, Nat mode, const LType *expected, const Bindings *environment,
                    Tokens tokens, Stepper *op, Tokens *rest, Nat *left, const Term **term, Failure *failure) {
  if (fuel == 0) return fail_at(failure, first_position(tokens), eFuel);
  Fuel more = fuel - 1;
  if (tokens.size == 0) return fail_at(failure, 0, eStep);
  Token head = tokens.items[0];
  Tokens tail = {tokens.items + 1, tokens.size - 1};
  switch (head.kind) {
  case TOKEN_NUMBER:
  case TOKEN_STRING: return fail_at(failure, head.position, eStep);
  case TOKEN_PUNCTUATION:
    if (head.number != 40) return fail_at(failure, head.position, eStep);
    return stepper_term(more, budget, mode, expected, environment, tokens, op, rest, left, term, failure);
  case TOKEN_IDENTIFIER: {
    if (same_text(head.text, sfun) == 1)
      return inline_stepper(more, budget, head.position, mode, expected, environment, tail, op, rest, left, term,
                            failure);
    const Binding *item;
    if (!lookup(head.text, environment, &item)) return fail_at(failure, head.position, eStep);
    switch (item->kind) {
    case BIND_VALUE:
    case BIND_TYPE:
    case BIND_ARROW: return fail_at(failure, head.position, eStep);
    case BIND_FUN:
      if (dependent_params(item->params) == 1) return fail_at(failure, head.position, eStep);
      return bound_stepper(more, budget, head.position, head.text, item->params, item->type, environment, tail, op,
                           rest, left, term, failure);
    case BIND_CLOSURE:
      return bound_stepper(more, budget, head.position, head.text, item->params, item->type, environment, tail, op,
                           rest, left, term, failure);
    }
    return 0;
  }
  }
  return 0;
}

static int worked_stepper(Stepper found, Tokens after, Nat budget, Stepper *op, Tokens *rest, Nat *left) {
  *op = found;
  *rest = after;
  *left = budget;
  return 1;
}

static int worked_values(const Values *found, Tokens after, Nat budget, const Values **values, Tokens *rest,
                         Nat *left) {
  *values = found;
  *rest = after;
  *left = budget;
  return 1;
}

int inline_stepper(Fuel fuel, Nat budget, Nat position, Nat mode, const LType *expected, const Bindings *environment,
                   Tokens tokens, Stepper *op, Tokens *rest, Nat *left, const Term **term, Failure *failure) {
  if (fuel == 0) return fail_at(failure, first_position(tokens), eFuel);
  Fuel more = fuel - 1;
  const Params *params = NULL;
  Tokens body = {0};
  if (!inline_binders(more, environment, NULL, tokens, &params, &body, failure)) return 0;
  const LType *result = inline_result(mode, expected, params);
  const Value *value = NULL;
  Tokens after = {0};
  Nat spent = 0;
  const Term *inner = NULL;
  if (!parse_term(more, budget, 0, result, bind_params(params, NULL, bindings_item(check_marker(), environment)), body,
                  &value, &after, &spent, want_term(term, &inner), failure))
    return 0;
  const Term *made = inner != NULL ? term_fun(position, 0,
                                              binder_types(params, taken_tokens(tokens, body), environment), inner)
                                   : NULL;
  return with_term(
      worked_stepper((Stepper){params, result, taken_tokens(body, after), environment}, after, spent, op, rest, left),
      term, made);
}

/* The bound arguments are checked in the caller scope, one per parameter,
   up to the closing parenthesis. A bound function argument is a name or an
   inline function. */
int bound_stepper(Fuel fuel, Nat budget, Nat position, Text name, const Params *params, const LType *result,
                  const Bindings *environment, Tokens tokens, Stepper *op, Tokens *rest, Nat *left, const Term **term,
                  Failure *failure) {
  if (fuel == 0) return fail_at(failure, position, eFuel);
  Fuel more = fuel - 1;
  const Bindings *chosen = NULL;
  Tokens after_types = {0};
  const TermTypes *types = NULL;
  if (!type_arguments(more, params, environment, NULL, tokens, &chosen, &after_types, want_types(term, &types), failure))
    return 0;
  const Params *formal = value_params(chosen, params);
  const Values *values = NULL;
  Tokens after = {0};
  Nat spent = 0;
  const Terms *args = NULL;
  if (!bound_arguments(more, budget, formal, environment, after_types, &values, &after, &spent,
                       want_terms(term, &args), failure))
    return 0;
  if (bound_functions(take_params(values_length(values), formal), values) == 0)
    return fail_at(failure, position, eTerm);
  Binding made = partial_closure(name, arrow_type(drop_params(values_length(values), formal), subst_type(chosen, result)),
                                 name, typed_bound(params, tokens, after_types, values), environment);
  const Term *called = term != NULL ? named_term(TERM_PARTIAL, position, name, types, args, environment) : NULL;
  switch (made.kind) {
  case BIND_VALUE: return fail_at(failure, position, eStep);
  case BIND_TYPE: return fail_at(failure, position, eStep);
  case BIND_ARROW: return fail_at(failure, position, eStep);
  case BIND_FUN: {
    Stepper found = {made.params, made.type, term_tokens(made.term), definition_scope(made.name, environment)};
    return with_term(worked_stepper(found, after, spent, op, rest, left), term, called);
  }
  case BIND_CLOSURE: {
    Stepper found = {made.params, made.type, term_tokens(made.term), made.scope};
    return with_term(worked_stepper(found, after, spent, op, rest, left), term, called);
  }
  }
  return 0;
}

/* One bound argument per parameter, until the closing parenthesis or the
   last parameter. */
int bound_arguments(Fuel fuel, Nat budget, const Params *params, const Bindings *environment, Tokens tokens,
                    const Values **values, Tokens *rest, Nat *left, const Terms **terms, Failure *failure) {
  if (fuel == 0) return fail_at(failure, first_position(tokens), eFuel);
  Fuel more = fuel - 1;
  if (terms != NULL) *terms = NULL;
  if (params == NULL) return worked_values(NULL, tokens, budget, values, rest, left);
  if (closes_next(tokens) == 1) return worked_values(NULL, tokens, budget, values, rest, left);
  const Values *found = NULL;
  Tokens after = {0};
  Nat spent = 0;
  const Terms *found_terms = NULL;
  if (!parse_arguments(more, budget, 1, param_types(params_item(params->head, NULL)), environment, tokens, &found,
                       &after, &spent, want_terms(terms, &found_terms), failure))
    return 0;
  const Values *later = NULL;
  Tokens after_later = {0};
  Nat used = 0;
  const Terms *later_terms = NULL;
  if (!bound_arguments(more, spent, params->tail, environment, after, &later, &after_later, &used,
                       want_terms(terms, &later_terms), failure))
    return 0;
  if (terms != NULL) *terms = reverse_terms_onto(later_terms, reverse_terms_onto(NULL, found_terms));
  return worked_values(reverse_values_onto(later, reverse_values_onto(NULL, found)), after_later, used, values, rest,
                       left);
}

/* The body of an op at one application: eval_term on the body term when the
   op has one, else parse_term on the body tokens (D3-s3 part B). On the term
   path rest is empty and failure is not written: a 0 makes the evaluator give
   0, and the application site runs the token path again. */
static int apply_body(Fuel fuel, Nat budget, const LType *expected, const Bindings *environment, Tokens body,
                      const Term *term, const Value **value, Tokens *rest, Nat *left, Failure *failure) {
  /* A TERM_BODY with no callee takes the token path, as a NULL term. */
  if (term == NULL || (term->tag == TERM_BODY && term->callee == NULL))
    return parse_term(fuel, budget, 0, expected, environment, body, value, rest, left, NULL, failure);
  *rest = (Tokens){0};
  return eval_term(fuel, budget, expected, environment, term, value, left);
}

/* pure x lifts x. map, bind and filter name or partially apply a function,
   then take the source as an argument. In the check of a function body,
   map, bind and filter check the function and the source and give null. */
int structure_term(Fuel fuel, Nat budget, Nat position, Nat form, Nat atom, const LType *expected,
                   const Bindings *environment, Tokens tokens, const Value **value, Tokens *rest, Nat *left,
                   const Term **term, Failure *failure) {
  if (fuel == 0) return fail_at(failure, position, eFuel);
  Fuel more = fuel - 1;
  if (atom == 1) return fail_at(failure, position, eParen);
  if (shape_code(form, expected) == 0) return fail_at(failure, position, eStructure);
  if (form == 1) {
    const Value *lifted = NULL;
    Tokens after = {0};
    Nat spent = 0;
    const Term *element = NULL;
    if (!parse_term(more, budget, 1, shape_element(expected), environment, tokens, &lifted, &after, &spent,
                    want_term(term, &element), failure))
      return 0;
    return with_term(worked_value(pure_value(expected, lifted), after, spent, value, rest, left), term,
                     term != NULL ? form_term(TERM_PURE, position, terms_item(element, NULL)) : NULL);
  }
  Unary op = {0};
  Tokens after_function = {0};
  Nat spent = 0;
  const Term *function = NULL;
  if (!unary_term(more, budget, structure_result(form, expected), environment, tokens, &op, &after_function, &spent,
                  want_term(term, &function), failure))
    return 0;
  if (structure_fits(form, expected, op) != 1) return fail_at(failure, first_position(tokens), eTerm);
  const Value *source = NULL;
  Tokens after = {0};
  Nat used = 0;
  const Term *from = NULL;
  if (!parse_term(more, spent, 1, structure_source(form, expected, op), environment, after_function, &source, &after,
                  &used, want_term(term, &from), failure))
    return 0;
  const Term *made =
      term != NULL ? form_term(structure_tag(form), position, terms_item(function, terms_item(from, NULL))) : NULL;
  if (checking_body(environment) == 1)
    return with_term(worked_value(&null_value, after, used, value, rest, left), term, made);
  if (carrier_code(expected) == 2) {
    const Values *items = NULL;
    Tokens ignored = {0};
    Nat mapped_left = 0;
    if (!map_items(more, used, position, form, op, sequence_elements(source), &items, &ignored, &mapped_left, failure))
      return 0;
    const Value *rebuilt = NULL;
    Failure refused = {0};
    if (!rebuild(expected, items, &rebuilt, &refused)) return fail_at(failure, position, refused.message);
    return with_term(worked_value(rebuilt, after, mapped_left, value, rest, left), term, made);
  }
  const Value *item = NULL;
  if (!payload_of(expected, unary_param(op), source, &item))
    return with_term(worked_value(source, after, used, value, rest, left), term, made);
  const Value *applied = NULL;
  Tokens applied_rest = {0};
  Nat applied_left = 0;
  if (!apply_body(more, nat_sub(used, 1), unary_result(op), unary_environment(op, item), unary_body(op), op.term,
                  &applied, &applied_rest, &applied_left, failure))
    return 0;
  return with_term(worked_value(step_one(form, expected, source, applied), after, applied_left, value, rest, left), term,
                   made);
}

/* Over a list, the function applies to each item in order: 2 map keeps each
   result, 3 bind joins the result lists, 4 filter keeps the items with the
   result flagYes. Each item uses one step of the depth fuel. */
int map_items(Fuel fuel, Nat budget, Nat position, Nat form, Unary op, const Values *items, const Values **mapped,
              Tokens *rest, Nat *left, Failure *failure) {
  if (fuel == 0) return fail_at(failure, position, eFuel);
  Fuel more = fuel - 1;
  if (items == NULL) return worked_values(NULL, (Tokens){0}, budget, mapped, rest, left);
  const Value *applied = NULL;
  Tokens after = {0};
  Nat spent = 0;
  if (!apply_body(more, nat_sub(budget, 1), unary_result(op), unary_environment(op, items->head), unary_body(op),
                  op.term, &applied, &after, &spent, failure))
    return 0;
  const Values *later = NULL;
  Tokens ignored = {0};
  Nat used = 0;
  if (!map_items(more, spent, position, form, op, items->tail, &later, &ignored, &used, failure)) return 0;
  return worked_values(step_items(form, items->head, applied, later), (Tokens){0}, used, mapped, rest, left);
}

/* either f g s applies f to the payload of inl and g to the payload of inr.
   The two functions must have the same result type. */
int either_term(Fuel fuel, Nat budget, Nat position, const Bindings *environment, Tokens tokens, Typed *typed,
                Tokens *rest, Nat *left, const Term **term, Failure *failure) {
  if (fuel == 0) return fail_at(failure, position, eFuel);
  Fuel more = fuel - 1;
  Unary on_left = {0};
  Tokens after_left = {0};
  const Term *left_function = NULL;
  if (!unary_argument(environment, tokens, &on_left, &after_left, want_term(term, &left_function), failure)) return 0;
  Unary on_right = {0};
  Tokens after_right = {0};
  const Term *right_function = NULL;
  if (!unary_argument(environment, after_left, &on_right, &after_right, want_term(term, &right_function), failure))
    return 0;
  const LType *result = unary_result(on_left);
  if (!(dependent_result(result) == 0 && same_type(result, unary_result(on_right)) == 1))
    return fail_at(failure, first_position(after_left), eTerm);
  const Value *source = NULL;
  Tokens after = {0};
  Nat spent = 0;
  const Term *from = NULL;
  if (!parse_term(more, budget, 1, type_two(TY_SUM, unary_param(on_left), unary_param(on_right)), environment,
                  after_right, &source, &after, &spent, want_term(term, &from), failure))
    return 0;
  const Term *made =
      term != NULL ? form_term(TERM_EITHER, position,
                               terms_item(left_function, terms_item(right_function, terms_item(from, NULL))))
                   : NULL;
  if (checking_body(environment) == 1)
    return with_term(worked_typed((Typed){result, &null_value}, after, spent, typed, rest, left), term, made);
  Unary chosen = sum_left(source) != 0 ? on_left : on_right;
  const Value *applied = NULL;
  Tokens applied_rest = {0};
  Nat applied_left = 0;
  if (!apply_body(more, nat_sub(spent, 1), result, unary_environment(chosen, project_value(1, source)),
                  unary_body(chosen), chosen.term, &applied, &applied_rest, &applied_left, failure))
    return 0;
  return with_term(worked_typed((Typed){result, applied}, after, applied_left, typed, rest, left), term, made);
}

/* fold f z t synthesizes the type of t. Over a sequence it applies f from
   the last element: fold f z nil is z, and fold f z (cons x xs) is
   f x (fold f z xs). Over the number n it applies f n times to z. With five
   functions the source is a Value. */
int fold_term(Fuel fuel, Nat budget, Nat position, Nat atom, const LType *expected, const Bindings *environment,
              Tokens tokens, const Value **value, Tokens *rest, Nat *left, const Term **term, Failure *failure) {
  if (fuel == 0) return fail_at(failure, position, eFuel);
  Fuel more = fuel - 1;
  if (atom == 1) return fail_at(failure, position, eParen);
  Stepper op = {0};
  Tokens after_function = {0};
  Nat spent = 0;
  const Term *function = NULL;
  if (!stepper_term(more, budget, 0, expected, environment, tokens, &op, &after_function, &spent,
                    want_term(term, &function), failure))
    return 0;
  if (second_function(more, spent, expected, environment, after_function) == 1) {
    const Term *algebra = NULL;
    if (!fold_value_term(more, spent, position, first_position(tokens), expected, op, environment, after_function,
                         value, rest, left, want_term(term, &algebra), failure))
      return 0;
    return with_term(1, term,
                     function != NULL && algebra != NULL
                         ? term_form(TERM_FOLD_VALUE, position, 0, terms_item(function, algebra->args))
                         : NULL);
  }
  const Value *start = NULL;
  Tokens after_start = {0};
  Nat used = 0;
  const Term *start_term = NULL;
  if (!parse_term(more, spent, 1, expected, environment, after_function, &start, &after_start, &used,
                  want_term(term, &start_term), failure))
    return 0;
  Typed found = {0};
  Tokens after = {0};
  Nat found_left = 0;
  const Term *source = NULL;
  if (!synth_term(more, used, 1, environment, after_start, &found, &after, &found_left, want_term(term, &source),
                  failure))
    return 0;
  if (carrier_code(found.type) == 0)
    return fail_at(failure, first_position(after_start), same_type(found.type, &value_type) != 0 ? eCases : eStructure);
  if (fold_fits(found.type, expected, op) != 1) return fail_at(failure, first_position(tokens), eTerm);
  const Term *made = term != NULL ? form_term(TERM_FOLD, position,
                                              terms_item(function, terms_item(start_term, terms_item(source, NULL))))
                                  : NULL;
  if (checking_body(environment) == 1)
    return with_term(worked_value(&null_value, after, found_left, value, rest, left), term, made);
  const Values *items = NULL;
  if (!elements_of(more, found.value, &items)) return fail_at(failure, position, eFuel);
  const Value *result = NULL;
  Tokens ignored = {0};
  Nat folded_left = 0;
  if (!fold_items(more, found_left, position, op, carrier_code(found.type), items, start, &result, &ignored,
                  &folded_left, failure))
    return 0;
  return with_term(worked_value(result, after, folded_left, value, rest, left), term, made);
}

/* Each element uses one step of the depth fuel. Over Nat (code 1) the
   function takes only the accumulator. */
int fold_items(Fuel fuel, Nat budget, Nat position, Stepper op, Nat code, const Values *items, const Value *start,
               const Value **folded, Tokens *rest, Nat *left, Failure *failure) {
  if (fuel == 0) return fail_at(failure, position, eFuel);
  Fuel more = fuel - 1;
  if (items == NULL) return worked_value(start, (Tokens){0}, budget, folded, rest, left);
  const Value *acc = NULL;
  Tokens ignored = {0};
  Nat spent = 0;
  if (!fold_items(more, budget, position, op, code, items->tail, start, &acc, &ignored, &spent, failure)) return 0;
  const Values *arguments = code == 1 ? values_item(acc, NULL) : values_item(items->head, values_item(acc, NULL));
  return apply_body(more, nat_sub(spent, 1), stepper_result(op), stepper_environment(op, arguments),
                    stepper_body(op), op.term, folded, rest, left, failure);
}

/* unfold g n s checks against a carrier. It applies g to the seed s until g
   gives none or n elements exist. */
int unfold_term(Fuel fuel, Nat budget, Nat position, Nat atom, const LType *expected, const Bindings *environment,
                Tokens tokens, const Value **value, Tokens *rest, Nat *left, const Term **term, Failure *failure) {
  if (fuel == 0) return fail_at(failure, position, eFuel);
  Fuel more = fuel - 1;
  if (atom == 1) return fail_at(failure, position, eParen);
  if (carrier_code(expected) == 0) {
    if (same_type(expected, &value_type) == 1)
      return unfold_value_term(more, budget, position, environment, tokens, value, rest, left, term, failure);
    return fail_at(failure, position, eStructure);
  }
  Stepper op = {0};
  Tokens after_function = {0};
  Nat spent = 0;
  const Term *function = NULL;
  if (!stepper_term(more, budget, 1, expected, environment, tokens, &op, &after_function, &spent,
                    want_term(term, &function), failure))
    return 0;
  if (unfold_fits(expected, op) != 1) return fail_at(failure, first_position(tokens), eTerm);
  const Value *limit = NULL;
  Tokens after_limit = {0};
  Nat limit_left = 0;
  const Term *limit_term = NULL;
  if (!parse_term(more, spent, 1, &nat_type, environment, after_function, &limit, &after_limit, &limit_left,
                  want_term(term, &limit_term), failure))
    return 0;
  const Value *seed = NULL;
  Tokens after = {0};
  Nat seed_left = 0;
  const Term *seed_term = NULL;
  if (!parse_term(more, limit_left, 1, unfold_seed(op), environment, after_limit, &seed, &after, &seed_left,
                  want_term(term, &seed_term), failure))
    return 0;
  const Term *made = term != NULL ? form_term(TERM_UNFOLD, position,
                                              terms_item(function, terms_item(limit_term, terms_item(seed_term, NULL))))
                                  : NULL;
  if (checking_body(environment) == 1)
    return with_term(worked_value(&null_value, after, seed_left, value, rest, left), term, made);
  const Values *items = NULL;
  Tokens ignored = {0};
  Nat built_left = 0;
  if (!unfold_items(more, seed_left, position, op, carrier_code(expected), count_of(limit), seed, &items, &ignored,
                    &built_left, failure))
    return 0;
  const Value *rebuilt = NULL;
  Failure refused = {0};
  if (!rebuild(expected, items, &rebuilt, &refused)) return fail_at(failure, position, refused.message);
  return with_term(worked_value(rebuilt, after, built_left, value, rest, left), term, made);
}

/* Each element uses one step of the depth fuel. Into Nat (code 1) the
   payload of g is the next seed. Otherwise it is the pair of the element and
   the next seed. */
int unfold_items(Fuel fuel, Nat budget, Nat position, Stepper op, Nat code, Nat limit, const Value *seed,
                 const Values **values, Tokens *rest, Nat *left, Failure *failure) {
  if (fuel == 0) return fail_at(failure, position, eFuel);
  Fuel more = fuel - 1;
  if (limit == 0) return worked_values(NULL, (Tokens){0}, budget, values, rest, left);
  const Value *result = NULL;
  Tokens after = {0};
  Nat spent = 0;
  if (!apply_body(more, nat_sub(budget, 1), stepper_result(op), stepper_environment(op, values_item(seed, NULL)),
                  stepper_body(op), op.term, &result, &after, &spent, failure))
    return 0;
  const Value *payload = NULL;
  if (!payload_of(stepper_result(op), shape_element(stepper_result(op)), result, &payload))
    return worked_values(NULL, (Tokens){0}, spent, values, rest, left);
  const Values *items = NULL;
  Tokens ignored = {0};
  Nat used = 0;
  if (!unfold_items(more, spent, position, op, code, nat_sub(limit, 1), code == 1 ? payload : project_value(2, payload),
                    &items, &ignored, &used, failure))
    return 0;
  return worked_values(values_item(code == 1 ? &null_value : project_value(1, payload), items), (Tokens){0}, used,
                       values, rest, left);
}

/* One of the five functions of a fold over Value is a name or a partial
   application. Its parameter is the payload of its constructor and its
   result is the declared type. */
int algebra_term(Fuel fuel, Nat budget, Nat index, const LType *result, const Bindings *environment, Tokens tokens,
                 Stepper *op, Tokens *rest, Nat *left, const Term **term, Failure *failure) {
  if (fuel == 0) return fail_at(failure, first_position(tokens), eFuel);
  Fuel more = fuel - 1;
  Stepper found = {0};
  Tokens after = {0};
  Nat spent = 0;
  const Term *inner = NULL;
  if (!stepper_term(more, budget, 0, result, environment, tokens, &found, &after, &spent, want_term(term, &inner),
                    failure))
    return 0;
  if (same_type(stepper_result(found), result) != 0 &&
      same_types(param_types(stepper_params(found)), types_item(algebra_param(index, result), NULL)) != 0)
    return with_term(worked_stepper(found, after, spent, op, rest, left), term, inner);
  return fail_at(failure, first_position(tokens), eTerm);
}

/* The remaining four functions of a fold over Value. The first function has
   already been parsed and checked by fold_value_term. */
int algebra_terms(Fuel fuel, Nat budget, const LType *result, Stepper on_nat, const Bindings *environment,
                  Tokens tokens, ValueAlgebra *ops, Tokens *rest, Nat *left, const Terms **terms, Failure *failure) {
  if (fuel == 0) return fail_at(failure, first_position(tokens), eFuel);
  Fuel more = fuel - 1;
  Stepper on_flag = {0};
  Tokens after_flag = {0};
  Nat flag_left = 0;
  const Term *flag_term = NULL;
  if (!algebra_term(more, budget, 2, result, environment, tokens, &on_flag, &after_flag, &flag_left,
                    want_term(terms, &flag_term), failure))
    return 0;
  Stepper on_text = {0};
  Tokens after_text = {0};
  Nat text_left = 0;
  const Term *text_term = NULL;
  if (!algebra_term(more, flag_left, 3, result, environment, after_flag, &on_text, &after_text, &text_left,
                    want_term(terms, &text_term), failure))
    return 0;
  Stepper on_items = {0};
  Tokens after_items = {0};
  Nat items_left = 0;
  const Term *items_term = NULL;
  if (!algebra_term(more, text_left, 4, result, environment, after_text, &on_items, &after_items, &items_left,
                    want_term(terms, &items_term), failure))
    return 0;
  Stepper on_attrs = {0};
  Tokens after = {0};
  Nat attrs_left = 0;
  const Term *attrs_term = NULL;
  if (!algebra_term(more, items_left, 5, result, environment, after_items, &on_attrs, &after, &attrs_left,
                    want_term(terms, &attrs_term), failure))
    return 0;
  if (terms != NULL)
    *terms = terms_item(flag_term, terms_item(text_term, terms_item(items_term, terms_item(attrs_term, NULL))));
  *ops = (ValueAlgebra){on_nat, on_flag, on_text, on_items, on_attrs};
  *rest = after;
  *left = attrs_left;
  return 1;
}

/* A second function after the first selects the fold over Value. A name
   selects it, as the initial value is never the bare name of a function. A
   partial application selects it only when it fits the Flag position, as a
   parenthesized initial value also starts with an opening parenthesis. */
Nat second_function(Fuel fuel, Nat budget, const LType *result, const Bindings *environment, Tokens tokens) {
  if (fuel == 0) return 0;
  Fuel more = fuel - 1;
  if (names_function(environment, tokens) == 1) return 1;
  Stepper op = {0};
  Tokens rest = {0};
  Nat left = 0;
  Failure dropped = {0};
  return algebra_term(more, budget, 2, result, environment, tokens, &op, &rest, &left, NULL, &dropped) ? 1 : 0;
}

/* A fold over Value takes five functions before z. Each function is checked
   against the declared type before the source is read. */
int fold_value_term(Fuel fuel, Nat budget, Nat position, Nat function_position, const LType *expected,
                    Stepper on_nat, const Bindings *environment, Tokens tokens, const Value **value, Tokens *rest,
                    Nat *left, const Term **term, Failure *failure) {
  if (fuel == 0) return fail_at(failure, position, eFuel);
  Fuel more = fuel - 1;
  if (!(same_type(stepper_result(on_nat), expected) == 1 &&
        same_types(param_types(stepper_params(on_nat)), types_item(&nat_type, NULL)) == 1))
    return fail_at(failure, function_position, eTerm);
  ValueAlgebra ops = {0};
  Tokens after_functions = {0};
  Nat spent = 0;
  const Terms *functions = NULL;
  if (!algebra_terms(more, budget, expected, on_nat, environment, tokens, &ops, &after_functions, &spent,
                     want_terms(term, &functions), failure))
    return 0;
  const Value *start = NULL;
  Tokens after_start = {0};
  Nat used = 0;
  const Term *start_term = NULL;
  if (!parse_term(more, spent, 1, expected, environment, after_functions, &start, &after_start, &used,
                  want_term(term, &start_term), failure))
    return 0;
  Typed found = {0};
  Tokens after = {0};
  Nat found_left = 0;
  const Term *source = NULL;
  if (!synth_term(more, used, 1, environment, after_start, &found, &after, &found_left, want_term(term, &source),
                  failure))
    return 0;
  if (same_type(found.type, &value_type) != 1) return fail_at(failure, first_position(after_start), eCases);
  /* FOLD_VALUE [f2, f3, f4, f5, start, source]. fold_term adds the first function. */
  const Term *made = term != NULL ? form_term(TERM_FOLD_VALUE, position,
                                              reverse_terms_onto(terms_item(start_term, terms_item(source, NULL)),
                                                                 reverse_terms_onto(NULL, functions)))
                                  : NULL;
  if (checking_body(environment) == 1)
    return with_term(worked_value(&null_value, after, found_left, value, rest, left), term, made);
  const Value *result = NULL;
  Tokens ignored = {0};
  Nat folded_left = 0;
  if (!fold_value(more, found_left, position, ops, start, found.value, &result, &ignored, &folded_left, failure))
    return 0;
  return with_term(worked_value(result, after, folded_left, value, rest, left), term, made);
}

/* valueNull gives z. A scalar applies its function to the payload. Items and
   fields fold each child first, in order, and then apply their function to
   the list of the results. Each node and each child uses one step of the
   depth fuel. */
int fold_value(Fuel fuel, Nat budget, Nat position, ValueAlgebra ops, const Value *start, const Value *value,
               const Value **folded, Tokens *rest, Nat *left, Failure *failure) {
  if (fuel == 0) return fail_at(failure, position, eFuel);
  Fuel more = fuel - 1;
  if (value_index(value) == 0) return worked_value(start, (Tokens){0}, budget, folded, rest, left);
  const Values *results = NULL;
  Tokens ignored = {0};
  Nat spent = 0;
  if (!fold_children(more, budget, position, ops, start, value_index(value) == 5, child_elements(value), &results,
                     &ignored, &spent, failure))
    return 0;
  Stepper step = algebra_step(value_index(value), ops);
  return apply_body(more, nat_sub(spent, 1), stepper_result(step),
                    stepper_environment(step, values_item(algebra_input(value, results), NULL)), stepper_body(step),
                    step.term, folded, rest, left, failure);
}

/* A child of the fields (keyed = 1) is the pair of its key and its value.
   Its result is the pair of the key and the folded value. */
int fold_children(Fuel fuel, Nat budget, Nat position, ValueAlgebra ops, const Value *start, Nat keyed,
                  const Values *elements, const Values **folded, Tokens *rest, Nat *left, Failure *failure) {
  if (fuel == 0) return fail_at(failure, position, eFuel);
  Fuel more = fuel - 1;
  if (elements == NULL) return worked_values(NULL, (Tokens){0}, budget, folded, rest, left);
  const Value *head = elements->head;
  const Value *result = NULL;
  Tokens ignored = {0};
  Nat spent = 0;
  if (!fold_value(more, budget, position, ops, start, keyed != 0 ? project_value(2, head) : head, &result, &ignored,
                  &spent, failure))
    return 0;
  const Values *results = NULL;
  Tokens unused = {0};
  Nat used = 0;
  if (!fold_children(more, spent, position, ops, start, keyed, elements->tail, &results, &unused, &used, failure))
    return 0;
  const Value *child = keyed != 0 ? object_two(kFirst, project_value(1, head), kSecond, result) : result;
  return worked_values(values_item(child, results), (Tokens){0}, used, folded, rest, left);
}

/* unfold g n s into Value. g gives the layer of a seed. unfold applies g to
   the seeds in depth-first order, at most n times. A seed that is left after
   n applications becomes valueNull. */
int unfold_value_term(Fuel fuel, Nat budget, Nat position, const Bindings *environment, Tokens tokens,
                      const Value **value, Tokens *rest, Nat *left, const Term **term, Failure *failure) {
  if (fuel == 0) return fail_at(failure, position, eFuel);
  Fuel more = fuel - 1;
  Stepper op = {0};
  Tokens after_function = {0};
  Nat spent = 0;
  const Term *function = NULL;
  if (!stepper_term(more, budget, 2, &value_type, environment, tokens, &op, &after_function, &spent,
                    want_term(term, &function), failure))
    return 0;
  if (unfold_value_fits(op) != 1) return fail_at(failure, first_position(tokens), eTerm);
  const Value *limit = NULL;
  Tokens after_limit = {0};
  Nat limit_left = 0;
  const Term *limit_term = NULL;
  if (!parse_term(more, spent, 1, &nat_type, environment, after_function, &limit, &after_limit, &limit_left,
                  want_term(term, &limit_term), failure))
    return 0;
  const Value *seed = NULL;
  Tokens after = {0};
  Nat seed_left = 0;
  const Term *seed_term = NULL;
  if (!parse_term(more, limit_left, 1, unfold_seed(op), environment, after_limit, &seed, &after, &seed_left,
                  want_term(term, &seed_term), failure))
    return 0;
  const Term *made = term != NULL ? form_term(TERM_UNFOLD_VALUE, position,
                                              terms_item(function, terms_item(limit_term, terms_item(seed_term, NULL))))
                                  : NULL;
  if (checking_body(environment) == 1)
    return with_term(worked_value(&null_value, after, seed_left, value, rest, left), term, made);
  Grown node = {0};
  Tokens ignored = {0};
  Nat built_left = 0;
  if (!unfold_node(more, seed_left, position, op, count_of(limit), seed, &node, &ignored, &built_left, failure))
    return 0;
  return with_term(worked_value(grown_head(node), after, built_left, value, rest, left), term, made);
}

static int worked_grown(Grown found, Tokens after, Nat budget, Grown *grown, Tokens *rest, Nat *left) {
  *grown = found;
  *rest = after;
  *left = budget;
  return 1;
}

/* Each application of g uses one step of the depth fuel and one of the n
   applications. Duplicate keys of the fields are an error at unfold. */
int unfold_node(Fuel fuel, Nat budget, Nat position, Stepper op, Nat limit, const Value *seed, Grown *grown,
                Tokens *rest, Nat *left, Failure *failure) {
  if (fuel == 0) return fail_at(failure, position, eFuel);
  Fuel more = fuel - 1;
  if (limit == 0) return worked_grown(grown_leaf(&null_value, 0), (Tokens){0}, budget, grown, rest, left);
  const Value *layer = NULL;
  Tokens after = {0};
  Nat spent = 0;
  if (!apply_body(more, nat_sub(budget, 1), stepper_result(op), stepper_environment(op, values_item(seed, NULL)),
                  stepper_body(op), op.term, &layer, &after, &spent, failure))
    return 0;
  if (layer_index(layer) < 4)
    return worked_grown(grown_leaf(layer_payload(layer), nat_sub(limit, 1)), (Tokens){0}, spent, grown, rest, left);
  Grown built = {0};
  Tokens ignored = {0};
  Nat used = 0;
  if (!unfold_seeds(more, spent, position, op, layer_index(layer) == 5, nat_sub(limit, 1),
                    items_of(layer_payload(layer)), &built, &ignored, &used, failure))
    return 0;
  if (layer_index(layer) != 5)
    return worked_grown(grown_leaf(items_value(grown_items(built)), grown_limit(built)), (Tokens){0}, used, grown, rest,
                        left);
  const Attrs *fields = NULL;
  Failure refused = {0};
  if (!fields_of(grown_items(built), &fields, &refused)) return fail_at(failure, position, refused.message);
  return worked_grown(grown_leaf(make_value((Value){.kind = VALUE_ATTRS, .attrs = fields}), grown_limit(built)),
                      (Tokens){0}, used, grown, rest, left);
}

/* The seeds of the items, or the keys and seeds of the fields (keyed = 1),
   from the left. The applications that remain pass from each seed to the
   next seed. */
int unfold_seeds(Fuel fuel, Nat budget, Nat position, Stepper op, Nat keyed, Nat limit, const Values *seeds,
                 Grown *grown, Tokens *rest, Nat *left, Failure *failure) {
  if (fuel == 0) return fail_at(failure, position, eFuel);
  Fuel more = fuel - 1;
  if (seeds == NULL) return worked_grown((Grown){NULL, limit}, (Tokens){0}, budget, grown, rest, left);
  const Value *head = seeds->head;
  Grown node = {0};
  Tokens ignored = {0};
  Nat spent = 0;
  if (!unfold_node(more, budget, position, op, limit, keyed != 0 ? project_value(2, head) : head, &node, &ignored,
                   &spent, failure))
    return 0;
  Grown others = {0};
  Tokens unused = {0};
  Nat used = 0;
  if (!unfold_seeds(more, spent, position, op, keyed, grown_limit(node), seeds->tail, &others, &unused, &used, failure))
    return 0;
  const Value *child =
      keyed != 0 ? object_two(kFirst, project_value(1, head), kSecond, grown_head(node)) : grown_head(node);
  return worked_grown((Grown){values_item(child, grown_items(others)), grown_limit(others)}, (Tokens){0}, used, grown,
                      rest, left);
}
