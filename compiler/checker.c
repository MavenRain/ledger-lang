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

/* The slot of the first binder of the scope, or 0 (D3-s6 part C). */
static Nat frame_slot(const Bindings *environment) {
  for (; environment != NULL; environment = environment->tail)
    if (environment->head.slot != 0) return environment->head.slot;
  return 0;
}

/* A new binder takes the slot after the first binder of its scope: the
   parameters of a body 1 to n, an inline binder n + 1 plus the count of the
   inline binders below it (`### The index of a binder`). */
static const Bindings *slotted_item(Binding head, const Bindings *tail) {
  head.slot = frame_slot(tail) + 1;
  return bindings_item(head, tail);
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

/* The type arguments of an application on its definition scope. chosen
   holds the last type parameter first, thus the first one is deepest and
   each one takes the slot of its type parameter, as bind_params gives at
   check time. */
static const Bindings *type_frame(const Bindings *scope, const Bindings *chosen) {
  if (chosen == NULL) return scope;
  return slotted_item(chosen->head, type_frame(scope, chosen->tail));
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

/* D5 part C (design item 8): the node of a witness for a marker. A closed
   witness (VAL_CLOSED) gives the printed value of found, a body parameter
   its marker and a neutral term its node in marker form. */
static int witness_node(Fuel fuel, Nat position, Typed found, Val witness, const Term **node) {
  switch (witness.kind) {
  case VAL_CLOSED: {
    Val closed;
    if (!printed_side(fuel, found.value, &closed)) return 0;
    *node = term_closed(position, found.type, found.value, closed.text);
    return 1;
  }
  case VAL_VAR: *node = term_var(position, 0, marker_name(witness.index), witness.index); return 1;
  case VAL_TERM: *node = witness.node; return 1;
  }
  return 0;
}

/* D5 part B (design item 5): substitute a typed witness at level. Part C
   (design item 8): witness is the side form of the witness. A VAL_CLOSED
   witness puts the value of found. A side with no marker left closes on its
   node, as for a D4 side. */
static int put_side(Fuel fuel, Nat budget, const Bindings *environment, const LType *a, Nat level, Typed found,
                    Val witness, Val side, Val *result, Nat *left, Failure *failure) {
  *result = side;
  *left = budget;
  switch (side.kind) {
  case VAL_CLOSED: return 1;
  case VAL_VAR: {
    if (side.index != level) return 1;
    switch (witness.kind) {
    case VAL_CLOSED: return printed_side(fuel, found.value, result);
    case VAL_VAR: *result = witness; return 1;
    case VAL_TERM:
      *result = witness;
      if (term_marker_bound(witness.node) > 0) return 1;
      return close_side(fuel, budget, closed_environment(environment), a, witness, result, left, failure);
    }
    return 0;
  }
  case VAL_TERM: {
    Nat size = term_marker_bound(side.node);
    const Term *first = level < size ? term_marker_first(side.node, level) : NULL;
    if (first == NULL) return 1;
    const Term **table = arena_alloc(sizeof *table * (size + 1));
    for (Nat index = 0; index < size; index++) table[index] = NULL;
    if (!witness_node(fuel, first->position, found, witness, &table[level])) return 0;
    const Term *node = term_with_markers(side.node, table, size);
    *result = (Val){.kind = VAL_TERM, .node = node};
    if (term_marker_bound(node) > 0) return 1;
    /* A substituted side with no marker evaluates as at the top level,
       including a computed transport motive in a function body. */
    return close_side(fuel, budget, closed_environment(environment), a,
                      (Val){.kind = VAL_TERM, .node = node}, result, left, failure);
  }
  }
  return 0;
}

/* D5 part B (design items 5 and 7): B with the value of a for the marker at
   level, in each Eq of B. A nested Sigma binds its level in its right type,
   including when a type argument reuses an outer marker index. The walk has
   the form of instantiate_type and uses its fuel. Part C
   (design item 8): witness is the side form of a (see put_side). */
static int put_marker(Fuel fuel, Nat budget, const Bindings *environment, const LType *type, Nat level, Typed found,
                      Val witness, const LType **result, Nat *left, Failure *failure) {
  if (fuel == 0) return 0;
  Fuel more = fuel - 1;
  LType copy = *type;
  Nat first;
  Nat second;
  *left = budget;
  switch (type->tag) {
  case TY_EQ:
    if (!put_marker(more, budget, environment, type->left, level, found, witness, &copy.left, &first, failure) ||
        !put_side(more, first, environment, copy.left, level, found, witness, type->lhs, &copy.lhs, &second, failure) ||
        !put_side(more, second, environment, copy.left, level, found, witness, type->rhs, &copy.rhs, left, failure))
      return 0;
    break;
  case TY_OPTION:
  case TY_LIST:
  case TY_QUERY:
    if (!put_marker(more, budget, environment, type->left, level, found, witness, &copy.left, left, failure)) return 0;
    break;
  case TY_SIGMA:
    if (!put_marker(more, budget, environment, type->left, level, found, witness, &copy.left, left, failure)) return 0;
    if (type->level != level &&
        !put_marker(more, *left, environment, type->right, level, found, witness, &copy.right, left, failure)) return 0;
    break;
  case TY_PROD:
  case TY_SUM:
    if (!put_marker(more, budget, environment, type->left, level, found, witness, &copy.left, &first, failure) ||
        !put_marker(more, first, environment, type->right, level, found, witness, &copy.right, left, failure)) return 0;
    break;
  case TY_NAT:
  case TY_TEXT:
  case TY_FLAG:
  case TY_VALUE:
  case TY_VALUES:
  case TY_ATTRS:
  case TY_KIND:
  case TY_HASH:
  case TY_REF:
  case TY_SCHEMA:
  case TY_UNIVERSE:
  case TY_ARROW:
    *result = type;
    return 1;
  }
  *result = make_type(copy);
  return 1;
}

/* D5 part B (design item 7): witness and payload of a closed Sigma value.
   payload has B with the value of witness for the marker. Part C (design
   item 8): a neutral Sigma value (a parameter in a body) gives a neutral
   projection with the null value, and payload has B with the side of
   `witness s` for the marker (neutral_witness on the checked term of s, D8
   part B). With no term (eval_synth), a neutral payload is refused. */
static int neutral_witness(Fuel fuel, Nat budget, const Bindings *environment, const LType *a, Nat position,
                           const Term *argument, Val *side, Nat *left, Failure *failure);

/* D9 (design item 5): the failure of a side helper. A budget failure goes
   to the caller with no change (eBudget at the first token of the innermost
   body). Each other failure gives message at position, as before D9. */
static int side_failure(Failure *failure, Failure side, Nat position, Text message) {
  if (!same_text(side.message, eBudget)) return fail_at(failure, position, message);
  *failure = side;
  return 0;
}

/* D9 (design item 5): the failure of eval_term in a side. A budget failure
   goes to the caller with no change. Each other failure does not change the
   failure of the caller, as before D9. */
static int kept_budget_failure(Failure *failure, Failure side) {
  if (same_text(side.message, eBudget)) *failure = side;
  return 0;
}

static int project_sigma(Fuel fuel, Nat budget, const Bindings *environment, Nat position, Nat index, Typed found,
                         const Term *argument, Tokens tokens, Typed *result, Tokens *rest, Nat *left,
                         Failure *failure) {
  if (found.type->tag != TY_SIGMA) return fail_at(failure, position, eSigma);
  Nat neutral = found.value->kind != VALUE_ATTRS ? 1 : 0;
  Val side = {.kind = VAL_CLOSED};
  Nat spent = budget;
  Failure witnessed = {0, {NULL, 0}};
  if (neutral == 1 && index == 2 &&
      !neutral_witness(fuel, budget, environment, found.type->left, position, argument, &side, &spent, &witnessed))
    return side_failure(failure, witnessed, position, eTerm);
  const LType *b = found.type->left;
  const Value *witness = neutral == 1 ? &null_value : project_value(1, found.value);
  Nat used = spent;
  Failure put = {0, {NULL, 0}};
  if (index == 2 && !put_marker(fuel, spent, environment, found.type->right, found.type->level,
                                (Typed){found.type->left, witness}, side, &b, &used, &put))
    return side_failure(failure, put, position, eSigma);
  *result = (Typed){b, neutral == 1 ? &null_value : project_value(index, found.value)};
  *rest = tokens;
  *left = used;
  return 1;
}

int check_synthesized(Nat position, const LType *expected, Typed found, Tokens tokens, const Value **value,
                      Tokens *rest, Failure *failure) {
  if (!same_declared_type(expected, found.type)) return fail_at(failure, position, eTerm);
  *value = found.value;
  *rest = tokens;
  return 1;
}

/* Forms that synthesize a type from one argument: 1 first, 2 second,
   3 symm, 6 witness and 7 payload (D5 part B). The form 4 trans takes two
   arguments, and 5 either takes three. The form 8 cong (D6 part A) takes a
   name and one argument. The form 9 transport (D6 part B) takes a motive
   and two arguments. */
Nat synth_form(Text name) {
  if (same_text(name, seither)) return 5;
  if (same_text(name, scong)) return 8;
  if (same_text(name, stransport)) return 9;
  if (same_text(name, ssymm)) return 3;
  if (same_text(name, strans)) return 4;
  if (same_text(name, switness)) return 6;
  if (same_text(name, spayload)) return 7;
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

/* D6 part A (design item 3): the f of cong is the name of an earlier
   definition with one data parameter and a data result. A data result
   cannot name the parameter. */
static Nat cong_data(const LType *type) {
  return type->tag != TY_EQ && type->tag != TY_ARROW && type->tag != TY_SIGMA && type->tag != TY_UNIVERSE;
}

static int cong_function(Nat position, Text name, const Bindings *environment, const Binding **function,
                         Failure *failure) {
  if (!lookup(name, environment, function)) return fail_at(failure, position, eUnknown);
  const Binding *item = *function;
  if (item->kind != BIND_FUN || item->params == NULL || has_type_param(item->params)) return fail_at(failure, position, eCong);
  if (item->params->tail != NULL) return fail_at(failure, position, eCong);
  if (!cong_data(item->params->head.type) || !cong_data(item->type)) return fail_at(failure, position, eCong);
  return 1;
}

/* The number of the canonical JSON text of a closed Nat side. */
static Nat side_number(Text text) {
  Nat number = 0;
  for (Nat index = 0; index < text.size; index++) number = number * 10 + (text.items[index] - '0');
  return number;
}

/* D6 part A (design items 5 and 8): the argument node of a side (f x). A
   closed x of type Nat gives a number node. D11 part B (design item 8): a
   closed x of another type gives a closed node of the value that
   read_printed_value reads from its text. A text that the reader does not
   accept gives eTerm. A marker and a node give their witness node. */
static int cong_argument(Fuel fuel, Nat position, const LType *a, Val side, const Term **argument, Failure *failure) {
  switch (side.kind) {
  case VAL_CLOSED: {
    if (a->tag == TY_NAT) {
      *argument = term_number(position, 0, side_number(side.text));
      return 1;
    }
    const Value *value;
    if (!read_printed_value(side.text, &value)) return fail_at(failure, position, eTerm);
    *argument = term_closed(position, a, value, side.text);
    return 1;
  }
  case VAL_VAR:
  case VAL_TERM: return witness_node(fuel, position, (Typed){a, &null_value}, side, argument);
  }
  return 0;
}

/* A marker-free side needs real evaluation even during body checking.
   Keep named bindings in scope, but remove the unnamed checking frames.
   D11 part A (design item 2): each closed side in a body uses this path. */
const Bindings *closed_environment(const Bindings *environment) {
  if (checking_body(environment) != 1) return environment;
  const Bindings *kept = NULL;
  for (const Bindings *cell = environment; cell != NULL; cell = cell->tail)
    if (cell->head.name.size != 0) kept = bindings_item(cell->head, kept);
  return reverse_bindings_onto(NULL, kept);
}

/* The side (f x) of cong is a TERM_GROUP of a TERM_APPLY node, in the form
   of the parse of a declared side (f x). A side with a marker takes its
   normal form. A side with no marker closes with eval_term on the budget of
   the cong term (delta P2). D9: close_side and side_normal_at also run on
   the remaining work budget. A value that does not print is eTerm. */
static int cong_side(Fuel fuel, Nat budget, const Bindings *environment, Nat position, const Binding *function,
                     const LType *a, Val side, Val *result, Nat *left, Failure *failure) {
  if (fuel == 0) return 0;
  Fuel more = fuel - 1;
  const Term *argument;
  if (!cong_argument(more, position, a, side, &argument, failure)) return 0;
  const Term *call = term_call(TERM_APPLY, position, 0, (Tokens){NULL, 0}, 0, function->name,
                               term_named(TERM_NAME, position, 0, function->name, NULL, NULL), NULL,
                               terms_item(argument, NULL));
  const Term *node = term_form(TERM_GROUP, position, 0, terms_item(call, NULL));
  if (term_marker_bound(node) == 0) {
    const Value *value;
    if (!eval_term(more, budget, function->type, closed_environment(environment), node, &value, left, failure))
      return 0;
    return printed_side(more, value, result) ? 1 : fail_at(failure, position, eTerm);
  }
  if (!side_normal_at(more, budget, environment, function->type, node, &node, left, failure)) return 0;
  *result = (Val){.kind = VAL_TERM, .node = node};
  return 1;
}

/* D6 part A (design items 4 and 5): cong f e. e has the type Eq A x y, and
   f has one parameter of type A and the result type B. The result type is
   Eq B (f x) (f y). The value is the proof value of symm and trans. The
   budget after e is shared by both sides, and the remaining budget is returned. */
static int cong_proof(Fuel fuel, Nat budget, const Bindings *environment, Nat position, const Binding *function,
                      Typed found, Tokens tokens, Typed *result, Tokens *rest, Nat *left, Failure *failure) {
  const LType *a;
  Val x, y, fx, fy;
  if (!sides_of(found.type, &a, &x, &y)) return fail_at(failure, position, eProof);
  if (!same_type(function->params->head.type, a)) return fail_at(failure, position, eMatch);
  Nat spent;
  if (!cong_side(fuel, budget, environment, position, function, a, x, &fx, &spent, failure)) return 0;
  if (!cong_side(fuel, spent, environment, position, function, a, y, &fy, left, failure)) return 0;
  *result = (Typed){eq_type(function->type, fx, fy), &null_value};
  *rest = tokens;
  return 1;
}

/* D6 part B (design item 8, delta B-D2): the typed value of a side of e for
   put_marker. A closed side of type Nat gives its number. D11 part B (design
   item 8): a closed side of another type gives the value that
   read_printed_value reads from its text, as for cong. A text that the
   reader does not accept gives eTerm. A marker and a node give null, as for
   a neutral Sigma witness. */
static int transport_found(Nat position, const LType *a, Val side, Typed *found, Failure *failure) {
  switch (side.kind) {
  case VAL_CLOSED: {
    if (a->tag == TY_NAT) {
      *found = (Typed){a, nat_value(side_number(side.text))};
      return 1;
    }
    const Value *value;
    if (!read_printed_value(side.text, &value)) return fail_at(failure, position, eTerm);
    *found = (Typed){a, value};
    return 1;
  }
  case VAL_VAR:
  case VAL_TERM: *found = (Typed){a, &null_value}; return 1;
  }
  return 0;
}

/* D6 part B (design items 6 and 7): B of the motive (z : A') B with a side
   of e for the marker of z, on the pack path (put_marker). */
static int transport_type(Fuel fuel, Nat budget, const Bindings *environment, Nat position, const LType *motive,
                          Val side, const LType **result, Nat *left, Failure *failure) {
  Typed found;
  if (!transport_found(position, motive->left, side, &found, failure)) return 0;
  Failure put = {0, {NULL, 0}};
  if (!put_marker(fuel, budget, environment, motive->right, motive->level, found, side, result, left, &put))
    return side_failure(failure, put, position, eSigma);
  return 1;
}

/* D12 part B (design items 8 and 9): T of the family (x : A) T with the side
   of the argument for the marker of x. The reduction uses one step of the
   work budget, then transport_type uses the rest. At budget 0 the result is
   eBudget at position, and left keeps the budget (D10 delta 7). */
int family_type(Fuel fuel, Nat budget, const Bindings *environment, Nat position, const LType *family, Val side,
                const LType **result, Nat *left, Failure *failure) {
  if (budget == 0) {
    *left = budget;
    return fail_at(failure, position, eBudget);
  }
  return transport_type(fuel, budget - 1, environment, position, family, side, result, left, failure);
}

/* D6 part B (design items 7 and 8): transport (z : A') B e t. e has the type
   Eq A x y, and A' must be A. t checks against B with x for z. The result
   type is B with y for z. A neutral e and a closed e use this one path. */
static int transport_types(Fuel fuel, Nat budget, const Bindings *environment, Nat position, const LType *motive,
                           Typed found, const LType **bx, const LType **by, Nat *left, Failure *failure) {
  const LType *a;
  Val x, y;
  Nat spent;
  if (!sides_of(found.type, &a, &x, &y)) return fail_at(failure, position, eProof);
  if (!same_type(motive->left, a)) return fail_at(failure, position, eMatch);
  return transport_type(fuel, budget, environment, position, motive, x, bx, &spent, failure) &&
         transport_type(fuel, spent, environment, position, motive, y, by, left, failure);
}

/* D12 part C (design items 12, 13 and 15): the motive of form 9. A family
   name gives the family LType. In a body, the family moves by the count of
   the body parameters, as in family_application. The lookup parses nothing,
   thus left keeps the budget. Else sigma_type parses (z : A') B. */
static int transport_motive(Fuel fuel, Nat budget, const Bindings *environment, Tokens tokens, const LType **motive,
                            const Bindings **scope, Tokens *rest, Nat *left, Failure *failure) {
  const Params *done = body_params(environment);
  *scope = NULL;
  const Bindings *named = environment;
  if (tokens.size != 0 && tokens.items[0].kind == TOKEN_IDENTIFIER) {
    for (; named != NULL; named = named->tail)
      if (same_text(tokens.items[0].text, named->head.name)) break;
  } else {
    named = NULL;
  }
  if (named == NULL || named->head.kind != BIND_FAMILY)
    return sigma_type(fuel, budget, environment, done, tokens, motive, rest, left, failure);
  /* Keep the family binding as well, so an otherwise empty definition
     scope remains distinct from the current scope of an inline motive. */
  *scope = named;
  *motive = shift_type_markers(param_count(done), named->head.type);
  *rest = (Tokens){tokens.items + 1, tokens.size - 1};
  *left = budget;
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

/* The type parameter of a function type hides an outer type argument of the
   same name (step D7b). */
static const Bindings *hide_type_name(Text name, const Bindings *chosen) {
  if (name.size == 0) return chosen;
  return bindings_item(type_binding(name, &universe_zero, schema_of(name)), chosen);
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
    return make_type(
        (LType){.tag = ty->tag, .left = subst_type(chosen, ty->left), .right = subst_type(chosen, ty->right)});
  case TY_ARROW:
    return make_type((LType){.tag = TY_ARROW, .name = ty->name, .left = subst_type(chosen, ty->left),
                             .right = subst_type(hide_type_name(ty->name, chosen), ty->right)});
  case TY_SIGMA:
    return make_type((LType){.tag = TY_SIGMA, .name = ty->name, .level = ty->level,
                             .left = subst_type(chosen, ty->left), .right = subst_type(chosen, ty->right)});
  }
  return ty;
}

/* D8 part C (design item 13): the motive of a transport in the scope of an
   application. A type parameter gives its type argument (subst_type). A value
   parameter of slot s gives its value for the marker s - 1 (put_marker, the
   project_sigma form). A type parameter also has a slot, thus the walk skips
   each binding that is not a value. In a checking body the markers stay. */
static int application_motive(Fuel fuel, Nat budget, const Bindings *environment, Nat position, const LType *motive,
                              const LType **result, Nat *left, Failure *failure) {
  *result = motive;
  *left = budget;
  if (checking_body(environment) == 1) return 1;
  *result = subst_type(environment, motive);
  for (const Bindings *cell = environment; cell != NULL; cell = cell->tail) {
    if (cell->head.slot == 0 || cell->head.kind != BIND_VALUE) continue;
    Failure put = {0, {NULL, 0}};
    if (!put_marker(fuel, *left, environment, *result, cell->head.slot - 1, (Typed){cell->head.type, cell->head.value},
                    (Val){.kind = VAL_CLOSED}, result, left, &put))
      return side_failure(failure, put, position, eSigma);
  }
  return 1;
}

/* The value parameters of a function, with the type arguments in place of
   the type parameters. */
const Params *value_params(const Bindings *chosen, const Params *params) {
  if (params == NULL) return NULL;
  if (is_type_param(params->head)) return value_params(chosen, params->tail);
  return params_item((Param){params->head.name, subst_type(chosen, params->head.type)},
                     value_params(chosen, params->tail));
}

/* A closure with a type parameter, as a ReadPath parameter, takes its type
   arguments first (step D7b). A closure with no type parameter keeps its
   parameters and its result. */
static const Params *closure_params(const Bindings *chosen, const Params *params) {
  return chosen != NULL ? value_params(chosen, params) : params;
}

static const LType *closure_result(const Bindings *chosen, const LType *result) {
  return chosen != NULL ? subst_type(chosen, result) : result;
}

/* Side markers use the positions of all parameters, including type
   parameters. Keep those positions while specializing argument types. */
static const Params *side_params(const Bindings *chosen, const Params *params) {
  if (chosen == NULL || params == NULL) return params;
  return params_item((Param){params->head.name, subst_type(chosen, params->head.type)},
                     side_params(chosen, params->tail));
}

/* One type argument for each leading type parameter. The fuel goes to
   parse_type unchanged, as in the mech. D10: each type argument runs on
   the rest of the work budget, and left gets the rest. */
int type_arguments(Fuel fuel, Nat budget, const Params *params, const Bindings *environment, const Bindings *chosen,
                   Tokens tokens, const Bindings **result, Tokens *rest, const TermTypes **types, Nat *left,
                   Failure *failure) {
  const TermTypes *done = NULL;
  for (; params != NULL && is_type_param(params->head); params = params->tail) {
    const LType *given;
    Tokens after;
    if (!parse_type(fuel, budget, 1, environment, tokens, &given, &after, &budget, failure)) return 0;
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
  *left = budget;
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
  /* The builtin write as an argument (M1 part B, delta B-3). */
  if (!lookup(target, caller, &item))
    return same_text(target, swrite) == 1 && same_type(ty, write_path_type()) == 1
               ? closure_binding(name, write_binders(), arrow_result(ty),
                                 write_body(0, (Tokens){NULL, 0}, (Tokens){NULL, 0}), caller)
               : opaque_closure(name, ty);
  switch (item->kind) {
  case BIND_VALUE:
  case BIND_FAMILY:
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
   the TERM_BODY of the argument Value: inline_argument builds it also on the
   run-time path (D8 part A). */
Binding inline_closure(Text name, const LType *ty, const Value *value, const Bindings *caller) {
  return closure_binding(name, inline_params(inline_parts(value->items->head), arrow_params(ty)), arrow_result(ty),
                         value->term, caller);
}

Fuel type_fuel(Tokens tokens) { return (Fuel)tokens.size + 1; }

Tokens type_tokens_of(const Value *types) {
  const Values *items;
  return as_values(types, &items) ? inline_tokens(items) : (Tokens){0};
}

/* A partial application keeps both the tokens and the resolved type
   arguments. Closure reconstruction reuses the already-budgeted types. */
const Values *typed_bound(const Params *params, const Bindings *chosen, Tokens tokens, Tokens rest,
                          const Values *values) {
  if (!has_type_param(params)) return values;
  Nat used = tokens.size > rest.size ? tokens.size - rest.size : 0;
  const Value *types = make_value((Value){.kind = VALUE_ITEMS,
                                        .items = inline_token_values((Tokens){tokens.items, used}),
                                        .chosen = chosen});
  return values_item(types, values);
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
  case BIND_FAMILY:
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
      scope = slotted_item(value_binding(head.name, head.type, values->head), scope);
    else
      scope = slotted_item(bound_binding(values->head, head.name, head.type, caller), scope);
  }
  return scope;
}

/* The closure of a function with type parameters binds the type arguments
   in front of the definition scope, as an application does. */
static Binding typed_closure(const Values *rest, Text name, const LType *ty, Text other, const Params *params,
                             const LType *result, const Term *term, const Bindings *caller) {
  if (rest == NULL) return opaque_closure(name, ty);
  const Bindings *chosen = rest->head->chosen;
  const Values *values = rest->tail;
  if (chosen == NULL) {
    Tokens types = type_tokens_of(rest->head);
    Tokens after;
    Failure ignored;
    Nat unused;
    /* Token-only carriers can reconstruct types that evaluate no bodies.
       Checked partial applications keep their resolved types above. */
    if (!type_arguments(type_fuel(types), 1, params, caller, NULL, types, &chosen, &after, NULL, &unused, &ignored))
      return opaque_closure(name, ty);
  }
  const Params *formal = value_params(chosen, params);
  return closure_binding(name, drop_params(values_length(values), formal), subst_type(chosen, result), term,
                         bind_bound(values, formal, caller,
                                    type_frame(definition_scope(other, caller), chosen)));
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
        slotted_item(bind_param(params->head.name, params->head.type, argument_head(values), caller), environment);
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
const Bindings *unary_environment(Unary op, const Value *value) {
  return slotted_item(value_binding(op.name, op.type, value), op.scope);
}

int unary_from(const Bindings *scope, const Params *params, const LType *result, const Term *term, Unary *op) {
  if (params == NULL || params->tail != NULL || is_type_param(params->head)) return 0;
  *op = (Unary){params->head.name, params->head.type, result, scope, term};
  return 1;
}

/* A function parameter keeps the scope of its function argument. The op term
   is the term of the binding. The evaluator path uses this form: it makes no
   new node. */
static int unary_checked(const Bindings *scope, const Binding *item, Unary *op) {
  switch (item->kind) {
  case BIND_VALUE:
  case BIND_FAMILY:
  case BIND_TYPE:
  case BIND_ARROW:
    return 0;
  case BIND_FUN:
    return unary_from(scope, item->params, item->type, item->term, op);
  case BIND_CLOSURE:
    return unary_from(item->scope, item->params, item->type, item->term, op);
  }
  return 0;
}

/* The op term is the checked body Term of the binding (D8 part A). */
int unary_of(const Bindings *scope, const Binding *item, Unary *op) { return unary_checked(scope, item, op); }

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

const Bindings *stepper_environment(Stepper op, const Values *values) {
  return bind_params(op.params, values, op.scope);
}

/* A name gives reference_term, as unary_argument does. The op term is the
   checked body Term of the binding, as in unary_of (D8 part A). */
int stepper_argument(const Bindings *environment, Tokens tokens, Stepper *op, Tokens *rest, const Term **term,
                     Failure *failure) {
  if (tokens.size == 0) return fail_at(failure, 0, eStep);
  Token head = tokens.items[0];
  const Binding *item;
  if (head.kind != TOKEN_IDENTIFIER || !lookup(head.text, environment, &item)) return fail_at(failure, head.position, eStep);
  switch (item->kind) {
  case BIND_FUN:
    if (has_type_param(item->params)) return fail_at(failure, head.position, eStep);
    *op = (Stepper){item->params, item->type, definition_scope(item->name, environment), item->term};
    break;
  case BIND_CLOSURE:
    *op = (Stepper){item->params, item->type, item->scope, item->term};
    break;
  case BIND_VALUE: return fail_at(failure, head.position, eStep);
  case BIND_FAMILY:
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

int inline_binder(Fuel fuel, Nat budget, const Bindings *environment, const Bindings *seen, Tokens tokens,
                  Param *binder, Tokens *rest, Nat *left, Failure *failure) {
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
  if (!parse_type(fuel, budget, 0, environment, after_colon, &ty, &after_type, left, failure)) return 0;
  if (type_level(ty) != 0) return fail_at(failure, first_position(after_colon), eData);
  if (!expect_mark(41, after_type, rest, failure)) return fail_at(failure, failure->position, eFun);
  *binder = (Param){head.text, ty};
  return 1;
}

/* Each binder takes one unit of fuel (fuelMore), and the binder itself
   parses its type with the fuel that remains. */
int inline_binders(Fuel fuel, Nat budget, const Bindings *environment, const Bindings *seen, Tokens tokens,
                   const Params **binders, Tokens *body, Nat *left, Failure *failure) {
  const Params *done = NULL;
  for (;;) {
    if (fuel == 0) return fail_at(failure, first_position(tokens), eFuel);
    Fuel more = fuel - 1;
    Param binder;
    Tokens after_binder;
    if (!inline_binder(more, budget, environment, seen, tokens, &binder, &after_binder, &budget, failure)) return 0;
    done = params_item(binder, done);
    Failure ignored;
    if (expect_mark(63, after_binder, body, &ignored)) {
      *binders = reverse_params_onto(NULL, done);
      *left = budget;
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

/* D8 part B (design item 7): put the marker of each value parameter in a
   checked term, as marker_vars does for a marker name. A signature side
   (done is not NULL) names the parameters of done. A body side (done is
   NULL) names the body parameters of environment, and each one gets a
   binding of its marker in scope, bound to null with the type of the
   parameter. An inline function, a type or function parameter and a name
   under an inline binder are refused, as on the token path. */
static int param_marker(const Params *done, const Bindings *environment, Text name, Nat *found, Nat *index) {
  *found = 0;
  if (done != NULL) return !marker_for(name, done, found, index) || *found == 1;
  if (!body_level(name, environment, found, index)) return 0;
  const Binding *item;
  return *found == 0 || (lookup(name, environment, &item) && is_arrow_type(item->type) != 1);
}

static int put_marker_list(const Params *done, const Bindings *environment, const Terms *terms,
                           const Bindings **scope, const Terms **marked);

int put_param_markers(const Params *done, const Bindings *environment, const Term *term, const Bindings **scope,
                      const Term **marked) {
  *marked = term;
  if (term == NULL) return 1;
  if (term->tag == TERM_FUN) return 0;
  Nat found = 0;
  Nat index = 0;
  Nat named = term->tag == TERM_NAME || term->tag == TERM_VAR || term->tag == TERM_APPLY || term->tag == TERM_PARTIAL;
  Nat plain = (term->tag == TERM_NAME || term->tag == TERM_VAR) && term->types == NULL && term->args == NULL;
  if (named == 1 && !param_marker(done, environment, term->name, &found, &index)) return 0;
  if (found == 1 && plain != 1) return 0;
  const Binding *item;
  if (found == 1 && done == NULL && lookup(term->name, environment, &item))
    *scope = bindings_item(value_binding(marker_name(index), item->type, &null_value), *scope);
  if (found == 1) {
    *marked = term_var(term->position, term->cost, marker_name(index), index);
    return 1;
  }
  const Term *callee;
  const Terms *args;
  if (!put_param_markers(done, environment, term->callee, scope, &callee) ||
      !put_marker_list(done, environment, term->args, scope, &args))
    return 0;
  if (callee == term->callee && args == term->args) return 1;
  Term *copy = arena_alloc(sizeof *copy);
  *copy = *term;
  copy->callee = callee;
  copy->args = args;
  *marked = copy;
  return 1;
}

static int put_marker_list(const Params *done, const Bindings *environment, const Terms *terms,
                           const Bindings **scope, const Terms **marked) {
  *marked = terms;
  if (terms == NULL) return 1;
  const Term *head;
  const Terms *tail;
  if (!put_param_markers(done, environment, terms->head, scope, &head) ||
      !put_marker_list(done, environment, terms->tail, scope, &tail))
    return 0;
  if (head != terms->head || tail != terms->tail) *marked = terms_item(head, tail);
  return 1;
}

/* The node already names markers in scope, either from a signature or
   from put_param_markers on a body term. */
static int node_side(Fuel fuel, Nat budget, const Bindings *scope, const LType *a, const Term *node, Val *side,
                     Nat *left, Failure *failure) {
  if (node == NULL) return 0;
  const Term *marked = marker_vars(node);
  if (!side_normal_at(fuel, budget, scope, a, marked, &marked, left, failure)) return 0;
  *side = marked->tag == TERM_VAR ? (Val){.kind = VAL_VAR, .index = marked->index}
                                : (Val){.kind = VAL_TERM, .node = marked};
  return 1;
}

/* D4 part D (Q-D4-7 lift 1): a parenthesized argument in a body gives a
   VAL_TERM side of type a. As in a computed side, each body parameter of
   the atom becomes the marker of its body level, bound to null with the
   type of the parameter, and a side with a marker takes its normal form.
   An inline function stays refused. D8 part B (design item 7): the side
   comes from the checked term, not from a copy of the tokens. */
static int body_term_side(Fuel fuel, Nat budget, const Bindings *environment, const LType *a, const Term *term,
                          Val *side, Nat *left, Failure *failure) {
  const Bindings *scope = environment;
  const Term *marked;
  if (!put_param_markers(NULL, environment, term, &scope, &marked)) return 0;
  return node_side(fuel, budget, scope, a, marked, side, left, failure);
}

/* D5 part C (design item 8): the side of `witness s` for the checked term
   of s. D8 part B (design item 8): the node is the TERM_GROUP of TERM_WITNESS
   s, the form of the parenthesized argument `(witness s)`. It takes the path
   of a parenthesized argument in a body (body_term_side), thus the side has
   the form of a declared side `(witness s)`. A signature already names its
   markers and has no body-level frame, so its node uses node_side directly. */
static int neutral_witness(Fuel fuel, Nat budget, const Bindings *environment, const LType *a, Nat position,
                           const Term *argument, Val *side, Nat *left, Failure *failure) {
  if (argument == NULL) return 0;
  const Term *node = term_form(TERM_GROUP, position, 0,
                               terms_item(term_form(TERM_WITNESS, position, 0, terms_item(argument, NULL)), NULL));
  Nat found = 0;
  Nat index = 0;
  if (body_level(switness, environment, &found, &index))
    return body_term_side(fuel, budget, environment, a, node, side, left, failure);
  return node_side(fuel, budget, environment, a, node, side, left, failure);
}

/* D8 part B (design item 7, delta D-B1): the side of an argument comes from
   its checked term. A body parameter in parentheses has the side of the
   body parameter. Another parenthesized term gives a VAL_TERM side
   (body_term_side). */
int argument_text(Fuel fuel, Nat budget, const Bindings *environment, const LType *a, const Value *value,
                  const Term *term, Val *side, Nat *left, Failure *failure) {
  *left = budget;
  if (checking_body(environment) != 1) return printed_side(fuel, value, side);
  if (term == NULL) return 0;
  if (term->tag == TERM_NUMBER || term->tag == TERM_STRING) return printed_side(fuel, value, side);
  const Term *inner = term;
  for (; inner->tag == TERM_GROUP && inner->args != NULL; inner = inner->args->head) {}
  Nat plain = (inner->tag == TERM_VAR || inner->tag == TERM_NAME) && inner->types == NULL && inner->args == NULL;
  Nat found = 0;
  Nat index = 0;
  if (term->tag == TERM_GROUP && plain == 1 && body_level(inner->name, environment, &found, &index) && found == 1) {
    *side = (Val){.kind = VAL_VAR, .index = index};
    return 1;
  }
  if (term->tag == TERM_GROUP) return body_term_side(fuel, budget, environment, a, term, side, left, failure);
  if (!body_level(term->name, environment, &found, &index)) return 0;
  if (found == 0) return printed_side(fuel, value, side);
  *side = (Val){.kind = VAL_VAR, .index = index};
  return 1;
}

int argument_side(Fuel fuel, Nat budget, Nat index, const Bindings *environment, const Params *params,
                  const Values *values, const Terms *args, Val *side, Nat *left, Failure *failure) {
  for (; params != NULL; params = params->tail, index = index - 1) {
    if (is_type_param(params->head) == 1) {
      if (index == 0) return 0;
      continue;
    }
    if (index == 0)
      return argument_text(fuel, budget, environment, params->head.type, argument_head(values),
                           args != NULL ? args->head : NULL, side, left, failure);
    values = argument_tail(values);
    args = args != NULL ? args->tail : NULL;
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

/* The node of a closed argument token, with cost 0 (Q-S9-6). A
   parenthesized argument gives a VAL_TERM side (argument_text, D4 part D),
   thus rename_markers does not come here with it. */
static int closed_node(Fuel fuel, Nat budget, Nat index, const Bindings *environment, const Params *params, Token token,
                       const Term **node, Nat *left, Failure *failure) {
  *left = budget;
  switch (token.kind) {
  case TOKEN_NUMBER: *node = term_number(token.position, 0, token.number); return 1;
  case TOKEN_STRING: *node = term_string(token.position, 0, token.text); return 1;
  case TOKEN_IDENTIFIER: {
    for (; params != NULL && index != 0; params = params->tail, index--) {}
    if (params == NULL) return 0;
    /* Match parse_term: bindings take precedence over constructors, and
       refl is a form rather than a name. */
    const Binding *item;
    Plan selected;
    if (lookup(token.text, environment, &item)) {
      *node = term_named(TERM_NAME, token.position, 0, token.text, NULL, NULL);
    } else if (constructor_plan(params->head.type, token.text, &selected)) {
      *node = term_named(TERM_CONSTRUCT, token.position, 0, token.text, NULL, NULL);
    } else if (same_text(token.text, srefl)) {
      *node = term_form(TERM_REFL, token.position, 0, NULL);
    } else {
      return 0;
    }
    return side_normal_at(fuel, budget, environment, params->head.type, *node, node, left, failure);
  }
  case TOKEN_PUNCTUATION: return 0;
  }
  return 0;
}

/* The mech recursion renames the tail first, but a none anywhere gives
   none and nothing else depends on the order, so the loop goes forward.
   The table maps each marker of the node to its argument: a VAL_VAR
   argument to the variable node of its marker, at the position of the
   first variable node of the marker, a VAL_TERM argument to its node (its
   markers are body levels already; D4 part D), and a closed argument to
   its node. */
int rename_markers(Fuel fuel, Nat budget, const Bindings *environment, const Params *params, const Values *values,
                   const Terms *args, Tokens tokens, const Term *node, const Term **renamed_node, Nat *left,
                   Failure *failure) {
  Nat size = term_marker_bound(node);
  const Term **table = arena_alloc(sizeof *table * (size + 1));
  for (Nat index = 0; index < size; index++) {
    table[index] = NULL;
    const Term *first = term_marker_first(node, index);
    if (first == NULL) continue;
    Val side;
    if (!argument_side(fuel, budget, index, environment, params, values, args, &side, &budget, failure)) return 0;
    if (side.kind == VAL_TERM) {
      table[index] = side.node;
      continue;
    }
    if (side.kind == VAL_VAR) {
      table[index] = term_var(first->position, 0, marker_name(side.index), side.index);
      continue;
    }
    Token token;
    if (!argument_token(index, params, tokens, &token)) return 0;
    if (!closed_node(fuel, budget, index, environment, params, token, &table[index], &budget, failure)) return 0;
  }
  *renamed_node = term_with_markers(node, table, size);
  *left = budget;
  return 1;
}

Nat kept_side(Val side) {
  switch (side.kind) {
  case VAL_CLOSED:
  case VAL_VAR: return 1;
  case VAL_TERM: return term_marker_bound(side.node) > 0;
  }
  return 0;
}

int instantiate_side(Fuel fuel, Nat budget, const Bindings *environment, const Params *params, const Values *values,
                     const Terms *args, Tokens tokens, Val side, Val *result, Nat *left, Failure *failure) {
  *left = budget;
  switch (side.kind) {
  case VAL_CLOSED: *result = side; return 1;
  case VAL_VAR: return argument_side(fuel, budget, side.index, environment, params, values, args, result, left, failure);
  case VAL_TERM: {
    if (checking_body(environment) != 1) {
      *result = side;
      return 1;
    }
    const Term *node;
    if (!rename_markers(fuel, budget, environment, params, values, args, tokens, side.node, &node, left, failure))
      return 0;
    /* D4 part C: a side with a marker left takes its normal form again
       (design item 5). close_body_side closes a side with no marker left. */
    if (term_marker_bound(node) > 0 && !side_normal(fuel, *left, environment, node, &node, left, failure)) return 0;
    *result = (Val){.kind = VAL_TERM, .node = node};
    return 1;
  }
  }
  return 0;
}

typedef struct SigmaMarker SigmaMarker;
struct SigmaMarker {
  Nat from;
  Nat to;
  const SigmaMarker *outer;
};

static int sigma_marker(const SigmaMarker *scope, Nat from, Nat *to) {
  for (; scope != NULL; scope = scope->outer)
    if (scope->from == from) {
      *to = scope->to;
      return 1;
    }
  return 0;
}

/* A local Sigma variable stays bound. Free signature variables become
   arguments. Fresh local markers prevent those arguments from being captured. */
static int instantiate_scoped_side(Fuel fuel, Nat budget, const Bindings *environment, const Params *params,
                                   const Values *values, const Terms *args, Tokens tokens,
                                   const SigmaMarker *scope, Val side, Val *result, Nat *left, Failure *failure) {
  *left = budget;
  if (scope == NULL || side.kind == VAL_CLOSED)
    return instantiate_side(fuel, budget, environment, params, values, args, tokens, side, result, left, failure);
  if (side.kind == VAL_VAR) {
    Nat to;
    if (!sigma_marker(scope, side.index, &to))
      return instantiate_side(fuel, budget, environment, params, values, args, tokens, side, result, left, failure);
    *result = (Val){.kind = VAL_VAR, .index = to};
    return 1;
  }
  Nat size = term_marker_bound(side.node);
  const Term **table = arena_alloc(sizeof *table * (size + 1));
  for (Nat index = 0; index < size; index++) {
    table[index] = NULL;
    const Term *first = term_marker_first(side.node, index);
    if (first == NULL) continue;
    Nat to;
    if (sigma_marker(scope, index, &to)) {
      table[index] = term_var(first->position, 0, marker_name(to), to);
      continue;
    }
    if (checking_body(environment) != 1) continue;
    Val argument;
    if (!argument_side(fuel, budget, index, environment, params, values, args, &argument, &budget, failure)) return 0;
    if (argument.kind == VAL_TERM) table[index] = argument.node;
    else if (argument.kind == VAL_VAR)
      table[index] = term_var(first->position, 0, marker_name(argument.index), argument.index);
    else {
      Token token;
      if (!argument_token(index, params, tokens, &token) ||
          !closed_node(fuel, budget, index, environment, params, token, &table[index], &budget, failure)) return 0;
    }
  }
  const Term *node = term_with_markers(side.node, table, size);
  *left = budget;
  if (checking_body(environment) == 1 && term_marker_bound(node) > 0 &&
      !side_normal(fuel, budget, environment, node, &node, left, failure)) return 0;
  *result = (Val){.kind = VAL_TERM, .node = node};
  return 1;
}

static int instantiate_type(Fuel fuel, Nat budget, const Bindings *environment, const Params *params,
                            const Values *values, const Terms *args, Tokens tokens, const Bindings *chosen,
                            const SigmaMarker *scope, const LType *type, const LType **instantiated, Nat *left,
                            Failure *failure) {
  *left = budget;
  /* A supplied type already uses the caller's markers. Substituting the
     callee's arguments into it would change its free variables. */
  for (const Bindings *cell = chosen; cell != NULL; cell = cell->tail)
    if (cell->head.kind == BIND_TYPE && cell->head.defined == type) {
      *instantiated = type;
      return 1;
    }
  LType copy = *type;
  Nat first;
  Nat second;
  switch (type->tag) {
  case TY_EQ:
    if (!instantiate_type(fuel, budget, environment, params, values, args, tokens, chosen, scope, type->left,
                          &copy.left, &first, failure) ||
        !instantiate_scoped_side(fuel, first, environment, params, values, args, tokens, scope, type->lhs, &copy.lhs,
                                 &second, failure) ||
        !instantiate_scoped_side(fuel, second, environment, params, values, args, tokens, scope, type->rhs, &copy.rhs,
                                 left, failure)) return 0;
    if (checking_body(environment) == 1 &&
        (!close_body_side(fuel, *left, environment, copy.left, copy.lhs, &copy.lhs, &first, failure) ||
         !close_body_side(fuel, first, environment, copy.left, copy.rhs, &copy.rhs, left, failure))) return 0;
    break;
  case TY_SIGMA: {
    if (fuel == 0) return 0;
    if (!instantiate_type(fuel - 1, budget, environment, params, values, args, tokens, chosen, scope, type->left,
                          &copy.left, &first, failure)) return 0;
    copy.level = frame_slot(environment) + type->level;
    SigmaMarker inner = {type->level, copy.level, scope};
    if (!instantiate_type(fuel - 1, first, environment, params, values, args, tokens, chosen, &inner, type->right,
                          &copy.right, left, failure)) return 0;
    break;
  }
  case TY_OPTION:
  case TY_LIST:
  case TY_QUERY:
    if (fuel == 0 || !instantiate_type(fuel - 1, budget, environment, params, values, args, tokens, chosen, scope,
                                     type->left, &copy.left, left, failure)) return 0;
    break;
  case TY_PROD:
  case TY_SUM:
    if (fuel == 0 || !instantiate_type(fuel - 1, budget, environment, params, values, args, tokens, chosen, scope,
                                     type->left, &copy.left, &first, failure) ||
        !instantiate_type(fuel - 1, first, environment, params, values, args, tokens, chosen, scope, type->right,
                          &copy.right, left, failure)) return 0;
    break;
  case TY_NAT:
  case TY_TEXT:
  case TY_FLAG:
  case TY_VALUE:
  case TY_VALUES:
  case TY_ATTRS:
  case TY_KIND:
  case TY_HASH:
  case TY_REF:
  case TY_SCHEMA:
  case TY_UNIVERSE:
  case TY_ARROW:
    *instantiated = type;
    return 1;
  }
  *instantiated = make_type(copy);
  return 1;
}

int instantiate_result(Fuel fuel, Nat budget, const Bindings *environment, const Params *params, const Values *values,
                       const Terms *args, Tokens tokens, const LType *result, const LType **instantiated, Nat *left,
                       Failure *failure) {
  return instantiate_type(fuel, budget, environment, params, values, args, tokens, NULL, NULL, result, instantiated,
                          left, failure);
}

static int instantiate_specialized(Fuel fuel, Nat budget, const Bindings *environment, const Params *params,
                                   const Values *values, const Terms *args, Tokens tokens, const Bindings *chosen,
                                   const LType *result, const LType **instantiated, Nat *left, Failure *failure) {
  return instantiate_type(fuel, budget, environment, params, values, args, tokens, chosen, NULL, result, instantiated,
                          left, failure);
}

/* D9: a param that does not instantiate stays as it is, as before D9, and
   its work is not charged (the same rule as close_params). */
const Params *instantiate_params(Fuel fuel, Nat budget, const Bindings *environment, const Params *params,
                                 const Values *values, const Terms *args, Tokens tokens, const Params *remaining,
                                 Nat *left) {
  const Params *done = NULL;
  *left = budget;
  for (; remaining != NULL; remaining = remaining->tail) {
    Param head = remaining->head;
    const LType *found;
    Nat spent;
    Failure failure = {0, {NULL, 0}};
    int instantiated = instantiate_result(fuel, *left, environment, params, values, args, tokens, head.type, &found,
                                          &spent, &failure);
    if (instantiated) *left = spent;
    done = params_item(instantiated ? (Param){head.name, found} : head, done);
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
                              Tokens tokens, Nat end, const Bindings *environment) {
  if (terms_built(args) != 1) return NULL;
  const Term *callee = tag == TERM_APPLY || tag == TERM_PARTIAL ? reference_term(position, name, environment) : NULL;
  return term_call(tag, position, 0, tokens, end, name, callee, types, args);
}

static const Term *form_term(TermTag tag, Nat position, const Terms *args) {
  return terms_built(args) == 1 ? term_form(tag, position, 0, args) : NULL;
}

/* D6 part B (delta B-D3): TERM_TRANSPORT keeps the motive as its one term
   type, and e and t in args. D8 part C (design item 12): the motive is the
   LType of the check, with the parameters of the body as markers. It has no
   source tokens. */
static const Term *transport_term(Nat position, const LType *motive, const Bindings *scope, const Term *proof,
                                  const Term *value) {
  const Terms *args = terms_item(proof, terms_item(value, NULL));
  return terms_built(args) == 1
             ? term_named(TERM_TRANSPORT, position, 0, stransport,
                          term_types_item((TermType){.position = position, .type = motive, .scope = scope}, NULL), args)
             : NULL;
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
      case BIND_FAMILY:
      case BIND_TYPE:
      case BIND_ARROW: return fail_at(failure, head.position, eInfer);
      case BIND_FUN: {
        if (atom == 1) return fail_at(failure, head.position, eParen);
        const Bindings *chosen;
        Tokens after_types;
        const TermTypes *types = NULL;
        if (!type_arguments(more, budget, item->params, environment, NULL, tail, &chosen, &after_types,
                            want_types(term, &types), &budget, failure))
          return 0;
        const Values *values;
        const Terms *args = NULL;
        if (!dependent_arguments(more, budget, chosen, environment, item->params, item->params, NULL, after_types,
                                 after_types, &values, &after, &spent, want_terms(term, &args), failure))
          return 0;
        const Term *applied_term = term != NULL ? named_term(TERM_APPLY, head.position, head.text, types, args,
                                                             taken_tokens(tail, after), first_position(after),
                                                             environment)
                                                : NULL;
        const LType *instantiated = NULL;
        Nat ready = spent;
        Failure closing = {0, {NULL, 0}};
        int resolved = instantiate_specialized(more, spent, environment, side_params(chosen, item->params), values,
                                               term != NULL ? args : NULL, after_types, chosen,
                                               subst_type(chosen, item->type), &instantiated, &ready, &closing);
        const LType *applied;
        if (!close_result(more, ready, environment, item->params, values, resolved, instantiated, &applied, &spent,
                          &closing))
          return side_failure(failure, closing, head.position, eTerm);
        if (checking_body(environment) == 1)
          return with_term(worked_typed((Typed){applied, &null_value}, after, spent, typed, rest, left), term,
                           applied_term);
        const Params *instantiated_params =
            instantiate_params(more, spent, environment, item->params, values, term != NULL ? args : NULL, after_types,
                               item->params, &spent);
        const Params *closed;
        if (!close_params(more, spent, environment, item->params, values, instantiated_params, &closed, &spent,
                          failure))
          return 0;
        const Bindings *scope = bind_arguments(environment, value_params(chosen, closed), values,
                                               type_frame(definition_scope(item->name, environment), chosen));
        const Value *value;
        Nat used;
        /* eval_term gives a value or a failure for a body Term (D8 part A). */
        if (!eval_term(more, nat_sub(spent, 1), applied, scope, item->term, &value, &used, failure)) return 0;
        return with_term(worked_typed((Typed){applied, value}, after, used, typed, rest, left), term, applied_term);
      }
      case BIND_CLOSURE: {
        if (dependent_result(item->type) == 1 || dependent_params(item->params) == 1)
          return fail_at(failure, head.position, eTerm);
        if (atom == 1) return fail_at(failure, head.position, eParen);
        const Bindings *chosen;
        Tokens after_types;
        const TermTypes *types = NULL;
        if (!type_arguments(more, budget, item->params, environment, NULL, tail, &chosen, &after_types,
                            want_types(term, &types), &budget, failure))
          return 0;
        const Params *formal = closure_params(chosen, item->params);
        const LType *result = closure_result(chosen, item->type);
        const Values *values;
        const Terms *args = NULL;
        if (!parse_arguments(more, budget, 1, param_types(formal), environment, after_types, &values, &after, &spent,
                             want_terms(term, &args), failure))
          return 0;
        const Term *applied_term = term != NULL ? named_term(TERM_APPLY, head.position, head.text, types, args,
                                                             taken_tokens(tail, after), first_position(after),
                                                             environment)
                                                : NULL;
        if (checking_body(environment) == 1)
          return with_term(worked_typed((Typed){result, &null_value}, after, spent, typed, rest, left), term,
                           applied_term);
        const Bindings *scope = bind_arguments(environment, formal, values, type_frame(item->scope, chosen));
        const Value *value;
        Nat used;
        /* A closure with no term (a failed lookup) gives eTerm at 0, the answer
           of the token path on an empty span. Else eval_term gives a value or a
           failure for a body Term (D8 part A). */
        if (item->term == NULL) return fail_at(failure, 0, eTerm);
        if (!eval_term(more, nat_sub(spent, 1), result, scope, item->term, &value, &used, failure)) return 0;
        return with_term(worked_typed((Typed){result, value}, after, used, typed, rest, left), term,
                         applied_term);
      }
      }
      return 0;
    }
    Nat form = synth_form(head.text);
    if (form == 0) return fail_at(failure, head.position, same_text(head.text, spack) ? eSigma : eInfer);
    if (atom == 1) return fail_at(failure, head.position, eParen);
    if (form == 5)
      return either_term(more, budget, head.position, environment, tail, typed, rest, left, term, failure);
    if (form == 8) {
      /* D6 part A (design items 3 and 4): read f before e. */
      if (tail.size == 0 || tail.items[0].kind != TOKEN_IDENTIFIER)
        return fail_at(failure, tail.size == 0 ? head.position : tail.items[0].position, eCong);
      Token name = tail.items[0];
      const Binding *function;
      if (!cong_function(name.position, name.text, environment, &function, failure)) return 0;
      const Term *proof = NULL;
      if (!synth_term(more, budget, 1, environment, (Tokens){tail.items + 1, tail.size - 1}, &found, &after, &spent,
                      want_term(term, &proof), failure))
        return 0;
      return with_term(
          cong_proof(more, spent, environment, head.position, function, found, after, typed, rest, left, failure),
          term,
          term != NULL ? form_term(TERM_CONG, head.position,
                                   terms_item(term_named(TERM_NAME, name.position, 0, name.text, NULL, NULL),
                                              terms_item(proof, NULL)))
                       : NULL);
    }
    if (form == 9) {
      /* D6 part B (design items 6 and 7): the motive (z : A') B, then e, then t. */
      const LType *motive;
      const Bindings *motive_scope;
      Tokens proof_tokens;
      /* D10: the motive runs on the work budget, and the proof takes the rest.
         D12 part C: a family name is also a motive (transport_motive). */
      if (!transport_motive(more, budget, environment, tail, &motive, &motive_scope, &proof_tokens, &spent, failure))
        return 0;
      const Term *proof = NULL;
      if (!synth_term(more, spent, 1, environment, proof_tokens, &found, &after, &spent, want_term(term, &proof),
                      failure))
        return 0;
      const LType *bx, *by;
      if (!transport_types(more, spent, motive_scope != NULL ? motive_scope : environment,
                           head.position, motive, found, &bx, &by, &spent, failure)) return 0;
      const Value *value;
      Tokens later;
      Nat used;
      const Term *second = NULL;
      if (!parse_term(more, spent, 1, bx, environment, after, &value, &later, &used, want_term(term, &second), failure))
        return 0;
      return with_term(worked_typed((Typed){by, value}, later, used, typed, rest, left), term,
                       term != NULL ? transport_term(head.position, motive, motive_scope, proof, second) : NULL);
    }
    const Term *first = NULL;
    if (!synth_term(more, budget, 1, environment, tail, &found, &after, &spent, &first, failure))
      return 0;
    if (form < 3)
      return with_term(lift_parsed(spent, project(head.position, form, found, after, typed, rest, failure), left), term,
                       term != NULL ? form_term(form == 1 ? TERM_FIRST : TERM_SECOND, head.position,
                                                terms_item(first, NULL))
                                    : NULL);
    if (form > 5)
      return with_term(project_sigma(more, spent, environment, head.position, form - 5, found, first, after, typed,
                                     rest, left, failure),
                       term, term != NULL ? form_term(form == 6 ? TERM_WITNESS : TERM_PAYLOAD, head.position,
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

/* D5 part B (design items 5 and 6): pack a b checks only against an expected
   Sigma type. It checks a against A, puts a for the marker in B, and checks b
   against that B. The value is the object of witness and payload. An Eq
   payload is null (refl). Part C (design item 8): a is put as its side form
   (argument_text). In a body, a body parameter or a parenthesized term thus
   stays in marker form, not a printed null value. */
static int pack_term(Fuel fuel, Nat budget, Nat atom, Nat position, const LType *expected,
                     const Bindings *environment, Tokens tokens, const Value **value, Tokens *rest, Nat *left,
                     const Term **term, Failure *failure) {
  if (fuel == 0) return 0;
  Fuel more = fuel - 1;
  if (expected->tag != TY_SIGMA) return fail_at(failure, position, eSigma);
  if (atom == 1) return fail_at(failure, position, eParen);
  const Value *witness;
  Tokens after;
  Nat spent;
  const Term *first = NULL;
  if (!parse_term(more, budget, 1, expected->left, environment, tokens, &witness, &after, &spent, &first, failure))
    return 0;
  Val side;
  Nat ready;
  Failure argued = {0, {NULL, 0}};
  if (!argument_text(more, spent, environment, expected->left, witness, first, &side, &ready, &argued))
    return side_failure(failure, argued, position, eTerm);
  const LType *b;
  Failure put = {0, {NULL, 0}};
  if (!put_marker(more, ready, environment, expected->right, expected->level, (Typed){expected->left, witness}, side,
                  &b, &spent, &put))
    return side_failure(failure, put, position, eSigma);
  const Value *payload;
  Tokens later;
  Nat used;
  const Term *second = NULL;
  if (!parse_term(more, spent, 1, b, environment, after, &payload, &later, &used, want_term(term, &second), failure))
    return 0;
  const Term *built = term != NULL ? named_term(TERM_CONSTRUCT, position, spack, NULL,
                                                terms_item(first, terms_item(second, NULL)),
                                                taken_tokens(tokens, later), first_position(later), environment)
                                   : NULL;
  return with_term(worked_value(object_two(kWitness, witness, kPayload, payload), later, used, value, rest, left), term,
                   built);
}

/* M1 part B (design items 5 to 8): the builtin write. */

/* The body of a WritePath function: write log command, with the names of
   write_binders (delta B-2). The body is the TERM_CONSTRUCT, not a
   TERM_BODY (delta B-4). */
const Term *write_body(Nat position, Tokens body, Tokens rest) {
  const Terms *args =
      terms_item(term_named(TERM_NAME, position, 0, text_of_cstring("log"), NULL, NULL),
                 terms_item(term_named(TERM_NAME, position, 0, text_of_cstring("command"), NULL, NULL), NULL));
  return term_call(TERM_CONSTRUCT, position, 0, taken_tokens(body, rest), first_position(rest), swrite, NULL, NULL,
                   args);
}

static const LType *write_schema_type(const char *name) {
  LType *made = arena_alloc(sizeof *made);
  *made = (LType){.tag = TY_SCHEMA, .name = text_of_cstring(name)};
  return made;
}

/* The value of a constructor of a schema family, from its plan. Thus the
   tag and the field order are the normal ones. */
static int write_value(const char *family, const char *name, const Values *values, const Value **value,
                       Failure *failure) {
  Plan selected;
  if (!constructor_plan(write_schema_type(family), text_of_cstring(name), &selected))
    return fail_at(failure, 0, eTerm);
  return evaluate_plan(&selected, values, value, failure);
}

static const Value *write_attr(Text key, const Attrs *attrs) {
  return attrs == NULL ? &null_value : same_text(attrs->key, key) == 1 ? attrs->value : write_attr(key, attrs->rest);
}

/* The field key of an attrs value. A missing field is null. */
static const Value *write_field(Text key, const Value *value) {
  return value->kind == VALUE_ATTRS ? write_attr(key, value->attrs) : &null_value;
}

static const Value *write_last(const Values *items) {
  return items == NULL ? NULL : items->tail == NULL ? items->head : write_last(items->tail);
}

/* The Commands with a Body (k5 item 12): the Command, its field, and the
   Body constructor. The Body field has the same name. */
static const char *const write_bodies[6][3] = {
    {"commandStartMembership", "membership", "createsMembership"},
    {"commandOpenCommercial", "commercial", "createsCommercial"},
    {"commandPropose", "commitment", "createsCommitment"},
    {"commandIngest", "artifact", "createsArtifact"},
    {"commandRecord", "event", "createsEvent"},
    {"commandAssign", "assignment", "createsAssignment"}};

/* commandResolveParty kind displayName identifiers gives createsParty of
   makeParty kind displayName none identifiers attrsEnd none none. */
static int write_party_body(const Value *command, const Value **body, Failure *failure) {
  const Value *party;
  const Values *fields =
      values_item(write_field(text_of_cstring("kind"), command),
                  values_item(write_field(text_of_cstring("displayName"), command),
                              values_item(&null_value,
                                          values_item(write_field(text_of_cstring("identifiers"), command),
                                                      values_item(make_value((Value){.kind = VALUE_ATTRS}),
                                                                  values_item(&null_value,
                                                                              values_item(&null_value, NULL)))))));
  if (!write_value("Party", "makeParty", fields, &party, failure)) return 0;
  return write_value("Body", "createsParty", values_item(party, NULL), body, failure);
}

static int write_no_body(const Value **body) {
  *body = NULL;
  return 1;
}

/* The Body of the Command with the tag, from the row index on. body is
   NULL when the Command has no Body. */
static int write_command_body(const Value *command, Text tag, Nat index, const Value **body, Failure *failure) {
  if (index == 6 && same_text(tag, text_of_cstring("commandResolveParty")) == 1)
    return write_party_body(command, body, failure);
  if (index == 6) return write_no_body(body);
  if (same_text(tag, text_of_cstring(write_bodies[index][0])) != 1)
    return write_command_body(command, tag, index + 1, body, failure);
  return write_value("Body", write_bodies[index][2],
                     values_item(write_field(text_of_cstring(write_bodies[index][1]), command), NULL), body, failure);
}

/* makeStep log (outcome fields). */
/* The Step that write gives. Its copy gets written = 1, thus the projection
   reads its log (ruling R1). A Step from makeStep keeps written = 0. */
static int write_answer(const Value *log, const char *outcome, const Values *fields, const Value **value,
                        Failure *failure) {
  const Value *made;
  const Value *step;
  if (!write_value("Outcome", outcome, fields, &made, failure)) return 0;
  if (!write_value("Step", "makeStep", values_item(log, values_item(made, NULL)), &step, failure)) return 0;
  Value marked = *step;
  marked.written = 1;
  *value = make_value(marked);
  return 1;
}

static int write_denied(const Value *log, const Value **value, Failure *failure) {
  return write_answer(log, "outcomeDenied", values_item(&null_value, values_item(items_value(NULL), NULL)), value,
                      failure);
}

/* write log w (design items 7 and 8). The apply takes one work step. No
   Body, or an expect on an empty log: outcomeDenied none nil. An expect
   that is not the hash of the last entry: outcomeConflict with that hash.
   Else the new Entry goes at the end of the log, and its hash takes one
   more work step. The hash of the last entry takes no work step (delta
   B-5). */
int write_step(Fuel hash_fuel, Nat budget, Nat position, const Value *log, const Value *write, const Value **value,
               Nat *left, Failure *failure) {
  if (budget == 0) {
    *left = 0;
    return fail_at(failure, position, eBudget);
  }
  Nat ready = budget - 1;
  const Value *command = write_field(text_of_cstring("command"), write);
  const Value *expect = write_field(text_of_cstring("expect"), write);
  const Values *items = log->kind == VALUE_ITEMS ? log->items : NULL;
  const Value *last = write_last(items);
  const Value *body;
  if (!write_command_body(command, write_field(kSchemaTag(), command)->text, 0, &body, failure)) return 0;
  *left = ready;
  if (body == NULL) return write_denied(log, value, failure);
  if (last == NULL && expect->kind == VALUE_TEXT) return write_denied(log, value, failure);
  Text head = {NULL, 0};
  Nat unused;
  if (last != NULL && !entry_hash(hash_fuel, 1, position, last, &head, &unused, failure)) return 0;
  if (expect->kind == VALUE_TEXT && same_text(expect->text, head) != 1)
    return write_answer(log, "outcomeConflict", values_item(text_value(head), NULL), value, failure);
  const Value *entry;
  const Values *fields = values_item(last != NULL ? text_value(head) : &null_value,
                                     values_item(write_field(text_of_cstring("actor"), write), values_item(body, NULL)));
  if (!write_value("Entry", "makeEntry", fields, &entry, failure)) return 0;
  Text hash;
  if (!entry_hash(hash_fuel, ready, position, entry, &hash, left, failure)) return 0;
  return write_answer(items_value(append_values(items, values_item(entry, NULL))), "outcomeAppended",
                      values_item(items_value(values_item(text_value(hash), NULL)), values_item(&null_value, NULL)),
                      value, failure);
}

/* The builtin write on the token path (the model of pack_term). At the
   WritePath type the name is a function argument (the first test of
   partial_argument). Else the expected type is Step, then the log and the
   Write, as atoms. A wrong use gives eTerm. */
static int write_term(Fuel fuel, Nat budget, Nat atom, Nat position, const LType *expected,
                      const Bindings *environment, Tokens tokens, const Value **value, Tokens *rest, Nat *left,
                      const Term **term, Failure *failure) {
  if (fuel == 0) return 0;
  Fuel more = fuel - 1;
  const LType *path = write_path_type();
  if (same_type(expected, path) == 1)
    return with_term(worked_value(text_value(swrite), tokens, budget, value, rest, left), term,
                     term != NULL ? reference_term(position, swrite, environment) : NULL);
  if (same_type(expected, arrow_result(path)) != 1) return fail_at(failure, position, eTerm);
  if (atom == 1) return fail_at(failure, position, eParen);
  const Params *params = arrow_params(path);
  const Value *log;
  Tokens after;
  Nat spent;
  const Term *first = NULL;
  if (!parse_term(more, budget, 1, params->head.type, environment, tokens, &log, &after, &spent,
                  want_term(term, &first), failure))
    return 0;
  const Value *write;
  Tokens later;
  Nat used;
  const Term *second = NULL;
  if (!parse_term(more, spent, 1, params->tail->head.type, environment, after, &write, &later, &used,
                  want_term(term, &second), failure))
    return 0;
  const Value *step;
  Nat done;
  if (!write_step(OUTPUT_LIMIT, used, position, log, write, &step, &done, failure)) return 0;
  const Term *built = term != NULL ? named_term(TERM_CONSTRUCT, position, swrite, NULL,
                                                terms_item(first, terms_item(second, NULL)),
                                                taken_tokens(tokens, later), first_position(later), environment)
                                   : NULL;
  return with_term(worked_value(step, later, done, value, rest, left), term, built);
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
        if (proof_in_scope(item->name, item->type, environment) && same_declared_type(expected, item->type))
          return with_term(worked_value(item->value, tail, budget, value, rest, left), term,
                           term != NULL ? value_term(head.position, item, environment) : NULL);
        return fail_at(failure, head.position, eTerm);
      case BIND_FAMILY:
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
    if (same_text(head.text, spack))
      return pack_term(more, budget, atom, head.position, expected, environment, tail, value, rest, left, term,
                       failure);
    if (same_text(head.text, swrite))
      return write_term(more, budget, atom, head.position, expected, environment, tail, value, rest, left, term,
                        failure);
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
    const Term *built = term != NULL ? named_term(TERM_CONSTRUCT, head.position, head.text, NULL, args,
                                                  taken_tokens(tail, after), first_position(after), environment)
                                     : NULL;
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
   synth_term with a Term in place of the tokens. It uses the same helpers,
   the same fuel steps and the same work charges in the same order. An
   eval function gives 1 (a value), 0 with a code in failure (a failed
   answer) or 0 with no code (unknown) (D3-s5 part E, Q-S5-1). A failed
   answer is the failure of the token path: the same position and the same
   code. The caller gives it up and does not replay the tokens. The
   evaluator gives a failed answer for:
   - fuel 0 at the entry of a node, and budget 0 at a parse_term entry;
   - a fuel step in an argument list;
   - the token-path refusals that it mirrors (eTerm, eUnary, eStep, the
     constructor plan) and the failures of the shared helpers.
   It gives unknown, and the caller replays the tokens, when:
   - the budget is 0 at a node that is not a parse_term entry;
   - the expected type is an arrow and the argument is not a FUN, a
     PARTIAL, a NAME or a VAR (Q-S4-4; NAME and VAR from D3-s5 part D);
   - FOLD_VALUE or UNFOLD_VALUE has low fuel (D3-s3 part B2);
   - the token path fails at the node and the evaluator does not mirror
     the failure.
   A trial (the closure body term, the FOLD_VALUE f2 term) uses a local
   Failure, thus a failed trial writes no failure. */
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

/* The TERM_BODY of the body tokens before rest. end is the first token of
   rest: an application that ends the body has this Term.end (D8 part A). */
const Term *spanned_body(Tokens body, Tokens rest, const Term *callee) {
  Tokens span = taken_tokens(body, rest);
  return term_call(TERM_BODY, first_position(span), callee != NULL ? callee->cost : 0, span, first_position(rest),
                   (Text){NULL, 0}, callee, NULL, NULL);
}

/* The answer of a TERM_BODY (D8 part A). The token path runs on the body
   span. After the last argument of an application that ends the body, it
   gives eFuel at first_position of the empty rest (0). fuel_at_next gives
   eFuel at Term.end of that application, which is end of the TERM_BODY.
   Thus this failure moves to 0. */
static int body_answer(const Term *body, int worked, Failure *failure) {
  if (worked == 0 && body->end != 0 && failure->position == body->end && same_text(failure->message, eFuel) == 1)
    failure->position = 0;
  return worked;
}

/* The fuel step of an argument list: eFuel at the first token of the next
   argument (D3-s5 part E). next is the next argument of a bound list, or
   NULL. After the last argument: eFuel at end, the Term.end of the
   application (the first token after its argument list). body_answer moves
   it to 0 when the application ends the body (D8 part A). */
static int fuel_at_next(Failure *failure, const Terms *args, const Term *next, Nat end) {
  const Term *at = args != NULL ? args->head : next;
  return fail_at(failure, at != NULL ? at->position : end, eFuel);
}

/* parse_term with atom 1. A constructor name that now resolves to a
   function takes checked_synth and must be parenthesized. Keep the entry
   fuel and budget failures, including synth_term at fuel 0, in eval_term.
   A GROUP evaluates its inner term with atom 0. Arrow arguments retain
   the partial_argument path and the evaluator's existing replay rule. */
static int eval_argument(Fuel fuel, Nat budget, const LType *expected, const Bindings *environment,
                         const Term *term, const Value **value, Nat *left, Failure *failure) {
  const Binding *item;
  if (term != NULL && fuel > 1 && budget > 0 && term->tag == TERM_CONSTRUCT &&
      is_arrow_type(expected) != 1 && lookup(term->name, environment, &item) &&
      (item->kind == BIND_FUN || item->kind == BIND_CLOSURE)) {
    if (item->kind == BIND_CLOSURE &&
        (dependent_result(item->type) == 1 || dependent_params(item->params) == 1))
      return fail_at(failure, term->position, eTerm);
    return fail_at(failure, term->position, eParen);
  }
  return eval_term(fuel, budget, expected, environment, term, value, left, failure);
}

/* parse_arguments on the argument terms. */
static int eval_arguments(Fuel fuel, Nat budget, const LTypes *types, const Bindings *environment, const Terms *args,
                          const Values **values, Nat *left, const Term *next, Nat end, Failure *failure) {
  const Values *done = NULL;
  for (;; types = types->tail, args = args->tail) {
    /* parse_arguments: eFuel at the next argument. After the last argument:
       eFuel at end (fuel_at_next). */
    if (fuel == 0) return fuel_at_next(failure, args, next, end);
    fuel = fuel - 1;
    if (types == NULL) {
      if (args != NULL) return 0;
      *values = reverse_values_onto(NULL, done);
      *left = budget;
      return 1;
    }
    if (args == NULL) return 0;
    const Value *value;
    if (!eval_argument(fuel, budget, types->head, environment, args->head, &value, &budget, failure)) return 0;
    done = values_item(value, done);
  }
}

/* The tokens before the token at position. The tokens of a pack Term start
   at the witness, thus this is the witness span. */
static Tokens tokens_before(Tokens tokens, Nat position) {
  Nat size = 0;
  while (size < tokens.size && tokens.items[size].position != position) size = size + 1;
  return (Tokens){tokens.items, size};
}

/* pack_term on the pack Term (TERM_CONSTRUCT spack, args witness and
   payload; D8 part A). The same fuel steps, failures and budget. The side
   form of the witness comes from the witness span. At fuel 0 pack_term
   gives 0 with no failure; this gives the same answer. */
static int eval_pack(Fuel fuel, Nat budget, const LType *expected, const Bindings *environment, const Term *term,
                     const Value **value, Nat *left, Failure *failure) {
  if (fuel == 0) return 0;
  Fuel more = fuel - 1;
  if (expected->tag != TY_SIGMA) return fail_at(failure, term->position, eSigma);
  const Term *second = second_arg(term);
  const Value *witness;
  Nat spent;
  if (!eval_argument(more, budget, expected->left, environment, first_arg(term), &witness, &spent, failure)) return 0;
  Val side;
  Nat ready;
  Failure argued = {0, {NULL, 0}};
  if (second == NULL ||
      !argument_text(more, spent, environment, expected->left, witness, first_arg(term), &side, &ready, &argued))
    return side_failure(failure, argued, term->position, eTerm);
  const LType *b;
  Failure put = {0, {NULL, 0}};
  if (!put_marker(more, ready, environment, expected->right, expected->level, (Typed){expected->left, witness}, side,
                  &b, &spent, &put))
    return side_failure(failure, put, term->position, eSigma);
  const Value *payload;
  Nat used;
  if (!eval_argument(more, spent, b, environment, second, &payload, &used, failure)) return 0;
  return eval_worked(object_two(kWitness, witness, kPayload, payload), used, value, left);
}

/* write_term on the write Term (TERM_CONSTRUCT swrite, args log and Write).
   The same fuel steps, failures and budget. */
static int eval_write(Fuel fuel, Nat budget, const LType *expected, const Bindings *environment, const Term *term,
                      const Value **value, Nat *left, Failure *failure) {
  if (fuel == 0) return 0;
  Fuel more = fuel - 1;
  const LType *path = write_path_type();
  const Term *second = second_arg(term);
  if (same_type(expected, arrow_result(path)) != 1 || second == NULL) return fail_at(failure, term->position, eTerm);
  const Params *params = arrow_params(path);
  const Value *log;
  Nat spent;
  if (!eval_argument(more, budget, params->head.type, environment, first_arg(term), &log, &spent, failure)) return 0;
  const Value *write;
  Nat used;
  if (!eval_argument(more, spent, params->tail->head.type, environment, second, &write, &used, failure)) return 0;
  return write_step(OUTPUT_LIMIT, used, term->position, log, write, value, left, failure);
}

/* dependent_arguments on the argument terms. start is the argument span
   after the type arguments. instantiate_result reads the argument tokens
   on it with skip_atom, as on the token path (D3-s5 part C). If close_result
   gives 0, the answer is eTerm at the current argument, as on the token
   path (D3-s7 part D). D8 part B (Q-B5 (a), delta D-B4): instantiate_result
   also gets all of the argument terms, so a side comes from the checked term
   as on the check path. */
static int eval_dependent(Fuel fuel, Nat budget, const Bindings *chosen, const Bindings *environment,
                          const Params *params, const Params *remaining, const Values *seen, Tokens start,
                          const Terms *args, Nat end, const Values **values, Nat *left, Failure *failure) {
  const Params *specialized = side_params(chosen, params);
  const Terms *given = args;
  for (;; remaining = remaining->tail) {
    /* The dependent loop: eFuel at the next argument. After the last
       argument: eFuel at end, as in eval_arguments (fuel_at_next). */
    if (fuel == 0) return fuel_at_next(failure, args, NULL, end);
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
    Nat ready = budget;
    Failure closing = {0, {NULL, 0}};
    int resolved = instantiate_specialized(fuel, budget, environment, specialized, earlier, given, start, chosen,
                                           subst_type(chosen, head.type), &instantiated, &ready, &closing);
    const LType *expected;
    if (!close_result(fuel, ready, environment, params, earlier, resolved, instantiated, &expected, &budget, &closing))
      return side_failure(failure, closing, args->head->position, eTerm);
    const Value *value;
    if (!eval_argument(fuel, budget, expected, environment, args->head, &value, &budget, failure)) return 0;
    seen = values_item(value, seen);
    args = args->tail;
  }
}

/* synth_term on an application: fuel is the fuel of the callee step. If
   close_result gives 0, the answer is eTerm at the APPLY position, as in
   synth_term (D3-s7 part D). */
static int eval_apply(Fuel fuel, Nat budget, const Bindings *environment, const Term *term, Typed *typed, Nat *left, Failure *failure) {
  const Binding *item;
  if (!lookup(term->name, environment, &item)) return 0;
  switch (item->kind) {
  case BIND_VALUE:
  case BIND_FAMILY:
  case BIND_TYPE:
  case BIND_ARROW: return 0;
  case BIND_FUN: {
    /* type_arguments on the argument span with the fuel of the token path
       (D3-s5 part B). An empty span gives 0 for a callee with type params. */
    const Bindings *chosen;
    Tokens after_types;
    if (!type_arguments(fuel, budget, item->params, environment, NULL, term->tokens, &chosen, &after_types, NULL,
                        &budget, failure))
      return 0;
    const Values *values;
    Nat spent;
    if (!eval_dependent(fuel, budget, chosen, environment, item->params, item->params, NULL, after_types, term->args,
                        term->end, &values, &spent, failure))
      return 0;
    const LType *instantiated = NULL;
    Nat ready = spent;
    Failure closing = {0, {NULL, 0}};
    int resolved = instantiate_specialized(fuel, spent, environment, side_params(chosen, item->params), values,
                                           term->args, after_types, chosen, subst_type(chosen, item->type),
                                           &instantiated, &ready, &closing);
    const LType *applied;
    if (!close_result(fuel, ready, environment, item->params, values, resolved, instantiated, &applied, &spent,
                      &closing))
      return side_failure(failure, closing, term->position, eTerm);
    if (checking_body(environment) == 1) return eval_typed((Typed){applied, &null_value}, spent, typed, left);
    const Params *instantiated_params = instantiate_params(fuel, spent, environment, item->params, values, term->args,
                                                           after_types, item->params, &spent);
    const Params *closed;
    if (!close_params(fuel, spent, environment, item->params, values, instantiated_params, &closed, &spent, failure))
      return 0;
    const Bindings *scope = bind_arguments(environment, value_params(chosen, closed), values,
                                           type_frame(definition_scope(item->name, environment), chosen));
    const Value *value;
    Nat used;
    if (!eval_term(fuel, nat_sub(spent, 1), applied, scope, item->term, &value, &used, failure)) return 0;
    return eval_typed((Typed){applied, value}, used, typed, left);
  }
  case BIND_CLOSURE: {
    /* The token path gives eTerm for a dependent closure (D3-s5 part C, step
       C3). The evaluator gives the same failure (part E). */
    if (dependent_result(item->type) == 1 || dependent_params(item->params) == 1)
      return fail_at(failure, term->position, eTerm);
    /* The type arguments of a closure with a type parameter (step D7b), as
       for a function above. */
    const Bindings *chosen;
    Tokens after_types;
    if (!type_arguments(fuel, budget, item->params, environment, NULL, term->tokens, &chosen, &after_types, NULL,
                        &budget, failure))
      return 0;
    const Params *formal = closure_params(chosen, item->params);
    const LType *result = closure_result(chosen, item->type);
    const Values *values;
    Nat spent;
    if (!eval_arguments(fuel, budget, param_types(formal), environment, term->args, &values, &spent, NULL, term->end,
                        failure))
      return 0;
    if (checking_body(environment) == 1) return eval_typed((Typed){result, &null_value}, spent, typed, left);
    const Bindings *scope = bind_arguments(environment, formal, values, type_frame(item->scope, chosen));
    const Value *value;
    Nat used;
    /* The closure body Term only (D8 part A). An opaque closure has no term:
       the answer is the eTerm of an empty body, as on the token path. */
    if (item->term == NULL) return fail_at(failure, 0, eTerm);
    if (!eval_term(fuel, nat_sub(spent, 1), result, scope, item->term, &value, &used, failure)) return 0;
    return eval_typed((Typed){result, value}, used, typed, left);
  }
  }
  return 0;
}

static int apply_body(Fuel fuel, Nat budget, const LType *expected, const Bindings *environment, const Term *term,
                      const Value **value, Tokens *rest, Nat *left, Failure *failure);

static const Term *third_arg(const Term *term) {
  return term->args != NULL && term->args->tail != NULL && term->args->tail->tail != NULL
             ? term->args->tail->tail->head
             : NULL;
}

/* unary_argument on a name term. A function or a closure gives its body term
   (D3-s4). Dependent params do not change this, as on the token path
   (D3-s5 part C). */
static int eval_unary_argument(const Bindings *environment, const Term *term, Unary *op) {
  const Binding *item;
  if (term == NULL || !lookup(term->name, environment, &item)) return 0;
  return unary_checked(definition_scope(term->name, environment), item, op);
}

static int eval_partial_unary(Fuel fuel, Nat budget, const LType *wanted, const Bindings *environment,
                              const Term *term, Unary *op, Nat *left, Failure *failure);

/* unary_term on the head term of a keyword form. */
static int eval_unary(Fuel fuel, Nat budget, const LType *wanted, const Bindings *environment, const Term *term,
                      Unary *op, Nat *left, Failure *failure) {
  if (term == NULL) return 0;
  if (fuel == 0) return fail_at(failure, term->position, eFuel);
  Fuel more = fuel - 1;
  switch (term->tag) {
  case TERM_VAR:
  case TERM_NAME:
    if (!eval_unary_argument(environment, term, op)) return 0;
    *left = budget;
    return 1;
  case TERM_GROUP: return eval_partial_unary(more, budget, wanted, environment, first_arg(term), op, left, failure);
  case TERM_CLOSED:
  case TERM_NUMBER:
  case TERM_STRING:
  case TERM_APPLY:
  case TERM_PARTIAL:
  case TERM_FUN:
  case TERM_CONSTRUCT:
  case TERM_REFL:
  case TERM_FIRST:
  case TERM_SECOND:
  case TERM_WITNESS:
  case TERM_PAYLOAD:
  case TERM_SYMM:
  case TERM_TRANS:
  case TERM_CONG:
  case TERM_TRANSPORT:
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

/* inline_unary on a FUN term (D3-s5 part B). inline_binder reads the one
   binder on the binder span at fuel - 1, as on the token path. Then the body
   walk in check mode at fuel - 1. The walk makes no charge, thus its budget
   answer is not used. */
static int eval_inline_unary(Fuel fuel, Nat budget, const LType *wanted, const Bindings *environment,
                             const Term *term, Unary *op, Nat *left, Failure *failure) {
  Param binder;
  Tokens after_binder;
  Tokens body;
  Failure refused = {0, {NULL, 0}};
  if (fuel == 0 || budget == 0 || first_arg(term) == NULL || term->tokens.size < 2) return 0;
  /* inline_unary reads one binder with the tests of inline_binder: a refusal
     is the failure of the token path (D3-s8 U1). A span of one token is
     unknown: the token path gives eFun at the fun token. */
  if (!inline_binder(fuel - 1, budget, environment, NULL, term->tokens, &binder, &after_binder, &budget, &refused))
    return fail_at(failure, refused.position, refused.message);
  /* Two binders are unknown: the token path gives eFun at the second `(`. */
  if (!expect_mark(63, after_binder, &body, &refused)) return 0;
  const Value *checked;
  Nat spent;
  if (!eval_term(fuel - 1, budget, wanted,
                 slotted_item(value_binding(binder.name, binder.type, &null_value),
                              bindings_item(check_marker(), environment)),
                 first_arg(term), &checked, &spent, failure))
    return 0;
  *op = (Unary){binder.name, binder.type, wanted, environment, first_arg(term)};
  *left = budget;
  return 1;
}

/* 1 when partial_unary makes a bound_unary op from the binding. A function
   with dependent params gives 0: there the token path gives eUnary
   (partial_unary), eStep (partial_stepper) or eTerm (partial_argument).
   Part E makes these the failures (D3-s5 part C, step C4). */
static Nat partial_callee(const Binding *item) {
  switch (item->kind) {
  case BIND_VALUE:
  case BIND_FAMILY:
  case BIND_TYPE:
  case BIND_ARROW: return 0;
  case BIND_FUN: return dependent_params(item->params) == 1 ? 0 : 1;
  case BIND_CLOSURE: return 1;
  }
  return 0;
}

/* bound_unary on a PARTIAL term. type_arguments on the argument span gives
   the type arguments, and typed_bound keeps their tokens, as on the token
   path (D3-s5 part B). A function callee gives its body term in the closure
   scope; a closure callee keeps the body tokens. */
static int eval_bound_unary(Fuel fuel, Nat budget, const Bindings *environment, const Term *term, Unary *op,
                            Nat *left, Failure *failure) {
  const Binding *item;
  if (!lookup(term->name, environment, &item)) return 0;
  /* The callee is not a function, or it is a function with dependent params:
     the token path gives eUnary at the name (partial_unary, D3-s5 part E). */
  if (partial_callee(item) == 0) return fail_at(failure, term->position, eUnary);
  /* fuel 0: the fuel step of bound_unary. */
  if (fuel == 0) return fail_at(failure, term->position, eFuel);
  Fuel more = fuel - 1;
  const Bindings *chosen;
  Tokens after_types;
  if (!type_arguments(more, budget, item->params, environment, NULL, term->tokens, &chosen, &after_types, NULL,
                      &budget, failure))
    return 0;
  const Params *formal = value_params(chosen, item->params);
  const Params *front = front_params(formal);
  const Values *values;
  Nat spent;
  if (!eval_arguments(more, budget, param_types(front), environment, term->args, &values, &spent, NULL, term->end,
                      failure))
    return 0;
  if (bound_functions(front, values) == 0) return fail_at(failure, term->position, eTerm);
  /* Use locals, not a nested call. With the nested call, tcc on arm64 makes
     code that causes an invalid memory access. */
  const Values *bound = typed_bound(item->params, chosen, term->tokens, after_types, values);
  const LType *ty = arrow_type(drop_params(params_length(front), formal), subst_type(chosen, item->type));
  Binding closure = partial_closure(term->name, ty, term->name, bound, environment);
  if (!unary_checked(environment, &closure, op)) return fail_at(failure, term->position, eUnary);
  *left = spent;
  return 1;
}

/* partial_unary on the inner term of a GROUP head. */
static int eval_partial_unary(Fuel fuel, Nat budget, const LType *wanted, const Bindings *environment,
                              const Term *term, Unary *op, Nat *left, Failure *failure) {
  if (term == NULL) return 0;
  if (fuel == 0) return fail_at(failure, term->position, eFuel);
  Fuel more = fuel - 1;
  switch (term->tag) {
  case TERM_GROUP: return eval_unary(more, budget, wanted, environment, term, op, left, failure);
  case TERM_FUN: return eval_inline_unary(more, budget, wanted, environment, term, op, left, failure);
  case TERM_PARTIAL: return eval_bound_unary(more, budget, environment, term, op, left, failure);
  case TERM_CLOSED:
  case TERM_NUMBER:
  case TERM_STRING:
  case TERM_VAR:
  case TERM_NAME:
  case TERM_APPLY:
  case TERM_CONSTRUCT:
  case TERM_REFL:
  case TERM_FIRST:
  case TERM_SECOND:
  case TERM_WITNESS:
  case TERM_PAYLOAD:
  case TERM_SYMM:
  case TERM_TRANS:
  case TERM_CONG:
  case TERM_TRANSPORT:
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
                          const Term *term, const Value **value, Nat *left, Failure *failure) {
  if (fuel == 0 || shape_code(form, expected) == 0) return 0;
  Fuel more = fuel - 1;
  if (form == 1) {
    const Value *lifted;
    Nat spent;
    if (!eval_argument(more, budget, shape_element(expected), environment, first_arg(term), &lifted, &spent, failure)) return 0;
    return eval_worked(pure_value(expected, lifted), spent, value, left);
  }
  Unary op;
  Nat spent;
  if (!eval_unary(more, budget, structure_result(form, expected), environment, first_arg(term), &op, &spent, failure))
    return 0;
  if (structure_fits(form, expected, op) != 1) return 0;
  const Value *source;
  Nat used;
  if (!eval_argument(more, spent, structure_source(form, expected, op), environment, second_arg(term), &source, &used, failure))
    return 0;
  if (checking_body(environment) == 1) return eval_worked(&null_value, used, value, left);
  Tokens ignored;
  Failure refused = {0, {NULL, 0}};
  if (carrier_code(expected) == 2) {
    const Values *items;
    Nat mapped_left;
    if (!map_items(more, used, term->position, form, op, sequence_elements(source), &items, &ignored, &mapped_left,
                   failure))
      return 0;
    const Value *rebuilt;
    /* The refusal of rebuild at the node, as on the token path (D3-s8 U3). */
    if (!rebuild(expected, items, &rebuilt, &refused)) return fail_at(failure, term->position, refused.message);
    return eval_worked(rebuilt, mapped_left, value, left);
  }
  const Value *item;
  if (!payload_of(expected, unary_param(op), source, &item)) return eval_worked(source, used, value, left);
  const Value *applied;
  Nat applied_left;
  if (!apply_body(more, nat_sub(used, 1), unary_result(op), unary_environment(op, item), op.term,
                  &applied, &ignored, &applied_left, failure))
    return 0;
  return eval_worked(step_one(form, expected, source, applied), applied_left, value, left);
}

/* either_term on an EITHER term: fuel is the fuel of either_term. */
static int eval_either(Fuel fuel, Nat budget, const Bindings *environment, const Term *term, Typed *typed,
                       Nat *left, Failure *failure) {
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
  if (!eval_argument(more, budget, type_two(TY_SUM, unary_param(on_left), unary_param(on_right)), environment,
                 third_arg(term), &source, &spent, failure))
    return 0;
  if (checking_body(environment) == 1) return eval_typed((Typed){result, &null_value}, spent, typed, left);
  Unary chosen = sum_left(source) != 0 ? on_left : on_right;
  const Value *applied;
  Tokens ignored;
  Nat applied_left;
  if (!apply_body(more, nat_sub(spent, 1), result, unary_environment(chosen, project_value(1, source)),
                  chosen.term, &applied, &ignored, &applied_left, failure))
    return 0;
  return eval_typed((Typed){result, applied}, applied_left, typed, left);
}

static Nat terms_count(const Terms *terms) { return terms == NULL ? 0 : 1 + terms_count(terms->tail); }

static const Term *nth_term(const Terms *terms, Nat index) {
  if (terms == NULL) return NULL;
  if (index == 0) return terms->head;
  return nth_term(terms->tail, index - 1);
}

/* stepper_argument on a VAR or NAME head. A function or a closure gives its
   body term. Dependent params do not change this, as on the token path
   (D3-s5 part C). */
static int eval_stepper_argument(const Bindings *environment, const Term *term, Stepper *op) {
  const Binding *item;
  if (term == NULL || !lookup(term->name, environment, &item)) return 0;
  switch (item->kind) {
  case BIND_VALUE:
  case BIND_FAMILY:
  case BIND_TYPE:
  case BIND_ARROW: return 0;
  case BIND_FUN:
    if (has_type_param(item->params) == 1) return 0;
    *op = (Stepper){item->params, item->type, definition_scope(item->name, environment), item->term};
    return 1;
  case BIND_CLOSURE:
    *op = (Stepper){item->params, item->type, item->scope, item->term};
    return 1;
  }
  return 0;
}

static int eval_partial_stepper(Fuel fuel, Nat budget, Nat mode, const LType *expected, const Bindings *environment,
                                const Term *term, Stepper *op, Nat *left, Failure *failure);

/* stepper_term on the function term of fold or unfold. */
static int eval_stepper(Fuel fuel, Nat budget, Nat mode, const LType *expected, const Bindings *environment,
                        const Term *term, Stepper *op, Nat *left, Failure *failure) {
  if (term == NULL) return 0;
  if (fuel == 0) return fail_at(failure, term->position, eFuel);
  Fuel more = fuel - 1;
  switch (term->tag) {
  case TERM_VAR:
  case TERM_NAME:
    if (!eval_stepper_argument(environment, term, op)) return 0;
    *left = budget;
    return 1;
  case TERM_GROUP: return eval_partial_stepper(more, budget, mode, expected, environment, first_arg(term), op, left, failure);
  case TERM_CLOSED:
  case TERM_NUMBER:
  case TERM_STRING:
  case TERM_APPLY:
  case TERM_PARTIAL:
  case TERM_FUN:
  case TERM_CONSTRUCT:
  case TERM_REFL:
  case TERM_FIRST:
  case TERM_SECOND:
  case TERM_WITNESS:
  case TERM_PAYLOAD:
  case TERM_SYMM:
  case TERM_TRANS:
  case TERM_CONG:
  case TERM_TRANSPORT:
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

/* inline_stepper on a FUN term (D3-s5 part B): inline_binders on the binder
   span and the body walk in check mode, both at fuel - 1, as on the token
   path. The walk makes no charge, thus its budget answer is not used.
   Fuel 0 gives eFuel at the first token of the binder span, the token after
   `fun`, as on the token path (D3-s7 part B). There is no budget test: the
   token path has none, and eval_term on the body gives eBudget. The binder
   span stops at the body, and the token path does not. Thus a refusal at
   position 0 is at the end of the span, and it stays unknown. A refusal at a
   different position is in the span: it is the token path failure. A missing
   binder span at fuel 0 stays unknown: its first token is unavailable. */
static int eval_inline_stepper(Fuel fuel, Nat budget, Nat mode, const LType *expected, const Bindings *environment,
                               const Term *term, Stepper *op, Nat *left, Failure *failure) {
  if (fuel == 0)
    return term->tokens.size == 0 ? 0 : fail_at(failure, first_position(term->tokens), eFuel);
  const Params *params;
  Tokens body;
  Failure refused;
  if (first_arg(term) == NULL) return 0;
  if (!inline_binders(fuel - 1, budget, environment, NULL, term->tokens, &params, &body, &budget, &refused))
    return refused.position == 0 ? 0 : fail_at(failure, refused.position, refused.message);
  const LType *result = inline_result(mode, expected, params);
  const Value *checked;
  Nat spent;
  if (result == NULL ||
      !eval_term(fuel - 1, budget, result, bind_params(params, NULL, bindings_item(check_marker(), environment)),
                 first_arg(term), &checked, &spent, failure))
    return 0;
  *op = (Stepper){params, result, environment, first_arg(term)};
  *left = budget;
  return 1;
}

/* bound_arguments on the argument terms: one fuel step per parameter, then
   parse_arguments on one argument. */
static int eval_bound_arguments(Fuel fuel, Nat budget, const Params *params, const Bindings *environment,
                                const Terms *args, Nat end, const Values **values, Nat *left, Failure *failure) {
  /* fuel 0: the fuel step of bound_arguments, at the first token of the next
     argument. After the last argument: eFuel at end (fuel_at_next). */
  if (fuel == 0) return fuel_at_next(failure, args, NULL, end);
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
                      terms_item(args->head, NULL), &found, &spent, args->tail != NULL ? args->tail->head : NULL, end,
                      failure))
    return 0;
  const Values *later;
  Nat used;
  if (!eval_bound_arguments(more, spent, params->tail, environment, args->tail, end, &later, &used, failure)) return 0;
  *values = reverse_values_onto(later, reverse_values_onto(NULL, found));
  *left = used;
  return 1;
}

/* bound_stepper on a PARTIAL term. type_arguments on the argument span and
   typed_bound, as on the token path (D3-s5 part B). A function or a closure
   callee gives its body term in the closure scope (D3-s4). */
static int eval_bound_stepper(Fuel fuel, Nat budget, const Bindings *environment, const Term *term, Stepper *op,
                              Nat *left, Failure *failure) {
  const Binding *item;
  if (!lookup(term->name, environment, &item)) return 0;
  /* The callee is not a function, or it is a function with dependent params:
     the token path gives eStep at the name (partial_stepper, D3-s5 part E). */
  if (partial_callee(item) == 0) return fail_at(failure, term->position, eStep);
  /* fuel 0: the fuel step of bound_stepper. */
  if (fuel == 0) return fail_at(failure, term->position, eFuel);
  Fuel more = fuel - 1;
  const Bindings *chosen;
  Tokens after_types;
  if (!type_arguments(more, budget, item->params, environment, NULL, term->tokens, &chosen, &after_types, NULL,
                      &budget, failure))
    return 0;
  const Params *formal = value_params(chosen, item->params);
  const Params *front = take_params(terms_count(term->args), formal);
  const Values *values;
  Nat spent;
  if (!eval_bound_arguments(more, budget, front, environment, term->args, term->end, &values, &spent, failure)) return 0;
  if (bound_functions(front, values) == 0) return fail_at(failure, term->position, eTerm);
  /* Use locals, not a nested call, as in eval_bound_unary (tcc on arm64). */
  const Values *bound = typed_bound(item->params, chosen, term->tokens, after_types, values);
  const LType *ty = arrow_type(drop_params(params_length(front), formal), subst_type(chosen, item->type));
  Binding made = partial_closure(term->name, ty, term->name, bound, environment);
  const Term *body = made.term;
  switch (made.kind) {
  case BIND_VALUE:
  case BIND_FAMILY:
  case BIND_TYPE:
  case BIND_ARROW: return fail_at(failure, term->position, eStep);
  case BIND_FUN:
    *op = (Stepper){made.params, made.type, definition_scope(made.name, environment), body};
    break;
  case BIND_CLOSURE: *op = (Stepper){made.params, made.type, made.scope, body}; break;
  }
  *left = spent;
  return 1;
}

/* partial_stepper on the inner term of a GROUP head. */
static int eval_partial_stepper(Fuel fuel, Nat budget, Nat mode, const LType *expected, const Bindings *environment,
                                const Term *term, Stepper *op, Nat *left, Failure *failure) {
  if (term == NULL) return 0;
  if (fuel == 0) return fail_at(failure, term->position, eFuel);
  Fuel more = fuel - 1;
  switch (term->tag) {
  case TERM_GROUP: return eval_stepper(more, budget, mode, expected, environment, term, op, left, failure);
  case TERM_FUN: return eval_inline_stepper(more, budget, mode, expected, environment, term, op, left, failure);
  case TERM_PARTIAL: return eval_bound_stepper(more, budget, environment, term, op, left, failure);
  case TERM_CLOSED:
  case TERM_NUMBER:
  case TERM_STRING:
  case TERM_VAR:
  case TERM_NAME:
  case TERM_APPLY:
  case TERM_CONSTRUCT:
  case TERM_REFL:
  case TERM_FIRST:
  case TERM_SECOND:
  case TERM_WITNESS:
  case TERM_PAYLOAD:
  case TERM_SYMM:
  case TERM_TRANS:
  case TERM_CONG:
  case TERM_TRANSPORT:
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
                     const Value **value, Nat *left, Failure *failure) {
  if (fuel == 0) return fail_at(failure, term->position, eFuel);
  Fuel more = fuel - 1;
  Stepper op;
  Nat spent;
  if (!eval_stepper(more, budget, 0, expected, environment, first_arg(term), &op, &spent, failure)) return 0;
  const Value *start;
  Nat used;
  if (!eval_argument(more, spent, expected, environment, second_arg(term), &start, &used, failure)) return 0;
  Typed found;
  Nat found_left;
  if (!eval_synth(more, used, environment, third_arg(term), &found, &found_left, failure)) return 0;
  if (carrier_code(found.type) == 0 || fold_fits(found.type, expected, op) != 1) return 0;
  if (checking_body(environment) == 1) return eval_worked(&null_value, found_left, value, left);
  const Values *items;
  if (!elements_of(more, found.value, &items)) return 0;
  const Value *result;
  Tokens ignored;
  Nat folded_left;
  if (!fold_items(more, found_left, term->position, op, carrier_code(found.type), items, start, &result, &ignored,
                  &folded_left, failure))
    return 0;
  return eval_worked(result, folded_left, value, left);
}

/* algebra_term on one of f2 to f5 of a FOLD_VALUE term. */
static int eval_algebra_term(Fuel fuel, Nat budget, Nat index, const LType *result, const Bindings *environment,
                             const Term *term, Stepper *op, Nat *left, Failure *failure) {
  if (term == NULL) return 0;
  if (fuel == 0) return fail_at(failure, term->position, eFuel);
  Stepper found;
  Nat spent;
  if (!eval_stepper(fuel - 1, budget, 0, result, environment, term, &found, &spent, failure)) return 0;
  if (same_type(stepper_result(found), result) == 0 ||
      same_types(param_types(stepper_params(found)), types_item(algebra_param(index, result), NULL)) == 0)
    return 0;
  *op = found;
  *left = spent;
  return 1;
}

/* algebra_terms on [f2, f3, f4, f5, ...] of a FOLD_VALUE term. */
static int eval_algebra_terms(Fuel fuel, Nat budget, const LType *result, Stepper on_nat,
                              const Bindings *environment, const Terms *terms, ValueAlgebra *ops, Nat *left, Failure *failure) {
  if (fuel == 0) return 0;
  Fuel more = fuel - 1;
  Stepper on_flag, on_text, on_items, on_attrs;
  Nat flag_left, text_left, items_left, attrs_left;
  if (!eval_algebra_term(more, budget, 2, result, environment, nth_term(terms, 0), &on_flag, &flag_left, failure) ||
      !eval_algebra_term(more, flag_left, 3, result, environment, nth_term(terms, 1), &on_text, &text_left, failure) ||
      !eval_algebra_term(more, text_left, 4, result, environment, nth_term(terms, 2), &on_items, &items_left, failure) ||
      !eval_algebra_term(more, items_left, 5, result, environment, nth_term(terms, 3), &on_attrs, &attrs_left, failure))
    return 0;
  *ops = (ValueAlgebra){on_nat, on_flag, on_text, on_items, on_attrs};
  *left = attrs_left;
  return 1;
}

/* fold_term on a FOLD_VALUE term [f1, f2, f3, f4, f5, start, source]: fuel
   is the fuel of fold_term. The token path selects FOLD_VALUE with
   second_function, a trial parse of f2 at fuel - 2. The evaluator runs that
   trial first. A failed trial runs fold_tail on the span after f1, a local
   token fallback as the closure body (Q-S4-3), and an empty span gives 0
   (D3-s6 part B). Then the steps of fold_value_term at fuel - 1. */
static int eval_fold_value(Fuel fuel, Nat budget, const LType *expected, const Bindings *environment,
                           const Term *term, const Value **value, Nat *left, Failure *failure) {
  if (fuel == 0) return fail_at(failure, term->position, eFuel);
  Fuel more = fuel - 1;
  const Term *function = first_arg(term);
  Stepper on_nat;
  Nat spent;
  if (!eval_stepper(more, budget, 0, expected, environment, function, &on_nat, &spent, failure)) return 0;
  Fuel inner = more - 1;
  Stepper trial;
  Nat trial_left;
  /* A trial: a failed trial writes no failure (D3-s5 part E). */
  Failure tried = {0, {NULL, 0}};
  if (!eval_algebra_term(inner, spent, 2, expected, environment, second_arg(term), &trial, &trial_left, &tried)) {
    Tokens ignored;
    return term->tokens.size != 0 && fold_tail(more, spent, term->position, function->position, expected, on_nat,
                                               environment, term->tokens, NULL, value, &ignored, left, NULL, failure);
  }
  if (same_type(stepper_result(on_nat), expected) != 1 ||
      same_types(param_types(stepper_params(on_nat)), types_item(&nat_type, NULL)) != 1)
    return 0;
  ValueAlgebra ops;
  Nat functions_left;
  if (!eval_algebra_terms(inner, spent, expected, on_nat, environment, term->args->tail, &ops, &functions_left, failure))
    return 0;
  const Value *start;
  Nat used;
  if (!eval_argument(inner, functions_left, expected, environment, nth_term(term->args, 5), &start, &used, failure)) return 0;
  Typed found;
  Nat found_left;
  if (!eval_synth(inner, used, environment, nth_term(term->args, 6), &found, &found_left, failure)) return 0;
  if (same_type(found.type, &value_type) != 1) return 0;
  if (checking_body(environment) == 1) return eval_worked(&null_value, found_left, value, left);
  const Value *result;
  Tokens ignored;
  Nat folded_left;
  if (!fold_value(inner, found_left, term->position, ops, start, found.value, &result, &ignored, &folded_left,
                  failure))
    return 0;
  return eval_worked(result, folded_left, value, left);
}

/* unfold_term on an UNFOLD term [g, n, seed]: fuel is the fuel of
   unfold_term. */
static int eval_unfold(Fuel fuel, Nat budget, const LType *expected, const Bindings *environment, const Term *term,
                       const Value **value, Nat *left, Failure *failure) {
  if (fuel == 0 || carrier_code(expected) == 0) return 0;
  Fuel more = fuel - 1;
  Stepper op;
  Nat spent;
  if (!eval_stepper(more, budget, 1, expected, environment, first_arg(term), &op, &spent, failure)) return 0;
  if (unfold_fits(expected, op) != 1) return 0;
  const Value *limit;
  Nat limit_left;
  if (!eval_argument(more, spent, &nat_type, environment, second_arg(term), &limit, &limit_left, failure)) return 0;
  const Value *seed;
  Nat seed_left;
  if (!eval_argument(more, limit_left, unfold_seed(op), environment, third_arg(term), &seed, &seed_left, failure)) return 0;
  if (checking_body(environment) == 1) return eval_worked(&null_value, seed_left, value, left);
  const Values *items;
  Tokens ignored;
  Nat built_left;
  Failure refused = {0, {NULL, 0}};
  if (!unfold_items(more, seed_left, term->position, op, carrier_code(expected), count_of(limit), seed, &items,
                    &ignored, &built_left, failure))
    return 0;
  const Value *rebuilt;
  /* The refusal of rebuild at the node, as on the token path (D3-s8 U3). */
  if (!rebuild(expected, items, &rebuilt, &refused)) return fail_at(failure, term->position, refused.message);
  return eval_worked(rebuilt, built_left, value, left);
}

/* unfold_term on an UNFOLD_VALUE term [g, n, seed]: fuel is the fuel of
   unfold_term, which calls unfold_value_term at fuel - 1. The fuel tests of
   the two and of stepper_term, step for step (D3-s6 part B). The type test
   stays: the token path selects UNFOLD_VALUE by the same test. */
static int eval_unfold_value(Fuel fuel, Nat budget, const LType *expected, const Bindings *environment,
                             const Term *term, const Value **value, Nat *left, Failure *failure) {
  if (carrier_code(expected) != 0 || same_type(expected, &value_type) != 1) return 0;
  /* unfold_term at fuel 0, then unfold_value_term at fuel 0: eFuel at the
     position of the keyword. */
  if (fuel <= 1) return fail_at(failure, term->position, eFuel);
  Fuel more = fuel - 2;
  const Term *function = first_arg(term);
  Stepper op;
  Nat spent;
  if (!eval_stepper(more, budget, 2, &value_type, environment, function, &op, &spent, failure)) return 0;
  if (unfold_value_fits(op) != 1) return 0;
  const Value *limit;
  Nat limit_left;
  if (!eval_argument(more, spent, &nat_type, environment, second_arg(term), &limit, &limit_left, failure)) return 0;
  const Value *seed;
  Nat seed_left;
  if (!eval_argument(more, limit_left, unfold_seed(op), environment, third_arg(term), &seed, &seed_left, failure)) return 0;
  if (checking_body(environment) == 1) return eval_worked(&null_value, seed_left, value, left);
  Grown node;
  Tokens ignored;
  Nat built_left;
  if (!unfold_node(more, seed_left, term->position, op, count_of(limit), seed, &node, &ignored, &built_left,
                   failure))
    return 0;
  return eval_worked(grown_head(node), built_left, value, left);
}

int eval_synth(Fuel fuel, Nat budget, const Bindings *environment, const Term *term, Typed *typed, Nat *left, Failure *failure) {
  /* synth_term: eFuel at fuel 0. It has no budget test, thus budget 0 gives
     unknown (D3-s5 part E). */
  if (term == NULL) return 0;
  if (fuel == 0) return fail_at(failure, term->position, eFuel);
  if (budget == 0) return 0;
  Fuel more = fuel - 1;
  Typed found;
  Nat spent;
  Tokens rest;
  switch (term->tag) {
  case TERM_GROUP: return eval_synth(more, budget, environment, first_arg(term), typed, left, failure);
  case TERM_CLOSED: return eval_typed(*term->closed, budget, typed, left);
  case TERM_VAR:
  case TERM_NAME: {
    const Binding *item;
    if (!lookup(term->name, environment, &item) || item->kind != BIND_VALUE) return 0;
    if (!proof_in_scope(item->name, item->type, environment)) return 0;
    return eval_typed((Typed){item->type, item->value}, budget, typed, left);
  }
  case TERM_APPLY: return eval_apply(more, budget, environment, term, typed, left, failure);
  case TERM_FIRST:
  case TERM_SECOND:
    if (!eval_synth(more, budget, environment, first_arg(term), &found, &spent, failure)) return 0;
    return lift_parsed(spent,
                       project(term->position, term->tag == TERM_FIRST ? 1 : 2, found, no_tokens, typed, &rest,
                               failure),
                       left);
  case TERM_WITNESS:
  case TERM_PAYLOAD:
    if (!eval_synth(more, budget, environment, first_arg(term), &found, &spent, failure)) return 0;
    return project_sigma(more, spent, environment, term->position, term->tag == TERM_WITNESS ? 1 : 2, found, NULL,
                         no_tokens, typed, &rest, left, failure);
  case TERM_SYMM:
    if (!eval_synth(more, budget, environment, first_arg(term), &found, &spent, failure)) return 0;
    return lift_parsed(spent, symm_proof(term->position, found, no_tokens, typed, &rest, failure), left);
  case TERM_CONG: {
    const Term *name = first_arg(term);
    const Binding *function;
    if (!cong_function(name->position, name->name, environment, &function, failure)) return 0;
    if (!eval_synth(more, budget, environment, second_arg(term), &found, &spent, failure)) return 0;
    return cong_proof(more, spent, environment, term->position, function, found, no_tokens, typed, &rest, left,
                      failure);
  }
  case TERM_TRANSPORT: {
    /* D6 part B (design items 8 and 9): one path for a neutral and a closed
       e. The value is the value of t. */
    if (term->types == NULL) return 0;
    /* D8 part C (design item 13): the motive is the LType of the check. Put
       the type and value arguments of this application scope in it. */
    const LType *motive;
    Nat ready;
    if (!application_motive(more, budget, environment, term->position, term->types->head.type, &motive, &ready,
                            failure))
      return 0;
    const LType *bx, *by;
    if (!eval_synth(more, ready, environment, first_arg(term), &found, &spent, failure) ||
        !transport_types(more, spent, term->types->head.scope != NULL ? term->types->head.scope : environment,
                         term->position, motive, found, &bx, &by, &spent, failure))
      return 0;
    const Value *value;
    Nat used;
    if (!eval_term(more, spent, bx, environment, second_arg(term), &value, &used, failure)) return 0;
    return eval_typed((Typed){by, value}, used, typed, left);
  }
  case TERM_TRANS: {
    if (!eval_synth(more, budget, environment, first_arg(term), &found, &spent, failure)) return 0;
    Typed other;
    Nat used;
    if (!eval_synth(more, spent, environment, second_arg(term), &other, &used, failure)) return 0;
    return lift_parsed(used, trans_proof(term->position, found, other, no_tokens, typed, &rest, failure), left);
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
  case TERM_EITHER: return eval_either(more, budget, environment, term, typed, left, failure);
  /* A TERM_BODY takes no fuel step and no charge (the token path has no node for it). */
  case TERM_BODY:
    return body_answer(term, eval_synth(fuel, budget, environment, term->callee, typed, left, failure), failure);
  }
  return 0;
}

/* 1 for the tags that eval_term takes at an arrow expected type: a FUN, a
   PARTIAL, a NAME or a VAR argument and the GROUP around it (the atom
   rule). NAME and VAR give 1 from D3-s5 part D (Q-S5-4). */
static Nat arrow_tag(const Term *term) {
  switch (term->tag) {
  case TERM_GROUP:
  case TERM_FUN:
  case TERM_PARTIAL:
  case TERM_VAR:
  case TERM_NAME: return 1;
  case TERM_NUMBER:
  case TERM_STRING:
  case TERM_CLOSED:
  case TERM_APPLY:
  case TERM_CONSTRUCT:
  case TERM_REFL:
  case TERM_FIRST:
  case TERM_SECOND:
  case TERM_WITNESS:
  case TERM_PAYLOAD:
  case TERM_SYMM:
  case TERM_TRANS:
  case TERM_CONG:
  case TERM_TRANSPORT:
  case TERM_EITHER:
  case TERM_PURE:
  case TERM_MAP:
  case TERM_BIND:
  case TERM_FILTER:
  case TERM_FOLD:
  case TERM_FOLD_VALUE:
  case TERM_UNFOLD:
  case TERM_UNFOLD_VALUE: return 0;
  /* A body Term takes the tag of its callee: apply_body runs eval_term on it
     with no token path (D8 part A). */
  case TERM_BODY: return term->callee != NULL ? arrow_tag(term->callee) : 0;
  }
  return 0;
}

/* inline_argument on a FUN term: inline_binders on the binder span at
   fuel - 1, as on the token path (D3-s5 part B). The body walk is in check
   mode with its charge. The Value keeps the TERM_BODY of the FUN node. */
static int eval_inline_argument(Fuel fuel, Nat budget, const LType *expected, const Bindings *environment,
                                const Term *term, const Value **value, Nat *left, Failure *failure) {
  /* inline_argument: eFuel at fuel 0 (D3-s5 part E). */
  if (fuel == 0) return fail_at(failure, term->position, eFuel);
  Fuel more = fuel - 1;
  const Term *body = first_arg(term);
  const Params *params;
  Tokens binder_rest;
  Failure refused = {0, {NULL, 0}};
  if (body == NULL || body->tag != TERM_BODY) return 0;
  /* inline_argument: the refusal of inline_binders at fuel - 1 (D3-s8 U2). */
  if (!inline_binders(more, budget, environment, NULL, term->tokens, &params, &binder_rest, &budget, &refused))
    return fail_at(failure, refused.position, refused.message);
  /* inline_argument: eTerm when the binders do not give the type (D3-s5 part E). */
  if (same_type(expected, arrow_type(params, arrow_result(expected))) != 1) return fail_at(failure, term->position, eTerm);
  const Value *checked;
  Nat spent;
  if (!eval_term(more, budget, arrow_result(expected),
                 bind_params(params, NULL, bindings_item(check_marker(), environment)), body, &checked, &spent, failure))
    return 0;
  return eval_worked(inline_value(params, term_tokens(body), body), spent, value, left);
}

/* partial_argument and prefix_argument on a PARTIAL term: one fuel step
   each, then eval_arguments (parse_arguments in mode 1). */
static int eval_partial_argument(Fuel fuel, Nat budget, const LType *expected, const Bindings *environment,
                                 const Term *term, const Value **value, Nat *left, Failure *failure) {
  /* fuel 0: the fuel step of partial_argument (D3-s5 part E). */
  if (fuel == 0) return fail_at(failure, term->position, eFuel);
  const Binding *item;
  if (!lookup(term->name, environment, &item) || (item->kind != BIND_FUN && item->kind != BIND_CLOSURE)) return 0;
  const Params *params = item->params;
  /* A callee of the expected type: the token path gives a NAME, not a
     PARTIAL. */
  if (same_type(expected, arrow_type(params, item->type)) == 1) return 0;
  /* A dependent callee: the token path gives eTerm at the name
     (partial_argument, D3-s5 parts C and E). */
  if (dependent_result(item->type) == 1 || dependent_params(params) == 1)
    return fail_at(failure, term->position, eTerm);
  /* A type-param callee: type_arguments on the argument span at fuel - 1,
     then typed_bound, as partial_argument does (D3-s5 part B). */
  const Bindings *chosen;
  Tokens after_types;
  if (!type_arguments(fuel - 1, budget, params, environment, NULL, term->tokens, &chosen, &after_types, NULL, &budget,
                      failure))
    return 0;
  /* fuel 1: the fuel step of prefix_argument, after type_arguments. */
  if (fuel == 1) return fail_at(failure, term->position, eFuel);
  Nat typed = has_type_param(params);
  const Params *formal = typed == 1 ? value_params(chosen, params) : params;
  const LType *result = typed == 1 ? subst_type(chosen, item->type) : item->type;
  const Params *bound = bound_params(formal, arrow_params(expected));
  Nat same = same_type(expected, arrow_type(drop_params(params_length(bound), formal), result));
  if (same == 0) return fail_at(failure, term->position, eTerm);
  if (same != 1) return 0;
  const Values *values;
  Nat spent;
  if (!eval_arguments(fuel - 2, budget, param_types(bound), environment, term->args, &values, &spent, NULL, term->end,
                      failure))
    return 0;
  if (bound_functions(bound, values) == 0) return fail_at(failure, term->position, eTerm);
  const Values *kept = typed_bound(params, chosen, term->tokens, after_types, values);
  return eval_worked(make_value((Value){.kind = VALUE_ITEMS, .items = values_item(text_value(term->name), kept)}),
                     spent, value, left);
}

static int var_binding(const Term *term, const Bindings *environment, const Binding **found);

/* The name branch of parse_term at an arrow expected type (D3-s5 part D):
   lookup, then the Binding kind. A BIND_FUN or a BIND_CLOSURE goes to
   partial_argument at fuel - 1. Its first test gives the name as a text
   Value when the type is the same. The token path builds a NAME or a VAR
   node only for that test. A BIND_VALUE gives its Value, as in parse_term.
   Each other answer gives 0. A TERM_VAR finds its item by slot, as in
   eval_term (var_binding, D3-s7 part C). A TERM_NAME keeps lookup. */
static int eval_name_argument(Fuel fuel, Nat budget, const LType *expected, const Bindings *environment,
                              const Term *term, const Value **value, Nat *left, Failure *failure) {
  const Binding *item;
  int found = term->tag == TERM_VAR ? var_binding(term, environment, &item) : lookup(term->name, environment, &item);
  /* The builtin write at the WritePath type (M1 part B, delta B-3). */
  if (!found)
    return term->tag == TERM_NAME && same_text(term->name, swrite) == 1 &&
                   same_type(expected, write_path_type()) == 1
               ? eval_worked(text_value(swrite), budget, value, left)
               : 0;
  switch (item->kind) {
  case BIND_VALUE:
    /* The test of the token path: eTerm at the name (D3-s8 U5). */
    if (!proof_in_scope(item->name, item->type, environment) || same_declared_type(expected, item->type) != 1)
      return fail_at(failure, term->position, eTerm);
    return eval_worked(item->value, budget, value, left);
  case BIND_FAMILY:
  case BIND_TYPE:
  case BIND_ARROW: return fail_at(failure, term->position, eTerm);
  case BIND_FUN:
  case BIND_CLOSURE:
    /* partial_argument: eFuel at fuel 0 (D3-s5 part E). */
    if (fuel == 0) return fail_at(failure, term->position, eFuel);
    if (same_type(expected, arrow_type(item->params, item->type)) != 1) return 0;
    return eval_worked(text_value(term->name), budget, value, left);
  }
  return 0;
}

/* TERM_CONSTRUCT when lookup finds the name in the run-time scope: the
   mirror of the name branch of the token path (D3-s6 part A). BIND_VALUE
   with no arguments is the TERM_VAR arm. BIND_VALUE with arguments is
   unknown: the token path takes the value and leaves the arguments in rest,
   and the term has no node for that state. BIND_FUN and BIND_CLOSURE give
   the TERM_APPLY arm on an APPLY view of the node, at the same fuel. There
   is no PARTIAL view: eval_term gives 0 for TERM_CONSTRUCT at an arrow type
   before the switch. */
static int eval_construct_name(Fuel fuel, Nat budget, const LType *expected, const Bindings *environment,
                               const Term *term, const Binding *item, const Value **value, Nat *left,
                               Failure *failure) {
  switch (item->kind) {
  case BIND_VALUE:
    if (term->args != NULL) return 0;
    /* The test of the token path: eTerm at the name (D3-s8 U5). */
    if (!proof_in_scope(item->name, item->type, environment) || same_declared_type(expected, item->type) != 1)
      return fail_at(failure, term->position, eTerm);
    return eval_worked(item->value, budget, value, left);
  case BIND_FAMILY:
  case BIND_TYPE:
  case BIND_ARROW: return fail_at(failure, term->position, eTerm);
  case BIND_FUN:
  case BIND_CLOSURE: {
    /* An empty constructor argument span omits the following token. A
       missing type argument must replay to locate its error there. */
    if (item->kind == BIND_FUN && item->params != NULL && is_type_param(item->params->head) == 1 &&
        term->tokens.size == 0)
      return 0;
    /* An arena node, not a stack copy: a closure Value borrows its term. */
    const Term *view = term_call(TERM_APPLY, term->position, term->cost, term->tokens, term->end, term->name, NULL,
                                 term->types, term->args);
    return eval_term(fuel, budget, expected, environment, view, value, left, failure);
  }
  }
  return 0;
}

static Nat slot_misses = 0;

Nat slot_mismatches(void) { return slot_misses; }

/* TERM_VAR by slot (D3-s6 part C): the first item with the slot index + 1,
   then one name compare. No such item, or a different name, looks the name
   up (the local fallback) and counts a mismatch. The C test asserts 0. */
static int var_binding(const Term *term, const Bindings *environment, const Binding **found) {
  for (const Bindings *at = environment; at != NULL; at = at->tail)
    if (at->head.slot == term->index + 1) {
      if (same_text(term->name, at->head.name) != 1) break;
      *found = &at->head;
      return 1;
    }
  slot_misses = slot_misses + 1;
  return lookup(term->name, environment, found);
}

int eval_term(Fuel fuel, Nat budget, const LType *expected, const Bindings *environment, const Term *term,
              const Value **value, Nat *left, Failure *failure) {
  /* fuel 0 and budget 0: the failures of the parse_term entry (D3-s5 part E). */
  if (term == NULL) return 0;
  if (fuel == 0) return fail_at(failure, term->position, eFuel);
  if (budget == 0) return fail_at(failure, term->position, eBudget);
  if (is_arrow_type(expected) == 1 && arrow_tag(term) == 0) return 0;
  Fuel more = fuel - 1;
  Tokens rest;
  Failure refused;
  switch (term->tag) {
  case TERM_NUMBER:
    return same_type(expected, &nat_type) == 1 && eval_worked(nat_value(term->number), budget, value, left);
  case TERM_STRING:
    return same_type(expected, &text_type) == 1 && eval_worked(text_value(term->name), budget, value, left);
  case TERM_CLOSED:
    if (!same_declared_type(expected, term->closed->type)) return fail_at(failure, term->position, eTerm);
    return eval_worked(term->closed->value, budget, value, left);
  case TERM_GROUP: return eval_term(more, budget, expected, environment, first_arg(term), value, left, failure);
  case TERM_VAR:
  case TERM_NAME: {
    if (is_arrow_type(expected) == 1) return eval_name_argument(more, budget, expected, environment, term, value, left, failure);
    const Binding *item;
    int found = term->tag == TERM_VAR ? var_binding(term, environment, &item) : lookup(term->name, environment, &item);
    if (!found || item->kind != BIND_VALUE) return 0;
    /* The test of the token path: eTerm at the name (D3-s8 U5). */
    if (!proof_in_scope(item->name, item->type, environment) || same_declared_type(expected, item->type) != 1)
      return fail_at(failure, term->position, eTerm);
    return eval_worked(item->value, budget, value, left);
  }
  case TERM_CONSTRUCT: {
    const Binding *item;
    Plan selected;
    /* A name of the run-time scope takes the name branch (D3-s6 part A). */
    if (lookup(term->name, environment, &item))
      return eval_construct_name(fuel, budget, expected, environment, term, item, value, left, failure);
    /* pack: the order of parse_term (pack_term before constructor_plan). */
    if (same_text(term->name, spack)) return eval_pack(more, budget, expected, environment, term, value, left, failure);
    if (same_text(term->name, swrite)) return eval_write(more, budget, expected, environment, term, value, left, failure);
    if (!constructor_plan(expected, term->name, &selected)) return 0;
    const Values *values;
    Nat spent;
    if (!eval_arguments(more, budget, plan_arguments(&selected), environment, term->args, &values, &spent, NULL,
                        term->end, failure))
      return 0;
    const Value *made;
    Failure planned = {0, {NULL, 0}};
    if (evaluate_plan(&selected, values, &made, &planned)) return eval_worked(made, spent, value, left);
    if (checking_body(environment) == 1) return eval_worked(&null_value, spent, value, left);
    /* The failure of the token path at the constructor name (F5, D3-s5
       part E). An empty message is unknown. */
    return fail_at(failure, term->position, planned.message);
  }
  case TERM_REFL:
    return lift_parsed(budget, refl_check(term->position, expected, no_tokens, value, &rest, failure), left);
  case TERM_APPLY:
  case TERM_FIRST:
  case TERM_SECOND:
  case TERM_WITNESS:
  case TERM_PAYLOAD:
  case TERM_SYMM:
  case TERM_TRANS:
  case TERM_CONG:
  case TERM_TRANSPORT:
  case TERM_EITHER: {
    /* checked_synth: synth_term at fuel - 1, then the check of the type. */
    Typed found;
    Nat spent;
    if (!eval_synth(more, budget, environment, term, &found, &spent, failure)) return 0;
    return check_worked(term->position, expected, found, no_tokens, spent, value, &rest, left, &refused);
  }
  case TERM_PURE: return eval_structure(more, budget, 1, expected, environment, term, value, left, failure);
  case TERM_MAP: return eval_structure(more, budget, 2, expected, environment, term, value, left, failure);
  case TERM_BIND: return eval_structure(more, budget, 3, expected, environment, term, value, left, failure);
  case TERM_FILTER: return eval_structure(more, budget, 4, expected, environment, term, value, left, failure);
  case TERM_FOLD: return eval_fold(more, budget, expected, environment, term, value, left, failure);
  case TERM_FOLD_VALUE: return eval_fold_value(more, budget, expected, environment, term, value, left, failure);
  case TERM_UNFOLD: return eval_unfold(more, budget, expected, environment, term, value, left, failure);
  case TERM_UNFOLD_VALUE: return eval_unfold_value(more, budget, expected, environment, term, value, left, failure);
  case TERM_PARTIAL:
    return is_arrow_type(expected) == 1 && eval_partial_argument(more, budget, expected, environment, term, value, left, failure);
  case TERM_FUN:
    return is_arrow_type(expected) == 1 && eval_inline_argument(more, budget, expected, environment, term, value, left, failure);
  /* A TERM_BODY takes no fuel step and no charge (the token path has no node for it). */
  case TERM_BODY:
    return body_answer(term, eval_term(fuel, budget, expected, environment, term->callee, value, left, failure),
                       failure);
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
    return prefix_argument(more, budget, atom, position, expected, name, params, params, result, NULL, environment, tokens,
                           tokens, value, rest, left, term, failure);
  if (atom == 1) return fail_at(failure, position, eTerm);
  const Bindings *chosen;
  Tokens after_types;
  const TermTypes *types = NULL;
  if (!type_arguments(more, budget, params, environment, NULL, tokens, &chosen, &after_types, want_types(term, &types),
                      &budget, failure))
    return 0;
  const Term *partial = NULL;
  int ok = prefix_argument(more, budget, atom, position, expected, name, params, value_params(chosen, params),
                           subst_type(chosen, result), chosen, environment, tokens, after_types, value, rest, left,
                           want_term(term, &partial), failure);
  return with_term(ok, term,
                   partial != NULL ? term_call(TERM_PARTIAL, position, 0, partial->tokens, partial->end, partial->name,
                                               partial->callee, types, partial->args)
                                   : NULL);
}

int prefix_argument(Fuel fuel, Nat budget, Nat atom, Nat position, const LType *expected, Text name,
                    const Params *params, const Params *formal, const LType *result, const Bindings *chosen,
                    const Bindings *environment,
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
                           .items = values_item(text_value(name), typed_bound(params, chosen, tokens, after_types, values))}),
                         after, spent, value, rest, left),
                     term,
                     term != NULL ? named_term(TERM_PARTIAL, position, name, NULL, args, taken_tokens(tokens, after),
                                               first_position(after), environment)
                                  : NULL);
  return fail_at(failure, position, eTerm);
}

int inline_argument(Fuel fuel, Nat budget, Nat position, const LType *expected, const Bindings *environment,
                    Tokens tokens, const Value **value, Tokens *rest, Nat *left, const Term **term, Failure *failure) {
  if (fuel == 0) return fail_at(failure, position, eFuel);
  Fuel more = fuel - 1;
  const Params *params;
  Tokens body;
  if (!inline_binders(more, budget, environment, NULL, tokens, &params, &body, &budget, failure)) return 0;
  if (same_type(expected, arrow_type(params, arrow_result(expected))) != 1) return fail_at(failure, position, eTerm);
  const Value *checked;
  Tokens after;
  Nat spent;
  const Term *inner = NULL;
  if (!parse_term(more, budget, 0, arrow_result(expected),
                  bind_params(params, NULL, bindings_item(check_marker(), environment)), body, &checked, &after,
                  &spent, &inner, failure))
    return 0;
  /* The FUN node, the argument Value and its closure share one TERM_BODY. The
     body Term is built also when the caller wants no term (D8 part A). */
  const Term *carrier = spanned_body(body, after, inner);
  Tokens binder_span = taken_tokens(tokens, body);
  const Term *made =
      term != NULL ? term_fun(position, 0, binder_span, binder_types(params, binder_span, environment), carrier) : NULL;
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
  const Params *specialized = side_params(chosen, params);
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
    Nat ready = budget;
    Failure closing = {0, {NULL, 0}};
    int resolved = instantiate_specialized(fuel, budget, environment, specialized, earlier,
                                           terms != NULL ? reverse_terms_onto(NULL, built) : NULL, start, chosen,
                                           subst_type(chosen, head.type), &instantiated, &ready, &closing);
    const LType *expected;
    if (!close_result(fuel, ready, environment, params, earlier, resolved, instantiated, &expected, &budget, &closing))
      return side_failure(failure, closing, first_position(tokens), eTerm);
    const Value *value;
    const Term *made = NULL;
    if (!parse_term(fuel, budget, 1, expected, environment, tokens, &value, &tokens, &budget, want_term(terms, &made),
                    failure))
      return 0;
    seen = values_item(value, seen);
    if (terms != NULL) built = terms_item(made, built);
  }
}

int close_side(Fuel fuel, Nat budget, const Bindings *bound, const LType *a, Val side, Val *closed, Nat *left,
               Failure *failure) {
  if (fuel == 0) return 0;
  Fuel more = fuel - 1;
  switch (side.kind) {
  case VAL_CLOSED:
  case VAL_VAR:
    *closed = side;
    *left = budget;
    return 1;
  case VAL_TERM: {
    const Value *value;
    Failure evaluated = {0, {NULL, 0}};
    /* D4: a side closes on its node with eval_term. An unknown answer is a
       refusal: the side has no tokens to replay (K1 stays out, Q-D4-4). D9
       (design item 1): the side runs on the remaining work budget, and a
       budget failure of eval_term goes to the caller. */
    if (!eval_term(more, budget, a, bound, side.node, &value, left, &evaluated))
      return kept_budget_failure(failure, evaluated);
    return printed_side(more, value, closed);
  }
  }
  return 0;
}

/* D4 part C (design item 5): side_normal gives the normal form of a side
   node in the scope. A marker, a number and a string give themselves. A
   closed sub-term (no marker) of another form gives the literal of its
   eval_synth value (value_node), or keeps its node if the value has no
   literal. A closed form that needs an expected type keeps its checked
   node. A constructor and an application of an earlier definition give
   the same node with the normal forms of their arguments (Q-D4-5: no
   unfold). A group gives the normal form of its inner term, and a new
   literal without the group. Each other form with a marker is refused
   (eTerm at its position). A node is copied only when a child changes. */
static int normal_args(Fuel fuel, Nat budget, const Bindings *scope, const Terms *args, const Terms **normal,
                       Nat *left, Failure *failure) {
  if (fuel == 0) return 0;
  if (args == NULL) {
    *normal = NULL;
    *left = budget;
    return 1;
  }
  const Term *head;
  const Terms *tail;
  Nat spent;
  if (!side_normal(fuel - 1, budget, scope, args->head, &head, &spent, failure)) return 0;
  if (!normal_args(fuel - 1, spent, scope, args->tail, &tail, left, failure)) return 0;
  *normal = head == args->head && tail == args->tail ? args : terms_item(head, tail);
  return 1;
}

static const Term *with_args(const Term *node, const Terms *args) {
  if (args == node->args) return node;
  Term *copy = arena_alloc(sizeof *copy);
  *copy = *node;
  copy->args = args;
  return copy;
}

static int normal_typed_args(Fuel fuel, Nat budget, const Bindings *scope, const LTypes *types, const Terms *args,
                             const Terms **normal, Nat *left, Failure *failure) {
  if (fuel == 0) return 0;
  if (types == NULL || args == NULL) {
    *normal = NULL;
    *left = budget;
    return types == NULL && args == NULL;
  }
  const Term *head;
  const Terms *tail;
  Nat spent;
  if (!side_normal_at(fuel - 1, budget, scope, types->head, args->head, &head, &spent, failure) ||
      !normal_typed_args(fuel - 1, spent, scope, types->tail, args->tail, &tail, left, failure)) return 0;
  *normal = head == args->head && tail == args->tail ? args : terms_item(head, tail);
  return 1;
}

/* Closed constructor arguments use the same typed constants as substituted
   witnesses. This also canonicalizes a closed data name inside an open side.
   A group around a variable stays a group, thus refl keeps (n) different
   from n. The declared-type check compares it as the variable (D-C1).
   Applications with markers remain applications, as in side_normal. */
int side_normal_at(Fuel fuel, Nat budget, const Bindings *scope, const LType *type, const Term *node,
                   const Term **normal, Nat *left, Failure *failure) {
  if (fuel == 0) return 0;
  Fuel more = fuel - 1;
  if (node->tag == TERM_GROUP) {
    const Term *inner;
    if (!side_normal_at(more, budget, scope, type, first_arg(node), &inner, left, failure)) return 0;
    *normal = inner->tag == TERM_NUMBER || inner->tag == TERM_STRING ||
              inner->tag == TERM_CLOSED
                  ? inner : with_args(node, terms_item(inner, NULL));
    return 1;
  }
  Plan plan;
  int constructor = node->tag == TERM_CONSTRUCT && constructor_plan(type, node->name, &plan);
  const Binding *item = NULL;
  int data_name = node->tag == TERM_NAME && lookup(node->name, scope, &item) &&
                  item->kind == BIND_VALUE && item->slot == 0 && same_type(type, item->type);
  if (term_marker_bound(node) == 0 && (constructor || data_name)) {
    const Value *value;
    Val closed;
    Failure evaluated = {0, {NULL, 0}};
    /* D9 (design item 2): the node runs on the remaining work budget, and a
       budget failure of eval_term goes to the caller. D11 part A: the
       closed node runs as at the top level (closed_environment). */
    if (!eval_term(more, budget, type, closed_environment(scope), node, &value, left, &evaluated))
      return kept_budget_failure(failure, evaluated);
    if (!printed_side(more, value, &closed)) return 0;
    *normal = term_closed(node->position, type, value, closed.text);
    return 1;
  }
  const LTypes *types = constructor ? plan_arguments(&plan) : NULL;
  if (node->tag == TERM_APPLY && lookup(node->name, scope, &item) && item->kind == BIND_FUN) {
    const Bindings *chosen;
    Tokens after;
    if (!type_arguments(more, budget, item->params, scope, NULL, node->tokens, &chosen, &after, NULL, &budget, failure))
      return 0;
    types = param_types(side_params(chosen, item->params));
  }
  if (types != NULL) {
    const Terms *args;
    if (!normal_typed_args(more, budget, scope, types, node->args, &args, left, failure)) return 0;
    *normal = with_args(node, args);
    return 1;
  }
  return side_normal(fuel, budget, scope, node, normal, left, failure);
}

int side_normal(Fuel fuel, Nat budget, const Bindings *scope, const Term *node, const Term **normal, Nat *left,
                Failure *failure) {
  if (fuel == 0) return 0;
  Fuel more = fuel - 1;
  *left = budget;
  if (node->tag == TERM_VAR || node->tag == TERM_NUMBER || node->tag == TERM_STRING || node->tag == TERM_CLOSED) {
    *normal = node;
    return 1;
  }
  if (term_marker_bound(node) == 0 && node->tag != TERM_CONSTRUCT && node->tag != TERM_GROUP) {
    /* These checked forms have no eval_synth case. Their expected type
       came from the enclosing constructor, so inference cannot replace
       the node. Keep the closed form, as for other non-literal values. */
    switch (node->tag) {
    case TERM_PARTIAL:
    case TERM_FUN:
    case TERM_REFL:
    case TERM_PURE:
    case TERM_MAP:
    case TERM_BIND:
    case TERM_FILTER:
    case TERM_FOLD:
    case TERM_FOLD_VALUE:
    case TERM_UNFOLD:
    case TERM_UNFOLD_VALUE:
      *normal = node;
      return 1;
    default: break;
    }
    Typed typed;
    /* D11 part A: the closed sub-term runs as at the top level. */
    if (!eval_synth(more, budget, closed_environment(scope), node, &typed, left, failure)) return 0;
    /* Some Option payloads use VALUE_NAT or VALUE_TEXT too. Only a Nat
       or Text term can be replaced by the corresponding scalar literal. */
    *normal = same_type(typed.type, &nat_type) || same_type(typed.type, &text_type)
                  ? value_node(node->position, typed.value, node)
                  : node;
    return 1;
  }
  if (node->tag == TERM_GROUP) {
    const Term *inner;
    if (!side_normal(more, budget, scope, node->args->head, &inner, left, failure)) return 0;
    if (inner->tag == TERM_NUMBER || inner->tag == TERM_STRING || inner->tag == TERM_CLOSED) {
      *normal = inner;
      return 1;
    }
    *normal = inner == node->args->head ? node : with_args(node, terms_item(inner, node->args->tail));
    return 1;
  }
  int applied = node->tag == TERM_APPLY && (node->callee == NULL || node->callee->tag == TERM_NAME);
  /* D5 part C: projections of a neutral Sigma value stay nodes, as an
     application with a marker does. A payload can itself be a Sigma. */
  int projected = node->tag == TERM_WITNESS || node->tag == TERM_PAYLOAD;
  if (node->tag != TERM_CONSTRUCT && !applied && !projected) return fail_at(failure, node->position, eTerm);
  const Terms *args;
  if (!normal_args(more, budget, scope, node->args, &args, left, failure)) return 0;
  *normal = with_args(node, args);
  return 1;
}

int close_body_side(Fuel fuel, Nat budget, const Bindings *environment, const LType *a, Val side, Val *closed,
                    Nat *left, Failure *failure) {
  if (fuel == 0) return 0;
  if (kept_side(side) == 1) {
    *closed = side;
    *left = budget;
    return 1;
  }
  /* D11 part A (design items 2 and 4): a side with no marker closes as at
     the top level, on the remaining work budget. On a failure, *left keeps
     the budget (D10 delta 7). */
  Nat spent;
  *left = budget;
  if (!close_side(fuel - 1, budget, closed_environment(environment), a, side, closed, &spent, failure)) return 0;
  *left = spent;
  return 1;
}

int close_result(Fuel fuel, Nat budget, const Bindings *environment, const Params *params, const Values *values,
                 int resolved, const LType *result, const LType **closed, Nat *left, Failure *failure) {
  if (fuel == 0) return 0;
  Fuel more = fuel - 1;
  if (!resolved) return 0;
  const LType *a;
  Val lhs;
  Val rhs;
  if (!sides_of(result, &a, &lhs, &rhs)) {
    *closed = result;
    *left = budget;
    return 1;
  }
  Val x;
  Val y;
  Nat spent;
  if (checking_body(environment) == 1) {
    if (!close_body_side(more, budget, environment, a, lhs, &x, &spent, failure)) return 0;
    if (!close_body_side(more, spent, environment, a, rhs, &y, left, failure)) return 0;
    *closed = eq_type(a, x, y);
    return 1;
  }
  const Bindings *bound = argument_bindings(0, params, values, environment);
  if (!close_side(more, budget, bound, a, lhs, &x, &spent, failure)) return 0;
  if (!close_side(more, spent, bound, a, rhs, &y, left, failure)) return 0;
  *closed = eq_type(a, x, y);
  return 1;
}

/* At fuel 0 the params not yet closed are kept as they are. A param that
   cannot close keeps its type and does not take work budget. Exhaustion of
   the work budget stops the call and preserves its failure. */
int close_params(Fuel fuel, Nat budget, const Bindings *environment, const Params *params,
                 const Values *values, const Params *remaining, const Params **closed, Nat *left,
                 Failure *failure) {
  const Params *done = NULL;
  *left = budget;
  for (; remaining != NULL; remaining = remaining->tail) {
    if (fuel == 0) {
      *closed = reverse_params_onto(remaining, done);
      return 1;
    }
    fuel = fuel - 1;
    Param head = remaining->head;
    const LType *found;
    Nat spent;
    Failure closing = {0, {NULL, 0}};
    int ready = close_result(fuel, *left, environment, params, values, 1, head.type, &found, &spent, &closing);
    if (!ready && same_text(closing.message, eBudget)) {
      *failure = closing;
      return 0;
    }
    if (ready) *left = spent;
    done = params_item(ready ? (Param){head.name, found} : head, done);
  }
  *closed = reverse_params_onto(NULL, done);
  return 1;
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
    case BIND_FAMILY:
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
    if (!parse_type(more, budget, 0, environment, after_colon, &ty, &after_type, &budget, failure)) return 0;
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
                    slotted_item(value_binding(head.text, ty, &null_value), bindings_item(check_marker(), environment)),
                    body, &value, &after, &spent, &inner, failure))
      return 0;
    *op = (Unary){head.text, ty, wanted, environment, spanned_body(body, after, inner)};
    *rest = after;
    *left = spent;
    Tokens binder_span = taken_tokens(tokens, body);
    return with_term(1, term,
                     term != NULL ? term_fun(position, 0, binder_span,
                                             binder_types(params_item((Param){head.text, ty}, NULL), binder_span,
                                                          environment),
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
  if (!type_arguments(more, budget, params, environment, NULL, tokens, &chosen, &after_types, want_types(term, &types),
                      &budget, failure))
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
                      typed_bound(params, chosen, tokens, after_types, values), environment);
  Unary shaped;
  if (!unary_of(environment, &closure, &shaped)) return fail_at(failure, position, eUnary);
  *op = shaped;
  *rest = after;
  *left = spent;
  return with_term(1, term,
                   term != NULL ? named_term(TERM_PARTIAL, position, name, types, args, taken_tokens(tokens, after),
                                             first_position(after), environment)
                                : NULL);
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
    case BIND_FAMILY:
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
  if (!inline_binders(more, budget, environment, NULL, tokens, &params, &body, &budget, failure)) return 0;
  const LType *result = inline_result(mode, expected, params);
  const Value *value = NULL;
  Tokens after = {0};
  Nat spent = 0;
  const Term *inner = NULL;
  if (!parse_term(more, budget, 0, result, bind_params(params, NULL, bindings_item(check_marker(), environment)), body,
                  &value, &after, &spent, &inner, failure))
    return 0;
  Tokens binder_span = taken_tokens(tokens, body);
  const Term *made =
      term != NULL ? term_fun(position, 0, binder_span, binder_types(params, binder_span, environment), inner) : NULL;
  return with_term(
      worked_stepper((Stepper){params, result, environment, spanned_body(body, after, inner)},
                     after, spent, op, rest, left),
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
  if (!type_arguments(more, budget, params, environment, NULL, tokens, &chosen, &after_types, want_types(term, &types),
                      &budget, failure))
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
                                 name, typed_bound(params, chosen, tokens, after_types, values), environment);
  const Term *called = term != NULL ? named_term(TERM_PARTIAL, position, name, types, args, taken_tokens(tokens, after),
                                                 first_position(after), environment)
                                    : NULL;
  switch (made.kind) {
  case BIND_VALUE: return fail_at(failure, position, eStep);
  case BIND_FAMILY:
  case BIND_TYPE: return fail_at(failure, position, eStep);
  case BIND_ARROW: return fail_at(failure, position, eStep);
  case BIND_FUN: {
    Stepper found = {made.params, made.type, definition_scope(made.name, environment), made.term};
    return with_term(worked_stepper(found, after, spent, op, rest, left), term, called);
  }
  case BIND_CLOSURE: {
    Stepper found = {made.params, made.type, made.scope, made.term};
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

/* The body of an op at one application: eval_term on the checked body Term,
   and rest is empty (D8 part A). An opaque closure has no term: the answer is
   the eTerm of an empty body, as on the token path. */
static int apply_body(Fuel fuel, Nat budget, const LType *expected, const Bindings *environment, const Term *term,
                      const Value **value, Tokens *rest, Nat *left, Failure *failure) {
  *rest = (Tokens){0};
  if (term == NULL) return fail_at(failure, 0, eTerm);
  return eval_term(fuel, budget, expected, environment, term, value, left, failure);
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
  if (!apply_body(more, nat_sub(used, 1), unary_result(op), unary_environment(op, item), op.term,
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
  if (!apply_body(more, nat_sub(budget, 1), unary_result(op), unary_environment(op, items->head), op.term,
                  &applied, &after, &spent, failure))
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
                  chosen.term, &applied, &applied_rest, &applied_left, failure))
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
  return fold_tail(more, spent, position, first_position(tokens), expected, op, environment, after_function, function,
                   value, rest, left, term, failure);
}

/* fold_term after f1 (D3-s6 part B): second_function selects FOLD_VALUE,
   else the FOLD route. The FOLD_VALUE node keeps after_function, the span
   after f1, as Term.tokens. eval_fold_value runs fold_tail on that span,
   with function and term NULL, when its f2 trial gives 0. */
int fold_tail(Fuel more, Nat spent, Nat position, Nat function_position, const LType *expected, Stepper op,
              const Bindings *environment, Tokens after_function, const Term *function, const Value **value,
              Tokens *rest, Nat *left, const Term **term, Failure *failure) {
  if (second_function(more, spent, expected, environment, after_function) == 1) {
    const Term *algebra = NULL;
    if (!fold_value_term(more, spent, position, function_position, expected, op, environment, after_function,
                         value, rest, left, want_term(term, &algebra), failure))
      return 0;
    return with_term(1, term,
                     function != NULL && algebra != NULL
                         ? term_call(TERM_FOLD_VALUE, position, 0, after_function, 0, (Text){NULL, 0}, NULL, NULL,
                                     terms_item(function, algebra->args))
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
  if (fold_fits(found.type, expected, op) != 1) return fail_at(failure, function_position, eTerm);
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
                    op.term, folded, rest, left, failure);
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
                  op.term, &result, &after, &spent, failure))
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
                    stepper_environment(step, values_item(algebra_input(value, results), NULL)), step.term,
                    folded, rest, left, failure);
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
                  op.term, &layer, &after, &spent, failure))
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
