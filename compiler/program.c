/* program.c: the definitions of a program and its JSON document. A port of
   program.mech. parameter_type, parse_signature, parse_binders and
   parse_program take one unit of fuel per call and fail with eFuel at the
   first token position when no fuel is left; starts_arrow answers 0. A
   Worked answer follows checker.c: int 1 with the answer, the rest tokens
   and the remaining budget written, or 0 with the failure written. */
#include "ledger.h"

static const Value null_value = {.kind = VALUE_NULL};
static const LType universe_zero = {.tag = TY_UNIVERSE, .level = 0};

/* A function type of a definition or of a named function type. */
typedef struct {
  const Params *params;
  const LType *result;
} Signature;

/* A checked instance keeps the source byte and name of its definition for
   print errors. NULL is the end. */
typedef struct Located Located;
struct Located {
  Nat position;
  Text name;
  const Value *value;
  const Located *tail;
};

static Tokens drop_token(Tokens tokens) {
  if (tokens.size == 0) return tokens;
  return (Tokens){tokens.items + 1, tokens.size - 1};
}

static const LType *make_type(LType value) {
  LType *type = arena_alloc(sizeof *type);
  *type = value;
  return type;
}

static const LType *schema_type_of(Text name) { return make_type((LType){.tag = TY_SCHEMA, .name = name}); }

static const LType *list_type_of(const LType *item) { return make_type((LType){.tag = TY_LIST, .left = item}); }

static const LType *eq_type(const LType *a, Val lhs, Val rhs) {
  return make_type((LType){.tag = TY_EQ, .left = a, .lhs = lhs, .rhs = rhs});
}

static Val closed_side(Text text) { return (Val){.kind = VAL_CLOSED, .text = text}; }

static Val var_side(Nat index) { return (Val){.kind = VAL_VAR, .index = index}; }

static Val term_side(const Term *node) { return (Val){.kind = VAL_TERM, .node = node}; }

static const Params *param_cons(Param head, const Params *tail) {
  Params *cell = arena_alloc(sizeof *cell);
  *cell = (Params){head, tail};
  return cell;
}

static const Bindings *binding_cons(Binding head, const Bindings *tail) {
  Bindings *cell = arena_alloc(sizeof *cell);
  *cell = (Bindings){head, tail};
  return cell;
}

/* reverseListOnto: the items of params in reverse order, then done. */
static const Params *reverse_params_onto(const Params *done, const Params *params) {
  for (const Params *cell = params; cell != NULL; cell = cell->tail) done = param_cons(cell->head, done);
  return done;
}

/* Checking fuel from source bytes, capped at 512 steps: one step per byte
   while the count is below 512, and one at the end if it still is. */
static Fuel depth_fuel_from(Nat count, Fuel done, Text source) {
  for (Nat index = 0; index < source.size; index++) {
    if (count >= 512) return done;
    count++;
    done++;
  }
  return count < 512 ? done + 1 : done;
}

static Fuel output_fuel_from(Fuel done, Text source) { return done + (Fuel)source.size * 32 + 128; }

/* The work budget is 8 function bodies for each source byte, plus 64. The
   count starts at 65 because the budget 0 is the error. */
static Nat work_budget_from(Nat done, Text source) { return done + 8 * source.size; }

/* printValue with a fresh printer. The text is in output order. */
static int printed_text(Fuel fuel, const Value *value, Text *text, Failure *failure) {
  Printer printer = {fuel, builder_new()};
  if (!print_value(&printer, value, failure)) return 0;
  *text = builder_text(&printer.output);
  return 1;
}

/* An equality type keeps the canonical JSON text of its two sides. A print
   error fails at the position of the definition. */
static int eq_type_printed(Nat position, Fuel fuel, const LType *a, const Value *lhs, const Value *rhs,
                           const LType **type, Failure *failure) {
  Failure printing;
  Text left;
  Text right;
  if (!printed_text(fuel, lhs, &left, &printing)) return fail_at(failure, position, printing.message);
  if (!printed_text(fuel, rhs, &right, &printing)) return fail_at(failure, position, printing.message);
  *type = eq_type(a, closed_side(left), closed_side(right));
  return 1;
}

/* `Eq A x y` is only the type of a definition. A is an atom that is a data
   type, and the sides x and y are atoms of type A. */
static int parse_eq_type(Nat position, Fuel fuel, Nat budget, const Bindings *environment, Tokens tokens,
                         const LType **type, Tokens *rest, Nat *left, Failure *failure) {
  const LType *a;
  Tokens after_type;
  Nat typed;
  if (!parse_type(fuel, budget, 1, environment, tokens, &a, &after_type, &typed, failure)) return 0;
  if (type_level(a) != 0) return fail_at(failure, first_position(tokens), eData);
  const Value *lhs;
  Tokens after_left;
  Nat spent;
  if (!parse_term(fuel, typed, 1, a, environment, after_type, &lhs, &after_left, &spent, NULL, failure)) return 0;
  const Value *rhs;
  Tokens after_right;
  Nat remaining;
  if (!parse_term(fuel, spent, 1, a, environment, after_left, &rhs, &after_right, &remaining, NULL, failure)) return 0;
  *rest = after_right;
  return lift_parsed(remaining, eq_type_printed(position, fuel, a, lhs, rhs, type, failure), left);
}

static int declared_type(Fuel fuel, Nat budget, const Bindings *environment, Tokens tokens, const LType **type,
                         Tokens *rest, Nat *left, Failure *failure) {
  if (tokens.size != 0 && tokens.items[0].kind == TOKEN_IDENTIFIER && same_text(tokens.items[0].text, sEq) == 1)
    return parse_eq_type(tokens.items[0].position, fuel, budget, environment, drop_token(tokens), type, rest, left,
                         failure);
  return parse_type(fuel, budget, 0, environment, tokens, type, rest, left, failure);
}

/* The mark of a first punctuation token, else 1. No punctuation has mark 1. */
static Nat mark_of(Tokens tokens) {
  if (tokens.size == 0 || tokens.items[0].kind != TOKEN_PUNCTUATION) return 1;
  return tokens.items[0].number;
}

static int name_of(Tokens tokens, Text *name) {
  if (tokens.size == 0 || tokens.items[0].kind != TOKEN_IDENTIFIER) return 0;
  *name = tokens.items[0].text;
  return 1;
}

static Nat is_word(Text word, Tokens tokens) {
  Text name;
  if (!name_of(tokens, &name)) return 0;
  return same_text(name, word);
}

/* A parameter group `(x : A)` starts with an opening parenthesis, a name
   and a colon. A type never contains a colon. */
static Nat starts_param(Tokens tokens) {
  return mark_of(tokens) == 40 && mark_of(drop_token(tokens)) == 1
    && mark_of(drop_token(drop_token(tokens))) == 58;
}

/* WritePath is the function type of core/ops.def:
   (log : Log) -> (write : Write) -> Step. */
static Signature write_path_signature(void) {
  const Params *params =
    param_cons((Param){text_of_cstring("log"), list_type_of(schema_type_of(text_of_cstring("Entry")))},
               param_cons((Param){text_of_cstring("write"), schema_type_of(text_of_cstring("Write"))}, NULL));
  return (Signature){params, schema_type_of(text_of_cstring("Step"))};
}

/* M1 part B (design items 5 and 6): the WritePath type, and the binders of
   the builtin write. The second binder is command, not write: a binder write
   hides the builtin in the body (delta B-2). */
const LType *write_path_type(void) {
  Signature found = write_path_signature();
  return arrow_type(found.params, found.result);
}

const Params *write_binders(void) {
  const Params *params = write_path_signature().params;
  return param_cons(params->head, param_cons((Param){text_of_cstring("command"), params->tail->head.type}, NULL));
}

/* ReadPath is the function type of core/ops.def (step D7b):
   (answer : Type 0) -> (log : Log) -> (query : Query answer) -> answer.
   The query type and the result keep the type parameter answer as a schema
   name, as a written type parameter does. */
static Signature read_path_signature(void) {
  const LType *answer = schema_type_of(text_of_cstring("answer"));
  LType *query = arena_alloc(sizeof *query);
  *query = (LType){.tag = TY_QUERY, .left = answer};
  const Params *params =
    param_cons((Param){text_of_cstring("answer"), &universe_zero},
               param_cons((Param){text_of_cstring("log"), list_type_of(schema_type_of(text_of_cstring("Entry")))},
                          param_cons((Param){text_of_cstring("query"), query}, NULL)));
  return (Signature){params, answer};
}

/* M2 part A (design item 2): the ReadPath type, and the binders of the
   builtin read: answer, log and query. */
const LType *read_path_type(void) {
  Signature found = read_path_signature();
  return arrow_type(found.params, found.result);
}

const Params *read_binders(void) { return read_path_signature().params; }

/* A type definition can name a function type. A parameter hides this name. */
static int named_signature(const Bindings *environment, Tokens tokens, Signature *found) {
  Text name;
  if (!name_of(tokens, &name)) return 0;
  const Binding *item;
  if (!lookup(name, environment, &item)) {
    if (same_text(name, opsTextWritePath()) != 1 && same_text(name, opsTextReadPath()) != 1) return 0;
    *found = same_text(name, opsTextWritePath()) == 1 ? write_path_signature() : read_path_signature();
    return 1;
  }
  switch (item->kind) {
  case BIND_ARROW:
    *found = (Signature){item->params, item->type};
    return 1;
  case BIND_VALUE:
  case BIND_FAMILY:
  case BIND_TYPE:
  case BIND_FUN:
  case BIND_CLOSURE: return 0;
  }
  return 0;
}

/* The type of a parameter can also be the name of a function type, also of
   a function type with a type parameter, as ReadPath (step D7b). The argument
   of this parameter is a function. */
static int parameter_type(Fuel fuel, Nat budget, const Bindings *environment, const Params *done, Tokens tokens,
                          const LType **type, Tokens *rest, Nat *left, Failure *failure) {
  if (fuel == 0) return fail_at(failure, first_position(tokens), eFuel);
  if (mark_of(tokens) == 40) {
    Tokens inside;
    if (!parameter_type(fuel - 1, budget, environment, done, drop_token(tokens), type, &inside, left, failure))
      return 0;
    return close_parsed(inside, rest, failure);
  }
  Signature found;
  if (!named_signature(environment, tokens, &found))
    return parse_type_in(fuel, budget, 0, environment, done, tokens, type, rest, left, failure);
  *type = arrow_type(found.params, found.result);
  *rest = drop_token(tokens);
  *left = budget;
  return 1;
}

/* A function type starts with a parameter group or is the name of one.
   Grouping parentheses preserve this distinction from data types. */
static Nat starts_arrow(Fuel fuel, const Bindings *environment, Tokens tokens) {
  Signature found;
  if (fuel == 0) return 0;
  if (named_signature(environment, tokens, &found)) return 1;
  if (starts_param(tokens) == 1) return 1;
  if (mark_of(tokens) != 40) return 0;
  return starts_arrow(fuel - 1, environment, drop_token(tokens));
}

static Nat reserved_param(Param item) { return reserved_name(item.name); }

Nat param_count(const Params *params) {
  Nat count = 0;
  for (const Params *cell = params; cell != NULL; cell = cell->tail) count++;
  return count;
}

/* Prefixing a named signature moves its neutral parameter positions. A
   closed side and the local scopes of function parameter types stay intact.
   The table of shift_node maps the marker i to the variable node of the
   marker offset + i, at the position of the first variable node of the
   marker i, with cost 0. */
static const Term *shift_node(Nat offset, const Term *node) {
  Nat size = term_marker_bound(node);
  const Term **table = arena_alloc(sizeof *table * (size + 1));
  for (Nat index = 0; index < size; index++) {
    const Term *first = term_marker_first(node, index);
    table[index] = first == NULL ? NULL : term_var(first->position, 0, marker_name(offset + index), offset + index);
  }
  return term_with_markers(node, table, size);
}

static Val shift_eq_side(Nat offset, Val side) {
  switch (side.kind) {
  case VAL_CLOSED: return side;
  case VAL_VAR: return var_side(offset + side.index);
  case VAL_TERM: return term_side(shift_node(offset, side.node));
  }
  return side;
}

/* The markers of a type move by offset: the sides of each Eq and the binder
   of each Sigma, also inside a type former. */
const LType *shift_type_markers(Nat offset, const LType *result) {
  switch (result->tag) {
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
    return result;
  case TY_OPTION:
  case TY_LIST:
  case TY_QUERY:
    return make_type((LType){.tag = result->tag, .left = shift_type_markers(offset, result->left)});
  case TY_PROD:
  case TY_SUM:
    return make_type((LType){.tag = result->tag, .left = shift_type_markers(offset, result->left),
                             .right = shift_type_markers(offset, result->right)});
  case TY_EQ:
    return eq_type(shift_type_markers(offset, result->left), shift_eq_side(offset, result->lhs),
                   shift_eq_side(offset, result->rhs));
  case TY_SIGMA:
    return make_type((LType){.tag = TY_SIGMA, .name = result->name, .level = offset + result->level,
                             .left = shift_type_markers(offset, result->left),
                             .right = shift_type_markers(offset, result->right)});
  }
  return result;
}

static const Params *shift_eq_params(Nat offset, const Params *params) {
  if (params == NULL) return NULL;
  return param_cons((Param){params->head.name, shift_type_markers(offset, params->head.type)},
                    shift_eq_params(offset, params->tail));
}

/* The position of the nearest parameter with this name, if it is a value
   parameter of type A. The list holds the latest parameter first. */
static int param_index(const LType *a, Text name, const Params *done, Nat *index) {
  for (const Params *cell = done; cell != NULL; cell = cell->tail) {
    if (same_text(name, cell->head.name) == 1) {
      if (same_type(cell->head.type, a) != 1) return 0;
      *index = param_count(cell->tail);
      return 1;
    }
  }
  return 0;
}

/* A value parameter is a neutral side: the position of the parameter. */
static int neutral_side(const LType *a, const Params *done, Tokens tokens, Val *side) {
  Nat index;
  Text name;
  if (!name_of(tokens, &name) || !param_index(a, name, done, &index)) return 0;
  *side = var_side(index);
  return 1;
}

/* A closed side cannot name a value parameter. Each value parameter hides
   an outer definition with the same name. */
static const Bindings *hide_params(const Params *done, const Bindings *environment) {
  if (done == NULL) return environment;
  if (is_type_param(done->head) == 1) return hide_params(done->tail, environment);
  return binding_cons((Binding){.kind = BIND_TYPE, .name = done->head.name, .type = &universe_zero,
                                .defined = schema_type_of(done->head.name)},
                      hide_params(done->tail, environment));
}

/* The position of the nearest parameter with this name: Option (Option Nat)
   as in param_level. found 0: a type parameter or a function parameter,
   which a computed side cannot name. */
int marker_for(Text name, const Params *done, Nat *found, Nat *index) {
  for (const Params *cell = done; cell != NULL; cell = cell->tail) {
    if (same_text(name, cell->head.name) == 1) {
      *found = !(is_type_param(cell->head) == 1 || is_arrow_type(cell->head.type) == 1);
      *index = param_count(cell->tail);
      return 1;
    }
  }
  return 0;
}

static Nat names_param(const Params *done, Tokens tokens) {
  Nat found;
  Nat index;
  for (Nat at = 0; at < tokens.size; at++)
    if (tokens.items[at].kind == TOKEN_IDENTIFIER && marker_for(tokens.items[at].text, done, &found, &index)) return 1;
  return 0;
}

/* The tokens of one atom: a token or a parenthesized group. At depth 0 a
   punctuation other than `(` does not end the atom (as in the mech). */
static Tokens atom_of(Nat depth, Tokens tokens) {
  Nat count = 0;
  while (count < tokens.size) {
    Token head = tokens.items[count];
    count++;
    if (head.kind != TOKEN_PUNCTUATION) {
      if (depth == 0) break;
    } else if (head.number == 40) {
      depth++;
    } else if (head.number == 41 && depth == 1) {
      break;
    } else if (head.number == 41) {
      depth = nat_sub(depth, 1);
    }
  }
  return (Tokens){tokens.items, count};
}

/* A computed side can name an earlier definition: at the head of an
   application (D4 part C, Q-D4-7 lift 2) and as a bare name (D4 part D, lift
   3). It cannot name a type or function parameter, and it cannot hold an
   inline function. D8 part B (delta D-B5): this check stays on the tokens
   before the parse, so the refusal keeps its message and position. */
static Nat side_refused(const Params *done, Tokens tokens) {
  for (Nat at = 0; at < tokens.size; at++) {
    Token head = tokens.items[at];
    Nat found;
    Nat level;
    if (head.kind == TOKEN_IDENTIFIER && marker_for(head.text, done, &found, &level) && !found) return 1;
    if (head.kind == TOKEN_IDENTIFIER && same_text(head.text, sfun) == 1) return 1;
  }
  return 0;
}

/* The definition check binds each marker to null with the type of its
   parameter. */
static const Bindings *marker_bindings(const Params *done, const Bindings *environment) {
  if (done == NULL) return environment;
  return binding_cons((Binding){.kind = BIND_VALUE, .name = marker_name(param_count(done->tail)),
                                .type = done->head.type, .value = &null_value},
                      marker_bindings(done->tail, environment));
}

/* A computed side (step D4a) is an atom that names value parameters, such
   as `(some n)`. A function type with type parameters cannot have one. The
   side keeps only the term, with each marker as a variable node. D8 part B
   (design item 7): the atom is parsed once with the parameters in scope
   (parse_signature binds them), and put_param_markers puts the markers in
   the checked term. A side with no term is refused. */
static int computed_side(Fuel fuel, Nat budget, const LType *a, const Bindings *environment, const Params *done,
                         Tokens tokens, Val *side, Tokens *rest, Nat *left, Failure *failure) {
  if (side_refused(done, atom_of(0, tokens)) == 1) return fail_at(failure, first_position(tokens), eTerm);
  if (has_type_param(done) == 1) return fail_at(failure, first_position(tokens), eTerm);
  const Value *value;
  const Term *node = NULL;
  Tokens after;
  Nat remaining;
  if (!parse_term(fuel, budget, 1, a, binding_cons(check_marker(), environment), atom_of(0, tokens), &value,
                  &after, &remaining, &node, failure))
    return 0;
  const Bindings *unused = environment;
  const Term *marked;
  if (node == NULL || !put_param_markers(done, environment, node, &unused, &marked))
    return fail_at(failure, first_position(tokens), eTerm);
  const Bindings *scope = binding_cons(check_marker(), marker_bindings(done, environment));
  /* D4 part C: a side with a marker takes its normal form (design item 5).
     close_side closes a side with no marker later, as before. */
  if (term_marker_bound(marked) > 0 &&
      !side_normal_at(fuel, remaining, scope, a, marked, &marked, &remaining, failure))
    return 0;
  *side = marked->tag == TERM_VAR ? var_side(marked->index) : term_side(marked);
  *rest = skip_atom(0, tokens);
  *left = remaining;
  return 1;
}

/* A side of an equality in a function type is the name of a value parameter
   of type A, an atom that names no value parameter and applies no function,
   or a computed side. A closed side keeps its canonical JSON text. */
static int eq_side(Fuel fuel, Nat budget, const LType *a, const Bindings *environment, const Params *done,
                   Tokens tokens, Val *side, Tokens *rest, Nat *left, Failure *failure) {
  if (neutral_side(a, done, tokens, side)) {
    *rest = drop_token(tokens);
    *left = budget;
    return 1;
  }
  if (names_param(done, atom_of(0, tokens)) == 1)
    return computed_side(fuel, budget, a, environment, done, tokens, side, rest, left, failure);
  const Value *value;
  /* D11 part A: a closed side in a body (a transport motive) runs as at the
     top level, without the checking frames. */
  if (!parse_term(fuel, budget, 1, a, closed_environment(hide_params(done, environment)), tokens, &value, rest, left,
                  NULL, failure))
    return 0;
  Failure printing;
  Text text;
  if (!printed_text(fuel, value, &text, &printing)) return fail_at(failure, first_position(tokens), printing.message);
  *side = closed_side(text);
  return 1;
}

/* D12 part B (design items 7 to 9): the type `P a` for the type family P.
   The argument a has the form of an Eq side and checks against A. The family
   moves into the scope of done before the substitution (delta F-B2), so the
   marker of a parameter in a stays as written. No argument (no token, or
   punctuation other than `(`) gives eData at the name. */
int family_application(Fuel fuel, Nat budget, Nat position, const LType *family, const Bindings *environment,
                       const Params *done, Tokens tokens, const LType **type, Tokens *rest, Nat *left,
                       Failure *failure) {
  if (tokens.size == 0 || (tokens.items[0].kind == TOKEN_PUNCTUATION && tokens.items[0].number != 40)) {
    *left = budget;
    return fail_at(failure, position, eData);
  }
  const LType *shifted = shift_type_markers(param_count(done), family);
  Val side;
  Nat spent;
  return eq_side(fuel, budget, shifted->left, environment, done, tokens, &side, rest, &spent, failure)
    && family_type(fuel, spent, environment, position, shifted, side, type, left, failure);
}

/* `Eq A x y` as the result of a function type. A is a data type. The
   definition checks the body with neutral sides, so `refl` needs the same
   parameter or the same closed value on both sides. D8 part B: the first side
   takes the work budget, and the second side takes the rest. */
static int eq_result(Fuel fuel, Nat budget, const Bindings *environment, const Params *done, Tokens tokens,
                     const LType **type, Tokens *rest, Nat *left, Failure *failure) {
  const LType *a;
  Tokens after_type;
  Nat typed;
  if (!parse_type_in(fuel, budget, 1, environment, done, tokens, &a, &after_type, &typed, failure)) return 0;
  if (type_level(a) != 0) return fail_at(failure, first_position(tokens), eData);
  Val lhs;
  Val rhs;
  Tokens after_left;
  Nat spent;
  if (!eq_side(fuel, typed, a, environment, done, after_type, &lhs, &after_left, &spent, failure)) return 0;
  if (!eq_side(fuel, spent, a, environment, done, after_left, &rhs, rest, left, failure)) return 0;
  *type = eq_type(a, lhs, rhs);
  return 1;
}

/* A of `Sigma (x : A) B` or of the short form `Sigma A B`. The short form
   has no binder name. */
static int sigma_domain(Fuel fuel, Nat budget, const Bindings *environment, const Params *done, Tokens tokens,
                        Text *name, const LType **a, Tokens *rest, Nat *left, Failure *failure) {
  Tokens inside;
  *name = text_end();
  if (starts_param(tokens) != 1)
    return parse_type_in(fuel, budget, 1, environment, done, tokens, a, rest, left, failure);
  if (!name_of(drop_token(tokens), name)) return fail_at(failure, first_position(tokens), eType);
  return parse_type_in(fuel, budget, 0, environment, done, drop_token(drop_token(drop_token(tokens))), a, &inside,
                       left, failure)
    && close_parsed(inside, rest, failure);
}

/* B of a Sigma type: a data type, `(Eq A y z)` or a Sigma type. done holds
   the binder, so an Eq side can name it. */
static int sigma_body(Fuel fuel, Nat budget, const Bindings *environment, const Params *done, Tokens tokens,
                      const LType **b, Tokens *rest, Nat *left, Failure *failure) {
  Tokens inside;
  if (mark_of(tokens) == 40 && is_word(sEq, drop_token(tokens)) == 1)
    return eq_result(fuel, budget, environment, done, drop_token(drop_token(tokens)), b, &inside, left, failure)
      && close_parsed(inside, rest, failure);
  if (!parse_type_in(fuel, budget, 1, environment, done, tokens, b, rest, left, failure)) return 0;
  if (type_level(*b) != 0) return fail_at(failure, first_position(tokens), eType);
  return 1;
}

/* `Sigma (x : A) B` and `Sigma A B` (D5 design items 2 and 3). A is a data
   type. The binder takes the next marker after the earlier parameters, also
   in the short form. */
int sigma_type(Fuel fuel, Nat budget, const Bindings *environment, const Params *done, Tokens tokens,
               const LType **type, Tokens *rest, Nat *left, Failure *failure) {
  if (fuel == 0) return fail_at(failure, first_position(tokens), eFuel);
  Fuel more = fuel - 1;
  Text name;
  const LType *a;
  Tokens after_a;
  Nat spent;
  if (!sigma_domain(more, budget, environment, done, tokens, &name, &a, &after_a, &spent, failure)) return 0;
  if (type_level(a) != 0 || a->tag == TY_EQ) return fail_at(failure, first_position(tokens), eType);
  const Params *inner = param_cons((Param){name, a}, done);
  const Bindings *scope =
    starts_param(tokens) == 1 ? bind_params(param_cons((Param){name, a}, NULL), NULL, environment) : environment;
  const LType *b;
  if (!sigma_body(more, spent, scope, inner, after_a, &b, rest, left, failure)) return 0;
  *type = make_type((LType){.tag = TY_SIGMA, .name = name, .level = param_count(done), .left = a, .right = b});
  return 1;
}

/* A Query type is in Type 1. Thus a function type with a Query parameter or a
   Query result is in Type 1, as a function type with a type parameter
   (step D7a). This also applies through function parameter types. */
static Nat query_in_type(const LType *type) {
  if (is_query_type(type) == 1) return 1;
  return is_arrow_type(type) == 1 && (query_in_type(type->left) == 1 || query_in_type(type->right) == 1);
}

static Nat has_query_param(const Params *params) {
  return params != NULL && (query_in_type(params->head.type) == 1 || has_query_param(params->tail) == 1);
}

static Nat has_query_type(Signature found) {
  return has_query_param(found.params) == 1 || is_query_type(found.result) == 1;
}

/* The type of a parameter. A proof parameter `(e : Eq A x y)` can name
   earlier value parameters of type A as its sides (step D2b), also inside a
   computed side (step D4b). */
static int param_declared(Fuel fuel, Nat budget, const Bindings *environment, const Params *done, Tokens tokens,
                          const LType **type, Tokens *rest, Nat *left, Failure *failure) {
  if (is_word(sEq, tokens) == 1)
    return eq_result(fuel, budget, environment, done, drop_token(tokens), type, rest, left, failure);
  return parameter_type(fuel, budget, environment, done, tokens, type, rest, left, failure);
}

static int parse_param(Fuel fuel, Nat budget, const Bindings *environment, const Params *done, Tokens tokens,
                       Param *item, Tokens *rest, Nat *left, Failure *failure) {
  Text name;
  if (!name_of(drop_token(tokens), &name)) return fail_at(failure, first_position(tokens), eFun);
  Tokens declared = drop_token(drop_token(drop_token(tokens)));
  const LType *type;
  Tokens after;
  if (!param_declared(fuel, budget, environment, done, declared, &type, &after, left, failure)) return 0;
  /* A Query type `Query T` is a parameter type (step D7a). */
  if (!(is_arrow_type(type) == 1 || type_level(type) == 0 || same_type(type, &universe_zero) == 1
        || is_query_type(type) == 1))
    return fail_at(failure, first_position(declared), eData);
  *item = (Param){name, type};
  return close_parsed(after, rest, failure);
}

/* The result rule of a signature. RESULT_DATA: the result is a data type or
   a Query type. RESULT_FAMILY: the result can also be Type 0 after one
   parameter, the domain of a type family (D12). */
typedef enum { RESULT_DATA, RESULT_FAMILY } ResultRule;

/* The family rule accepts the result Type 0 when done has one parameter, and
   the type of that parameter is a data type of level 0 that is not an
   equality (as the domain of sigma_type). */
static Nat family_result(ResultRule rule, const Params *done, const LType *result) {
  switch (rule) {
  case RESULT_DATA: return 0;
  case RESULT_FAMILY:
    return result->tag == TY_UNIVERSE && result->level == 0 && param_count(done) == 1 &&
                   type_level(done->head.type) == 0 && done->head.type->tag != TY_EQ
               ? 1
               : 0;
  }
  return 0;
}

/* The end of a chain: an `Eq` result, or a type with the level that the
   rule accepts. Each other result gives eData at its first token. */
static int chain_result(Fuel fuel, Nat budget, const Bindings *environment, const Params *done, Tokens tokens,
                        ResultRule rule, const LType **result, Tokens *rest, Nat *left, Failure *failure) {
  if (fuel == 0) return fail_at(failure, first_position(tokens), eFuel);
  if (mark_of(tokens) == 40) {
    Tokens inside;
    return chain_result(fuel - 1, budget, environment, done, drop_token(tokens), rule, result, &inside, left, failure)
      && close_parsed(inside, rest, failure);
  }
  if (is_word(sEq, tokens) == 1)
    return eq_result(fuel, budget, environment, done, drop_token(tokens), result, rest, left, failure);
  if (!parse_type_in(fuel, budget, 0, environment, done, tokens, result, rest, left, failure)) return 0;
  /* The result can also be a Query type (step D7a). */
  if (type_level(*result) != 0 && is_query_type(*result) != 1 && family_result(rule, done, *result) != 1)
    return fail_at(failure, first_position(tokens), eData);
  return 1;
}

/* `(x : A) -> ... -> B` with data types. A data type B cannot refer to a
   value parameter. An equality B = `Eq A x y` can name value parameters as
   its sides, and so can the type of a proof parameter. A type parameter
   `(A : Type 0)` comes before each value parameter, and the later types and
   B can refer to it. Its name is not a reserved name. Parameters hide outer
   names in subsequent type annotations. The name of a function type can end
   the chain. Its parameters follow the earlier ones. The rule tells which
   results end the chain (chain_result). */
static int parse_signature(Fuel fuel, Nat budget, const Bindings *environment, const Params *done, Tokens tokens,
                           ResultRule rule, Signature *found, Tokens *rest, Nat *left, Failure *failure) {
  if (fuel == 0) return fail_at(failure, first_position(tokens), eFuel);
  Fuel more = fuel - 1;
  if (starts_param(tokens) != 1) {
    if (mark_of(tokens) == 40) {
      Tokens inside;
      if (!parse_signature(more, budget, environment, done, drop_token(tokens), rule, found, &inside, left, failure))
        return 0;
      return close_parsed(inside, rest, failure);
    }
    Signature named;
    const LType *result;
    if (named_signature(environment, tokens, &named)) {
      /* A named signature at the end of a chain can bring its type parameter
         after value parameters, as `(head : Hash) -> ReadPath` (step D7b). */
      Nat offset = param_count(done);
      *found = (Signature){reverse_params_onto(shift_eq_params(offset, named.params), done),
                           shift_type_markers(offset, named.result)};
      *rest = drop_token(tokens);
      *left = budget;
      return 1;
    }
    if (!chain_result(more, budget, environment, done, tokens, rule, &result, rest, left, failure)) return 0;
    *found = (Signature){reverse_params_onto(NULL, done), result};
    return 1;
  }
  Param item;
  Tokens after;
  Nat spent;
  if (!parse_param(more, budget, environment, done, tokens, &item, &after, &spent, failure)) return 0;
  if (is_type_param(item) == 1 && reserved_param(item) == 1)
    return fail_at(failure, first_position(drop_token(tokens)), eReserved);
  if (is_type_param(item) == 1 && has_value_param(done) == 1)
    return fail_at(failure, first_position(drop_token(tokens)), eTypeParam);
  if (mark_of(after) != 62) return fail_at(failure, first_position(after), eDef);
  return parse_signature(more, spent, bind_params(param_cons(item, NULL), NULL, environment), param_cons(item, done),
                         drop_token(after), rule, found, rest, left, failure);
}

static Nat param_named(Text name, const Params *params) {
  const Binding *item;
  return lookup(name, bind_params(params, NULL, NULL), &item) ? 1 : 0;
}

/* A binder can give a new name to a type parameter. The list keeps the
   opaque type of the binder for each declared type parameter. */
static const Bindings *rename_param(Param declared, Text name, const Bindings *renames) {
  if (same_type(declared.type, &universe_zero) != 1) return renames;
  return binding_cons((Binding){.kind = BIND_TYPE, .name = declared.name, .type = declared.type,
                                .defined = schema_type_of(name)},
                      renames);
}

static const Bindings *param_renames(const Params *declared, const Params *binders, const Bindings *renames) {
  if (declared == NULL || binders == NULL) return renames;
  return param_renames(declared->tail, binders->tail, rename_param(declared->head, binders->head.name, renames));
}

/* `fun (x : A) (y : B) => t` or `fun (x : A) => fun (y : B) => t`. The
   binder types are the declared ones, with the binder names of the earlier
   type parameters. The result is the body's tokens. Earlier binders are in
   scope when checking later annotations. */
static int parse_binders(Fuel fuel, Nat budget, const Bindings *environment, const Bindings *renames,
                         const Params *declared, const Params *done, Tokens tokens, const Params **binders,
                         Tokens *rest, Nat *left, Failure *failure) {
  if (fuel == 0) return fail_at(failure, first_position(tokens), eFuel);
  Fuel more = fuel - 1;
  if (declared == NULL) {
    if (mark_of(tokens) != 63) return fail_at(failure, first_position(tokens), eFun);
    *binders = reverse_params_onto(NULL, done);
    *rest = drop_token(tokens);
    *left = budget;
    return 1;
  }
  if (mark_of(tokens) == 63 && is_word(sfun, drop_token(tokens)) == 1) {
    Tokens next = drop_token(drop_token(tokens));
    if (done == NULL) return fail_at(failure, first_position(tokens), eFun);
    if (starts_param(next) != 1) return fail_at(failure, first_position(next), eFun);
    return parse_binders(more, budget, environment, renames, declared, done, next, binders, rest, left, failure);
  }
  if (starts_param(tokens) != 1) return fail_at(failure, first_position(tokens), eFun);
  Param item;
  Tokens after;
  Nat spent;
  if (!parse_param(more, budget, environment, done, tokens, &item, &after, &spent, failure)) return 0;
  if (reserved_name(item.name) == 1) return fail_at(failure, first_position(drop_token(tokens)), eReserved);
  if (param_named(item.name, done) == 1) return fail_at(failure, first_position(drop_token(tokens)), eDuplicate);
  if (same_type(subst_type(renames, declared->head.type), item.type) != 1)
    return fail_at(failure, first_position(tokens), eFun);
  return parse_binders(more, spent, bind_params(param_cons(item, NULL), NULL, environment),
                       rename_param(declared->head, item.name, renames), declared->tail, param_cons(item, done), after,
                       binders, rest, left, failure);
}

/* `def P : (x : A) -> Type 0 := fun (x : A) => T` is a type family. T is a
   data type in the scope of the binder, with the end of a chain of a
   signature. The binding keeps the form of the motive of sigma_type: A in
   left, T in right and the binder at level 0. It is not an instance (D12). */
static int parse_family(Fuel fuel, Nat budget, Text name, const Bindings *environment, const Params *binders,
                        Tokens body, Binding *item, Tokens *rest, Nat *left, Failure *failure) {
  const LType *family;
  if (!chain_result(fuel, budget, bind_params(binders, NULL, environment), binders, body, RESULT_DATA, &family, rest,
                    left, failure))
    return 0;
  /* A Query type is not a data type. */
  if (type_level(family) != 0) return fail_at(failure, first_position(body), eData);
  *item = (Binding){.kind = BIND_FAMILY,
                    .name = name,
                    .type = make_type((LType){.tag = TY_SIGMA,
                                              .name = binders->head.name,
                                              .level = 0,
                                              .left = binders->head.type,
                                              .right = family}),
                    .params = binders};
  return 1;
}

/* A function definition checks its body once. It is not an instance. The Eq
   sides of its signature and closed side work in its body share the work
   budget, and left gets the rest. The binders check the same types again,
   thus they do not take more budget. The result Type 0 makes a type family
   (parse_family). */
static int parse_function(Fuel fuel, Nat budget, Text name, const Bindings *environment, Tokens tokens, Binding *item,
                          Tokens *rest, Nat *left, Failure *failure) {
  Signature found;
  Tokens after_type;
  if (!parse_signature(fuel, budget, environment, NULL, tokens, RESULT_FAMILY, &found, &after_type, left, failure))
    return 0;
  Tokens after_assign;
  if (!expect_mark(61, after_type, &after_assign, failure)) return 0;
  const Binding *hidden;
  /* M1 part B (design item 6, delta B-2): the one name write is the body of
     a WritePath definition when no binding hides the builtin. */
  if (is_word(swrite, after_assign) == 1 && !lookup(swrite, environment, &hidden) &&
      same_type(arrow_type(found.params, found.result), write_path_type()) == 1) {
    *rest = drop_token(after_assign);
    *item = (Binding){.kind = BIND_FUN,
                      .name = name,
                      .type = found.result,
                      .params = write_binders(),
                      .term = write_body(first_position(after_assign), after_assign, *rest)};
    return 1;
  }
  /* M2 part A (design item 3): the one name read is the body of a ReadPath
     definition when no binding hides the builtin. */
  if (is_word(sread, after_assign) == 1 && !lookup(sread, environment, &hidden) &&
      same_type(arrow_type(found.params, found.result), read_path_type()) == 1) {
    *rest = drop_token(after_assign);
    *item = (Binding){.kind = BIND_FUN,
                      .name = name,
                      .type = found.result,
                      .params = read_binders(),
                      .term = read_body(first_position(after_assign), after_assign, *rest)};
    return 1;
  }
  if (is_word(sfun, after_assign) != 1) return fail_at(failure, first_position(after_assign), eFun);
  const Params *binders;
  Tokens body;
  Nat used;
  if (!parse_binders(fuel, budget, environment, NULL, found.params, NULL, drop_token(after_assign), &binders, &body,
                     &used, failure))
    return 0;
  const LType *result = subst_type(param_renames(found.params, binders, NULL), found.result);
  if (result->tag == TY_UNIVERSE)
    return parse_family(fuel, *left, name, environment, binders, body, item, rest, left, failure);
  const Value *value;
  const Term *term = NULL;
  if (!parse_term(fuel, *left, 0, result,
                  binding_cons(body_marker(param_count(binders)), bind_params(binders, NULL, environment)), body,
                   &value, rest, left, &term, failure))
    return 0;
  *item = (Binding){
      .kind = BIND_FUN,
      .name = name,
      .type = result,
      .params = binders,
      .term = spanned_body(body, *rest, term)};
  return 1;
}

static int parse_definition(Fuel fuel, Nat budget, const Bindings *environment, Tokens tokens, Binding *item,
                            Tokens *rest, Nat *left, Failure *failure) {
  if (tokens.size == 0) return fail_at(failure, 0, eDef);
  Token head = tokens.items[0];
  if (head.kind != TOKEN_IDENTIFIER) return fail_at(failure, head.position, eDef);
  Text name = head.text;
  if (reserved_name(name) == 1) return fail_at(failure, head.position, eReserved);
  const Binding *previous;
  if (lookup(name, environment, &previous)) return fail_at(failure, head.position, eDuplicate);
  Tokens after_colon;
  if (!expect_mark(58, drop_token(tokens), &after_colon, failure)) return 0;
  if (starts_arrow(fuel, environment, after_colon) == 1)
    return parse_function(fuel, budget, name, environment, after_colon, item, rest, left, failure);
  const LType *type;
  Tokens after_type;
  Nat spent;
  if (!declared_type(fuel, budget, environment, after_colon, &type, &after_type, &spent, failure)) return 0;
  Tokens after_assign;
  if (!expect_mark(61, after_type, &after_assign, failure)) return 0;
  if (is_term_type(type) == 1) {
    const Value *value;
    if (!parse_term(fuel, spent, 0, type, environment, after_assign, &value, rest, left, NULL, failure)) return 0;
    *item = (Binding){.kind = BIND_VALUE, .name = name, .type = type, .value = value};
    return 1;
  }
  if (starts_arrow(fuel, environment, after_assign) == 1) {
    Signature found;
    if (!parse_signature(fuel, spent, environment, NULL, after_assign, RESULT_DATA, &found, rest, left, failure))
      return 0;
    if (type_level(type) != 1 + (has_type_param(found.params) == 1 || has_query_type(found) == 1))
      return fail_at(failure, first_position(after_assign), eUniverse);
    *item = (Binding){.kind = BIND_ARROW, .name = name, .type = found.result, .params = found.params};
    return 1;
  }
  const LType *inner;
  if (!parse_type(fuel, spent, 0, environment, after_assign, &inner, rest, left, failure)) return 0;
  if (type_level(type) != type_level(inner) + 1) return fail_at(failure, first_position(after_assign), eUniverse);
  *item = (Binding){.kind = BIND_TYPE, .name = name, .type = type, .defined = inner};
  return 1;
}

static const Value *text_value(Text text) {
  Value *value = arena_alloc(sizeof *value);
  *value = (Value){.kind = VALUE_TEXT, .text = text};
  return value;
}

static const Attrs *attrs_field(Text key, const Value *value, const Attrs *rest) {
  Attrs *cell = arena_alloc(sizeof *cell);
  *cell = (Attrs){key, value, rest};
  return cell;
}

static const Value *instance_value(Text name, const LType *type, const Value *value) {
  Value *instance = arena_alloc(sizeof *instance);
  *instance = (Value){.kind = VALUE_ATTRS,
                      .attrs = attrs_field(kName, text_value(name),
                                           attrs_field(kType, text_value(type_name(type)),
                                                       attrs_field(kValue, value, NULL)))};
  return instance;
}

static const Located *located_cons(Nat position, Text name, const Value *value, const Located *tail) {
  Located *cell = arena_alloc(sizeof *cell);
  *cell = (Located){position, name, value, tail};
  return cell;
}

/* Type definitions, type families, names of function types, proofs and
   Query values are not instances, so the output omits them. */
static const Located *record_instance(Nat position, Binding item, const Located *done) {
  const LType *a;
  Val lhs;
  Val rhs;
  switch (item.kind) {
  case BIND_VALUE:
    if (is_query_type(item.type) == 1 || sides_of(item.type, &a, &lhs, &rhs)) return done;
    return located_cons(position, item.name, instance_value(item.name, item.type, item.value), done);
  case BIND_FAMILY:
  case BIND_TYPE:
  case BIND_ARROW:
  case BIND_FUN:
  case BIND_CLOSURE: return done;
  }
  return done;
}

static const Located *reverse_located(const Located *done) {
  const Located *reversed = NULL;
  for (const Located *cell = done; cell != NULL; cell = cell->tail)
    reversed = located_cons(cell->position, cell->name, cell->value, reversed);
  return reversed;
}

/* A failure in a declaration keeps the name of the declaration: the token
   after `def` when it is an identifier. Else the name has size 0. */
static int name_failure(Failure *failure, Tokens tokens) {
  failure->name = tokens.size > 1 && tokens.items[1].kind == TOKEN_IDENTIFIER ? tokens.items[1].text : text_end();
  return 0;
}

static int parse_program(Fuel fuel, Nat budget, Fuel checking_fuel, const Bindings *environment, const Located *done,
                         Tokens tokens, const Located **instances, const Bindings **checked, Nat *remaining,
                         Failure *failure) {
  if (fuel == 0) return fail_at(failure, first_position(tokens), eFuel);
  if (tokens.size == 0) return fail_at(failure, 0, eDef);
  Token head = tokens.items[0];
  if (head.kind == TOKEN_PUNCTUATION && head.number == 0) {
    *instances = reverse_located(done);
    *checked = environment;
    *remaining = budget;
    return 1;
  }
  if (head.kind != TOKEN_IDENTIFIER || same_text(head.text, sdef) != 1) return fail_at(failure, head.position, eDef);
  Binding item;
  Tokens rest;
  Nat left;
  if (!parse_definition(checking_fuel, budget, environment, drop_token(tokens), &item, &rest, &left, failure))
    return name_failure(failure, tokens);
  return parse_program(fuel - 1, left, checking_fuel, binding_cons(item, environment),
                       record_instance(head.position, item, done), rest, instances, checked, remaining, failure);
}

/* A print error reports the first byte and name of the definition being printed.
   end closes the list of instances. */
static int print_instances(Printer *printer, Nat first, const Located *instances, Text end, Failure *failure) {
  Failure printing;
  const Located *last = NULL;
  for (const Located *cell = instances; cell != NULL; cell = cell->tail) {
    if (!emit_text(printer, separator(first), &printing) || !print_value(printer, cell->value, &printing)) {
      fail_at(failure, cell->position, printing.message);
      failure->name = cell->name;
      return 0;
    }
    first = 0;
    last = cell;
  }
  if (emit_text(printer, end, failure)) return 1;
  if (last != NULL) {
    failure->position = last->position;
    failure->name = last->name;
  }
  return 0;
}

Text error_text(Nat position, Text message) {
  Printer printer = {fuel_for(message), builder_new()};
  Failure ignored;
  builder_push(&printer.output, 34);
  if (!quote_bytes(&printer, message, &ignored)) return jNull;
  return append_text(jError, append_text(number_text(position), append_text(jMessage,
                     append_text(builder_text(&printer.output), jErrorEnd))));
}

/* The records of the logs (M1 design items 10 to 13). */

static const Value projection_null = {.kind = VALUE_NULL};

static const Value *projection_attrs(const Attrs *attrs) {
  Value *value = arena_alloc(sizeof *value);
  *value = (Value){.kind = VALUE_ATTRS, .attrs = attrs};
  return value;
}

static const Value *projection_attr(Text key, const Attrs *attrs) {
  return attrs == NULL ? &projection_null
         : same_text(attrs->key, key) == 1 ? attrs->value
                                           : projection_attr(key, attrs->rest);
}

/* The field key of an attrs value. A missing field is null. */
static const Value *projection_field(Text key, const Value *value) {
  return value->kind == VALUE_ATTRS ? projection_attr(key, value->attrs) : &projection_null;
}

/* The one field of a Body or a Subject value that is not the tag. */
static const Value *projection_payload(const Value *value) {
  const Attrs *attrs = value->kind == VALUE_ATTRS ? value->attrs : NULL;
  return attrs == NULL ? &projection_null
         : same_text(attrs->key, kSchemaTag()) == 1 ? projection_payload(projection_attrs(attrs->rest))
                                                     : attrs->value;
}

/* The entries of an instance: the value of a Log (List (Entry)), or the log
   of a Step that write gives (written = 1, ruling R1). A Step from makeStep
   and each other instance have no entries. */
static const Values *projection_log(const Value *instance) {
  Text type = projection_field(kType, instance)->text;
  const Value *value = projection_field(kValue, instance);
  const Value *log = same_text(type, text_of_cstring("Step")) == 1 && value->written == 1
                         ? projection_field(text_of_cstring("log"), value)
                     : same_text(type, text_of_cstring("List (Entry)")) == 1 ? value
                                                                              : &projection_null;
  return log->kind == VALUE_ITEMS ? log->items : NULL;
}

/* One record: the identity (the hash of the creating entry), the family and
   the state. */
static const Value *projection_record(Text ref, Text family, const Value *state) {
  return projection_attrs(attrs_field(text_of_cstring("ref"), text_value(ref),
                                      attrs_field(kType, text_value(family), attrs_field(kValue, state, NULL))));
}

static Nat projection_known(Text ref, const Located *records) {
  return records != NULL && (same_text(projection_field(text_of_cstring("ref"), records->value)->text, ref) == 1 ||
                             projection_known(ref, records->tail) == 1);
}

static const Attrs *projection_replace(Text key, const Value *value, const Attrs *attrs) {
  return attrs == NULL ? NULL
         : same_text(attrs->key, key) == 1
             ? attrs_field(key, value, attrs->rest)
             : attrs_field(attrs->key, attrs->value, projection_replace(key, value, attrs->rest));
}

/* Item 11: the Party or Commercial record with the identity subject gets
   lastEvent = some (refTo h). The value of some x is the value of x. */
static const Value *projection_updated(Text subject, const Value *event, const Value *record) {
  Text family = projection_field(kType, record)->text;
  if (same_text(projection_field(text_of_cstring("ref"), record)->text, subject) != 1) return record;
  if (same_text(family, text_of_cstring("Party")) != 1 && same_text(family, text_of_cstring("Commercial")) != 1)
    return record;
  const Value *state = projection_field(kValue, record);
  return projection_record(subject, family,
                           projection_attrs(projection_replace(text_of_cstring("lastEvent"), event, state->attrs)));
}

static const Located *projection_update(Text subject, const Value *event, const Located *records) {
  return records == NULL ? NULL
                         : located_cons(records->position, records->name,
                                        projection_updated(subject, event, records->value),
                                        projection_update(subject, event, records->tail));
}

/* Items 10, 11 and 13. The hash of the entry takes one work step. An entry
   with a known hash is a known record, and it changes nothing. Else a
   createsEvent entry first updates the record of its subject, and then the
   entry makes the record of its Body. records holds the newest record first. */
static int projection_entry(Nat position, Text name, const Value *entry, const Located **records, Nat *budget,
                            Failure *failure) {
  Text hash;
  if (!entry_hash(OUTPUT_LIMIT, *budget, position, entry, &hash, budget, failure)) return 0;
  if (projection_known(hash, *records) == 1) return 1;
  const Value *body = projection_field(text_of_cstring("body"), entry);
  Text tag = projection_field(kSchemaTag(), body)->text;
  const Value *state = projection_payload(body);
  const Value *subject = projection_payload(projection_field(text_of_cstring("subject"), state));
  const Value *event = object_two(text_of_cstring("kind"), text_value(text_of_cstring("kindEvent")),
                                  text_of_cstring("hash"), text_value(hash));
  const Located *seen = same_text(tag, text_of_cstring("createsEvent")) == 1
                           ? projection_update(projection_field(text_of_cstring("hash"), subject)->text, event, *records)
                           : *records;
  *records = located_cons(position, name, projection_record(hash, text_drop(tag, 7), state), seen);
  return 1;
}

/* The records of the Log and Step instances, in log order. A failure reports
   the definition of the log. */
static int project_records(Nat budget, const Located *instances, const Located **records, Failure *failure) {
  const Located *newest = NULL;
  for (const Located *cell = instances; cell != NULL; cell = cell->tail)
    for (const Values *item = projection_log(cell->value); item != NULL; item = item->tail)
      if (!projection_entry(cell->position, cell->name, item->head, &newest, &budget, failure)) {
        failure->position = cell->position;
        failure->name = cell->name;
        return 0;
      }
  *records = reverse_located(newest);
  return 1;
}

/* The records key belongs to the first record's log. Each record keeps its
   own definition for a failure in its value or the final closing bytes. */
static int print_records(Printer *printer, const Located *records, Failure *failure) {
  if (!emit_text(printer, text_of_cstring(",\"records\":["), failure)) {
    failure->position = records->position;
    failure->name = records->name;
    return 0;
  }
  return print_instances(printer, 1, records, jEnd, failure);
}

int compile_program(Text source, Text *output, Failure *failure) {
  Nat position;
  Tokens tokens;
  const Located *instances;
  const Bindings *checked;
  Nat left;
  const Located *records;
  if (utf8_error(source, &position)) return fail_at(failure, position, eUtf8);
  if (!lex(fuel_for(source), source, &tokens, failure)) return 0;
  if (!parse_program(fuel_for(source), work_budget_from(65, source), depth_fuel_from(0, 0, source), NULL, NULL,
                     tokens, &instances, &checked, &left, failure))
    return 0;
  if (!project_records(left, instances, &records, failure)) return 0;
  Printer printer = {output_fuel_from(0, source), builder_new()};
  if (!emit_text(&printer, jHeader, failure)) return 0;
  if (!print_instances(&printer, 1, instances, records == NULL ? jEnd : text_of_cstring("]"), failure))
    return 0;
  if (records != NULL && !print_records(&printer, records, failure)) return 0;
  *output = builder_text(&printer.output);
  return 1;
}

int check_definitions(Text source, const Bindings **environment, Failure *failure) {
  Nat position;
  Tokens tokens;
  const Located *instances;
  Nat left;
  if (utf8_error(source, &position)) return fail_at(failure, position, eUtf8);
  if (!lex(fuel_for(source), source, &tokens, failure)) return 0;
  return parse_program(fuel_for(source), work_budget_from(65, source), depth_fuel_from(0, 0, source), NULL, NULL,
                       tokens, &instances, environment, &left, failure);
}
