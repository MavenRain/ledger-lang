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

/* A checked instance keeps the source byte of its definition for print
   errors. NULL is the end. */
typedef struct Located Located;
struct Located {
  Nat position;
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

static Val term_side(Tokens term) { return (Val){.kind = VAL_TERM, .term = term}; }

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
  if (!parse_type(fuel, 1, environment, tokens, &a, &after_type, failure)) return 0;
  if (type_level(a) != 0) return fail_at(failure, first_position(tokens), eData);
  const Value *lhs;
  Tokens after_left;
  Nat spent;
  if (!parse_term(fuel, budget, 1, a, environment, after_type, &lhs, &after_left, &spent, NULL, failure)) return 0;
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
  return lift_parsed(budget, parse_type(fuel, 0, environment, tokens, type, rest, failure), left);
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

/* A type definition can name a function type. A parameter hides this name. */
static int named_signature(const Bindings *environment, Tokens tokens, Signature *found) {
  Text name;
  if (!name_of(tokens, &name)) return 0;
  const Binding *item;
  if (!lookup(name, environment, &item)) {
    if (same_text(name, opsTextWritePath()) != 1) return 0;
    *found = write_path_signature();
    return 1;
  }
  switch (item->kind) {
  case BIND_ARROW:
    *found = (Signature){item->params, item->type};
    return 1;
  case BIND_VALUE:
  case BIND_TYPE:
  case BIND_FUN:
  case BIND_CLOSURE: return 0;
  }
  return 0;
}

/* The type of a parameter can also be the name of a function type that has
   no type parameter. The argument of this parameter is a function. */
static int parameter_type(Fuel fuel, const Bindings *environment, Tokens tokens, const LType **type, Tokens *rest,
                          Failure *failure) {
  if (fuel == 0) return fail_at(failure, first_position(tokens), eFuel);
  if (mark_of(tokens) == 40) {
    Tokens inside;
    if (!parameter_type(fuel - 1, environment, drop_token(tokens), type, &inside, failure)) return 0;
    return close_parsed(inside, rest, failure);
  }
  Signature found;
  if (!named_signature(environment, tokens, &found)) return parse_type(fuel, 0, environment, tokens, type, rest, failure);
  if (has_type_param(found.params)) return fail_at(failure, first_position(tokens), eData);
  *type = arrow_type(found.params, found.result);
  *rest = drop_token(tokens);
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

static Nat param_count(const Params *params) {
  Nat count = 0;
  for (const Params *cell = params; cell != NULL; cell = cell->tail) count++;
  return count;
}

/* Prefixing a named signature moves its neutral parameter positions. A
   closed side and the local scopes of function parameter types stay intact. */
static Token shift_marker(Nat offset, Token token) {
  Nat index;
  if (token.kind != TOKEN_IDENTIFIER || !marker_index(token.text, &index)) return token;
  token.text = marker_name(offset + index);
  return token;
}

static Tokens shift_markers(Nat offset, Tokens tokens) {
  Token *items = arena_alloc(sizeof *items * (tokens.size + 1));
  for (Nat index = 0; index < tokens.size; index++) items[index] = shift_marker(offset, tokens.items[index]);
  return (Tokens){items, tokens.size};
}

static Val shift_eq_side(Nat offset, Val side) {
  switch (side.kind) {
  case VAL_CLOSED: return side;
  case VAL_VAR: return var_side(offset + side.index);
  case VAL_TERM: return term_side(shift_markers(offset, side.term));
  }
  return side;
}

static const LType *shift_eq_result(Nat offset, const LType *result) {
  const LType *a;
  Val lhs;
  Val rhs;
  if (!sides_of(result, &a, &lhs, &rhs)) return result;
  return eq_type(a, shift_eq_side(offset, lhs), shift_eq_side(offset, rhs));
}

static const Params *shift_eq_params(Nat offset, const Params *params) {
  if (params == NULL) return NULL;
  return param_cons((Param){params->head.name, shift_eq_result(offset, params->head.type)},
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
static int marker_for(Text name, const Params *done, Nat *found, Nat *index) {
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

/* A computed side renames each value parameter to its marker. It cannot
   name an earlier definition or hold an inline function. */
static int mark_side(const Bindings *environment, const Params *done, Tokens tokens, Tokens *marked) {
  Token *items = arena_alloc(sizeof *items * (tokens.size + 1));
  for (Nat at = 0; at < tokens.size; at++) {
    Token head = tokens.items[at];
    Nat found;
    Nat level;
    const Binding *item;
    if (head.kind == TOKEN_IDENTIFIER && marker_for(head.text, done, &found, &level)) {
      if (!found) return 0;
      head.text = marker_name(level);
    } else if (head.kind == TOKEN_IDENTIFIER) {
      if (lookup(head.text, environment, &item)) return 0;
      if (same_text(head.text, sfun) == 1) return 0;
    }
    items[at] = head;
  }
  *marked = (Tokens){items, tokens.size};
  return 1;
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
   as `(some n)`. A function type with type parameters cannot have one. */
static int computed_side(Fuel fuel, const LType *a, const Bindings *environment, const Params *done, Tokens tokens,
                         Val *side, Tokens *rest, Nat *left, Failure *failure) {
  Tokens term;
  if (!mark_side(environment, done, atom_of(0, tokens), &term)) return fail_at(failure, first_position(tokens), eTerm);
  if (has_type_param(done) == 1) return fail_at(failure, first_position(tokens), eTerm);
  const Value *value;
  Tokens after;
  Nat remaining;
  if (!parse_term(fuel, 1, 1, a, binding_cons(check_marker(), marker_bindings(done, environment)), term, &value,
                  &after, &remaining, NULL, failure))
    return 0;
  *side = term_side(term);
  *rest = skip_atom(0, tokens);
  *left = remaining;
  return 1;
}

/* A side of an equality in a function type is the name of a value parameter
   of type A, an atom that names no value parameter and applies no function,
   or a computed side. A closed side keeps its canonical JSON text. */
static int eq_side(Fuel fuel, const LType *a, const Bindings *environment, const Params *done, Tokens tokens,
                   Val *side, Tokens *rest, Nat *left, Failure *failure) {
  if (neutral_side(a, done, tokens, side)) {
    *rest = drop_token(tokens);
    *left = 1;
    return 1;
  }
  if (names_param(done, atom_of(0, tokens)) == 1)
    return computed_side(fuel, a, environment, done, tokens, side, rest, left, failure);
  const Value *value;
  if (!parse_term(fuel, 1, 1, a, hide_params(done, environment), tokens, &value, rest, left, NULL, failure)) return 0;
  Failure printing;
  Text text;
  if (!printed_text(fuel, value, &text, &printing)) return fail_at(failure, first_position(tokens), printing.message);
  *side = closed_side(text);
  return 1;
}

/* `Eq A x y` as the result of a function type. A is a data type. The
   definition checks the body with neutral sides, so `refl` needs the same
   parameter or the same closed value on both sides. */
static int eq_result(Fuel fuel, const Bindings *environment, const Params *done, Tokens tokens, const LType **type,
                     Tokens *rest, Failure *failure) {
  const LType *a;
  Tokens after_type;
  if (!parse_type(fuel, 1, environment, tokens, &a, &after_type, failure)) return 0;
  if (type_level(a) != 0) return fail_at(failure, first_position(tokens), eData);
  Val lhs;
  Val rhs;
  Tokens after_left;
  Nat spent;
  if (!eq_side(fuel, a, environment, done, after_type, &lhs, &after_left, &spent, failure)) return 0;
  if (!eq_side(fuel, a, environment, done, after_left, &rhs, rest, &spent, failure)) return 0;
  *type = eq_type(a, lhs, rhs);
  return 1;
}

/* The type of a parameter. A proof parameter `(e : Eq A x y)` can name
   earlier value parameters of type A as its sides (step D2b), also inside a
   computed side (step D4b). */
static int param_declared(Fuel fuel, const Bindings *environment, const Params *done, Tokens tokens,
                          const LType **type, Tokens *rest, Failure *failure) {
  if (is_word(sEq, tokens) == 1) return eq_result(fuel, environment, done, drop_token(tokens), type, rest, failure);
  return parameter_type(fuel, environment, tokens, type, rest, failure);
}

static int parse_param(Fuel fuel, const Bindings *environment, const Params *done, Tokens tokens, Param *item,
                       Tokens *rest, Failure *failure) {
  Text name;
  if (!name_of(drop_token(tokens), &name)) return fail_at(failure, first_position(tokens), eFun);
  Tokens declared = drop_token(drop_token(drop_token(tokens)));
  const LType *type;
  Tokens after;
  if (!param_declared(fuel, environment, done, declared, &type, &after, failure)) return 0;
  if (!(is_arrow_type(type) == 1 || type_level(type) == 0 || same_type(type, &universe_zero) == 1))
    return fail_at(failure, first_position(declared), eData);
  *item = (Param){name, type};
  return close_parsed(after, rest, failure);
}

/* `(x : A) -> ... -> B` with data types. A data type B cannot refer to a
   value parameter. An equality B = `Eq A x y` can name value parameters as
   its sides, and so can the type of a proof parameter. A type parameter
   `(A : Type 0)` comes before each value parameter, and the later types and
   B can refer to it. Its name is not a reserved name. Parameters hide outer
   names in subsequent type annotations. The name of a function type can end
   the chain. Its parameters follow the earlier ones. */
static int parse_signature(Fuel fuel, const Bindings *environment, const Params *done, Tokens tokens,
                           Signature *found, Tokens *rest, Failure *failure) {
  if (fuel == 0) return fail_at(failure, first_position(tokens), eFuel);
  Fuel more = fuel - 1;
  if (starts_param(tokens) != 1) {
    if (mark_of(tokens) == 40) {
      Tokens inside;
      if (!parse_signature(more, environment, done, drop_token(tokens), found, &inside, failure)) return 0;
      return close_parsed(inside, rest, failure);
    }
    Signature named;
    const LType *result;
    if (named_signature(environment, tokens, &named)) {
      if (has_value_param(done) == 1 && has_type_param(named.params) == 1)
        return fail_at(failure, first_position(tokens), eTypeParam);
      Nat offset = param_count(done);
      *found = (Signature){reverse_params_onto(shift_eq_params(offset, named.params), done),
                           shift_eq_result(offset, named.result)};
      *rest = drop_token(tokens);
      return 1;
    }
    if (is_word(sEq, tokens) == 1) {
      if (!eq_result(more, environment, done, drop_token(tokens), &result, rest, failure)) return 0;
      *found = (Signature){reverse_params_onto(NULL, done), result};
      return 1;
    }
    if (!parse_type(more, 0, environment, tokens, &result, rest, failure)) return 0;
    if (type_level(result) != 0) return fail_at(failure, first_position(tokens), eData);
    *found = (Signature){reverse_params_onto(NULL, done), result};
    return 1;
  }
  Param item;
  Tokens after;
  if (!parse_param(more, environment, done, tokens, &item, &after, failure)) return 0;
  if (is_type_param(item) == 1 && reserved_param(item) == 1)
    return fail_at(failure, first_position(drop_token(tokens)), eReserved);
  if (is_type_param(item) == 1 && has_value_param(done) == 1)
    return fail_at(failure, first_position(drop_token(tokens)), eTypeParam);
  if (mark_of(after) != 62) return fail_at(failure, first_position(after), eDef);
  return parse_signature(more, bind_params(param_cons(item, NULL), NULL, environment), param_cons(item, done),
                         drop_token(after), found, rest, failure);
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
static int parse_binders(Fuel fuel, const Bindings *environment, const Bindings *renames, const Params *declared,
                         const Params *done, Tokens tokens, const Params **binders, Tokens *rest, Failure *failure) {
  if (fuel == 0) return fail_at(failure, first_position(tokens), eFuel);
  Fuel more = fuel - 1;
  if (declared == NULL) {
    if (mark_of(tokens) != 63) return fail_at(failure, first_position(tokens), eFun);
    *binders = reverse_params_onto(NULL, done);
    *rest = drop_token(tokens);
    return 1;
  }
  if (mark_of(tokens) == 63 && is_word(sfun, drop_token(tokens)) == 1) {
    Tokens next = drop_token(drop_token(tokens));
    if (done == NULL) return fail_at(failure, first_position(tokens), eFun);
    if (starts_param(next) != 1) return fail_at(failure, first_position(next), eFun);
    return parse_binders(more, environment, renames, declared, done, next, binders, rest, failure);
  }
  if (starts_param(tokens) != 1) return fail_at(failure, first_position(tokens), eFun);
  Param item;
  Tokens after;
  if (!parse_param(more, environment, done, tokens, &item, &after, failure)) return 0;
  if (reserved_name(item.name) == 1) return fail_at(failure, first_position(drop_token(tokens)), eReserved);
  if (param_named(item.name, done) == 1) return fail_at(failure, first_position(drop_token(tokens)), eDuplicate);
  if (same_type(subst_type(renames, declared->head.type), item.type) != 1)
    return fail_at(failure, first_position(tokens), eFun);
  return parse_binders(more, bind_params(param_cons(item, NULL), NULL, environment),
                       rename_param(declared->head, item.name, renames), declared->tail, param_cons(item, done), after,
                       binders, rest, failure);
}

/* A function definition checks its body once. It is not an instance. */
static int parse_function(Fuel fuel, Nat budget, Text name, const Bindings *environment, Tokens tokens, Binding *item,
                          Tokens *rest, Failure *failure) {
  Signature found;
  Tokens after_type;
  if (!parse_signature(fuel, environment, NULL, tokens, &found, &after_type, failure)) return 0;
  Tokens after_assign;
  if (!expect_mark(61, after_type, &after_assign, failure)) return 0;
  if (is_word(sfun, after_assign) != 1) return fail_at(failure, first_position(after_assign), eFun);
  const Params *binders;
  Tokens body;
  if (!parse_binders(fuel, environment, NULL, found.params, NULL, drop_token(after_assign), &binders, &body, failure))
    return 0;
  const LType *result = subst_type(param_renames(found.params, binders, NULL), found.result);
  const Value *value;
  Nat left;
  const Term *term = NULL;
  if (!parse_term(fuel, budget, 0, result,
                  binding_cons(body_marker(param_count(binders)), bind_params(binders, NULL, environment)), body,
                  &value, rest, &left, &term, failure))
    return 0;
  *item = (Binding){
      .kind = BIND_FUN, .name = name, .type = result, .params = binders, .body = taken_tokens(body, *rest), .term = term};
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
    return lift_parsed(budget, parse_function(fuel, budget, name, environment, after_colon, item, rest, failure),
                       left);
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
    if (!parse_signature(fuel, environment, NULL, after_assign, &found, rest, failure)) return 0;
    if (type_level(type) != 1 + has_type_param(found.params))
      return fail_at(failure, first_position(after_assign), eUniverse);
    *item = (Binding){.kind = BIND_ARROW, .name = name, .type = found.result, .params = found.params};
    *left = spent;
    return 1;
  }
  const LType *inner;
  if (!parse_type(fuel, 0, environment, after_assign, &inner, rest, failure)) return 0;
  if (type_level(type) != type_level(inner) + 1) return fail_at(failure, first_position(after_assign), eUniverse);
  *item = (Binding){.kind = BIND_TYPE, .name = name, .type = type, .defined = inner};
  *left = spent;
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

static const Located *located_cons(Nat position, const Value *value, const Located *tail) {
  Located *cell = arena_alloc(sizeof *cell);
  *cell = (Located){position, value, tail};
  return cell;
}

/* Type definitions, names of function types, proofs and Query values are
   not instances, so the output omits them. */
static const Located *record_instance(Nat position, Binding item, const Located *done) {
  const LType *a;
  Val lhs;
  Val rhs;
  switch (item.kind) {
  case BIND_VALUE:
    if (is_query_type(item.type) == 1 || sides_of(item.type, &a, &lhs, &rhs)) return done;
    return located_cons(position, instance_value(item.name, item.type, item.value), done);
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
    reversed = located_cons(cell->position, cell->value, reversed);
  return reversed;
}

static int parse_program(Fuel fuel, Nat budget, Fuel checking_fuel, const Bindings *environment, const Located *done,
                         Tokens tokens, const Located **instances, const Bindings **checked, Failure *failure) {
  if (fuel == 0) return fail_at(failure, first_position(tokens), eFuel);
  if (tokens.size == 0) return fail_at(failure, 0, eDef);
  Token head = tokens.items[0];
  if (head.kind == TOKEN_PUNCTUATION && head.number == 0) {
    *instances = reverse_located(done);
    *checked = environment;
    return 1;
  }
  if (head.kind != TOKEN_IDENTIFIER || same_text(head.text, sdef) != 1) return fail_at(failure, head.position, eDef);
  Binding item;
  Tokens rest;
  Nat left;
  if (!parse_definition(checking_fuel, budget, environment, drop_token(tokens), &item, &rest, &left, failure)) return 0;
  return parse_program(fuel - 1, left, checking_fuel, binding_cons(item, environment),
                       record_instance(head.position, item, done), rest, instances, checked, failure);
}

/* A print error reports the first byte of the definition being printed. */
static int print_instances(Printer *printer, Nat first, const Located *instances, Failure *failure) {
  Failure printing;
  for (const Located *cell = instances; cell != NULL; cell = cell->tail) {
    if (!emit_text(printer, separator(first), &printing)) return fail_at(failure, cell->position, printing.message);
    if (!print_value(printer, cell->value, &printing)) return fail_at(failure, cell->position, printing.message);
    first = 0;
  }
  return emit_text(printer, jEnd, failure);
}

Text error_text(Nat position, Text message) {
  Printer printer = {fuel_for(message), builder_new()};
  Failure ignored;
  builder_push(&printer.output, 34);
  if (!quote_bytes(&printer, message, &ignored)) return jNull;
  return append_text(jError, append_text(number_text(position), append_text(jMessage,
                     append_text(builder_text(&printer.output), jErrorEnd))));
}

int compile_program(Text source, Text *output, Failure *failure) {
  Nat position;
  Tokens tokens;
  const Located *instances;
  const Bindings *checked;
  if (utf8_error(source, &position)) return fail_at(failure, position, eUtf8);
  if (!lex(fuel_for(source), source, &tokens, failure)) return 0;
  if (!parse_program(fuel_for(source), work_budget_from(65, source), depth_fuel_from(0, 0, source), NULL, NULL,
                     tokens, &instances, &checked, failure))
    return 0;
  Printer printer = {output_fuel_from(0, source), builder_new()};
  if (!emit_text(&printer, jHeader, failure)) return 0;
  if (!print_instances(&printer, 1, instances, failure)) return 0;
  *output = builder_text(&printer.output);
  return 1;
}

int check_definitions(Text source, const Bindings **environment, Failure *failure) {
  Nat position;
  Tokens tokens;
  const Located *instances;
  if (utf8_error(source, &position)) return fail_at(failure, position, eUtf8);
  if (!lex(fuel_for(source), source, &tokens, failure)) return 0;
  return parse_program(fuel_for(source), work_budget_from(65, source), depth_fuel_from(0, 0, source), NULL, NULL,
                       tokens, &instances, environment, failure);
}
