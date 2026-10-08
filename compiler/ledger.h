/* Shared types of the ledger-lang compiler. */
#ifndef LEDGER_H
#define LEDGER_H

#include <stddef.h>
#include <stdint.h>

/* A natural number. Number tokens stay below 2^30, so no compiler
   computation wraps. Subtraction stops at zero (nat_sub). */
typedef uint32_t Nat;

/* A text is a sequence of Nat items. Most texts hold bytes. A token text
   or a type name can hold larger items. A text never changes after it is
   made, so slices share their items. */
typedef struct {
  const Nat *items;
  Nat size;
} Text;

/* Fuel is the number of steps that remain to a bounded recursion. */
typedef uint64_t Fuel;

/* A failure keeps a source byte offset and a message text. */
typedef struct {
  Nat position;
  Text message;
} Failure;

/* A growable text that collects output in order. */
typedef struct {
  Nat *items;
  Nat size;
  Nat capacity;
} TextBuilder;

/* All compiler memory comes from one arena. The arena lives until exit. */
void *arena_alloc(size_t size);

TextBuilder builder_new(void);
void builder_push(TextBuilder *builder, Nat item);
void builder_append(TextBuilder *builder, Text text);
Text builder_text(const TextBuilder *builder);

/* Writes the failure and returns 0, so a caller can return it directly. */
int fail_at(Failure *failure, Nat position, Text message);

Nat between(Nat lo, Nat hi, Nat x);
Nat nat_sub(Nat a, Nat b);

Text text_end(void);
Text text_of_bytes(const unsigned char *bytes, size_t size);
Text text_of_cstring(const char *bytes);
Text text_one(Nat item);
Text text_byte(Nat item, Text rest);
Nat text_is_end(Text text);
Nat text_head(Text text);
Text text_tail(Text text);
Text text_take(Text text, Nat count);
Text text_drop(Text text, Nat count);
Text reverse_text(Text text);
Text append_text(Text a, Text b);
Nat same_text(Text a, Text b);
Nat text_size(Text text);
Fuel fuel_for(Text text);

/* Returns 1 and writes the offset of the first bad byte when the text is
   not UTF-8. A sequence that the end cuts short reports its lead byte. */
int utf8_error(Text text, Nat *position);
Nat valid_utf8(Text text);

typedef enum {
  TOKEN_IDENTIFIER,
  TOKEN_NUMBER,
  TOKEN_STRING,
  TOKEN_PUNCTUATION
} TokenKind;

/* An identifier or a string keeps its text. A number keeps its value in
   number. A punctuation keeps its mark in number. */
typedef struct {
  TokenKind kind;
  Nat position;
  Nat number;
  Text text;
} Token;

typedef struct {
  const Token *items;
  Nat size;
} Tokens;

Text marker_name(Nat index);
int marker_index(Text name, Nat *index);
Text token_text(Token token);
Text tokens_text(Tokens tokens);
Nat has_marker(Tokens tokens);
Nat token_position(Token token);
Nat first_position(Tokens tokens);

/* A side of an equality type. A closed side keeps the canonical JSON text
   of its value. A neutral side keeps the position of a value parameter. A
   computed side keeps the tokens of an atom. */
typedef enum { VAL_CLOSED, VAL_VAR, VAL_TERM } ValKind;

typedef struct {
  ValKind kind;
  Text text;
  Nat index;
  Tokens term;
} Val;

Nat same_val(Val left, Val right);
Text val_text(Val side);

typedef enum {
  TY_NAT,
  TY_TEXT,
  TY_FLAG,
  TY_VALUE,
  TY_VALUES,
  TY_ATTRS,
  TY_KIND,
  TY_HASH,
  TY_REF,
  TY_SCHEMA,
  TY_OPTION,
  TY_LIST,
  TY_PROD,
  TY_SUM,
  TY_UNIVERSE,
  TY_EQ,
  TY_QUERY,
  TY_ARROW
} LTypeTag;

/* TY_REF and TY_SCHEMA keep name. TY_UNIVERSE keeps level. TY_OPTION,
   TY_LIST, TY_QUERY and TY_EQ keep left. TY_PROD, TY_SUM and TY_ARROW keep
   left and right. TY_EQ keeps its sides in lhs and rhs. */
typedef struct LType LType;
struct LType {
  LTypeTag tag;
  Text name;
  Nat level;
  const LType *left;
  const LType *right;
  Val lhs;
  Val rhs;
};

/* A list of types. NULL is the end. */
typedef struct LTypes LTypes;
struct LTypes {
  const LType *head;
  const LTypes *tail;
};

/* A list of texts. NULL is the end. */
typedef struct Texts Texts;
struct Texts {
  Text head;
  const Texts *tail;
};

/* How a constructor applies to its arguments. PLAN_TAG keeps arguments,
   mode and label. PLAN_RECORD keeps arguments, fields and, when has_tag is
   1, tag. */
typedef enum { PLAN_TAG, PLAN_RECORD } PlanKind;

typedef struct {
  PlanKind kind;
  const LTypes *arguments;
  Nat mode;
  Text label;
  const Texts *fields;
  Nat has_tag;
  Text tag;
} Plan;

typedef enum { FLAG_NO, FLAG_YES } Flag;

typedef enum {
  VALUE_NULL,
  VALUE_FLAG,
  VALUE_NAT,
  VALUE_TEXT,
  VALUE_ITEMS,
  VALUE_ATTRS
} ValueKind;

typedef struct Value Value;
typedef struct Values Values;
typedef struct Attrs Attrs;

/* NULL is the end of a Values list. */
struct Values {
  const Value *head;
  const Values *tail;
};

/* NULL is the end of an Attrs list. */
struct Attrs {
  Text key;
  const Value *value;
  const Attrs *rest;
};

struct Value {
  ValueKind kind;
  Flag flag;
  Nat number;
  Text text;
  const Values *items;
  const Attrs *attrs;
};

Nat has_field(Text key, const Attrs *attrs);

/* lexer.c */
int lex(Fuel fuel, Text source, Tokens *tokens, Failure *failure);

/* json.c: every emitted output item takes one unit of fuel. */
typedef struct {
  Fuel fuel;
  TextBuilder output;
} Printer;

Text number_text(Nat number);
Text separator(Nat first);
int emit_text(Printer *printer, Text text, Failure *failure);
int quote_bytes(Printer *printer, Text text, Failure *failure);
int quoted(Printer *printer, Text text, Failure *failure);
int print_value(Printer *printer, const Value *value, Failure *failure);

/* schema.c: the families of core/schema.def. Only the added families
   (Account on) have plans and schema types. schema_constructor_plan and
   schema_type return 1 and write the answer, or return 0 for none. */
int schema_constructor_plan(Text family, Text name, Plan *plan);
int schema_type(Text name, const LType **type);
Nat schema_reserved_name(Text name);

/* operations.c: the families of core/ops.def. ops_constructor_plan and
   ops_type cover the Type 0 families and the alias Log. ops_query_plan and
   ops_query_answer cover the constructors of the indexed family Query. The
   int functions return 1 and write the answer, or return 0 for none. */
int ops_constructor_plan(Text family, Text name, Plan *plan);
int ops_query_plan(Text name, Plan *plan);
int ops_query_answer(Text name, const LType **type);
int ops_type(Text name, const LType **type);
Nat ops_later_type(Text name);
Nat ops_reserved_name(Text name);

/* Texts of schema.mech and operations.mech. literals.h keeps the texts of
   literals.mech as constants. Each other text is a function with the mech
   name that returns text_of_cstring of its bytes (runtime.c). */
Text sHash(void);
Text sRef(void);
Text sHashOf(void);
Text sRefTo(void);
Text opsTextQuery(void);
Text eQueryIndex(void);
Text kRefKind(void);
Text kRefHash(void);
Text kSchemaTag(void);
Text eIndex(void);
Text eLaterType(void);
Text opsTextWritePath(void);

/* A parameter of a function type. A list of parameters; NULL is the end. */
typedef struct {
  Text name;
  const LType *type;
} Param;

typedef struct Params Params;
struct Params {
  Param head;
  const Params *tail;
};

/* A name of the environment. BIND_VALUE keeps type and value. BIND_TYPE
   keeps the universe in type and the type it stands for in defined.
   BIND_ARROW keeps params and the result in type. BIND_FUN keeps params,
   the result in type and the checked body. BIND_CLOSURE also keeps the
   scope of its function argument. A list of bindings (also a Scope); NULL
   is the end, and the head is the latest binding. */
typedef enum { BIND_VALUE, BIND_TYPE, BIND_ARROW, BIND_FUN, BIND_CLOSURE } BindingKind;

typedef struct Bindings Bindings;

typedef struct {
  BindingKind kind;
  Text name;
  const LType *type;
  const Value *value;
  const LType *defined;
  const Params *params;
  Tokens body;
  const Bindings *scope;
} Binding;

struct Bindings {
  Binding head;
  const Bindings *tail;
};

/* runtime.c: lookup returns 1 and writes the first binding of the name, or
   returns 0 for none. */
int lookup(Text name, const Bindings *environment, const Binding **found);

/* types.c: constructor_plan returns 1 and writes the plan, or returns 0
   for none. */
Nat encodes_null(const LType *ty);
Nat has_arguments(const LTypes *types);
const LTypes *plan_arguments(const Plan *selected);
Text type_name(const LType *ty);
Nat type_level(const LType *ty);
Nat same_type(const LType *a, const LType *b);
int constructor_plan(const LType *ty, Text name, Plan *plan);
Nat is_query_type(const LType *ty);
const Params *arrow_params(const LType *ty);
const LType *arrow_result(const LType *ty);
Nat is_arrow_type(const LType *ty);
const LType *arrow_type(const Params *params, const LType *result);
Nat is_term_type(const LType *ty);
Text unknown_name(const LType *expected, Text name);
Nat primitive_reserved_name(Text name);
Nat form_reserved_name(Text name);
Nat reserved_name(Text name);

/* evaluate.c: a List Value is a Values list, and a missing argument is
   null. The as_ functions return 1 and write the payload when the value
   has that form, or return 0. The build, plan and record functions return
   1 and write the answer, or return 0 and write the failure. */
const Value *argument_head(const Values *args);
const Values *argument_tail(const Values *args);
const Value *argument_second(const Values *args);
const Value *argument_third(const Values *args);
const Value *object_one(Text key, const Value *value);
const Value *object_two(Text a, const Value *x, Text b, const Value *y);
int as_nat(const Value *value, Nat *number);
int as_text(const Value *value, Text *text);
int as_values(const Value *value, const Values **items);
int as_attrs(const Value *value, const Attrs **attrs);
int build_byte(const Values *args, const Value **value, Failure *failure);
int build_prepend(const Values *args, const Value **value, Failure *failure);
int build_field(const Values *args, const Value **value, Failure *failure);
int apply_plan(Nat mode, Text label, const Values *args, const Value **value, Failure *failure);
int record_fields(const Texts *fields, const Values *values, const Attrs **attrs, Failure *failure);
int evaluate_plan(const Plan *selected, const Values *values, const Value **value, Failure *failure);

/* parser.c: a Parsed answer is int 1 with the value and the rest tokens
   written, or 0 with the failure written. expect_mark and close_parsed keep
   no value (the caller keeps its own). kind_binding returns 1 and writes the
   kind, or returns 0 for none. */
int expect_mark(Nat mark, Tokens tokens, Tokens *rest, Failure *failure);
int close_parsed(Tokens tokens, Tokens *rest, Failure *failure);
Nat type_former(Text name);
int kind_binding(const Binding *item, Text *kind);
int parse_kind_index(Fuel fuel, const Bindings *environment, Tokens tokens, Text *kind, Tokens *rest,
                     Failure *failure);
int named_type(Nat position, Text name, const Bindings *environment, Tokens tokens, const LType **type, Tokens *rest,
               Failure *failure);
int data_type(Nat position, const LType *argument, const LType *result, Tokens tokens, const LType **type,
              Tokens *rest, Failure *failure);
int data_types(Nat at, const LType *a, Nat bt, const LType *b, const LType *result, Tokens tokens, const LType **type,
               Tokens *rest, Failure *failure);
int parse_type(Fuel fuel, Nat atom, const Bindings *environment, Tokens tokens, const LType **type, Tokens *rest,
               Failure *failure);

/* checker.c (S4: checker.mech lines 1..614). A checked term keeps its type
   and its value. A unary function argument keeps the parameter name and
   type, the result type, the body tokens and the scope of the definition.
   A Parsed answer follows parser.c; check_synthesized takes the synthesized
   term (the caller passes an error on). sides_of, unary_from and unary_of
   return 1 and write the answer, or return 0 for none. */
typedef struct {
  const LType *type;
  const Value *value;
} Typed;

typedef struct {
  Text name;
  const LType *type;
  const LType *result;
  Tokens body;
  const Bindings *scope;
} Unary;

Nat projection_index(Text name);
const Value *project_value(Nat index, const Value *value);
int project(Nat position, Nat index, Typed found, Tokens tokens, Typed *result, Tokens *rest, Failure *failure);
int check_synthesized(Nat position, const LType *expected, Typed found, Tokens tokens, const Value **value,
                      Tokens *rest, Failure *failure);
Nat synth_form(Text name);
Nat structure_form(Text name);
int sides_of(const LType *ty, const LType **a, Val *lhs, Val *rhs);
Nat is_neutral_side(Val side);
Nat dependent_result(const LType *ty);
Nat dependent_params(const Params *params);
int refl_check(Nat position, const LType *expected, Tokens tokens, const Value **value, Tokens *rest,
               Failure *failure);
int symm_proof(Nat position, Typed found, Tokens tokens, Typed *result, Tokens *rest, Failure *failure);
int trans_proof(Nat position, Typed left, Typed right, Tokens tokens, Typed *result, Tokens *rest,
                Failure *failure);
Binding check_marker(void);
Nat checking_body(const Bindings *environment);
const LTypes *param_types(const Params *params);
Nat is_type_param(Param item);
Nat has_type_param(const Params *params);
Nat has_value_param(const Params *params);
const LType *type_argument(Text name, const Bindings *chosen);
const LType *subst_type(const Bindings *chosen, const LType *ty);
const Params *value_params(const Bindings *chosen, const Params *params);
int type_arguments(Fuel fuel, const Params *params, const Bindings *environment, const Bindings *chosen,
                   Tokens tokens, const Bindings **result, Tokens *rest, Failure *failure);
const Bindings *definition_scope(Text name, const Bindings *environment);
Binding opaque_closure(Text name, const LType *ty);
Binding closure_of_name(Text name, const LType *ty, Text target, const Bindings *caller);
const Value *inline_item(Nat kind, Nat position, const Value *payload);
const Value *inline_token_value(Token token);
const Values *inline_token_values(Tokens tokens);
const Values *inline_names(const Params *params);
const Value *inline_value(const Params *params, Tokens body);
Nat inline_nat(const Value *value);
Text inline_text(const Value *value);
Token inline_token(Nat kind, Nat position, const Value *payload);
const Values *inline_parts(const Value *value);
Token inline_token_of(const Values *parts);
Tokens inline_tokens(const Values *items);
const Params *inline_params(const Values *names, const Params *params);
Binding inline_closure(Text name, const LType *ty, const Value *names, const Values *body, const Bindings *caller);
Fuel type_fuel(Tokens tokens);
Tokens type_tokens_of(const Value *types);
const Values *typed_bound(const Params *params, Tokens tokens, Tokens rest, const Values *values);
Binding bound_binding(const Value *value, Text name, const LType *ty, const Bindings *caller);
const Bindings *bind_bound(const Values *values, const Params *params, const Bindings *caller,
                           const Bindings *scope);
Binding partial_closure(Text name, const LType *ty, Text target, const Values *bound, const Bindings *caller);
Binding bind_param(Text name, const LType *ty, const Value *value, const Bindings *caller);
const Bindings *bind_arguments(const Bindings *caller, const Params *params, const Values *values,
                               const Bindings *environment);
const Bindings *bind_params(const Params *params, const Values *values, const Bindings *environment);
Nat bound_functions(const Params *params, const Values *values);
Nat closes_next(Tokens tokens);
const Params *front_params(const Params *params);
const Params *bound_params(const Params *params, const Params *expected);
const LType *unary_param(Unary op);
const LType *unary_result(Unary op);
Tokens unary_body(Unary op);
const Bindings *unary_environment(Unary op, const Value *value);
int unary_from(const Bindings *scope, const Params *params, const LType *result, Tokens body, Unary *op);
int unary_of(const Bindings *scope, const Binding *item, Unary *op);
int unary_argument(const Bindings *environment, Tokens tokens, Unary *op, Tokens *rest, Failure *failure);

/* checker.c (S5a1: checker.mech lines 615..1012). A Shape keeps the element
   type of Option, List, Sum E and the sequences, and the error type of Sum E.
   A Stepper is the function argument of fold and unfold: the parameters, the
   result type, the body tokens and the scope. A ValueAlgebra keeps the five
   steppers of a fold over Value in constructor order. payload_of, unit_items,
   elements_of and text_of_elements return 1 and write the answer, or 0 for
   none; fields_of and rebuild return 0 with a Failure. */
typedef enum { SHAPE_OPTION, SHAPE_LIST, SHAPE_SUM, SHAPE_SEQUENCE, SHAPE_NONE } ShapeKind;

typedef struct {
  ShapeKind kind;
  const LType *error;
  const LType *element;
} Shape;

typedef struct {
  const Params *params;
  const LType *result;
  Tokens body;
  const Bindings *scope;
} Stepper;

typedef struct {
  Stepper on_nat;
  Stepper on_flag;
  Stepper on_text;
  Stepper on_items;
  Stepper on_attrs;
} ValueAlgebra;

Shape shape_of(const LType *ty);
Nat shape_code(Nat form, const LType *ty);
const LType *shape_element(const LType *ty);
const LType *shape_with(const LType *ty, const LType *element);
const Value *some_value(const LType *ty, const Value *value);
const Value *pure_value(const LType *ty, const Value *value);
Nat is_null(const Value *value);
Nat is_yes(const Value *value);
Nat sum_left(const Value *value);
const Values *items_of(const Value *value);
const Values *append_values(const Values *front, const Values *back);
int payload_of(const LType *ty, const LType *element, const Value *value, const Value **payload);
const Value *step_one(Nat form, const LType *ty, const Value *source, const Value *result);
const Values *step_items(Nat form, const Value *item, const Value *result, const Values *rest);
Nat structure_fits(Nat form, const LType *ty, Unary op);
const LType *structure_source(Nat form, const LType *ty, Unary op);
const LType *structure_result(Nat form, const LType *ty);
const Params *stepper_params(Stepper op);
const LType *stepper_result(Stepper op);
Tokens stepper_body(Stepper op);
const Bindings *stepper_environment(Stepper op, const Values *values);
int stepper_argument(const Bindings *environment, Tokens tokens, Stepper *op, Tokens *rest, Failure *failure);
Nat same_types(const LTypes *left, const LTypes *right);
Nat carrier_code(const LType *ty);
const Values *text_elements(Text text);
const Values *field_elements(const Attrs *attrs);
const Values *sequence_elements(const Value *value);
int unit_items(Fuel fuel, Nat count, const Values **items);
int elements_of(Fuel fuel, const Value *value, const Values **items);
Nat count_of(const Value *value);
Nat count_values(const Values *items);
int text_of_elements(const Values *items, Text *text);
Text key_of(const Value *item);
int fields_of(const Values *items, const Attrs **attrs, Failure *failure);
int rebuild(const LType *ty, const Values *items, const Value **value, Failure *failure);
Nat fold_fits(const LType *ty, const LType *result, Stepper op);
const LType *param_seed(const Params *params);
const LType *unfold_seed(Stepper op);
Nat unfold_fits(const LType *ty, Stepper op);
Stepper algebra_step(Nat index, ValueAlgebra ops);
Nat value_index(const Value *value);
const LType *algebra_param(Nat index, const LType *result);
Nat names_function(const Bindings *environment, Tokens tokens);
const Values *child_elements(const Value *value);
const Value *algebra_input(const Value *value, const Values *results);
const LType *value_layer(const LType *seed);
Nat unfold_value_fits(Stepper op);

/* checker.c (S5a2: checker.mech lines 1013..1363). A Grown keeps the values
   that an unfold into Value built and the number of applications that
   remain. A Worked answer is int 1 with the value, the rest tokens and the
   remaining budget written, or 0 with the failure written; check_worked
   takes the worked term (the caller passes an error on). inline_binder and
   inline_binders follow parser.c. param_level and body_level give Option
   (Option Nat): the int is the outer some, found the inner some, and index
   the level. The other int functions return 1 and write the answer, or 0
   for none. */
typedef struct {
  const Values *items;
  Nat limit;
} Grown;

const LType *inline_result(Nat mode, const LType *expected, const Params *params);
int inline_binder(Fuel fuel, const Bindings *environment, const Bindings *seen, Tokens tokens, Param *binder,
                  Tokens *rest, Failure *failure);
int inline_binders(Fuel fuel, const Bindings *environment, const Bindings *seen, Tokens tokens, const Params **binders,
                   Tokens *body, Failure *failure);
Nat layer_index(const Value *layer);
const Value *layer_payload(const Value *layer);
const Values *grown_items(Grown built);
Nat grown_limit(Grown built);
const Value *grown_head(Grown built);
Grown grown_leaf(const Value *value, Nat limit);
int lift_parsed(Nat budget, int parsed, Nat *left);
int check_worked(Nat position, const LType *expected, Typed found, Tokens tokens, Nat budget, const Value **value,
                 Tokens *rest, Nat *left, Failure *failure);
Binding body_marker(Nat count);
Tokens skip_atom(Nat depth, Tokens tokens);
int param_level(Text name, Nat count, const Bindings *environment, Nat *found, Nat *index);
int body_level(Text name, const Bindings *environment, Nat *found, Nat *index);
Nat proof_in_scope(Text name, const LType *ty, const Bindings *environment);
int printed_side(Fuel fuel, const Value *value, Val *side);
int argument_text(Fuel fuel, const Bindings *environment, const Value *value, Tokens tokens, Val *side);
int argument_side(Fuel fuel, Nat index, const Bindings *environment, const Params *params, const Values *values,
                  Tokens tokens, Val *side);
int argument_token(Nat index, const Params *params, Tokens tokens, Token *token);
int rename_markers(Fuel fuel, const Bindings *environment, const Params *params, const Values *values, Tokens tokens,
                   Tokens term, Tokens *renamed);
Nat kept_side(Val side);
int instantiate_side(Fuel fuel, const Bindings *environment, const Params *params, const Values *values, Tokens tokens,
                     Val side, Val *result);
int instantiate_result(Fuel fuel, const Bindings *environment, const Params *params, const Values *values,
                       Tokens tokens, const LType *result, const LType **instantiated);
const Params *instantiate_params(Fuel fuel, const Bindings *environment, const Params *params, const Values *values,
                                 Tokens tokens, const Params *remaining);
const Bindings *argument_bindings(Nat index, const Params *params, const Values *values,
                                  const Bindings *environment);

/* program.c: compile_program returns 1 and writes the JSON document, or
   returns 0 and writes the failure. error_text is the JSON of a failure. */
int compile_program(Text source, Text *output, Failure *failure);
Text error_text(Nat position, Text message);

#include "literals.h"

#endif
