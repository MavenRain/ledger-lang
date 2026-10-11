/* The syntax tree of a checked body (step D3 of docs/DEPENDENT-TYPES.md):
   constructors, structural equality and the printer. The printer gives the
   token text of the source (tokens_text), so a term and its source tokens
   print the same. */
#include "ledger.h"

static const Term *make_term(Term term) {
  Term *made = arena_alloc(sizeof(Term));
  *made = term;
  return made;
}

const Terms *terms_item(const Term *head, const Terms *tail) {
  Terms *item = arena_alloc(sizeof(Terms));
  *item = (Terms){head, tail};
  return item;
}

const TermTypes *term_types_item(TermType head, const TermTypes *tail) {
  TermTypes *item = arena_alloc(sizeof(TermTypes));
  *item = (TermTypes){head, tail};
  return item;
}

const Term *term_number(Nat position, Nat cost, Nat number) {
  return make_term((Term){.tag = TERM_NUMBER, .position = position, .cost = cost, .number = number});
}

const Term *term_string(Nat position, Nat cost, Text text) {
  return make_term((Term){.tag = TERM_STRING, .position = position, .cost = cost, .name = text});
}

const Term *term_var(Nat position, Nat cost, Text name, Nat index) {
  return make_term((Term){.tag = TERM_VAR, .position = position, .cost = cost, .index = index, .name = name});
}

/* TERM_NAME, TERM_APPLY, TERM_PARTIAL and TERM_CONSTRUCT. */
const Term *term_named(TermTag tag, Nat position, Nat cost, Text name, const TermTypes *types, const Terms *args) {
  return make_term((Term){.tag = tag, .position = position, .cost = cost, .name = name, .types = types, .args = args});
}

/* TERM_APPLY and TERM_PARTIAL with a callee, and TERM_CONSTRUCT with
   callee NULL. tokens is the argument span and end the position after the
   argument list. */
const Term *term_call(TermTag tag, Nat position, Nat cost, Tokens tokens, Nat end, Text name, const Term *callee,
                      const TermTypes *types, const Terms *args) {
  return make_term((Term){.tag = tag,
                          .position = position,
                          .cost = cost,
                          .name = name,
                          .callee = callee,
                          .types = types,
                          .args = args,
                          .tokens = tokens,
                          .end = end});
}

/* TERM_FUN: tokens is the binder span. */
const Term *term_fun(Nat position, Nat cost, Tokens tokens, const TermTypes *binders, const Term *body) {
  return make_term((Term){.tag = TERM_FUN,
                          .position = position,
                          .cost = cost,
                          .types = binders,
                          .args = terms_item(body, NULL),
                          .tokens = tokens});
}

/* TERM_GROUP, TERM_REFL and the keyword forms. */
const Term *term_form(TermTag tag, Nat position, Nat cost, const Terms *args) {
  return make_term((Term){.tag = tag, .position = position, .cost = cost, .args = args});
}

/* TERM_BODY: the span of a body and its term (NULL when parse_term built
   none). The cost is the cost of the callee. */
const Term *term_body(Tokens tokens, const Term *callee) {
  return make_term((Term){.tag = TERM_BODY,
                          .position = first_position(tokens),
                          .cost = callee != NULL ? callee->cost : 0,
                          .callee = callee,
                          .tokens = tokens});
}

Tokens term_tokens(const Term *term) { return term != NULL && term->tag == TERM_BODY ? term->tokens : (Tokens){0}; }

/* A binder or a type argument compares by its resolved type. */
static Nat same_term_types(const TermTypes *left, const TermTypes *right) {
  for (; left != NULL && right != NULL; left = left->tail, right = right->tail)
    if (!same_type(left->head.identity != NULL ? left->head.identity : left->head.type,
                   right->head.identity != NULL ? right->head.identity : right->head.type))
      return 0;
  return left == NULL && right == NULL;
}

Nat same_terms(const Terms *left, const Terms *right) {
  for (; left != NULL && right != NULL; left = left->tail, right = right->tail)
    if (!same_term(left->head, right->head)) return 0;
  return left == NULL && right == NULL;
}

static Nat same_callee(const Term *left, const Term *right) {
  if (left->callee != NULL && right->callee != NULL) return same_term(left->callee, right->callee);
  if (left->callee != NULL && left->callee->tag != TERM_NAME) return 0;
  if (right->callee != NULL && right->callee->tag != TERM_NAME) return 0;
  return same_text(left->name, right->name);
}

/* A variable compares by its parameter position, so the name of the
   parameter does not count. The position and the cost do not count. A
   TERM_BODY with a callee compares as its callee (the span does not count). */
Nat same_term(const Term *left, const Term *right) {
  if (left->tag == TERM_BODY && left->callee != NULL) return same_term(left->callee, right);
  if (right->tag == TERM_BODY && right->callee != NULL) return same_term(left, right->callee);
  if (left->tag != right->tag) return 0;
  switch (left->tag) {
    case TERM_NUMBER: return left->number == right->number;
    case TERM_STRING: return same_text(left->name, right->name);
    case TERM_VAR: return left->index == right->index;
    case TERM_NAME:
    case TERM_CONSTRUCT:
      return same_text(left->name, right->name) && same_term_types(left->types, right->types) &&
             same_terms(left->args, right->args);
    case TERM_APPLY:
    case TERM_PARTIAL:
      return same_callee(left, right) && same_term_types(left->types, right->types) && same_terms(left->args, right->args);
    case TERM_FUN: return same_term_types(left->types, right->types) && same_terms(left->args, right->args);
    case TERM_GROUP:
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
    case TERM_UNFOLD_VALUE: return same_terms(left->args, right->args);
    case TERM_BODY: return 1;
  }
  return 0;
}

/* The keyword of a form. A tag without a keyword gives the end text. */
static Text term_keyword(TermTag tag) {
  switch (tag) {
    case TERM_NUMBER:
    case TERM_STRING:
    case TERM_GROUP:
    case TERM_VAR:
    case TERM_NAME:
    case TERM_APPLY:
    case TERM_PARTIAL:
    case TERM_CONSTRUCT:
    case TERM_BODY: return text_end();
    case TERM_FUN: return sfun;
    case TERM_REFL: return srefl;
    case TERM_FIRST: return sfirst;
    case TERM_SECOND: return ssecond;
    case TERM_SYMM: return ssymm;
    case TERM_TRANS: return strans;
    case TERM_EITHER: return seither;
    case TERM_PURE: return spure;
    case TERM_MAP: return smap;
    case TERM_BIND: return sbind;
    case TERM_FILTER: return sfilter;
    case TERM_FOLD:
    case TERM_FOLD_VALUE: return sfold;
    case TERM_UNFOLD:
    case TERM_UNFOLD_VALUE: return sunfold;
  }
  return text_end();
}

static void emit_token(TextBuilder *builder, TokenKind kind, Nat number, Text text) {
  builder_append(builder, token_text((Token){kind, 0, number, text}));
}

static void emit_mark(TextBuilder *builder, Nat mark) { emit_token(builder, TOKEN_PUNCTUATION, mark, text_end()); }

static void emit_term(TextBuilder *builder, const Term *term);

static void emit_terms(TextBuilder *builder, const Terms *terms) {
  for (; terms != NULL; terms = terms->tail) emit_term(builder, terms->head);
}

static void emit_types(TextBuilder *builder, const TermTypes *types) {
  for (; types != NULL; types = types->tail) builder_append(builder, tokens_text(types->head.source));
}

/* A binder prints as ( name : type ). */
static void emit_binders(TextBuilder *builder, const TermTypes *binders) {
  for (; binders != NULL; binders = binders->tail) {
    emit_mark(builder, 40);
    emit_token(builder, TOKEN_IDENTIFIER, 0, binders->head.name);
    emit_mark(builder, 58);
    builder_append(builder, tokens_text(binders->head.source));
    emit_mark(builder, 41);
  }
}

static void emit_term(TextBuilder *builder, const Term *term) {
  switch (term->tag) {
    case TERM_NUMBER: emit_token(builder, TOKEN_NUMBER, term->number, text_end()); return;
    case TERM_STRING: emit_token(builder, TOKEN_STRING, 0, term->name); return;
    case TERM_GROUP:
      emit_mark(builder, 40);
      emit_terms(builder, term->args);
      emit_mark(builder, 41);
      return;
    case TERM_VAR:
    case TERM_NAME:
    case TERM_APPLY:
    case TERM_PARTIAL:
    case TERM_CONSTRUCT:
      emit_token(builder, TOKEN_IDENTIFIER, 0, term->name);
      emit_types(builder, term->types);
      emit_terms(builder, term->args);
      return;
    case TERM_BODY:
      if (term->callee != NULL) emit_term(builder, term->callee);
      return;
    case TERM_FUN:
      emit_token(builder, TOKEN_IDENTIFIER, 0, term_keyword(term->tag));
      emit_binders(builder, term->types);
      emit_mark(builder, 63);
      emit_terms(builder, term->args);
      return;
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
      emit_token(builder, TOKEN_IDENTIFIER, 0, term_keyword(term->tag));
      emit_terms(builder, term->args);
      return;
  }
}

Text term_text(const Term *term) {
  TextBuilder builder = builder_new();
  emit_term(&builder, term);
  return builder_text(&builder);
}

/* parse_term gives a marker name as TERM_NAME: the marker bindings have no
   count frame (binder_index). marker_vars gives each TERM_NAME or TERM_VAR
   that names the marker i, with no types and no arguments, as a variable
   node with index i. Other nodes are copied only when a child changes. */
static const Terms *marker_var_list(const Terms *terms);

const Term *marker_vars(const Term *term) {
  Nat index;
  if (term == NULL) return NULL;
  if ((term->tag == TERM_NAME || term->tag == TERM_VAR) && term->types == NULL && term->args == NULL &&
      marker_index(term->name, &index))
    return term_var(term->position, term->cost, term->name, index);
  const Term *callee = marker_vars(term->callee);
  const Terms *args = marker_var_list(term->args);
  if (callee == term->callee && args == term->args) return term;
  Term copy = *term;
  copy.callee = callee;
  copy.args = args;
  return make_term(copy);
}

static const Terms *marker_var_list(const Terms *terms) {
  if (terms == NULL) return NULL;
  const Term *head = marker_vars(terms->head);
  const Terms *tail = marker_var_list(terms->tail);
  if (head == terms->head && tail == terms->tail) return terms;
  return terms_item(head, tail);
}

/* term_with_markers gives each TERM_VAR that names the marker i, with i
   less than size and a table item that is not NULL, as table[i] (the
   shift and the rename of D3-s9 part B). The new node keeps the position
   and the cost of the table item. Other nodes are copied only when a child
   changes. term_marker_bound gives 1 plus the largest marker index of a
   TERM_VAR in the term, or 0 if no TERM_VAR names a marker. */
static const Terms *marker_list_with(const Terms *terms, const Term *const *table, Nat size);

const Term *term_with_markers(const Term *term, const Term *const *table, Nat size) {
  Nat index;
  if (term == NULL) return NULL;
  if (term->tag == TERM_VAR && marker_index(term->name, &index) && index < size && table[index] != NULL)
    return table[index];
  const Term *callee = term_with_markers(term->callee, table, size);
  const Terms *args = marker_list_with(term->args, table, size);
  if (callee == term->callee && args == term->args) return term;
  Term copy = *term;
  copy.callee = callee;
  copy.args = args;
  return make_term(copy);
}

static const Terms *marker_list_with(const Terms *terms, const Term *const *table, Nat size) {
  if (terms == NULL) return NULL;
  const Term *head = term_with_markers(terms->head, table, size);
  const Terms *tail = marker_list_with(terms->tail, table, size);
  if (head == terms->head && tail == terms->tail) return terms;
  return terms_item(head, tail);
}

static Nat larger(Nat left, Nat right) { return left > right ? left : right; }

Nat term_marker_bound(const Term *term) {
  Nat index;
  if (term == NULL) return 0;
  Nat bound = term_marker_bound(term->callee);
  if (term->tag == TERM_VAR && marker_index(term->name, &index)) bound = larger(bound, index + 1);
  for (const Terms *at = term->args; at != NULL; at = at->tail) bound = larger(bound, term_marker_bound(at->head));
  return bound;
}
