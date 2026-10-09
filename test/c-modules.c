#include <assert.h>
#include <stdio.h>
#include <string.h>

#include "../compiler/ledger.h"

static Text text(const char *bytes) {
  return text_of_bytes((const unsigned char *)bytes, strlen(bytes));
}

static void test_runtime(void) {
  Text empty = text_of_bytes((const unsigned char *)"", 0);
  assert(same_text(empty, reverse_text(empty)));
  assert(same_text(text_tail(empty), empty));
  assert(same_text(text_drop(text("abc"), 99), empty));
  assert(same_text(append_text(text("ab"), text("cd")), text("abcd")));
  Nat position;
  assert(valid_utf8(text("\xf0\x9f\x98\x80")));
  assert(utf8_error(text("a\xe2\x82"), &position) && position == 1);
  assert(utf8_error(text("\xed\xa0\x80"), &position) && position == 1);
  assert(utf8_error(text("\xf4\x90\x80\x80"), &position) && position == 1);
  Nat index;
  assert(marker_index(marker_name(300), &index) && index == 300);
  Token a = {TOKEN_IDENTIFIER, 0, 0, text("x")};
  Token b = {TOKEN_STRING, 0, 0, text("x")};
  assert(!same_text(token_text(a), token_text(b)));
  b = a;
  b.position = 99;
  assert(same_text(token_text(a), token_text(b)));
}

static void test_lexer(void) {
  Text source = text("abc 1073741823 \"x\\n\" := -> => ( ) -- comment\r\n");
  Tokens tokens;
  Failure failure;
  assert(lex(fuel_for(source), source, &tokens, &failure));
  assert(tokens.size == 9);
  assert(tokens.items[0].kind == TOKEN_IDENTIFIER && same_text(tokens.items[0].text, text("abc")));
  assert(tokens.items[1].kind == TOKEN_NUMBER && tokens.items[1].number == 1073741823);
  assert(tokens.items[2].kind == TOKEN_STRING && same_text(tokens.items[2].text, text("x\n")));
  const Nat marks[] = {61, 62, 63, 40, 41, 0};
  for (Nat i = 0; i < 6; i++) {
    assert(tokens.items[i + 3].kind == TOKEN_PUNCTUATION);
    assert(tokens.items[i + 3].number == marks[i]);
  }
  assert(tokens.items[8].position == source.size);
  assert(!lex(20, text("1073741824"), &tokens, &failure));
  assert(failure.position == 9 && same_text(failure.message, eNumber));
  assert(!lex(20, text("1foo"), &tokens, &failure));
  assert(failure.position == 1 && same_text(failure.message, eCharacter));
  assert(!lex(20, text("\"\\q\""), &tokens, &failure));
  assert(failure.position == 2 && same_text(failure.message, eEscape));
  assert(!lex(1, text("a"), &tokens, &failure));
  assert(failure.position == 1 && same_text(failure.message, eFuel));
  assert(lex(1, text_end(), &tokens, &failure));
  assert(tokens.size == 1 && tokens.items[0].number == 0);
}

static void test_json(void) {
  Failure failure;
  assert(same_text(number_text(0), text("0")));
  assert(same_text(number_text(1073741823), text("1073741823")));
  Printer printer = {100, builder_new()};
  Text raw = text_of_bytes((const unsigned char *)"\"\n\\\0", 4);
  assert(quoted(&printer, raw, &failure));
  assert(same_text(builder_text(&printer.output), text("\"\\\"\\u000a\\\\\\u0000\"")));
  Printer invalid = {100, builder_new()};
  assert(!quoted(&invalid, text("\xc0\x80"), &failure));
  assert(same_text(failure.message, eUtf8));
  Value number = {.kind = VALUE_NAT, .number = 7};
  Values tail = {&number, NULL};
  Values head = {&number, &tail};
  Value list = {.kind = VALUE_ITEMS, .items = &head};
  Attrs field = {text("n"), &list, NULL};
  Value object = {.kind = VALUE_ATTRS, .attrs = &field};
  Printer exact = {11, builder_new()};
  assert(print_value(&exact, &object, &failure));
  assert(exact.fuel == 0);
  assert(same_text(builder_text(&exact.output), text("{\"n\":[7,7]}")));
  Printer short_budget = {10, builder_new()};
  assert(!print_value(&short_budget, &object, &failure));
  assert(same_text(failure.message, eOutput));
}

static Tokens lexed(const char *bytes) {
  Text source = text(bytes);
  Tokens tokens;
  Failure failure;
  assert(lex(fuel_for(source), source, &tokens, &failure));
  /* The EOF sentinel belongs to the program, not the term's source. */
  assert(tokens.size > 0);
  Token eof = tokens.items[tokens.size - 1];
  assert(eof.kind == TOKEN_PUNCTUATION && eof.number == 0);
  tokens.size -= 1;
  return tokens;
}

static Tokens slice(Tokens tokens, Nat from, Nat to) { return (Tokens){tokens.items + from, to - from}; }

static const Terms *one(const Term *head) { return terms_item(head, NULL); }

static void test_term(void) {
  LType nat = {.tag = TY_NAT};
  LType txt = {.tag = TY_TEXT};
  Tokens nat_source = lexed("Nat");
  Tokens txt_source = lexed("Text");
  const TermTypes *nat_types = term_types_item((TermType){text_end(), 0, &nat, nat_source}, NULL);
  const TermTypes *txt_types = term_types_item((TermType){text_end(), 0, &txt, txt_source}, NULL);
  const Term *n = term_number(0, 1, 7);
  const Term *all[] = {n,
                       term_string(0, 1, text("s")),
                       term_form(TERM_GROUP, 0, 1, one(n)),
                       term_var(0, 1, text("x"), 0),
                       term_named(TERM_NAME, 0, 1, text("xs"), NULL, NULL),
                       term_named(TERM_APPLY, 0, 1, text("f"), nat_types, one(n)),
                       term_named(TERM_PARTIAL, 0, 1, text("f"), nat_types, one(n)),
                       term_fun(0, 1, term_types_item((TermType){text("x"), 0, &nat, nat_source}, NULL), n),
                       term_named(TERM_CONSTRUCT, 0, 1, text("some"), NULL, one(n)),
                       term_form(TERM_REFL, 0, 1, NULL),
                       term_form(TERM_FIRST, 0, 1, one(n)),
                       term_form(TERM_SECOND, 0, 1, one(n)),
                       term_form(TERM_SYMM, 0, 1, one(n)),
                       term_form(TERM_TRANS, 0, 1, terms_item(n, one(n))),
                       term_form(TERM_EITHER, 0, 1, terms_item(n, terms_item(n, one(n)))),
                       term_form(TERM_PURE, 0, 1, one(n)),
                       term_form(TERM_MAP, 0, 1, terms_item(n, one(n))),
                       term_form(TERM_BIND, 0, 1, terms_item(n, one(n))),
                       term_form(TERM_FILTER, 0, 1, terms_item(n, one(n))),
                       term_form(TERM_FOLD, 0, 1, terms_item(n, one(n))),
                       term_form(TERM_FOLD_VALUE, 0, 1, terms_item(n, one(n))),
                       term_form(TERM_UNFOLD, 0, 1, terms_item(n, one(n))),
                       term_form(TERM_UNFOLD_VALUE, 0, 1, terms_item(n, one(n)))};
  Nat count = sizeof(all) / sizeof(all[0]);
  /* TERM_BODY is the last tag and is not in the array: it has no text and
     compares as its callee. */
  assert(count == TERM_BODY);
  for (Nat i = 0; i < count; i++) {
    assert(all[i]->tag == i);
    assert(text_size(term_text(all[i])) > 0);
    for (Nat j = 0; j < count; j++) assert(same_term(all[i], all[j]) == (i == j));
  }
  const Term *carried = term_body(nat_source, n);
  assert(carried->tag == TERM_BODY);
  assert(same_term(carried, n) && same_term(n, carried));
  assert(same_text(term_text(carried), term_text(n)));
  assert(term_tokens(carried).items == nat_source.items && term_tokens(carried).size == nat_source.size);
  assert(term_tokens(NULL).size == 0 && term_tokens(n).size == 0);
  const Term *bare = term_body(nat_source, NULL);
  assert(text_size(term_text(bare)) == 0);
  assert(same_term(bare, term_body(txt_source, NULL)));
  assert(!same_term(bare, n) && !same_term(n, bare));
  /* Equal pairs: the position, the cost and the parameter names do not
     count. Unequal pairs: a field, a type or the number of arguments. */
  assert(same_term(term_number(3, 1, 7), term_number(9, 5, 7)));
  assert(!same_term(term_number(0, 1, 7), term_number(0, 1, 8)));
  assert(same_term(term_var(0, 1, text("x"), 2), term_var(4, 1, text("y"), 2)));
  assert(!same_term(term_var(0, 1, text("x"), 0), term_var(0, 1, text("x"), 1)));
  assert(!same_term(term_string(0, 1, text("a")), term_string(0, 1, text("b"))));
  assert(!same_term(term_named(TERM_NAME, 0, 1, text("a"), NULL, NULL),
                    term_named(TERM_NAME, 0, 1, text("b"), NULL, NULL)));
  assert(!same_term(term_named(TERM_APPLY, 0, 1, text("f"), nat_types, one(n)),
                    term_named(TERM_APPLY, 0, 1, text("f"), txt_types, one(n))));
  assert(!same_term(term_named(TERM_APPLY, 0, 1, text("f"), NULL, one(n)),
                    term_named(TERM_APPLY, 0, 1, text("f"), NULL, terms_item(n, one(n)))));
  assert(!same_term(term_fun(0, 1, nat_types, n), term_fun(0, 1, txt_types, n)));
  assert(!same_term(term_form(TERM_FOLD, 0, 1, one(n)), term_form(TERM_FOLD_VALUE, 0, 1, one(n))));

  /* term_text gives tokens_text of the source. Tokens:
     0 fold 1 ( 2 fun 3 ( 4 x 5 : 6 Nat 7 ) 8 ( 9 acc 10 : 11 Nat 12 ) 13 =>
     14 add 15 x 16 acc 17 ) 18 0 19 xs */
  Tokens folded = lexed("fold (fun (x : Nat) (acc : Nat) => add x acc) 0 xs");
  assert(folded.size == 20);
  const Term *x = term_var(folded.items[15].position, 1, text("x"), 0);
  const Term *acc = term_var(folded.items[16].position, 1, text("acc"), 1);
  assert(x->position == 39 && x->index == 0);
  assert(acc->position == 41 && acc->index == 1);
  const TermTypes *binders =
      term_types_item((TermType){text("x"), folded.items[4].position, &nat, slice(folded, 6, 7)},
                      term_types_item((TermType){text("acc"), folded.items[9].position, &nat, slice(folded, 11, 12)},
                                      NULL));
  const Term *body = term_named(TERM_APPLY, folded.items[14].position, 1, text("add"), NULL, terms_item(x, one(acc)));
  const Term *function = term_form(TERM_GROUP, 5, 1, one(term_fun(6, 1, binders, body)));
  const Term *fold = term_form(TERM_FOLD, 0, 1,
                               terms_item(function, terms_item(term_number(46, 1, 0),
                                                               one(term_named(TERM_NAME, 48, 1, text("xs"), NULL, NULL)))));
  assert(same_text(term_text(fold), tokens_text(folded)));
  assert(same_term(fold, fold));

  /* Tokens: 0 map 1 ( 2 pickK 3 6 4 ) 5 ( 6 pure 7 ( 8 wrap 9 Nat 10 "a" 11 ) 12 ) */
  Tokens mapped = lexed("map (pickK 6) (pure (wrap Nat \"a\"))");
  assert(mapped.size == 13);
  const Term *partial = term_named(TERM_PARTIAL, 5, 1, text("pickK"), NULL, one(term_number(11, 1, 6)));
  const Term *wrapped =
      term_named(TERM_APPLY, 21, 1, text("wrap"),
                 term_types_item((TermType){text_end(), 26, &nat, slice(mapped, 9, 10)}, NULL),
                 one(term_string(30, 1, text("a"))));
  const Term *pure = term_form(TERM_PURE, 15, 1, one(term_form(TERM_GROUP, 20, 1, one(wrapped))));
  const Term *map = term_form(TERM_MAP, 0, 1,
                              terms_item(term_form(TERM_GROUP, 4, 1, one(partial)),
                                         one(term_form(TERM_GROUP, 14, 1, one(pure)))));
  assert(same_text(term_text(map), tokens_text(mapped)));
  assert(!same_text(term_text(map), tokens_text(folded)));

  /* refl, symm, trans, either, first and second print their keywords. */
  Tokens proof = lexed("trans (symm p) (refl) either first q second q");
  const Term *p = term_var(0, 1, text("p"), 0);
  const Term *q = term_var(0, 1, text("q"), 1);
  const Term *proofs = term_form(
      TERM_TRANS, 0, 1,
      terms_item(term_form(TERM_GROUP, 0, 1, one(term_form(TERM_SYMM, 0, 1, one(p)))),
                 terms_item(term_form(TERM_GROUP, 0, 1, one(term_form(TERM_REFL, 0, 1, NULL))),
                            one(term_form(TERM_EITHER, 0, 1,
                                          terms_item(term_form(TERM_FIRST, 0, 1, one(q)),
                                                     one(term_form(TERM_SECOND, 0, 1, one(q)))))))));
  assert(same_text(term_text(proofs), tokens_text(proof)));
}

/* The term of the function name in the bindings, or NULL. The binding term
   is a TERM_BODY (D3-s4), thus this gives its callee. */
static const Term *body_term(const Bindings *environment, const char *name) {
  for (; environment != NULL; environment = environment->tail)
    if (environment->head.kind == BIND_FUN && same_text(environment->head.name, text(name)))
      return environment->head.term->callee;
  return NULL;
}

/* The checked type of the first parameter of the function name, or NULL. */
static const LType *first_param_type(const Bindings *environment, const char *name) {
  for (; environment != NULL; environment = environment->tail)
    if (environment->head.kind == BIND_FUN && same_text(environment->head.name, text(name)))
      return environment->head.params->head.type;
  return NULL;
}

/* The body of nested in test_definitions, with the given indexes of w and z:
   useTwo (fun (y : Nat) (w : Nat) => useOne (fun (z : Nat) => pickK k (pickK w z))) */
static const Term *nested_body(const LType *nat, Tokens nat_source, Nat w, Nat z) {
  const TermTypes *yw = term_types_item((TermType){text("y"), 0, nat, nat_source},
                                        term_types_item((TermType){text("w"), 0, nat, nat_source}, NULL));
  const TermTypes *zs = term_types_item((TermType){text("z"), 0, nat, nat_source}, NULL);
  const Term *inner_pick = term_named(TERM_APPLY, 0, 0, text("pickK"), NULL,
                                      terms_item(term_var(0, 0, text("w"), w), one(term_var(0, 0, text("z"), z))));
  const Term *outer_pick =
      term_named(TERM_APPLY, 0, 0, text("pickK"), NULL,
                 terms_item(term_var(0, 0, text("k"), 0), one(term_form(TERM_GROUP, 0, 0, one(inner_pick)))));
  const Term *inner_fun = term_form(TERM_GROUP, 0, 0, one(term_fun(0, 0, zs, outer_pick)));
  const Term *outer_fun = term_form(
      TERM_GROUP, 0, 0, one(term_fun(0, 0, yw, term_named(TERM_APPLY, 0, 0, text("useOne"), NULL, one(inner_fun)))));
  return term_named(TERM_APPLY, 0, 0, text("useTwo"), NULL, one(outer_fun));
}

/* check_definitions gives a term for each function body. The text of the
   term is the text of the body tokens. The binders of an inline fun
   continue after the function parameters, and a fun inside it continues
   after its binders. */
static void test_definitions(void) {
  const char *source =
      "def xs : List Nat := cons 4 (cons 7 nil)\n"
      "def One : Type 0 := (n : Nat) -> Nat\n"
      "def Two : Type 0 := (k : Nat) -> (n : Nat) -> Nat\n"
      "def pickK : (k : Nat) -> (n : Nat) -> Nat := fun (k : Nat) (n : Nat) => k\n"
      "def twoList : (a : Nat) -> (b : Nat) -> List Nat := fun (a : Nat) (b : Nat) => cons a (cons (pickK b 5) nil)\n"
      "def useOne : (g : One) -> Nat := fun (g : One) => g 3\n"
      "def useTwo : (h : Two) -> Nat := fun (h : Two) => h 1 2\n"
      "def viaName : (k : Nat) -> Nat := fun (k : Nat) => useTwo pickK\n"
      "def viaPartial : (k : Nat) -> Nat := fun (k : Nat) => useOne (pickK k)\n"
      "def nested : (k : Nat) -> (j : Nat) -> Nat := fun (k : Nat) (j : Nat) => useTwo (fun (y : Nat) (w : Nat) => "
      "useOne (fun (z : Nat) => pickK k (pickK w z)))\n"
      "def r1 : List Nat := twoList 1 2\n"
      "def r4 : Nat := nested 6 0\n";
  const Bindings *environment = NULL;
  Failure failure;
  assert(check_definitions(text(source), &environment, &failure) == 1);
  Nat checked = 0;
  for (const Bindings *item = environment; item != NULL; item = item->tail) {
    if (item->head.kind != BIND_FUN) continue;
    assert(item->head.term != NULL);
    assert(same_text(term_text(item->head.term), tokens_text(item->head.body)));
    checked++;
  }
  assert(checked == 7);

  assert(body_term(environment, "twoList")->tag == TERM_CONSTRUCT);
  const Term *k = term_var(0, 0, text("k"), 0);
  const Term *by_name =
      term_named(TERM_APPLY, 0, 0, text("useTwo"), NULL, one(term_named(TERM_NAME, 0, 0, text("pickK"), NULL, NULL)));
  assert(same_term(body_term(environment, "viaName"), by_name));
  const Term *by_partial =
      term_named(TERM_APPLY, 0, 0, text("useOne"), NULL,
                 one(term_form(TERM_GROUP, 0, 0, one(term_named(TERM_PARTIAL, 0, 0, text("pickK"), NULL, one(k))))));
  assert(same_term(body_term(environment, "viaPartial"), by_partial));

  /* nested: k and j are 0 and 1, y and w are 2 and 3, z is 4. A fun that
     starts its binders at 0 again gives a different term. */
  LType nat = {.tag = TY_NAT};
  Tokens nat_source = lexed("Nat");
  assert(same_term(body_term(environment, "nested"), nested_body(&nat, nat_source, 3, 4)));
  assert(!same_term(body_term(environment, "nested"), nested_body(&nat, nat_source, 1, 0)));
}

/* Function parameters keep their binder positions when called, partially
   applied, or passed as arguments. Renaming a binder preserves the term;
   choosing another binder changes it, even when its source name matches. */
static void test_function_references(void) {
  const char *source =
      "def One : Type 0 := (n : Nat) -> Nat\n"
      "def Two : Type 0 := (k : Nat) -> (n : Nat) -> Nat\n"
      "def use : (g : One) -> Nat := fun (g : One) => g 3\n"
      "def runG : (g : One) -> Nat := fun (g : One) => g 3\n"
      "def runH : (h : One) -> Nat := fun (h : One) => h 3\n"
      "def passG : (g : One) -> Nat := fun (g : One) => use g\n"
      "def passH : (h : One) -> Nat := fun (h : One) => use h\n"
      "def firstOf : (g : One) -> (h : One) -> Nat := fun (g : One) (h : One) => g 3\n"
      "def secondOf : (h : One) -> (g : One) -> Nat := fun (h : One) (g : One) => g 3\n"
      "def partialG : (g : Two) -> Nat := fun (g : Two) => use (g 1)\n"
      "def partialH : (h : Two) -> Nat := fun (h : Two) => use (h 1)\n"
      "def partialFirst : (g : Two) -> (h : Two) -> Nat := fun (g : Two) (h : Two) => use (g 1)\n"
      "def partialSecond : (h : Two) -> (g : Two) -> Nat := fun (h : Two) (g : Two) => use (g 1)\n"
      "def nestedG : (g : One) -> Nat := fun (g : One) => use (fun (n : Nat) => g n)\n"
      "def nestedH : (h : One) -> Nat := fun (h : One) => use (fun (m : Nat) => h m)\n"
      "def innerG : (n : Nat) -> Nat := fun (n : Nat) => use (fun (g : Nat) => runG (fun (h : Nat) => g))\n";
  const Bindings *environment = NULL;
  Failure failure;
  assert(check_definitions(text(source), &environment, &failure) == 1);
  assert(same_term(body_term(environment, "runG"), body_term(environment, "runH")));
  assert(same_term(body_term(environment, "passG"), body_term(environment, "passH")));
  assert(!same_term(body_term(environment, "firstOf"), body_term(environment, "secondOf")));
  assert(same_term(body_term(environment, "partialG"), body_term(environment, "partialH")));
  assert(!same_term(body_term(environment, "partialFirst"), body_term(environment, "partialSecond")));
  assert(same_term(body_term(environment, "nestedG"), body_term(environment, "nestedH")));
  const Term *call = body_term(environment, "runG");
  assert(call->callee != NULL && call->callee->tag == TERM_VAR && call->callee->index == 0);
  assert(!same_term(call, term_named(TERM_APPLY, 0, 0, text("g"), NULL, call->args)));
  const Term *passed = body_term(environment, "passG");
  assert(passed->args->head->tag == TERM_VAR && passed->args->head->index == 0);
  for (const Bindings *item = environment; item != NULL; item = item->tail)
    if (item->head.kind == BIND_FUN)
      assert(item->head.term != NULL && same_text(term_text(item->head.term), tokens_text(item->head.body)));
}

/* The number of terms in a list. */
static Nat args_count(const Terms *terms) {
  Nat count = 0;
  for (; terms != NULL; terms = terms->tail) count++;
  return count;
}

/* The body of mapK in test_keyword_definitions, with the index of y:
   map (fun (y : Nat) => pickK k y) ys */
static const Term *map_body(const LType *nat, Tokens nat_source, Nat y) {
  const TermTypes *binders = term_types_item((TermType){text("y"), 0, nat, nat_source}, NULL);
  const Term *pick = term_named(TERM_APPLY, 0, 0, text("pickK"), NULL,
                                terms_item(term_var(0, 0, text("k"), 0), one(term_var(0, 0, text("y"), y))));
  const Term *function = term_form(TERM_GROUP, 0, 0, one(term_fun(0, 0, binders, pick)));
  return term_form(TERM_MAP, 0, 0, terms_item(function, one(term_var(0, 0, text("ys"), 1))));
}

/* The body of foldTwo in test_keyword_definitions, with the index of acc:
   fold (fun (x : Nat) (acc : Nat) => pickK k acc) 0 xs */
static const Term *fold_body(const LType *nat, Tokens nat_source, Nat acc) {
  const TermTypes *binders = term_types_item((TermType){text("x"), 0, nat, nat_source},
                                             term_types_item((TermType){text("acc"), 0, nat, nat_source}, NULL));
  const Term *pick = term_named(TERM_APPLY, 0, 0, text("pickK"), NULL,
                                terms_item(term_var(0, 0, text("k"), 0), one(term_var(0, 0, text("acc"), acc))));
  const Term *function = term_form(TERM_GROUP, 0, 0, one(term_fun(0, 0, binders, pick)));
  return term_form(TERM_FOLD, 0, 0,
                   terms_item(function, terms_item(term_number(0, 0, 0),
                                                   one(term_named(TERM_NAME, 0, 0, text("xs"), NULL, NULL)))));
}

/* Each keyword form gives its term in a function body. The binders of an
   inline fun continue after the function parameters, and a parameter name
   as the function of a form gives a TERM_VAR. */
static void test_keyword_definitions(void) {
  const char *source =
      "def xs : List Nat := cons 4 (cons 7 nil)\n"
      "def pickK : (k : Nat) -> (n : Nat) -> Nat := fun (k : Nat) (n : Nat) => k\n"
      "def keepK : (k : Flag) -> (b : Flag) -> Flag := fun (k : Flag) (b : Flag) => k\n"
      "def Three : Type 0 := (k : Nat) -> (x : Nat) -> (acc : Nat) -> Nat\n"
      "def pick3 : Three := fun (k : Nat) (x : Nat) (acc : Nat) => k\n"
      "def One : Type 0 := (n : Nat) -> Nat\n"
      "def again : (s : Nat) -> Option (Prod Nat Nat) := fun (s : Nat) => some (pair s s)\n"
      "def size : (n : Nat) -> Nat := fun (n : Nat) => n\n"
      "def mapK : (k : Nat) -> (ys : List Nat) -> List Nat := fun (k : Nat) (ys : List Nat) => "
      "map (fun (y : Nat) => pickK k y) ys\n"
      "def bindK : (k : Nat) -> (ys : List Nat) -> List Nat := fun (k : Nat) (ys : List Nat) => "
      "bind (fun (y : Nat) => cons k (cons y nil)) ys\n"
      "def filterK : (k : Flag) -> (bs : List Flag) -> List Flag := fun (k : Flag) (bs : List Flag) => "
      "filter (fun (b : Flag) => keepK k b) bs\n"
      "def mapG : (g : One) -> List Nat := fun (g : One) => map g xs\n"
      "def mapH : (h : One) -> List Nat := fun (h : One) => map h xs\n"
      "def foldTwo : (k : Nat) -> Nat := fun (k : Nat) => fold (fun (x : Nat) (acc : Nat) => pickK k acc) 0 xs\n"
      "def foldPartial : (k : Nat) -> Nat := fun (k : Nat) => fold (pick3 k) 0 xs\n"
      "def settle : (s : Sum Nat Nat) -> Nat := fun (s : Sum Nat Nat) => either size size s\n"
      "def single : (k : Nat) -> List Nat := fun (k : Nat) => pure k\n"
      "def foldValue : (k : Nat) -> (v : Value) -> Nat := fun (k : Nat) (v : Value) => fold (pickK k) "
      "(fun (b : Flag) => 0) (fun (t : Text) => 0) (fun (ns : List Nat) => 0) (fun (fs : List (Prod Text Nat)) => k) 0 v\n"
      "def unfoldList : (n : Nat) -> List Nat := fun (n : Nat) => unfold again 3 n\n"
      "def grow : (s : Text) -> Option (Sum Nat (Sum Flag (Sum Text (Sum (List Text) (List (Prod Text Text)))))) :=\n"
      "  fun (s : Text) => some (inr (inr (inr (inr (cons (pair \"left\" s) (cons (pair \"right\" s) nil))))))\n"
      "def unfoldValue : (s : Text) -> Value := fun (s : Text) => unfold grow 2 s\n";
  const Bindings *environment = NULL;
  Failure failure;
  assert(check_definitions(text(source), &environment, &failure) == 1);
  Nat checked = 0;
  for (const Bindings *item = environment; item != NULL; item = item->tail) {
    if (item->head.kind != BIND_FUN) continue;
    assert(item->head.term != NULL);
    assert(same_text(term_text(item->head.term), tokens_text(item->head.body)));
    checked++;
  }
  assert(checked == 18);

  /* mapK: k and ys are 0 and 1, y is 2. foldTwo: k is 0, x and acc are 1
     and 2. A fun that starts its binders at 0 again gives a different term. */
  LType nat = {.tag = TY_NAT};
  Tokens nat_source = lexed("Nat");
  assert(same_term(body_term(environment, "mapK"), map_body(&nat, nat_source, 2)));
  assert(!same_term(body_term(environment, "mapK"), map_body(&nat, nat_source, 0)));
  assert(same_term(body_term(environment, "foldTwo"), fold_body(&nat, nat_source, 2)));
  assert(!same_term(body_term(environment, "foldTwo"), fold_body(&nat, nat_source, 1)));

  const Term *by_g = body_term(environment, "mapG");
  assert(by_g->tag == TERM_MAP && by_g->args->head->tag == TERM_VAR && by_g->args->head->index == 0);
  assert(same_term(by_g, body_term(environment, "mapH")));

  assert(body_term(environment, "bindK")->tag == TERM_BIND);
  assert(body_term(environment, "filterK")->tag == TERM_FILTER);
  const Term *partial = body_term(environment, "foldPartial");
  assert(partial->tag == TERM_FOLD && partial->args->head->tag == TERM_GROUP &&
         partial->args->head->args->head->tag == TERM_PARTIAL);
  const Term *either = body_term(environment, "settle");
  assert(either->tag == TERM_EITHER && args_count(either->args) == 3);
  assert(body_term(environment, "single")->tag == TERM_PURE);
  /* fold over Value: the first function, the four others, start, source. */
  const Term *value_fold = body_term(environment, "foldValue");
  assert(value_fold->tag == TERM_FOLD_VALUE && args_count(value_fold->args) == 7);
  assert(value_fold->args->head->tag == TERM_GROUP && value_fold->args->head->args->head->tag == TERM_PARTIAL);
  const Term *unfolded = body_term(environment, "unfoldList");
  assert(unfolded->tag == TERM_UNFOLD && args_count(unfolded->args) == 3);
  const Term *grown = body_term(environment, "unfoldValue");
  assert(grown->tag == TERM_UNFOLD_VALUE && args_count(grown->args) == 3);
}

static Nat check_fun_positions(const Term *term, Tokens body) {
  Nat count = 0;
  if (term->tag == TERM_FUN) {
    Nat at = 0;
    for (; at < body.size && body.items[at].position != term->position; at++) {}
    assert(at < body.size);
    assert(body.items[at].kind == TOKEN_IDENTIFIER && same_text(body.items[at].text, text("fun")));
    count++;
  }
  if (term->callee != NULL) count += check_fun_positions(term->callee, body);
  for (const Terms *args = term->args; args != NULL; args = args->tail)
    count += check_fun_positions(args->head, body);
  return count;
}

/* Inline stepper nodes start at fun in every fold and unfold mode. */
static void test_keyword_positions(void) {
  const char *source =
      "def xs : List Nat := cons 3 nil\n"
      "def foldNat : (k : Nat) -> Nat := fun (k : Nat) => "
      "fold (fun (acc : Nat) => acc) 0 k\n"
      "def foldList : (k : Nat) -> Nat := fun (k : Nat) => "
      "fold (fun (n : Nat) (acc : Nat) => acc) k xs\n"
      "def unfoldList : (n : Nat) -> List Nat := fun (n : Nat) => "
      "unfold (fun (s : Nat) => some (pair s s)) 2 n\n"
      "def unfoldNat : (n : Nat) -> Nat := fun (n : Nat) => "
      "unfold (fun (s : Nat) => some s) 2 n\n"
      "def foldValue : (v : Value) -> Nat := fun (v : Value) => "
      "fold (fun (n : Nat) => n) (fun (b : Flag) => 0) (fun (t : Text) => 0) "
      "(fun (ns : List Nat) => 0) (fun (fs : List (Prod Text Nat)) => 0) 0 v\n"
      "def unfoldValue : (n : Nat) -> Value := fun (n : Nat) => "
      "unfold (fun (s : Nat) => none) 2 n\n";
  const Bindings *environment = NULL;
  Failure failure;
  assert(check_definitions(text(source), &environment, &failure));
  Nat count = 0;
  for (const Bindings *item = environment; item != NULL; item = item->tail) {
    if (item->head.kind != BIND_FUN) continue;
    assert(item->head.term != NULL);
    assert(same_text(term_text(item->head.term), tokens_text(item->head.body)));
    count += check_fun_positions(item->head.term, item->head.body);
  }
  assert(count == 10);
}

static void test_type_references(void) {
  const char *source =
      "def id : (A : Type 0) -> (x : A) -> A := fun (A : Type 0) (x : A) => x\n"
      "def viaA : (A : Type 0) -> (x : A) -> A := fun (A : Type 0) (x : A) => id A x\n"
      "def viaB : (B : Type 0) -> (y : B) -> B := fun (B : Type 0) (y : B) => id B y\n"
      "def viaFirst : (A : Type 0) -> (B : Type 0) -> (x : A) -> A := "
      "fun (A : Type 0) (B : Type 0) (x : A) => id A x\n"
      "def viaSecond : (B : Type 0) -> (A : Type 0) -> (x : A) -> A := "
      "fun (B : Type 0) (A : Type 0) (x : A) => id A x\n"
      "def listA : (A : Type 0) -> (xs : List (Option A)) -> List (Option A) := "
      "fun (A : Type 0) (xs : List (Option A)) => id (List (Option A)) xs\n"
      "def listB : (B : Type 0) -> (ys : List (Option B)) -> List (Option B) := "
      "fun (B : Type 0) (ys : List (Option B)) => id (List (Option B)) ys\n"
      "def One : Type 0 := (n : Nat) -> Nat\n"
      "def keep : (A : Type 0) -> (x : A) -> (n : Nat) -> Nat := "
      "fun (A : Type 0) (x : A) (n : Nat) => n\n"
      "def useNat : (g : One) -> Nat := fun (g : One) => g 1\n"
      "def partialA : (A : Type 0) -> (x : A) -> Nat := "
      "fun (A : Type 0) (x : A) => useNat (keep A x)\n"
      "def partialB : (B : Type 0) -> (y : B) -> Nat := "
      "fun (B : Type 0) (y : B) => useNat (keep B y)\n";
  const Bindings *environment = NULL;
  Failure failure;
  assert(check_definitions(text(source), &environment, &failure) == 1);
  assert(same_term(body_term(environment, "viaA"), body_term(environment, "viaB")));
  assert(!same_term(body_term(environment, "viaFirst"), body_term(environment, "viaSecond")));
  assert(same_term(body_term(environment, "listA"), body_term(environment, "listB")));
  assert(same_term(body_term(environment, "partialA"), body_term(environment, "partialB")));
  for (const Bindings *item = environment; item != NULL; item = item->tail)
    if (item->head.kind == BIND_FUN)
      assert(item->head.term != NULL && same_text(term_text(item->head.term), tokens_text(item->head.body)));
}

/* The binding of the function name, or NULL. */
static const Binding *fun_named(const Bindings *environment, const char *name) {
  for (; environment != NULL; environment = environment->tail)
    if (environment->head.kind == BIND_FUN && same_text(environment->head.name, text(name))) return &environment->head;
  return NULL;
}

/* The print_value text of the value. */
static Text printed(const Value *value) {
  Printer printer = {1000, builder_new()};
  Failure failure;
  assert(print_value(&printer, value, &failure));
  return builder_text(&printer.output);
}

/* The scope of the body of the function item, called with the arguments in
   args (the run-time call site of synth_term). */
static const Bindings *call_scope(const Bindings *environment, const Binding *item, const char *args) {
  const Values *values;
  Tokens rest;
  Nat left;
  Failure failure;
  assert(parse_arguments(1000, 1000, 1, param_types(item->params), environment, lexed(args), &values, &rest, &left,
                         NULL, &failure));
  assert(rest.size == 0);
  return bind_arguments(environment, item->params, values, definition_scope(item->name, environment));
}

typedef struct {
  int eval;
  int parse;
  Text value;
} BothPaths;

/* eval_term and parse_term on the body of item at one fuel and budget. When
   eval_term gives 1, parse_term gives 1 with the same value text and the
   same remaining budget. */
static BothPaths both_paths(const Bindings *scope, const Binding *item, Fuel fuel, Nat budget) {
  const Value *eval_value = NULL;
  Nat eval_left = 0;
  int eval = eval_term(fuel, budget, item->type, scope, item->term, &eval_value, &eval_left);
  const Value *parse_value = NULL;
  Tokens rest;
  Nat parse_left = 0;
  Failure failure;
  int parse = parse_term(fuel, budget, 0, item->type, scope, item->body, &parse_value, &rest, &parse_left, NULL, &failure);
  if (eval == 1) {
    assert(parse == 1 && eval_left == parse_left);
    assert(same_text(printed(eval_value), printed(parse_value)));
  }
  return (BothPaths){eval, parse, eval == 1 ? printed(eval_value) : text("")};
}

typedef struct {
  Nat worked;
  Nat differ;
} GridCount;

/* both_paths on each fuel below 64 and each budget below 16. worked counts
   the points where eval_term gives 1; differ counts the points where the
   two answers differ. */
static GridCount body_grid(const Bindings *environment, const char *name, const char *args) {
  const Binding *item = fun_named(environment, name);
  assert(item != NULL && item->term != NULL);
  const Bindings *scope = call_scope(environment, item, args);
  GridCount count = {0, 0};
  for (Fuel fuel = 0; fuel < 64; fuel++)
    for (Nat budget = 0; budget < 16; budget++) {
      BothPaths paths = both_paths(scope, item, fuel, budget);
      count.worked += paths.eval == 1;
      count.differ += paths.eval != paths.parse;
    }
  return count;
}

/* both_paths on the body of the function name at one fuel and budget. */
static BothPaths body_at(const Bindings *environment, const char *name, const char *args, Fuel fuel, Nat budget) {
  const Binding *item = fun_named(environment, name);
  assert(item != NULL && item->term != NULL);
  return both_paths(call_scope(environment, item, args), item, fuel, budget);
}

/* eval_term gives the value, the remaining budget and the answer of
   parse_term on the body tokens, or 0 (D3-s3 part A). A body with no type
   arguments gives the same answer on both paths. A keyword form and a
   dependent callee give 0 from eval_term. A body with type arguments gives 0
   at the fuel margin. */
static void test_term_evaluator(void) {
  const char *source =
      "def pickK : (k : Nat) -> (n : Nat) -> Nat := fun (k : Nat) (n : Nat) => k\n"
      "def twoList : (a : Nat) -> (b : Nat) -> List Nat := fun (a : Nat) (b : Nat) => cons a (cons (pickK b 5) nil)\n"
      "def label : (a : Nat) -> (b : Nat) -> Text := fun (a : Nat) (b : Nat) => \"hi\"\n"
      "def grouped : (a : Nat) -> (b : Nat) -> Nat := fun (a : Nat) (b : Nat) => (pickK b a)\n"
      "def deep : (a : Nat) -> (b : Nat) -> Nat := fun (a : Nat) (b : Nat) => pickK (pickK a b) 9\n"
      "def mapK : (k : Nat) -> (ys : List Nat) -> List Nat := fun (k : Nat) (ys : List Nat) => "
      "map (fun (y : Nat) => pickK k y) ys\n"
      "def sameNat : (n : Nat) -> (p : Eq Nat n n) -> Nat := fun (n : Nat) (p : Eq Nat n n) => n\n"
      "def viaSame : (a : Nat) -> (b : Nat) -> Nat := fun (a : Nat) (b : Nat) => sameNat a refl\n"
      "def id : (A : Type 0) -> (x : A) -> A := fun (A : Type 0) (x : A) => x\n"
      "def viaA : (A : Type 0) -> (x : A) -> A := fun (A : Type 0) (x : A) => id A x\n"
      "def viaNat : (a : Nat) -> (b : Nat) -> Nat := fun (a : Nat) (b : Nat) => viaA Nat b\n"
      "def size : (n : Nat) -> Nat := fun (n : Nat) => n\n"
      "def half : (n : Nat) -> Option Nat := fun (n : Nat) => some n\n"
      "def keep : (n : Nat) -> Flag := fun (n : Nat) => flagYes\n"
      "def keepK : (k : Flag) -> (n : Nat) -> Flag := fun (k : Flag) (n : Nat) => k\n"
      "def twoOf : (k : Nat) -> (y : Nat) -> List Nat := fun (k : Nat) (y : Nat) => cons k (cons y nil)\n"
      "def someOf : (k : Nat) -> (y : Nat) -> Option Nat := fun (k : Nat) (y : Nat) => some k\n"
      "def constA : (A : Type 0) -> (a : A) -> (n : Nat) -> A := fun (A : Type 0) (a : A) (n : Nat) => a\n"
      "def One : Type 0 := (n : Nat) -> Nat\n"
      "def ToOption : Type 0 := (n : Nat) -> Option Nat\n"
      "def pureL : (k : Nat) -> (ys : List Nat) -> List Nat := fun (k : Nat) (ys : List Nat) => pure k\n"
      "def mapP : (k : Nat) -> (ys : List Nat) -> List Nat := fun (k : Nat) (ys : List Nat) => map (pickK k) ys\n"
      "def mapN : (k : Nat) -> (ys : List Nat) -> List Nat := fun (k : Nat) (ys : List Nat) => map size ys\n"
      "def mapGP : (k : Nat) -> (ys : List Nat) -> List Nat := fun (k : Nat) (ys : List Nat) => map ((pickK k)) ys\n"
      "def mapGF : (k : Nat) -> (ys : List Nat) -> List Nat := fun (k : Nat) (ys : List Nat) => "
      "map ((fun (y : Nat) => size y)) ys\n"
      "def mapV : (g : One) -> (ys : List Nat) -> List Nat := fun (g : One) (ys : List Nat) => map g ys\n"
      "def bindF : (k : Nat) -> (ys : List Nat) -> List Nat := fun (k : Nat) (ys : List Nat) => "
      "bind (fun (y : Nat) => cons k (cons y nil)) ys\n"
      "def bindP : (k : Nat) -> (ys : List Nat) -> List Nat := fun (k : Nat) (ys : List Nat) => bind (twoOf k) ys\n"
      "def filterF : (k : Flag) -> (ys : List Nat) -> List Nat := fun (k : Flag) (ys : List Nat) => "
      "filter (fun (y : Nat) => k) ys\n"
      "def filterP : (k : Flag) -> (ys : List Nat) -> List Nat := fun (k : Flag) (ys : List Nat) => "
      "filter (keepK k) ys\n"
      "def pureO : (k : Nat) -> (o : Option Nat) -> Option Nat := fun (k : Nat) (o : Option Nat) => pure k\n"
      "def mapO : (k : Nat) -> (o : Option Nat) -> Option Nat := fun (k : Nat) (o : Option Nat) => map (pickK k) o\n"
      "def mapOF : (k : Nat) -> (o : Option Nat) -> Option Nat := fun (k : Nat) (o : Option Nat) => "
      "map (fun (y : Nat) => size y) o\n"
      "def bindO : (k : Nat) -> (o : Option Nat) -> Option Nat := fun (k : Nat) (o : Option Nat) => "
      "bind (someOf k) o\n"
      "def bindOV : (h : ToOption) -> (o : Option Nat) -> Option Nat := fun (h : ToOption) (o : Option Nat) => "
      "bind h o\n"
      "def filterON : (k : Nat) -> (o : Option Nat) -> Option Nat := fun (k : Nat) (o : Option Nat) => "
      "filter keep o\n"
      "def filterOG : (k : Flag) -> (o : Option Nat) -> Option Nat := fun (k : Flag) (o : Option Nat) => "
      "filter ((keepK k)) o\n"
      "def settle : (s : Sum Nat Nat) -> Nat := fun (s : Sum Nat Nat) => either size size s\n"
      "def settleV : (f : One) -> (g : One) -> (s : Sum Nat Nat) -> Nat := "
      "fun (f : One) (g : One) (s : Sum Nat Nat) => either f g s\n"
      "def mapT : (k : Nat) -> (ys : List Nat) -> List Nat := fun (k : Nat) (ys : List Nat) => "
      "map (constA Nat k) ys\n"
      "def push : (y : Nat) -> (acc : List Nat) -> List Nat := fun (y : Nat) (acc : List Nat) => cons y acc\n"
      "def pushK : (k : Nat) -> (y : Nat) -> (acc : List Nat) -> List Nat := "
      "fun (k : Nat) (y : Nat) (acc : List Nat) => cons k (cons y acc)\n"
      "def Pusher : Type 0 := (y : Nat) -> (acc : List Nat) -> List Nat\n"
      "def foldN : (k : Nat) -> (ys : List Nat) -> List Nat := fun (k : Nat) (ys : List Nat) => "
      "fold push (cons k nil) ys\n"
      "def foldP : (k : Nat) -> (ys : List Nat) -> List Nat := fun (k : Nat) (ys : List Nat) => "
      "fold (pushK k) nil ys\n"
      "def foldG : (k : Nat) -> (ys : List Nat) -> List Nat := fun (k : Nat) (ys : List Nat) => "
      "fold ((pushK k)) nil ys\n"
      "def foldF : (k : Nat) -> (ys : List Nat) -> List Nat := fun (k : Nat) (ys : List Nat) => "
      "fold (fun (y : Nat) (a : List Nat) => cons y a) nil ys\n"
      "def foldV : (g : Pusher) -> (ys : List Nat) -> List Nat := fun (g : Pusher) (ys : List Nat) => fold g nil ys\n"
      "def unfoldN : (k : Nat) -> (n : Nat) -> Nat := fun (k : Nat) (n : Nat) => unfold half k n\n"
      "def unfoldP : (k : Nat) -> (n : Nat) -> Nat := fun (k : Nat) (n : Nat) => unfold (someOf k) 3 n\n"
      "def unfoldG : (k : Nat) -> (n : Nat) -> Nat := fun (k : Nat) (n : Nat) => unfold ((someOf k)) 3 n\n"
      "def unfoldF : (k : Nat) -> (n : Nat) -> Nat := fun (k : Nat) (n : Nat) => "
      "unfold (fun (y : Nat) => some y) k n\n"
      "def unfoldV : (h : ToOption) -> (n : Nat) -> Nat := fun (h : ToOption) (n : Nat) => unfold h 3 n\n"
      "def foldValue : (k : Nat) -> (v : Value) -> Nat := fun (k : Nat) (v : Value) => "
      "fold (pickK k) (fun (b : Flag) => 1) (fun (s : Text) => 2) (fun (xs : List Nat) => 3) "
      "(fun (fs : List (Prod Text Nat)) => 4) 0 v\n"
      "def foldValueT : (k : Nat) -> (v : Value) -> Nat := fun (k : Nat) (v : Value) => "
      "fold (constA Nat k) (fun (b : Flag) => 1) (fun (s : Text) => 2) (fun (xs : List Nat) => 3) "
      "(fun (fs : List (Prod Text Nat)) => 4) 0 v\n"
      "def grow : (s : Text) -> Option (Sum Nat (Sum Flag (Sum Text (Sum (List Text) (List (Prod Text Text)))))) := "
      "fun (s : Text) => some (inr (inr (inr (inr (cons (pair \"left\" s) nil)))))\n"
      "def unfoldValue : (k : Nat) -> (s : Text) -> Value := fun (k : Nat) (s : Text) => unfold grow k s\n";
  const Bindings *environment = NULL;
  Failure failure;
  assert(check_definitions(text(source), &environment, &failure) == 1);

  /* D3-s4 part A: the term of a BIND_FUN is the TERM_BODY of its body span. */
  for (const Bindings *item = environment; item != NULL; item = item->tail) {
    if (item->head.kind != BIND_FUN) continue;
    const Term *carrier = item->head.term;
    assert(carrier->tag == TERM_BODY);
    assert(term_tokens(carrier).items == item->head.body.items && term_tokens(carrier).size == item->head.body.size);
    if (carrier->callee != NULL) assert(same_text(term_text(carrier), tokens_text(item->head.body)));
  }
  /* An inline argument Value at check time keeps the TERM_BODY of the FUN
     node, and its closure keeps the same pointer. The argument tokens start
     after fun, as at the call in parse_term. The type is One (the g of mapV). */
  const LType *one_type = first_param_type(environment, "mapV");
  assert(one_type != NULL && is_arrow_type(one_type));
  Text fun_source = text("fun (y : Nat) => size y");
  Tokens fun_tokens;
  assert(lex(fuel_for(fun_source), fun_source, &fun_tokens, &failure));
  const Value *argument;
  Tokens after_fun;
  Nat fun_left;
  const Term *made = NULL;
  assert(inline_argument(1000, 1000, 0, one_type, environment, slice(fun_tokens, 1, fun_tokens.size), &argument,
                         &after_fun, &fun_left, &made, &failure));
  assert(made != NULL && made->tag == TERM_FUN);
  assert(argument->term != NULL && argument->term == made->args->head);
  Binding closure = bound_binding(argument, text("g"), one_type, environment);
  assert(closure.kind == BIND_CLOSURE && closure.term == argument->term);
  assert(closure.body.items == term_tokens(argument->term).items);
  assert(closure.body.size == term_tokens(argument->term).size);
  Value replayed = *argument;
  replayed.term = NULL;
  Binding decoded = bound_binding(&replayed, text("g"), one_type, environment);
  assert(decoded.kind == BIND_CLOSURE && decoded.term->tag == TERM_BODY && decoded.term->callee == NULL);
  assert(decoded.body.size == closure.body.size);

  const char *exact[] = {"pickK", "twoList", "label", "grouped", "deep"};
  for (Nat i = 0; i < sizeof exact / sizeof exact[0]; i++) {
    GridCount count = body_grid(environment, exact[i], "4 7");
    assert(count.worked > 0 && count.differ == 0);
  }
  assert(same_text(body_at(environment, "twoList", "4 7", 1000, 1000).value, text("[4,7]")));
  assert(same_text(body_at(environment, "label", "4 7", 1000, 1000).value, text("\"hi\"")));
  assert(same_text(body_at(environment, "deep", "4 7", 1000, 1000).value, text("4")));

  /* Budget 1: the inner call spends it, and the outer body has none left. */
  BothPaths starved = body_at(environment, "deep", "4 7", 1000, 1);
  assert(starved.eval == 0 && starved.parse == 0);

  /* Keyword forms (part B1: pure, map, bind, filter and either; part B2:
     fold and unfold, also over Value): eval 1 gives parse 1 on the grid, and eval 1
     at fuel 1000 (no replay). Heads: VAR, NAME, GROUP, FUN and PARTIAL. A
     FUN head gives 0 at or below its fuel margin, thus only the other heads
     give the same answer at each point (exact 1). */
  const struct {
    const char *name;
    const char *args;
    const char *value;
    int exact;
  } keyword[] = {
      {"mapK", "4 (cons 7 (cons 8 nil))", "[4,4]", 0},
      {"pureL", "4 (cons 7 (cons 8 nil))", "[4]", 1},
      {"mapP", "4 (cons 7 (cons 8 nil))", "[4,4]", 1},
      {"mapN", "4 (cons 7 (cons 8 nil))", "[7,8]", 1},
      {"mapGP", "4 (cons 7 (cons 8 nil))", "[4,4]", 1},
      {"mapGF", "4 (cons 7 (cons 8 nil))", "[7,8]", 0},
      {"mapV", "size (cons 7 (cons 8 nil))", "[7,8]", 1},
      {"bindF", "4 (cons 7 (cons 8 nil))", "[4,7,4,8]", 0},
      {"bindP", "4 (cons 7 (cons 8 nil))", "[4,7,4,8]", 1},
      {"filterF", "flagYes (cons 7 (cons 8 nil))", "[7,8]", 0},
      {"filterP", "flagNo (cons 7 (cons 8 nil))", "[]", 1},
      {"pureO", "4 (some 7)", "4", 1},
      {"mapO", "4 (some 7)", "4", 1},
      {"mapO", "4 none", "null", 1},
      {"mapOF", "4 (some 7)", "7", 0},
      {"bindO", "4 (some 7)", "4", 1},
      {"bindOV", "half (some 7)", "7", 1},
      {"filterON", "4 (some 7)", "7", 1},
      {"filterOG", "flagNo (some 7)", "null", 1},
      {"settle", "(inl 4)", "4", 1},
      {"settleV", "size size (inr 9)", "9", 1},
      {"foldN", "4 (cons 7 (cons 8 nil))", "[7,8,4]", 1},
      {"foldP", "4 (cons 7 (cons 8 nil))", "[4,7,4,8]", 1},
      {"foldG", "4 (cons 7 (cons 8 nil))", "[4,7,4,8]", 1},
      {"foldF", "4 (cons 7 (cons 8 nil))", "[7,8]", 0},
      {"foldV", "push (cons 7 (cons 8 nil))", "[7,8]", 1},
      {"unfoldN", "3 7", "3", 1},
      {"unfoldP", "3 7", "3", 1},
      {"unfoldG", "3 7", "3", 1},
      {"unfoldF", "3 7", "3", 0},
      {"unfoldV", "half 7", "3", 1},
      {"foldValue", "4 (valueNat 9)", "4", 0},
      {"foldValue", "4 (valueText \"a\")", "2", 0},
      {"unfoldValue", "2 \"s\"", "{\"left\":{\"left\":null}}", 1},
  };
  for (Nat i = 0; i < sizeof keyword / sizeof keyword[0]; i++) {
    GridCount count = body_grid(environment, keyword[i].name, keyword[i].args);
    assert(count.worked > 0 && (keyword[i].exact == 0 || count.differ == 0));
    BothPaths full = body_at(environment, keyword[i].name, keyword[i].args, 1000, 1000);
    assert(full.eval == 1 && same_text(full.value, text(keyword[i].value)));
  }

  /* Budget 1 on a map over 3 items: the first item spends it. eval_term
     gives 0, and the token path gives eBudget at the first token of the
     body. */
  const Binding *mapped = fun_named(environment, "mapK");
  const Bindings *three = call_scope(environment, mapped, "4 (cons 1 (cons 2 (cons 3 nil)))");
  assert(both_paths(three, mapped, 1000, 1).eval == 0);
  const Value *starved_value;
  Tokens starved_rest;
  Nat starved_left;
  assert(parse_term(1000, 1, 0, mapped->type, three, mapped->body, &starved_value, &starved_rest, &starved_left,
                    NULL, &failure) == 0);
  assert(failure.position == (Nat)(strstr(source, "=> pickK k y) ys") + 3 - source) &&
         same_text(failure.message, eBudget));

  /* Fallback: the token path gives the value. */
  BothPaths dependent = body_at(environment, "viaSame", "4 7", 1000, 1000);
  assert(dependent.eval == 0 && dependent.parse == 1);
  BothPaths typed_partial = body_at(environment, "mapT", "4 (cons 7 (cons 8 nil))", 1000, 1000);
  assert(typed_partial.eval == 0 && typed_partial.parse == 1);
  BothPaths typed_fold = body_at(environment, "foldValueT", "4 (valueNat 9)", 1000, 1000);
  assert(typed_fold.eval == 0 && typed_fold.parse == 1);

  /* Budget 1 on a fold over 3 items (part B2): the first step spends it.
     eval_term gives 0, and the token path gives eBudget at the first token
     of the body of the inline fun. */
  const Binding *folded = fun_named(environment, "foldF");
  const Bindings *three_folded = call_scope(environment, folded, "4 (cons 1 (cons 2 (cons 3 nil)))");
  assert(both_paths(three_folded, folded, 1000, 1).eval == 0);
  assert(parse_term(1000, 1, 0, folded->type, three_folded, folded->body, &starved_value, &starved_rest,
                    &starved_left, NULL, &failure) == 0);
  assert(failure.position == (Nat)(strstr(source, "=> cons y a) nil ys") + 3 - source) &&
         same_text(failure.message, eBudget));

  /* FOLD_VALUE at fuel 8 (part B2): second_function gives 0, thus the
     token path selects FOLD and fails at the first token of the second
     function. eval_term gives 0. */
  const Binding *valued = fun_named(environment, "foldValue");
  const Bindings *nine = call_scope(environment, valued, "4 (valueNat 9)");
  assert(both_paths(nine, valued, 8, 1000).eval == 0);
  assert(parse_term(8, 1000, 0, valued->type, nine, valued->body, &starved_value, &starved_rest, &starved_left,
                    NULL, &failure) == 0);
  assert(failure.position == (Nat)(strstr(source, "(fun (b : Flag) => 1)") + 1 - source));

  /* Type arguments: eval 1 gives parse 1 on the grid, and the margin is
     term_text(APPLY).size + 2 at entry. */
  assert(body_grid(environment, "viaNat", "4 7").worked > 0);
  assert(same_text(body_at(environment, "viaNat", "4 7", 1000, 1000).value, text("7")));
  Fuel margin = term_text(fun_named(environment, "viaNat")->term).size + 2;
  assert(body_at(environment, "viaNat", "4 7", margin, 1000).eval == 0);
}

int main(void) {
  test_runtime();
  test_lexer();
  test_json();
  test_term();
  test_definitions();
  test_function_references();
  test_keyword_definitions();
  test_keyword_positions();
  test_type_references();
  test_term_evaluator();
  puts("C module tests passed");
  return 0;
}
