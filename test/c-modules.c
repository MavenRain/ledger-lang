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
                       term_fun(0, 1, (Tokens){0},
                                term_types_item((TermType){text("x"), 0, &nat, nat_source}, NULL), n),
                       term_named(TERM_CONSTRUCT, 0, 1, text("some"), NULL, one(n)),
                       term_form(TERM_REFL, 0, 1, NULL),
                       term_form(TERM_FIRST, 0, 1, one(n)),
                       term_form(TERM_SECOND, 0, 1, one(n)),
                       term_form(TERM_SYMM, 0, 1, one(n)),
                       term_form(TERM_TRANS, 0, 1, terms_item(n, one(n))),
                       term_form(TERM_CONG, 0, 1, terms_item(n, one(n))),
                       term_form(TERM_TRANSPORT, 0, 1, terms_item(n, one(n))),
                       term_form(TERM_EITHER, 0, 1, terms_item(n, terms_item(n, one(n)))),
                       term_form(TERM_PURE, 0, 1, one(n)),
                       term_form(TERM_MAP, 0, 1, terms_item(n, one(n))),
                       term_form(TERM_BIND, 0, 1, terms_item(n, one(n))),
                       term_form(TERM_FILTER, 0, 1, terms_item(n, one(n))),
                       term_form(TERM_FOLD, 0, 1, terms_item(n, one(n))),
                       term_form(TERM_FOLD_VALUE, 0, 1, terms_item(n, one(n))),
                       term_form(TERM_UNFOLD, 0, 1, terms_item(n, one(n))),
                       term_form(TERM_UNFOLD_VALUE, 0, 1, terms_item(n, one(n))),
                       term_form(TERM_WITNESS, 0, 1, one(n)),
                       term_form(TERM_PAYLOAD, 0, 1, one(n)),
                       term_closed(0, &(LType){.tag = TY_FLAG}, &(Value){.kind = VALUE_FLAG, .flag = FLAG_YES}, text("true"))};
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
  assert(!same_term(term_fun(0, 1, (Tokens){0}, nat_types, n), term_fun(0, 1, (Tokens){0}, txt_types, n)));
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
  const Term *function = term_form(TERM_GROUP, 5, 1, one(term_fun(6, 1, (Tokens){0}, binders, body)));
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

/* The count of BIND_FUN bindings whose TERM_BODY has no callee. Each checked
   body gives a node, thus a checked program gives 0 (D3-s6 part D). */
static Nat bare_bodies(const Bindings *environment) {
  Nat count = 0;
  for (; environment != NULL; environment = environment->tail)
    count += environment->head.kind == BIND_FUN && environment->head.term->callee == NULL;
  return count;
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
  const Term *inner_fun = term_form(TERM_GROUP, 0, 0, one(term_fun(0, 0, (Tokens){0}, zs, outer_pick)));
  const Term *outer_fun = term_form(
      TERM_GROUP, 0, 0,
      one(term_fun(0, 0, (Tokens){0}, yw, term_named(TERM_APPLY, 0, 0, text("useOne"), NULL, one(inner_fun)))));
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
  assert(bare_bodies(environment) == 0);
  Nat checked = 0;
  for (const Bindings *item = environment; item != NULL; item = item->tail) {
    if (item->head.kind != BIND_FUN) continue;
    assert(item->head.term != NULL);
    assert(same_text(term_text(item->head.term), tokens_text(term_tokens(item->head.term))));
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
  assert(bare_bodies(environment) == 0);
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
      assert(item->head.term != NULL && same_text(term_text(item->head.term), tokens_text(term_tokens(item->head.term))));
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
  const Term *function = term_form(TERM_GROUP, 0, 0, one(term_fun(0, 0, (Tokens){0}, binders, pick)));
  return term_form(TERM_MAP, 0, 0, terms_item(function, one(term_var(0, 0, text("ys"), 1))));
}

/* The body of foldTwo in test_keyword_definitions, with the index of acc:
   fold (fun (x : Nat) (acc : Nat) => pickK k acc) 0 xs */
static const Term *fold_body(const LType *nat, Tokens nat_source, Nat acc) {
  const TermTypes *binders = term_types_item((TermType){text("x"), 0, nat, nat_source},
                                             term_types_item((TermType){text("acc"), 0, nat, nat_source}, NULL));
  const Term *pick = term_named(TERM_APPLY, 0, 0, text("pickK"), NULL,
                                terms_item(term_var(0, 0, text("k"), 0), one(term_var(0, 0, text("acc"), acc))));
  const Term *function = term_form(TERM_GROUP, 0, 0, one(term_fun(0, 0, (Tokens){0}, binders, pick)));
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
  assert(bare_bodies(environment) == 0);
  Nat checked = 0;
  for (const Bindings *item = environment; item != NULL; item = item->tail) {
    if (item->head.kind != BIND_FUN) continue;
    assert(item->head.term != NULL);
    assert(same_text(term_text(item->head.term), tokens_text(term_tokens(item->head.term))));
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

/* D3-s5 part A. The span of an APPLY or a PARTIAL starts after the head
   name; the head name and the span give term_text. The binder span of a FUN
   starts after fun and stops at the body. end is the position of the first
   token after the argument list. The parse input of a body can continue
   after the body span, so at the end of a body end is 0 or the position of
   the token after the body. */
typedef struct {
  Nat calls;
  Nat funs;
  Nat ends;
} SpanCount;

static SpanCount add_spans(SpanCount left, SpanCount right) {
  return (SpanCount){left.calls + right.calls, left.funs + right.funs, left.ends + right.ends};
}

static SpanCount check_spans(const Term *term, Tokens body) {
  SpanCount count = {0, 0, 0};
  const Token *limit = body.items + body.size;
  if (term->tag == TERM_APPLY || term->tag == TERM_PARTIAL) {
    const Token *head = term->tokens.items - 1;
    const Token *next = term->tokens.items + term->tokens.size;
    assert(head >= body.items && next <= limit && head->position == term->position);
    assert(same_text(tokens_text((Tokens){head, term->tokens.size + 1}), term_text(term)));
    assert(term->end == (next < limit || term->end != 0 ? next->position : 0));
    count = add_spans(count, (SpanCount){term->args != NULL ? 1 : 0, 0, term->end != 0 ? 1 : 0});
  }
  if (term->tag == TERM_CONSTRUCT) {
    Nat at = 0;
    for (; at < body.size && body.items[at].position != term->position; at++) {}
    assert(at < body.size);
    if (term->args == NULL)
      assert(term->end == (at + 1 < body.size || term->end != 0 ? body.items[at + 1].position : 0));
    else assert(term->end == 0 || term->end > term->position);
  }
  if (term->tag == TERM_FUN) {
    const Token *fun = term->tokens.items - 1;
    const Token *next = term->tokens.items + term->tokens.size;
    assert(fun >= body.items && next < limit && fun->position == term->position && same_text(fun->text, text("fun")));
    assert(next->position == term->args->head->position);
    TextBuilder whole = builder_new();
    builder_append(&whole, tokens_text((Tokens){fun, term->tokens.size + 1}));
    builder_append(&whole, term_text(term->args->head));
    assert(same_text(builder_text(&whole), term_text(term)));
    count = add_spans(count, (SpanCount){0, 1, 0});
  }
  if (term->callee != NULL) count = add_spans(count, check_spans(term->callee, body));
  for (const Terms *args = term->args; args != NULL; args = args->tail)
    count = add_spans(count, check_spans(args->head, body));
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
  assert(bare_bodies(environment) == 0);
  Nat count = 0;
  for (const Bindings *item = environment; item != NULL; item = item->tail) {
    if (item->head.kind != BIND_FUN) continue;
    assert(item->head.term != NULL);
    assert(same_text(term_text(item->head.term), tokens_text(term_tokens(item->head.term))));
    count += check_fun_positions(item->head.term, term_tokens(item->head.term));
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
  assert(bare_bodies(environment) == 0);
  assert(same_term(body_term(environment, "viaA"), body_term(environment, "viaB")));
  assert(!same_term(body_term(environment, "viaFirst"), body_term(environment, "viaSecond")));
  assert(same_term(body_term(environment, "listA"), body_term(environment, "listB")));
  assert(same_term(body_term(environment, "partialA"), body_term(environment, "partialB")));
  for (const Bindings *item = environment; item != NULL; item = item->tail)
    if (item->head.kind == BIND_FUN)
      assert(item->head.term != NULL && same_text(term_text(item->head.term), tokens_text(term_tokens(item->head.term))));
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
  Failure failure;
} BothPaths;

/* eval_term and parse_term on the body of item at one fuel and budget. When
   eval_term gives 1, parse_term gives 1 with the same value text and the
   same remaining budget. When eval_term gives a failed answer (0 with a
   code), parse_term gives 0 with the same position and code (D3-s5 part E,
   the rule E5). failure is the failure of eval_term: a message of size 0 is
   an unknown answer. */
static BothPaths both_paths(const Bindings *scope, const Binding *item, Fuel fuel, Nat budget) {
  const Value *eval_value = NULL;
  Nat eval_left = 0;
  Failure eval_failure = {0, {NULL, 0}};
  int eval = eval_term(fuel, budget, item->type, scope, item->term, &eval_value, &eval_left, &eval_failure);
  const Value *parse_value = NULL;
  Tokens rest;
  Nat parse_left = 0;
  Failure failure = {0, {NULL, 0}};
  int parse = parse_term(fuel, budget, 0, item->type, scope, term_tokens(item->term), &parse_value, &rest, &parse_left,
                         NULL, &failure);
  if (eval == 1) {
    assert(parse == 1 && eval_left == parse_left);
    assert(same_text(printed(eval_value), printed(parse_value)));
  }
  if (eval == 0 && eval_failure.message.size != 0)
    assert(parse == 0 && eval_failure.position == failure.position && same_text(eval_failure.message, failure.message));
  return (BothPaths){eval, parse, eval == 1 ? printed(eval_value) : text(""), eval_failure};
}

typedef struct {
  Nat worked;
  Nat failed;
  Nat unknown;
  Nat differ;
} GridCount;

/* both_paths on each fuel below 64 and each budget below 16. worked counts
   the points where eval_term gives 1; failed counts the failed answers;
   unknown counts the answers 0 with no code (a replay); differ counts the
   points where the two answers differ. both_paths compares each failed
   answer with the token path (the rule E5). The fuel step after the last
   argument gives unknown, not a failure at Term.end (D3-s5 part E). The
   term body takes the place of the body of item in scope (D3-s6 part A). */
static GridCount term_grid(const Bindings *scope, const Binding *item, const Term *body) {
  Binding copy = *item;
  copy.term = body;
  GridCount count = {0, 0, 0, 0};
  for (Fuel fuel = 0; fuel < 64; fuel++)
    for (Nat budget = 0; budget < 16; budget++) {
      BothPaths paths = both_paths(scope, &copy, fuel, budget);
      count.worked += paths.eval == 1;
      count.failed += paths.eval == 0 && paths.failure.message.size != 0;
      count.unknown += paths.eval == 0 && paths.failure.message.size == 0;
      count.differ += paths.eval != paths.parse;
    }
  return count;
}

/* term_grid on the body of the function name, called with args. */
static GridCount body_grid(const Bindings *environment, const char *name, const char *args) {
  const Binding *item = fun_named(environment, name);
  assert(item != NULL && item->term != NULL);
  return term_grid(call_scope(environment, item, args), item, item->term);
}

/* 1 when the two counts are the same in each field. */
static int same_grid(GridCount left, GridCount right) {
  return left.worked == right.worked && left.failed == right.failed && left.unknown == right.unknown &&
         left.differ == right.differ;
}

/* The grid rows with no unknown answer (D3-s5 part E). D3-s7 part D adds
   twoList, grouped and deep: the close_result sites give eTerm. Other rows
   can give unknown at the sites that stay unknown (TERM-DESIGN D3-s7, Out
   of scope). */
static int no_unknown(const char *name) {
  return strcmp(name, "pickK") == 0 || strcmp(name, "label") == 0 || strcmp(name, "twice") == 0 ||
         strcmp(name, "twoList") == 0 || strcmp(name, "grouped") == 0 || strcmp(name, "deep") == 0;
}

/* both_paths on the body of the function name at one fuel and budget. */
static BothPaths body_at(const Bindings *environment, const char *name, const char *args, Fuel fuel, Nat budget) {
  const Binding *item = fun_named(environment, name);
  assert(item != NULL && item->term != NULL);
  return both_paths(call_scope(environment, item, args), item, fuel, budget);
}

/* node with the tag TERM_CONSTRUCT, callee NULL and the arguments args
   (D3-s6 part A). */
static const Term *as_construct(const Term *node, const Terms *args) {
  return term_call(TERM_CONSTRUCT, node->position, node->cost, node->tokens, node->end, node->name, NULL, node->types,
                   args);
}

/* A TERM_BODY on the tokens of bytes with a TERM_CONSTRUCT node of name at
   position 0 and the arguments args, built by hand (D3-s6 part A). */
static const Term *construct_body(const char *bytes, const char *name, const Terms *args) {
  Tokens tokens = lexed(bytes);
  return term_body(tokens, term_call(TERM_CONSTRUCT, 0, 0, tokens, text(bytes).size, text(name), NULL, NULL, args));
}

/* A checked constructor can resolve to a function in the run-time scope.
   In argument position the token path still requires parentheses, even
   for a function with no parameters. Check both binding kinds and both
   argument loops, plus the direct argument of a structure form. */
/* D8 part A: each body runs from its checked Term. The chain f0 to fk has
   2 to the power k + 1, minus 1, bodies (probes a11 and a12). */
#define D8_F0 "def f0 : (x : Nat) -> Nat := fun (x : Nat) => x\n"
#define D8_F(k, j) "def f" #k " : (x : Nat) -> Nat := fun (x : Nat) => f" #j " (f" #j " x)\n"
#define D8_CHAIN                                                                                               \
  D8_F0 D8_F(1, 0) D8_F(2, 1) D8_F(3, 2) D8_F(4, 3) D8_F(5, 4) D8_F(6, 5) D8_F(7, 6) D8_F(8, 7) D8_F(9, 8) \
      D8_F(10, 9) D8_F(11, 10)

/* The call scope of name, with the closure (the second binding) on its body
   Term with an empty token span. A token run on this span gives eTerm. */
static BothPaths bare_closure(const Bindings *environment, const char *name, const char *args) {
  const Binding *item = fun_named(environment, name);
  const Bindings *scope = call_scope(environment, item, args);
  assert(scope->tail->head.kind == BIND_CLOSURE && scope->tail->head.term != NULL);
  Bindings closure = *scope->tail;
  closure.head.term = term_body((Tokens){0}, closure.head.term);
  Bindings top = *scope;
  top.tail = &closure;
  return both_paths(&top, item, 1000, 1000);
}

static void test_d8_body_term(const Bindings *environment) {
  /* The closure arm of eval_apply (f of twice) and apply_body (map over g of
     mapV, a partial and an inline fun) give the value of the body Term. */
  BothPaths twice_bare = bare_closure(environment, "twice", "size 4");
  assert(twice_bare.eval == 1 && twice_bare.parse == 1 && same_text(twice_bare.value, text("4")));
  BothPaths partial_bare = bare_closure(environment, "mapV", "(pickK 3) (cons 7 (cons 8 nil))");
  assert(partial_bare.eval == 1 && partial_bare.parse == 1 && same_text(partial_bare.value, text("[3,3]")));
  BothPaths inline_bare = bare_closure(environment, "mapV", "(fun (y : Nat) => pickK 5 y) (cons 7 (cons 8 nil))");
  assert(inline_bare.eval == 1 && inline_bare.parse == 1 && same_text(inline_bare.value, text("[5,5]")));

  /* The fold in a body (probe b1) and the map in a body (probe b2). */
  Text output;
  Failure failure = {0, {NULL, 0}};
  assert(compile_program(text("def Reducer : Type 0 := (a : Nat) -> (b : List Nat) -> List Nat\n"
                              "def pick : Reducer := fun (a : Nat) (b : List Nat) => cons a b\n"
                              "def xs : List Nat := cons 4 (cons 7 nil)\n"
                              "def run : (f : Reducer) -> List Nat := fun (f : Reducer) => fold f nil xs\n"
                              "def out : List Nat := run pick\n"),
                         &output, &failure));
  assert(same_text(output, text("{\"ledger-lang\":1,\"instances\":[{\"name\":\"xs\",\"type\":\"List (Nat)\","
                                "\"value\":[4,7]},{\"name\":\"out\",\"type\":\"List (Nat)\",\"value\":[4,7]}]}")));
  assert(compile_program(text("def four : (x : Nat) -> Nat := fun (x : Nat) => 4\n"
                              "def g : (o : Option Nat) -> Option Nat := fun (o : Option Nat) => map four o\n"
                              "def xs : Option Nat := g (some 1)\n"),
                         &output, &failure));
  assert(same_text(output, text("{\"ledger-lang\":1,\"instances\":[{\"name\":\"xs\",\"type\":\"Option (Nat)\","
                                "\"value\":4}]}")));

  /* The work budget: 4095 bodies in 689 bytes check (a11). 8191 bodies in
     748 bytes give eBudget at the first token of the innermost body, byte 46
     (a12). */
  assert(compile_program(text(D8_CHAIN "def n : Nat := f11 1\n"), &output, &failure));
  Failure starved = {0, {NULL, 0}};
  assert(!compile_program(text(D8_CHAIN D8_F(12, 11) "def n : Nat := f12 1\n"), &output, &starved));
  assert(starved.position == 46 && same_text(starved.message, eBudget));
}

#undef D8_CHAIN
#undef D8_F
#undef D8_F0

static void test_construct_argument_lookup(void) {
  const LType *flag;
  Tokens rest;
  Failure failure = {0, {NULL, 0}};
  Nat type_left;
  assert(parse_type(1000, 1000, 0, NULL, lexed("Flag"), &flag, &rest, &type_left, &failure) && rest.size == 0);
  Params param = {{text("x"), flag}, NULL};
  Bindings identity = {{.kind = BIND_FUN, .name = text("idFlag"), .type = flag, .params = &param,
                        .term = term_body(lexed("x"), term_var(0, 0, text("x"), 0))}, NULL};
  const Value *value;
  Nat left;
  const Term *truth = NULL;
  Tokens truth_tokens = lexed("flagYes");
  assert(parse_term(1000, 1000, 0, flag, &identity, truth_tokens, &value, &rest, &left, &truth, &failure));
  const LType *universe;
  assert(parse_type(1000, 1000, 0, NULL, lexed("Type 0"), &universe, &rest, &left, &failure) && rest.size == 0);
  Params type_param = {{text("A"), universe}, NULL};
  LType equality = {.tag = TY_EQ, .left = flag, .lhs = {.kind = VAL_VAR}, .rhs = {.kind = VAL_VAR}};
  Params proof_param = {{text("proof"), &equality}, NULL};
  const struct {
    const char *type;
    const char *body;
    int works;
  } rows[] = {{"Prod Flag Flag", "pair flagNo flagYes", 0},
              {"Option Flag", "some flagNo", 0},
              {"Flag", "idFlag flagNo", 0},
              {"Option Flag", "pure flagNo", 0},
              {"Prod Flag Flag", "pair (flagNo) flagYes", 1},
              {"Flag", "idFlag (flagNo)", 1},
              {"Option Flag", "pure (flagNo)", 1},
              {"Flag", "flagNo", 1}};
  for (Nat row = 0; row < sizeof rows / sizeof rows[0]; row++) {
    const LType *expected;
    assert(parse_type(1000, 1000, 0, &identity, lexed(rows[row].type), &expected, &rest, &left, &failure) &&
           rest.size == 0);
    Tokens tokens = lexed(rows[row].body);
    const Term *node = NULL;
    assert(parse_term(1000, 1000, 0, expected, &identity, tokens, &value, &rest, &left, &node, &failure) &&
           rest.size == 0 && node != NULL);
    Binding body = {.type = expected, .term = term_body(tokens, node)};
    for (Nat closure = 0; closure < 2; closure++)
      for (Nat parameter = 0; parameter < 2; parameter++) {
        /* A missing type argument can fail at the closing parenthesis,
           which an empty constructor span omits. A dependent closure
           gives eTerm before the parentheses check. */
        const Params *params = parameter ? (closure ? &proof_param : &type_param) : NULL;
        Bindings shadow = {{.kind = closure ? BIND_CLOSURE : BIND_FUN, .name = text("flagNo"), .type = flag,
                            .params = params, .term = term_body(truth_tokens, truth), .scope = &identity}, &identity};
        GridCount count = term_grid(&shadow, &body, body.term);
        int works = rows[row].works && parameter == 0;
        assert(count.failed > 0 && count.differ == 0);
        assert(works ? count.worked > 0 : count.worked == 0);
        BothPaths paths = both_paths(&shadow, &body, 1000, 1000);
        if (works)
          assert(paths.eval == 1 && paths.parse == 1);
        else {
          assert(paths.eval == 0 && paths.parse == 0);
          if (parameter == 0) assert(same_text(paths.failure.message, eParen));
        }
      }
  }
}

/* eval_term gives the value, the remaining budget and the answer of
   parse_term on the body tokens (D3-s3 part A), a failed answer with the
   Failure of parse_term, or unknown: 0 with no code, a replay (D3-s5 part
   E). The grid rows test this at each fuel and budget. */
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
      "def reflN : (n : Nat) -> Eq Nat n n := fun (n : Nat) => refl\n"
      "def viaRefl : (a : Nat) -> (b : Nat) -> Nat := fun (a : Nat) (b : Nat) => sameNat b (reflN b)\n"
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
      "def pushA : (A : Type 0) -> (k : Nat) -> (y : Nat) -> (acc : List Nat) -> List Nat := "
      "fun (A : Type 0) (k : Nat) (y : Nat) (acc : List Nat) => cons k (cons y acc)\n"
      "def foldT : (k : Nat) -> (ys : List Nat) -> List Nat := fun (k : Nat) (ys : List Nat) => "
      "fold (pushA Nat k) nil ys\n"
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
      "def foldValueN : (k : Nat) -> (v : Value) -> Nat := fun (k : Nat) (v : Value) => "
      "fold size (fun (b : Flag) => 1) (fun (s : Text) => 2) (fun (xs : List Nat) => 3) "
      "(fun (fs : List (Prod Text Nat)) => 4) 0 v\n"
      "def grow : (s : Text) -> Option (Sum Nat (Sum Flag (Sum Text (Sum (List Text) (List (Prod Text Text)))))) := "
      "fun (s : Text) => some (inr (inr (inr (inr (cons (pair \"left\" s) nil)))))\n"
      "def unfoldValue : (k : Nat) -> (s : Text) -> Value := fun (k : Nat) (s : Text) => unfold grow k s\n"
      "def twice : (f : One) -> (n : Nat) -> Nat := fun (f : One) (n : Nat) => f (f n)\n"
      "def Two : Type 0 := (k : Nat) -> (n : Nat) -> Nat\n"
      "def PushK : Type 0 := (k : Nat) -> (y : Nat) -> (acc : List Nat) -> List Nat\n"
      "def mapC : (g : Two) -> (k : Nat) -> (ys : List Nat) -> List Nat := "
      "fun (g : Two) (k : Nat) (ys : List Nat) => map (g k) ys\n"
      "def foldC : (g : PushK) -> (k : Nat) -> (ys : List Nat) -> List Nat := "
      "fun (g : PushK) (k : Nat) (ys : List Nat) => fold (g k) nil ys\n"
      "def twiceF : (k : Nat) -> (n : Nat) -> Nat := "
      "fun (k : Nat) (n : Nat) => twice (fun (y : Nat) => pickK k y) n\n"
      "def twiceP : (k : Nat) -> (n : Nat) -> Nat := fun (k : Nat) (n : Nat) => twice (pickK k) n\n"
      "def twiceT : (k : Nat) -> (n : Nat) -> Nat := fun (k : Nat) (n : Nat) => twice (constA Nat k) n\n"
      "def twiceN : (k : Nat) -> (n : Nat) -> Nat := fun (k : Nat) (n : Nat) => twice size n\n"
      "def twiceFF : (k : Nat) -> (n : Nat) -> Nat := fun (k : Nat) (n : Nat) => "
      "twice (fun (y : Nat) => twice (fun (z : Nat) => pickK y z) k) n\n"
      "def twiceS : (k : Nat) -> (n : Nat) -> Nat := fun (k : Nat) (n : Nat) => "
      "twice (fun (k : Nat) => pickK k n) n\n"
      "def twiceV : (g : One) -> (n : Nat) -> Nat := fun (g : One) (n : Nat) => twice g n\n";
  const Bindings *environment = NULL;
  Failure failure;
  assert(check_definitions(text(source), &environment, &failure) == 1);
  assert(bare_bodies(environment) == 0);

  /* D3-s4 part A: the term of a BIND_FUN is the TERM_BODY of its body span.
     D3-s5 part A: the spans and end of the nodes of each body. */
  SpanCount spans = {0, 0, 0};
  for (const Bindings *item = environment; item != NULL; item = item->tail) {
    if (item->head.kind != BIND_FUN) continue;
    const Term *carrier = item->head.term;
    assert(carrier->tag == TERM_BODY && carrier->callee != NULL);
    assert(same_text(term_text(carrier), tokens_text(term_tokens(item->head.term))));
    spans = add_spans(spans, check_spans(carrier->callee, term_tokens(carrier)));
  }
  assert(spans.calls > 0 && spans.funs > 0 && spans.ends > 0);
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
  Value replayed = *argument;
  replayed.term = NULL;
  /* D8 part A: a Value with no term gives a closure with no term (no token
     TERM_BODY). Only a Value made by hand has no term. */
  Binding decoded = bound_binding(&replayed, text("g"), one_type, environment);
  assert(decoded.kind == BIND_CLOSURE && decoded.term == NULL);

  const char *exact[] = {"pickK", "twoList", "label", "grouped", "deep"};
  for (Nat i = 0; i < sizeof exact / sizeof exact[0]; i++) {
    GridCount count = body_grid(environment, exact[i], "4 7");
    assert(count.worked > 0 && count.differ == 0);
    assert(no_unknown(exact[i]) == 0 || count.unknown == 0);
  }
  assert(same_text(body_at(environment, "twoList", "4 7", 1000, 1000).value, text("[4,7]")));
  assert(same_text(body_at(environment, "label", "4 7", 1000, 1000).value, text("\"hi\"")));
  assert(same_text(body_at(environment, "deep", "4 7", 1000, 1000).value, text("4")));
  /* D3-s7 part D: close_result at fuel 0 in eval_dependent gives eTerm at
     the current argument, as on the token path. Fuel 3 stops at the first
     argument of the outer pickK, fuel 8 at the second argument of the inner
     pickK. */
  const char *deep_source = strstr(source, "pickK (pickK a b) 9");
  const struct {
    Fuel fuel;
    Nat offset;
  } close_points[] = {{3, 6}, {8, 15}};
  for (Nat i = 0; i < sizeof close_points / sizeof close_points[0]; i++) {
    BothPaths closed = body_at(environment, "deep", "4 7", close_points[i].fuel, 1000);
    assert(closed.eval == 0 && closed.parse == 0 && same_text(closed.failure.message, eTerm) &&
           closed.failure.position == (Nat)(deep_source - source) + close_points[i].offset);
  }
  /* D3-s6 part D: a BIND_FUN with term_body(span, NULL) as its term gives
     unknown, and the token path gives the value. */
  const Binding *deep_item = fun_named(environment, "deep");
  assert(deep_item != NULL);
  Binding bare_deep = *deep_item;
  bare_deep.term = term_body(term_tokens(deep_item->term), NULL);
  BothPaths bare_paths = both_paths(call_scope(environment, deep_item, "4 7"), &bare_deep, 1000, 1000);
  assert(bare_paths.eval == 0 && bare_paths.failure.message.size == 0 && bare_paths.parse == 1);

  /* Budget 1: the inner call spends it, and the outer body has none left. */
  BothPaths starved = body_at(environment, "deep", "4 7", 1000, 1);
  assert(starved.eval == 0 && starved.parse == 0);

  /* Keyword forms (part B1: pure, map, bind, filter and either; part B2:
     fold and unfold, also over Value): eval 1 gives parse 1 on the grid, and eval 1
     at fuel 1000 (no replay). Heads: VAR, NAME, GROUP, FUN and PARTIAL, also
     a PARTIAL of a callee with type params (mapT, foldT). A FUN head walks its
     body in check mode with no fuel margin (D3-s5 part B4), thus each head
     gives the same answer at each point (exact 1). The FOLD_VALUE rows are
     exact too: a failed f2 trial runs fold_tail (D3-s6 part B). */
  const struct {
    const char *name;
    const char *args;
    const char *value;
    int exact;
  } keyword[] = {
      {"mapK", "4 (cons 7 (cons 8 nil))", "[4,4]", 1},
      {"pureL", "4 (cons 7 (cons 8 nil))", "[4]", 1},
      {"mapP", "4 (cons 7 (cons 8 nil))", "[4,4]", 1},
      {"mapT", "4 (cons 7 (cons 8 nil))", "[4,4]", 1},
      {"mapN", "4 (cons 7 (cons 8 nil))", "[7,8]", 1},
      {"mapGP", "4 (cons 7 (cons 8 nil))", "[4,4]", 1},
      {"mapGF", "4 (cons 7 (cons 8 nil))", "[7,8]", 1},
      {"mapV", "size (cons 7 (cons 8 nil))", "[7,8]", 1},
      {"bindF", "4 (cons 7 (cons 8 nil))", "[4,7,4,8]", 1},
      {"bindP", "4 (cons 7 (cons 8 nil))", "[4,7,4,8]", 1},
      {"filterF", "flagYes (cons 7 (cons 8 nil))", "[7,8]", 1},
      {"filterP", "flagNo (cons 7 (cons 8 nil))", "[]", 1},
      {"pureO", "4 (some 7)", "4", 1},
      {"mapO", "4 (some 7)", "4", 1},
      {"mapO", "4 none", "null", 1},
      {"mapOF", "4 (some 7)", "7", 1},
      {"bindO", "4 (some 7)", "4", 1},
      {"bindOV", "half (some 7)", "7", 1},
      {"filterON", "4 (some 7)", "7", 1},
      {"filterOG", "flagNo (some 7)", "null", 1},
      {"settle", "(inl 4)", "4", 1},
      {"settleV", "size size (inr 9)", "9", 1},
      {"foldN", "4 (cons 7 (cons 8 nil))", "[7,8,4]", 1},
      {"foldP", "4 (cons 7 (cons 8 nil))", "[4,7,4,8]", 1},
      {"foldT", "4 (cons 7 (cons 8 nil))", "[4,7,4,8]", 1},
      {"foldG", "4 (cons 7 (cons 8 nil))", "[4,7,4,8]", 1},
      {"foldF", "4 (cons 7 (cons 8 nil))", "[7,8]", 1},
      {"foldV", "push (cons 7 (cons 8 nil))", "[7,8]", 1},
      {"unfoldN", "3 7", "3", 1},
      {"unfoldP", "3 7", "3", 1},
      {"unfoldG", "3 7", "3", 1},
      {"unfoldF", "3 7", "3", 1},
      {"unfoldV", "half 7", "3", 1},
      {"foldValue", "4 (valueNat 9)", "4", 1},
      {"foldValue", "4 (valueText \"a\")", "2", 1},
      {"foldValueT", "4 (valueNat 9)", "4", 1},
      {"unfoldValue", "2 \"s\"", "{\"left\":{\"left\":null}}", 1},
  };
  for (Nat i = 0; i < sizeof keyword / sizeof keyword[0]; i++) {
    GridCount count = body_grid(environment, keyword[i].name, keyword[i].args);
    assert(count.worked > 0 && (keyword[i].exact == 0 || count.differ == 0));
    BothPaths full = body_at(environment, keyword[i].name, keyword[i].args, 1000, 1000);
    assert(full.eval == 1 && same_text(full.value, text(keyword[i].value)));
  }

  /* D3-s6 part B: the grid counts of the FOLD_VALUE and UNFOLD_VALUE rows,
     and the rows at fuel 0 to 4 with budget 1000. D3-s7 part B: each
     FOLD_VALUE row had 60 unknown points, fuel 9 to 12 at each budget above
     0, where eval_inline_stepper on f2 gave 0 with no code. Now
     eval_inline_stepper gives the failure of the token path at these points.
     Thus the 60 points are failed answers, and no FOLD_VALUE row gives
     unknown.
     D3-s7 part A: at fuel 3, eval_stepper on f1 (a GROUP) calls
     eval_partial_stepper at fuel 0, which gives eFuel at the PARTIAL, the
     same failure as the token path. Thus the 15 points of fuel 3 at budget 1
     to 15 are failed answers, and no row gives unknown at fuel 0 to 4. */
  const struct {
    const char *name;
    const char *args;
    GridCount count;
    int fold;
  } valued_rows[] = {
      {"foldValue", "4 (valueNat 9)", {714, 310, 0, 0}, 1},
      {"foldValue", "4 (valueText \"a\")", {714, 310, 0, 0}, 1},
      {"foldValueT", "4 (valueNat 9)", {714, 310, 0, 0}, 1},
      {"unfoldValue", "2 \"s\"", {468, 556, 0, 0}, 0},
  };
  for (Nat i = 0; i < sizeof valued_rows / sizeof valued_rows[0]; i++) {
    assert(same_grid(body_grid(environment, valued_rows[i].name, valued_rows[i].args), valued_rows[i].count));
    for (Fuel fuel = 0; fuel < 5; fuel++) {
      BothPaths low = body_at(environment, valued_rows[i].name, valued_rows[i].args, fuel, 1000);
      assert(low.eval == 0 && low.parse == 0 && low.failure.message.size != 0);
    }
    /* D3-s7 part A: at fuel 3, a FOLD_VALUE row gives no unknown at each
       budget below 16. */
    for (Nat budget = 0; budget < 16; budget++) {
      BothPaths at_three = body_at(environment, valued_rows[i].name, valued_rows[i].args, 3, budget);
      assert(valued_rows[i].fold == 0 || at_three.eval != 0 || at_three.failure.message.size != 0);
    }
  }

  /* D3-s7 part A: the fuel 0 test of the six helper entries. eval_term at
     fuel F calls the node helper at fuel F - 1. Each row puts fuel 0 on one
     entry. In foldP, F 1 gives eval_fold at fuel 0, F 2 gives eval_stepper on
     the GROUP (pushK k) and F 3 gives eval_partial_stepper on the PARTIAL. In
     mapP, eval_structure keeps its own fuel 0 unknown, F 2 gives eval_unary on
     the GROUP (pickK k) and F 3 gives eval_partial_unary on the PARTIAL. In
     foldValueN, f1 is a NAME, thus at F 3 eval_stepper on f1 works at fuel 1
     and the trial of f2 calls eval_algebra_term at fuel 0. The trial keeps
     its failure local, and fold_tail gives the failed answer. Each row gives
     a failed answer, and both_paths compares it with the token path. */
  const struct {
    const char *name;
    const char *args;
    Fuel fuel;
  } entry_rows[] = {
      {"foldP", "4 (cons 7 (cons 8 nil))", 1},
      {"foldP", "4 (cons 7 (cons 8 nil))", 2},
      {"foldP", "4 (cons 7 (cons 8 nil))", 3},
      {"mapP", "4 (cons 7 (cons 8 nil))", 2},
      {"mapP", "4 (cons 7 (cons 8 nil))", 3},
      {"foldValueN", "4 (valueNat 9)", 3},
  };
  for (Nat i = 0; i < sizeof entry_rows / sizeof entry_rows[0]; i++) {
    BothPaths entry = body_at(environment, entry_rows[i].name, entry_rows[i].args, entry_rows[i].fuel, 1000);
    assert(entry.eval == 0 && entry.parse == 0 && entry.failure.message.size != 0);
  }

  /* D3-s7 part B: eval_inline_stepper on the inline stepper of two binders
     of foldF. eval_term at fuel F calls eval_inline_stepper at fuel F - 4.
     F 4 gives fuel 0: eFuel at the first token of the binder span (the `(`
     after `fun`). F 5 to 8 give a refusal of inline_binders in the binder
     span: F 5 eFuel at the same token, F 6 eFuel at the type of y, F 7 and 8
     eFuel in the type of a (parse_type). F 0 to 3 fail before the stepper.
     Each answer below F 9 is a failed answer, and both_paths compares it
     with the token path. F 9 and above give the value. The grid has no
     unknown point. */
  const char *stepper_at = strstr(source, "fun (y : Nat) (a : List Nat) => cons y a");
  const struct {
    Fuel fuel;
    Nat offset;
  } inline_rows[] = {
      {4, 4}, {5, 4}, {6, 9}, {7, 19}, {8, 24},
  };
  assert(same_grid(body_grid(environment, "foldF", "4 (cons 7 (cons 8 nil))"), (GridCount){715, 309, 0, 0}));
  for (Fuel fuel = 0; fuel < 13; fuel++) {
    BothPaths inline_at = body_at(environment, "foldF", "4 (cons 7 (cons 8 nil))", fuel, 1000);
    assert(fuel < 9 ? inline_at.eval == 0 && inline_at.failure.message.size != 0 : inline_at.eval == 1);
  }
  for (Nat i = 0; i < sizeof inline_rows / sizeof inline_rows[0]; i++) {
    BothPaths refusal = body_at(environment, "foldF", "4 (cons 7 (cons 8 nil))", inline_rows[i].fuel, 1000);
    assert(refusal.failure.position == (Nat)(stepper_at - source) + inline_rows[i].offset &&
           same_text(refusal.failure.message, eFuel));
  }

  /* D3-s7 part B: a FUN node with an empty binder span. At F 4, the first
     binder position is unavailable; at F 5 and 6, inline_binders refuses at
     position 0, the end of the span. Thus eval_inline_stepper gives 0 with
     no code (unknown, a replay). Keep the body tokens for the token path. */
  const Term *fold_f = body_term(environment, "foldF");
  const Term *group_f = fold_f->args->head;
  Term bare_fun = *group_f->args->head;
  assert(group_f->tag == TERM_GROUP && bare_fun.tag == TERM_FUN && bare_fun.tokens.size != 0);
  bare_fun.tokens = (Tokens){0};
  Term bare_group = *group_f;
  bare_group.args = terms_item(&bare_fun, NULL);
  Term bare_fold = *fold_f;
  bare_fold.args = terms_item(&bare_group, fold_f->args->tail);
  const Binding *fold_f_item = fun_named(environment, "foldF");
  Binding bare_item = *fold_f_item;
  bare_item.term = term_body(term_tokens(fold_f_item->term), &bare_fold);
  const Bindings *fold_f_scope = call_scope(environment, fold_f_item, "4 (cons 7 (cons 8 nil))");
  for (Fuel fuel = 4; fuel < 7; fuel++) {
    BothPaths bare_paths = both_paths(fold_f_scope, &bare_item, fuel, 1000);
    assert(bare_paths.eval == 0 && bare_paths.failure.message.size == 0);
  }

  /* D3-s7 part A: a TERM_FOLD node with a NULL stepper. At fuel 2,
     eval_fold calls eval_stepper at fuel 0 on the NULL term. The NULL guard
     comes before the fuel 0 test, thus the answer is 0 with no code. */
  const Binding *fold_item = fun_named(environment, "foldP");
  Binding no_stepper = *fold_item;
  no_stepper.term = term_form(TERM_FOLD, 0, 1, one(NULL));
  BothPaths no_stepper_paths =
      both_paths(call_scope(environment, fold_item, "4 (cons 7 (cons 8 nil))"), &no_stepper, 2, 1000);
  assert(no_stepper_paths.eval == 0 && no_stepper_paths.failure.message.size == 0);

  /* D3-s4 part B: closures by term. A closure param applied in the body
     (twice), a VAR head bound to a closure (mapV, foldV) and a PARTIAL head
     over a closure param (mapC, foldC). The args text gives the closure: a
     name or a partial gives the body term of the function. An inline fun
     gives a Value that keeps the Term of its FUN node, thus its closure has
     the checked body Term as the callee (D8 part A). Each row gives the same
     answer at each point of the grid. */
  const struct {
    const char *name;
    const char *args;
    const char *value;
  } closures[] = {
      {"twice", "size 4", "4"},
      {"twice", "(pickK 3) 4", "3"},
      {"twice", "(fun (y : Nat) => pickK 5 y) 4", "5"},
      {"mapV", "(pickK 3) (cons 7 (cons 8 nil))", "[3,3]"},
      {"mapV", "(fun (y : Nat) => pickK 5 y) (cons 7 (cons 8 nil))", "[5,5]"},
      {"foldV", "(pushK 4) (cons 7 (cons 8 nil))", "[4,7,4,8]"},
      {"foldV", "(fun (y : Nat) (a : List Nat) => cons y a) (cons 7 (cons 8 nil))", "[7,8]"},
      {"mapC", "pickK 4 (cons 7 (cons 8 nil))", "[4,4]"},
      {"mapC", "(fun (a : Nat) (b : Nat) => a) 4 (cons 7 (cons 8 nil))", "[4,4]"},
      {"foldC", "pushK 4 (cons 7 (cons 8 nil))", "[4,7,4,8]"},
  };
  for (Nat i = 0; i < sizeof closures / sizeof closures[0]; i++) {
    GridCount count = body_grid(environment, closures[i].name, closures[i].args);
    assert(count.worked > 0 && count.differ == 0);
    assert(no_unknown(closures[i].name) == 0 || count.unknown == 0);
    BothPaths full = body_at(environment, closures[i].name, closures[i].args, 1000, 1000);
    assert(full.eval == 1 && same_text(full.value, text(closures[i].value)));
  }
  /* The closure of f (the second binding of the call scope): a name gives the
     body term of size; an inline fun gives the TERM_BODY of its FUN node,
     with the checked body Term as the callee (D8 part A). */
  const Binding *twice_item = fun_named(environment, "twice");
  const Bindings *name_scope = call_scope(environment, twice_item, "size 4");
  assert(name_scope->tail->head.kind == BIND_CLOSURE && name_scope->tail->head.term->callee != NULL);
  const Bindings *fun_scope = call_scope(environment, twice_item, "(fun (y : Nat) => pickK 5 y) 4");
  assert(fun_scope->tail->head.kind == BIND_CLOSURE && fun_scope->tail->head.term->tag == TERM_BODY);
  assert(fun_scope->tail->head.term->callee != NULL);
  test_d8_body_term(environment);

  /* Budget 1 on a map over 3 items: the first item spends it. eval_term
     gives a failed answer, eBudget at the first token of the body, the same
     failure as the token path (D3-s5 part E). */
  const Binding *mapped = fun_named(environment, "mapK");
  const Bindings *three = call_scope(environment, mapped, "4 (cons 1 (cons 2 (cons 3 nil)))");
  BothPaths starved_map = both_paths(three, mapped, 1000, 1);
  assert(starved_map.eval == 0 && starved_map.parse == 0);
  assert(starved_map.failure.position == (Nat)(strstr(source, "=> pickK k y) ys") + 3 - source) &&
         same_text(starved_map.failure.message, eBudget));
  const Value *starved_value;
  Tokens starved_rest;
  Nat starved_left;
  assert(parse_term(1000, 1, 0, mapped->type, three, term_tokens(mapped->term), &starved_value, &starved_rest,
                    &starved_left, NULL, &failure) == 0);
  assert(failure.position == (Nat)(strstr(source, "=> pickK k y) ys") + 3 - source) &&
         same_text(failure.message, eBudget));

  /* Dependent callees (D3-s5 part C): eval_apply gives instantiate_result
     the argument tokens after the type arguments, as the token path does,
     thus the two paths give the same answer at each point of the grid.
     viaSame has a callee with a dependent param; viaRefl also has a callee
     with a dependent result (an Eq proof) as an argument. */
  const char *dependent_rows[] = {"viaSame", "viaRefl"};
  const char *dependent_values[] = {"4", "7"};
  for (Nat i = 0; i < sizeof dependent_rows / sizeof dependent_rows[0]; i++) {
    GridCount count = body_grid(environment, dependent_rows[i], "4 7");
    assert(count.worked > 0 && count.differ == 0);
    BothPaths full = body_at(environment, dependent_rows[i], "4 7", 1000, 1000);
    assert(full.eval == 1 && same_text(full.value, text(dependent_values[i])));
  }

  /* Budget 1 on a fold over 3 items (part B2): the first step spends it.
     The token path gives eBudget at the first token of the body of the
     inline fun. eval_term gives a failed answer with the same Failure (part
     E). */
  const Binding *folded = fun_named(environment, "foldF");
  const Bindings *three_folded = call_scope(environment, folded, "4 (cons 1 (cons 2 (cons 3 nil)))");
  BothPaths starved_fold = both_paths(three_folded, folded, 1000, 1);
  assert(starved_fold.eval == 0);
  assert(parse_term(1000, 1, 0, folded->type, three_folded, term_tokens(folded->term), &starved_value,
                    &starved_rest, &starved_left, NULL, &failure) == 0);
  assert(failure.position == (Nat)(strstr(source, "=> cons y a) nil ys") + 3 - source) &&
         same_text(failure.message, eBudget));
  assert(starved_fold.failure.position == failure.position && same_text(starved_fold.failure.message, eBudget));

  /* FOLD_VALUE at fuel 8 (part B2): second_function gives 0, thus the
     token path selects FOLD and fails at the first token of the second
     function. The f2 trial of eval_term gives 0, thus eval_term runs
     fold_tail on the FOLD_VALUE span and gives the same failed answer
     (D3-s6 part B). A FOLD_VALUE node with an empty span gives unknown. */
  const Binding *valued = fun_named(environment, "foldValue");
  const Bindings *nine = call_scope(environment, valued, "4 (valueNat 9)");
  BothPaths valued8 = both_paths(nine, valued, 8, 1000);
  assert(parse_term(8, 1000, 0, valued->type, nine, term_tokens(valued->term), &starved_value, &starved_rest,
                    &starved_left, NULL, &failure) == 0);
  assert(failure.position == (Nat)(strstr(source, "(fun (b : Flag) => 1)") + 1 - source));
  assert(valued8.eval == 0 && valued8.failure.position == failure.position &&
         same_text(valued8.failure.message, failure.message));
  const Term *spanned = body_term(environment, "foldValue");
  assert(spanned->tag == TERM_FOLD_VALUE && spanned->tokens.size != 0);
  Term bare = *spanned;
  bare.tokens = (Tokens){0};
  Failure bare_failure = {0, {NULL, 0}};
  assert(eval_term(8, 1000, valued->type, nine, &bare, &starved_value, &starved_left, &bare_failure) == 0 &&
         bare_failure.message.size == 0);

  /* Term.end (part E, ruling (a)): filterON at budget 2. Term.end of the
     last argument is the next token of the source, and the token path runs
     on the body tokens and gives eFuel at first_position of the empty rest
     (0). The fuel step after the last argument gives eFuel at Term.end of
     the application. That is the end of the TERM_BODY of spanned_body, and
     body_answer moves the failure to 0 (D8 part A). At fuel 3, eval_term
     thus gives the Failure of the token path (eFuel at 0). D3-s7 part A: at fuel 2,
     eval_unary on keep gets fuel 0 and gives eFuel at keep, the same failure
     as the token path. */
  const Binding *filtered = fun_named(environment, "filterON");
  const Bindings *some7 = call_scope(environment, filtered, "4 (some 7)");
  BothPaths at_end = both_paths(some7, filtered, 3, 2);
  assert(at_end.eval == 0 && at_end.failure.position == 0 && same_text(at_end.failure.message, eFuel));
  BothPaths before_end = both_paths(some7, filtered, 2, 2);
  assert(before_end.eval == 0 && before_end.parse == 0 && before_end.failure.position != 0 &&
         same_text(before_end.failure.message, eFuel));
  assert(parse_term(3, 2, 0, filtered->type, some7, term_tokens(filtered->term), &starved_value, &starved_rest,
                    &starved_left, NULL, &failure) == 0);
  assert(failure.position == 0 && same_text(failure.message, eFuel));

  /* Type arguments: eval_apply reads them with type_arguments, as the token
     path does (D3-s5 part B), thus the two paths give the same answer at each
     point of the grid. At the old margin term_text(APPLY).size + 2, eval 1
     and parse 1. */
  GridCount via = body_grid(environment, "viaNat", "4 7");
  assert(via.worked > 0 && via.differ == 0);
  assert(same_text(body_at(environment, "viaNat", "4 7", 1000, 1000).value, text("7")));
  Fuel margin = term_text(fun_named(environment, "viaNat")->term).size + 2;
  BothPaths at_margin = body_at(environment, "viaNat", "4 7", margin, 1000);
  assert(at_margin.eval == 1 && at_margin.parse == 1);

  /* CONSTRUCT by lookup (D3-s6 part A): a CONSTRUCT node in a scope that
     binds its name. eval_term takes the name branch of the token path, one
     row for each Binding kind. The token path builds no such node (A1: 0
     hits over all gates), thus the rows build the node by hand or retag the
     APPLY node of a body. */
  const Binding *lookup_hit;
  const Binding *size_fun = fun_named(environment, "size");
  const Bindings *size_at = call_scope(environment, size_fun, "4");
  /* BIND_VALUE with no arguments: the TERM_VAR arm. */
  GridCount value_name = term_grid(size_at, size_fun, construct_body("n", "n", NULL));
  assert(value_name.worked > 0 && value_name.unknown == 0 && value_name.differ == 0);
  /* BIND_VALUE with arguments: unknown after the fuel 0 and budget 0
     failures. The token path takes the value and leaves the arguments in
     rest. */
  GridCount value_args = term_grid(size_at, size_fun, construct_body("n 5", "n", one(term_number(2, 1, 5))));
  assert(value_args.worked == 0 && value_args.unknown == 63 * 15);
  /* BIND_ARROW: eTerm at the node position, the Failure of parse_term at
     each point. BIND_TYPE shares the case label in both paths; call_scope
     cannot build a scope with a type name. */
  const Binding *twice_fun = fun_named(environment, "twice");
  const Bindings *twice_at = call_scope(environment, twice_fun, "size 4");
  assert(lookup(text("One"), twice_at, &lookup_hit) && lookup_hit->kind == BIND_ARROW);
  GridCount arrow_name = term_grid(twice_at, twice_fun, construct_body("One", "One", NULL));
  assert(arrow_name.failed == 64 * 16 && arrow_name.differ == 0);
  /* BIND_FUN and BIND_CLOSURE: the APPLY view at the same fuel, thus the
     same count as the grid of the body. */
  const Binding *deep_fun = fun_named(environment, "deep");
  const Bindings *deep_at = call_scope(environment, deep_fun, "4 7");
  const Term *deep_apply = deep_fun->term->callee;
  assert(deep_apply->tag == TERM_APPLY);
  assert(lookup(deep_apply->name, deep_at, &lookup_hit) && lookup_hit->kind == BIND_FUN);
  const Term *deep_body = term_body(term_tokens(deep_fun->term), as_construct(deep_apply, deep_apply->args));
  assert(same_grid(term_grid(deep_at, deep_fun, deep_body), body_grid(environment, "deep", "4 7")));
  const Term *twice_apply = twice_fun->term->callee;
  assert(twice_apply->tag == TERM_APPLY);
  assert(lookup(twice_apply->name, twice_at, &lookup_hit) && lookup_hit->kind == BIND_CLOSURE);
  const Term *twice_body = term_body(term_tokens(twice_fun->term), as_construct(twice_apply, twice_apply->args));
  assert(same_grid(term_grid(twice_at, twice_fun, twice_body), body_grid(environment, "twice", "size 4")));

  /* D3-s4 part C: a FUN or a PARTIAL argument at an arrow expected type in
     the body (the checked tree). Each row gives the value at fuel 1000 by
     eval_term, thus the replay count is 0. Each row gives the same answer at
     each point of the grid: the inline fun reads its binders with
     inline_binders, as the token path does, and a PARTIAL of a callee with
     type params (twiceT) keeps its type arguments (D3-s5 part B). */
  const struct {
    const char *name;
    Nat exact;
  } arrow_rows[] = {{"twiceF", 1}, {"twiceP", 1}, {"twiceT", 1}};
  Nat replays = 0;
  for (Nat i = 0; i < sizeof arrow_rows / sizeof arrow_rows[0]; i++) {
    GridCount count = body_grid(environment, arrow_rows[i].name, "4 7");
    assert(count.worked > 0 && (arrow_rows[i].exact == 0 || count.differ == 0));
    BothPaths full = body_at(environment, arrow_rows[i].name, "4 7", 1000, 1000);
    assert(same_text(full.value, text("4")));
    replays += full.eval != 1;
  }
  assert(replays == 0);

  /* The closure by term. The argument is a GROUP (the atom rule). A FUN
     gives a Value with the TERM_BODY of the FUN node. A PARTIAL gives the
     name and the bound values. */
  const Value *arrow_value;
  Nat arrow_left;
  const Binding *fun_item = fun_named(environment, "twiceF");
  const Term *fun_group = fun_item->term->callee->args->head;
  const Term *fun_node = fun_group->args->head;
  assert(fun_group->tag == TERM_GROUP && fun_node->tag == TERM_FUN);
  assert(eval_term(1000, 1000, one_type, call_scope(environment, fun_item, "4 7"), fun_group, &arrow_value,
                   &arrow_left, &(Failure){0, {NULL, 0}}) == 1);
  assert(arrow_value->term == fun_node->args->head);
  const Binding *partial_item = fun_named(environment, "twiceP");
  const Term *partial_group = partial_item->term->callee->args->head;
  assert(partial_group->tag == TERM_GROUP && partial_group->args->head->tag == TERM_PARTIAL);
  assert(eval_term(1000, 1000, one_type, call_scope(environment, partial_item, "4 7"), partial_group, &arrow_value,
                   &arrow_left, &(Failure){0, {NULL, 0}}) == 1);
  assert(arrow_value->kind == VALUE_ITEMS && arrow_value->items->head->kind == VALUE_TEXT);
  assert(same_text(arrow_value->items->head->text, text("pickK")));

  /* NAME and VAR arguments (D3-s5 part D, Q-S5-4): eval_name_argument
     mirrors the name branch of parse_term at an arrow expected type, thus
     the two paths give the same answer at each point of the grid. twiceN
     has a NAME (the function size). twiceV has a VAR (the closure param g,
     bound to size). The D3-s4 fallback assert "a NAME argument gives 0" is
     now a row with eval 1. */
  const struct {
    const char *name;
    const char *args;
  } name_rows[] = {{"twiceN", "4 7"}, {"twiceV", "size 7"}};
  for (Nat i = 0; i < sizeof name_rows / sizeof name_rows[0]; i++) {
    GridCount count = body_grid(environment, name_rows[i].name, name_rows[i].args);
    assert(count.worked > 0 && count.differ == 0);
    BothPaths name_arrow = body_at(environment, name_rows[i].name, name_rows[i].args, 1000, 1000);
    assert(name_arrow.eval == 1 && same_text(name_arrow.value, text("7")));
  }

  /* D3-s6 part C: the binder slots. Each row gives the same answer on the
     two paths at each point of the grid, and the value at fuel 1000. viaNat
     and twiceT: a function with type params (type_frame at the BIND_FUN
     site and at typed_closure). twiceF: an inline fun in a function, its
     body in check mode on bind_params. mapK: the unary binder in check mode
     (eval_inline_unary). twiceFF: a fun in a fun. twiceS: an inline binder
     with the name of a parameter (a shadow), thus the value is n. twiceV
     (D3-s7 part C): a VAR at an arrow type (the param g), thus
     eval_name_argument finds its item by slot. */
  const struct {
    const char *name;
    const char *args;
    const char *value;
  } slot_rows[] = {{"viaNat", "4 7", "7"},           {"twiceT", "4 7", "4"},  {"twiceF", "4 7", "4"},
                   {"mapK", "4 (cons 1 nil)", NULL}, {"twiceFF", "4 7", "7"}, {"twiceS", "4 7", "7"},
                   {"twiceV", "size 7", "7"}};
  for (Nat i = 0; i < sizeof slot_rows / sizeof slot_rows[0]; i++) {
    GridCount count = body_grid(environment, slot_rows[i].name, slot_rows[i].args);
    assert(count.worked > 0 && count.differ == 0);
    BothPaths full = body_at(environment, slot_rows[i].name, slot_rows[i].args, 1000, 1000);
    assert(full.eval == 1 && (slot_rows[i].value == NULL || same_text(full.value, text(slot_rows[i].value))));
  }

  /* D3-s6 part C: each TERM_VAR of the full grid finds its binder by slot. */
  assert(slot_mismatches() == 0);

  /* The fallback: a TERM_VAR with a wrong index gives the value of lookup
     by name, and the count goes up by 1. */
  const Value *fallback_value;
  Nat fallback_left;
  Nat misses = slot_mismatches();
  assert(eval_term(1000, 1000, size_fun->type, size_at, term_var(0, 1, text("n"), 5), &fallback_value,
                   &fallback_left, &(Failure){0, {NULL, 0}}) == 1);
  assert(same_text(printed(fallback_value), text("4")));
  assert(slot_mismatches() == misses + 1);

  /* D3-s7 part C: a TERM_VAR at an arrow type goes to eval_name_argument,
     and it finds its item by slot. A wrong index gives the answer of lookup
     by name (the same as the right index), and the count goes up by 1. */
  const Binding *twice_v = fun_named(environment, "twiceV");
  const Bindings *twice_v_at = call_scope(environment, twice_v, "size 7");
  const Binding *g_item;
  assert(lookup(text("g"), twice_v_at, &g_item) && g_item->kind == BIND_CLOSURE);
  const LType *g_type = arrow_type(g_item->params, g_item->type);
  const Value *slot_value;
  Nat slot_left;
  Nat arrow_misses = slot_mismatches();
  assert(eval_term(1000, 1000, g_type, twice_v_at, term_var(0, 1, text("g"), 0), &slot_value, &slot_left,
                   &(Failure){0, {NULL, 0}}) == 1);
  assert(slot_mismatches() == arrow_misses);
  assert(eval_term(1000, 1000, g_type, twice_v_at, term_var(0, 1, text("g"), 5), &fallback_value,
                   &fallback_left, &(Failure){0, {NULL, 0}}) == 1);
  assert(same_text(printed(fallback_value), printed(slot_value)));
  assert(slot_mismatches() == arrow_misses + 1);
}

/* both_paths on the body of the function name in the scope of the function
   scope_name, called with args, at the result type of scope_name. In that
   scope a name of the body can have a different type (D3-s8 part A). */
static BothPaths swapped_at(const Bindings *environment, const char *name, const char *scope_name, const char *args) {
  const Binding *host = fun_named(environment, scope_name);
  const Binding *guest = fun_named(environment, name);
  assert(host != NULL && guest != NULL);
  Binding swapped = *host;
  swapped.term = guest->term;
  return both_paths(call_scope(environment, host, args), &swapped, 1000, 1000);
}

/* both_paths on item, with fun in place of the FUN in the first argument (a
   GROUP) of the body node. The body tokens stay, thus the token path reads
   the original body (D3-s7 part B). */
static BothPaths fun_swapped(const Bindings *scope, const Binding *item, const Term *fun) {
  const Term *node = item->term->callee;
  Term group = *node->args->head;
  group.args = terms_item(fun, NULL);
  Term changed = *node;
  changed.args = terms_item(&group, node->args->tail);
  Binding copy = *item;
  copy.term = term_body(term_tokens(item->term), &changed);
  return both_paths(scope, &copy, 1000, 1000);
}

/* 1 when both paths give 0 with the message at the position. */
static int refused_at(BothPaths paths, Text message, Nat position) {
  return paths.eval == 0 && paths.parse == 0 && same_text(paths.failure.message, message) &&
         paths.failure.position == position;
}

/* 1 when the node path gives 0 with no code (an unknown answer, a replay). */
static int unknown_answer(BothPaths paths) {
  return paths.eval == 0 && paths.failure.message.size == 0;
}

/* The offset of mark in source. */
static Nat offset_of(const char *source, const char *mark) {
  const char *at = strstr(source, mark);
  assert(at != NULL);
  return (Nat)(at - source);
}

/* D3-s8 part A: the new failed answers of the node path, and the unknown
   answers that stay. Each row has the token answer as the expected answer.
   The source has its own definitions, thus the grid counts of the other
   rows do not change. */
static void test_refused_nodes(void) {
  const char *source =
      "def Num : Type 0 := Nat\n"
      "def One : Type 0 := (n : Nat) -> Nat\n"
      "def pickK : (k : Nat) -> (n : Nat) -> Nat := fun (k : Nat) (n : Nat) => k\n"
      "def twice : (f : One) -> (n : Nat) -> Nat := fun (f : One) (n : Nat) => f (f n)\n"
      "def someOf : (k : Nat) -> (y : Nat) -> Option (Prod Nat Nat) := "
      "fun (k : Nat) (y : Nat) => some (pair k y)\n"
      "def five : Nat := 5\n"
      "def mapNum : (k : Nat) -> (ys : List Nat) -> List Nat := fun (k : Nat) (ys : List Nat) => "
      "map (fun (y : Num) => y) ys\n"
      "def twiceNum : (k : Nat) -> (n : Nat) -> Nat := fun (k : Nat) (n : Nat) => twice (fun (y : Num) => y) n\n"
      "def foldF : (k : Nat) -> (ys : List Nat) -> List Nat := fun (k : Nat) (ys : List Nat) => "
      "fold (fun (y : Nat) (a : List Nat) => cons y a) nil ys\n"
      "def numScope : (Num : Nat) -> (ys : List Nat) -> List Nat := fun (Num : Nat) (ys : List Nat) => ys\n"
      "def numScopeN : (Num : Nat) -> (n : Nat) -> Nat := fun (Num : Nat) (n : Nat) => n\n"
      "def fstP : (n : Nat) -> (p : Prod Nat Nat) -> Nat := fun (n : Nat) (p : Prod Nat Nat) => first p\n"
      "def sndP : (n : Nat) -> (p : Prod Nat Nat) -> Nat := fun (n : Nat) (p : Prod Nat Nat) => second p\n"
      "def symmP : (n : Nat) -> (p : Eq Nat n n) -> Eq Nat n n := fun (n : Nat) (p : Eq Nat n n) => symm p\n"
      "def transP : (n : Nat) -> (p : Eq Nat n n) -> Eq Nat n n := fun (n : Nat) (p : Eq Nat n n) => trans p p\n"
      "def reflP : (n : Nat) -> (p : Eq Nat n n) -> Eq Nat n n := fun (n : Nat) (p : Eq Nat n n) => refl\n"
      "def valP : (n : Nat) -> (p : Nat) -> Nat := fun (n : Nat) (p : Nat) => p\n"
      "def flagP : (n : Nat) -> (p : Flag) -> Nat := fun (n : Nat) (p : Flag) => n\n"
      "def useFive : (n : Nat) -> (p : Nat) -> Nat := fun (n : Nat) (p : Nat) => five\n"
      "def fiveScope : (n : Nat) -> (five : Flag) -> Nat := fun (n : Nat) (five : Flag) => n\n"
      "def keep : (n : Nat) -> Flag := fun (n : Nat) => flagYes\n"
      "def filterT : (k : Nat) -> (s : Text) -> Text := fun (k : Nat) (s : Text) => filter keep s\n"
      "def unfoldL : (k : Nat) -> (n : Nat) -> List Nat := fun (k : Nat) (n : Nat) => unfold (someOf k) 3 n\n"
      "def textHost : (k : Nat) -> (n : Nat) -> Text := fun (k : Nat) (n : Nat) => \"x\"\n";
  const Bindings *environment = NULL;
  Failure failure;
  assert(check_definitions(text(source), &environment, &failure));

  /* U1 and U2: in numScope, Num is a Nat value and not a type. Thus the
     binder of the inline function refuses. */
  assert(refused_at(swapped_at(environment, "mapNum", "numScope", "4 (cons 7 nil)"), text("expected a supported type"),
                    offset_of(source, "Num) => y) ys")));
  assert(refused_at(swapped_at(environment, "twiceNum", "numScopeN", "4 5"), text("expected a supported type"),
                    offset_of(source, "Num) => y) n")));

  /* U3: rebuild refuses an item above 255 at Text. unfold: the body of
     unfoldL gives the items 300 in the scope of textHost. filter: s holds
     the items of cons 300 nil in place of a text. */
  assert(refused_at(swapped_at(environment, "unfoldL", "textHost", "300 5"), eByte,
                    offset_of(source, "unfold (someOf")));
  const LType *list_nat;
  Tokens rest;
  Nat left;
  const Value *items_300;
  assert(parse_type(1000, 1000, 0, NULL, lexed("List Nat"), &list_nat, &rest, &left, &failure));
  assert(parse_term(1000, 1000, 0, list_nat, NULL, lexed("cons 300 nil"), &items_300, &rest, &left, NULL, &failure));
  const Binding *filter_item = fun_named(environment, "filterT");
  const Bindings *filter_scope = call_scope(environment, filter_item, "4 \"ab\"");
  assert(same_text(filter_scope->head.name, text("s")));
  Bindings byte_scope = *filter_scope;
  byte_scope.head.value = items_300;
  assert(refused_at(both_paths(&byte_scope, filter_item, 1000, 1000), eByte, offset_of(source, "filter keep")));

  /* U4: p is a Nat. Thus first and second do not get a pair, symm and trans
     do not get a proof, and refl does not get an equality type. */
  assert(refused_at(swapped_at(environment, "fstP", "valP", "4 5"), eProduct, offset_of(source, "first p")));
  assert(refused_at(swapped_at(environment, "sndP", "valP", "4 5"), eProduct, offset_of(source, "second p")));
  assert(refused_at(swapped_at(environment, "symmP", "valP", "4 5"), eProof, offset_of(source, "symm p")));
  assert(refused_at(swapped_at(environment, "transP", "valP", "4 5"), eProof, offset_of(source, "trans p")));
  assert(refused_at(swapped_at(environment, "reflP", "valP", "4 5"), eTerm, offset_of(source, "refl\n")));

  /* U5: a VAR, a NAME and a CONSTRUCT over a BIND_VALUE of type Flag where
     the body expects a Nat, and a proof name over a value that is not a
     proof (a proof out of scope). */
  assert(refused_at(swapped_at(environment, "valP", "flagP", "4 flagYes"), eTerm, offset_of(source, "=> p\n") + 3));
  assert(refused_at(swapped_at(environment, "useFive", "fiveScope", "4 flagYes"), eTerm,
                    offset_of(source, "=> five") + 3));
  const Binding *flag_item = fun_named(environment, "flagP");
  Binding construct = *flag_item;
  construct.term = construct_body("p", "p", NULL);
  assert(refused_at(both_paths(call_scope(environment, flag_item, "4 flagYes"), &construct, 1000, 1000), eTerm, 0));
  const LType *nat;
  assert(parse_type(1000, 1000, 0, NULL, lexed("Nat"), &nat, &rest, &left, &failure));
  LType equality = {.tag = TY_EQ, .left = nat, .lhs = {.kind = VAL_VAR}, .rhs = {.kind = VAL_VAR}};
  const Value *five;
  assert(parse_term(1000, 1000, 0, nat, NULL, lexed("5"), &five, &rest, &left, NULL, &failure));
  Bindings proof_scope = {{.kind = BIND_VALUE, .name = text("proof"), .type = &equality, .value = five}, NULL};
  Binding proof_var = {.type = &equality, .term = term_body(lexed("proof"), term_var(0, 0, text("proof"), 0))};
  assert(refused_at(both_paths(&proof_scope, &proof_var, 1000, 1000), eTerm, 0));
  Binding proof_name = {.type = &equality,
                        .term = term_body(lexed("proof"), term_named(TERM_NAME, 0, 0, text("proof"), NULL, NULL))};
  assert(refused_at(both_paths(&proof_scope, &proof_name, 1000, 1000), eTerm, 0));

  /* The unknown answers that stay (the D3-s8 fallback list). U1: a binder
     span of 0 or 1 token, two binders, and fuel 4 (the node path gives
     unknown at the inline binder, the token path gives eFuel at fun). U2: a
     FUN with no body, and a FUN whose body is not a TERM_BODY. */
  const Binding *map_item = fun_named(environment, "mapNum");
  const Bindings *map_scope = call_scope(environment, map_item, "4 (cons 7 nil)");
  const Term *map_fun = map_item->term->callee->args->head->args->head;
  const Term *fold_fun = fun_named(environment, "foldF")->term->callee->args->head->args->head;
  assert(map_fun->tag == TERM_FUN && fold_fun->tag == TERM_FUN && map_fun->tokens.size > 1);
  Term no_span = *map_fun;
  no_span.tokens = (Tokens){0};
  Term one_token = *map_fun;
  one_token.tokens.size = 1;
  Term two_binders = *map_fun;
  two_binders.tokens = fold_fun->tokens;
  assert(unknown_answer(fun_swapped(map_scope, map_item, &no_span)));
  assert(unknown_answer(fun_swapped(map_scope, map_item, &one_token)));
  assert(unknown_answer(fun_swapped(map_scope, map_item, &two_binders)));
  assert(unknown_answer(both_paths(map_scope, map_item, 4, 1000)));
  const Binding *twice_item = fun_named(environment, "twiceNum");
  const Term *twice_fun = twice_item->term->callee->args->head->args->head;
  assert(twice_fun->tag == TERM_FUN && twice_fun->args->head->tag == TERM_BODY);
  Term no_body = *twice_fun;
  no_body.args = NULL;
  Term var_body = *twice_fun;
  var_body.args = twice_item->term->callee->args->tail;
  const Bindings *twice_scope = call_scope(environment, twice_item, "4 5");
  assert(unknown_answer(fun_swapped(twice_scope, twice_item, &no_body)));
  assert(unknown_answer(fun_swapped(twice_scope, twice_item, &var_body)));
}

/* The count of marker names in the term. Each one is a TERM_VAR with the
   index of its marker. */
static Nat marker_vars_at(const Term *term) {
  if (term == NULL) return 0;
  Nat index;
  Nat count = 0;
  if (marker_index(term->name, &index)) {
    assert(term->tag == TERM_VAR && term->index == index);
    count = 1;
  }
  count = count + marker_vars_at(term->callee);
  for (const Terms *at = term->args; at != NULL; at = at->tail) count = count + marker_vars_at(at->head);
  return count;
}

/* A grid row: both sides keep a node with the marker variables, and
   same_val on the nodes gives the answer of the printed sides. */
static void val_row(Val left, Val right, Nat expected, Nat left_markers, Nat right_markers) {
  assert(left.kind == VAL_TERM && right.kind == VAL_TERM && left.node != NULL && right.node != NULL);
  assert(marker_vars_at(left.node) == left_markers && marker_vars_at(right.node) == right_markers);
  assert(same_text(val_text(left), val_text(right)) == expected);
  assert(same_val(left, right) == expected);
}

static void test_val_terms(void) {
  const char *source =
      "def someA : (n : Nat) -> Eq (Option Nat) (some n) (some n) := fun (n : Nat) => refl\n"
      "def someB : (n : Nat) -> (m : Nat) -> (e : Eq (Option Nat) (some n) (some m)) -> "
      "Eq (Option Nat) (some m) (some n) := fun (n : Nat) (m : Nat) (e : Eq (Option Nat) (some n) (some m)) => symm e\n"
      "def listA : (n : Nat) -> Eq (List Nat) (cons n nil) (cons n nil) := fun (n : Nat) => refl\n"
      "def pairA : (n : Nat) -> Eq (Prod Nat Nat) (pair n 5) (pair n 5) := fun (n : Nat) => refl\n"
      "def pairB : (n : Nat) -> Eq (Prod Nat Nat) (pair n 6) (pair n 6) := fun (n : Nat) => refl\n";
  const Bindings *environment = NULL;
  Failure failure;
  assert(check_definitions(text(source), &environment, &failure));
  Val some_a;
  Val some_a_rhs;
  Val some_m;
  Val some_n;
  Val list_a;
  Val list_a_rhs;
  Val pair_5;
  Val pair_5_rhs;
  Val pair_6;
  Val pair_6_rhs;
  const LType *a;
  assert(sides_of(fun_named(environment, "someA")->type, &a, &some_a, &some_a_rhs));
  assert(sides_of(fun_named(environment, "someB")->type, &a, &some_m, &some_n));
  assert(sides_of(fun_named(environment, "listA")->type, &a, &list_a, &list_a_rhs));
  assert(sides_of(fun_named(environment, "pairA")->type, &a, &pair_5, &pair_5_rhs));
  assert(sides_of(fun_named(environment, "pairB")->type, &a, &pair_6, &pair_6_rhs));

  /* Equal atoms, in one definition and in two definitions. */
  val_row(some_a, some_a_rhs, 1, 1, 1);
  val_row(some_a, some_n, 1, 1, 1);
  val_row(pair_5, pair_5_rhs, 1, 1, 1);
  /* Another constructor, another marker, another literal. */
  val_row(some_a, list_a, 0, 1, 1);
  val_row(some_m, some_n, 0, 1, 1);
  val_row(pair_5, pair_6, 0, 1, 1);
  /* No row has another fun binder name: mark_side refuses fun in a
     computed side. Thus no grid row has two different answers. */
}

static Val lhs_of(const Bindings *environment, const char *name) {
  const LType *a;
  Val lhs;
  Val rhs;
  assert(sides_of(fun_named(environment, name)->type, &a, &lhs, &rhs));
  return lhs;
}

/* A rename row (D3-s9 part B): instantiate_side on the left side of callee
   in the body of outer, with the arguments in args. The renamed side keeps
   a node with the marker variables, and kept_side on the node is 1 only
   with a marker. */
static void rename_row(const Bindings *environment, const char *callee, const char *args, Nat answer, Nat markers) {
  const Binding *item = fun_named(environment, callee);
  /* The body scope of program.c parse_function: body_marker on the bound
     parameters of outer. */
  Bindings *body = arena_alloc(sizeof *body);
  *body = (Bindings){.head = body_marker(2),
                     .tail = bind_params(fun_named(environment, "outer")->params, NULL, environment)};
  const Values *values;
  Tokens rest;
  Nat left;
  const Terms *terms = NULL;
  Failure failure;
  Tokens tokens = lexed(args);
  assert(parse_arguments(1000, 1000, 1, param_types(item->params), body, tokens, &values, &rest, &left, &terms,
                         &failure));
  assert(rest.size == 0);
  Val result;
  assert(instantiate_side(1000, 1000, body, item->params, values, terms, tokens, lhs_of(environment, callee), &result,
                          &(Nat){0}, &(Failure){0, {NULL, 0}}) == answer);
  if (answer == 0) return;
  assert(result.kind == VAL_TERM && result.node != NULL);
  assert(marker_vars_at(result.node) == markers);
  assert(kept_side(result) == (markers > 0));
}

/* A closed constructor substituted into a computed side must compare as
   the same constructor written directly in another proof. */
static void test_closed_marker_nodes(void) {
  const char *cases[][2] = {{"Flag", "flagYes"}, {"Flag", "flagNo"}, {"Option Nat", "none"},
                            {"List Nat", "nil"}, {"Text", "textEnd"}, {"Value", "valueNull"},
                            {"Values", "valuesEnd"}, {"Attrs", "attrsEnd"}};
  for (size_t at = 0; at < sizeof cases / sizeof *cases; at++) {
    char source[2048];
    const char *type = cases[at][0];
    const char *atom = cases[at][1];
    int length = snprintf(source, sizeof source,
                          "def wrap : (x : %s) -> (n : Nat) -> Eq (Prod (%s) Nat) (pair x n) (pair x n) := "
                          "fun (x : %s) (n : Nat) => refl\n"
                          "def direct : (n : Nat) -> Eq (Prod (%s) Nat) (pair %s n) (pair %s n) := "
                          "fun (n : Nat) => refl\n"
                          "def use : (n : Nat) -> Eq (Prod (%s) Nat) (pair %s n) (pair %s n) := "
                          "fun (n : Nat) => trans (wrap %s n) (direct n)\n",
                          type, type, type, type, atom, atom, type, atom, atom, atom);
    assert(length > 0 && (size_t)length < sizeof source);
    const Bindings *environment = NULL;
    Failure failure;
    int accepted = check_definitions(text(source), &environment, &failure);
    if (!accepted)
      fprintf(stderr, "closed marker case %s: %s at %llu\n", type, atom, (unsigned long long)failure.position);
    assert(accepted);
  }

  const Bindings *environment = NULL;
  Failure failure;
  const char *different =
      "def wrap : (b : Flag) -> (n : Nat) -> Eq (Prod Flag Nat) (pair b n) (pair b n) := "
      "fun (b : Flag) (n : Nat) => refl\n"
      "def direct : (n : Nat) -> Eq (Prod Flag Nat) (pair flagNo n) (pair flagNo n) := "
      "fun (n : Nat) => refl\n"
      "def use : (n : Nat) -> Eq (Prod Flag Nat) (pair flagYes n) (pair flagNo n) := "
      "fun (n : Nat) => trans (wrap flagYes n) (direct n)\n";
  assert(!check_definitions(text(different), &environment, &failure));
  assert(same_text(failure.message, eTrans));
}

static void test_val_nodes(void) {
  const char *source =
      "def PairEq : Type 0 := (n : Nat) -> (m : Nat) -> Eq (Prod Nat Nat) (pair n m) (pair n m)\n"
      "def q0 : PairEq := fun (n : Nat) (m : Nat) => refl\n"
      "def q1 : (a : Nat) -> PairEq := fun (a : Nat) (n : Nat) (m : Nat) => refl\n"
      "def q2 : (a : Nat) -> (b : Nat) -> PairEq := fun (a : Nat) (b : Nat) (n : Nat) (m : Nat) => refl\n"
      "def d0 : (n : Nat) -> (m : Nat) -> Eq (Prod Nat Nat) (pair n m) (pair n m) := fun (n : Nat) (m : Nat) => refl\n"
      "def d1 : (a : Nat) -> (n : Nat) -> (m : Nat) -> Eq (Prod Nat Nat) (pair n m) (pair n m) := "
      "fun (a : Nat) (n : Nat) (m : Nat) => refl\n"
      "def d2 : (a : Nat) -> (b : Nat) -> (n : Nat) -> (m : Nat) -> Eq (Prod Nat Nat) (pair n m) (pair n m) := "
      "fun (a : Nat) (b : Nat) (n : Nat) (m : Nat) => refl\n"
      "def dt : (n : Nat) -> (s : Text) -> Eq (Prod Nat Text) (pair n s) (pair n s) := fun (n : Nat) (s : Text) => refl\n"
      "def one : Nat := 1\n"
      "def outer : (j : Nat) -> (k : Nat) -> Nat := fun (j : Nat) (k : Nat) => k\n";
  const Bindings *environment = NULL;
  Failure failure;
  assert(check_definitions(text(source), &environment, &failure));

  /* Shift (program.c shift_node): the named signature after 0, 1 and 2
     value parameters gives the node of the side written directly after
     the same parameters. Another offset gives other markers. */
  val_row(lhs_of(environment, "q0"), lhs_of(environment, "d0"), 1, 2, 2);
  val_row(lhs_of(environment, "q1"), lhs_of(environment, "d1"), 1, 2, 2);
  val_row(lhs_of(environment, "q2"), lhs_of(environment, "d2"), 1, 2, 2);
  val_row(lhs_of(environment, "q0"), lhs_of(environment, "q1"), 0, 2, 2);
  val_row(lhs_of(environment, "q1"), lhs_of(environment, "q2"), 0, 2, 2);

  /* Rename (checker.c rename_markers): body parameters in both orders, so
     one row moves each marker to the other index; a body parameter and a
     closed name; closed numbers, a closed string and a closed name. A
     parenthesized argument in a body gives a VAL_TERM argument
     (argument_text) that keeps its body markers. */
  rename_row(environment, "d0", "k j", 1, 2);
  rename_row(environment, "d0", "j k", 1, 2);
  rename_row(environment, "d0", "k one", 1, 1);
  rename_row(environment, "dt", "3 \"a\"", 1, 0);
  rename_row(environment, "d0", "one 2", 1, 0);
  rename_row(environment, "d0", "(k) 1", 1, 1);
}

/* The values of the arguments in args for params (parse_arguments). */
static const Values *call_values(const Bindings *environment, const Params *params, const char *args) {
  const Values *values;
  Tokens rest;
  Nat left;
  Failure failure;
  assert(parse_arguments(1000, 1000, 1, param_types(params), environment, lexed(args), &values, &rest, &left, NULL,
                         &failure));
  assert(rest.size == 0);
  return values;
}

/* The checked argument terms of call_values. */
static const Terms *call_args(const Bindings *environment, const Params *params, const char *args) {
  const Values *values;
  Tokens rest;
  Nat left;
  const Terms *terms = NULL;
  Failure failure;
  assert(parse_arguments(1000, 1000, 1, param_types(params), environment, lexed(args), &values, &rest, &left, &terms,
                         &failure));
  assert(rest.size == 0);
  return terms;
}

/* The closed side of side in bound: close_body_side in a body scope, else
   close_side. */
static Val closed_in(const Bindings *bound, const LType *a, Val side) {
  Val closed;
  assert(checking_body(bound) == 1
             ? close_body_side(1000, 1000, bound, a, side, &closed, &(Nat){0}, &(Failure){0, {NULL, 0}})
             : close_side(1000, 1000, bound, a, side, &closed, &(Nat){0}, &(Failure){0, {NULL, 0}}));
  assert(closed.kind == VAL_CLOSED);
  return closed;
}

/* The closed side of the closed atom source, as eq_side makes it:
   parse_term in bound, then printed_side. */
static Val closed_atom(const Bindings *bound, const LType *a, const char *source) {
  const Value *value;
  Tokens rest;
  Nat left;
  Failure failure;
  Val closed;
  assert(parse_term(1000, 1, 1, a, bound, lexed(source), &value, &rest, &left, NULL, &failure));
  assert(printed_side(1000, value, &closed) && closed.kind == VAL_CLOSED);
  return closed;
}

/* A D4 row: the close on the node of side gives the closed side of the
   closed atom expected (closed_atom) in the same scope. */
static Val close_row(const Bindings *bound, const LType *a, Val side, const char *expected) {
  assert(side.kind == VAL_TERM && side.node != NULL);
  Val closed = closed_in(bound, a, side);
  assert(same_text(val_text(closed), val_text(closed_atom(bound, a, expected))));
  return closed;
}

/* The rows of the Eq type ty in bound. closed is the type that close_result
   or close_params gives for ty: its sides are the closed atom expected. */
static void close_type_row(const Bindings *bound, const LType *ty, const LType *closed, const char *expected) {
  const LType *a;
  const LType *b;
  Val lhs;
  Val rhs;
  Val x;
  Val y;
  assert(sides_of(ty, &a, &lhs, &rhs) && sides_of(closed, &b, &x, &y));
  assert(x.kind == VAL_CLOSED && same_text(val_text(x), val_text(close_row(bound, a, lhs, expected))));
  assert(y.kind == VAL_CLOSED && same_text(val_text(y), val_text(close_row(bound, a, rhs, expected))));
}

/* A D4c row: instantiate_side renames the markers of the left side of p to
   the closed arguments in args, in the body scope. kept_side gives 0, thus
   close_body_side closes the renamed side to the closed atom expected. */
static void body_close_row(const Bindings *environment, const Bindings *body, const char *args, const char *expected) {
  const Binding *p = fun_named(environment, "p");
  const LType *a;
  Val lhs;
  Val rhs;
  Val side;
  assert(sides_of(p->type, &a, &lhs, &rhs));
  assert(instantiate_side(1000, 1000, body, p->params, call_values(body, p->params, args),
                          call_args(body, p->params, args), lexed(args), lhs, &side, &(Nat){0},
                          &(Failure){0, {NULL, 0}}) == 1);
  assert(kept_side(side) == 0);
  close_row(body, a, side, expected);
}

/* D4 part A: a computed side in a result (D4a, close_result), in the type of
   a proof parameter (D4b, close_params) and with closed arguments in a body
   (D4c, close_body_side) closes on its node with eval_term. Called last from
   main: a marker on the node resolves by name (argument_bindings sets no
   slot), thus each close adds slot misses, and an earlier row asserts
   slot_mismatches() == 0. */
static void test_d4_close(void) {
  const char *source =
      "def p : (n : Nat) -> (m : Nat) -> Eq (Prod Nat Nat) (pair n m) (pair n m) := fun (n : Nat) (m : Nat) => refl\n"
      "def q : (n : Nat) -> (m : Nat) -> (e : Eq (Prod Nat Nat) (pair n m) (pair n m)) -> "
      "Eq (Prod Nat Nat) (pair n m) (pair n m) := fun (n : Nat) (m : Nat) (e : Eq (Prod Nat Nat) (pair n m) (pair n m)) "
      "=> symm e\n"
      "def w : (n : Nat) -> Eq (Option Nat) (some n) (some n) := fun (n : Nat) => refl\n"
      "def three : (a : Nat) -> (b : Nat) -> (c : Nat) -> Nat := fun (a : Nat) (b : Nat) (c : Nat) => c\n"
      "def one : Nat := 1\n"
      "def outer : (j : Nat) -> (k : Nat) -> Nat := fun (j : Nat) (k : Nat) => k\n";
  const Bindings *environment = NULL;
  Failure failure;
  assert(check_definitions(text(source), &environment, &failure));

  /* D4a: the results of p 2 6 and w 4. */
  const Binding *p = fun_named(environment, "p");
  const Values *p_values = call_values(environment, p->params, "2 6");
  const LType *closed;
  assert(close_result(1000, 1000, environment, p->params, p_values, 1, p->type, &closed, &(Nat){0},
                      &(Failure){0, {NULL, 0}}));
  close_type_row(argument_bindings(0, p->params, p_values, environment), p->type, closed, "(pair 2 6)");
  const Binding *w = fun_named(environment, "w");
  const Values *w_values = call_values(environment, w->params, "4");
  assert(close_result(1000, 1000, environment, w->params, w_values, 1, w->type, &closed, &(Nat){0},
                      &(Failure){0, {NULL, 0}}));
  close_type_row(argument_bindings(0, w->params, w_values, environment), w->type, closed, "(some 4)");

  /* D4b: the proof parameter e of q 2 6. The third value is a number: the
     sides of e use only the markers of n and m. */
  const Binding *q = fun_named(environment, "q");
  const Values *q_values = call_values(environment, fun_named(environment, "three")->params, "2 6 0");
  const Params *q_closed;
  assert(close_params(1000, 1000, environment, q->params, q_values, q->params, &q_closed, &(Nat){0},
                      &(Failure){0, {NULL, 0}}));
  close_type_row(argument_bindings(0, q->params, q_values, environment), q->params->tail->tail->head.type,
                 q_closed->tail->tail->head.type, "(pair 2 6)");

  /* D4c: closed numbers and the closed name one in the body of outer. */
  Bindings *body = arena_alloc(sizeof *body);
  *body = (Bindings){.head = body_marker(2),
                     .tail = bind_params(fun_named(environment, "outer")->params, NULL, environment)};
  body_close_row(environment, body, "3 4", "(pair 3 4)");
  body_close_row(environment, body, "one 2", "(pair 1 2)");

  /* The unknown answer (Q-D4-4): a side with markers in a scope with no
     marker binding. The close on the node gives 0: the side has no tokens
     to replay. */
  const LType *a;
  Val lhs;
  Val rhs;
  Val none;
  assert(sides_of(p->type, &a, &lhs, &rhs));
  assert(close_side(1000, 1000, environment, a, lhs, &none, &(Nat){0}, &(Failure){0, {NULL, 0}}) == 0);
}

/* The renamed left side of callee in body, with the arguments in args. */
static Val renamed_in(const Bindings *environment, const Bindings *body, const char *callee, const char *args) {
  const Binding *item = fun_named(environment, callee);
  Val side;
  assert(instantiate_side(1000, 1000, body, item->params, call_values(body, item->params, args),
                          call_args(body, item->params, args), lexed(args),
                          lhs_of(environment, callee), &side, &(Nat){0}, &(Failure){0, {NULL, 0}}) == 1);
  assert(side.kind == VAL_TERM && side.node != NULL);
  return side;
}

/* D4 part B: a computed side keeps only its node. The shift after 0, 1 and
   2 value parameters and the rename to body parameters, closed numbers, a
   closed string and a closed name walk the node, with no side tokens.
   Called last from main: each close on a node adds slot misses
   (test_d4_close). */
static void test_d4_carrier(void) {
  const char *source =
      "def PairEq : Type 0 := (n : Nat) -> (m : Nat) -> Eq (Prod Nat Nat) (pair n m) (pair n m)\n"
      "def q0 : PairEq := fun (n : Nat) (m : Nat) => refl\n"
      "def q1 : (a : Nat) -> PairEq := fun (a : Nat) (n : Nat) (m : Nat) => refl\n"
      "def q2 : (a : Nat) -> (b : Nat) -> PairEq := fun (a : Nat) (b : Nat) (n : Nat) (m : Nat) => refl\n"
      "def d0 : (n : Nat) -> (m : Nat) -> Eq (Prod Nat Nat) (pair n m) (pair n m) := fun (n : Nat) (m : Nat) => refl\n"
      "def d1 : (a : Nat) -> (n : Nat) -> (m : Nat) -> Eq (Prod Nat Nat) (pair n m) (pair n m) := "
      "fun (a : Nat) (n : Nat) (m : Nat) => refl\n"
      "def d2 : (a : Nat) -> (b : Nat) -> (n : Nat) -> (m : Nat) -> Eq (Prod Nat Nat) (pair n m) (pair n m) := "
      "fun (a : Nat) (b : Nat) (n : Nat) (m : Nat) => refl\n"
      "def sw : (n : Nat) -> (m : Nat) -> Eq (Prod Nat Nat) (pair m n) (pair m n) := fun (n : Nat) (m : Nat) => refl\n"
      "def dt : (n : Nat) -> (s : Text) -> Eq (Prod Nat Text) (pair n s) (pair n s) := fun (n : Nat) (s : Text) => refl\n"
      "def one : Nat := 1\n"
      "def outer : (j : Nat) -> (k : Nat) -> Nat := fun (j : Nat) (k : Nat) => k\n";
  const Bindings *environment = NULL;
  Failure failure;
  assert(check_definitions(text(source), &environment, &failure));

  /* Shift (program.c shift_node) by 0, 1 and 2: the node of the side
     written directly after the same parameters. Another offset gives other
     markers. */
  val_row(lhs_of(environment, "q0"), lhs_of(environment, "d0"), 1, 2, 2);
  val_row(lhs_of(environment, "q1"), lhs_of(environment, "d1"), 1, 2, 2);
  val_row(lhs_of(environment, "q2"), lhs_of(environment, "d2"), 1, 2, 2);
  val_row(lhs_of(environment, "q1"), lhs_of(environment, "d0"), 0, 2, 2);
  val_row(lhs_of(environment, "q2"), lhs_of(environment, "d1"), 0, 2, 2);

  /* Rename (checker.c rename_markers) in the body of outer. VAL_VAR: j k
     keeps the markers of d0, and k j gives the markers of sw. */
  Bindings *body = arena_alloc(sizeof *body);
  *body = (Bindings){.head = body_marker(2),
                     .tail = bind_params(fun_named(environment, "outer")->params, NULL, environment)};
  val_row(renamed_in(environment, body, "d0", "j k"), lhs_of(environment, "d0"), 1, 2, 2);
  val_row(renamed_in(environment, body, "d0", "k j"), lhs_of(environment, "sw"), 1, 2, 2);
  val_row(renamed_in(environment, body, "d0", "k j"), lhs_of(environment, "d0"), 0, 2, 2);

  /* A closed number, a closed string and a closed name: no marker stays,
     and the close on the node gives the closed atom. */
  const LType *a;
  const LType *t;
  Val lhs;
  Val rhs;
  assert(sides_of(fun_named(environment, "d0")->type, &a, &lhs, &rhs));
  assert(sides_of(fun_named(environment, "dt")->type, &t, &lhs, &rhs));
  Val numbers = renamed_in(environment, body, "d0", "3 4");
  Val text_side = renamed_in(environment, body, "dt", "3 \"a\"");
  Val named = renamed_in(environment, body, "d0", "one 2");
  assert(kept_side(numbers) == 0 && kept_side(text_side) == 0 && kept_side(named) == 0);
  close_row(body, a, numbers, "(pair 3 4)");
  close_row(body, t, text_side, "(pair 3 \"a\")");
  close_row(body, a, named, "(pair 1 2)");

  /* A body parameter and a closed name: one marker stays. */
  Val mixed = renamed_in(environment, body, "d0", "k one");
  assert(marker_vars_at(mixed.node) == 1 && kept_side(mixed) == 1);
}

/* The node inside each TERM_GROUP around node. */
static const Term *ungrouped(const Term *node) {
  return node->tag == TERM_GROUP ? ungrouped(node->args->head) : node;
}

/* A normal form row (D4 part C): the left side of left keeps a node with
   one marker, side_normal on it gives the same node (the make-time normal
   form, no copy), and same_type on the two types agrees with same_val on
   the two left sides (design item 6). */
static void normal_row(const Bindings *environment, const char *left, const char *right, Nat expected) {
  Val lhs = lhs_of(environment, left);
  Val rhs = lhs_of(environment, right);
  const Term *normal;
  Failure failure = {0, {NULL, 0}};
  assert(lhs.kind == VAL_TERM && marker_vars_at(lhs.node) == 1);
  assert(side_normal(1000, 1000, environment, lhs.node, &normal, &(Nat){0}, &failure) == 1 && normal == lhs.node);
  assert(same_val(lhs, rhs) == expected);
  assert(same_type(fun_named(environment, left)->type, fun_named(environment, right)->type) == expected);
}

/* Closed forms keep the expected type supplied by their constructor. */
static void test_d4_closed_forms(void) {
  const char *source =
      "def option : (n : Nat) -> Eq (Prod Nat (Option Nat)) (pair n (pure 1)) (pair n (pure 1)) := fun (n : Nat) => refl\n"
      "def list : (n : Nat) -> Eq (Prod Nat (List Text)) (pair n (pure \"s\")) (pair n (pure \"s\")) := fun (n : Nat) => refl\n"
      "def sum : (n : Nat) -> Eq (Prod Nat (Sum Text Nat)) (pair n (pure 1)) (pair n (pure 1)) := fun (n : Nat) => refl\n"
      "def nested : (n : Nat) -> Eq (Prod Nat (Option (List Nat))) (pair n (pure (pure 1))) (pair n (pure (pure 1))) := fun (n : Nat) => refl\n";
  const Bindings *environment = NULL;
  Failure failure = {0, {NULL, 0}};
  assert(check_definitions(text(source), &environment, &failure));
  normal_row(environment, "option", "option", 1);
  normal_row(environment, "list", "list", 1);
  normal_row(environment, "sum", "sum", 1);
  normal_row(environment, "nested", "nested", 1);
}

/* D4 part D (Q-D4-7 lifts 1 and 3, split row D). Lift 1: a parenthesized
   argument in a body, at a neutral position and in a side; its body
   parameters become markers and the side takes its normal form. Lift 3:
   the bare name of an earlier definition in a side. A parenthesized closed
   argument takes its normal form after the rename (pf m (one)). Q-D4-5: no
   unfold, thus (natAdd 1 m) does not prove (natAdd m 1). A parenthesized
   parameter (m) stays a group and does not prove the side m. Called last
   from main. */
static void test_d4_lifts(void) {
  const char *head =
      "def one : Nat := 1\n"
      "def identity : (n : Nat) -> Nat := fun (n : Nat) => n\n"
      "def polyProof : (A : Type 0) -> (n : A) -> Eq A n n := fun (A : Type 0) (n : A) => refl\n"
      "def polyLast : (A : Type 0) -> (B : Type 0) -> (n : A) -> (j : B) -> Eq B j j := "
      "fun (A : Type 0) (B : Type 0) (n : A) (j : B) => refl\n"
      "def polyUse : (A : Type 0) -> (n : A) -> (p : Eq A n n) -> Eq A n n := "
      "fun (A : Type 0) (n : A) (p : Eq A n n) => p\n"
      "def natAdd : (a : Nat) -> (b : Nat) -> Nat := fun (a : Nat) (b : Nat) => a\n"
      "def e : (n : Nat) -> Eq Nat n n := fun (n : Nat) => refl\n"
      "def pf : (n : Nat) -> (j : Nat) -> Eq (Prod Nat Nat) (pair n j) (pair n j) := fun (n : Nat) (j : Nat) => refl\n"
      "def po : (n : Nat) -> (o : Option Nat) -> Eq (Prod Nat (Option Nat)) (pair n o) (pair n o) := "
      "fun (n : Nat) (o : Option Nat) => refl\n";
  const char *accepted[] = {
      "def g : (m : Nat) -> Eq Nat (natAdd m 1) (natAdd m 1) := fun (m : Nat) => e (natAdd m 1)\n",
      "def g : (m : Nat) -> Eq Nat (natAdd m 1) (natAdd m 1) := fun (m : Nat) => e (natAdd m one)\n",
      "def g : (m : Nat) -> Eq (Prod Nat (Option Nat)) (pair m (some m)) (pair m (some m)) := "
      "fun (m : Nat) => po m (some m)\n",
      "def p1 : (n : Nat) -> Eq (Prod Nat Nat) (pair n one) (pair n one) := fun (n : Nat) => refl\n"
      "def u : (m : Nat) -> Eq (Prod Nat Nat) (pair m 1) (pair m 1) := fun (m : Nat) => p1 m\n"
      "def w : Eq (Prod Nat Nat) (pair 3 1) (pair 3 1) := p1 3\n",
      "def q : (n : Nat) -> Eq Nat (natAdd n one) (natAdd n 1) := fun (n : Nat) => refl\n",
      "def g : (m : Nat) -> Eq (Prod Nat Nat) (pair m 1) (pair m 1) := fun (m : Nat) => pf m (one)\n",
      "def g : (m : Nat) -> Eq Nat (identity m) (identity m) := fun (m : Nat) => polyProof Nat (identity m)\n",
      "def g : (m : Nat) -> Eq Nat 1 1 := fun (m : Nat) => polyProof Nat (one)\n"
      "def resultProof : Eq Nat 1 1 := g 3\n",
      "def g : (m : Nat) -> Eq (Option Nat) (some m) (some m) := fun (m : Nat) => polyProof (Option Nat) (some m)\n"
      "def resultProof : Eq (Option Nat) (some 3) (some 3) := g 3\n",
      "def g : (m : Nat) -> Eq (Option Nat) (some m) (some m) := "
      "fun (m : Nat) => polyLast Text (Option Nat) (\"a\") (some m)\n"
      "def resultProof : Eq (Option Nat) (some 3) (some 3) := g 3\n",
      "def g : (m : Nat) -> Eq Nat (identity m) (identity m) := fun (m : Nat) => polyUse Nat (identity m) refl\n",
      "def g : (m : Nat) -> Eq (Option Nat) (some m) (some m) := "
      "fun (m : Nat) => polyUse (Option Nat) (some m) refl\n"
      "def resultProof : Eq (Option Nat) (some 3) (some 3) := g 3\n",
      "def g : (m : Nat) -> Eq (Prod Nat Nat) (pair m 1) (pair m 1) := fun (m : Nat) => pf (m) 1\n"};
  for (size_t at = 0; at < sizeof accepted / sizeof *accepted; at++) {
    char source[2048];
    int length = snprintf(source, sizeof source, "%s%s", head, accepted[at]);
    assert(length > 0 && (size_t)length < sizeof source);
    const Bindings *environment = NULL;
    Failure failure = {0, {NULL, 0}};
    int ok = check_definitions(text(source), &environment, &failure);
    if (!ok)
      fprintf(stderr, "lift row %llu: failure at %llu\n", (unsigned long long)at, (unsigned long long)failure.position);
    assert(ok);
  }

  struct {
    const char *source;
    const Text *message;
  } refused[] = {
      {"def g : (m : Nat) -> Eq Nat (natAdd m 1) (natAdd m 1) := fun (m : Nat) => e (natAdd 1 m)\n", &eTerm},
      {"def bad : (n : Nat) -> Eq Nat (natAdd 1 n) (natAdd n 1) := fun (n : Nat) => refl\n", &eRefl},
      {"def g : (m : Nat) -> Eq Nat (identity m) (identity m) := fun (m : Nat) => polyProof Text (identity m)\n", &eTerm},
      {"def g : (m : Nat) -> Eq Nat (identity m) (identity m) := fun (m : Nat) => polyUse Nat (identity m) (e 1)\n", &eTerm}};
  for (size_t at = 0; at < sizeof refused / sizeof *refused; at++) {
    char source[2048];
    int length = snprintf(source, sizeof source, "%s%s", head, refused[at].source);
    assert(length > 0 && (size_t)length < sizeof source);
    const Bindings *environment = NULL;
    Failure failure = {0, {NULL, 0}};
    assert(!check_definitions(text(source), &environment, &failure));
    assert(same_text(failure.message, *refused[at].message));
  }
}

/* Option payloads share Value kinds with scalars, but need Option terms. */
static void test_d4_option_literals(void) {
  const char *source =
      "def number : Option Nat := some 1\n"
      "def text : Option Text := some \"s\"\n"
      "def fn : (n : Nat) -> Eq (Prod Nat (Option Nat)) (pair n (number)) (pair n (number)) := fun (n : Nat) => refl\n"
      "def ft : (n : Nat) -> Eq (Prod Nat (Option Text)) (pair n (text)) (pair n (text)) := fun (n : Nat) => refl\n"
      "def pn : Eq (Prod Nat (Option Nat)) (pair 3 (some 1)) (pair 3 (some 1)) := fn 3\n"
      "def pt : Eq (Prod Nat (Option Text)) (pair 3 (some \"s\")) (pair 3 (some \"s\")) := ft 3\n";
  const Bindings *environment = NULL;
  Failure failure = {0, {NULL, 0}};
  assert(check_definitions(text(source), &environment, &failure));
  const char *bad =
      "def number : Option Nat := some 1\n"
      "def f : (n : Nat) -> Eq (Prod Nat (Option Nat)) (pair n (number)) (pair n (number)) := fun (n : Nat) => refl\n"
      "def p : Eq (Prod Nat (Option Nat)) (pair 3 (some 2)) (pair 3 (some 2)) := f 3\n";
  assert(!check_definitions(text(bad), &environment, &failure));
  assert(failure.position == (Nat)(strstr(bad, "f 3") - bad) && same_text(failure.message, eTerm));
}

/* D4 part C: side_normal (design item 5). A constructor, a nested
   constructor and a neutral application of an earlier definition keep
   their node (Q-D4-5: no unfold, thus some (inc n) is not some n). A closed
   name after the rename gives its literal. A fun with a marker is refused
   at the position of the fun. Called from main after test_d4_close;
   test_d4_lifts (D4 part D) comes after it. */
static void test_d4_normal(void) {
  const char *source =
      "def inc : (n : Nat) -> Nat := fun (n : Nat) => n\n"
      "def dec : (n : Nat) -> Nat := fun (n : Nat) => n\n"
      "def c1 : (n : Nat) -> Eq (Option Nat) (some n) (some n) := fun (n : Nat) => refl\n"
      "def c2 : (n : Nat) -> Eq (Option Nat) (some n) (some n) := fun (n : Nat) => refl\n"
      "def s1 : (n : Nat) -> Eq (Option (Option Nat)) (some (some n)) (some (some n)) := fun (n : Nat) => refl\n"
      "def s2 : (n : Nat) -> Eq (Option (Option Nat)) (some (some n)) (some (some n)) := fun (n : Nat) => refl\n"
      "def a1 : (n : Nat) -> Eq (Option Nat) (some (inc n)) (some (inc n)) := fun (n : Nat) => refl\n"
      "def a2 : (n : Nat) -> Eq (Option Nat) (some (inc n)) (some (inc n)) := fun (n : Nat) => refl\n"
      "def a3 : (n : Nat) -> Eq (Option Nat) (some (dec n)) (some (dec n)) := fun (n : Nat) => refl\n"
      "def pf : (n : Nat) -> (m : Nat) -> Eq (Prod Nat Nat) (pair n m) (pair n m) := fun (n : Nat) (m : Nat) => refl\n"
      "def k1 : (j : Nat) -> (k : Nat) -> Eq (Prod Nat Nat) (pair k 1) (pair k 1) := fun (j : Nat) (k : Nat) => refl\n"
      "def one : Nat := 1\n"
      "def outer : (j : Nat) -> (k : Nat) -> Nat := fun (j : Nat) (k : Nat) => k\n";
  const Bindings *environment = NULL;
  Failure failure;
  assert(check_definitions(text(source), &environment, &failure));

  /* A constructor, a nested constructor and a neutral application. */
  normal_row(environment, "c1", "c2", 1);
  normal_row(environment, "s1", "s2", 1);
  normal_row(environment, "a1", "a2", 1);
  normal_row(environment, "c1", "a1", 0);
  normal_row(environment, "a1", "a3", 0);
  normal_row(environment, "s1", "c1", 0);

  /* A closed name after the rename in the body of outer: pf k one gives
     the literal 1 (R-C1), and the side is the left side of k1. */
  Bindings *body = arena_alloc(sizeof *body);
  *body = (Bindings){.head = body_marker(2),
                     .tail = bind_params(fun_named(environment, "outer")->params, NULL, environment)};
  Val closed = renamed_in(environment, body, "pf", "k one");
  assert(ungrouped(closed.node)->args->tail->head->tag == TERM_NUMBER);
  val_row(closed, lhs_of(environment, "k1"), 1, 1, 1);

  /* A fun with a marker in a constructor. mark_side refuses fun, thus the
     node is built by hand. */
  const Term *some = ungrouped(lhs_of(environment, "c1").node);
  const Term *marker = some->args->head;
  assert(marker->tag == TERM_VAR);
  const Term *fun = term_form(TERM_FUN, 9, 1, one(marker));
  const Term *normal;
  Failure refused = {0, {NULL, 0}};
  assert(side_normal(1000, 1000, environment, as_construct(some, one(fun)), &normal, &(Nat){0}, &refused) == 0);
  assert(refused.position == 9 && same_text(refused.message, eTerm));
}

/* The type of source, parsed with no environment and no parameters. */
static const LType *sigma_parsed(const char *source) {
  const LType *type;
  Tokens rest;
  Failure failure = {0, {NULL, 0}};
  Nat left;
  assert(parse_type(1000, 1000, 0, NULL, lexed(source), &type, &rest, &left, &failure) && rest.size == 0);
  return type;
}

/* check_definitions refuses source at the first byte of at, with message. */
static void sigma_refused(const char *source, const char *at, Text message) {
  const Bindings *environment = NULL;
  Failure failure = {0, {NULL, 0}};
  assert(!check_definitions(text(source), &environment, &failure));
  assert(failure.position == (Nat)(strstr(source, at) - source) && same_text(failure.message, message));
}

/* D5 part A: the Sigma type (design items 1 to 4 and 9). The parse of both
   forms, the marker level of the binder, type_name, same_type and the
   refusals. A body that is not pack is refused for a Sigma type (ruling
   R-A1; part B adds pack, see test_d5_pack). Called from main after
   test_d4_lifts. */
static void test_d5_type(void) {
  /* Both forms. The short form has no binder name. */
  const LType *binder = sigma_parsed("Sigma (x : Nat) Text");
  assert(binder->tag == TY_SIGMA && same_text(binder->name, text("x")) && binder->level == 0);
  assert(binder->left->tag == TY_NAT && binder->right->tag == TY_TEXT);
  const LType *short_form = sigma_parsed("Sigma Nat Text");
  assert(short_form->tag == TY_SIGMA && short_form->name.size == 0 && short_form->level == 0);
  assert(short_form->left->tag == TY_NAT && short_form->right->tag == TY_TEXT);

  /* The marker level of the binder: 0 at the top, 1 in a nested Sigma and
     3 after 3 parameters. An Eq side that names the binder has its marker. */
  const LType *nested = sigma_parsed("Sigma (x : Nat) (Sigma (y : Nat) (Eq Nat x y))");
  assert(nested->level == 0 && nested->right->tag == TY_SIGMA && nested->right->level == 1);
  const LType *inner = nested->right->right;
  assert(inner->tag == TY_EQ && inner->lhs.kind == VAL_VAR && inner->lhs.index == 0);
  assert(inner->rhs.kind == VAL_VAR && inner->rhs.index == 1);
  const char *source =
      "def g : (a : Nat) -> (b : Nat) -> (c : Nat) -> (s : Sigma (x : Nat) (Eq Nat x c)) -> Nat := "
      "fun (a : Nat) (b : Nat) (c : Nat) (s : Sigma (x : Nat) (Eq Nat x c)) => a\n"
      "def f1 : (n : Nat) -> (s : Sigma (x : Nat) (Eq Nat x x)) -> Nat := "
      "fun (n : Nat) (s : Sigma (x : Nat) (Eq Nat x x)) => n\n"
      "def f2 : (m : Nat) -> (t : Sigma (z : Nat) (Eq Nat z z)) -> Nat := "
      "fun (m : Nat) (t : Sigma (z : Nat) (Eq Nat z z)) => m\n"
      "def f3 : (n : Nat) -> (s : Sigma (x : Nat) (Eq Nat x n)) -> Nat := "
      "fun (n : Nat) (s : Sigma (x : Nat) (Eq Nat x n)) => n\n";
  const Bindings *environment = NULL;
  Failure failure = {0, {NULL, 0}};
  assert(check_definitions(text(source), &environment, &failure));
  const LType *fourth = fun_named(environment, "g")->params->tail->tail->tail->head.type;
  assert(fourth->tag == TY_SIGMA && fourth->level == 3 && fourth->right->tag == TY_EQ);
  assert(fourth->right->lhs.index == 3 && fourth->right->rhs.index == 2);

  /* type_name: the source binder name, and `Sigma (A) (B)` for the short
     form. */
  assert(same_text(type_name(binder), text("Sigma (x : Nat) (Text)")));
  assert(same_text(type_name(short_form), text("Sigma (Nat) (Text)")));
  assert(same_text(type_name(sigma_parsed("Sigma (p : Prod Nat Nat) (Sigma Text Nat)")),
                   text("Sigma (p : Prod (Nat) (Nat)) (Sigma (Text) (Nat))")));

  /* same_type: binder and parameter names do not count; A, B and the marker
     of a side count. */
  const LType *s1 = fun_named(environment, "f1")->params->tail->head.type;
  const LType *s2 = fun_named(environment, "f2")->params->tail->head.type;
  const LType *s3 = fun_named(environment, "f3")->params->tail->head.type;
  assert(same_type(s1, s2) == 1 && same_type(s1, s3) == 0);
  assert(same_type(binder, sigma_parsed("Sigma (y : Nat) Text")) == 1 && same_type(binder, short_form) == 1);
  assert(same_type(binder, sigma_parsed("Sigma (x : Text) Text")) == 0);
  assert(same_type(binder, sigma_parsed("Sigma (x : Nat) Nat")) == 0);

  /* Refusals: Type 0 as A, a function type as A, fun in B, and the body of
     a Sigma definition. */
  sigma_refused("def a : Sigma (x : Type 0) Nat := 1\n", "(x", eType);
  sigma_refused("def One : Type 0 := (n : Nat) -> Nat\ndef a : Sigma (x : One) Nat := 1\n", "One) Nat", eData);
  sigma_refused("def a : Sigma Nat (fun x => Nat) := 1\n", "fun", eType);
  sigma_refused("def a : Sigma Nat Nat := 1\n", "1\n", eTerm);
}

/* Sigma aliases and bound variables retain their meaning in a new scope.
   Calls substitute free signature variables without capturing local binders. */
static void test_d5_scope(void) {
  const char *source =
      "def Plain : Type 0 := Sigma Nat Nat\n"
      "def Proof : Type 0 := Sigma (x : Nat) (Eq Nat x x)\n"
      "def alias : (n : Nat) -> (s : Plain) -> Nat := fun (n : Nat) (s : Sigma Nat Nat) => n\n"
      "def proofAlias : (n : Nat) -> (s : Proof) -> Nat := "
      "fun (n : Nat) (s : Sigma (y : Nat) (Eq Nat y y)) => n\n"
      "def nestedAlias : (s : Sigma Nat Proof) -> Nat := "
      "fun (s : Sigma Nat (Sigma (y : Nat) (Eq Nat y y))) => 0\n"
      "def take : (s : Proof) -> Nat := fun (s : Proof) => 0\n"
      "def pass : (n : Nat) -> (s : Proof) -> Nat := fun (n : Nat) (s : Proof) => take s\n"
      "def returnSigma : (s : Sigma Nat Nat) -> Sigma Nat Nat := fun (s : Sigma Nat Nat) => s\n"
      "def polymorphic : (A : Type 0) -> (s : Sigma (x : A) (Eq A x x)) -> Nat := "
      "fun (B : Type 0) (s : Sigma (y : B) (Eq B y y)) => 0\n"
      "def Signature : Type 0 := (s : Proof) -> Nat\n"
      "def prefixed : (n : Nat) -> Signature := fun (n : Nat) (s : Proof) => n\n"
      "def dependent : (n : Nat) -> (s : Sigma (x : Nat) (Eq Nat x n)) -> Nat := "
      "fun (n : Nat) (s : Sigma (x : Nat) (Eq Nat x n)) => n\n"
      "def moved : (unused : Nat) -> (m : Nat) -> (s : Sigma (x : Nat) (Eq Nat x m)) -> Nat := "
      "fun (unused : Nat) (m : Nat) (s : Sigma (y : Nat) (Eq Nat y m)) => dependent m s\n"
      "def computed : (n : Nat) -> (s : Sigma (x : Nat) (Eq (Option Nat) (some x) (some n))) -> Nat := "
      "fun (n : Nat) (s : Sigma (x : Nat) (Eq (Option Nat) (some x) (some n))) => n\n"
      "def movedComputed : (unused : Nat) -> (m : Nat) -> "
      "(s : Sigma (x : Nat) (Eq (Option Nat) (some x) (some m))) -> Nat := "
      "fun (unused : Nat) (m : Nat) (s : Sigma (y : Nat) (Eq (Option Nat) (some y) (some m))) => computed m s\n"
      "def wrapped : (n : Nat) -> (s : Option (Sigma (x : Nat) (Eq Nat x n))) -> Nat := "
      "fun (n : Nat) (s : Option (Sigma (x : Nat) (Eq Nat x n))) => n\n"
      "def movedWrapped : (unused : Nat) -> (m : Nat) -> (s : Option (Sigma (x : Nat) (Eq Nat x m))) -> Nat := "
      "fun (unused : Nat) (m : Nat) (s : Option (Sigma (y : Nat) (Eq Nat y m))) => wrapped m s\n"
      "def generic : (A : Type 0) -> (s : A) -> Nat := fun (A : Type 0) (s : A) => 0\n"
      "def typeArgument : (n : Nat) -> (s : Sigma (x : Nat) (Eq Nat x n)) -> Nat := "
      "fun (n : Nat) (s : Sigma (x : Nat) (Eq Nat x n)) => generic (Sigma (y : Nat) (Eq Nat y n)) s\n"
      "def wrappedTypeArgument : (n : Nat) -> (s : Option (Sigma (x : Nat) (Eq Nat x n))) -> Nat := "
      "fun (n : Nat) (s : Option (Sigma (x : Nat) (Eq Nat x n))) => "
      "generic (Option (Sigma (y : Nat) (Eq Nat y n))) s\n"
      "def closedComputed : (n : Nat) -> (s : Sigma Nat (Eq (Option Nat) (some n) (some 1))) -> Nat := "
      "fun (n : Nat) (s : Sigma Nat (Eq (Option Nat) (some n) (some 1))) => n\n"
      "def closeArgument : (s : Sigma Nat (Eq (Option Nat) (some 1) (some 1))) -> Nat := "
      "fun (s : Sigma Nat (Eq (Option Nat) (some 1) (some 1))) => closedComputed 1 s\n";
  const Bindings *environment = NULL;
  Failure failure = {0, {NULL, 0}};
  assert(check_definitions(text(source), &environment, &failure));
  const LType *alias = fun_named(environment, "proofAlias")->params->tail->head.type;
  assert(alias->level == 1 && alias->right->lhs.index == 1 && alias->right->rhs.index == 1);
  const LType *nested = fun_named(environment, "nestedAlias")->params->head.type->right;
  assert(nested->level == 1 && nested->right->lhs.index == 1 && nested->right->rhs.index == 1);
  assert(same_type(alias, fun_named(environment, "take")->params->head.type));
  assert(same_type(sigma_parsed("Sigma (x : Nat) (Sigma (y : Nat) (Eq Nat x y))"),
                   sigma_parsed("Sigma (a : Nat) (Sigma (b : Nat) (Eq Nat b a))")) == 0);

  /* The original call accepted a proof relative to m as a proof relative
     to 1. The final argument must be refused. */
  sigma_refused(
      "def f : (n : Nat) -> (s : Sigma (x : Nat) (Eq Nat x n)) -> Nat := "
      "fun (n : Nat) (s : Sigma (x : Nat) (Eq Nat x n)) => n\n"
      "def g : (m : Nat) -> (s : Sigma (x : Nat) (Eq Nat x m)) -> Nat := "
      "fun (m : Nat) (s : Sigma (x : Nat) (Eq Nat x m)) => f 1 s\n", "s\n", eTerm);
  /* m has the callee's local binder marker before substitution. It must
     remain free, distinct from the Sigma binder. */
  sigma_refused(
      "def f : (n : Nat) -> (s : Sigma (x : Nat) (Eq Nat x n)) -> Nat := "
      "fun (n : Nat) (s : Sigma (x : Nat) (Eq Nat x n)) => n\n"
      "def g : (unused : Nat) -> (m : Nat) -> (s : Sigma (x : Nat) (Eq Nat x x)) -> Nat := "
      "fun (unused : Nat) (m : Nat) (s : Sigma (x : Nat) (Eq Nat x x)) => f m s\n", "s\n", eTerm);
  sigma_refused(
      "def f : (n : Nat) -> (s : Sigma (x : Nat) (Eq (Option Nat) (some x) (some n))) -> Nat := "
      "fun (n : Nat) (s : Sigma (x : Nat) (Eq (Option Nat) (some x) (some n))) => n\n"
      "def g : (m : Nat) -> (s : Sigma (x : Nat) (Eq (Option Nat) (some x) (some m))) -> Nat := "
      "fun (m : Nat) (s : Sigma (x : Nat) (Eq (Option Nat) (some x) (some m))) => f 1 s\n", "s\n", eTerm);
  sigma_refused(
      "def generic : (A : Type 0) -> (s : A) -> Nat := fun (A : Type 0) (s : A) => 0\n"
      "def g : (n : Nat) -> (s : Sigma (x : Nat) (Eq Nat x n)) -> Nat := "
      "fun (n : Nat) (s : Sigma (x : Nat) (Eq Nat x n)) => generic (Sigma (y : Nat) (Eq Nat y 1)) s\n",
      "s\n", eTerm);
}

static const Binding *value_named(const Bindings *environment, const char *name) {
  for (; environment != NULL; environment = environment->tail)
    if (environment->head.kind == BIND_VALUE && same_text(environment->head.name, text(name))) return &environment->head;
  return NULL;
}

/* D5 part B: pack against an expected Sigma type, witness and payload on a
   closed value, the JSON keys witness and payload, and the failure
   "expected a Sigma type" (design items 5 to 7). Called from main after
   test_d5_type. */
static void test_d5_pack(void) {
  const char *source =
      "def s : Sigma (x : Nat) (Eq Nat x x) := pack 1 refl\n"
      "def one : Sigma (x : Nat) (Eq Nat x 1) := pack 1 refl\n"
      "def t : Sigma Nat Text := pack 1 \"a\"\n"
      "def w : Nat := witness s\n"
      "def p : Eq Nat 1 1 := payload s\n"
      "def wt : Nat := witness t\n"
      "def pt : Text := payload t\n"
      "def u : Sigma (x : Nat) (Sigma (y : Nat) (Eq Nat x y)) := pack 1 (pack 1 refl)\n"
      "def q : Sigma (y : Nat) (Eq Nat 1 y) := payload u\n";
  const Bindings *environment = NULL;
  Failure failure = {0, {NULL, 0}};
  assert(check_definitions(text(source), &environment, &failure));

  /* pack checks a, puts the value of a for x in B and checks b: `one` checks
     refl against Eq Nat 1 1. The type text puts each argument in
     parentheses and names a bound marker by its binder. An Eq payload
     writes null. */
  const Binding *s = value_named(environment, "s");
  assert(same_text(type_name(s->type), text("Sigma (x : Nat) (Eq (Nat) (x) (x))")));
  assert(same_text(printed(s->value), text("{\"witness\":1,\"payload\":null}")));
  assert(same_text(printed(value_named(environment, "one")->value), text("{\"witness\":1,\"payload\":null}")));
  const Binding *t = value_named(environment, "t");
  assert(same_text(type_name(t->type), text("Sigma (Nat) (Text)")));
  assert(same_text(printed(t->value), text("{\"witness\":1,\"payload\":\"a\"}")));

  /* Projections on closed values: witness gives projection 1 with type A,
     payload gives projection 2 with B where x is the witness. A nested Sigma
     keeps its own binder. */
  assert(same_text(printed(value_named(environment, "w")->value), text("1")));
  assert(same_text(printed(value_named(environment, "wt")->value), text("1")));
  assert(same_text(printed(value_named(environment, "pt")->value), text("\"a\"")));
  const Binding *u = value_named(environment, "u");
  assert(same_text(type_name(u->type), text("Sigma (x : Nat) (Sigma (y : Nat) (Eq (Nat) (x) (y)))")));
  assert(same_text(printed(u->value), text("{\"witness\":1,\"payload\":{\"witness\":1,\"payload\":null}}")));
  assert(same_text(printed(value_named(environment, "q")->value), text("{\"witness\":1,\"payload\":null}")));

  /* Refusals. pack with no expected Sigma type and witness of a value that is
     not a Sigma give the new failure; a literal argument does not synthesize
     a type (as `first 1`). */
  sigma_refused("def r : Nat := witness (pack 1 refl)\n", "pack", eSigma);
  sigma_refused("def r : Nat := pack 1 refl\n", "pack", eSigma);
  sigma_refused("def n : Nat := 1\ndef r : Nat := witness n\n", "witness n", eSigma);
  sigma_refused("def r : Nat := witness 1\n", "1\n", eInfer);
  sigma_refused("def r : Sigma (x : Nat) (Eq Nat x 2) := pack 1 refl\n", "refl", text("refl needs two equal sides"));
  sigma_refused("def u : Sigma (x : Nat) (Sigma (y : Nat) (Eq Nat x y)) := pack 1 (pack 2 refl)\n", "refl",
                text("refl needs two equal sides"));
  sigma_refused("def s : Sigma (x : Nat) (Eq Nat x x) := pack 1 refl\ndef p : Eq Nat 2 2 := payload s\n", "payload s",
                eTerm);
  sigma_refused("def t : Sigma Nat Text := pack 1 \"a\"\ndef wt : Text := witness t\n", "witness t", eTerm);
}

/* D5 part C: projections on neutral Sigma values (design item 8). pack in a
   body, witness and payload of a parameter, refl against a declared side
   `witness s`, and pack of the projections of a parameter. A neutral value
   does not prove a false Eq: the refusals are at the body, not at the
   declared type. Called from main after test_d5_pack. */
static void test_d5_neutral(void) {
  const char *source =
      "def f : (n : Nat) -> Sigma (x : Nat) (Eq Nat x x) := fun (n : Nat) => pack n refl\n"
      "def g : (s : Sigma Nat Text) -> Nat := fun (s : Sigma Nat Text) => witness s\n"
      "def a : (s : Sigma (x : Nat) (Eq Nat x x)) -> Eq Nat (witness s) (witness s) :=\n"
      "  fun (s : Sigma (x : Nat) (Eq Nat x x)) => refl\n"
      "def b : (s : Sigma (x : Nat) (Eq Nat x x)) -> Eq Nat (witness s) (witness s) :=\n"
      "  fun (s : Sigma (x : Nat) (Eq Nat x x)) => payload s\n"
      "def e : (n : Nat) -> Sigma (x : Nat) (Eq Nat x n) := fun (n : Nat) => pack n refl\n"
      "def r : (s : Sigma (x : Nat) (Eq Nat x x)) -> Sigma (x : Nat) (Eq Nat x x) :=\n"
      "  fun (s : Sigma (x : Nat) (Eq Nat x x)) => pack (witness s) (payload s)\n"
      "def h : (n : Nat) -> (s : Sigma (x : Nat) (Eq Nat x n)) -> Eq Nat (witness s) n :=\n"
      "  fun (n : Nat) (s : Sigma (x : Nat) (Eq Nat x n)) => payload s\n";
  const Bindings *environment = NULL;
  Failure failure = {0, {NULL, 0}};
  assert(check_definitions(text(source), &environment, &failure));

  /* A side of B with the marker in an application: the witness node of a
     body parameter (pack n refl) and of `witness s` (payload s). */
  const char *applied_pack =
      "def id : (n : Nat) -> Nat := fun (n : Nat) => n\n"
      "def k : (n : Nat) -> Sigma (x : Nat) (Eq Nat (id x) (id x)) := fun (n : Nat) => pack n refl\n";
  const char *applied_payload =
      "def id : (n : Nat) -> Nat := fun (n : Nat) => n\n"
      "def q : (s : Sigma (x : Nat) (Eq Nat (id x) (id x))) -> Eq Nat (id (witness s)) (id (witness s)) :=\n"
      "  fun (s : Sigma (x : Nat) (Eq Nat (id x) (id x))) => payload s\n";
  const Bindings *pack_environment = NULL;
  assert(check_definitions(text(applied_pack), &pack_environment, &failure));
  const Bindings *payload_environment = NULL;
  assert(check_definitions(text(applied_payload), &payload_environment, &failure));

  /* Two parameters s and t: `witness s` and `witness t` are different
     sides. pack m refl puts m for x, thus refl needs Eq Nat m n. */
  sigma_refused("def f : (s : Sigma (x : Nat) (Eq Nat x x)) -> (t : Sigma (x : Nat) (Eq Nat x x)) ->\n"
                "  Eq Nat (witness s) (witness t) :=\n"
                "  fun (s : Sigma (x : Nat) (Eq Nat x x)) (t : Sigma (x : Nat) (Eq Nat x x)) => refl\n",
                "refl\n", text("refl needs two equal sides"));
  sigma_refused("def f : (s : Sigma (x : Nat) (Eq Nat x x)) -> (t : Sigma (x : Nat) (Eq Nat x x)) ->\n"
                "  Eq Nat (witness s) (witness t) :=\n"
                "  fun (s : Sigma (x : Nat) (Eq Nat x x)) (t : Sigma (x : Nat) (Eq Nat x x)) => payload s\n",
                "payload s", eTerm);
  sigma_refused("def f : (m : Nat) -> (n : Nat) -> Sigma (x : Nat) (Eq Nat x n) := fun (m : Nat) (n : Nat) => pack m refl\n",
                "refl\n", text("refl needs two equal sides"));
  sigma_refused("def f : (s : Sigma (x : Nat) (Eq Nat x x)) -> (t : Sigma (x : Nat) (Eq Nat x x)) ->\n"
                "  Sigma (x : Nat) (Eq Nat x x) :=\n"
                "  fun (s : Sigma (x : Nat) (Eq Nat x x)) (t : Sigma (x : Nat) (Eq Nat x x)) =>\n"
                "  pack (witness s) (payload t)\n",
                "payload t", eTerm);
}

/* Nested neutral payloads remain nodes in computed equality sides. */
static void test_d5_nested_neutral(void) {
  const char *source =
      "def payloadProof : (s : Sigma Nat Nat) -> Eq Nat (payload s) (payload s) :=\n"
      "  fun (s : Sigma Nat Nat) => refl\n"
      "def S : Type 0 := Sigma Nat (Sigma (x : Nat) (Eq Nat x x))\n"
      "def extract : (s : S) -> Eq Nat (witness (payload s)) (witness (payload s)) :=\n"
      "  fun (s : S) => payload (payload s)\n"
      "def copy : (s : S) -> Sigma (x : Nat) (Eq Nat x x) :=\n"
      "  fun (s : S) => pack (witness (payload s)) (payload (payload s))\n"
      "def linked : (s : Sigma (x : Nat) (Sigma (y : Nat) (Eq Nat x y))) ->\n"
      "  Eq Nat (witness s) (witness (payload s)) :=\n"
      "  fun (s : Sigma (x : Nat) (Sigma (y : Nat) (Eq Nat x y))) => payload (payload s)\n"
      "def s : S := pack 0 (pack 7 refl)\n"
      "def p : Eq Nat 7 7 := extract s\n"
      "def t : Sigma (x : Nat) (Eq Nat x x) := copy s\n"
      "def u : Sigma (x : Nat) (Sigma (y : Nat) (Eq Nat x y)) := pack 9 (pack 9 refl)\n"
      "def q : Eq Nat 9 9 := linked u\n"
      "def v : Sigma Nat Nat := pack 1 2\n"
      "def vp : Eq Nat 2 2 := payloadProof v\n";
  const Bindings *environment = NULL;
  Failure failure = {0, {NULL, 0}};
  assert(check_definitions(text(source), &environment, &failure));
  assert(same_text(printed(value_named(environment, "t")->value), text("{\"witness\":7,\"payload\":null}")));
  assert(same_text(printed(value_named(environment, "p")->value), text("null")));
  assert(same_text(printed(value_named(environment, "q")->value), text("null")));
  assert(same_text(printed(value_named(environment, "vp")->value), text("null")));

  const char *distinct =
      "def f : (s : Sigma Nat (Sigma (x : Nat) (Eq Nat x x))) ->\n"
      "  (t : Sigma Nat (Sigma (x : Nat) (Eq Nat x x))) ->\n"
      "  Eq Nat (witness (payload s)) (witness (payload t)) :=\n"
      "  fun (s : Sigma Nat (Sigma (x : Nat) (Eq Nat x x)))\n"
      "      (t : Sigma Nat (Sigma (x : Nat) (Eq Nat x x))) => ";
  char refused[1024];
  int length = snprintf(refused, sizeof refused, "%srefl\n", distinct);
  assert(length > 0 && (size_t)length < sizeof refused);
  sigma_refused(refused, "refl\n", text("refl needs two equal sides"));
  length = snprintf(refused, sizeof refused, "%spayload (payload s)\n", distinct);
  assert(length > 0 && (size_t)length < sizeof refused);
  sigma_refused(refused, "payload (payload s)\n", eTerm);
}

static void test_d5_witness_types(void) {
  const char *source =
      "def o : Sigma (x : Option Nat) (Eq (Option Nat) x x) := pack (some 1) refl\n"
      "def op : Eq (Option Nat) (some 1) (some 1) := payload o\n"
      "def f : Sigma (x : Flag) (Eq Flag x flagYes) := pack flagYes refl\n"
      "def fp : Eq Flag flagYes flagYes := payload f\n"
      "def l : Sigma (x : List Nat) (Eq (List Nat) x (cons 1 nil)) := pack (cons 1 nil) refl\n"
      "def lp : Eq (List Nat) (cons 1 nil) (cons 1 nil) := payload l\n"
      "def c : Sigma (x : Option Nat) (Eq (Prod (Option Nat) Nat) (pair x 2) (pair (some 1) 2)) := pack (some 1) refl\n"
      "def cp : Eq (Prod (Option Nat) Nat) (pair (some 1) 2) (pair (some 1) 2) := payload c\n"
      "def n : Sigma (x : List Nat) (Sigma (y : Nat) (Eq (Prod (List Nat) Nat) (pair x y) (pair x y))) := pack (cons 1 nil) (pack 2 refl)\n"
      "def q : Sigma (y : Nat) (Eq (Prod (List Nat) Nat) (pair (cons 1 nil) y) (pair (cons 1 nil) y)) := payload n\n"
      "def np : Eq (Prod (List Nat) Nat) (pair (cons 1 nil) 2) (pair (cons 1 nil) 2) := payload (payload n)\n"
      "def proof : Eq Nat 1 1 := refl\n"
      "def use : (n : Nat) -> (e : Eq Nat n n) -> (m : Nat) -> Nat := fun (n : Nat) (e : Eq Nat n n) (m : Nat) => m\n"
      "def dependent : (x : Nat) -> Eq Nat (use 1 proof x) (use 1 proof x) := fun (x : Nat) => refl\n";
  const Bindings *environment = NULL;
  Failure failure = {0, {NULL, 0}};
  assert(check_definitions(text(source), &environment, &failure));
  assert(same_text(printed(value_named(environment, "o")->value), text("{\"witness\":1,\"payload\":null}")));
  assert(same_text(printed(value_named(environment, "f")->value), text("{\"witness\":true,\"payload\":null}")));
  assert(same_text(printed(value_named(environment, "l")->value), text("{\"witness\":[1],\"payload\":null}")));
  sigma_refused("def f : Sigma (x : Flag) (Eq Flag x flagNo) := pack flagYes refl\n", "refl",
                text("refl needs two equal sides"));
  sigma_refused("def l : Sigma (x : List Nat) (Eq (List Nat) x nil) := pack (cons 1 nil) refl\n", "refl",
                text("refl needs two equal sides"));
}

static void test_d5_equality_carrier(void) {
  const char *source =
      "def s : Sigma (z : Nat) (Eq Nat 1 z) := pack 1 refl\n"
      "def u : Sigma (x : Nat) (Sigma (y : Sigma (z : Nat) (Eq Nat x z)) (Eq (Sigma (z : Nat) (Eq Nat x z)) y y)) := pack 1 (pack s refl)\n"
      "def p : Eq (Sigma (z : Nat) (Eq Nat 1 z)) s s := payload (payload u)\n";
  const Bindings *environment = NULL;
  Failure failure = {0, {NULL, 0}};
  assert(check_definitions(text(source), &environment, &failure));
  assert(same_text(printed(value_named(environment, "p")->value), text("null")));
  char bad[1024];
  int size = snprintf(bad, sizeof bad, "%s%s", source,
      "def s2 : Sigma (z : Nat) (Eq Nat 2 z) := pack 2 refl\n"
      "def bad : Eq (Sigma (z : Nat) (Eq Nat 2 z)) s2 s2 := payload (payload u)\n");
  assert(size > 0 && (size_t)size < sizeof bad);
  environment = NULL;
  assert(!check_definitions(text(bad), &environment, &failure));
  assert(failure.position == (Nat)(strstr(strstr(bad, "def bad :"), "payload") - bad));
  assert(same_text(failure.message, eTerm));
}

/* D6 part A: cong f e (design items 3 to 5 and 8). synth form 8. A neutral
   e: the built sides (inc x) and (inc y) against the parsed sides, symm of
   cong, and cong in a group. A closed e. The refusals: the built side
   (inc y) against the parsed side (inc x) gives eTerm. Then eInfer, eCong
   (no name, two parameters), eUnknown, eProof, eMatch, and eTerm for a
   closed e on Text (delta D1). Called from main after test_d5_scope. */
static void test_d6_cong(void) {
  assert(synth_form(text("cong")) == 8);
  const char *source =
      "def inc : (n : Nat) -> Nat := fun (n : Nat) => n\n"
      "def f : (x : Nat) -> (y : Nat) -> (e : Eq Nat x y) -> Eq Nat (inc x) (inc y) :=\n"
      "  fun (x : Nat) (y : Nat) (e : Eq Nat x y) => cong inc e\n"
      "def g : (x : Nat) -> (y : Nat) -> (e : Eq Nat x y) -> Eq Nat (inc y) (inc x) :=\n"
      "  fun (x : Nat) (y : Nat) (e : Eq Nat x y) => symm (cong inc e)\n"
      "def h : (x : Nat) -> (y : Nat) -> (e : Eq Nat x y) -> Eq Nat (inc x) (inc y) :=\n"
      "  fun (x : Nat) (y : Nat) (e : Eq Nat x y) => (cong inc e)\n"
      "def pf : Eq Nat 1 1 := refl\n"
      "def c : Eq Nat (inc 1) (inc 1) := cong inc pf\n";
  const Bindings *environment = NULL;
  Failure failure = {0, {NULL, 0}};
  assert(check_definitions(text(source), &environment, &failure));

  sigma_refused("def inc : (n : Nat) -> Nat := fun (n : Nat) => n\n"
                "def f : (x : Nat) -> (y : Nat) -> (e : Eq Nat x y) -> Eq Nat (inc x) (inc x) :=\n"
                "  fun (x : Nat) (y : Nat) (e : Eq Nat x y) => cong inc e\n",
                "cong inc e", eTerm);
  sigma_refused("def inc : (n : Nat) -> Nat := fun (n : Nat) => n\n"
                "def c : Eq Nat (inc 1) (inc 1) := cong inc refl\n",
                "refl", eInfer);
  sigma_refused("def inc : (n : Nat) -> Nat := fun (n : Nat) => n\n"
                "def pf : Eq Nat 1 1 := refl\n"
                "def c : Eq Nat (inc 1) (inc 1) := cong 1 pf\n",
                "1 pf", eCong);
  sigma_refused("def add : (m : Nat) -> (n : Nat) -> Nat := fun (m : Nat) (n : Nat) => m\n"
                "def pf : Eq Nat 1 1 := refl\n"
                "def c : Eq Nat (add 1 1) (add 1 1) := cong add pf\n",
                "add pf", eCong);
  sigma_refused("def inc : (n : Nat) -> Nat := fun (n : Nat) => n\n"
                "def pf : Eq Nat 1 1 := refl\n"
                "def c : Eq Nat (inc 1) (inc 1) := cong nope pf\n",
                "nope pf", eUnknown);
  sigma_refused("def inc : (n : Nat) -> Nat := fun (n : Nat) => n\n"
                "def one : Nat := 1\n"
                "def c : Eq Nat (inc 1) (inc 1) := cong inc one\n",
                "cong inc one", eProof);
  sigma_refused("def len : (t : Text) -> Nat := fun (t : Text) => 1\n"
                "def pf : Eq Nat 1 1 := refl\n"
                "def c : Eq Nat (len \"a\") (len \"a\") := cong len pf\n",
                "cong len pf", eMatch);
  /* D11 part B (USER ruling Q-D11-10 (a)): a closed side of type Text reads
     back from its text, and cong tx tp checks. */
  const Bindings *texts = NULL;
  assert(check_definitions(text("def tx : (t : Text) -> Text := fun (t : Text) => t\n"
                                "def tp : Eq Text \"a\" \"a\" := refl\n"
                                "def c : Eq Text (tx \"a\") (tx \"a\") := cong tx tp\n"),
                           &texts, &failure));
}

/* Closed congruence sides share the caller's remaining body budget on
   both the token path and the captured term path. */
static void test_d6_cong_budget(void) {
  const char *source =
      "def inc : (n : Nat) -> Nat := fun (n : Nat) => n\n"
      "def pf : Eq Nat 1 1 := refl\n";
  const Bindings *environment = NULL;
  Failure failure = {0, {NULL, 0}};
  assert(check_definitions(text(source), &environment, &failure));
  Tokens tokens, rest;
  assert(lex(512, text("cong inc pf"), &tokens, &failure));
  Typed found;
  Nat left;
  const Term *term = NULL;
  assert(synth_term(512, 3, 0, environment, tokens, &found, &rest, &left, &term, &failure));
  assert(rest.size == 1 && rest.items[0].kind == TOKEN_PUNCTUATION && rest.items[0].number == 0 && left == 1);
  Typed evaluated;
  assert(eval_synth(512, 3, environment, term, &evaluated, &left, &failure));
  assert(left == 1 && same_type(found.type, evaluated.type));
  const Value *value;
  assert(eval_term(512, 3, found.type, environment, term, &value, &left, &failure));
  assert(left == 1 && value->kind == VALUE_NULL);
  for (Nat budget = 1; budget <= 2; budget++) {
    failure = (Failure){0, {NULL, 0}};
    assert(!synth_term(512, budget, 0, environment, tokens, &evaluated, &rest, &left, NULL, &failure));
    assert(same_text(failure.message, eBudget));
    failure = (Failure){0, {NULL, 0}};
    assert(!eval_synth(512, budget, environment, term, &evaluated, &left, &failure));
    assert(same_text(failure.message, eBudget));
    failure = (Failure){0, {NULL, 0}};
    assert(!eval_term(512, budget, found.type, environment, term, &value, &left, &failure));
    assert(same_text(failure.message, eBudget));
  }
}

/* A marker-free congruence side needs its real value during body checking,
   including when the other side is neutral. */
static void test_d6_cong_closed_body(void) {
  const char *sources[] = {
      "def inc : (n : Nat) -> Nat := fun (n : Nat) => n\n"
      "def pf : Eq Nat 1 1 := refl\n"
      "def f : (n : Nat) -> Eq Nat 1 1 := fun (n : Nat) => cong inc pf\n"
      "def q : Eq Nat 1 1 := f 0\n",
      "def inc : (n : Nat) -> Nat := fun (n : Nat) => n\n"
      "def lift : (x : Nat) -> (e : Eq Nat x 1) -> Eq Nat (inc x) 1 := "
      "fun (x : Nat) (e : Eq Nat x 1) => cong inc e\n",
      "def two : (n : Nat) -> Nat := fun (n : Nat) => 2\n"
      "def pf : Eq Nat 1 1 := refl\n"
      "def f : (n : Nat) -> Eq Nat 2 2 := fun (n : Nat) => cong two pf\n"
      "def q : Eq Nat 2 2 := f 0\n",
  };
  for (Nat index = 0; index < sizeof sources / sizeof sources[0]; index++) {
    const Bindings *environment = NULL;
    Failure failure = {0, {NULL, 0}};
    assert(check_definitions(text(sources[index]), &environment, &failure));
  }
  sigma_refused("def two : (n : Nat) -> Nat := fun (n : Nat) => 2\n"
                "def pf : Eq Nat 1 1 := refl\n"
                "def f : (n : Nat) -> Eq Nat 1 1 := fun (n : Nat) => cong two pf\n",
                "cong two pf", eTerm);
}

/* D6 part B: transport (z : A) B e t. The synth form 9; the motive parse and
   the marker level of z (0 at the top, 3 after 3 parameters); the check of t
   against B with x; the result type B with y; the value of t; the refusals.
   Called from main after test_d6_cong_closed_body. */
static void test_d6_transport(void) {
  assert(synth_form(text("transport")) == 9);
  const char *source =
      "def inc : (n : Nat) -> Nat := fun (n : Nat) => n\n"
      "def pf : Eq Nat 1 1 := refl\n"
      "def q : Eq Nat 1 1 := refl\n"
      "def g : (a : Nat) -> (b : Nat) -> (c : Nat) -> Nat := fun (a : Nat) (b : Nat) (c : Nat) => a\n"
      "def f : (x : Nat) -> (y : Nat) -> (e : Eq Nat x y) -> (p : Eq Nat (inc x) 3) -> Eq Nat (inc y) 3 :=\n"
      "  fun (x : Nat) (y : Nat) (e : Eq Nat x y) (p : Eq Nat (inc x) 3) =>\n"
      "  transport (z : Nat) (Eq Nat (inc z) 3) e p\n"
      "def t : Eq Nat 1 1 := transport (z : Nat) (Eq Nat z 1) pf q\n"
      "def h : (a : Nat) -> (b : Nat) -> (c : Nat) -> Eq Nat 1 1 :=\n"
      "  fun (a : Nat) (b : Nat) (c : Nat) => transport (z : Nat) (Eq Nat z 1) pf q\n"
      "def u : Option Nat := transport (z : Nat) (Option Nat) pf (some 1)\n";
  const Bindings *environment = NULL;
  Failure failure = {0, {NULL, 0}};
  assert(check_definitions(text(source), &environment, &failure));

  /* The motive parse. The marker of z is at level 0 at the top and at level 3
     after the 3 parameters of g. */
  Tokens tokens, rest;
  const LType *motive = NULL;
  assert(lex(512, text("(z : Nat) (Eq Nat z 1) pf q"), &tokens, &failure));
  Nat motive_left;
  assert(sigma_type(512, 1, environment, NULL, tokens, &motive, &rest, &motive_left, &failure));
  assert(motive->tag == TY_SIGMA && same_text(motive->name, text("z")) && motive->level == 0);
  assert(motive->left->tag == TY_NAT && motive->right->tag == TY_EQ && rest.size == 3);
  assert(motive->right->lhs.kind == VAL_VAR && motive->right->lhs.index == 0);
  assert(sigma_type(512, 1, environment, fun_named(environment, "g")->params, tokens, &motive, &rest, &motive_left,
                    &failure));
  assert(motive->tag == TY_SIGMA && motive->level == 3);
  assert(motive->right->lhs.kind == VAL_VAR && motive->right->lhs.index == 3);

  /* On a closed e, the result has the type B with y and the value of t (some
     1), not the value of e. */
  assert(lex(512, text("transport (z : Nat) (Option Nat) pf (some 1)"), &tokens, &failure));
  Typed found;
  Nat left;
  const Term *term = NULL;
  assert(synth_term(512, 512, 0, environment, tokens, &found, &rest, &left, &term, &failure));
  assert(found.type->tag == TY_OPTION && rest.size == 1);
  Typed evaluated;
  assert(eval_synth(512, 512, environment, term, &evaluated, &left, &failure));
  assert(same_type(found.type, evaluated.type));
  const Value *value;
  assert(eval_term(512, 512, found.type, environment, term, &value, &left, &failure));
  assert(found.value != NULL && found.value->kind != VALUE_NULL);
  assert(found.value->kind == value->kind && found.value->number == value->number);

  /* t with the type B with y is refused at t. A declared result B with x is
     refused at transport. A motive on Text with e on Nat gives eMatch. */
  sigma_refused("def inc : (n : Nat) -> Nat := fun (n : Nat) => n\n"
                "def f : (x : Nat) -> (y : Nat) -> (e : Eq Nat x y) -> (p : Eq Nat (inc y) 3) -> Eq Nat (inc y) 3 :=\n"
                "  fun (x : Nat) (y : Nat) (e : Eq Nat x y) (p : Eq Nat (inc y) 3) =>\n"
                "  transport (z : Nat) (Eq Nat (inc z) 3) e p\n",
                "p\n", eTerm);
  sigma_refused("def inc : (n : Nat) -> Nat := fun (n : Nat) => n\n"
                "def f : (x : Nat) -> (y : Nat) -> (e : Eq Nat x y) -> (p : Eq Nat (inc x) 3) -> Eq Nat (inc x) 3 :=\n"
                "  fun (x : Nat) (y : Nat) (e : Eq Nat x y) (p : Eq Nat (inc x) 3) =>\n"
                "  transport (z : Nat) (Eq Nat (inc z) 3) e p\n",
                "transport", eTerm);
  sigma_refused("def pf : Eq Nat 1 1 := refl\n"
                "def u : Option Nat := transport (z : Text) (Option Nat) pf (some 1)\n",
                "transport", eMatch);
}

/* Transport motives resolve the free value and type parameters of each
   application, including motives with a nested Sigma binder. */
static void test_d6_transport_scope(void) {
  const char *source =
      "def f : (x : Nat) -> (p : Eq Nat x x) -> Eq Nat x x :=\n"
      "  fun (x : Nat) (p : Eq Nat x x) => transport (z : Nat) (Eq Nat z x) p p\n"
      "def q : Eq Nat 1 1 := refl\n"
      "def r : Eq Nat 1 1 := f 1 q\n"
      "def move : (A : Type 0) -> (e : Eq Nat 1 1) -> (a : A) -> A :=\n"
      "  fun (A : Type 0) (e : Eq Nat 1 1) (a : A) => transport (z : Nat) A e a\n"
      "def n : Nat := move Nat q 11\n"
      "def t : Text := move Text q \"hello\"\n"
      "def g : (x : Nat) -> (p : Eq Nat x x) -> Sigma (w : Nat) (Eq Nat w x) :=\n"
      "  fun (x : Nat) (p : Eq Nat x x) =>\n"
      "  transport (z : Nat) (Sigma (w : Nat) (Eq Nat w z)) p (pack x p)\n"
      "def s : Sigma (w : Nat) (Eq Nat w 1) := g 1 q\n";
  const Bindings *environment = NULL;
  Failure failure = {0, {NULL, 0}};
  assert(check_definitions(text(source), &environment, &failure));
  const Binding *item;
  assert(lookup(text("n"), environment, &item));
  assert(same_text(printed(item->value), text("11")));
  assert(lookup(text("t"), environment, &item));
  assert(same_text(printed(item->value), text("\"hello\"")));

  /* The parsed application and the node path must agree after the body
     parameters have been replaced by closed arguments. */
  Tokens tokens, rest;
  const Term *term = NULL;
  Typed parsed, evaluated;
  Nat left;
  assert(lex(512, text("f 1 q"), &tokens, &failure));
  assert(synth_term(512, 512, 0, environment, tokens, &parsed, &rest, &left, &term, &failure));
  assert(rest.size == 1);
  assert(eval_synth(512, 512, environment, term, &evaluated, &left, &failure));
  assert(same_type(parsed.type, evaluated.type));
  assert(same_text(printed(parsed.value), printed(evaluated.value)));
}

/* D7 part A: a Query type is a parameter type and a result type. A function
   type with a Query parameter or a Query result is in Type 1. */
#define D7_ASK                                                 \
  "def deal : Ref kindCommercial := refTo (hashOf \"deal\")\n" \
  "def ask : Query Flag := queryAmountReconciled deal\n"
#define D7_F "def f : (q : Query Flag) -> Query Flag := fun (q : Query Flag) => q\n"
#define D7_G "def g : (T : Type 0) -> (q : Query T) -> Query T := fun (T : Type 0) (q : Query T) => q\n"

static void test_d7_query_param(void) {
  const Bindings *environment = NULL;
  Failure failure = {0, {NULL, 0}};
  const Binding *item;
  const Binding *ask;
  assert(check_definitions(text(D7_F D7_G), &environment, &failure));
  assert(lookup(text("g"), environment, &item) && item->params != NULL && item->params->tail != NULL);
  /* The signature keeps the type parameter T in TY_QUERY.left by its name;
     instantiate_type replaces it at an application. */
  const LType *query = item->params->tail->head.type;
  assert(query->tag == TY_QUERY && query->left->tag == TY_SCHEMA);
  assert(same_text(query->left->name, item->params->head.name) && same_type(item->type, query));

  environment = NULL;
  assert(check_definitions(text(D7_ASK D7_F "def a2 : Query Flag := f ask\n"), &environment, &failure));
  assert(lookup(text("ask"), environment, &ask) && lookup(text("a2"), environment, &item));
  assert(same_type(item->type, ask->type));
  environment = NULL;
  assert(check_definitions(text(D7_ASK D7_G "def a3 : Query Flag := g Flag ask\n"), &environment, &failure));
  assert(lookup(text("ask"), environment, &ask) && lookup(text("a3"), environment, &item));
  assert(same_type(item->type, ask->type));

  const char *a4 = D7_ASK D7_F "def a4 : Query Verdict := f ask\n";
  environment = NULL;
  assert(!check_definitions(text(a4), &environment, &failure));
  assert(failure.position == (Nat)(strstr(strstr(a4, "def a4 :"), "f ask") - a4) && same_text(failure.message, eTerm));
  sigma_refused(D7_ASK D7_G "def a5 : Query Verdict := g Flag ask\n", "g Flag ask", eTerm);

  environment = NULL;
  assert(check_definitions(text("def F : Type 1 := (q : Query Flag) -> Flag\n"
                                "def F1 : Type 1 := (n : Nat) -> Query Flag\n"),
                           &environment, &failure));
  assert(lookup(text("F"), environment, &item) && item->kind == BIND_ARROW && is_query_type(item->params->head.type));
  assert(lookup(text("F1"), environment, &item) && item->kind == BIND_ARROW && is_query_type(item->type));
  sigma_refused("def F0 : Type 0 := (q : Query Flag) -> Flag", "(q", eUniverse);
  /* The level of F comes from the rule of parse_definition, not from
     type_level of TY_ARROW (1 for each arrow). A Query parameter type is in
     Type 1. */
  assert(lookup(text("F"), environment, &item) && type_level(item->params->head.type) == 1);

  sigma_refused("def h : (x : Option (Query Flag)) -> Nat := fun (x : Option (Query Flag)) => 1", "(Query", eData);
  sigma_refused("def k : (x : Type 1) -> Nat := fun (x : Type 1) => 1", "Type 1", eData);
}

static void test_d7_query_universe(void) {
  sigma_refused("def F : Type 1 := (q : Query Flag) -> Flag\n"
                "def H : Type 0 := (f : F) -> Nat\n", "(f", eUniverse);
  sigma_refused("def F : Type 1 := (n : Nat) -> Query Flag\n"
                "def H : Type 0 := (f : F) -> Nat\n", "(f", eUniverse);
  sigma_refused("def F : Type 1 := (q : Query Flag) -> Flag\n"
                "def H : Type 1 := (f : F) -> Nat\n"
                "def J : Type 0 := (h : H) -> Nat\n", "(h", eUniverse);

  const Bindings *environment = NULL;
  Failure failure = {0, {NULL, 0}};
  assert(check_definitions(text("def F : Type 1 := (q : Query Flag) -> Flag\n"
                                "def G : Type 1 := (n : Nat) -> Query Flag\n"
                                "def H : Type 1 := (f : F) -> Nat\n"
                                "def I : Type 1 := (f : G) -> Nat\n"
                                "def J : Type 1 := (h : H) -> Nat\n"
                                "def Alias : Type 1 := J\n"
                                "def Tail : Type 1 := (n : Nat) -> H\n"
                                "def Data : Type 0 := (n : Nat) -> Flag\n"
                                "def HigherData : Type 0 := (f : Data) -> Nat\n"),
                           &environment, &failure));
}

/* D7 part B: the function type ReadPath (design items 6 to 12). The binders
   of the signature and the type parameter answer in the query type and in
   the result, the level 1, the parameter (r : ReadPath), the application of
   a ReadPath parameter, no instance, the reserved name ReadPath, and
   ReadPath in a data position. Called from main after
   test_d7_query_universe. */
#define D7_LIFT                                                                                 \
  "def lift : (r : ReadPath) -> ReadPath := fun (r : ReadPath) (answer : Type 0) (log : Log) " \
  "(query : Query answer) => r answer log query\n"
#define D7_APPLY "fun (r : ReadPath) (log : Log) (ask : Query Flag) => r Flag log ask\n"
#define D7_EMPTY "{\"ledger-lang\":1,\"instances\":[]}"

static void test_d7_read_path(void) {
  const Bindings *environment = NULL;
  Failure failure = {0, {NULL, 0}};
  const Binding *item;
  Text output;
  /* read_path_signature: (answer : Type 0) -> (log : Log) ->
     (query : Query answer) -> answer. The query type and the result keep
     answer by its name. */
  assert(check_definitions(text("def R : Type 1 := ReadPath\n"), &environment, &failure));
  assert(lookup(text("R"), environment, &item) && item->kind == BIND_ARROW);
  const Params *params = item->params;
  assert(params != NULL && params->tail != NULL && params->tail->tail != NULL && params->tail->tail->tail == NULL);
  assert(same_text(params->head.name, text("answer")) && params->head.type->tag == TY_UNIVERSE &&
         params->head.type->level == 0);
  assert(same_text(params->tail->head.name, text("log")) && params->tail->head.type->tag == TY_LIST);
  const LType *query = params->tail->tail->head.type;
  assert(same_text(params->tail->tail->head.name, text("query")) && query->tag == TY_QUERY);
  assert(query->left->tag == TY_SCHEMA && same_text(query->left->name, params->head.name));
  assert(item->type->tag == TY_SCHEMA && same_text(item->type->name, params->head.name));
  sigma_refused("def R : Type 0 := ReadPath", "ReadPath", eUniverse);

  /* parameter_type of (r : ReadPath): a function type in Type 1. The arrow
     keeps the name answer of its type parameter (types.c arrow_type), and
     arrow_params gives the three binders. A value parameter has no name in
     the arrow. */
  environment = NULL;
  assert(check_definitions(text("def T : Type 1 := (r : ReadPath) -> Nat\n"), &environment, &failure));
  assert(lookup(text("T"), environment, &item) && item->kind == BIND_ARROW);
  const LType *reader = item->params->head.type;
  assert(reader->tag == TY_ARROW && same_text(reader->name, text("answer")) && type_level(reader) == 1);
  const Params *binders = arrow_params(reader);
  assert(binders != NULL && binders->tail != NULL && binders->tail->tail != NULL);
  assert(same_text(binders->head.name, text("answer")) && binders->tail->head.type->tag == TY_LIST);
  assert(binders->tail->tail->head.type->tag == TY_QUERY);
  sigma_refused("def T : Type 0 := (r : ReadPath) -> Nat", "(r", eUniverse);

  /* The application of a ReadPath parameter has the type of its type
     argument: Flag for `r Flag log ask`, the type parameter of lift for
     `r answer log query`, and T for `r T log ask`. */
  assert(compile_program(text(D7_LIFT), &output, &failure) && same_text(output, text(D7_EMPTY)));
  assert(compile_program(text("def g : (r : ReadPath) -> (log : Log) -> (ask : Query Flag) -> Flag := " D7_APPLY),
                         &output, &failure) &&
         same_text(output, text(D7_EMPTY)));
  sigma_refused("def g : (r : ReadPath) -> (log : Log) -> (ask : Query Flag) -> Verdict := " D7_APPLY, "r Flag",
                eTerm);
  environment = NULL;
  assert(check_definitions(text("def c : (answer : Type 0) -> (r : ReadPath) -> (log : Log) -> "
                                "(ask : Query answer) -> answer := "
                                "fun (T : Type 0) (r : ReadPath) (log : Log) (ask : Query T) => r T log ask\n"),
                           &environment, &failure));
  const char *wrong = "def lift : (r : ReadPath) -> ReadPath := fun (r : ReadPath) (answer : Type 0) (log : Log) "
                      "(query : Query answer) => log\n";
  environment = NULL;
  assert(!check_definitions(text(wrong), &environment, &failure));
  assert(failure.position == (Nat)(strstr(wrong, "=> log") + 3 - wrong) && same_text(failure.message, eTerm));

  /* The definitions lift and g above are not instances (D7_EMPTY). The body
     query has the type Query answer, not answer. */
  const char *value = "def r : ReadPath := fun (answer : Type 0) (log : Log) (query : Query answer) => query";
  environment = NULL;
  assert(!check_definitions(text(value), &environment, &failure));
  assert(failure.position == (Nat)(strstr(value, "=> query") + 3 - value) && same_text(failure.message, eTerm));

  /* ReadPath is a reserved name: a parameter or a definition cannot take it,
     thus no binding hides the function type. */
  sigma_refused("def f : (ReadPath : Type 0) -> (x : ReadPath) -> ReadPath := "
                "fun (ReadPath : Type 0) (x : ReadPath) => x",
                "ReadPath", text("reserved definition name"));
  sigma_refused("def ReadPath : Type 0 := Nat", "ReadPath", text("reserved definition name"));

  /* named_type: ReadPath in a data position gives eData. */
  sigma_refused("def x : Option (ReadPath) := none", "ReadPath", eData);
  sigma_refused("def f : (w : List ReadPath) -> Nat := fun (w : Nat) => 1", "ReadPath", eData);
}

static void test_d7_type_names(void) {
  Text output;
  Failure failure = {0, {NULL, 0}};
  const Text expected = text("{\"ledger-lang\":1,\"instances\":[{\"name\":\"n\",\"type\":\"Nat\",\"value\":3}]}");
  /* Type aliases and implementations may rename their bound type variables. */
  assert(compile_program(text("def Poly : Type 1 := (A : Type 0) -> (x : A) -> A\n"
                              "def PolyB : Type 1 := (B : Type 0) -> (x : B) -> B\n"
                              "def id : PolyB := fun (T : Type 0) (x : T) => x\n"
                              "def use : (f : Poly) -> Nat := fun (f : Poly) => f Nat 3\n"
                              "def n : Nat := use id\n"), &output, &failure));
  assert(same_text(output, expected));
  assert(compile_program(text("def Poly : Type 1 := (A : Type 0) -> (x : A) -> A\n"
                              "def id : Poly := fun (T : Type 0) (x : T) => x\n"
                              "def use : (f : Poly) -> Nat := fun (f : Poly) => f Nat 3\n"
                              "def n : Nat := use id\n"), &output, &failure));
  assert(same_text(output, expected));
  assert(compile_program(text("def Alias : Type 1 := (T : Type 0) -> (log : Log) -> (query : Query T) -> T\n"
                              "def accept : (f : Alias) -> Nat := fun (f : Alias) => 1\n"
                              "def forward : (r : ReadPath) -> Nat := fun (r : ReadPath) => accept r\n"),
                         &output, &failure));
  assert(same_text(output, text(D7_EMPTY)));

  /* A free name cannot equal a bound variable, and distinct binders stay distinct. */
  const LType a = {.tag = TY_SCHEMA, .name = text("A")};
  const LType b = {.tag = TY_SCHEMA, .name = text("B")};
  const LType universe = {.tag = TY_UNIVERSE, .level = 0};
  const Params pa = {{text("A"), &universe}, NULL};
  const Params pb = {{text("B"), &universe}, NULL};
  assert(same_type(arrow_type(&pa, &a), arrow_type(&pb, &b)));
  assert(!same_type(arrow_type(&pa, &a), arrow_type(&pb, &a)));
  assert(!same_type(arrow_type(&pa, &b), arrow_type(&pb, &b)));
  const Params both = {{text("A"), &universe}, &pb};
  assert(!same_type(arrow_type(&both, &a), arrow_type(&both, &b)));

  /* Unknown types retain their own diagnostic after ReadPath becomes available. */
  sigma_refused("def x : Unknown := nil", "Unknown", eType);
}

#undef D7_LIFT
#undef D7_APPLY
#undef D7_EMPTY
#undef D7_ASK
#undef D7_F
#undef D7_G

/* D8 part B: the side of the argument args in the body of h (the body scope
   of program.c parse_function), and the left side of someA instantiated with
   args. */
typedef struct {
  Val argument;
  Val side;
} SideRow;

static SideRow h_side_row(const Bindings *environment, const char *args) {
  const Binding *item = fun_named(environment, "someA");
  Bindings *body = arena_alloc(sizeof *body);
  *body = (Bindings){.head = body_marker(1), .tail = bind_params(fun_named(environment, "h")->params, NULL, environment)};
  const Values *values;
  Tokens rest;
  Nat left;
  const Terms *terms = NULL;
  Failure failure;
  Tokens tokens = lexed(args);
  assert(parse_arguments(1000, 1000, 1, param_types(item->params), body, tokens, &values, &rest, &left, &terms,
                         &failure));
  assert(rest.size == 0);
  SideRow row;
  assert(argument_side(1000, 1000, 0, body, item->params, values, terms, &row.argument, &(Nat){0},
                       &(Failure){0, {NULL, 0}}));
  assert(instantiate_side(1000, 1000, body, item->params, values, terms, tokens, lhs_of(environment, "someA"),
                          &row.side, &(Nat){0}, &(Failure){0, {NULL, 0}}));
  return row;
}

/* D8 part B (T3, T4 and P4): sides and witnesses come from checked Terms,
   and a side gets the remaining work budget. */
static void test_d8_sides(void) {
  const char *c1 = "def someA : (n : Nat) -> Eq (Option Nat) (some n) (some n) := fun (n : Nat) => refl\n"
                   "def p : Eq (Option Nat) (some 2) (some 2) := someA 2\n"
                   "def h : (m : Nat) -> Eq (Option Nat) (some m) (some m) := fun (m : Nat) => someA (m)\n"
                   "def q : Eq (Option Nat) (some 3) (some 3) := h 3\n";
  const char *control = "def someA : (n : Nat) -> Eq (Option Nat) (some n) (some n) := fun (n : Nat) => refl\n"
                        "def h : (m : Nat) -> Eq (Option Nat) (some m) (some m) := fun (m : Nat) => someA m\n"
                        "def q : Eq (Option Nat) (some 3) (some 3) := h 3\n";
  const Bindings *environment = NULL;
  Failure failure = {0, {NULL, 0}};
  assert(check_definitions(text(c1), &environment, &failure));

  /* T3: the computed side of someA is a Term with the marker of n, and both
     sides are the same Val. */
  const LType *a;
  Val lhs;
  Val rhs;
  assert(sides_of(fun_named(environment, "someA")->type, &a, &lhs, &rhs));
  assert(lhs.kind == VAL_TERM && lhs.node != NULL && marker_vars_at(lhs.node) == 1 && kept_side(lhs) == 1);
  assert(same_val(lhs, rhs));

  /* T3 (design item 7, probe c1): in the body of h, the side of `(m)` is the
     side of `m` (VAL_VAR), and someA (m) gives the same side as someA m. */
  SideRow grouped = h_side_row(environment, "(m)");
  SideRow plain = h_side_row(environment, "m");
  assert(grouped.argument.kind == VAL_VAR && plain.argument.kind == VAL_VAR);
  assert(same_val(grouped.argument, plain.argument));
  assert(grouped.side.kind == VAL_TERM && marker_vars_at(grouped.side.node) == 1);
  assert(same_val(grouped.side, plain.side));

  /* c1 and its control `someA m` check and write no instance. */
  Text output;
  assert(compile_program(text(c1), &output, &failure));
  assert(same_text(output, text("{\"ledger-lang\":1,\"instances\":[]}")));
  assert(compile_program(text(control), &output, &failure));
  assert(same_text(output, text("{\"ledger-lang\":1,\"instances\":[]}")));

  /* T4 (design item 8, probe d2): the witness side of `pack n refl` and of
     `witness t` comes from the checked Term of the argument. payload u does
     not have the witness of t. */
  assert(compile_program(text("def s : Sigma (x : Nat) (Eq Nat x x) := pack 5 refl\n"
                              "def pw : (t : Sigma (x : Nat) (Eq Nat x x)) -> Eq Nat (witness t) (witness t) := "
                              "fun (t : Sigma (x : Nat) (Eq Nat x x)) => payload t\n"
                              "def e : Eq Nat 5 5 := pw s\n"
                              "def mk : (n : Nat) -> Sigma (x : Nat) (Eq Nat x x) := fun (n : Nat) => pack n refl\n"
                              "def mkg : (n : Nat) -> Sigma (x : Nat) (Eq Nat x x) := fun (n : Nat) => pack (n) refl\n"),
                         &output, &failure));
  assert(same_text(output, text("{\"ledger-lang\":1,\"instances\":[{\"name\":\"s\",\"type\":\"Sigma (x : Nat) "
                                "(Eq (Nat) (x) (x))\",\"value\":{\"witness\":5,\"payload\":null}}]}")));
  sigma_refused("def pw : (t : Sigma (x : Nat) (Eq Nat x x)) -> (u : Sigma (x : Nat) (Eq Nat x x)) -> "
                "Eq Nat (witness t) (witness t) := "
                "fun (t : Sigma (x : Nat) (Eq Nat x x)) (u : Sigma (x : Nat) (Eq Nat x x)) => payload u\n",
                "payload", eTerm);

  /* P4 (probes f2 and f3): a computed side with a remaining budget above 1
     evaluates the application id 2. f2 and f3 check with compile_program
     and write no instance. */
  const char *f2 = "def id : (x : Nat) -> Nat := fun (x : Nat) => x\n"
                   "def k : (n : Nat) -> Eq Nat (id 2) 2 := fun (n : Nat) => refl\n";
  const char *f3 = "def id : (x : Nat) -> Nat := fun (x : Nat) => x\n"
                   "def q : Eq Nat 2 2 := refl\n"
                   "def k : (n : Nat) -> Eq Nat (id 2) 2 := fun (n : Nat) => q\n";
  const Bindings *budget_scope = NULL;
  assert(check_definitions(text(f2), &budget_scope, &failure));
  assert(sides_of(fun_named(budget_scope, "k")->type, &a, &lhs, &rhs));
  assert(lhs.kind == VAL_CLOSED && same_val(lhs, rhs));
  assert(compile_program(text(f2), &output, &failure));
  assert(same_text(output, text("{\"ledger-lang\":1,\"instances\":[]}")));
  assert(compile_program(text(f3), &output, &failure));
  assert(same_text(output, text("{\"ledger-lang\":1,\"instances\":[]}")));
}

static void test_d8_grouped_sides(void) {
  const char *head =
      "def someA : (n : Nat) -> Eq (Option Nat) (some n) (some n) := fun (n : Nat) => refl\n"
      "def pf : (n : Nat) -> (m : Nat) -> Eq (Prod Nat Nat) (pair n m) (pair n m) := "
      "fun (n : Nat) (m : Nat) => refl\n";
  const char *accepted[] = {
      "def g : (m : Nat) -> Eq (Option Nat) (some (m)) (some (m)) := fun (m : Nat) => someA (m)\n",
      "def g : (m : Nat) -> Eq (Option Nat) (some ((m))) (some ((m))) := fun (m : Nat) => someA ((m))\n",
      "def g : (m : Nat) -> Eq (Prod Nat Nat) (pair (m) 1) (pair (m) 1) := fun (m : Nat) => pf (m) 1\n",
      "def g : (m : Nat) -> Eq (Prod Nat Nat) (pair ((m)) 1) (pair ((m)) 1) := fun (m : Nat) => pf ((m)) 1\n",
      "def g : (m : Nat) -> (p : Eq Nat (m) (m)) -> Sigma (x : Nat) (Eq Nat x x) := "
      "fun (m : Nat) (p : Eq Nat (m) (m)) => pack (m) p\n",
      "def g : (m : Nat) -> (p : Eq Nat ((m)) ((m))) -> Sigma (x : Nat) (Eq Nat x x) := "
      "fun (m : Nat) (p : Eq Nat ((m)) ((m))) => pack ((m)) p\n"};
  for (size_t at = 0; at < sizeof accepted / sizeof *accepted; at++) {
    char source[2048];
    int length = snprintf(source, sizeof source, "%s%s", head, accepted[at]);
    assert(length > 0 && (size_t)length < sizeof source);
    Text output;
    Failure failure = {0};
    assert(compile_program(text(source), &output, &failure));
    assert(same_text(output, text("{\"ledger-lang\":1,\"instances\":[]}")));
  }
  const char *refused[] = {
      "def g : (m : Nat) -> (n : Nat) -> Eq (Option Nat) (some (m)) (some (m)) := "
      "fun (m : Nat) (n : Nat) => someA (n)\n",
      "def g : (m : Nat) -> (n : Nat) -> (p : Eq Nat (n) (n)) -> Sigma (x : Nat) (Eq Nat x x) := "
      "fun (m : Nat) (n : Nat) (p : Eq Nat (n) (n)) => pack (m) p\n"};
  for (size_t at = 0; at < sizeof refused / sizeof *refused; at++) {
    char source[2048];
    int length = snprintf(source, sizeof source, "%s%s", head, refused[at]);
    assert(length > 0 && (size_t)length < sizeof source);
    Text output;
    Failure failure = {0};
    assert(!compile_program(text(source), &output, &failure));
    assert(same_text(failure.message, eTerm));
  }
}

/* D-C1 (USER ruling 3): a group around a variable that is a full side stays
   a different side for refl. */
static void test_d8_side_groups(void) {
  const char *refused[] = {
      "def g : (n : Nat) -> Eq Nat (n) n := fun (n : Nat) => refl\n",
      "def g : (n : Nat) -> Eq Nat ((n)) (n) := fun (n : Nat) => refl\n"};
  for (size_t at = 0; at < sizeof refused / sizeof *refused; at++) {
    Text output;
    Failure failure = {0};
    assert(!compile_program(text(refused[at]), &output, &failure));
    assert(same_text(failure.message, eRefl));
  }
}

/* A parsed proof keeps its declared-type compatibility when evaluated. */
static void test_d8_declared_evaluation(void) {
  const char *source =
      "def g : (m : Nat) -> (p : Eq Nat (m) (m)) -> Eq Nat m m := "
      "fun (m : Nat) (p : Eq Nat (m) (m)) => p\n";
  const Bindings *environment = NULL;
  Failure failure = {0};
  assert(check_definitions(text(source), &environment, &failure));
  const Binding *function = fun_named(environment, "g");
  Bindings body = {.head = body_marker(2), .tail = bind_params(function->params, NULL, environment)};
  const Binding *proof;
  assert(lookup(text("p"), &body, &proof));
  const Term *node = function->term->callee;
  assert(node != NULL && node->tag == TERM_VAR);
  const Value *value;
  Nat left;
  assert(eval_term(512, 512, function->type, &body, function->term, &value, &left, &failure));
  assert(same_text(printed(value), text("null")));

  /* The name and constructor views use the same declared-type check. */
  Term named = *node;
  named.tag = TERM_NAME;
  assert(eval_term(512, 512, function->type, &body, &named, &value, &left, &failure));
  named.tag = TERM_CONSTRUCT;
  assert(eval_term(512, 512, function->type, &body, &named, &value, &left, &failure));
  const Term *closed = term_closed(node->position, proof->type, proof->value, text("null"));
  assert(eval_term(512, 512, function->type, &body, closed, &value, &left, &failure));

  /* A value of function type reaches eval_name_argument. */
  LType expected = {.tag = TY_ARROW, .left = function->type, .right = function->type};
  LType actual = {.tag = TY_ARROW, .left = proof->type, .right = proof->type};
  Bindings higher = {.head = {.kind = BIND_VALUE, .name = text("h"), .type = &actual, .value = proof->value},
                     .tail = &body};
  const Term *name = term_named(TERM_NAME, 0, 0, text("h"), NULL, NULL);
  assert(eval_term(512, 512, &expected, &higher, name, &value, &left, &failure));
}

/* The type of the node path of a call. It must be the type of the parsed
   call. */
static Typed motive_call(const Bindings *environment, const char *call) {
  Tokens tokens, rest;
  const Term *term = NULL;
  Typed parsed, evaluated;
  Nat left;
  Failure failure = {0, {NULL, 0}};
  assert(lex(512, text(call), &tokens, &failure));
  assert(synth_term(512, 512, 0, environment, tokens, &parsed, &rest, &left, &term, &failure));
  assert(rest.size == 1);
  assert(eval_synth(512, 512, environment, term, &evaluated, &left, &failure));
  assert(same_type(parsed.type, evaluated.type));
  assert(same_text(printed(parsed.value), printed(evaluated.value)));
  return evaluated;
}

/* D8 part C (test_d8_transport_motive in the test plan): the motive of
   TERM_TRANSPORT is the LType of the check with markers and no source, and
   eval_synth puts the type and value arguments of an application in it. */
static void test_d8_motive(void) {
  const char *source =
      "def f : (x : Nat) -> (p : Eq Nat x x) -> Eq Nat x x :=\n"
      "  fun (x : Nat) (p : Eq Nat x x) => transport (z : Nat) (Eq Nat z x) p p\n"
      "def q : Eq Nat 1 1 := refl\n"
      "def move : (A : Type 0) -> (e : Eq Nat 1 1) -> (a : A) -> A :=\n"
      "  fun (A : Type 0) (e : Eq Nat 1 1) (a : A) => transport (z : Nat) A e a\n";
  const Bindings *environment = NULL;
  Failure failure = {0, {NULL, 0}};
  assert(check_definitions(text(source), &environment, &failure));

  /* The body of f is the TERM_TRANSPORT. Its motive has no source: Sigma
     (z : Nat) (Eq Nat z x), with z at marker 2 and x at marker 0. */
  const Term *body = fun_named(environment, "f")->term;
  assert(body->tag == TERM_BODY && body->callee != NULL);
  const Term *node = body->callee;
  assert(node->tag == TERM_TRANSPORT && node->types != NULL && node->types->tail == NULL);
  const TermType *motive = &node->types->head;
  assert(motive->source.size == 0);
  assert(motive->type->tag == TY_SIGMA && motive->type->level == 2);
  const LType *equality = motive->type->right;
  assert(equality->tag == TY_EQ);
  assert(equality->lhs.kind == VAL_VAR && equality->lhs.index == 2);
  assert(equality->rhs.kind == VAL_VAR && equality->rhs.index == 0);

  /* A type parameter: the node path gives Nat, not the schema A. */
  Typed moved = motive_call(environment, "move Nat q 11");
  assert(moved.type->tag == TY_NAT);

  /* Bound Sigma markers in a type argument can share indices with the
     function parameters and the transport binder. They remain bound. */
  Typed nested = motive_call(environment,
      "move (Sigma (u : Nat) (Sigma (v : Nat) (Eq Nat u v))) q (pack 1 (pack 1 refl))");
  assert(nested.type->tag == TY_SIGMA && nested.type->right->tag == TY_SIGMA);
  assert(nested.type->right->right->lhs.kind == VAL_VAR && nested.type->right->right->lhs.index == 0);
  assert(nested.type->right->right->rhs.kind == VAL_VAR && nested.type->right->right->rhs.index == 1);
  Typed deep = motive_call(environment,
      "move (Sigma (u : Nat) (Sigma (v : Nat) (Sigma (w : Nat) (Sigma (r : Nat) (Eq Nat u r))))) "
      "q (pack 1 (pack 2 (pack 3 (pack 1 refl))))");
  assert(deep.type->right->right->right->right->rhs.kind == VAL_VAR);
  assert(deep.type->right->right->right->right->rhs.index == 3);

  /* A value parameter: the node path gives Eq Nat 1 1 with closed sides. */
  Typed proved = motive_call(environment, "f 1 q");
  assert(proved.type->tag == TY_EQ);
  assert(proved.type->lhs.kind == VAL_CLOSED && same_text(proved.type->lhs.text, text("1")));
  assert(proved.type->rhs.kind == VAL_CLOSED && same_text(proved.type->rhs.text, text("1")));
}

/* D9 part A: close_side, side_normal_at and side_normal run on the
   remaining work budget (design items 1 and 2). At budget 1000 each helper
   gives the rest less 1, for the one body of id. At budget 1 each helper
   gives 0 and eBudget at the first token of the body of id (byte 46). */
static void test_d9_side_budget(void) {
  const char *source =
      "def id : (x : Nat) -> Nat := fun (x : Nat) => x\n"
      "def k : (n : Nat) -> Eq Nat (id n) (id n) := fun (n : Nat) => refl\n"
      "def pf : (n : Nat) -> (m : Nat) -> Eq (Prod Nat Nat) (pair n m) (pair n m) := fun (n : Nat) (m : Nat) => refl\n";
  const Bindings *environment = NULL;
  Failure failure = {0, {NULL, 0}};
  assert(check_definitions(text(source), &environment, &failure));
  Nat left = 0;

  /* close_side: the a1 side (id n) with n = 2 closes to 2. */
  const Binding *k = fun_named(environment, "k");
  const Bindings *bound = argument_bindings(0, k->params, call_values(environment, k->params, "2"), environment);
  const LType *a;
  Val lhs;
  Val rhs;
  Val closed;
  assert(sides_of(k->type, &a, &lhs, &rhs) && lhs.kind == VAL_TERM);
  assert(close_side(1000, 1000, bound, a, lhs, &closed, &left, &failure) == 1);
  assert(closed.kind == VAL_CLOSED && same_text(val_text(closed), text("2")) && left == 999);
  failure = (Failure){0, {NULL, 0}};
  assert(close_side(1000, 1, bound, a, lhs, &closed, &left, &failure) == 0);
  assert(failure.position == 46 && same_text(failure.message, eBudget));

  /* side_normal_at: the closed constructor cons (id 2) nil at List Nat
     gives a TERM_CLOSED node. */
  const LType *list = sigma_parsed("List Nat");
  const Value *value;
  Typed found;
  Tokens rest;
  const Term *term = NULL;
  const Term *normal = NULL;
  failure = (Failure){0, {NULL, 0}};
  assert(parse_term(1000, 1000, 0, list, environment, lexed("cons (id 2) nil"), &value, &rest, &left, &term, &failure));
  assert(side_normal_at(1000, 1000, environment, list, term, &normal, &left, &failure) == 1);
  assert(normal->tag == TERM_CLOSED && left == 999);
  failure = (Failure){0, {NULL, 0}};
  assert(side_normal_at(1000, 1, environment, list, term, &normal, &left, &failure) == 0);
  assert(failure.position == 46 && same_text(failure.message, eBudget));

  /* side_normal: the closed application id 2 next to the marker n in the
     node of pair n (id 2) gives the literal 2 node. */
  const Term *pair = ungrouped(lhs_of(environment, "pf").node);
  failure = (Failure){0, {NULL, 0}};
  assert(synth_term(1000, 1000, 0, environment, lexed("id 2"), &found, &rest, &left, &term, &failure));
  const Term *node = as_construct(pair, terms_item(pair->args->head, one(term)));
  assert(side_normal(1000, 1000, environment, node, &normal, &left, &failure) == 1);
  assert(ungrouped(normal)->args->tail->head->tag == TERM_NUMBER && left == 999);
  failure = (Failure){0, {NULL, 0}};
  assert(side_normal(1000, 1, environment, node, &normal, &left, &failure) == 0);
  assert(failure.position == 46 && same_text(failure.message, eBudget));
}

static void test_d9_parameter_budget_failure(void) {
  const char *source =
      "def id : (x : Nat) -> Nat := fun (x : Nat) => x\n"
      "def f : (x : Nat) -> (p : Eq Nat (id x) (id x)) -> Eq Nat (id x) (id x) := fun (x : Nat) (p : Eq Nat (id x) (id x)) => p\n"
      "def r : Eq Nat (id 2) (id 2) := refl\n";
  const Bindings *environment = NULL;
  Failure failure = {0, {NULL, 0}};
  assert(check_definitions(text(source), &environment, &failure));
  Typed found;
  Tokens rest;
  Nat left;
  const Term *node = NULL;
  assert(synth_term(1000, 8, 0, environment, lexed("f 2 r"), &found, &rest, &left, &node, &failure));
  assert(rest.size == 0 && left == 1);
  for (Nat budget = 5; budget < 8; budget++) {
    failure = (Failure){0, {NULL, 0}};
    assert(!synth_term(1000, budget, 0, environment, lexed("f 2 r"), &found, &rest, &left, NULL, &failure));
    assert(same_text(failure.message, eBudget));
    if (budget == 6) assert(failure.position == 46);
    failure = (Failure){0, {NULL, 0}};
    assert(!eval_synth(1000, budget, environment, node, &found, &left, &failure));
    assert(same_text(failure.message, eBudget));
    if (budget == 6) assert(failure.position == 46);
  }
  failure = (Failure){0, {NULL, 0}};
  assert(eval_synth(1000, 8, environment, node, &found, &left, &failure) && left == 1);
}

static Text d9_function_budget_source(Nat depth, Nat signature_work, Nat repeat) {
  TextBuilder source = builder_new();
  builder_append(&source, text("def f0 : (x : Nat) -> Nat := fun (x : Nat) => x\n"));
  char row[256];
  for (Nat k = 1; k <= depth; k++) {
    int size = snprintf(row, sizeof row,
                        "def f%u : (x : Nat) -> Nat := fun (x : Nat) => f%u (f%u x)\n", k, k - 1, k - 1);
    assert(size > 0 && (size_t)size < sizeof row);
    builder_append(&source, text(row));
  }
  builder_append(&source, text("def e : Eq Nat 1 1 := refl\n"));
  for (Nat k = 0; k <= repeat; k++) {
    int size = signature_work
                   ? snprintf(row, sizeof row,
                              "def g%u : (m : Nat) -> Eq Nat (f%u 1) (f%u 1) := fun (m : Nat) => cong f%u e\n",
                              k, depth, depth, depth)
                   : snprintf(row, sizeof row,
                              "def g%u : (m : Nat) -> Eq Nat 1 1 := fun (m : Nat) => cong f%u e\n", k, depth);
    assert(size > 0 && (size_t)size < sizeof row);
    builder_append(&source, text(row));
  }
  return builder_text(&source);
}

static void test_d9_function_budget(void) {
  Text output;
  Failure failure = {0, {NULL, 0}};
  assert(compile_program(d9_function_budget_source(1, 1, 0), &output, &failure));
  assert(compile_program(d9_function_budget_source(9, 1, 0), &output, &failure));
  assert(!compile_program(d9_function_budget_source(10, 1, 0), &output, &failure));
  assert(same_text(failure.message, eBudget));
  assert(!compile_program(d9_function_budget_source(10, 0, 1), &output, &failure));
  assert(same_text(failure.message, eBudget));
}

/* D10: a Sigma side in a type runs on the work budget. At budget 1 the
   body of id is over the budget. At budget 1000 left is less than the
   budget, because the sides evaluate bodies. */
static void test_d10_type_budget(void) {
  const Bindings *environment = NULL;
  Failure failure = {0, {NULL, 0}};
  assert(check_definitions(text("def id : (x : Nat) -> Nat := fun (x : Nat) => x\n"), &environment, &failure));
  const char *source = "Sigma (x : Nat) (Eq Nat (id 2) (id 2))";
  const LType *type;
  Tokens rest;
  Nat left = 0;
  assert(!parse_type(1000, 1, 0, environment, lexed(source), &type, &rest, &left, &failure));
  /* D10 delta: on the eBudget failure, *left keeps the budget (1), not 0. */
  assert(same_text(failure.message, eBudget) && failure.position == 46 && left == 1);
  failure = (Failure){0, {NULL, 0}};
  assert(parse_type(1000, 1000, 0, environment, lexed(source), &type, &rest, &left, &failure) && rest.size == 0);
  assert(type->tag == TY_SIGMA && left == 998);
}

/* Computed type arguments remain available when a partial application
   becomes a callback, on both the token and checked-term paths. */
static void test_d10_partial_type_arguments(void) {
  const char *prefix =
      "def id : (n : Nat) -> Nat := fun (n : Nat) => n\n"
      "def F : Type 0 := (n : Nat) -> Nat\n"
      "def pick : (A : Type 0) -> (n : Nat) -> Nat := fun (A : Type 0) (n : Nat) => n\n"
      "def call : (f : F) -> (n : Nat) -> Nat := fun (f : F) (n : Nat) => f n\n"
      "def step : (A : Type 0) -> (n : Nat) -> (a : Nat) -> Nat := "
      "fun (A : Type 0) (n : Nat) (a : Nat) => n\n"
      "def xs : List Nat := cons 7 nil\n";
  const struct { const char *source; const char *expected; } rows[] = {
      {"def out : Nat := call (pick (Sigma (x : Nat) (Eq Nat (id 2) 2))) 7\n", "7"},
      {"def outer : (n : Nat) -> Nat := fun (n : Nat) => "
       "call (pick (Sigma (x : Nat) (Eq Nat (id 2) 2))) n\n"
       "def out : Nat := outer 7\n", "7"},
      {"def out : List Nat := map (pick (Sigma (x : Nat) (Eq Nat (id 2) 2))) (cons 7 nil)\n", "[7]"},
      {"def outer : (n : Nat) -> List Nat := fun (n : Nat) => "
       "map (pick (Sigma (x : Nat) (Eq Nat (id 2) 2))) (cons n nil)\n"
       "def out : List Nat := outer 7\n", "[7]"},
      {"def out : Nat := fold (step (Sigma (x : Nat) (Eq Nat (id 2) 2))) 0 xs\n", "7"},
      {"def outer : (n : Nat) -> Nat := fun (n : Nat) => "
       "fold (step (Sigma (x : Nat) (Eq Nat (id 2) 2))) n xs\n"
       "def out : Nat := outer 7\n", "7"}
  };
  for (Nat row = 0; row < sizeof rows / sizeof rows[0]; row++) {
    char source[1024];
    int size = snprintf(source, sizeof source, "%s%s", prefix, rows[row].source);
    assert(size > 0 && (size_t)size < sizeof source);
    const Bindings *environment = NULL;
    Failure failure = {0};
    int accepted = check_definitions(text(source), &environment, &failure);
    if (!accepted)
      fprintf(stderr, "partial type argument row %lu: failure at byte %lu\n", (unsigned long)row,
              (unsigned long)failure.position);
    assert(accepted);
    const Binding *out;
    assert(lookup(text("out"), environment, &out));
    assert(same_text(printed(out->value), text(rows[row].expected)));
  }
  const Bindings *environment = NULL;
  Failure failure = {0};
  assert(check_definitions(text(prefix), &environment, &failure));
  Tokens tokens = lexed("call (pick (Sigma (x : Nat) (Eq Nat (id 2) 2))) 7");
  Tokens rest;
  const Value *value;
  const Term *term = NULL;
  Nat left;
  const LType *nat;
  assert(parse_type(1000, 4, 0, environment, lexed("Nat"), &nat, &rest, &left, &failure));
  /* One type-side body, call, and pick cost three units. Rebuilding the
     callback consumes no extra work and never replenishes the budget. */
  assert(parse_term(1000, 4, 0, nat, environment, tokens, &value, &rest, &left, &term, &failure));
  assert(rest.size == 0 && left == 1 && same_text(printed(value), text("7")));
  assert(eval_term(1000, 4, nat, environment, term, &value, &left, &failure));
  assert(left == 1 && same_text(printed(value), text("7")));
  assert(!parse_term(1000, 3, 0, nat, environment, tokens, &value, &rest, &left, NULL, &failure));
  assert(same_text(failure.message, eBudget));
  failure = (Failure){0};
  assert(!eval_term(1000, 3, nat, environment, term, &value, &left, &failure));
  assert(same_text(failure.message, eBudget));
}

/* D11 part A (design item 2): the closed side (id 2) of the c11-a4 call
   `k 2` in a body closes on its value 2, not on the null of the body check.
   At budget 1 it gives eBudget, and *left keeps the budget. */
static void test_d11_body_closed_side(void) {
  const Bindings *environment = NULL;
  Failure failure = {0, {NULL, 0}};
  assert(check_definitions(text("def id : (x : Nat) -> Nat := fun (x : Nat) => x\n"), &environment, &failure));
  const LType *nat;
  Tokens rest;
  Nat left = 0;
  assert(parse_type(1000, 1000, 0, environment, lexed("Nat"), &nat, &rest, &left, &failure));
  Bindings scope = {.head = check_marker(), .tail = environment};
  const Bindings *body = &scope;
  const Value *value;
  const Term *node = NULL;
  assert(parse_term(1000, 1000, 1, nat, body, lexed("(id 2)"), &value, &rest, &left, &node, &failure) && node != NULL);
  Val closed;
  assert(close_body_side(1000, 1000, body, nat, (Val){.kind = VAL_TERM, .node = node}, &closed, &left, &failure));
  assert(closed.kind == VAL_CLOSED && same_text(closed.text, text("2")) && left < 1000);
  failure = (Failure){0, {NULL, 0}};
  left = 0;
  assert(!close_body_side(1000, 1, body, nat, (Val){.kind = VAL_TERM, .node = node}, &closed, &left, &failure));
  assert(same_text(failure.message, eBudget) && left == 1);
}

/* D11 part B (design item 7): each form that print_value writes reads back
   with read_printed_value and prints to the same text. A text in another
   form gives 0. */
static void test_d11_closed_reader(void) {
  const char *good[] = {"null", "0", "4294967295", "true", "false", "\"\"",
                        "\"\\u001f\\\"\\\\\xc3\xa9\"", "[]", "[1,\"a\"]", "{}", "{\"k\":[null]}"};
  for (Nat row = 0; row < sizeof good / sizeof good[0]; row++) {
    const Value *value;
    assert(read_printed_value(text(good[row]), &value));
    assert(same_text(printed(value), text(good[row])));
  }
  const char *bad[] = {"01", "4294967296", " ", "\"\\U001f\"", "\"a", "1 2", "[1,]", "{\"k\"}", "", "\"\xff\""};
  for (Nat row = 0; row < sizeof bad / sizeof bad[0]; row++) {
    const Value *value;
    assert(!read_printed_value(text(bad[row]), &value));
  }
}

/* A closed product witness makes a computed transport motive closed, also
   in a function body. Both motive sides consume the shared work budget. */
static void test_d11_closed_transport_motive(void) {
  const char *prefix =
      "def fst : (p : Prod Nat Text) -> Nat := fun (p : Prod Nat Text) => first p\n"
      "def p : Prod Nat Text := pair 7 \"a\"\n"
      "def pf : Eq (Prod Nat Text) p p := refl\n";
  const char *body =
      "def top : Eq Nat 7 7 := transport (z : Prod Nat Text) (Eq Nat (fst z) 7) pf refl\n"
      "def f : (m : Nat) -> Eq Nat 7 7 := fun (m : Nat) => "
      "transport (z : Prod Nat Text) (Eq Nat (fst z) 7) pf refl\n"
      "def out : Eq Nat 7 7 := f 1\n";
  char source[1024];
  int size = snprintf(source, sizeof source, "%s%s", prefix, body);
  assert(size > 0 && (size_t)size < sizeof source);
  const Bindings *environment = NULL;
  Failure failure = {0};
  assert(check_definitions(text(source), &environment, &failure));

  environment = NULL;
  assert(check_definitions(text(prefix), &environment, &failure));
  Bindings scope = {.head = check_marker(), .tail = environment};
  Tokens tokens = lexed("transport (z : Prod Nat Text) (Eq Nat (fst z) 7) pf refl");
  Tokens rest;
  Typed found;
  Nat left = 0;
  assert(synth_term(1000, 3, 0, &scope, tokens, &found, &rest, &left, NULL, &failure));
  assert(rest.size == 0 && left == 1 && found.type->tag == TY_EQ);
  assert(found.type->lhs.kind == VAL_CLOSED && same_text(found.type->lhs.text, text("7")));
  assert(found.type->rhs.kind == VAL_CLOSED && same_text(found.type->rhs.text, text("7")));
  failure = (Failure){0};
  assert(!synth_term(1000, 1, 0, &scope, tokens, &found, &rest, &left, NULL, &failure));
  assert(same_text(failure.message, eBudget));
}

/* D11 part C: a failure in a declaration keeps the name of that declaration
   (design item 10). A failure outside a declaration, or after a `def` with no
   identifier, has a name of size 0. */
static void test_d11_failure_name(void) {
  const Bindings *environment = NULL;
  Failure failure = {0};
  assert(!check_definitions(text("def a : Nat := 1\ndef b : Nat := c\n"), &environment, &failure));
  assert(failure.position == 32 && same_text(failure.message, text("unknown name or constructor")));
  assert(same_text(failure.name, text("b")));

  environment = NULL;
  failure = (Failure){0};
  assert(!check_definitions(text("a : Nat := 1\n"), &environment, &failure));
  assert(failure.position == 0 && failure.name.size == 0);

  environment = NULL;
  failure = (Failure){0};
  assert(!check_definitions(text("def 1 : Nat := 1\n"), &environment, &failure));
  assert(failure.name.size == 0);
}

static Text d11_shared_values(Nat text_size, Nat levels) {
  TextBuilder payload = builder_new();
  for (Nat index = 0; index < text_size; index++) builder_push(&payload, 'x');
  Text source = append_text(text("def a0 : Values := valuesItem (valueText \""),
                            append_text(builder_text(&payload), text("\") valuesEnd\n")));
  for (Nat index = 1; index <= levels; index++) {
    Text previous = append_text(text("a"), number_text(index - 1));
    Text declaration = append_text(text("def a"), append_text(number_text(index), text(" : Values := valuesItem (valueItems ")));
    declaration = append_text(declaration, append_text(previous, append_text(text(") "), append_text(previous, text("\n")))));
    source = append_text(source, declaration);
  }
  return source;
}

static void test_d11_print_failure_name(void) {
  Text output;
  Failure failure = {0};
  Text source = text("def a : Nat := 1 def b : Attrs := attrsField (textByte 255 textEnd) valueNull attrsEnd def c : Nat := 3");
  assert(!compile_program(source, &output, &failure));
  assert(failure.position == 17 && same_text(failure.message, eUtf8));
  assert(same_text(failure.name, text("b")));

  source = d11_shared_values(100, 18);
  failure = (Failure){0};
  assert(!compile_program(source, &output, &failure));
  assert(same_text(failure.message, eOutput));
  assert(failure.name.size > 0);
  Text declaration = append_text(text("def "), append_text(failure.name, text(" :")));
  assert(same_text(text_take(text_drop(source, failure.position), declaration.size), declaration));

  /* The document needs 59138 bytes. Padding gives a budget of 59136, so
     only the final two closing bytes fail, after every instance printed. */
  source = d11_shared_values(110, 8);
  TextBuilder padding = builder_new();
  for (Nat index = 0; index < 1287; index++) builder_push(&padding, ' ');
  source = append_text(source, builder_text(&padding));
  failure = (Failure){0};
  assert(!compile_program(source, &output, &failure));
  assert(failure.position == 508 && same_text(failure.message, eOutput));
  assert(same_text(failure.name, text("a8")));
}

/* D12 part A: a one-binder type family keeps the motive form of sigma_type.
   put_marker is static, thus the transport path puts the side 1 in place of
   the binder (delta F3). */
static void test_d12_family_definition(void) {
  const Bindings *environment = NULL;
  Failure failure = {0};
  assert(check_definitions(text("def P : (x : Nat) -> Type 0 := fun (x : Nat) => Nat\n"), &environment, &failure));
  const Binding *family;
  assert(lookup(text("P"), environment, &family) && family->kind == BIND_FAMILY);
  assert(family->type->tag == TY_SIGMA && family->type->level == 0);
  assert(family->type->left->tag == TY_NAT && family->type->right->tag == TY_NAT);

  environment = NULL;
  assert(check_definitions(text("def Q : (z : Nat) -> Type 0 := fun (z : Nat) => Eq Nat z 1\n"
                                "def pf : Eq Nat 1 1 := refl\n"),
                           &environment, &failure));
  assert(lookup(text("Q"), environment, &family) && family->kind == BIND_FAMILY);
  const LType *motive;
  Tokens rest;
  Nat left = 0;
  assert(sigma_type(1000, 100, environment, NULL, lexed("(z : Nat) (Eq Nat z 1)"), &motive, &rest, &left, &failure));
  assert(rest.size == 0 && motive->tag == TY_SIGMA);
  assert(family->type->tag == motive->tag && family->type->level == motive->level);
  assert(same_type(family->type->left, motive->left) == 1 && same_type(family->type->right, motive->right) == 1);

  Bindings scope = {.head = check_marker(), .tail = environment};
  Typed found;
  assert(synth_term(1000, 100, 0, &scope, lexed("transport (z : Nat) (Eq Nat z 1) pf refl"), &found, &rest, &left,
                    NULL, &failure));
  assert(rest.size == 0 && found.type->tag == TY_EQ);
  assert(found.type->lhs.kind == VAL_CLOSED && same_text(found.type->lhs.text, text("1")));
  assert(found.type->rhs.kind == VAL_CLOSED && same_text(found.type->rhs.text, text("1")));
}

static void test_d12_parenthesized_family_body(void) {
  const char *sources[] = {
    "def P : (x : Nat) -> Type 0 := fun (z : Nat) => (Eq Nat z 1)",
    "def P : (x : Nat) -> Type 0 := fun (z : Nat) => ((Eq Nat z 1))",
    "def P : (x : Nat) -> Type 0 := fun (z : Nat) => ((Prod Nat Nat))",
  };
  for (Nat index = 0; index < sizeof sources / sizeof *sources; index++) {
    const Bindings *environment = NULL;
    Failure failure = {0};
    assert(check_definitions(text(sources[index]), &environment, &failure));
    const Binding *family;
    assert(lookup(text("P"), environment, &family) && family->kind == BIND_FAMILY);
    assert(family->type->tag == TY_SIGMA && family->type->level == 0);
    if (index < 2) {
      const LType *body = family->type->right;
      assert(body->tag == TY_EQ && body->lhs.kind == VAL_VAR && body->lhs.index == 0);
      assert(body->rhs.kind == VAL_CLOSED && same_text(body->rhs.text, text("1")));
    } else {
      assert(family->type->right->tag == TY_PROD);
    }
  }
}

/* D12 part B: family_type gives T of the family with the side for the
   binder, and uses one step of the work budget. */
static void test_d12_family_reduce(void) {
  const Bindings *environment = NULL;
  Failure failure = {0};
  assert(check_definitions(text("def P : (x : Nat) -> Type 0 := fun (x : Nat) => Nat\n"
                                "def Q : (z : Nat) -> Type 0 := fun (z : Nat) => Eq Nat z 1\n"),
                           &environment, &failure));
  const Binding *p;
  const Binding *q;
  assert(lookup(text("P"), environment, &p) && p->kind == BIND_FAMILY);
  assert(lookup(text("Q"), environment, &q) && q->kind == BIND_FAMILY);
  Val three = {.kind = VAL_CLOSED, .text = text("3")};
  Val one = {.kind = VAL_CLOSED, .text = text("1")};
  const LType *result = NULL;
  Nat left = 0;
  assert(family_type(1000, 100, environment, 7, p->type, three, &result, &left, &failure));
  assert(result->tag == TY_NAT);
  LType nat = {.tag = TY_NAT};
  LType equality = {.tag = TY_EQ, .left = &nat, .lhs = one, .rhs = one};
  assert(family_type(1000, 100, environment, 7, q->type, one, &result, &left, &failure));
  assert(result->tag == TY_EQ && same_type(result, &equality) == 1);

  left = 9;
  assert(!family_type(1000, 0, environment, 7, p->type, three, &result, &left, &failure));
  assert(failure.position == 7 && same_text(failure.message, eBudget) && left == 0);
  left = 9;
  assert(family_type(1000, 1, environment, 7, p->type, three, &result, &left, &failure));
  assert(result->tag == TY_NAT && left == 0);
}

static void test_d12_family_type_atoms(void) {
  const char *sources[] = {
    "def P : (x : Nat) -> Type 0 := fun (x : Nat) => Nat\n"
    "def v : Option P 1 := none",
    "def P : (x : Nat) -> Type 0 := fun (x : Nat) => Nat\n"
    "def v : Prod P 1 Nat := pair 2 3",
    "def P : (x : Nat) -> Type 0 := fun (x : Nat) => Nat\n"
    "def v : Prod Nat P 1 := pair 2 3",
  };
  for (size_t index = 0; index < sizeof sources / sizeof sources[0]; index++) {
    const Bindings *environment = NULL;
    Failure failure = {0};
    assert(!check_definitions(text(sources[index]), &environment, &failure));
    assert(same_text(failure.message, eParen));
    assert(failure.position == (Nat)(strstr(sources[index], "P 1") - sources[index]));
  }
  const Bindings *environment = NULL;
  Failure failure = {0};
  assert(check_definitions(text("def P : (x : Nat) -> Type 0 := fun (x : Nat) => Nat\n"
                                "def a : Option (P 1) := none\n"
                                "def b : Prod (P 1) Nat := pair 2 3\n"
                                "def c : Prod Nat (P 1) := pair 2 3\n"
                                "def f : (P : Type 0) -> (x : Option P) -> Option P := "
                                "fun (P : Type 0) (x : Option P) => x\n"),
                           &environment, &failure));
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
  test_construct_argument_lookup();
  test_refused_nodes();
  test_val_terms();
  test_val_nodes();
  test_closed_marker_nodes();
  test_d4_close();
  test_d4_carrier();
  test_d4_closed_forms();
  test_d4_option_literals();
  test_d4_normal();
  test_d4_lifts();
  test_d5_type();
  test_d5_pack();
  test_d5_neutral();
  test_d5_nested_neutral();
  test_d5_witness_types();
  test_d5_equality_carrier();
  test_d5_scope();
  test_d6_cong();
  test_d6_cong_budget();
  test_d6_cong_closed_body();
  test_d6_transport();
  test_d6_transport_scope();
  test_d7_query_param();
  test_d7_query_universe();
  test_d7_read_path();
  test_d7_type_names();
  test_d8_sides();
  test_d8_grouped_sides();
  test_d8_side_groups();
  test_d8_declared_evaluation();
  test_d8_motive();
  test_d9_side_budget();
  test_d9_parameter_budget_failure();
  test_d9_function_budget();
  test_d10_type_budget();
  test_d10_partial_type_arguments();
  test_d11_body_closed_side();
  test_d11_closed_reader();
  test_d11_closed_transport_motive();
  test_d11_failure_name();
  test_d11_print_failure_name();
  test_d12_family_definition();
  test_d12_parenthesized_family_body();
  test_d12_family_reduce();
  test_d12_family_type_atoms();
  puts("C module tests passed");
  return 0;
}
