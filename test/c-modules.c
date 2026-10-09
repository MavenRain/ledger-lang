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
  assert(count == TERM_UNFOLD_VALUE + 1);
  for (Nat i = 0; i < count; i++) {
    assert(all[i]->tag == i);
    assert(text_size(term_text(all[i])) > 0);
    for (Nat j = 0; j < count; j++) assert(same_term(all[i], all[j]) == (i == j));
  }
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

int main(void) {
  test_runtime();
  test_lexer();
  test_json();
  test_term();
  puts("C module tests passed");
  return 0;
}
