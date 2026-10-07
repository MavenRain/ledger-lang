#include "ledger.h"

static const Nat decimal_places[] = {
  1000000000u, 100000000u, 10000000u, 1000000u, 100000u, 10000u, 1000u, 100u, 10u, 1u
};

/* One place takes at most ten subtractions, as with the fuel of ten in the
   old compiler. A larger quotient prints as the item 58. */
static Nat divide_digit(Nat *number, Nat place) {
  Nat digit = 0;
  while (digit < 10 && *number >= place) {
    *number -= place;
    digit += 1;
  }
  return digit;
}

Text number_text(Nat number) {
  TextBuilder done = builder_new();
  Nat remaining = number;
  Nat started = 0;
  for (Nat index = 0; index < 10; index++) {
    Nat place = decimal_places[index];
    Nat digit = divide_digit(&remaining, place);
    if (started || digit != 0 || place == 1) builder_push(&done, 48 + digit);
    started = started || digit != 0;
  }
  return builder_text(&done);
}

static Nat hex_byte(Nat digit) { return digit < 10 ? 48 + digit : 87 + digit; }

Text separator(Nat first) { return first ? text_end() : text_one(44); }

/* Every emitted output item takes one unit of the output budget. */
int emit_text(Printer *printer, Text text, Failure *failure) {
  for (Nat index = 0; index < text.size; index++) {
    if (printer->fuel == 0) return fail_at(failure, 0, eOutput);
    printer->fuel -= 1;
    builder_push(&printer->output, text.items[index]);
  }
  return 1;
}

/* The JSON form of one string byte, in output order. */
static int emit_quoted_byte(Printer *printer, Nat byte, Failure *failure) {
  Nat items[6];
  Text text = {items, 0};
  if (byte < 32) {
    items[0] = 92;
    items[1] = 117;
    items[2] = 48;
    items[3] = 48;
    items[4] = hex_byte(byte / 16);
    items[5] = hex_byte(byte % 16);
    text.size = 6;
    return emit_text(printer, text, failure);
  }
  if (byte == 34 || byte == 92) {
    items[0] = 92;
    items[1] = byte;
    text.size = 2;
    return emit_text(printer, text, failure);
  }
  items[0] = byte;
  text.size = 1;
  return emit_text(printer, text, failure);
}

int quote_bytes(Printer *printer, Text text, Failure *failure) {
  for (Nat index = 0; index < text.size; index++) {
    if (!emit_quoted_byte(printer, text.items[index], failure)) return 0;
  }
  return emit_text(printer, text_one(34), failure);
}

int quoted(Printer *printer, Text text, Failure *failure) {
  if (!valid_utf8(text)) return fail_at(failure, 0, eUtf8);
  return emit_text(printer, text_one(34), failure) && quote_bytes(printer, text, failure);
}

static int print_values(Printer *printer, const Values *values, Failure *failure) {
  Nat first = 1;
  for (const Values *item = values; item != NULL; item = item->tail) {
    if (!emit_text(printer, separator(first), failure)) return 0;
    if (!print_value(printer, item->head, failure)) return 0;
    first = 0;
  }
  return emit_text(printer, text_one(93), failure);
}

static int print_attrs(Printer *printer, const Attrs *attrs, Failure *failure) {
  Nat first = 1;
  for (const Attrs *field = attrs; field != NULL; field = field->rest) {
    if (!emit_text(printer, separator(first), failure)) return 0;
    if (!quoted(printer, field->key, failure)) return 0;
    if (!emit_text(printer, text_one(58), failure)) return 0;
    if (!print_value(printer, field->value, failure)) return 0;
    first = 0;
  }
  return emit_text(printer, text_one(125), failure);
}

/* Remaining fuel is threaded through sequential children, so the budget
   bounds the total output, shared values included. */
int print_value(Printer *printer, const Value *value, Failure *failure) {
  switch (value->kind) {
    case VALUE_NULL: return emit_text(printer, jNull, failure);
    case VALUE_NAT: return emit_text(printer, number_text(value->number), failure);
    case VALUE_FLAG: return emit_text(printer, value->flag == FLAG_YES ? jTrue : jFalse, failure);
    case VALUE_TEXT: return quoted(printer, value->text, failure);
    case VALUE_ITEMS: return emit_text(printer, text_one(91), failure) && print_values(printer, value->items, failure);
    case VALUE_ATTRS: return emit_text(printer, text_one(123), failure) && print_attrs(printer, value->attrs, failure);
  }
  return 0;
}
