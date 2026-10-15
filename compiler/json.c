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

/* D11 part B (design item 7): the reader of the canonical JSON text of a
   closed side. It accepts only the forms that print_value writes, thus a
   value that it reads prints back to the same text. */
typedef struct {
  Text text;
  Nat at;
} JsonReader;

static const Value *make_value(Value value) {
  Value *made = arena_alloc(sizeof *made);
  *made = value;
  return made;
}

static const Values *values_item(const Value *head, const Values *tail) {
  Values *item = arena_alloc(sizeof *item);
  *item = (Values){head, tail};
  return item;
}

static const Attrs *attrs_field(Text key, const Value *value, const Attrs *rest) {
  Attrs *field = arena_alloc(sizeof *field);
  *field = (Attrs){key, value, rest};
  return field;
}

static int succeed(const Value **slot, const Value *value) {
  *slot = value;
  return 1;
}

/* 1 when the next byte is byte. */
static Nat json_next(const JsonReader *reader, Nat byte) {
  return reader->at < reader->text.size && reader->text.items[reader->at] == byte;
}

/* Reads byte when it is next. */
static int json_byte(JsonReader *reader, Nat byte) {
  if (!json_next(reader, byte)) return 0;
  reader->at += 1;
  return 1;
}

/* Reads literal (null, true or false) when it is next. */
static int json_literal(JsonReader *reader, Text literal) {
  if (literal.size > reader->text.size - reader->at) return 0;
  for (Nat index = 0; index < literal.size; index++)
    if (reader->text.items[reader->at + index] != literal.items[index]) return 0;
  reader->at += literal.size;
  return 1;
}

/* The value of a hex digit that hex_byte writes (lower case), else 16. */
static Nat json_hex(Nat byte) {
  if (byte >= 48 && byte <= 57) return byte - 48;
  if (byte >= 97 && byte <= 102) return byte - 87;
  return 16;
}

/* The size of the escape at items (rest items remain), else 0: a quote or
   a backslash after a backslash (2), or \u00 and two hex digits for a byte
   below 32 (6), as emit_quoted_byte writes them. */
static Nat json_escape(const Nat *items, Nat rest) {
  if (rest >= 2 && (items[1] == 34 || items[1] == 92)) return 2;
  if (rest < 6 || items[1] != 117 || items[2] != 48 || items[3] != 48) return 0;
  return json_hex(items[4]) < 2 && json_hex(items[5]) < 16 ? 6 : 0;
}

/* One string byte. A byte from 32 to 255 that is not a backslash is itself.
   A backslash starts an escape. The caller stops at the closing quote. */
static int json_string_byte(JsonReader *reader, Nat *byte) {
  const Nat *items = reader->text.items + reader->at;
  Nat size = items[0] == 92 ? json_escape(items, reader->text.size - reader->at) : items[0] >= 32 && items[0] <= 255;
  if (size == 0) return 0;
  if (size == 6) *byte = json_hex(items[4]) * 16 + json_hex(items[5]);
  if (size != 6) *byte = items[size - 1];
  reader->at += size;
  return 1;
}

/* A string in the form of quoted. The bytes must be UTF-8. */
static int json_string(JsonReader *reader, Text *text) {
  if (!json_byte(reader, 34)) return 0;
  TextBuilder bytes = builder_new();
  while (reader->at < reader->text.size && !json_next(reader, 34)) {
    Nat byte;
    if (!json_string_byte(reader, &byte)) return 0;
    builder_push(&bytes, byte);
  }
  if (!json_byte(reader, 34)) return 0;
  *text = builder_text(&bytes);
  return valid_utf8(*text) != 0;
}

/* A number in the form of number_text: digits with no leading zero, not
   more than the largest Nat. */
static int json_number(JsonReader *reader, const Value **value) {
  Nat start = reader->at;
  Nat number = 0;
  while (reader->at < reader->text.size && reader->text.items[reader->at] >= 48 &&
         reader->text.items[reader->at] <= 57) {
    Nat digit = reader->text.items[reader->at] - 48;
    if (number > (UINT32_MAX - digit) / 10) return 0;
    number = number * 10 + digit;
    reader->at += 1;
  }
  if (reader->at == start) return 0;
  if (reader->text.items[start] == 48 && reader->at - start > 1) return 0;
  return succeed(value, make_value((Value){.kind = VALUE_NAT, .number = number}));
}

static int json_value_at(Fuel fuel, JsonReader *reader, const Value **value);

/* The items after [, in the form of print_values. */
static int json_items(Fuel fuel, JsonReader *reader, const Value **value) {
  const Values *reversed = NULL;
  for (Nat first = 1; !json_byte(reader, 93); first = 0) {
    const Value *item;
    if (!first && !json_byte(reader, 44)) return 0;
    if (!json_value_at(fuel, reader, &item)) return 0;
    reversed = values_item(item, reversed);
  }
  const Values *items = NULL;
  for (const Values *item = reversed; item != NULL; item = item->tail) items = values_item(item->head, items);
  return succeed(value, make_value((Value){.kind = VALUE_ITEMS, .items = items}));
}

/* The fields after {, in the form of print_attrs. */
static int json_attrs(Fuel fuel, JsonReader *reader, const Value **value) {
  const Attrs *reversed = NULL;
  for (Nat first = 1; !json_byte(reader, 125); first = 0) {
    Text key;
    const Value *field;
    if (!first && !json_byte(reader, 44)) return 0;
    if (!json_string(reader, &key) || !json_byte(reader, 58) || !json_value_at(fuel, reader, &field)) return 0;
    reversed = attrs_field(key, field, reversed);
  }
  const Attrs *attrs = NULL;
  for (const Attrs *field = reversed; field != NULL; field = field->rest)
    attrs = attrs_field(field->key, field->value, attrs);
  return succeed(value, make_value((Value){.kind = VALUE_ATTRS, .attrs = attrs}));
}

/* One value. Each [ or { level takes one unit of fuel. */
static int json_value_at(Fuel fuel, JsonReader *reader, const Value **value) {
  if (fuel == 0) return 0;
  Text text;
  if (json_literal(reader, jNull)) return succeed(value, make_value((Value){.kind = VALUE_NULL}));
  if (json_literal(reader, jTrue)) return succeed(value, make_value((Value){.kind = VALUE_FLAG, .flag = FLAG_YES}));
  if (json_literal(reader, jFalse)) return succeed(value, make_value((Value){.kind = VALUE_FLAG, .flag = FLAG_NO}));
  if (json_byte(reader, 91)) return json_items(fuel - 1, reader, value);
  if (json_byte(reader, 123)) return json_attrs(fuel - 1, reader, value);
  if (!json_next(reader, 34)) return json_number(reader, value);
  return json_string(reader, &text) && succeed(value, make_value((Value){.kind = VALUE_TEXT, .text = text}));
}

/* The depth is at most the size of the text (fuel_for). The answer is 1
   only when the whole text is one value. */
int read_printed_value(Text text, const Value **value) {
  JsonReader reader = {text, 0};
  return json_value_at(fuel_for(text), &reader, value) && reader.at == text.size;
}
