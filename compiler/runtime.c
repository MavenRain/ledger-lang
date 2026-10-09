#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "ledger.h"

#define ARENA_CHUNK ((size_t)1 << 24)

static unsigned char *arena_next;
static size_t arena_left;

static void out_of_memory(void) {
  fputs("ledgerc: out of memory\n", stderr);
  exit(70);
}

void *arena_alloc(size_t size) {
  size_t rounded = (size + 15u) & ~(size_t)15u;
  if (rounded > arena_left) {
    size_t chunk = rounded > ARENA_CHUNK ? rounded : ARENA_CHUNK;
    arena_next = malloc(chunk);
    if (arena_next == NULL) out_of_memory();
    arena_left = chunk;
  }
  void *result = arena_next;
  arena_next += rounded;
  arena_left -= rounded;
  return result;
}

TextBuilder builder_new(void) {
  TextBuilder builder = {NULL, 0, 0};
  return builder;
}

void builder_push(TextBuilder *builder, Nat item) {
  if (builder->size == builder->capacity) {
    Nat capacity = builder->capacity == 0 ? 64 : builder->capacity * 2;
    Nat *items = realloc(builder->items, (size_t)capacity * sizeof(Nat));
    if (items == NULL) out_of_memory();
    builder->items = items;
    builder->capacity = capacity;
  }
  builder->items[builder->size] = item;
  builder->size += 1;
}

void builder_append(TextBuilder *builder, Text text) {
  for (Nat index = 0; index < text.size; index++) builder_push(builder, text.items[index]);
}

Text builder_text(const TextBuilder *builder) {
  Text text = {builder->items, builder->size};
  return text;
}

int fail_at(Failure *failure, Nat position, Text message) {
  failure->position = position;
  failure->message = message;
  return 0;
}

Nat between(Nat lo, Nat hi, Nat x) { return x >= lo && x < hi; }

Nat nat_sub(Nat a, Nat b) { return a > b ? a - b : 0; }

static Text text_alloc(Nat size, Nat **items) {
  *items = arena_alloc((size_t)size * sizeof(Nat));
  Text text = {*items, size};
  return text;
}

Text text_end(void) {
  Text text = {NULL, 0};
  return text;
}

Text text_of_bytes(const unsigned char *bytes, size_t size) {
  Nat *items;
  Text text = text_alloc((Nat)size, &items);
  for (size_t index = 0; index < size; index++) items[index] = bytes[index];
  return text;
}

Text text_one(Nat item) {
  Nat *items;
  Text text = text_alloc(1, &items);
  items[0] = item;
  return text;
}

Text text_byte(Nat item, Text rest) {
  Nat *items;
  Text text = text_alloc(rest.size + 1, &items);
  items[0] = item;
  if (rest.size > 0) memcpy(items + 1, rest.items, (size_t)rest.size * sizeof(Nat));
  return text;
}

Nat text_is_end(Text text) { return text.size == 0; }

Nat text_head(Text text) { return text.size == 0 ? 0 : text.items[0]; }

Text text_tail(Text text) { return text_drop(text, 1); }

Text text_take(Text text, Nat count) {
  Text taken = {text.items, count < text.size ? count : text.size};
  return taken;
}

Text text_drop(Text text, Nat count) {
  Nat dropped = count < text.size ? count : text.size;
  Text rest = {text.size == dropped ? NULL : text.items + dropped, text.size - dropped};
  return rest;
}

Text reverse_text(Text text) {
  Nat *items;
  Text reversed = text_alloc(text.size, &items);
  for (Nat index = 0; index < text.size; index++) items[index] = text.items[text.size - 1 - index];
  return reversed;
}

Text append_text(Text a, Text b) {
  if (a.size == 0) return b;
  if (b.size == 0) return a;
  Nat *items;
  Text text = text_alloc(a.size + b.size, &items);
  memcpy(items, a.items, (size_t)a.size * sizeof(Nat));
  memcpy(items + a.size, b.items, (size_t)b.size * sizeof(Nat));
  return text;
}

Nat same_text(Text a, Text b) {
  if (a.size != b.size) return 0;
  if (a.size == 0) return 1;
  return memcmp(a.items, b.items, (size_t)a.size * sizeof(Nat)) == 0;
}

Nat text_size(Text text) { return text.size; }

Fuel fuel_for(Text text) { return (Fuel)text.size + 1; }

/* The state keeps the number and bounds of the continuation bytes that
   remain, and the offset of the lead byte of the current sequence. */
int utf8_error(Text text, Nat *position) {
  Nat lead = 0;
  Nat pending = 0;
  Nat lo = 128;
  Nat hi = 192;
  for (Nat at = 0; at < text.size; at++) {
    Nat byte = text.items[at];
    if (pending != 0) {
      if (!between(lo, hi, byte)) {
        *position = at;
        return 1;
      }
      pending -= 1;
      lo = 128;
      hi = 192;
      continue;
    }
    lead = at;
    lo = 128;
    hi = 192;
    if (byte < 128) continue;
    if (between(194, 224, byte)) {
      pending = 1;
      continue;
    }
    if (between(224, 240, byte)) {
      pending = 2;
      lo = byte == 224 ? 160 : 128;
      hi = byte == 237 ? 160 : 192;
      continue;
    }
    if (between(240, 245, byte)) {
      pending = 3;
      lo = byte == 240 ? 144 : 128;
      hi = byte == 244 ? 144 : 192;
      continue;
    }
    *position = at;
    return 1;
  }
  if (pending == 0) return 0;
  *position = lead;
  return 1;
}

Nat valid_utf8(Text text) {
  Nat position;
  return !utf8_error(text, &position);
}

/* A marker is an identifier that no source can spell: item 0, then the
   position of a value parameter. */
Text marker_name(Nat index) { return text_byte(0, text_one(index)); }

int marker_index(Text name, Nat *index) {
  if (name.size < 2 || name.items[0] != 0) return 0;
  *index = name.items[1];
  return 1;
}

/* The text of a token without its source position. Each token starts with
   its kind and the size of its text, so the text of a token list is
   injective. */
Text token_text(Token token) {
  switch (token.kind) {
    case TOKEN_IDENTIFIER: return text_byte(2, text_byte(token.text.size, token.text));
    case TOKEN_NUMBER: return text_byte(3, text_one(token.number));
    case TOKEN_STRING: return text_byte(4, text_byte(token.text.size, token.text));
    case TOKEN_PUNCTUATION: return text_byte(5, text_one(token.number));
  }
  return text_end();
}

Text tokens_text(Tokens tokens) {
  TextBuilder builder = builder_new();
  for (Nat index = 0; index < tokens.size; index++) builder_append(&builder, token_text(tokens.items[index]));
  return builder_text(&builder);
}

Nat has_marker(Tokens tokens) {
  Nat index;
  for (Nat at = 0; at < tokens.size; at++) {
    if (tokens.items[at].kind == TOKEN_IDENTIFIER && marker_index(tokens.items[at].text, &index)) return 1;
  }
  return 0;
}

Nat token_position(Token token) { return token.position; }

Nat first_position(Tokens tokens) { return tokens.size == 0 ? 0 : tokens.items[0].position; }

Nat same_val(Val left, Val right) {
  if (left.kind != right.kind) return 0;
  switch (left.kind) {
    case VAL_CLOSED: return same_text(left.text, right.text);
    case VAL_VAR: return left.index == right.index;
    case VAL_TERM: return same_text(tokens_text(left.term), tokens_text(right.term));
  }
  return 0;
}

/* A neutral side prints as item 0, then its position. A computed side
   prints as item 1, then its tokens. Neither equals the JSON text of a
   closed side. */
Text val_text(Val side) {
  switch (side.kind) {
    case VAL_CLOSED: return side.text;
    case VAL_VAR: return text_byte(0, text_one(side.index));
    case VAL_TERM: return text_byte(1, tokens_text(side.term));
  }
  return text_end();
}

Nat has_field(Text key, const Attrs *attrs) {
  for (const Attrs *field = attrs; field != NULL; field = field->rest) {
    if (same_text(key, field->key)) return 1;
  }
  return 0;
}

Text text_of_cstring(const char *bytes) {
  return text_of_bytes((const unsigned char *)bytes, strlen(bytes));
}

/* Texts of the schema and operation modules (see ledger.h). */
Text sHash(void) { return text_of_cstring("Hash"); }
Text sRef(void) { return text_of_cstring("Ref"); }
Text sHashOf(void) { return text_of_cstring("hashOf"); }
Text sRefTo(void) { return text_of_cstring("refTo"); }
Text opsTextQuery(void) { return text_of_cstring("Query"); }
Text eQueryIndex(void) { return text_of_cstring("this constructor gives a Query of another answer type"); }
Text kRefKind(void) { return text_of_cstring("kind"); }
Text kRefHash(void) { return text_of_cstring("hash"); }
Text kSchemaTag(void) { return text_of_cstring("tag"); }
Text eIndex(void) { return text_of_cstring("expected Kind index"); }
Text eLaterType(void) { return text_of_cstring("this type belongs to a later milestone"); }
Text opsTextWritePath(void) { return text_of_cstring("WritePath"); }

int lookup(Text name, const Bindings *environment, const Binding **found) {
  for (; environment != NULL; environment = environment->tail) {
    if (same_text(name, environment->head.name) == 1) {
      *found = &environment->head;
      return 1;
    }
  }
  return 0;
}
