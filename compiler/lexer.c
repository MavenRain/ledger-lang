#include <stdio.h>
#include <stdlib.h>

#include "ledger.h"

/* The number scan stops before a value of 2^30 or more. */
#define NUMBER_PREFIX_LIMIT 107374182u

typedef struct {
  Token *items;
  Nat size;
  Nat capacity;
} TokenBuilder;

static void push_token(TokenBuilder *builder, TokenKind kind, Nat position, Nat number, Text text) {
  if (builder->size == builder->capacity) {
    Nat capacity = builder->capacity == 0 ? 256 : builder->capacity * 2;
    Token *items = realloc(builder->items, (size_t)capacity * sizeof(Token));
    if (items == NULL) {
      fputs("ledgerc: out of memory\n", stderr);
      exit(70);
    }
    builder->items = items;
    builder->capacity = capacity;
  }
  Token token = {kind, position, number, text};
  builder->items[builder->size] = token;
  builder->size += 1;
}

static Nat is_letter(Nat byte) { return between(65, 91, byte) || between(97, 123, byte) || byte == 95; }

static Nat is_digit(Nat byte) { return between(48, 58, byte); }

static Nat is_name_byte(Nat byte) { return is_letter(byte) || is_digit(byte); }

static Nat is_space(Nat byte) { return byte == 32 || byte == 9 || byte == 10 || byte == 13; }

/* Returns 1 and writes the decoded byte for a known escape. */
static int escape_byte(Nat byte, Nat *decoded) {
  switch (byte) {
    case 34: case 92: case 47: *decoded = byte; return 1;
    case 110: *decoded = 10; return 1;
    case 114: *decoded = 13; return 1;
    case 116: *decoded = 9; return 1;
    case 98: *decoded = 8; return 1;
    case 102: *decoded = 12; return 1;
    default: return 0;
  }
}

/* Scans the body of a string after its opening quote. On success, writes
   the decoded text and moves *position and *rest past the closing quote. */
static int scan_string(Nat *position, Text *rest, Text *value, Failure *failure) {
  TextBuilder done = builder_new();
  Nat at = *position;
  Text source = *rest;
  Nat escaped = 0;
  for (;;) {
    if (source.size == 0) return fail_at(failure, at, eString);
    Nat byte = source.items[0];
    if (escaped) {
      Nat decoded;
      if (!escape_byte(byte, &decoded)) return fail_at(failure, at, eEscape);
      builder_push(&done, decoded);
      escaped = 0;
      at += 1;
      source = text_tail(source);
      continue;
    }
    if (byte == 34) break;
    if (byte < 32 || byte == 127) return fail_at(failure, at, eString);
    if (byte == 92) escaped = 1;
    if (byte != 92) builder_push(&done, byte);
    at += 1;
    source = text_tail(source);
  }
  *value = builder_text(&done);
  *position = at + 1;
  *rest = text_tail(source);
  return 1;
}

/* Every token, every whitespace byte, every comment and the end of the
   source each take one unit of fuel. */
int lex(Fuel fuel, Text source, Tokens *tokens, Failure *failure) {
  TokenBuilder done = {NULL, 0, 0};
  Nat position = 0;
  Text rest = source;
  for (;;) {
    if (fuel == 0) return fail_at(failure, position, eFuel);
    fuel -= 1;
    if (rest.size == 0) {
      push_token(&done, TOKEN_PUNCTUATION, position, 0, text_end());
      Tokens result = {done.items, done.size};
      *tokens = result;
      return 1;
    }
    Nat byte = rest.items[0];
    Text after = text_tail(rest);
    Nat next = text_head(after);
    if (is_space(byte)) {
      position += 1;
      rest = after;
      continue;
    }
    if (is_letter(byte)) {
      Nat size = 0;
      while (size < rest.size && is_name_byte(rest.items[size])) size += 1;
      push_token(&done, TOKEN_IDENTIFIER, position, 0, text_take(rest, size));
      position += size;
      rest = text_drop(rest, size);
      continue;
    }
    if (is_digit(byte)) {
      Nat number = 0;
      Nat size = 0;
      while (size < rest.size && is_digit(rest.items[size])) {
        Nat digit = rest.items[size];
        int bounded = number < NUMBER_PREFIX_LIMIT || (number == NUMBER_PREFIX_LIMIT && digit < 52);
        if (!bounded) return fail_at(failure, position + size, eNumber);
        number = number * 10 + (digit - 48);
        size += 1;
      }
      Text tail = text_drop(rest, size);
      if (is_letter(text_head(tail))) return fail_at(failure, position + size, eCharacter);
      push_token(&done, TOKEN_NUMBER, position, number, text_end());
      position += size;
      rest = tail;
      continue;
    }
    if (byte == 34) {
      Nat at = position + 1;
      Text tail = after;
      Text value;
      if (!scan_string(&at, &tail, &value, failure)) return 0;
      push_token(&done, TOKEN_STRING, position, 0, value);
      position = at;
      rest = tail;
      continue;
    }
    if (byte == 45 && next == 45) {
      Nat at = position + 2;
      Text tail = text_tail(after);
      while (tail.size > 0) {
        Nat skipped = tail.items[0];
        at += 1;
        tail = text_tail(tail);
        if (skipped == 10 || skipped == 13) break;
      }
      position = at;
      rest = tail;
      continue;
    }
    if (byte == 45 && next == 62) {
      push_token(&done, TOKEN_PUNCTUATION, position, 62, text_end());
      position += 2;
      rest = text_tail(after);
      continue;
    }
    if (byte == 58 && next == 61) {
      push_token(&done, TOKEN_PUNCTUATION, position, 61, text_end());
      position += 2;
      rest = text_tail(after);
      continue;
    }
    if (byte == 58 || byte == 40 || byte == 41) {
      push_token(&done, TOKEN_PUNCTUATION, position, byte, text_end());
      position += 1;
      rest = after;
      continue;
    }
    if (byte == 61 && next == 62) {
      push_token(&done, TOKEN_PUNCTUATION, position, 63, text_end());
      position += 2;
      rest = text_tail(after);
      continue;
    }
    return fail_at(failure, position, eCharacter);
  }
}
