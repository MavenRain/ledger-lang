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

/* program.c: compile_program returns 1 and writes the JSON document, or
   returns 0 and writes the failure. error_text is the JSON of a failure. */
int compile_program(Text source, Text *output, Failure *failure);
Text error_text(Nat position, Text message);

#include "literals.h"

#endif
