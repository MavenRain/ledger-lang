/* Checked constructor evaluation uses the schema's own JSON value family.
   Port of evaluate.mech (hand-written, no fuel). A List Value is a Values
   list here, and a missing argument is null. */
#include "ledger.h"

static const Value null_value = {.kind = VALUE_NULL};

static const Value *make_value(Value value) {
  Value *made = arena_alloc(sizeof *made);
  *made = value;
  return made;
}

static const Value *text_value(Text text) { return make_value((Value){.kind = VALUE_TEXT, .text = text}); }
static const Value *flag_value(Flag flag) { return make_value((Value){.kind = VALUE_FLAG, .flag = flag}); }
static const Value *items_value(const Values *items) { return make_value((Value){.kind = VALUE_ITEMS, .items = items}); }
static const Value *attrs_value(const Attrs *attrs) { return make_value((Value){.kind = VALUE_ATTRS, .attrs = attrs}); }

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

const Value *argument_head(const Values *args) { return args == NULL ? &null_value : args->head; }
const Values *argument_tail(const Values *args) { return args == NULL ? NULL : args->tail; }
const Value *argument_second(const Values *args) { return argument_head(argument_tail(args)); }
const Value *argument_third(const Values *args) { return argument_head(argument_tail(argument_tail(args))); }

const Value *object_one(Text key, const Value *value) { return attrs_value(attrs_field(key, value, NULL)); }

const Value *object_two(Text a, const Value *x, Text b, const Value *y) {
  return attrs_value(attrs_field(a, x, attrs_field(b, y, NULL)));
}

int as_nat(const Value *value, Nat *number) {
  switch (value->kind) {
  case VALUE_NAT: *number = value->number; return 1;
  case VALUE_NULL: case VALUE_FLAG: case VALUE_TEXT: case VALUE_ITEMS: case VALUE_ATTRS: return 0;
  }
  return 0;
}

int as_text(const Value *value, Text *text) {
  switch (value->kind) {
  case VALUE_TEXT: *text = value->text; return 1;
  case VALUE_NULL: case VALUE_FLAG: case VALUE_NAT: case VALUE_ITEMS: case VALUE_ATTRS: return 0;
  }
  return 0;
}

int as_values(const Value *value, const Values **items) {
  switch (value->kind) {
  case VALUE_ITEMS: *items = value->items; return 1;
  case VALUE_NULL: case VALUE_FLAG: case VALUE_NAT: case VALUE_TEXT: case VALUE_ATTRS: return 0;
  }
  return 0;
}

int as_attrs(const Value *value, const Attrs **attrs) {
  switch (value->kind) {
  case VALUE_ATTRS: *attrs = value->attrs; return 1;
  case VALUE_NULL: case VALUE_FLAG: case VALUE_NAT: case VALUE_TEXT: case VALUE_ITEMS: return 0;
  }
  return 0;
}

int build_byte(const Values *args, const Value **value, Failure *failure) {
  Nat byte;
  Text rest;
  if (!as_nat(argument_head(args), &byte)) return fail_at(failure, 0, eTerm);
  if (!as_text(argument_second(args), &rest)) return fail_at(failure, 0, eTerm);
  if (byte >= 256) return fail_at(failure, 0, eByte);
  return succeed(value, text_value(text_byte(byte, rest)));
}

int build_prepend(const Values *args, const Value **value, Failure *failure) {
  const Values *rest;
  if (!as_values(argument_second(args), &rest)) return fail_at(failure, 0, eTerm);
  return succeed(value, items_value(values_item(argument_head(args), rest)));
}

int build_field(const Values *args, const Value **value, Failure *failure) {
  Text name;
  const Attrs *rest;
  if (!as_text(argument_head(args), &name)) return fail_at(failure, 0, eTerm);
  if (!as_attrs(argument_third(args), &rest)) return fail_at(failure, 0, eTerm);
  if (has_field(name, rest)) return fail_at(failure, 0, eField);
  return succeed(value, attrs_value(attrs_field(name, argument_second(args), rest)));
}

int apply_plan(Nat mode, Text label, const Values *args, const Value **value, Failure *failure) {
  switch (mode) {
  case 0: return succeed(value, &null_value);
  case 1: return succeed(value, flag_value(FLAG_NO));
  case 2: return succeed(value, flag_value(FLAG_YES));
  case 3: return succeed(value, text_value(text_end()));
  case 4: return build_byte(args, value, failure);
  case 5: return succeed(value, argument_head(args));
  case 6: return succeed(value, items_value(NULL));
  case 7: return build_prepend(args, value, failure);
  case 8: return succeed(value, attrs_value(NULL));
  case 9: return build_field(args, value, failure);
  case 10: return succeed(value, object_two(kFirst, argument_head(args), kSecond, argument_second(args)));
  case 11: return succeed(value, object_one(kInl, argument_head(args)));
  case 12: return succeed(value, object_one(kInr, argument_head(args)));
  case 13: return succeed(value, object_one(kSome, argument_head(args)));
  case 14: return succeed(value, text_value(label));
  case 15: return succeed(value, object_two(kRefKind(), text_value(label), kRefHash(), argument_head(args)));
  default: return fail_at(failure, 0, eTerm);
  }
}

int record_fields(const Texts *fields, const Values *values, const Attrs **attrs, Failure *failure) {
  const Attrs *remaining;
  if (fields == NULL && values == NULL) {
    *attrs = NULL;
    return 1;
  }
  if (fields == NULL || values == NULL) return fail_at(failure, 0, eTerm);
  if (!record_fields(fields->tail, values->tail, &remaining, failure)) return 0;
  *attrs = attrs_field(fields->head, values->head, remaining);
  return 1;
}

int evaluate_plan(const Plan *selected, const Values *values, const Value **value, Failure *failure) {
  const Attrs *attrs;
  switch (selected->kind) {
  case PLAN_TAG: return apply_plan(selected->mode, selected->label, values, value, failure);
  case PLAN_RECORD:
    if (!record_fields(selected->fields, values, &attrs, failure)) return 0;
    return succeed(value, attrs_value(selected->has_tag
      ? attrs_field(kSchemaTag(), text_value(selected->tag), attrs) : attrs));
  }
  return 0;
}
