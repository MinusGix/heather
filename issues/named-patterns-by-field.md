---
title: Should a pattern name its fields, as a call now names its arguments?
status: open
labels: [frontend,syntax,design]
created: 2026-08-18
updated: 2026-08-18
---

Sketch. Filed by the [[named-arguments]] round, which decided calls and
deliberately did **not** decide patterns (docs/named-arguments-design.md
§10.3).

```heather
match xs {
    Cons(head, tail) => …            // today: positional binders
    Cons(head: h, tail: t) => …      // by field?
}
```

## Why it is not simply "the same feature in pattern position"

`:=` would be pointing the wrong way. A call's `f(x := e)` **fills** the slot
`x` with `e`; a pattern's `Cons(head, tail)` **binds** `head` and `tail` *from*
the fields. So the pattern form is field-to-binder, not binder-to-value, and
the natural spelling is `Cons(head: h, tail: t)` or Rust's
`Cons { head: h, tail: t }` — a different operator, with a different collision
surface, in a position (`pat_args`) that shares no code with `call_args`.

The other asymmetry: a call may omit an implicit and let inference fill it; a
pattern that omits a field has *not bound* it, which is a legal and useful
thing to say (`Cons(head: h)`, ignoring the tail) and has no analogue on the
call side, where §4.3 refuses gaps.

## Who should decide it

[[surface-records]] and this issue together, and the two spellings must agree —
which is the standing observation from `issues/named-arguments.md`'s open
question 4. A record's destructuring `let` (`docs/surface-records.md` §5) is
the third member of the same family and would inherit whatever is chosen.

Not scheduled, no live customer.

## What it assumes from elsewhere

- **[[named-arguments]]** owns the call-site spelling. Assumed here: only that
  it chose `:=` and that its reason (§3.1: `:` introduces a type in binding
  position) is about *binding* positions, which a pattern is — so the pattern
  form cannot simply reuse it without an argument.
