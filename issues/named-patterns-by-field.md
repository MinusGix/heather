---
title: Named and renamed fields in constructor and record patterns
status: closed
labels: [frontend,syntax,design,patterns,records,ergonomics]
created: 2026-08-18
updated: 2026-08-20
---

Record destructuring currently binds fields only under their declared names:

```heather
let { witness, proof } = h;
```

That is particularly awkward for an existential, where the rest of the proof
wants mathematical names such as `x` and `hx`. Admit a field-to-subpattern
mapping:

```heather
let { witness := x, proof := hx } = h;
// x  : A
// hx : P(x)
```

This is scoped existential elimination, not choice: `x` is the witness already
stored in `h`, remains local to the block, and `hx` depends on that local alias.
Nothing is synthesized and no witness escapes unless the result explicitly
packages it again.

The same named-pattern operation should be available at constructors:

```heather
match xs {
    Cons(head := h, tail := t) => ...,
    Nil => ...,
}
```

and consequently inside [[let-else-sugar]]:

```heather
if let Some(value := x) = y { ... } else { ... }
```

The final example is schematic until a real named-field constructor is the
customer; positional `Some(x)` remains the ordinary spelling.

## Syntax decision

Use `field := pattern`. The left side identifies the declared slot and the
right side is a pattern filling that slot; a binder is merely the smallest
pattern. This is the same structural reading as named call arguments, without
claiming that matching flows values in the same operational direction as a
call.

The earlier sketch proposed `field: binder` because extraction flows out of a
field. That spelling is rejected: `:` introduces a type at binding positions
throughout Heather, while `:=` already means “fill this named slot.” Treating
the right side as a subpattern also scales to `_` and nested patterns without a
second syntax:

```heather
Cons(head := _, tail := Cons(head := x))
```

The existing record shorthand remains:

```heather
{ witness, proof }
```

means the same as:

```heather
{ witness := witness, proof := proof }
```

At a constructor, the right side is the general subpattern described above.
At a record `let`, it is a binder or `_`: a constructor subpattern is
refutable, while plain `let` has no failure continuation. That form is refused
with advice to use `match` or `if let`; silently inventing failure behavior
would be a control-flow feature rather than destructuring sugar.

## Semantics and boundaries

- Field order is irrelevant; the elaborator restores declaration order before
  using the existing positional pattern machinery.
- Omitted fields are deliberately ignored, as current record destructuring
  already permits.
- Unknown and duplicate field names are errors. Binding the same local name
  twice follows the existing duplicate-pattern-binder rule.
- Dependent fields are elaborated in declaration order, not written order, so
  `proof := hx` receives a type mentioning the renamed `witness := x` even if
  the clauses were written in the opposite order.
- Record destructuring continues to lower to projections and therefore keeps
  definitional Sigma eta; constructor patterns continue through the pattern
  matrix compiler. This is syntax sharing, not a new kernel pattern form.

## Acceptance

- `let { witness := x, proof := hx } = h;` checks at an open
  `Exists(λ (x: A) => P(x))` and `hx` is usable at `P(x)`.
- Written field order does not affect dependent binding; shorthand and renamed
  forms elaborate to convertible terms.
- Partial patterns, `_`, and one nested named subpattern work.
- Unknown fields, duplicates, and a named field on a positional-only
  constructor have targeted diagnostics.
- The form composes with explicit `match` and [[let-else-sugar]].

## What it assumes from elsewhere

- **[[named-arguments]]** owns call-site `:=`. Assumed here: only the shared
  “fill a named slot” reading.
- **[[surface-records]]** owns record projection and existing shorthand
  destructuring.
- **[[nested-match-patterns]]** owns nested positional pattern compilation.

## Log

- 2026-08-18: Filed by the named-arguments round as an undecided
  `Cons(head: h, tail: t)` sketch.
- 2026-08-19: Rescoped around the first concrete customer: opening
  `Exists` as `let { witness := x, proof := hx } = h;`. Chose
  `field := pattern`; the right side is a general subpattern, which makes the
  call-site operator coherent and leaves `:` exclusively type-directed.
- 2026-08-20: Landed and closed
  (`docs/named-patterns-by-field-design.md`). Record `let` maps fields to
  renamed binders or `_`, validates and then projects in declaration order,
  so an open dependent `Exists` may be written in reverse field order while
  `hx` still checks at `P(x)`. Constructor patterns retain named wrappers only
  until `prepare_arms`: one normalizer validates field metadata, restores
  declaration order, fills omissions with `_`, and recurses through nested
  constructors before the existing pattern matrix runs. Explicit `match` and
  positional `if let` therefore share the feature without any lowering or
  kernel change. Unknown and duplicate fields, positional-only constructors,
  mixed positional/named lists, and the refutable record-`let` boundary have
  targeted controls. Seven elaboration tests; `scripts/test --fast` reported
  1966 passed, zero failed; the full `scripts/test` reported 1977 passed,
  zero failed, zero ignored.
