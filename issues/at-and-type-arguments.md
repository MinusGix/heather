---
title: `@` and type parameters collide: every explicit call breaks when a callee generalizes
status: open
labels: [frontend,elaboration,design]
created: 2026-07-26
updated: 2026-07-26
---

Generalizing a declaration — adding `<A>` to a `theorem` that had none — is
**not** a backwards-compatible change today, and the reason is entirely
`@`. Found by the prelude probe (2026-07-26): swapping `sym`/`trans` in
`crates/elab/src/prelude.hthr` for their polymorphic versions and running the
workspace gives

```
450 passed, 16 failed
```

and **all 16 failures are `@`-spelled calls or `calc`** (which desugars to
`@trans`, `parser.rs`'s `calc_expr`). Not one implicit use broke. The single
failing test in `implicit_args.rs` is the one named
`explicit_override_still_available`.

The messages are all one of two:

```
unknown type `a`
this argument fills a type parameter, so it has to be a type: …
```

because `@f(a, b, p)` means *every* parameter positional, a type parameter is
now the first one, and `a` is therefore read as a type.

## Why this matters more than the prelude

It is a general property, not a prelude quirk: **any** library declaration
that later gains a type parameter breaks **every** `@`-call to it, silently
at the call sites rather than at the declaration. That is a bad property for
a language whose whole round-two direction is "fewer special features in the
elaborator, more fundamental features in the language" —
[[surface-records]]'s generic operations will hit it immediately.

## The recommendation: `@` and `<…>` are orthogonal knobs

Today they are two points on one axis:

| spelling | type parameters | value implicits |
|---|---|---|
| `f(a, b)` | inferred | inferred |
| `f<T>(a, b)` | **written** | inferred |
| `@f(a, b)` | positional | positional |
| `@f<T>(a, b)` | *rejected by the parser* | — |

Proposed instead: `<…>` controls **type** arguments, `@` controls **value**
implicits, and they compose.

| spelling | type parameters | value implicits |
|---|---|---|
| `f(a, b)` | inferred | inferred |
| `f<T>(a, b)` | written | inferred |
| `@f(a, b)` | **inferred** | positional |
| `@f<T>(a, b)` | written | positional |

Consequences:

- `@sym(a, b, p)` keeps working verbatim when `sym` generalizes, and so does
  `calc`. The 16 failures go to zero with no test edits.
- `@f<T>(a, b)` becomes the fully-explicit form. That means **un-rejecting**
  `@f<…>` in the parser, which [[surface-polymorphism]] added a targeted
  error for — a decision to reverse, recorded here rather than quietly.
- It also fixes a gap that round shipped: there is currently **no spelling**
  for "give the type argument *and* the endpoints positionally".
  `psym<Nat>(n, m, p)` today says "`psym` is applied to too many arguments",
  because `f<T>(…)` leaves the remaining implicits inferred.

Cost: small. `apply_implicit` already takes a mask; `@` becomes "mask with
the `is_type` entries kept and the rest cleared" instead of a jump to
`apply_explicit`, and the parser stops rejecting `@f<…>`.

## What the probe found that this does *not* fix

`cong` cannot generalize with `f` implicit — `theorem cong<A, B>({f: A -> B},
{a: A}, {b: A}, p: a = b)` declares and kernel-checks, but `cong(p)` cannot
solve `f`, since `p`'s type mentions `a` and `b` and not `f`. Higher-order;
[[elab-unifier-completeness]].

**But it generalizes fine with `f` explicit**, and that spelling is usable
today:

```heather
theorem cong<A, B>(f: A -> B, {a: A}, {b: A}, p: a = b): f(a) = f(b) {
    j(p, (y, q) -> f(a) = f(y), refl)
}
// and `cong(Succ, p)` checks — `Succ` is a function value since
// [[constructors-as-function-values]].
```

So a polymorphic prelude is reachable in full, with `cong(f, p)` replacing
`cong_succ(p)`, once `@` stops colliding.

## Log

- 2026-07-26: Filed from the [[surface-polymorphism]] prelude probe. Probe
  result in full: polymorphic `sym`/`trans` declare, kernel-check, and are
  used with inference at `Nat` and at a declared `Bool` (`psym(p)`), through
  the method sugar (`p.psym()`), and in a `trans` chain — all green. Every
  failure in the workspace swap was `@` or `calc`. Recommendation above is to
  make `@` and `<…>` orthogonal; not implemented, because it changes shipped
  surface semantics and reverses a decision that round made deliberately.
