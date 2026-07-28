---
title: `@` and type parameters collide: every explicit call breaks when a callee generalizes
status: closed
labels: [frontend,elaboration,design]
created: 2026-07-26
updated: 2026-07-27
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
- 2026-07-26: IMPLEMENTED as recommended: '@' and '<...>' are orthogonal knobs. Parser un-rejects '@f<T, ...>(...)'; the named-call path narrows the mask under '@' (keep the is_type entries, clear the rest) instead of jumping to apply_explicit; a self-call never passes type parameters, under '@' or not (SelfRef gained n_tyvars). Two consequences neither the issue nor docs/surface-polymorphism.md section 5 predicted. (1) The 'expression read as a type at Ty l' coercion is now DEAD -- no position has that expected type any more -- so it was retired to a diagnostic; it had existed only to paper over this collision. (2) apply_implicit had to gain a CHECKING mode: '@sym(a, b, ?p)' now routes through it, and it inferred every explicit argument, so refl / ?-holes / vector literals lost their expected type. It now checks against the domain zonked with the solutions so far and infers only while metas remain unsolved -- 'a' solves the carrier before 'p's domain is needed. That is an improvement to implicit application generally. The prelude is now polymorphic (sym<A>, trans<A>); cong_succ stays monomorphic, since a general cong needs its function argument explicit. Workspace 466 green, no test edits beyond the two that pinned the old '@' spelling.
- 2026-07-27: Follow-on sketched as [[named-arguments]]: '@' and '<...>' are both all-or-nothing positional overrides, and a named-argument form would subsume them with finer grain -- including letting the calc desugaring name only the endpoints it cares about instead of emitting a fully-explicit @trans.
- 2026-07-27: The claim at line 82 that 'cong cannot generalize with f implicit' stands as a fact about today, but its reason is superseded by [[congruence-by-anti-unification]]: f is not recoverable from the proof, which is what that line says, but it IS recoverable from the expected type by anti-unification. The explicit-f spelling this issue recommends stays right regardless -- the tactic's output is a call to that same explicit-f declaration.
