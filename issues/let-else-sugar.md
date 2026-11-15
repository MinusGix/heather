---
title: "if let: one-pattern dependent match with equation evidence"
status: closed
labels: [frontend,syntax,elaboration,patterns,design]
created: 2026-08-05
updated: 2026-08-19
---

The one-interesting-pattern case should not require spelling a complete
constructor match:

```heather
if let Some(x) = y {
    use(x)
} else {
    fallback
}
```

When rewriting or an indexed result needs the connection to the original
scrutinee, the equation has a name in the same position as decidable `if h : P`
and `match h : e`:

```heather
if let hy : Some(x) = y {
    // x and the constructor equation are in scope
    ...
} else {
    ...
}
```

The `with h` spelling previously sketched here is rejected: `with` would be a
context-specific noise word for an operation the other branching forms already
express by putting the evidence name before `:`.

## Meaning

V1 is a one-row pattern matrix plus a default row:

```heather
match y {
    Some(x) => yes,
    _ => no,
}
```

It should lower onto the existing `ExprKind::Match`, as `split` and decidable
`if` do, and reuse the nested-pattern compiler. The braces are ordinary block
expressions. `else` is required: a refutable pattern never silently invents a
result for the remaining constructors.

This is more than Rust-style field extraction in a dependent language. The
success arm receives constructor fields and the refinements ordinary matching
provides. When requested, it also receives an equation connecting the original
scrutinee to the constructor-shaped value, so a goal mentioning `y` can be
rewritten rather than reconstructed around `x`.

### Equation orientation

The surface `=` is the pattern/scrutinee separator. The named equation follows
the existing equation-bearing-match convention and has type `y = Some(x)`:
original scrutinee to constructor-shaped arm value. This makes every
equation-bearing split uniform and preserves the direction that removed a real
`sym` at [[match-with-equation]]'s original consumer. The broader question of
making routine equality consumers less sensitive to orientation is recorded in
[[equality-orientation-ergonomics]], without changing this stable convention.

## Dependent and indexed boundary

Without `hy`, indexed inductives should receive exactly the refinements an
ordinary match already supplies. Equation evidence inherits the existing
homogeneous-identity boundary: `match h : e` currently refuses indexed/forded
families when constructor indices make the equation heterogeneous. V1 may
therefore accept the unbound form at an indexed family while refusing the
equation-binding form with the established explanation. A stronger inversion
principle is a separate feature, not a fake homogeneous equality.

## Not V1

The failure branch eventually wants negative match evidence, but it is not
merely the negation of one constructor equation when fields are existential or
patterns are nested. [[if-let-negative-evidence]] owns that proposition and
its syntax. V1's `else` branch binds no extra evidence.

`let pattern = e else ...`, early return, `?` propagation, and branchless
irrefutable `let pattern = e;` are related but separate scope/control-flow
questions. This issue owns the expression-valued two-branch form above.

## Acceptance

- Both displayed forms lower to the same ordinary match as their explicit
  spellings and compute for `Option` in both branches.
- Constructor fields, ignored fields, and nested patterns reuse the existing
  pattern compiler; constructor diagnostics name the written `if let`.
- The named form has a pinned equation direction and closes a proof whose goal
  mentions the original scrutinee.
- Constant-result inference, dependent checking, local branch blocks, and an
  `if let` nested inside another expression work.
- An indexed-family probe pins the boundary above rather than inheriting it by
  accident.

## What it assumes from elsewhere

- **[[match-with-equation]]** owns the existing match equation and its
  homogeneous-identity restriction. Assumed here: only its lowering can be
  reused.
- **[[nested-match-patterns]]** owns pattern-matrix compilation. Assumed here:
  a one-row matrix plus `_` has the same meaning as an explicit match.
- **[[named-patterns-by-field]]** owns named/renamed fields inside the pattern.

## Log

- 2026-08-05: Filed as `let Out(ws) with h := e else ...`, the degenerate
  equation-bearing match found while [[match-with-equation]] landed.
- 2026-08-19: RESCOPED before implementation to expression-valued `if let`,
  using `if let hy : Some(x) = y { ... } else { ... }`. The old `with` word is
  dropped. Ordinary negative-branch evidence is wanted but split to
  [[if-let-negative-evidence]] so it does not hold V1 open.
- 2026-08-19: LANDED positional V1. Both forms lower to one ordinary match;
  constructor fields and nested patterns reuse the pattern compiler, branches
  are blocks, and the named success equation is `scrutinee = pattern`. A hidden
  convoy name plus success-local alias keeps it out of `else`. Option computation,
  constant inference, equation direction/scope, diagnostics, and the indexed
  homogeneous-equality boundary are pinned in `positional_if_let.rs`; `unwrap_or`
  is the representative stdlib use. See
  `docs/language/matching/positional-if-let-design.md`.
