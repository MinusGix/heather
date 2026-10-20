---
title: "Lint matches that return a function only to be immediately applied"
status: open
labels: [tooling,lint,frontend,elaboration,stdlib,ergonomics]
area: language
created: 2026-08-22
updated: 2026-08-22
---

A recurring dependent-elimination spelling puts a hypothesis outside a
`match`, makes the match return a function that accepts it, then immediately
applies that function:

```heather
λ m h =>
    match m as λ y => P(y) → Q(y) {
        Zero => bad ⊢ absurd(bad),
        Succ(k) => good ⊢ use(k, good),
    }(h)
```

When the hypothesis binder is moved into the match's checking position, goal
motive synthesis can often remove both the application and the written
motive:

```heather
λ m =>
    match m {
        Zero => bad ⊢ absurd(bad),
        Succ(k) => good ⊢ use(k, good),
    }
```

Add a conservative lint for this shape and use it to audit the remaining
stdlib sites. This is not a textual `}(h)` rule: a match may intentionally
produce a first-class function. The initial recognizer should require an
immediately enclosing lambda, bare trailing lambda binders supplied as the
application arguments in order, and an explicit function-valued motive.

## Acceptance

- The lint has a stable identifier and is implemented as a registered source
  lint rather than an ad-hoc elaborator condition.
- It recognizes `λ x h⃗ => (match x as … { … })(h⃗)` when the applied
  arguments are exactly a trailing run of the lambda's binders.
- It does not warn when the match result is stored, returned, passed, applied
  to a non-binder expression, or deliberately used as a first-class function.
- Every warning offers the checking-position rewrite and explains that motive
  inference is the benefit; it does not claim the explicit motive is itself
  always redundant until the rewritten declaration has checked.
- The standard-library occurrences are audited and rewritten where the
  suggested form checks; genuine first-class-function cases are recorded as
  controls.
- Failed and generated declarations produce no lint findings, preserving the
  warning channel's existing attribution rules.

## What it assumes from elsewhere

- [[match-motive-surface-audit]] owns the complete motive census and any
  eventual replacement for `as λ`; this issue owns one mechanically
  recognizable source shape and its cleanup.
- [[stdlib-surface-style-lint]] owns the general rollout policy. This issue is
  a focused rule with a semantic exemption for intentional function values.

## Log

- 2026-08-22: Filed from the `le_succ_r` rewrite. Moving `h` inward made the
  existing checking-position synthesis remove two explicit motives without an
  elaborator change; the stdlib has many visually similar sites, but the lint
  must distinguish them from matches that intentionally compute functions.
- 2026-08-22: The lint substrate and first rule landed as a reviewable slice:
  warnings now carry stable `Lint` identities, syntactic rules occupy a small
  registry over a shared source-AST walker, and semantic warnings use the same
  emission channel. The rule requires an explicit function-valued motive and
  an exact nonempty trailing run of bare enclosing lambda binders; controls
  retain first-class matches and applications to other expressions. Its
  initial stdlib census is 35 findings: 12 in `std/nat` and 23 in `std/int`,
  with the other std modules clean. Those rewrites and their genuine controls
  remain the open cleanup portion of this issue.
