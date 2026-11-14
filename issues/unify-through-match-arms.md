---
title: Learn a lemma's arm functions from the match a goal holds
status: open
labels: [elaboration, unifier, inference]
area: language
milestone: [lang-proof-modularity]
code: crates/elab/src/unification.rs @ 7cda267
created: 2026-11-14
updated: 2026-11-14
---

A lemma over a `match h:` whose arms are its implicits,

    theorem Bool::taken_true<A>(b: Bool, {f: (b = True) → A}, {g: (b = False) → A}, e: b = True):
        (match h: b { True => f(h), False => g(h) }) = f(e)

could not have `f` and `g` solved from the `match` a goal holds — the
right side of a `decreases` function's unfolding at its `if h:` test —
though each arm `λ h => ?f(h)` is a Miller pattern. A step had to be
written `Bool::convoy_true(b, yes, no, e)` with both arms spelled out
proof-free (`/mnt/project-files/design/loop-proof-probe.hthr`).

## What was missing, and what is built

1. **No congruence for `case`.** `unify_tm` paired `elimNat`s but listed
   `case` among the inert patterns. A `(case, case)` pairing now unifies
   the summand types, the scrutinee, the motive and each arm under its
   binder; the arms then meet as `λ h => ?f(h)` against `λ h => body` and
   the Miller rule abstracts. Learn-only, like `elimNat`'s; the kernel
   judges the call. A `case` pattern against anything else is still inert.
2. **A `case` head against a call paired the spines positionally**: the
   lemma's `(case …)(refl)` met `taken_pick(b)` as head against head and
   learned nothing. A `case`-headed pattern against a call now takes the
   δ-lazy step (`unify_unfolded`), as two distinct rigid heads do.
3. **`next_head` walked past a stuck `case`**: it unfolds until a head a
   pattern could meet, and `case` was one it "steps through", so a body
   ending in a `case` on a neutral scrutinee unfolded to nothing. A walk
   that ends on a `case` it cannot take now ends there.

`Bool::taken_true` and `Bool::taken_false` are in `lib/std/core/bool.hthr`;
probes `taken_pick_*`, `taken_open`, `count_to_done`, `count_to_step`
and the negative control `taken_wrong_arm` in
`lib/_tests/std/core/bool_tests.hthr`. With them the SHA-256 step is

    trans(Sha256::begin_unfold(s, i), Bool::taken_false(i.unsigned_lt_bit(8), e))

with the test's verdict `e` the only thing written.

## Still open

- **Under an unannotated `let`.** `let t = trans(f_unfold(x),
  Bool::taken_true(c, e));` is refused (`could not infer the implicit
  argument g`): with no expected type, `trans`'s second argument is
  checked against `y = ?z` with the outer `?z` open, so it is inferred on
  its own, and alone it has nothing to learn `g` from. The same call
  where the goal is known (a theorem's body, an annotated `let`) works.
  What it needs is a deferred argument checked against its partially
  solved domain, the outer call's slot learned back from it: general
  application machinery (`apply_implicit`'s deferral), not this rule.
- **A step's right side has no surface spelling when the arm reads the
  equation**: `begin_step`'s `begin(…put(…, inside := begin#found_1(i, h)))`
  mentions the found proofs, so it cannot be written as a statement, only
  produced by `trans`. The interchangeable-proofs thread (brief §1) and
  the loop-rules thread (brief §2, generated `f_step`/`f_done`) are what
  retire that.

## Log

- 2026-11-14: rules 1–3 built (thread "Fix inference and printing around
  match"); the whole library re-elaborates unchanged.
