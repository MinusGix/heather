---
title: Substituting a payload deep-copies it, three times, even at depth zero
status: open
labels: [kernel,performance]
code: crates/kernel/src/subst.rs:770 @ b97e3c3
created: 2026-07-28
updated: 2026-07-28
---

`SubstLocal::local_var` ends every hit with

```rust
payload.shift_local(at.local).shift_global(at.global).shift_univ(at.univ)
```

and none of the three shifts has a no-op fast path, so a substituted term is
structurally rebuilt **three times** — including when all three depths are
zero, which is the common case. `Rc` sharing is discarded in the process: the
copy is deep in the payload, not just at its root.

`SubstGlobal` and `SubstUniv` shift their payloads the same way, so this is
one pattern in one file rather than three unrelated bugs.

## What it costs, measured

Found by the first run of the kernel bench suite ([[kernel-benchmarks]]);
reproduce with `scripts/bench --filter nat`.

`nat/step-once` isolates it: **one** `elim_Nat` β-step, timed against the size
of the eliminator's `base` annotation, which the rule never reads.

| base nodes | one β-step |
|---|---|
| 64 | 8.6 µs |
| 256 | 36.4 µs |
| 1024 | 154 µs |

Slope 1.03 — linear in an annotation the rule does not look at, ~150 ns per
untouched node. The rule is O(1) on paper:
`elim … (su t) ⇝ s'[t/x, elim … t/y]` substitutes the recursive occurrence
into a two-node step body, at depth zero.

Downstream that per-step cost moves unary arithmetic into the wrong
complexity class:

| family | should be | measured slope |
|---|---|---|
| `nat/add-normalize` | linear | **2.02** |
| `nat/mul-normalize` | quadratic | **2.77** |
| `conv/computed-numeral` | linear | **2.20** |

`add n n` at n = 1024 takes 230 ms; the conversion of the same computation
against its result, 90 ms at n = 512.

## Why it matters beyond arithmetic

Numerals are the messenger, not the point. The design leans on kernel
computation twice — ordinary `fn`s execute by it, and `Compile` equiv proofs
are meant to discharge by conversion making `simulate ir` unfold — and both
are recursions whose payload is a term carrying annotations. A per-step cost
linear in the payload makes a fuel-indexed evaluator quadratic in fuel when
its own definition is linear: the difference between "the checker replays the
program" and "the checker cannot". [[ir-simulate-design]] owns simulate's
shape; this issue owns the reason its cost model would be wrong today.

## What to look at

The fix looks like three lines — return the payload unchanged when the
corresponding depth is zero — and the law it needs is *already* property-
tested: `tests/subst_laws.rs`'s `shift_composition` asserts
`t.shift_local(0) == t` and the same for the other two namespaces, over
generated terms. So the change is sound by a law the suite already checks,
which is the good case. Still, it is an edit to the trusted base:

- Key the fast path on the whole operation being the identity, **tail
  included**. `Mapper::tail` rewrites `SubstTail` lengths and bases;
  `ShiftLocal::tail` adds `by` to the length, a no-op at 0 — verify that per
  mapper rather than assuming it of all three.
- Sharing is the actual win: after the fast path, a payload substituted at
  depth zero should be an `Rc` clone. Worth an explicit `Rc::ptr_eq` test,
  since a later refactor could reintroduce the rebuild and only the bench
  would notice.
- Consider whether the fast path belongs *inside* the `shift_*` entry points
  (fixing every caller at once, including the elaborator's shift-heavy walks)
  rather than at this one call site. The wider version is the same law.
- The bench is the proof of the fix: `nat/step-once`'s expected slope band
  becomes `(-0.15, 0.15)` and `nat/add-normalize`'s `(0.85, 1.30)`. Both bands
  carry a comment saying so, so landing the fix is a two-line fixture edit
  plus `scripts/bench --save`.

Explicitly not in scope: hash-consing, a conversion cache, or any other
representation change. [[dependency-policy]] already records that the real
lever at term volume is hash-consed `Rc<Term>` and that it is a kernel design
decision to take on purpose. This issue is the cheap half — the kernel doing
work it has no reason to do.

## What it assumes from elsewhere

- **[[kernel-substitutions]]** owns the substitution algebra and its laws.
  Assumed here: only that shifting by zero is the identity, so skipping it
  changes no result.
- **[[kernel-benchmarks]]** owns the bench suite. Assumed here: only that
  `nat/step-once` exists and isolates one β-step, so a fix has a proof.

## Log
