---
title: Substituting a payload deep-copies it, three times, even at depth zero
status: closed
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

- 2026-07-28: FIXED. Every shift_* entry point (Term/Type via the ops! macro, plus LocalCtx and LocalSubst, plus the two _above cutoff variants) returns self.clone() at by == 0 -- an Rc bump that keeps every subterm shared. Soundness argument written up in subst.rs §Shifting by zero: at by = 0 each mapper's variable case is v -> v, each tail case adds zero, and Level::shift(0, _) is structurally the identity because Level::succ/max are plain constructors that normalize nothing, so the fast path is indistinguishable from the traversal -- and t.shift_local(0) == t was already a property-tested law (tests/subst_laws.rs, shift_composition), now extended to the _above variants. Put the guard in the entry points rather than at SubstLocal::local_var, so every caller benefits, the elaborator's shift-heavy walks included.
- 2026-07-28: Effect, measured by the bench that found it (scripts/bench, baseline re-recorded): one beta-step at a 1024-node annotation 154 us -> 98 ns and FLAT (slope 1.03 -> -0.01); add n n at n=1024 232 ms -> 171 us, slope 2.02 -> 1.00; conv(add n n, 2n) at n=512 92 ms -> 154 us, slope 2.20 -> 1.02; mul n n now quadratic as designed (2.77 -> 1.98). Two effects nobody was looking for, which is the argument for a wide fixture set: wf/mirror-involution 3x faster (262 ms -> 89 ms at 2963 nodes -- generated recursors substitute a transient ih per node), and code/whnf-identity-recursor 2.6x at 33 code nodes, its slope falling 0.86 -> 0.43 as the marginal cost stopped dominating. Untouched, as predicted: subst/shift-local, subst/apply-local, nat/check-numeral, wf/check-tree -- all of those shift by nonzero, so the guard cannot help them.
- 2026-07-28: Tests: 42 binaries green. Added shifting_by_zero_preserves_sharing (tests/subst_laws.rs) -- Rc::ptr_eq on subterms, because equality alone would have passed against the deep-copying traversal too, plus a negative control that shift_local(1) does NOT share. Extended shift_composition to the _above variants at zero. Closing: the deeper half stays out, deliberately -- a payload inserted under k > 0 binders still costs a full copy, and making that cheap is shift-annotated or hash-consed terms, which [[dependency-policy]] already records as a kernel design decision to take on purpose. Nothing in the suite currently argues for it: the two remaining large per-node costs (wf/mirror-involution ~30 us/node, code/check-identity-recursor 0.54 ms fixed) have not been attributed to it.
