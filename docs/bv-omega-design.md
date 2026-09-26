# `bv_omega`: lifting word arithmetic to Nat

Status: implemented 2026-09-26 (first slice). Anchor issue: `issues/bitvec-nat-lifting-tactic.md`,
whose log holds the verdicts this rests on (flat per-node facts, one δ-step
into non-recursive definitions, arithmetic leaves only).

## 1. What it is

`bv_omega` is a checking-position leaf, like `omega` (`docs/goal-combinators.md`).
At a goal about `x.toNat()` of 64-bit (any literal-width) words built from
`add`, `sub`, `ofNat` and `word_of_nat`, it writes a proof as source:
one fact per word subterm, stating that word's value, with every
"does not overflow" side condition discharged by `omega`. It then elaborates
that source at the goal, so the result is an ordinary term the kernel checks.
Nothing is added to the trusted base.

Wrap-around is not modelled. A word whose value would need `mod` shows up as
a side condition `omega` cannot prove, and the refusal names it (§5).

## 2. The emitted shape

For `times4(y).toNat() = v * 4` with `value: y.toNat() = v` in scope
(abridged; the generator writes qualified names):

```text
have __bv_range_0: (y.toNat() < Nat::pow(2, 64)) = BitVec::toNat_lt_pow(64, y);
have __bv_goal: ((w2: Nat) → w2 + 0 = 4 * y.toNat() → w2 = v * 4) = λ w2 h2 => omega;
have __bv_obligations: ((B1) ∧ (N1)) ∧ ((B2) ∧ (N2)) = ⟨⟨omega, omega⟩, ⟨omega, omega⟩⟩;
have __bv_0: (y.toNat() + 0 = y.toNat()) = bitvec_omega::leaf_affine(64, y);
have __bv_1: (double(y).toNat() + 0 = 2 * y.toNat()) =
    bitvec_omega::add_affine(64, y, y, …, __bv_0, __bv_0, __bv_obligations.left.left, __bv_obligations.left.right);
have __bv_2: (times4(y).toNat() + 0 = 4 * y.toNat()) = bitvec_omega::add_affine(…);
have __bv_obligations = trivial;
__bv_goal(times4(y).toNat(), __bv_2)
```

Each property below was forced by a probe (the issue's 2026-09-26 log has the
measurements):

1. **One fact per node, over the leaves.** A node's fact is `t.toNat() + q = p`,
   where `p` and `q` are affine over *leaf* atoms: the `toNat` of a word the walk
   does not take apart, and the Nat atoms inside `ofNat(…)`. The `+ q` on the
   left is how `sub` stays in Nat. Relating a node to its *children* instead
   made each side condition carry the whole chain below it, and omega's cost
   grows with the chain.
2. **All `omega` work happens before any fact exists.** Each `add`/`sub` node
   contributes a bound (no overflow, or no borrow) and a normalisation (its
   operands' forms add up to its own). Each `ofNat`/`word_of_nat` node
   contributes a bound, and its normalisation holds by computation (`refl`).
   The side conditions form one conjunction, proved leaf by leaf by `omega`.
   An `omega` placed after the facts would reflect every one of them.
3. **The conjunction is balanced.** Every nesting level costs the kernel's
   conversion stack. A right-nested conjunction, or one Π binder per side
   condition, crossed the depth budget near eighty side conditions. A
   projection chain as deep as the conjunction also re-checks it at every
   step. Balanced, a projection is logarithmic.
4. **The goal is proved over Nat variables.** `__bv_goal` states the goal with
   each composite word's `toNat` replaced by a variable, together with that
   word's fact, and `omega` proves it before any fact exists. When `omega`
   met `toNat(double(…))` itself, its atom fallback, which fires on a call
   applied to a literal (the width), reduced the word into the bits of `add`,
   and the certificate outran the kernel's depth budget. A fact in scope over
   a composite word is restated the same way, bound under its own name so
   the original is hidden.
5. **Every binding is `have`.** A node's fact names its operand's fact twice.
   A transparent `let` makes that 2^depth paths through the kernel gate
   (`docs/have-design.md`).
6. **The bundle is hidden from the last step.** `have __bv_obligations = trivial;`
   rebinds the name, so no `omega` inside a later leaf splits the conjunction.

The library lemmas (`lib/std/bitvec/omega.hthr`, harness name `bitvec_omega`)
are `leaf_affine`, `add_affine`, `sub_affine`, `ofNat_affine` and
`word_of_nat_affine`. Each takes its operands' facts and its side conditions,
and states the node's fact. The arithmetic is proved once, over variables.
The module imports `omega`. `bitvec_nat` does not, because harnesses load it
without omega.

## 3. The walk

From every `toNat(n, t)` in the goal and in the Nat facts in context, the walk
classifies `t` by its head:

| head | children | bound | lemma |
|---|---|---|---|
| `BitVec::add(a, b)` | `a`, `b` | `pa + pb < 2^n + (na + nb)` | `add_affine` |
| `BitVec::sub(a, b)` | `a`, `b` | `pb + na <= pa + nb` | `sub_affine` |
| `BitVec::ofNat(c)` | — (`c` reified) | `c < 2^n` | `ofNat_affine` |
| `word_of_nat(n, c)` | — (`c` reified) | `c < 2^n` | `word_of_nat_affine` |
| a definition | its reduct's, under a step budget | — | — |
| anything else | leaf | — | `leaf_affine` |

A definition (`double`, `times256`, `line_state_start`) is stepped through
the oracle's transparent head reducts until a known head appears, under a
small step budget. A head the budget does not reach is a leaf. The fact is
stated at the word as the walk met it, and the kernel meets the δ-step once, in
the fact's ascription.

A word whose `toNat` a fact in scope mentions is not unfolded. The writer
stated what they know at that level: `leading_zeros(x).toNat() = line_skip(n)`
is about the whole word, and unfolding it into its three `below` terms would
leave that fact unused. A known head (`add` and the rest) is still taken apart.

Nodes are shared by their spelling, so `double(y).add(double(y))` has one fact
for `double(y)`. Each leaf also gets its range fact, `toNat_lt_pow`.

The Nat reifier inside `ofNat(c)` understands literals, `+`, `Succ` and
multiplication by a literal. Anything else is a Nat atom, spelled as written.
Affine forms are spelled with the literal on the left (`4 * y.toNat()`):
`mul` recurses on its second argument.

## 4. Scope of the first slice

- Goals: whatever `omega` accepts, over the lifted atoms. Truncated Nat `-`
  is an atom to `omega`, so a goal about a difference is stated as a sum.
- Operations: `add`, `sub`, `ofNat`, `word_of_nat`, and definitions that step
  to them. Byte extraction (`take_low`/`drop_low`) and `unsigned_lt_bit` are
  the next rows, over the same fact form.
- Not in scope: a `match` stuck on a word comparison (`place`); splitting it is
  a follow-up in the `split_all` family.

## 5. Failure

If the generated proof fails, `bv_omega` re-checks the side conditions one at
a time, each after the range facts as in the bundle. It reports the first one
`omega` refuses, with the word it came from: "`double(y)` may overflow 64
bits; `omega` could not prove `…`", then omega's own residual. If every side
condition checks, the goal step is what failed, and its error is reported with
the generated proof.

## 6. Cost

The tactic costs several times the hand proofs it replaces in
`lib/decimal_line.hthr`, so the library keeps its hand proofs.
`issues/bv-omega-check-cost.md` owns the three costs the probes point at.
The first, and the largest for a proof like `place_step`, is that every
`omega` runs in the enclosing declaration's whole context.
