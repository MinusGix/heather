# `bv_omega`: lifting word arithmetic to Nat

Status: implemented 2026-09-26. Anchor issues:
`issues/bitvec-nat-lifting-tactic.md` (the tactic and the verdicts it rests
on: flat per-word facts, a step into non-recursive definitions, arithmetic
leaves only) and `issues/bv-omega-check-cost.md` (the cost rounds that shaped
§2 and §6). Numbers live in those logs, not here.

## 1. What it is

`bv_omega` is a checking-position leaf, like `omega` (`docs/goal-combinators.md`).
At a goal about `x.toNat()` of words built from `add`, `sub`, `ofNat` and
`word_of_nat`, it writes a proof as source: one fact per word, stating that
word's value, with every "does not overflow" and "does not borrow" side
condition discharged by `omega`. It elaborates that source at the goal and
lifts the result into a lemma of its own (§6). The result is an ordinary
proof the kernel checks. Nothing is added to the trusted base.

Wrap-around is not modelled. A word whose value would need `mod` shows up as
a side condition `omega` cannot prove, and the refusal names it (§5).

## 2. Facts, forms, bounds

A word `t`'s fact is `t.toNat() + Q = P`. `P` and `Q` are *forms*:
`c₁ * a₁ + (c₂ * a₂ + (… + k))`, literal coefficients over the call's atoms in
one fixed order, zero coefficients left out. An atom is the `toNat` of a word
the walk does not take apart (a leaf), or a Nat atom inside `ofNat(…)`. `+ Q`
on the left is how a difference stays in Nat. An `add` merges `P` with `P` and
`Q` with `Q`; a `sub` merges crosswise.

Merging two forms is one lemma step per atom (`form_step` when both have it,
`form_left`/`form_right` when one does), and the coefficients add as literals,
which the checker computes. So no fact needs a search, and a fact costs the
checker a few dozen steps.

A word's *bound* is `P < 2^n + Q` (no overflow). Bounds flow down, facts flow
up:

- a leaf's bound is its range (`toNat_lt_pow`);
- an `add`'s operand gets its bound from the `add`'s bound and its sibling's
  *sign* `Q <= P` (free when `Q` is zero; a `sub`'s no-borrow otherwise);
- a `sub`'s subtrahend gets its bound from the no-borrow and the minuend's
  bound;
- every other word's bound, the outermost words' and a `sub`'s minuend's, is
  a side condition for `omega`. So is each `sub`'s no-borrow, `Q <= P`.

The goal is proved over Nat variables: `(w: Nat) → w + Q = P → GOAL[w]`, by
`omega`, before any fact exists. A fact in scope over a word the walk takes
apart is restated the same way, under its own name so the original is hidden.

Shapes that were tried and measured against, with the reason each lost:

- *Facts relating a word to its operands* made each side condition carry the
  chain below it, and `omega`'s cost grows with the chain.
- *A normalisation side condition per `add`* was half of all `omega` calls.
- *Omega rows* (`OfNat(t.toNat()) = k + dot(C, atoms)`, normalising by
  computing `add_coeffs`) cost the checker thousands of steps per lemma
  application. Any list literal in a type does, Nat or Int.
- *`let` for the facts*: a fact names its operand's twice, and a transparent
  `let` makes that 2^depth paths through the kernel gate
  (`docs/have-design.md`). Every binding is `have`.
- *`omega` over a composite word's `toNat`*: its atom fallback, which fires on
  a call applied to a literal (the width), reduced the word into the bits of
  `add`. Hence the goal over Nat variables.

The side conditions form one balanced conjunction, proved leaf by leaf by
`omega` in the entry context, before any fact exists. Balanced, because each
nesting level costs the kernel's conversion stack; before any fact, because
an `omega` after the facts would reflect every one of them.

## 3. The walk

From every `toNat(n, t)` in the goal and in the Nat facts in scope, the walk
classifies `t` by its head:

| head | taken apart as |
|---|---|
| `BitVec::add(a, b)` | `add_form` over `a`, `b` |
| `BitVec::sub(a, b)` | `sub_form` over `a`, `b` |
| `BitVec::ofNat(c)` | `ofNat_form`, `c` read as a form |
| `word_of_nat(n, c)` | `word_of_nat_form`, `c` read as a form |
| a definition | its reduct's, under a step budget |
| anything else | a leaf |

A definition (`double`, `times256`, `line_state_start`) is stepped through the
oracle's transparent head reducts until a known head appears; a head the
budget does not reach is a leaf. The fact is stated at the word as the walk
met it, and the kernel meets the δ-step once, in the fact's ascription.

A word whose `toNat` a fact in scope mentions is not unfolded. The writer
stated what they know at that level: `leading_zeros(x).toNat() = line_skip(n)`
is about the whole word. A known head is still taken apart.

The reader inside `ofNat(c)` understands literals, `+`, `Succ`, a literal
factor on either side, and the `toNat` of a word with no subtraction below it
(its fact then states its value). Anything else is a Nat atom. Coefficients
are spelled on the left (`4 * a`): `mul` recurses on its second argument.

A word that appears only in a fact in scope, not in the goal, is optional: it
may overflow or borrow where the goal's words do not. Its new side conditions
are tried first, and the fact is left alone if one fails.

## 4. Scope

- Goals: whatever `omega` accepts, over the lifted atoms. Truncated Nat `-` is
  an atom to `omega`, so a goal about a difference is stated as a sum.
- Operations: `add`, `sub`, `ofNat`, `word_of_nat`, and definitions that step
  to them. Byte extraction, `unsigned_lt_bit` and word equality goals are
  `issues/bv-omega-bytes-and-comparisons.md`; splitting a `match` stuck on a
  word comparison is `issues/bv-omega-split-stuck-comparison.md`.

## 5. Failure

If the generated proof fails, `bv_omega` re-checks the side conditions one at
a time and reports the first one `omega` refuses, with the word it came from:
"`double(y)` may overflow 64 bits; `omega` could not prove `…`", then omega's
own residual. If every side condition checks, the goal step failed, and its
error is reported with the generated proof.

## 6. Lifting

A proof inline in a declaration's body is checked, respelled, substituted and
imaged with the whole body, deep under its binders, and the kernel's term
handling there is sized by the context (a profile of `decimal_line`'s
`place_step` is flat across allocation, drops, shifts and substitutions). A
hand proof avoids that by putting its arithmetic in lemmas. `bv_omega` does
the same for itself:

- It stores its checked proof in a *proved slot* of the declaration's goal
  arena (`goals.rs`), over the current context, and returns the slot's
  reference `u^id(Γ)`: the reference a hole gets. `count_holes` reserves one
  slot per `bv_omega` in the source, so no slot forces a restart. A site met
  again in another context (a block cloned into several branches) stays
  inline.
- At the gate, `lift_proved` moves each proved slot out of the goal world into
  Ψ followed by the lifted proofs before it: a later proof may refer to an
  earlier one, since a `let` bound to one is inlined into what follows. Any
  other goal in a lifted proof is refused. The context is kernel-checked, then
  the statement and proof go through the ordinary gate (`gate_bodied`: cache,
  statement, proof inline or on the pool) as an opaque global
  `decl#auxN` in that context.
- The declaration's committed globals are shifted up past the lifted ones
  (`shift_global_above`), the slots are substituted by references to them,
  and the declaration is gated in Ψ extended by them. `commit_decl` pushes
  them just before the declaration's own binding. They carry no name: like a
  key-less generated definition, they travel in the module's Ψ suffix.

The lemma closes over the whole context. What that costs, and a relevance
filter, are `issues/bv-omega-check-cost.md`'s.
