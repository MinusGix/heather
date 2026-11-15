# `bv_omega`: lifting word arithmetic to Nat

Status: implemented 2026-09-26. Anchor issues:
`issues/bitvec-nat-lifting-tactic.md` (the tactic and the verdicts it rests
on: flat per-word facts, a step into non-recursive definitions, arithmetic
leaves only) and `issues/bv-omega-check-cost.md` (the cost rounds that shaped
§2 and §6). Numbers live in those logs, not here.

## 1. What it is

`bv_omega` is a checking-position leaf, like `omega` (`docs/tactics/goal-combinators.md`).
At a goal about `x.toNat()` of words built from `add`, `sub`, `ofNat` and
`word_of_nat`, or byte extraction, it writes a proof as source: one fact per word, stating that
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
- a word whose value a fact in scope bounds by a literal within the width,
  `x < k` or `x <= k` with `x` of the word's form `P` and `Q` zero, gets its
  bound from that fact (`below_top`, `below_top_le`): the writer stated it,
  as `c_fits: 1099511627776 * c < 1152921504606846976` does for
  `ofNat(1099511627776 * c)`;
- every other word's bound, the outermost words' and a `sub`'s minuend's, is
  a side condition for `omega`. So is each `sub`'s no-borrow, `Q <= P`.

Shared operands must not make bound dependencies cyclic: `w.sub(w)` cannot
get `w`'s bound from itself, and `w.add(w).sub(w)` must not pass it around
through the addition. A parent edge that would close a cycle is skipped,
leaving a stated bound or an independent side condition to supply it.

A side condition over no atoms (`5 < 2^64 + 0`) is a comparison of literals,
proved by `trivial`: the kernel decides `Le` of literals, `pow` included.

When the goal is a word's fact itself, it is read off the fact with no search:
`toNat(t) = r` where `r` reads as the form `P` and `Q` is zero
(`fact_value`), or `toNat(t) = a - b` where `a` and `b` read as `P` and `Q`
(`fact_diff`), either way round. Otherwise the goal is proved over Nat
variables: `(w: Nat) → w + Q = P → GOAL[w]`, by `omega`, before any fact
exists. A fact in scope over a word the walk takes apart is restated the same
way, under its own name so the original is hidden.

Each `omega` costs a floor of its own (reflection, a certificate elaborated
and gated), and a problem as small as a single bound pays mostly that floor.
So the shapes above exist to make no call where the answer is already
written down: in `decimal_line`'s word facts, all but `place_step`'s calls
now make at most one.

Shapes that were tried and measured against, with the reason each lost:

- *Facts relating a word to its operands* made each side condition carry the
  chain below it, and `omega`'s cost grows with the chain.
- *A normalisation side condition per `add`* was half of all `omega` calls.
- *Omega rows* (`OfNat(t.toNat()) = k + dot(C, atoms)`, normalising by
  computing `add_coeffs`) cost the checker thousands of steps per lemma
  application. Any list literal in a type does, Nat or Int.
- *`let` for the facts*: a fact names its operand's twice, and a transparent
  `let` makes that 2^depth paths through the kernel gate
  (`docs/language/have-design.md`). Every binding is `have`.
- *`omega` over a composite word's `toNat`*: its atom fallback, which fires on
  a call applied to a literal (the width), reduced the word into the bits of
  `add`. Hence the goal over Nat variables.

The side conditions form one balanced conjunction, proved leaf by leaf by
`omega` in the entry context, before the arithmetic word facts exist (the
ranges and comparison bridges in §3 are already available). Balanced, because
each nesting level costs the kernel's conversion stack; before the arithmetic
facts, because an `omega` after them would reflect every one of them.

A fact in scope can be about a composite word: `1 < n - i`, or a Nat fact
over `(n - i).toNat()`. Such a *hypothesis word*'s `toNat` is an atom to an
`omega` in the entry context, which cannot relate it to `n` and `i`, so a
side condition that needs it (`i + 2 <= n`, for `n - (i + 2)`'s no-borrow)
was unprovable there. The side conditions are therefore proved in stages: the
`k`th hypothesis word's own side conditions given the facts of the hypothesis
words before it, then the rest given every hypothesis word's fact. A stage
with facts is stated like the goal, over Nat variables
(`(w: Nat) → w + Q = P → bridges[w] → conditions`), and proved by `omega`
before any fact exists; once its words' facts are emitted it is applied to
them, and its conjunction is projected like the first stage's. A word built
from a literal is never a hypothesis word: its value is the literal. With no
hypothesis word there is one stage, as before. A failed proof re-checks each
side condition as its stage stated it (§5).

## 3. The walk

From every `toNat(n, t)` in the goal and in the Nat facts in scope, the walk
classifies `t` by its head:

| head | taken apart as |
|---|---|
| `BitVec::add(a, b)` | `add_form` over `a`, `b` |
| `BitVec::sub(a, b)` | `sub_form` over `a`, `b` |
| `BitVec::ofNat(c)` | `ofNat_form`, `c` read as a form |
| `word_of_nat(n, c)` | `word_of_nat_form`, `c` read as a form |
| `BitVec::take_low(n, m, x)` / `drop_low(n, m, x)` | half-word leaves, their ranges, and `x.toNat() = lo.toNat() + 2^n * hi.toNat()` |
| a definition | its reduct's, under a step budget |
| `BitVec::band(x, y)` | a leaf, beside its range `toNat(x & y) <= m` when `y` is `ofNat(m)` with `m` a literal, else `<= toNat(y)` with `y` walked (`toNat_band_ofNat_le`, `toNat_band_le_right`; `issues/bv-omega-masked-word-bound.md`) |
| anything else | a leaf |

A definition (`double`, `times256`, `line_state_start`) is stepped through the
oracle's transparent head reducts until a known head appears; a head the
budget does not reach is a leaf. The fact is stated at the word as the walk
met it, and the kernel meets the δ-step once, in the fact's ascription.

A word whose `toNat` a fact in scope mentions is not unfolded. The writer
stated what they know at that level: `leading_zeros(x).toNat() = line_skip(n)`
is about the whole word. A known head is still taken apart.

Such a leaf *defined* by a fact, `toNat(t) = v` or `v = toNat(t)`, is stated
over `v` instead of over its own `toNat` (`leaf_value`): its form is `v`'s, as
the reader reads `v`, and its bound is still its range. So a goal over
`line_skip(n)` meets a fact over `line_skip(n)`, not over
`leading_zeros(…).toNat()`, and the two forms compare equal without `omega`.
It is still a leaf for the goal over Nat variables: its `toNat` stays an atom
there, beside the fact that defines it. A cycle of definitions ends in a
plain leaf.

The reader inside `ofNat(c)` understands literals, `+`, `Succ`, a literal
factor on either side, and the `toNat` of a word with no subtraction below it
(its fact then states its value). Anything else is a Nat atom. Coefficients
are spelled on the left (`4 * a`): `mul` recurses on its second argument.

A word that appears only in a fact in scope, not in the goal, is optional: it
may overflow or borrow where the goal's words do not. The first attempt
restates every such fact untried; only if the checker refuses the proof does
the careful attempt (§5) try each fact's new side conditions first and leave
the fact alone when one fails. A fact left alone is tried again once a later
one is taken, since that one's comparison may be what its side conditions
needed (`1 < n - i` written before `i < n`). Trying them first had cost an `omega` per new
side condition on every call, and the bundle then proved each one again.

Byte decomposition is shared by the two halves of a split. Literal widths
spell `2^n` as a literal coefficient for `omega`; an open width retains the
power expression. The input is walked too, so extracting from an arithmetic
word uses its ordinary value fact. Definitions of either half retain their
written name, with equality facts connecting additional aliases.

An unsigned comparison equation in scope, in either orientation, supplies
`a.toNat() < b.toNat()` for `True`, or `b.toNat() <= a.toNat()` for `False`.
The other tests a `match h:` or an `if h:` puts in scope are read the same
way, each through its `bitvec_omega` lemma: `a.unsigned_le_bit(b)` (`<=`, or
`>` for `False`), `a.eq_bit(b)` (`=`, or `≠`), and the propositions `a < b`
and `a <= b` at a word (issues/decreases-word-measures-by-hand.md).
These bridge facts are available before side conditions and are restated
under the same names when the arithmetic goal generalises composite words.
Words appearing only in a comparison remain optional in the careful attempt.
For a comparison operand built by `ofNat` or `word_of_nat`, an independently
checked fit bound permits its value equation before the side conditions too.
This lets a comparison against `ofNat(c)` justify a subtraction's no-borrow
condition over `c`. When that bound fails, the comparison supplies no equation
equating the operand's value with the Nat it was built from.

## 4. Scope

- Goals: whatever `omega` accepts, over the lifted atoms, and a word's fact
  itself, including as a truncated difference `P - Q` (§2). Word equality
  goals reduce to equality of their Nat values through `ofNat_toNat`;
  equality with `ofNat(c)` uses a value equation directly. An unsigned
  comparison equal to `True` or `False`, in either orientation, reduces to
  the corresponding Nat order, as do the `<=` bit equal to a constructor and
  the propositions `a < b` and `a <= b` at a word (`unsigned_le_of_true`,
  `unsigned_lt_of_nat`, …). Each bridge is an ordinary lemma application
  over a checking-position `bv_omega` subgoal.
- Operations: `add`, `sub`, `ofNat`, `word_of_nat`, `take_low`, `drop_low`,
  and definitions that step to them. Byte extraction and comparison bridges
  are recorded in `issues/bv-omega-bytes-and-comparisons.md`. `split_all` also
  splits matches stuck on unsigned word comparisons and supplies their branch
  equations to the leaf (`docs/tactics/goal-combinators.md`,
  `issues/bv-omega-split-stuck-comparison.md`).

## 5. Failure

The first proof is optimistic: a goal read off a word's fact, and facts
restated without trying their side conditions. If the checker refuses it,
`bv_omega` writes the careful proof — the goal by `omega`, optional facts
tried first — and checks that; a proof that would have succeeded carefully
still succeeds. If the careful proof fails, `bv_omega` re-checks the side
conditions one at a time and reports the first one `omega` refuses, with the word it came from:
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

### 6.1 Named values: `omega`'s atom list

The same arena holds *transparent* slots, for a value a tactic would
otherwise spell at every use. `omega` is the one user. Its certificate
mentions its atom list in every `basis(i, atoms)`, `zeros(atoms)` and lemma
argument, and each literal copy costs the checker a full list check: on a
small goal the copies were essentially the whole kernel cost. The certificate
instead names the list `__omega_atoms`. The `omega` arm then works in three
steps:

- It elaborates the literal once, checked at `list::List<int::Int>`, since an
  empty list infers nothing.
- It stores the value in a transparent slot (`allocate_transparent`). The
  same value in the same context shares one slot.
- It checks the certificate with the name bound as an alias to the slot's
  reference.

A transparent slot is a definition in both worlds:

- **While the declaration elaborates**, conversion must compute
  `basis(i, atoms)` and the rows built from it. The semantic oracle's δ world
  and the goal world therefore carry the slot's body, scoped in committed Ψ.
  A value or context that mentions a goal cannot be scoped there and stays
  inline.
- **At the gate**, `lift_proved` lifts transparent slots alongside proved
  ones, in slot order, as definitions (`body: Some`). A proof lifted after
  one refers to it like an earlier proof.

Capacity is reserved up front by `count_tactic_slots`: two slots per
`omega`, since an equality goal is two calls, and a few per `bv_omega`, for
the `omega` calls in the proof it writes. An allocation past the reservation
requests a restart with double the capacity and aborts the attempt. A
declaration with a restart pending is never gated: the attempt is discarded
whatever it returns, and gating it had cost a full check of the inline
certificate. Where restarts are off, the list stays inline, as it was.
