---
title: Decide width-generic BitVec laws by transducers (multi-width linear-bitwise fragment)
status: open
labels: [proofs,solver,bitvec,tactics,research,design]
area: tactics
created: 2026-10-25
updated: 2026-10-25
---

Prove width-generic `BitVec` claims with a tactic, instead of by hand. The
claims in view are the open-width laws in `lib/std/bitvec/bitvec.hthr` and,
later, the rewrite rules of optimisation passes stated at a node's symbolic
width. The method is the multi-width transducer procedure of Bhat et al.,
OOPSLA 2026 (`docs/multi-width-bitvector-survey.md` §4, paper at
`docs/3839511.pdf` §5).

The fragment: add, subtract, multiplication by a literal, the bitwise
operations, truncation and both extensions, unsigned and signed comparison,
and equality. Width variables may appear with `+` and literals, and
hypotheses may relate them. A width is its mask bitstream (`n` trues, then
falses) and a value its bits, least significant first. Each operation is a
finite-state transducer (add is a ripple adder with one carry bit, equality
latches on the first difference), and the goal holds at every width when
every reachable state of the composed transducer outputs true.

Heather's `BitVec` is already the bitstream (a vector of Booleans, least
significant first), and `add`/`sub` are already ripple folds. So the
semantic lemma "this transducer's output is the operation's bits" should be
an induction that follows the library's own recursion.

## Shape

- An intrinsically width-indexed reflected syntax, a transducer built from
  it by a Heather function, and one soundness theorem: a safe transducer
  gives the goal. Completeness is not needed. Outside the fragment the
  tactic refuses and names the subterm (a variable multiplication, a
  variable shift count, an unknown head).
- **Rung A:** the host (an untrusted search, Rust or Heather) computes the
  reachable state set. The kernel checks by evaluation that it contains the
  start state, is closed under every input letter, and outputs only true.
  No SAT solver.
- **Rung B:** k-induction or IC3 with a symbolic invariant. It needs the
  SAT certificate checker of [[lrat-certified-bitvector-decision]], so it
  waits for that.
- The reifier must see through width transports
  (`Nat::add_succ_left`-shaped casts). Heather's extensions take a delta,
  `BitVec(n) → BitVec(extra + n)`, so multi-width statements meet `+` in
  types (survey §2). Whether to add target-width spellings is decided
  here, when a goal needs them.

## Acceptance (first round, investigation)

Restate a handful of the library's hand-proved laws through the procedure
at rung A: `band_comm`, `bxor_comm`, `xor_self`, `add_comm`,
`add_sub_cancel`, `truncate_zero_extend`, `add_zero_extend_mask`, and the
sign-flip signed comparison of survey §3. Add one negative control, a false
law refused with its counterexample width. Report reachable-state counts
and how the kernel's checking cost grows with them, as shapes. From that,
decide whether rung A is enough for the library's laws or whether rung B is
the real entry point.

## What it assumes from elsewhere

- **[[lrat-certified-bitvector-decision]]** owns SAT certificate checking.
  Assumed here: only that rung B can call it once it exists.
- **[[kernel-native-bitvector-values]]** owns the kernel's closed-word
  transducer class. Assumed here: nothing. This procedure is library code
  and proves open claims. The kernel model's planned bit-transducer rung
  (`docs/kernel-model-design.md`) needs the same transducer notion, so it
  should be defined once where both can import it.
- **[[function-ir-narrow-arithmetic]]** owns the narrow-width lowering
  rules. They are a customer: each rule is a fragment law.
