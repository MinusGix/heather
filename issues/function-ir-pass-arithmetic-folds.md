---
title: The FunctionIR pass folds sums, differences and shifts
status: open
labels: [native,compiler,optimisation]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-10-31
updated: 2026-11-09
---

The first FunctionIR pass in Heather ([[function-ir-pass-in-heather]],
`lib/native/function_ir/function_ir_pass.hthr`) folds a node only where its
result is a number's bits at every width, because a `Valuation` is read at
every width: a `Const`, a `Move` of a known word, a comparison (its bit), and
`BitAnd`/`BitOr`/`BitXor` of two bits. Arithmetic is left; constants across
leaves landed (below).

## Arithmetic at every width

`Add`, `Sub` and the shifts of known numbers fold once `bitvec` has their
`ofNat` laws at an open width: `ofNat(a).add(ofNat(c)) = ofNat(a + c)`,
`ofNat(a).sub(ofNat(c)) = ofNat(a - c)` where `c <= a` (a difference below
zero is not one number at every width), `ofNat(a).shift_left(k) =
ofNat(a * 2^k)`. A logical shift right is not a number at every width (the
bits shifted in depend on it), so it folds only where the pass is told the
widths the word is read at. Each rule is one case of `Node::folded` and one
of `Node::folded_value`.

The tools' leaves held no such fold when the pass landed (the builder places
each number into a word of its own and the leaves are cut small), so this is
for sources a richer front end writes.

## Constants across leaves (landed 2026-11-01)

Most of a tool's nodes are `Const`s whose word a later statement reads: a
call's descriptor, a loop's bound, a comparison's other side. Measured over
the ten tools, the payoff is where a call or an exit reads such a word: it
can take the number as an immediate, and the leaf before it then has one
word less live after it, so the pass drops the `Const`. Nearly all of that
is a leaf immediately before the call or exit; threading facts through
every statement found almost nothing more, so what landed is the local
pair, which needs no new claim between statements:

- the pass says what a leaf leaves known (`List::leaves_known`,
  `List::settled`; `Env::computes_knows` proves the run leaves it);
- a call or exit compiles with the words `known` holds as immediates
  (`Prog::known_to`), needing only the rest live (`Stmt::live_head`);
- in a `Then` whose first part is a leaf and whose rest starts with a call
  or exit, the leaf is compiled with what the rest then needs live, where
  that passes the checks the leaf did and needs no word it did not
  (`Stmt::pair_known`); `Target::then_pair` proves it.

The claim between statements is still `Target::Held` over the live set;
the known words are a premise of the one statement after the leaf
(`Target::RunsK`). Facts that would cross a loop's head or a branch's join
would need them in the claim itself, which no tool has wanted yet.

## Log

- 2026-11-09: 2026-11-09: the ofNat laws at an open width are part of [[machine-words-modular-ring]] (docs/native-mathematics-survey.md §2; probe P3 shows the Add law is not by conversion).
