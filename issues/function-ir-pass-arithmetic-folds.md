---
title: The FunctionIR pass folds sums, differences and shifts, and constants across leaves
status: open
labels: [native,compiler,optimisation]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-10-31
updated: 2026-10-31
---

The first FunctionIR pass in Heather ([[function-ir-pass-in-heather]],
`lib/native/function_ir/function_ir_pass.hthr`) folds a node only where its
result is a number's bits at every width, because a `Valuation` is read at
every width: a `Const`, a `Move` of a known word, a comparison (its bit), and
`BitAnd`/`BitOr`/`BitXor` of two bits. Two extensions are left.

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

## Constants across leaves

Most of a tool's nodes are `Const`s whose word a later statement reads: a
call's descriptor, a loop's bound, a comparison's other side. Folding those
needs facts carried between statements, which the compile's claim between
statements (`Target::Held`) does not say. It would be a set of words known
to hold numbers, checked against the environment as the live set is, and
the leaf's emission would start the pass from it. S4's selection already
folds a known constant into an immediate inside one leaf
(function-ir-verified-selection-rules), so the gain is where a constant
crosses a statement.
