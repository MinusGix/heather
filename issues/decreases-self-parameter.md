---
title: decreases: a measured recursion cannot be a method (a self or mut self parameter is refused)
status: closed
labels: [elaboration, termination]
area: language
created: 2026-11-11
updated: 2026-11-12
---

A `decreases` function may not take a `self` parameter:

```heather
fn List::raise_from(mut self span: List<BitVec(8)>, length, i: BitVec(64)) → BitVec(64)
    decreases length.sub(i).toNat() { … }
```

is refused with "`decreases` does not yet cover a declaration with a `self`
or solver parameter (`span`): the recursion re-binds every parameter
explicitly, and those two are filled another way"
(`crates/elab/src/measure.rs`). A plain `self` is refused the same way, so
no measured recursion is a method.

Who is waiting: a `runtime fn` that writes a span
(docs/native/native-one-compiler-design.md §2.6, U4 step 4c). Its source was
designed as a `mut self` method on the span's bytes; a loop over the span
is a measured recursion, so today it is written as a plain function that
returns `Mutated<List<BitVec(8)>, R>` itself, with `let mut span = span;`
in the arm that stores and `Mutated(span, value)` where it returns. The
kernel type is the one the method would have, and the reflector reads
that type, so the two spellings reflect alike once the method is allowed.

What it needs: the desugaring to strong induction re-binds the parameters
under their own names and rewrites `f(ȳ)` to `ih(ȳ, proof)`. With a `self`
parameter the self-call is also written `x.f(ȳ)`, and with `mut self` the
parser has already lowered the body to `{ let mut x = x; body′;
Mutated(x, value) }`, so a self-call on the receiver is a call whose
`.after` rebinds `x` and whose `.value` is read. The recursion then ends in
`Mutated(r.after, r.value)` and not in the call: with no η for records it
does not convert to the call, so a tail self-call on the receiver should
lower to the call itself where it is the method's last expression.

## Log

- 2026-11-12: Closed. `check_shape` refuses only solver parameters now.
  A member recurses by measure with or without a `self` marker, `mut self`
  included, and a self-call may be written as a method call on the
  receiver: `measure::method_calls_as_calls` respells `x.f(ā)` as the call
  `f(…, x, …)` before the lowering (the receiver at the `self` parameter,
  or the first explicit one), reading a typed receiver of another type as
  that type's member and an untyped one as the self-call. A claimed
  `mut self` call, `let p = x.f(ā);` or `x.f(ā);`, becomes the call bound
  once with `x` rebound to its `after` and `p` to its `value`, as the
  statement elaborates. Probes in
  `lib/_tests/std/core/decreases_unfolding_tests.hthr` (`count_down` with
  its unfolding, `count_named`, `count_first`, `push_down`, `peek` against
  another type's `peek`, `fill_down`, `fill_sum`, a negative control);
  docs/language/recursion/termination-measures-design.md §4 amended.

  What this does not give: the tail-call spelling the last paragraph asks
  for has no reachable shape. A receiver changes only in statement forms
  (a block in value position may not assign, and a value-position
  `x.f(…)` on a `mut self` method is refused), so a measured `mut self`
  method recurses from a statement `if`/`match`, never as the body's last
  expression. A statement form that assigns two locals (the receiver and
  a result) copies the call once per local:
  [[statement-form-join-copies-calls]]. A self-call in a statement
  declines the unfolding equation, as a `let`-bound call does for a
  function.
