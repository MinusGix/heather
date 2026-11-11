---
title: No ext, irrel or unfolding for a decreases arm with a mut self call statement before its self-call
status: open
labels: [frontend,elaboration,proofs,termination]
area: language
milestone: [nh-front]
created: 2026-11-11
updated: 2026-11-11
---

Found by U4 step 4c-3c of [[native-one-compiler]], making a loop over a
span a `runtime fn`. A `decreases` function whose arm stores through a
`mut self` method as a statement and then calls itself has no `f::ext`,
`f::irrel` or `f_unfold`:

```heather
fn fill(span: List<BitVec(8)>, length, i: BitVec(64)) → Mutated<List<BitVec(8)>, BitVec(64)> decreases length.sub(i).toNat() {
    match h: i.unsigned_lt_bit(length) {
        False => Mutated(span, i),
        True => {
            let mut span = span;
            span.put_within(length, i, BitVec::ofNat(0));
            fill(span, length, i.add(BitVec::ofNat(1)))
        },
    }
    on ?dec1 := { let below = bitvec_omega::unsigned_true(64, i, length, h); bv_omega };
}
```

The function checks, and `fill::body` is the body it should be (the
reflector reads the store off it). `fill::ext` is

> `fill` has no member `ext`: its access points are `rec`, `body`

and `fill_unfold` says why:

> no unfolding equation for `fill`: the generated `fill#ext` was refused
> (the kernel rejected `fill#ext`: NotConvertible. the type of this
> expression does not convert to `fill#body(__dec_a, __dec_g1, span, length,
> i, __dec_h1) = fill#body(__dec_b, __dec_g2, span, length, i, __dec_h2)`)

The same loop keeps all three in every spelling that has no `mut self`
call statement:

- `fill(span.with_byte_within(length, i, v), length, i.add(…))`, the store
  in the argument;
- `fill(List::put_within(span, length, i, v).after, …)`, the record by the
  method's qualified name;
- `let s2 = span.with_byte_within(…); fill(s2, …)`;
- `let mut span = span; span := span.with_byte_within(…); fill(span, …)`.

## Cause

The companions are a congruence proof written over the body's source
(`Respell::walk`, `crates/elab/src/measure.rs`). Its `Block` case
substitutes each `let` into the block's result, since a `let` is
zeta-transparent. A `mut self` call statement is a `let` of a name nothing
reads (`#seqN = \0mutated(span.put_within(…))`) whose effect is to rebind
its receiver (`elaborate_mut_call`, `crates/elab/src/statements.rs`): the
substitution drops the statement, the receiver in the self-call stays the
span before the store, and the proof is about a body with no store in it.
The kernel then refuses it against `f#body`, which has the store. The same
substitution is made where the walk reads a rendered `match`.

## Fix

Make the rebinding a substitution the walk can do: for a statement
`\0mutated(x.m(a))` substitute `x` by the call's record's `.after` (and a
`let p = x.m(a)`'s `p` by its `.value`) in what follows. That needs the
record of a marked call as an expression: the marker applied to the call,
elaborated by `infer_mut_call` wherever an expression is, where today it is
read in statement position only. (A block that keeps the statement around
each side instead does not survive the later substitution of `let mut x =
e`, which does not know the statement rebinds `x`.)

## Why it matters

A measured `runtime fn` is proved from `f::ext` and `f::irrel`, for a
function that writes a span as for one that reads
(`runtime_span_measured`, `lib/native/runtime/runtime.hthr`). The statement
form is how a store in a loop is naturally written, and how a loop that
calls another function that writes must be written unless it names the
callee by its qualified name. Until this is fixed the generator refuses
such a loop with a message that points here, and the probes
(`lib/_tests/native/runtime/runtime_span_tests.hthr`) write their loops
with the store in the self-call's argument.

Related: [[decreases-no-companions-nested-match-calls]] (a branch under
the arm loses the companions too, for a different reason) and
[[decreases-self-parameter]].
