---
title: A mut self method's tail if/match cannot update the receiver in an arm (and asks for a motive)
status: closed
labels: [frontend,imperative,effects,native]
area: language
milestone: [lang-sequencing]
created: 2026-11-12
updated: 2026-11-12
---

A `mut self` method whose body ends in an `if` or a `match` cannot update its receiver in an arm, and the refusal it gets names something else (2026-11-12):

```heather
record Counter { n: Nat, log: List<Nat> }

fn Counter::tick(mut self c: Counter, by: Nat) → Nat {
    c := Counter(c.n + by, Cons(by, c.log));
    c.n
}

fn Counter::tick_all(mut self c: Counter, m: Nat) → Nat decreases m {
    match m {
        Zero => 0,
        Succ(k) => {
            c.tick(k);
            c.tick_all(k)
        },
    }
}
```

> error: `match` in inference position needs a motive: `match e as λ z => T { … }`

The same without the recursion (an arm that is `{ c.tick(k); k }`), and for `if`. Two things are stacked:

1. **The body's end is bound before the receiver is returned.** `block_body` (`crates/syntax/src/parser.rs`) turns the body's result `e` into `let #value = e; Mutated(c, #value)`, with no annotation, so a tail `match` stands in inference position although the function's result type is written two lines above it.
2. **An arm of that `match` is a block in value position**, so `c` is not its to update. Give the `match` a motive and the second refusal shows: "`tick` is a `mut self` method, so it updates its receiver, and `c` cannot be updated here". `c := …` in the arm is refused in the parser for the same reason.

What works today is the statement spelling, which is not a tail call and assigns two locals, so each arm's calls are copied once per local ([[statement-form-join-copies-calls]]):

```heather
fn Counter::tick_stmt(mut self c: Counter, m: Nat) → Nat {
    let mut r = 0;
    match m {
        Zero => {},
        Succ(k) => {
            c.tick(k);
            r := k;
        },
    }
    r
}
```

or threading the receiver by hand, which is what `lib/native/crypto/sha256_block.hthr`'s loops do (`let mut ctx = ctx; ctx.put_within(…); sha256_take_block(ctx, …)` under a `Mutated<List<u8>, u64>` result), and why they are not methods ([[sha256-context-type]]).

## Proposed

The end of a `mut self` body is where the receiver is returned, so a branch there returns it per arm: the parser pushes the `Mutated(c, ·)` wrap into the arms of a tail `if`/`match` (and through a tail block), as `wrap_ret_leaves` already does for the `return` leaves of a loop (`crates/syntax/src/imperative.rs`). Each arm is then a `mut self` body of its own: `let mut c = c;` at its head, its statements, `Mutated(c, value)` at its end. The `match` is checked against the declared result, so no motive is asked for.

To settle while building:

- **A tail call on the receiver stays a tail call.** `c.tick_all(k)` at an arm's end lowers to `let #tail = c.tick_all(k); Mutated(c, #tail)`, which is the call itself up to the record's eta. The generator recognises a loop by the function's own call in tail position (`lib/native/runtime/runtime.hthr`), so either the elaborator emits the bare call when a claimed call is its block's whole result and the callee is a `mut self` method with the same receiver type, or the reflector reads the eta-expanded form. The first is the one a `decreases` companion can follow too.
- **An equation-binding match** (`match h: e { … }`) keeps its binder; the wrap does not touch the scrutinee.
- **The message**, for where the lowering does not apply (a non-tail `match` whose arm updates the receiver): the receiver refusal, not the motive one.

## Done when

`Counter::tick_all` above elaborates, with `.after` and `.value` probes at a neutral receiver beside the `mut self` probes of `lib/_tests/std/core/imperative_statements_tests.hthr`, and a `runtime fn` loop written as a `mut self` method on its span certifies (`lib/_tests/native/runtime/runtime_loop_tests.hthr`), so the SHA-256 loops can be methods.

## Log

- 2026-11-12: Built on PR #551 as proposed, in three parts (docs/sequencing-surface-design.md §19). (1) A branch that ends a block updates the block's mutable locals in its arms: `lower_block` re-lowers each arm of the result `if`/`match` with those locals in scope (`claim_tail`, `crates/syntax/src/imperative.rs`), names an arm's pattern or equation binds excluded. (2) A `mut self` body that ends in a motive-less branch one of whose arms updates the receiver returns the receiver per arm (`Parser::receiver_end`); a branch whose arms leave it alone is `Mutated(c, match …)` as before, and the end value now stands in the record, so it is checked at the declared result and a tail `match` asks for no motive. (3) The method's own call on its receiver at the body's end or a tail arm's is the whole result (`MUTATED_WHOLE`): the elaborator reads it as the call, so structural recursion, a `decreases` companion and the generator's loop rule all see a tail call. Another method's call there is bound and taken apart as before, which keeps every existing method's term and the generator's end rule ("ends in `Mutated(span, value)`") as they were. Probes: `Counter::tick_some`, `tick_pick`, `tick_down` and the negative control `tick_inner` in `imperative_statements_tests`; `Counter::fill_all`, `fill_carry` and the refused `fill_up` in `decreases_unfolding_tests`; `List::fill_all` in `runtime_span_tests`, whose program is `fill_from`'s by `refl`. `lib/native/crypto`'s loops are methods on the span, the assembly unchanged. Left open, each where it belongs: an inner (non-tail) branch that updates the receiver is still the receiver refusal; a method cannot be exported ([[sha256-context-type]]).
