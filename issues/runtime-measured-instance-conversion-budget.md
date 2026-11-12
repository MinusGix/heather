---
title: A measured runtime fn's instance runs out of the conversion budget when its loop is the scanner's
status: closed
labels: [native,runtime-fn,performance,lexer]
area: heather-in-heather
milestone: [self-lexer,nh-library]
created: 2026-11-11
updated: 2026-11-12
---

Found by round E of [[native-one-compiler]], writing the scanner's token loop as a `runtime fn` over a span ([[native-library-exports-design]] §10, R3; [[self-lexer-linked]]). The loop is the one `lexer_tokens`' `Accepted::longest` is, with the source a span and the offsets words:

```heather
runtime fn scan_from(source: List<BitVec(8)>, length, state, i, last: u64) → u64 decreases length.sub(i).toNat() {
    match h: i.unsigned_lt_bit(length) && !(state.eq_bit(FAIL) || state.eq_bit(DEAD)) {
        False => scan_stopped(state, i, last),
        True => scan_from(source, length, scan_at(source, length, state, i), i.add(1), scan_last(state, i, last)),
    }
    on ?dec1 := { … };
}
```

(`scan_at` is `scan_step` at the span's byte; the one self-call is the arm itself, as [[decreases-no-companions-nested-match-calls]] asks, with the two exits decided after the loop.) The function and its companions check. The generator then fails:

> `runtime fn scan_from`: the generator failed: runtime: `scan_from`'s instance: an argument's type could not be compared with the expected type within the conversion budget (1048576 steps): the comparison ran out of fuel, which is not a mismatch

It is the `infer` of `Setup::compile_measured(…, guarded, …)` in `runtime_measured_instance`: the proof of `Fun::Guarded` (`sym` of `f::ext` at `g1`, `g2`) compared with its statement.

## What moves it

Probes over one loop shape, `(source, length, state, i, last)`, each a variation of the test and of the word passed for `state` (all in a scratch module importing `lexer_scan`; each takes about three seconds either way):

| test | `state` passed on | |
|---|---|---|
| `i < length` | `scan_step(state, i)` | checks |
| `i < length` | `scan_at(source, length, state, i)`, with `scan_last` and `scan_stopped` | checks |
| `i < length && !(state = FAIL ∨ state = DEAD)` | `state.add(1)` | checks |
| the same | `scan_accept(state)`, `step_stop(state, i)`, `scan_family(state, i)`, `step_names(state, i)` | checks |
| the same | `scan_step(state, i)` | **out of budget** |
| `i < length && !(state = DEAD)` | `scan_step(state, i)` | checks |
| `i < length && !(state.bor(FAIL) = FAIL)` (the state read once) | `scan_at(…)`, with `scan_last` and `scan_stopped` | **out of budget** |
| the same, the state stepped one pass early so the test reads a parameter the pass was handed | | **out of budget** |
| `i < length` | `scan_step(state, byte)`, and `match scan_accept(state).eq_bit(0)` in the last argument | **out of budget** |

So no one construct is refused. The cost follows the size of what is called with the state (the automaton's step is a program of two dozen functions; a family alone is fine) times how much of the body reads a value made from it, and the budget is passed between one read and two. That reads as the comparison unfolding the callee at open arguments and walking the result, once per use, where the two sides name the same call.

## What it blocks

`scan_token` as one linked function, so the scanner's loop stays Rust's (`crates/linked/src/scanner.rs`'s `munch`) and `self-lexer-linked` stays where it is. Any loop that carries the state of a large step function has the same shape: a hash's rounds over a block will.

## Where to look

- What the comparison is, first: which side holds the callee unfolded (the reflection's `tail_sem` at the body, or `f::rec` at the next arguments), by the conversion-miss sampler or by stack samples, before guessing.
- Whether `Guarded` can be proved without the comparison seeing through the callees: the world's entries are the functions themselves, so a call of one is the same application on both sides, and a comparison that tried the spines before unfolding would stop there.
- The same proof for a loop lent a span goes through `Setup::guarded_span`; whether the family over spans adds its own copy.

## Log

- 2026-11-12: Cause found and removed, in the library. The comparison that ran out was not of the Heather body with its reflection (that one is small): it was of the reflection with itself at two spellings of one file. `Setup::guarded_span` gave `Fun::Guarded` at the world `w.at(callees, [b.span(0)])`, `Setup::compile_measured` wants it at `w.at(callees, b)`, and the two convert only by walking the body's meaning (`tail_sem`) node by node: the environment at every binder, the callee table at every call, each word's type unfolded on the way. So the cost was the body's size times what it calls, a slope and not a cliff, and the scanner's loop (two connectives in the test, the automaton behind the step) was the first past the budget. Measured with a counter of conversion steps per host comparison (`tools/host-conversion-ladder.patch` in the project folder, not in the tree); the table above reads as that slope, and its "checks" rows at the larger shapes were replays of images, which is why it looked like a cliff.

  The fix: `Fun::GuardedBy` (rt_loop), the family with two indices. Its worlds are indexed by the file and its recursion is keyed by the span, so `Fun::guarded_by` answers `Guarded` at the file's own world and nothing is compared across the two spellings but the function at its head. `Fun::GuardedAt` is the keyed family whose key is its index; `Setup::GuardedSpans` and the generator's `runtime_measured_instance` use the keyed one (the first binder of a lent loop's statement is the file, the ih binds a span). The scanner's loop as first written is accepted with room to spare, and no elaborator or kernel change was needed. Design: docs/native-one-compiler-design.md §2.3.

  What this issue's "where to look" asked beyond that (a comparison that tries spines before unfolding) was not the problem: conversion already does.
