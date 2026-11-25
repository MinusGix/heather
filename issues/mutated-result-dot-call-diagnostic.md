---
title: A dot call of a plain-self function answering Mutated is refused as a mut self call, and under a projection the refusal is lost
status: open
labels: [frontend,diagnostics]
area: language
milestone: [none]
created: 2026-11-24
updated: 2026-11-25
---

Found by [[ownership-stores-and-keys]] (2026-11-24). `refuse_unthreaded_mut_call` (`crates/elab/src/dispatch/member.rs`) decides a callee is a `mut self` method by its written result head alone, so a function written with a plain `self` receiver whose result is `Mutated<S, R>` (`Store::alloc`, `Heap::alloc`, `Heap::grow` in the library) is refused at a dot call too. And when the call is the receiver of a projection, the refusal's message is lost:

```heather
record Counter { n: Nat }
fn Counter::tick(self c: Counter, k: Nat) → Mutated<Counter, Nat> { Mutated(Counter(c.n + k), c.n) }
theorem dotted(c: Counter): c.tick(1).value = c.n { refl }      // no field `value` here (and the receiver's type could not be inferred)
theorem qualified(c: Counter): Counter::tick(c, 1).value = c.n { refl }   // checks
```

Two things to settle:

- Whether a plain `self` receiver with a `Mutated` result should be read as a `mut self` method at all. The parser's desugaring knows which receivers were written `mut`; the dot call reads only the result head. A function that answers the record on purpose (a store's allocation, whose key is the `value`) is what the qualified spelling is for today, and the library writes it that way.
- Either way, the refusal should reach the user where it fires: a `.value`/`.after` on the call should say the call was refused and why, not that the receiver's type is unknown.

## Log

- 2026-11-25: Fixed with [[parameter-modes-residue]] (docs/language/sequencing-surface-design.md §24.4). Settled: **a plain `self` receiver with a `Mutated` result is not a `mut self` method**. Since [[ownership-parameter-modes]] every declaration records its receiver's mode, so `refuse_unthreaded_mut_call` and the statement forms (`elaborate_mut_call`, `mut_call_part`) read that (`Members::threads_receiver`, `crates/elab/src/dispatch/member.rs`) instead of the result head: `c.tick(1).value` answers the record as `Counter::tick(c, 1).value` does, also on a `let mut` local (`let r = d.split(2);` binds the record and leaves `d`), and the statement `d.split(2);` is refused as discarding its value. Where no mode is recorded (a local function) the result head decides as before. And the refusal reaches the user under a projection: a field read whose receiver is a call refused by the elaborator reports that refusal (`dispatch/member.rs`, the `args: None` branch). Probes: `split_dotted`, `split_on_local_open`, `split_statement`, `tally_projected` in `lib/_tests/std/core/parameter_modes_tests.hthr`. The library had no dot call that relied on the old reading (a grep of every plain-`self` function answering `Mutated`; the plain suite is the evidence).
