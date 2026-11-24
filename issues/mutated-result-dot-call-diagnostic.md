---
title: A dot call of a plain-self function answering Mutated is refused as a mut self call, and under a projection the refusal is lost
status: open
labels: [frontend,diagnostics]
area: language
milestone: [none]
created: 2026-11-24
updated: 2026-11-24
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
