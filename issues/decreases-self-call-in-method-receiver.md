---
title: decreases: a self-call in a method call's receiver gets its obligation at the call's own arguments
status: closed
labels: [elaboration,termination]
area: language
created: 2026-11-12
updated: 2026-11-12
---

A `decreases` function whose own call is the receiver of a method call is refused, with an obligation no proof can meet. The same body with the method spelled as a function call checks.

```heather
import logic;
import bool;
import nat;
import list;
import bitvec;
import bitvec_nat;
import bitvec_omega;
import omega;

fn List::other(self xs: List<BitVec(8)>, n, k: BitVec(64)) → List<BitVec(8)> { xs }

fn after(span: List<BitVec(8)>, length, i: BitVec(64)) → Mutated<List<BitVec(8)>, BitVec(64)> decreases length.sub(i).toNat() {
    match h: i.unsigned_lt_bit(length) {
        False => Mutated(span, i),
        True => Mutated(after(span, length, i.add(BitVec::ofNat(1))).after.other(length, i), i),
    }
    on ?dec1 := {
        let below = bitvec_omega::unsigned_true(64, i, length, h);
        bv_omega
    };
}
```

```
error: this has type `toNat(length - (i + ofNat(1))) < toNat(length - i)`, but
`Succ(toNat(length - (i + ofNat(1)))) <= toNat(length - (i + ofNat(1)))` is expected here
   |         True => Mutated(after(span, length, i.add(BitVec::ofNat(1))).after.other(length, i), i),
   |                         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```

The obligation expected at the call is the measure at the call's arguments on both sides, `Succ(m(i + 1)) <= m(i + 1)`, where it should be `Succ(m(i + 1)) <= m(i)`. The hole's own proof has the right type, which is what the message says it has.

What narrows it:

- `Mutated(after(…).after, i)`, the projection alone, checks.
- `Mutated(List::other(after(…).after, length, i), i)`, the method as a function call, checks.
- `Mutated(after(…).after.other(length, i), i)` is refused, whatever the method's parameters are named (tried with `n, k` and with `length, i`).

So it is the method-call route with the self-call inside its receiver, not the projection and not a clash of names. A guess, not checked: the receiver is elaborated once to find the method and again as the call's argument, and the second elaboration runs where the measure's parameters are already bound to the call's arguments.

Seen on PR #551's branch with master's #579 merged (2026-11-12), with a plain `fn`; whether it predates #579 was not checked. Found while probing which loop forms `runtime fn` takes; nothing in the library is written this way, so it blocks nothing. The workaround is the function-call spelling.

Done when: the repro checks, with a probe in `lib/_tests/std/core/decreases_unfolding_tests.hthr`.

## Log

- 2026-11-12: Closed. Not the method route, and not BitVec: the dot-call
  receiver cache (`context::DotReceivers`,
  issues/method-chain-receiver-reinference.md) keyed a receiver by its
  source span alone, and the obligation `le_trans(Succ(e[ȳ]), e, …)`
  writes the measure twice at one span, once substituted. Inside a dot
  chain (the self-call in `.other`'s receiver) the cache registers every
  dotted receiver, so `length.sub(i)` was answered with its substituted
  twin `length.sub(i + 1)`'s inference. Any measure that is a chain of
  two method calls reproduces it (`decreases n.sub(i).sub(0)` over `Nat`).
  The key is now the span and a fingerprint of the expression; a span no
  receiver registered pays nothing extra. Probe `in_receiver` in
  `lib/_tests/std/core/decreases_unfolding_tests.hthr`; the context unit
  test checks a same-span twin is not shared.
