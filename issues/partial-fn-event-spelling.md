---
title: "partial(E) fn: spell E's commands the same in a loop's pass and in a body over its calls"
status: open
labels: [sequencing,coinduction]
area: language
milestone: [lang-sequencing,nh-effects]
created: 2026-11-06
updated: 2026-11-06
---

Since [[partial-fn-tail-iter]], a `partial(E) fn` has two shapes
(docs/partial-functions-design.md §10 item 4):

- **tail-only** (no self-call under `<-`): `f#body` is a pass over `E`
  itself, so a command is `CoTree::trigger(E, c)`;
- **with a bound call**: `f#body` is over `Events::sum(Events::calls(A, B), E)`,
  so a command is `CoTree::trigger(Events::sum(Events::calls(A, B), E), Inr(c))`.

Adding one bound call to a function therefore changes how every command in
it is written, and a body with a bound call cannot bind another computation
over `E` (or another `partial fn`'s `Partial(X)`) without a
`CoTree::translate` into the sum. A pass can.

Fix: in a body over its calls, accept a computation over `E` where the
sum's carrier is expected, injected by `translate` along `Inr` (the
lowering knows both event families, so it can insert the translation at
each bind, or a carrier coercion could), so that both shapes are written
over `E`. `rec_sound`'s safety proofs then meet `translate` at those binds
and want a `safe_translate` rule (a translated tree makes no calls).

## Done when

The same `partial(E) fn` source, with `CoTree::trigger(E, c)`, elaborates
whether or not it has a bound call, and a probe in
`lib/_tests/std/itree/partial_fn_tests.hthr` proves a bound-call body with
an `E` command safe.
