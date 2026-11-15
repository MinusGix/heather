---
title: The span reflector refuses another computation called last; record η makes that pin a conversion
status: open
labels: [runtime, reflection]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-14
updated: 2026-11-14
---

A `runtime fn` over a span must end in `Mutated(span, value)`, in a
`match` on a `Bool` whose arms do, or in its own call
(`lib/native/runtime/rt_file_reflect.hthr`, the refusal "a function over a
span ends in …"). Ending in a call of *another* computation, `g(span, …)`,
is refused, and `docs/native/native-one-compiler-design.md` gave the reason as "the
kernel has no η for records, so the pin could not be a conversion".

That reason is false. A record lowers to the Σ spine of its tag, its fields
and `Unit`, the kernel has η at all three, and `Mutated(c.after, c.value) = c`
is `refl` for any `c`, a call included
(`lib/_tests/lang/record_eta_tests.hthr`, 2026-11-14). The four hand
`eta` lemmas the library had (`Sha2Feed::eta`, `Ending::eta`,
`Env::with_own_words`, `FTm::mutated_eta`, the last emitted by the span
measured generator) were removed in the same round.

## What to do

Reflect a body that ends in a call of another computation as that call's
`.after` and `.value` rebuilt (the shape the reflector already reads), and
let the pin convert by η. Then a writing function can delegate its tail to a
helper without binding the result first.

## Done when

A `runtime fn` ending in `g(span, …)` for a computation `g` of the program
compiles and pins, with a probe in `lib/_tests/native/runtime/`, and the
refusal's message no longer lists the restriction.
