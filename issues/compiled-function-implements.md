---
title: State a compiled function as implementing its source function, not one argument list at a time
status: open
labels: [native,theorems,readability]
area: heather-in-heather
milestone: [hih-program-logic]
created: 2026-11-16
updated: 2026-11-16
---

A certificate proves `code.Computes(machine, 0, [a0, a1, a2], clamp(a0, a1, a2))` at open words (`lib/native/function_ir/function_ir_correct.hthr`, `docs/native/compiler-theorem.md`). "This code is `clamp`" is spread over a binder per argument and a list literal.

Wanted: `Prog::Implements(machine, f, spec)` taking the source function curried at the function's arity (built from `Spread` in `function_ir_compile.hthr`), with a lemma from the per-list `Computes` and back, and certificates stating `clamp_code().Implements(machine, 0, clamp)`. The README and the compiler-theorem doc quote that line.

Done when: the definition and both directions are in `function_ir_correct`, a probe states `clamp` this way, and `compile-x86`'s word certificates state it.

## Related
The other readability rounds on the compiler's theorem, from the same review (2026-11-16): [[words-as-unlent-spans]], [[span-certificate-statements]], [[stack-room-by-call-depth]], [[compiled-call-frame-rule]], [[optimizer-as-refinement]].
