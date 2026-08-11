---
title: Reflection for analyzers: signatures (and bodies) the language can see, pull not push
status: open
labels: [metaprogramming,elaboration,design,frontend]
created: 2026-08-11
updated: 2026-08-11
---

Research direction from the transcriber round's user review (2026-08-11). Today the fragment's definition lives in two halves: Rust owns the signature check (arity, Nat-only — decided while peeling the Lam spine before marking), the library owns the body check (the walker's decline set). Fail-safe (disagreement yields declines or refused certificates, never wrongness) but a drift vector as fragments multiply: the halves are coupled only by the design doc and the cross-check.

**Cheap first step, no blockers:** a fn's signature is a closed concrete TYPE, and type-codes are already analyzable — ElimCodeTy and the eight ty_* branches the transcriber round defaulted. An analyzer taking sig: Code(g |- Ty)-shaped input could check Nat -> ... -> Nat itself with ty_pi/ty_nat arms. Small honest widening (the type motive stops being Unit, or a second match code over a Typ code), and a natural second dogfooding exercise after retire-rust-transcriber's freeze.

**The API shape: PULL, not push.** Not annotations stored per declaration ('the elaborator emits extra data for every fn') but reflection primitives an analyzer requests — 'this fn's type as code', 'this fn's marked body'. Two reasons: (1) it is exactly the interface the opaque-globals kernel round must define anyway (u^delta unfolding-for-analysis with its ch. 07 obligations), so designing the pull API Rust-side now means that round later replaces the implementation, not the interface; (2) it stays honest about staging — the elaborator is destined to be Heather itself (the thesis), at which point a pull API is just an ordinary metaprogram operation, no residual magic.

Related: generators-in-the-language blockers (1)-(3) (the kernel-round half), code-variable-analysis-api (the body-side data the same API hands over), certgen-transcriber-in-language-design sec. 5 (the phase split this dissolves).
