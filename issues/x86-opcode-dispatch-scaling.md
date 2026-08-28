---
title: Separate cheap opcode classification from expensive decoding evidence
status: closed
labels: [x86,performance,proofs]
created: 2026-08-28
updated: 2026-08-28
---

The direct decoder currently recognizes supported opcodes through a linear
chain of evidence-producing byte equalities.  The chain itself is cheap and
scales linearly; what is expensive is that every successful arm immediately
constructs `ByteDecode`, forcing the kernel to check a concrete
`DecodesInstruction`/`RrEncoding` proof.  Completeness specializations then
revisit the decoder at each supported opcode.

With the original five opcodes and no general completeness layer, the x86
module checked in about 15 seconds on the debug test path. After adding the
constructive completeness layer and four `SUB`/`CMP` opcodes, it checks in
about 42 seconds; the focused consumer is about 52 seconds. These figures mix
both changes and are diagnostic measurements, not benchmark thresholds.

## Acceptance

- Separate byte classification from semantic evidence with a finite opcode
  descriptor.  The classifier should carry only the byte equality and should
  remain close to the measured cheap dependent-dispatch control.
- Interpret a classified opcode and certified operands through one soundness
  function/theorem, so completeness specializations consume descriptor laws
  instead of normalizing the whole decoder chain.
- Preserve `ByteDecode` soundness and `decode_instruction_complete`.
- Keep unsupported opcodes distinct from malformed operand bytes.
- Measure module-only and focused-consumer checks before and after, and add a
  multi-opcode growth regression rather than baking these host times into CI.
- Do not raise kernel fuel or cache limits to hide the term shape.

## What it assumes from elsewhere

- **[[x86-direct-bitfield-decoder]]** owns direct operand extraction and
  completeness. This issue changes only opcode classification/proof sharing.

## Log

- 2026-08-28: Filed from the `SUB`/`CMP` round when nine supported opcode
  branches made the repeated completeness-dispatch cost visible.
- 2026-08-28: Attribution corrected the initial hypothesis.  Module-only
  elaboration is about 41.65 s: 29.86 s in the kernel gate and 11.79 s in the
  frontend.  `decode_opcode_from_operands` alone is about 9.57 s (8.84 s
  kernel); `decode_opcode_complete_for` is about 3.47 s, and the nine opcode
  completeness specializations total about 8.7 s.  The cost is therefore not
  fuel exhaustion and not primarily elaborator search.

  A reduced dispatcher returning `Bool` scales from 1.8 ms at one arm to
  32.3 ms at seventeen.  The same dispatcher returning a dependent record
  carrying the equality proof scales from 4.3 ms to 58.5 ms.  At nine arms it
  takes only 30 ms.  Replacing that small payload with the real x86
  `ByteDecode` changes the series to roughly 0.87/2.81/6.27/7.71/9.98 s at
  1/3/5/7/9 arms, overwhelmingly in the kernel.  Thus nested `eq_dec` and
  dependent match lowering are both sane; each x86 semantic payload is itself
  expensive and the table multiplies it linearly.

  Value-machine counters agree: the direct declaration opens 297,731
  conversion arenas and performs 10.76 million type-cache lookups (10.41
  million inserts, with individual queries reaching the 16K cap), versus
  73,166 arenas and 1.15 million type lookups for
  `decode_opcode_reference`.  The compact emitted bodies are similar in size,
  so this is repeated normalization of dependent/global types, not a
  quadratic generated term.

  Two source-level shortcuts were measured and rejected.  A generic
  `package(bytes, instruction, decoding)` boundary is neutral-to-worse because
  every call must still check its concrete `DecodesInstruction` argument.
  Destructuring `DirectOperands` once rather than projecting its four fields
  is also worse (about 11.73 s at nine arms).  Do not repeat either experiment,
  and do not widen kernel fuel or caches: the next warranted implementation is
  the descriptor/classifier split above.  It leaves the unavoidable semantic
  proof linear once, but prevents every downstream theorem from paying for
  the classification table again.

- 2026-08-28: A one-arm extraction showed that some of the semantic payload
  cost was avoidable kernel repetition after all.  In a single gate,
  `El`/`Sum` conversion at variables made 1,042 calls for only 98 exact
  judgments (one repeated 48 times); `Sigma` projection families showed the
  same effect.  [[kernel-gate-conversion-reuse]] landed conservative positive
  reuse at the typing seam.  A same-session comparison against `e4c7c7c`
  moved this module from 30.590 s to 28.372 s and its kernel phase from
  23.004 s to 21.050 s.  Reflexivity alone measured 30.182/22.569 s, so the
  reuse rather than arena avoidance owns most of the improvement.

  The descriptor/classifier split remains worthwhile: the retained cache is
  deliberately cross-head, shallow-keyed, gate-local, and bounded, while the
  source design prevents downstream theorems from replaying the semantic
  table at all.  Broad reuse was rejected after it exposed linear candidate
  scans; the apparent frontend regression against the saved benchmark was a
  stale baseline (an untouched same-session build took 41.96 ms in the deep
  kernel case, versus 27.77 ms with memo lookup disabled).

- 2026-08-28: LANDED. `std/certified_lookup` now provides a reusable finite
  table whose rows certify `Valid(key, value)`, a plain `Option` classifier,
  and one generic `lookup_sound` theorem. The deliberately plain result is
  important: a prototype returning a dependent proof-carrying result made the
  two-opcode x86 module slower (31.700/23.202 s total/kernel), while separating
  computation from the soundness theorem stayed near baseline
  (29.434/21.105 s) and avoids transported-proof definitional-equality costs.

  The x86 decoder now classifies through a nine-constructor `RrOpcode`
  descriptor and one certified table, then interprets that descriptor into
  `ByteDecode`. Nine opcode-specific decoder completeness theorems and nine
  instruction completeness theorems collapsed to one match theorem at each
  layer. The x86 model is 71 lines smaller overall. Repeated all-nine module
  checks measured 29.584/18.942, 25.522/16.282, 32.331/21.015, and
  30.208/19.302 s total/kernel versus the same-session pre-round baseline of
  28.372/21.050 s. The robust claim is no kernel regression (with several
  materially cheaper repeats), not a hard host-time speedup; frontend timing
  remains noisy, and no fuel/cache limit changed.

  `scale/certified-dispatch` is the requested host-independent growth guard.
  It elaborates complete classifier/soundness/interpreter/completeness schemas
  at 2/4/8/16 rows and measured slope 1.31; CI accepts 0.95--1.65, the
  benchmark suite's ordinary +/-0.35 meaningful-drift band. The complete x86
  suite and the standalone generic-library controls pass, including malformed
  and unsupported byte boundaries.

- 2026-08-28: Post-landing cleanup replaced the classifier's hand-written
  convoy with equation-bearing `match`. A generic probe also confirmed that
  rigid abstract field types already infer values occurring only in the field;
  the unsafe-looking residue was split precisely. Partial syntactic progress
  suppressing a useful reduction retry is owned by
  [[argument-type-reduction-after-partial-inference]], while nominal source
  constructors hidden by shared kernel encodings are owned by
  [[implicit-value-inference-through-constructor-fields]].
