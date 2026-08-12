---
title: Certgen harness and kit costs: recorded levers if either grows
status: open
labels: [elaboration,performance,compiler,testing]
created: 2026-08-02
updated: 2026-08-12
---

Accumulator issue (perf convention: observations filed small and triggered,
one deliberate round per session). Two measured numbers from the v2 round
(2026-08-02), both fine today, with levers recorded for when they are not:

- **The two double-j kit lemmas** (\`letcall_conv\`/\`letmatch_conv\`) cost
  ~9s release EACH to elaborate — the step_mono term-size price (two
  interpreters in scope under a rewritten scrutinee), paid once per
  elaborator that loads them: once in \`lib/ir_v1.hthr\`'s full check
  (51s -> 70s release) and once per certgen-harness elaborator.
  Levers: an inversion record a la BindInv for the k_letcall/k_letmatch
  fragments (BindInv retired three convoy motives at -12.6%); elaborator-
  computed generalized motives ([[ih-generalization]]).
- **The certgen harness** is ~108 CPU-s in one elaborator: ~50s support
  prelude (step_mono + the kit re-elaborated), ~50s the five emissions.
  Scales linearly-ish with emission count, so a v3 that generates dozens of
  functions blows past the per-process rail. Levers: an elaborator
  snapshot/clone so the prelude is paid once per suite rather than per
  test binary; trimming step_mono's cost (above); checking emissions via
  the release CLI against a concatenated file instead of debug-profile
  in-process elaboration.

Trigger: certgen harness > ~200 CPU-s, or a third consumer of the kit
lemmas' elaboration cost appears.

## Log

- 2026-08-11: New rail entry (2026-08-11, signature-reflection round): the second match-code shell (check_sig) adds a second 52-branch rec_ga check per elaboration of lib/certgen_code.hthr and its registration re-elaboration. Small next to the transcriber shell's ~9s (the SigOut motive is tiny) and the full suite absorbed it (1450 green), but this file is the suite's second-most-expensive binary and each new analyzer shell adds another gate — the lever if it grows is shared-skeleton amortization, same family as schema-construction-caching.
- 2026-08-12: Rail entry from the route-1 spike (2026-08-12, memo sec. 5/7): IF round B (staged Psi emission) is ever scheduled, its cost shape is one Psi definition plus one Psi theorem PER IR INSTRUCTION where today the whole certificate is one theorem -- a Psi-growth and readability question, not a soundness one (every entry individually kernel-checked). The spike's measured baseline for the adjacent rider: the real-kit ret_cert addition to ir_v1.rs's full-library test was free (no match code, no 52-branch rec_ga gate; binary at 58.7s wall, inside the recorded envelope).
