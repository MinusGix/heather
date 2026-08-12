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
- 2026-08-12: Two rails measured by round A (2026-08-12, docs/certgen-cert-expression-design.md): (1) A Wf-LOWERED INDUCTIVE FIELD IN A DATATYPE COSTS 163x -- the first Cert draft carried rest/after: Ir fields, faithful to the kit lemmas' argument lists, and elaborated in 163 CPU-s; dropping them (the chain is its own IR -- the sub-certificate carries what the sub-Ir said, and the renderer prints the region off the sub-certificate, where the walker->closure renumbering already happens) gave 1.0 s. A single match on the Ir-carrying Cert was 4-7 s, a nested one 25-46 s. Rule of thumb: do not embed a Wf-lowered inductive as a field of another inductive that library code will match on; carry what you need of it, not it. (2) THE FOLD'S EVALUATION IS ~3.5 CPU-s PER GENERATED FUNCTION on top of the transcriber, which pushed the certgen.rs binary past the per-process ulimit -t 300 (the killed test truncated the suite total rather than failing loud -- the scripts-test-fail-fast lesson's cousin). Fixed with the free lever: the perturbed-library controls now live in certgen_controls.rs and the fold's control in certgen_cert.rs, three rails instead of one, free because each control builds its own elaborator anyway.
- 2026-08-12: Fast-lane drift, measured post-round-A (2026-08-12): scripts/test --fast is ~4 min wall, and CLAUDE.md's '~30s' was stale BEFORE this round -- the perturbed-library controls have been paying a 52-branch shell elaboration each since they landed. Per-binary, fast lane: certgen 90 s (in_language_transcriber, now also elaborating certgen_cert.hthr and running the ~3.5 s/fn fold for its positives), certgen_cert 92 s (the fold control: two sessions, each with a shell), certgen_controls 36 s, everything else noise. THE LEVER, recorded not pulled: the three mutation controls are kernel-refusal acceptance tests -- nothing an inner loop iterates on -- and adding their test names to scripts/test's --fast skip list would cut ~128 s, leaving in_language_transcriber's 90 s as the honest floor of a fast lane that still checks the generator at all. Pulling it changes what a green --fast means for anyone touching lib/certgen*, so it is a user/coordinator call, filed here.
