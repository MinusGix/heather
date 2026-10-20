---
title: "Grow lints as conservative checks with explicit style profiles"
status: open
labels: [tooling,lint,diagnostics,design,ergonomics]
area: language
created: 2026-08-22
updated: 2026-09-16
---

Heather now has stable lint identities, a registered source-AST lint pass, and
one semantic lint emitted from the pattern compiler. Grow that into a small
deliberate lint set rather than an accumulation of warnings nobody can silence.

The default profile should remain unusually conservative: a warning should
expose dead/unchecked structure, suspicious resolution, or a rewrite Heather
has mechanically verified. Project style belongs in explicit profiles. The
first such customer is the standard library, which wants consistent Unicode
and canonical surface spellings without making ASCII aliases uncomfortable in
ordinary user programs.

Profile selection belongs above elaboration. The CLI can select the stdlib
profile when checking its recognized standard-library target, or a checked-in
lint configuration can request it; the elaborator should not guess policy from
a source filename. All profiles still emit the same stable `Lint` identities
through the same warning channel.

## Proposed sequence

1. [[lint-unused-imports]] adds a module-finalization phase and semantic-use
   accounting.
2. [[lint-redundant-match-motive]] attacks the current largest proof-surface
   cost with a verified elaboration result.
3. [[lint-unused-pattern-binders]] catches dead constructor fields and
   induction hypotheses without warning on ordinary constant functions.
4. [[lint-operator-fallback]] exposes notation that resolved through a
   compatibility fallback rather than an intended designation.
5. [[lint-unnecessary-explicit-elaboration]] considers removable type
   arguments and `@` only when speculative elaboration proves the same result.
6. [[lint-stdlib-unicode-spelling]] is the first profile-only written-form
   rule.

Already-owned work stays with [[lint-match-function-application]],
[[lint-tight-negation-spacing]], [[lint-trivial-argument-slot]],
[[lint-unused-local-bindings]], [[lint-vacuous-match]],
[[lint-sequent-binder-intro]], [[lint-proof-apply]],
[[stdlib-surface-style-lint]], and [[warn-bare-eq-no-effect]]. Optional advice
and the distinction between activation level and style profile belong to
[[lint-review-only-mode]].

## Acceptance

- Lints declare whether they belong to the conservative default or a named
  style profile; this policy is independent of diagnostic wording.
- The stdlib profile is reproducibly enabled by its ordinary check workflow
  without matching arbitrary user paths named `std`.
- A profile can add warnings without changing whether a source file checks or
  whether the bare success line is printed.
- Every new lint has positive cases, semantic false-positive controls, and a
  library census before rollout.
- Per-site suppression is added only when a genuine intentional occurrence
  needs it; profiles are not used to hide a noisy recognizer.

## Log

- 2026-08-22: Filed from the first post-registry lint review. The sequencing
  favors infrastructure-paying rules first and records the user decision that
  Unicode preference is a stdlib policy, not a language-wide judgment on
  supported ASCII aliases.
- 2026-08-22: The first implementation batch added explicit profiles, a shared
  once-per-file token/span context, a total item/AST walker, and structured
  fix data. It closes [[lint-tight-negation-spacing]] and
  [[lint-stdlib-unicode-spelling]] and lands the n-ary-call half of
  [[stdlib-surface-style-lint]]; the semantic roadmap items remain open.
- 2026-08-22: The second batch closed [[lint-unused-pattern-binders]] and
  [[lint-operator-fallback]], and landed the kernel-verified checking-position
  portion of [[lint-redundant-match-motive]]. The shared warning fix format now
  supports token-completed multi-token deletions as well as single-token
  replacements.
- 2026-08-22: The clean-stdlib review added bounded owners for unused local
  bindings, vacuous matches, proof-lambda `⊢` spelling, and a future
  proof-`apply` readability lint. It also split optional review advice from
  always-on warnings rather than treating removable annotations as defects.
- 2026-09-16: Some lints determine their own fix ("write `_` instead", "write `[…]` instead"); [[lint-mechanical-fix-mode]] owns applying those, and assumes only that fixability is a property of the individual lint rather than of a profile.
- 2026-09-17: The first review-mode lint: [[lint-redundant-match-motive]] runs only under `heather check --review` (`Elaborator::set_review_lints`), because its recognizer re-elaborates and kernel-checks every written motive and was 45% of `lib/ir_v1.hthr`'s check and 20% of the x86 model's while finding nothing on a library that had already adopted its findings. The rule that falls out: a lint whose recognizer is a second elaboration of the item is review advice, never an always-on warning.
