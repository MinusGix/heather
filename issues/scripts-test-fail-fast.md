---
title: scripts/test inherits cargo's cross-target fail-fast, hiding co-failing tests
status: closed
labels: [testing,tooling]
created: 2026-08-06
updated: 2026-08-09
---

Noticed during [[branch-telescope-type-motive-level-slots]]'s polarity
verification: a mutation that broke both the in-crate `rec.rs` check and
the `tests/typing.rs` use-site test *looked* like it broke only the first,
because cargo aborts remaining test targets once one target fails. The
second failure had to be verified separately. For mutation-style polarity
work — now an established pattern in this suite — that turns "two
independent observers caught it" into "one did and the other is unknown".

Options: pass `--no-fail-fast` in `scripts/test` (honest, but a red run
then always pays for the slow acceptance targets too); pass it only in
`--fast` mode (where the expensive targets are already skipped — probably
the right cut); or leave it and note the behaviour in the script's header.

## When

The next time a polarity check or red-suite triage is misread because of
the abort; or the next `scripts/test` edit for any reason.

## Log

- 2026-08-09: Implemented the fast-lane cut: `scripts/test --fast` now passes
  Cargo `--no-fail-fast`, so all test binaries run and report their failures
  while the two expensive whole-library acceptance tests remain skipped. The
  full lane deliberately retains Cargo's fail-fast behavior and its existing
  final-verification cost. The Cargo flag is kept before caller arguments so
  it cannot accidentally land after the test-harness `--` separator.
