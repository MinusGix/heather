---
title: Preserve arithmetic certificate DAG sharing through elaboration
status: open
labels: [proofs,elaboration,arithmetic,performance]
created: 2026-08-27
updated: 2026-08-27
---

Materialize shared arithmetic derivations once instead of recursively spelling
their proof source at every use. CutSat already returns a typed derivation DAG,
but its first kernel reconstruction route emits nested continuation source; a
large Cooper tree such as Pugh's nightmare consequently crosses the runner's
memory/time ceiling despite its small reachable search DAG.

The facility should be useful to ordinary Omega and future arithmetic tactics,
not a Pugh-specific compression. Prefer scoped local proof bindings where all
dependencies are in scope; introduce generated declarations only where a local
binding cannot preserve the DAG. Generated names are private implementation
details, and every materialized proof still passes the ordinary kernel gate.

## Acceptance

- Reconstruction consumes a reachable derivation slice in topological order
  and emits each shareable node once per dependency scope.
- Pugh's nightmare is kernel-certified end to end under the normal test runner.
- Certificate source size and kernel-check cost have deterministic/coarse rails
  owned by [[omega-performance-telemetry]].
- Sharing never memoizes an elaboration failure or bypasses the final kernel
  check.

## What it assumes from elsewhere

- **[[cutsat-linear-integer-arithmetic]]** owns CutSat search and the initial
  kernel reconstruction route.
- **[[omega-performance-telemetry]]** owns arithmetic scaling measurements.
- **[[proof-scale-abbreviations]]** owns user-facing abbreviation syntax; this
  issue may use existing internal/local bindings without deciding that syntax.

## Log

- 2026-08-27: First sharing slice landed locally. Cooper case bodies are typed
  local closures rather than payloads nested directly under dependent matches.
  More importantly, reconstruction now hoists reachable assumption-only real
  projections, canonicalizes equal affine conclusions across distinct CutSat
  node IDs, binds assumptions once at the hoisted scope, and threads Cooper cut
  evidence instead of asking Omega to rediscover it. On Pugh's
  nightmare the deterministic structural rail moves from 30,191 bytes / 92
  recursive linear branches / 73 learned-inequality wrappers to 16,592 / 28 /
  9. This is substantial but not acceptance-complete: the remaining 19
  terminal divisibility/bound closures plus dynamic projections still exceed
  the 300-second end-to-end runner ceiling, even with a warm declaration cache.
  Next slice: reconstruct those terminal linear certificates directly or
  materialize them as named parameterized proofs; do not hide the gap with an
  ignored/slow test.
