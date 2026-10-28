---
title: Preserve arithmetic certificate DAG sharing through elaboration
status: closed
labels: [proofs,elaboration,arithmetic,performance]
area: tactics
created: 2026-08-27
updated: 2026-10-28
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
- **[[persistent-certified-fact-cache]]** owns persisting canonical sequents
  across processes; this issue owns only sharing within one reconstructed
  certificate.

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
- 2026-09-25: The plan's "prefer scoped local proof bindings" does not preserve a DAG today. A surface `let` is an alias, and the kernel gate, shifts under binders and the module image all walk the result as a tree: a chain where each let uses the previous twice costs 2^k ([[proof-let-substitution-cost]], 2026-09-25). A local binding shares only once that issue's fix lands (a kernel `let` or a typing memo on node identity); a β-redex binding shares today but is opaque.
- 2026-09-25: `have` (docs/have-design.md, 2026-09-25) is the local binding that shares today: opaque, so the kernel checks each bound derivation once. A reconstructor can emit its DAG nodes as `have`s in topological order. Derivation nodes are never unfolded, so the opacity costs nothing ([[proof-let-substitution-cost]]).
- 2026-10-28: Landed: CutSat's certificate is one `have` per reachable node, in topological (id) order, inside the block of the node's split-case scope (`crates/elab/src/cutsat_cert.rs`); nothing re-enters Omega. Pugh's nightmare is kernel-checked end to end under the normal runner as `omega_tests::cutsat_pughs_nightmare`; its cost is now dominated by elaborating the certificate, then the gate, with the search negligible. Ordinary Omega's own certificate is not converted; that is no longer this issue's acceptance. Closing.
