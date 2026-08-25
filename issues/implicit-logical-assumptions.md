---
title: "Implicit logical assumptions: ordinary evidence, scoped axiom fallback, and classical bundles"
status: open
labels: [frontend,elaboration,traits,logic,proofs,design,ergonomics]
created: 2026-08-24
updated: 2026-08-24
---

Make logical assumptions ordinary proof or class parameters that can be
filled ergonomically without hiding their place in a theorem's type. The
initial customer is a theorem parameter such as `Or<P, Not(P)>`: a local or
specialized constructive proof should win, while an explicitly scoped axiom
may serve as the fallback and create provenance at the caller that selected
it.

The full design record is
`docs/implicit-logical-assumptions-design.md`. It also fixes an important
boundary with [[decide-class]]: classical excluded middle is opaque and cannot
implement Heather's computational `Decide<P>` contract. Logical evidence and
reducing decision procedures remain different capabilities.

## Acceptance

- Choose how an ordinary logical-evidence parameter opts into resolution,
  accounting for today's distinction between `{implicit}` and `:= infer`.
- Extend resolution with a bounded, scoped axiom fallback; do not search every
  proved global.
- Preserve local-first selection and transactional dependency collection.
- Show the same conditional theorem used once with axiom-backed evidence and
  once with constructive evidence, with provenance attached only to the
  former caller.
- Show a narrow logical-evidence class derived from a broad classical
  capability without registering classical excluded middle as `Decide<P>`.
- Settle whether `assuming classical` is section sugar, a scoped instance
  installation, or both; it must elaborate to ordinary parameters rather than
  enable a global logic mode.
- Add resolution diagnostics that expose the selected assumption provider.

## What it assumes from elsewhere

- **[[axiom-provenance]]** owns explicit axioms and the committed dependency
  graph. Assumed here: selecting an axiom term through resolution records the
  ordinary global edge.
- **[[decide-class]]** owns the reducing `Decide<P>` contract. Assumed here:
  opaque classical evidence does not satisfy it.
- **[[scoped-instance-installation]]** owns named instance activation at
  module and block scope. Assumed here: a classical bundle may use that
  mechanism, but importing an axiom does not globally activate every derived
  instance.
- **[[traits]]** owns solver parameters and checked instance resolution.
  Assumed here: locals beat the registry and rejected candidate trials are
  transactional.

## Log

- 2026-08-24: Filed from the axiom-provenance follow-up discussion. User
  direction: the assumption should primarily be another argument, with
  implicit resolution able to use a scoped global axiom; typeclasses are the
  natural layer for recurring structure, and a special type should be able to
  discharge a narrow requirement constructively even in a classical context.
- 2026-08-24: Reconciled the proposal with the landed `Decide` design.
  `Decide<P>` promises reduction, so a neutral excluded-middle axiom cannot be
  its blanket instance. The design uses a distinct logical-evidence class for
  axiom-backed availability and keeps `Decide` for computation.
