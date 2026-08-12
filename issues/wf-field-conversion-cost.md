---
title: A Wf-lowered inductive as a field of another inductive costs ~163x: pathology or law?
status: open
labels: [kernel,elaboration,performance,conversion]
created: 2026-08-12
updated: 2026-08-12
---

Filed from round A (2026-08-12, docs/certgen-cert-expression-design.md): the
first `Cert` draft carried `rest`/`after: Ir` fields — faithful to the kit
lemmas' argument lists — and `lib/certgen_cert.hthr` elaborated in **163
CPU-s**; dropping the fields gave **1.0 s**. A single `match` on the
`Ir`-carrying `Cert` was 4–7 s, a nested one 25–46 s. The final design is
better *on its own merits* (the chain is its own IR, and the renderer is where
the renumbering already lives), so nothing is blocked — but the magnitude
smells like a **pathology, not a law**, and the user's standing position
(2026-08-12) is that perf surprises of this kind usually mean "make the
kernel/elaborator smarter or fix a pathology", not "design around it". This
issue owns finding the mechanism before anyone treats the workaround as a
design rule.

Suspects, unweighed:

- the tier-1 lowering of a constructor whose *field type* is itself Wf-lowered
  (a `Supf` label carrying a `Supf`-typed payload) — does the
  children-container encoding nest a whole second telescope per constructor?
- conversion/`refl` between values of such a type: the round's own note says a
  `refl` between two Wf-lowered values is "the expensive kind of pin" — is the
  cost in `conv_term` re-walking the nested `Supf` spines without sharing
  (cf. the closed whnf-sharing-term-growth mechanism)?
- the elaborator's `match` lowering over the nested shape (the 4–7 s single /
  25–46 s nested gradient points at per-arm motive/telescope rebuilding).

Reproducer: reconstruct the draft datatype from the design doc (§2 records the
field-carrying shape) beside the landed one; the 163× is the gap between the
two elaborations of one file. Measure per the recorded protocol only
([[perf-tracking-consistent-environment]]); a named candidate workload for the
instruction-count harness once it exists.

Trigger: the next time anyone wants an inductive carrying a Wf-lowered field
([[nested-inductives-container-fields]] is adjacent), or the next deliberate
perf round. Related: [[certgen-harness-cost]] (where the observation was first
logged — its "rule of thumb: don't embed" should be read as a marker of THIS
issue, not as design doctrine).

