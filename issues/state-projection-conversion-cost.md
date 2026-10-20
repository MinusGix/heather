---
title: Keep projection and equality checking local across long state-update chains
status: open
labels: [kernel,conversion,performance,proofs]
area: kernel
created: 2026-09-08
updated: 2026-09-11
---

During the reusable callee round (`cb877f2`), apparently small equalities such
as preservation of RSP unfolded substantial machine-state/register-update history.
Whole symbolic execution to concrete-state conversions and nested footprint
proofs also exhausted fuel or memory. Explicit fields, generic read-after-write
laws, relational intermediate-state witnesses, and staged exclusion proofs made
the accepted certificate fit unchanged limits. These are useful APIs, but their
success does not establish that the original conversion costs were necessary.

## Investigation

- Minimize a successful projection/preservation equality over increasing state
  history, varying irrelevant fields, shared subterms, and update depth.
- Compare direct definitional equality with the accepted explicit-field/lemma
  spelling; retain both as customers rather than prescribing a library workaround.
- Attribute repeated reduction, comparison, allocation, and cache eviction before
  choosing a kernel strategy, representation change, or core API improvement.
- Include neutral states, open memory types, overlapping updates, and false
  endpoints. Preserve judgments and honest resource refusal.
- Re-evaluate after the incoming transparent-unfolding change (`4afcaea`);
  observations above predate it and are not evidence that the same cliff remains.
- Record scaling through the existing benchmark protocol; raising resource caps
  or choosing smaller examples does not complete the investigation.

## What it assumes from elsewhere

- [[state-location-and-frame-kit]] owns reusable read/update/frame APIs.
- [[kernel-failed-conversion-cost]] owns the asymmetric false-conversion case.
- [[x86-reusable-callee-certificates]] records the accepted executable customer.

[[x86-native-certificate-cpu-budget]] owns the concrete merge acceptance failure;
this issue owns attribution and improvement of the general state-history family.

## Log

- 2026-09-11: Triage 2026-09-11: this issue's own re-evaluation trigger (transparent unfolding past a failed meet, 4afcaea) has landed, and two more changes on the same path followed (typed app/proj 43a743a; body cache per gate 335a722). Neither was re-measured here, and x86-native-certificate-cpu-budget (the concrete acceptance failure) is closed. Next action is the cheap re-measure of an RSP-preservation equality over a long update chain, not a design.
