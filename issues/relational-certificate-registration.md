---
title: Register and discover compatibility certificates explicitly
status: open
labels: [setoids,design,backlog]
created: 2026-09-05
updated: 2026-09-05
---

A derived theorem currently becomes convenient evidence through a local alias. Add an explicit way to make reusable certificates discoverable at an abstraction boundary, without unrestricted theorem search or selecting a relation from the carrier.

## Acceptance

- Identify rules by resolved operations, complete relational signatures, and their assumption parameters; support fixed-argument operation families.
- Specify local scope, imports, explicit registration, precedence, and ambiguity. Test two relations on one carrier and two conflicting certificates.
- Reuse a registered theorem for an opaque operation and prefer it over unfolding its implementation. Provide an explicit selection escape.
- Reject incomplete proofs and stale registrations after changes to definitions or assumptions. Decide how this integrates with existing classes before introducing a parallel instance system.

Customer: remove the alias-only plumbing around `augment_compatible` while keeping the choice inspectable. Related: [[named-function-compatibility-derivation]], [[operation-indexed-classes]], [[setoid-auto-lifting]], [[relational-derivation-cost]].

## Scheduling

Captured for a future concrete driver; not scheduled by this filing. See [[setoid-roadmap-and-resumption]].
