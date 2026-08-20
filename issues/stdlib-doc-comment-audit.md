---
title: "Make lib documentation concise, current, and API-facing"
status: open
labels: [stdlib,docs,cleanup]
created: 2026-08-20
updated: 2026-08-20
---

Comments throughout `lib/` mix several jobs: public API documentation,
historical implementation narrative, issue-round evidence, explanations for
constraints that no longer exist, and long rationale around small definitions.
That made sense while the library was being used as a language probe, but it
now obscures the API a reader is trying to learn.

Audit the library module by module. Keep concise semantic contracts,
non-obvious proof/computation behavior, law orientation, and genuine usage
guidance close to declarations. Delete obsolete history; move durable design
rationale to an owning design document or issue; and avoid explaining code
whose definition is clearer than the prose. This is an editorial audit, not a
line-count contest: subtle definitions may still deserve substantial notes.

The audit should also settle a consistent distinction between module comments,
public declaration documentation, and short implementation comments, even if
Heather does not yet extract documentation mechanically.

## Acceptance

- Every `lib/std` module is reviewed, with high-churn experimental modules
  handled after their public shape is settled.
- Comments that describe a completed migration, old limitation, test-round
  narrative, or stale implementation detail are removed or re-homed.
- Public declarations retain a short statement of meaning and any surprising
  laws, opacity, reduction, argument order, or failure behavior.
- Terminology and notation match current source spellings.
- Representative before/after modules establish a written comment style that
  future library changes can follow.
- The library and full test suite still check after the editorial pass.

## What it assumes from elsewhere

- **[[tree-library-public-shape]]** owns the public-vs-experimental boundary in
  `lib/std/tree.hthr`. Assumed here: that module's deep audit waits until its
  declarations have stable homes.

## Log

- 2026-08-20: Filed separately from the completed kernel-comment audit: the
  problem here is library voice and historical accumulation, not stale kernel
  rule counts.
