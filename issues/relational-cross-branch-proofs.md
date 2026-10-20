---
title: Prove compatibility when related inputs choose different branches
status: open
labels: [setoids,design,backlog]
area: tactics
created: 2026-09-05
updated: 2026-09-05
---

Equal branch choices are sufficient for compatibility, but unnecessary when the selected outputs are related. A failure to establish Boolean stability must not be presented as non-respectfulness.

## Acceptance

- State a checked rule covering the reachable pairs of branches, including different choices on the two inputs.
- Expose cross-branch output obligations under the relevant condition evidence. Do not require unreachable cases when their impossibility is supplied.
- Check an operation whose representation-sensitive condition selects equivalent outputs, and a negative control selecting genuinely distinguishable outputs.
- Try the cheaper same-choice rule first when applicable; bound case growth and retain manual proof escape points.

Do not silently strengthen the function contract or collapse proof-relevant branch evidence. Related: [[relational-ordinary-branches]], [[dependent-relational-transport]], [[setoid-auto-lifting]].

## Scheduling

Captured for a future concrete driver; not scheduled by this filing. See [[setoid-roadmap-and-resumption]].
