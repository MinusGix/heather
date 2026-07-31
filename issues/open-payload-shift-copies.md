---
title: Open payloads inserted under binders still deep-copy per occurrence
status: open
labels: [kernel,performance]
created: 2026-07-31
updated: 2026-07-31
---

The residue `subst.rs`'s module docs have flagged since
[[subst-copies-payloads-at-depth-zero]], now findable: β-substitution of a
payload under `k > 0` binders calls `shift_local(k)` on it per variable
occurrence, and for an *open* payload that is a full deep copy each time.
[[subst-visits-closed-subtrees]] made the closed case O(1) (skip fires at
any depth); the open case is untouched and is the last way a single
substitution can cost more than the paths to its variables.

The known fixes are representation changes, to be taken as a deliberate
kernel decision (the docs' words): explicit-shift/closure nodes on terms,
or hash-consing. Both are Wf-decision-weight: they touch the term
language itself, every traversal, structural equality (which conversion
at □ relies on being syntactic), and the code recursors' view of syntax —
an explicit-shift node either reduces away before code observation or
becomes observable syntax, and the second option breaks the Static Code
story. That interaction is the dangerous part and the reason this stays
an accumulating issue, not a round.

Deliberately deferred until after kernel definitions
([[simulate-conversion-cost]]): definitions shrink exactly the payloads
that make this expensive (the inlined interpreter), so the workload that
would justify the representation change may not survive that round.
Trigger: a post-definitions profile where `ShiftLocal` payload copies
dominate a real workload.
