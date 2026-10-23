---
title: Open payloads inserted under binders still deep-copy per occurrence
status: open
labels: [kernel,performance]
area: kernel
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

## Log

- 2026-07-31: Definitions landed ([[simulate-conversion-cost]]) and the prediction in the body held in the direction that matters: the inlined interpreter is gone from statements and ih terms, and heather check lib/certgen/ir_v1.hthr went 13.6s -> 2.1s without touching payload copying. The post-definitions profile this issue's trigger asks for has NOT been taken, so whether ShiftLocal payload copies still dominate anything real is open -- that measurement is the next thing this issue wants, and it is cheap.
- 2026-07-31: The cheap measurement the last entry asked for is taken: post-definitions perf profile of release heather check lib/certgen/ir_v1.hthr shows local substitution (sub_tm/sub_ty/ShiftLocal) at ~4.4% total, no payload-copy line above noise. Trigger NOT fired; the representation change stays deferred. Dominant costs are Psi cloning ([[context-representation-clones]], ~16%) and level normalization (new issue [[level-normalization-allocation]], ~14%).
