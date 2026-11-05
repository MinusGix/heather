---
title: Open payloads inserted under binders still deep-copy per occurrence
status: open
labels: [kernel,performance]
area: kernel
created: 2026-07-31
updated: 2026-10-26
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
- 2026-10-25: Pottier's *Fast thinnings via segment maps* (docs/segmap-survey.md, §3) is the reference for the shift annotation's data structure if this representation change is ever taken: composing one binder's weight-1 shift onto an accumulated annotation is O(log W), lookup is O(log W), and `prune` against the memoized max free index keeps annotations proportional to the variables used. It does not lower the risk this issue names: segment maps need the §3.5 variant to be canonical, and even canonical annotations need a push-to-leaves normalization before every `==` (□ conversion, the elaborator's strengthening and zonking tests, the bounds memo). Trigger unchanged. The survey's one value-machine idea, a random-access-list environment, is [[env-lookup-depth]].
- 2026-10-26: A third known alternative, from mengine (docs/mengine-survey.md §2, §6): pointer-unique named variables, so nothing ever shifts and a shared subterm under a binder stays one node. Its price is a context tree with an order-maintenance structure for O(1) ancestry, binder refreshing in substitution, and parent lists on every node; and `==` on terms would stop being structural, which the □ rule needs. Not a candidate. The cheap step it suggests, a per-traversal memo for shared nodes, is [[subst-shared-node-memo]], which could key payload copies by address and depth too.
- 2026-10-26: [[subst-shared-node-memo]] landed a per-call shared-node memo in every pure substitution traversal, so one shift of a shared value is now its shared size. What stays is this issue's cross-call case: a shift of an already-shifted value is a fresh copy, so a let chain with a binder between every link elaborates in time quadratic in its length (each link shifts the previous link's value once), down from 2^k. A representation change would make that linear; nothing measured needs it yet.
- 2026-10-26: Measured and bounded. New bench family `let/under` (`fixtures/rewriting.rs`: `fan` with a `λ` between every link, the `interleaved` shape of `let_and_blocks.rs`) fits slope 1.72 over 16..128 lets, ×3.7 from 64 to 128, elaboration 88%; 128 lets take ~45 ms on the cloud box. 128 is the most one expression can hold, since each link nests one level and elaboration refuses past 512. The quadratic is the representation's own bound, not a missing memo: link `i`, elaborated at depth `i`, holds every earlier link `j` shifted by `i − j`, and each of those mentions the outer locals at index `≥ i`, so no two links share a node and the links together are Σ i = Θ(k²) distinct terms. A cross-call shift memo keyed by (node, amount) never hits (each `s_j ↑ m` is wanted once), and storing aliases strengthened to their free variables' depth only moves the copy to the use, which must still be materialized at depth `i`. The finished term is linear (`s_j ↑ (k − j)`, one per link) and the gate's work on it is too. So the only way below k² is a deferred shift in the term representation (explicit-shift node, or the shift folded into the shared pointer), with the costs this issue and docs/segmap-survey.md §3 name. Trigger unchanged and not fired: no library workload has been seen paying this, and the expression depth limit caps the bench's chain at ~45 ms.
- 2026-11-05: gardener: cites a file it shares with [[image-tree-walks-let-shared-terms]] (`docs/mengine-survey.md`); [[signature-rescope-multiplicity]] (`docs/segmap-survey.md`).
