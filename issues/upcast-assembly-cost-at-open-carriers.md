---
title: The resolver's upcast assembles a fresh parent record per occurrence at an open carrier
status: closed
labels: [elaboration,performance,traits]
created: 2026-08-08
updated: 2026-08-08
---

Found by the type-projection round (2026-08-08), as the finding that decided
its migration: `plus_zero_of_comm` written `<G: AddCommMonoid>` with
`G.plus(x, G.zero)` elaborates correctly and takes the library check from
0.7 s to 25 s. The cost is not the projection: `plus` and `zero` are declared
by ANCESTORS (`AddSemigroup`, `AddMonoid`), so each type projection builds its
goal at an ancestor and is answered by the resolver's upcast
(docs/traits-owner-dispatch-design.md §3, §7.1), which at an open carrier
assembles a fresh parent record over the child dictionary's projections —
once per occurrence, FOUR times in that one small proof (the original "five"
miscounted: `plus_comm` is declared by `AddCommMonoid` itself, an exact-scope
hit), each a Σ-tuple of law types.

Measured (2026-08-08, release, lib/std/algebra/algebra.hthr):
- exact-dictionary spelling (`requires a` / `G::AddCommMonoid.plus`): 0.7 s
- upcast projections in the statement only: 1.7 s
- upcast projections in the proof body too: 19–25 s

Shape of the fix, decided by the 2026-08-08 diagnosis (log below): a NAMED Ψ
upcast definition per (child, ancestor) pair, generic over the carrier and
dictionary, minted at class-declaration time — each occurrence becomes a
small application typed once by the global's Π-type. The two levers the
filing guessed at are measured out: a per-declaration memo attacks only the
elaborator side (≤9% of the time), and a shared `let` is not expressible at
the kernel level (surface `let`s are elaborator aliases, inlined at use) and
would not help if it were, since the cost is not cross-copy conversion.

Until fixed, the library's `plus_zero_of_comm` keeps `requires` with the
measurement written beside it (the standing motive), and this issue is a NEW
ENTRY on the `requires`-removal prerequisite ledger
([[requires-placement-syntax]], 2026-08-07 INTENT entry): removal cannot
strand hierarchy-spanning proofs on a 25 s spelling.

Per the perf discipline (layer 2 §10's trial-cost entry is the doc home):
filed with its trigger, one deliberate round when picked up.

## What it assumes from elsewhere
- **docs/traits-owner-dispatch-design.md** owns the upcast rule (assembly, not
  projection, at open carriers). Assumed here: only that the assembly is per
  occurrence today.
- **[[traits]]** owns the resolver. The fix must not reorder the search
  (exact scope -> upcast -> registry) or bypass the kernel gate.

## Log

- 2026-08-08: DIAGNOSED (measurement round; scratch variants preserved in the session scratchpad, instrumentation reverted). Hypothesis confirmed in the large — the kernel gate is 90% of a 36.7 s fully-anonymous run (33.0 s gate; resolver trials 0.34 s across 90 calls whether counted kernel- or elaborator-side; elab side 3.3 s) — and REFINED in two ways that redirect the fix. (1) Growth is LINEAR at ~0.78 s per upcast occurrence, no pairwise cross-copy term: the cost is NOT conversion between copies (identical copies already hit conversion's a==b fast path) but the gate RE-CHECKING each inlined assembled record against the class's dependent Σ-type per copy — and a lawless hierarchy of identical shape costs microseconds, so the law fields are ~100% of the constant. (2) The tax escapes the declaring theorem: the assemblies are baked into its STATEMENT type, so every call site pays too — anonymous-statement-only is 12.7 s file-wide, of which 9.5 s is nat/bool_plus_zero consuming the statement at concrete carriers. Occurrence count corrected 5 -> 4 (plus_comm is the child's own field, exact-scope). Levers measured out: shared let recovers nothing (35.0 vs 36.7 s — surface lets inline, no kernel let exists) and per-declaration memo caps at the 9% elab side; kernel pointer-equality is second-order here. THE LEVER THE DATA PICKS: the named Ψ upcast definition per (child, ancestor), checked once at declaration time, which alone also shrinks the statement and so fixes the call-site tax. Unexplained residue worth one look in the fix round: Bool's call site costs 7.0 s where Nat's costs 2.8 s.
- 2026-08-08: FIXED and closing (managed round; docs/traits-named-upcast-design.md). The briefed fix — the named Ψ upcast per (child, ancestor) — was BUILT FIRST, MEASURED, AND WITHDRAWN, with its numbers kept in that doc's §5: it bought 2.2x (35.9 s -> 11.4 s) because the record literal was never the whole cost (the ancestor dictionary stays in the term and every later conversion re-reduces it: 43.9M conversion steps vs 1.1M, with only 670 delta-unfoldings), it needs 2^21 conversion fuel where the assembly needs under 2^20, and each mint costs 25-30 ms per class declaration whether or not anything upcasts. WHAT SHIPPED: a dispatched projection reads THROUGH the upcast — the assembled parent's f slot IS d.f, so the projection is taken from the child dictionary at the child's own flattened index and the ancestor never enters the term. resolve_goal grows a provenance-reporting sibling (resolve_goal_from), set only by step 1b, consumed only by the two dispatch sites; search order, candidate set, trace, and the checks_at gate untouched — the proposal is still built and gated, just read rather than taken. NUMBERS: file 35.9 s -> 0.948 s (1.41x the briefed 0.67 s baseline; 1.52x same-build); call sites 2.9/7.9 s -> 0.035/0.075 s; on a three-class reproducer the two spellings are indistinguishable because they are now the SAME TERM. plus_zero_of_comm is anonymous; zero library declarations keep requires for a perf reason. Suite 1326 -> 1328; frontend bench deltas verified pre-existing on the clean tree (logged on frontend-benchmarks). Residue filed elsewhere: trial cost (layer 2 §10 gains the read-through multiplier), the value-consumer path still assembles inline (correct per the design doc §2 — a value is what is asked for there), the dispatch-only boundary (provenance does not travel with a term passed to a function that later projects; nothing in the corpus does it — noted on traits), and the Bool/Nat call-site asymmetry (its own issue: synthesis-direction-cost-asymmetry).
