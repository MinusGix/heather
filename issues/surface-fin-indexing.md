---
title: Surface indexing layer: Fin(n) as a type, index constructors, xs[i]
status: open
labels: [frontend,elaboration]
created: 2026-08-02
updated: 2026-08-02
---

Filed off the [[meta-def-registration]] design round (2026-08-02,
docs/meta-def-registration-design.md §4.4), which discovered the blocker while
validating the registration seam against `tabulate_code`: **`Fin` has no
surface spelling.** `TyKind` has no `Fin`; `ExprKind` has no index
constructors (`inl ⟨⟩` / `inr`), no `elim_Empty`, and no `xs[i]` (brackets are
vector types and literals only). `Type::Fin` is constructed exclusively
elaborator-side (wf.rs, `elab_container_ih`). A user-declared `Fin` inductive
is not a substitute: it lowers to a `Wf` type, not `Type::Fin`, and the
cross-check against the Rust oracle would rightly fail.

Wanted: `Fin(n)` as a surface type, its two index constructors as
expressions, and (for `nth_code`) a case on `Fin` — i.e. an `elim_Empty` in
the zero arm, term.rs' spelling. `docs/container-proofs.md` §7 already
anticipates this layer ("it should land *with* the surface indexing layer
(`Fin`, `xs[i]`)").

Sequencing: gates the `tabulate_code` and `nth_code` ports of
[[quotation-stage-artifacts]] — that issue's candidate order is re-read as
"fold (landed), this layer, then tabulate and nth". Not gated by, and does not
gate, the registration round itself.

Also noted by the design round: `docs/types-as-expressions.md`'s coverage
table lists `Fin` as "reachable from the surface", which is true of its
*code* (`TmFin`) and not of its syntax — correct that row when this lands.
