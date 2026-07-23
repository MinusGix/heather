---
title: Decide how elaborated code avoids the box synthesis gap
status: closed
labels: [kernel,delam,design,elaboration]
created: 2026-07-22
updated: 2026-07-23
code: crates/kernel/src/typing.rs:20 @ bbb95ec
---

The ch. 04 rule for `box` pulls its contextual type (`Δ`, `T`, `l`) out of
the expected type — `box` carries no annotations. The kernel checker is
bidirectional and inference-heavy: every other form infers, and `box` is
the *only* checking-only form (`tm_infer` returns `NotInferable` on it,
typing.rs:847).

The checker mitigates this by descending structurally through the four
function intro forms during checking (`λ`, `Λ ℓ⃗`, `Λ g`, `Λ U`), so a
`box` under binders in checking position is fine. `letbox` also carries
`ctx`/`ty`/`code_level` and checks its scrutinee against the reconstructed
`□` type, so `box` as a letbox scrutinee is fine too.

**The gap:** a `box` in an un-annotated inference position is rejected even
though it is declaratively typable. The canonical case is the body of an
immediately β-reduced meta-function, e.g. `(Λ g. box Nat) @ Δ` — checking
the redex infers the head, inference hits the `box` body, `NotInferable`.
So the kernel's algorithmic system is deliberately incomplete w.r.t. the
declarative one on exactly these terms.

**Decision needed:** what invariant does elaborated code (the hand-built
[[end-to-end-compile-instance]] term now, the [[certifying-generator]]
later) maintain so it never emits such terms? Candidates:

1. **Meta-ANF discipline (status quo suggestion in typing.rs module docs):**
   never emit a meta-level β-redex; any boxed code that would be the body of
   an applied meta-function is instead named via `letbox` (or placed in
   checking position against an annotated type). Kernel unchanged.
2. **Annotate `box` in core syntax** (carry `Δ`, `T`, `l`): makes it
   inferable, at the cost of term size, divergence from the ch. 04 grammar,
   and conversion having to ignore the annotations.
3. **Add a type-ascription form** to core as a general escape hatch for any
   future checking-only form, not just `box`.

Relevant coupling: [[compile-typeclass-design]] keys instances on syntax
(boxed code is intensional), so elaborated output will be dense with `box`
literals — whichever discipline is chosen gets exercised constantly.

## Log

- 2026-07-23: Read the relevant chapters; findings sharpen the choice
  toward option 1 (meta-ANF discipline):
  - **The paper gives no algorithmic typing** — ch. 08 is decidability of
    *convertibility* only. The checking-only `box` is our own algorithmic
    reading; there is no book algorithm to converge back to, so "stay on
    the ch. 04 grammar and put the discipline in the elaborator" conflicts
    with nothing.
  - **The paper explicitly endorses the split** (04 tex, ~ll. 195–200): the
    core is deliberately verbose and "a type-inferring front-end fills in
    these types for the users." Annotation burden belongs to the front-end
    — and notably the paper chose to annotate *elimination* forms (for the
    code recursor's substructures) while leaving `box` bare.
  - **Code promotion makes a `box` annotation non-canonical** (04 tex,
    "Code Promotion", ~ll. 42–67): `box t` inhabits `□(Δ ⊢ T')` for every
    `T' ≈ T` (e.g. `□(Δ ⊢ (λx.x) Nat)` ≈ `□(Δ ⊢ Nat)`), so option 2 would
    privilege one arbitrary representative and conversion/reduction (letbox
    β, recursor β match on `box _` syntactically; `box T ≈ box T'`
    congruence) would have to erase it everywhere. Worst interaction:
    intensional instance keying — an annotation adds spurious syntactic
    identity to code.
  - **Ψ cannot bind meta-functions** (04 tex, global-ctx rules ~ll.
    969–985: only `g : Ctx`, `U : Typ`, `u : Trm`), so a meta-function
    "call" in core syntax is always a literal β-redex. But that cuts *for*
    option 1, not against: all meta-level computation is static, so the
    elaborator can β-normalize the meta layer at emission time (staging
    happens during elaboration), and the paper's stated mechanism for code
    composition is `letbox` (04 tex ~l. 931), whose scrutinee the kernel
    checks, not infers.
  - Net invariant proposal: **elaborated terms are meta-layer β-normal;
    code composition goes through `letbox`**. Every `box` then sits in a
    position reachable by checking descent, and `NotInferable` becomes an
    elaborator-bug detector rather than a language restriction.
- 2026-07-23: Decided: option 1. Elaborated terms are meta-layer β-normal; code naming/composition goes through letbox. Kernel grammar stays exactly ch. 04; NotInferable acts as an elaborator-bug detector. Follow-through lands as an emission invariant in [[ir-simulate-design]] / [[certifying-generator]].
