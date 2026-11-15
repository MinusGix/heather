---
title: ElabCode: metaprograms over a friendly reflected AST, certified against raw Code
status: open
labels: [metaprogramming,design,frontend,stdlib]
area: tactics
created: 2026-08-11
updated: 2026-10-31
---

User plan, stated 2026-08-11: most metaprograms should eventually NOT touch raw Code terms — arcane, iffy, disconnected from the normal code view. Instead: an ElabCode inductive (quote-style / simplified-elaborator-ish AST as ordinary data), manipulated by ordinary functions, theorems, tactics, DSL-ish parts, with a translation to the true underlying Code that is what actually gets kernel-checked. Tricky Annoying Stuff obscured behind the layer.

**The pattern already exists at n=1**: the transcriber round's TA/Pre/Ir is a domain-specific ElabCode — code reflected into first-order data, compiled by ordinary provable fns, the meta layer contributing only the traversal. Generalizing:

- **reflect (Code -> ElabCode)**: the walker direction. Status = the blocker list: variables via markers (closed-substituend substitution, cheap — code-variable-analysis-api), globals behind the opaque-globals round, per-fragment walkers until then.
- **reify (ElabCode -> Code)**: recursion over data emitting code. Near-term for closed fixed-context fragments (kernel formers are layer-generic so layer-m recursion should check; missing piece is SURFACE — ordinary match in a meta body, meta-body-statement-loop territory). The hard case is BINDERS: a Lam node's recursive result lives at an extended context — the same wall as transformation passes; grows with the rebuild/delayed-substitution machinery.
- **Verification, the key fact**: code does not compute, so conversion on code values is STRUCTURAL — a round-trip theorem reify(reflect(c)) = c at any concrete instance is refl, free, today. The universal theorem needs a dependent motive over code (blocked). Consequence: the abstraction layer can itself be CERTIFYING — every ElabCode metaprogram ships a per-use refl pin that its reflected view corresponds to the code it manipulates — with the universal theorem as the verify-at-stability lifecycle step (in-language-certificate-emission's route-2 pattern applied to the sugar itself).

Design principle this issue carries (user, 2026-08-11): 'it is beautiful if it can elegantly be in the theory, but if it isn't elegant fundamentally, it doesn't need to be in the theory most of the time.' The underlying duality: quotients/funext are IDENTIFICATION primitives (erase distinctions globally in the semantic layer — which is why they haunt: canonicity strain, undecidabilities, lost useful distinctions), Code is an OBSERVATION primitive (adds distinctions behind a modality, fenced by the layer discipline from the equational theory — tm_var's opacity being load-bearing is this fence working). Fenced observation is conservative where global identification is not; setoid-auto-lifting is the same stance applied to quotients.

Wants: fn-reflection-for-analyzers (the reflect inputs), retire-rust-transcriber (dogfooding pressure), meta-body-statement-loop (reify's surface prerequisite). Not scheduled; direction with a live first instance.

## Log

- 2026-08-11: Cross-link (2026-08-11, coordinator bookkeeping): [[ownership-discipline-over-code]] is this pattern's first named client — a decidable judgment over reflected code plus one soundness theorem, behind the layer fence, the kernel never learning the word. The link existed only in the 2026-08-11 commit message; it belongs here.
- 2026-08-11: Coordinator note (2026-08-11): the reflect direction's globals blocker is discharged fragment-scoped only — Elaborator::fn_body_code's interface is general but its DOMAIN is the certgen Nat fragment (markers typed at Nat, callee signatures Nat-chains), and each fragment widening reopens the marker recognizer's unambiguity argument; recorded in docs/metaprogramming/opaque-globals-analysis-design.md sec. 2 so the general-reflect round prices it up front.
- 2026-10-21: docs/metaprogramming/host-elaboration-interface-design.md places this pattern for tactics: the reflected AST is a lazy surface-level `Expr`/`Head` view with host-issued handles, manipulated as ordinary data, and the translation to the real thing is the host's elaboration of a returned `Expr` against the goal, re-checked by the kernel. Raw Code stays the carrier for typed generators.
- 2026-10-31: `tac-host-interface` is marked done in docs/roadmap.md (its "done when" is met), so this issue no longer serves it; it stays open in area `tactics` with no milestone.
- 2026-11-05: gardener: cites a file it shares with [[frontend-roadmap]] (`docs/metaprogramming/opaque-globals-analysis-design.md`); [[generators-in-the-language]] (`docs/metaprogramming/opaque-globals-analysis-design.md`).
