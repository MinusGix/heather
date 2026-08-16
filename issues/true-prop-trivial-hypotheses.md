---
title: A real True, and what pays a definitionally-trivial hypothesis
status: open
labels: [design,stdlib,frontend,ergonomics]
created: 2026-08-15
updated: 2026-08-16
---



Spun off [[datarepr-surface-ergonomics]] item 3 (2026-08-15). Naive/
trivial-`inv` reprs spell `inv` as `Zero = Zero`, so every generated
`refines` signature carries `h0: (Zero = Zero)` and every consumer passes
`refl`. Two separable halves:

1. **A real `True`** with a canonical inhabitant, so the spelling stops
   being a pun. Small, stdlib-shaped; relates to
   [[default-inhabited-nonempty]]'s ladder.
2. **Who pays a definitionally-trivial hypothesis.** Coordinator's
   recommendation (pending user verdict): keep the registry statement
   UNIFORM — `refines` always takes the `inv` hypotheses — because every
   consumer of the registry (reprgen's callee steps, the certgen
   composition, future dispatch) then handles one shape, and statement
   specialization would put a branch in every consumer to remove an
   argument that generators already pay invisibly. The human-facing noise
   is better addressed by auto-discharge (elaborator fills a hypothesis
   whose type is definitionally `True` / has a registered canonical
   inhabitant) as a general ergonomic feature, not a datarepr special
   case.

## Log

- 2026-08-15: User ratified both halves (2026-08-15): a real True is valuable; general auto-discharge is wanted as a feature in its own right. The recommendation stands as the plan: uniform registry statement, True now, auto-discharge as a general elaborator feature later.
- 2026-08-16: User verdicts (2026-08-16), settling both halves' mechanisms. Half 1: True := Unit — the kernel already has Unit^l with eta-as-proof-irrelevance (crates/kernel/src/conv.rs ~1225, every term of Unit type convertible), so a prelude True over kernel Unit gets judgmental uniqueness of the inhabitant with no sort question at all; the SProp-vs-Prop dilemma dissolves rather than being decided (survey: Coq's separate sTrue stayed siloed behind a boxing boundary; Lean made all of Prop strict; Agda's idiomatic ⊤ is the eta-record trick — Heather is in Agda's position with the eta rule already in the kernel). One dressing want: True should PRINT as True, not as its Unit spelling. Half 2: auto-discharge is NOT resolver-based — the licensing property is per-binder intent, not per-type inhabitedness (Inhabited(Nat) says nothing about whether omitting a Nat argument is meaningful), and a search per omitted position has real cost. Mechanism instead: DEFAULT ARGUMENT VALUES declared at the binder (h0: inv-statement := True::intro) — the binder stays in the signature so the ratified uniform-statement shape survives, generators keep passing explicitly, omission is substitution not resolution. User notes the general tool is wanted anyway, including defaults that run a tactic search over the surrounding context. The mini-round is now: prelude True/trivial over kernel Unit + printing dress-up, flip the defaulted inv from Zero = Zero to True, update emissions as they fall (user: no need to choreograph emission flips — actively iterating). Defaults-at-binders is its own feature, natural home near [[named-arguments]].
