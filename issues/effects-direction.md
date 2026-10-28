---
title: Choose the effects story (uniqueness threading vs interaction trees)
status: closed
labels: [design, effects]
area: interaction-trees
milestone: [it-library]
created: 2026-07-22
updated: 2026-10-28
---

Effectful runtime functions never run at kerneltime, so the question is what
kerneltime object they *denote* so theorems about them are stateable. Split
the programming surface from the reasoning denotation; users never write
monadic types.

Current leaning — the two candidate denotations compose, staged:

1. **Uniqueness typing (Clean-style) first.** `&uniq Fd` is a capability;
   `Fd::read : uniq Fd -> (uniq Fd, [u8; N])`. Effectful code is literally
   pure, `equiv` stays plain equality, and uniqueness is an *intensional
   library discipline* over boxed code (like the lifetime-system idea), not
   kernel machinery. This is also the first serious test of the
   "disciplines are libraries" bet.
2. **Interaction trees later**, when concurrency or genuine external
   nondeterminism forces trace-shaped semantics for specific primitives.
   Cost: coinduction in the kernel and bisimulation replacing propositional
   equality — check against the Coq DeLaM formalization whether layering
   tolerates it, or whether some weaker finitary notion suffices.

Avoid: a user-visible CPS/monadic elaboration target that people read and
prove against directly (monad-shaped goals + esoteric types, no equational
payoff).

Related: [[ir-simulate-design]] (trace-shaped simulate), [[kernel-v0-scope]]
(coinduction explicitly out of v0).

## Log

- 2026-07-24: CONSTRAINT from the equality-notation decision ([[surface-syntax]], 2026-07-24): `=` is now propositional equality (and `let` binding). Any future imperative/assignment-like effect syntax must therefore NOT use bare `=` (`place = value` would be indistinguishable from asserting `place = value`, since only `let` disambiguates). Use `:=` (user's stylistic lean) or `<-`. Applies whichever way the effects story lands (interaction trees are the plan to explore); mutable-value ergonomics are wanted, so pin the assignment glyph early.
- 2026-07-31: From the [[ir-simulate-design]] sketch (docs/ir-simulate-design.md sections 6-7): this issue now also owns the PARTIALITY futures for simulate, not only effects proper. simulate's public interface is converges (the exists-fuel closure, i.e. the Delay monad's big-step convergence) + fuel_monotone, so richer models slot in behind it without restating client theorems. Candidates, none scheduled: (1) coinductive Delay -- needs coinduction (out of kernel v0) and moves equiv toward bisimulation, the cost this issue already flags for interaction trees; (2) guarded recursion / later modality -- first-class fuel, a real kernel+metatheory round (clocks, Loeb); (3) Bove-Capretta domain predicates -- per-function fuel-free totality, wants function-typed inductive fields. Also recorded there: RVSDG state edges are uniqueness threading as an IR construct (a capability is an environment slot), so leaning 1 of this issue and the IR design reinforce each other; v1 IR defines no effect nodes but nothing in it precludes state slots.
- 2026-08-02: COMMITMENT IN THIS ISSUE'S FAVOUR from docs/let-and-blocks-design.md §3.1 (implementing round 2026-08-02): := was NOT spent on the `let` binder and remains free for the assignment glyph this issue's 2026-07-24 log asked to pin early. [[annotated-let-swallows-the-equals]] listed ':= as the let binder' as its most principled option and claimed it 'composes with [[effects-direction]]'s eventual assignment =' -- that claim is SUPERSEDED and was backwards: this issue's log records that = is NOT available for assignment (only `let` disambiguates `place = value` from asserting it), which is precisely why := is being held. Spending := on `let` would have made it goal discharge (parser.rs:729), a calc step proof, a local binding, and later an assignment: four meanings against the two = carries. That issue closed instead by suppressing the comparison rung in the annotation position, keeping = as the binder. Second commitment, from §4.5: INTERLEAVED statements in a block (`let a = …; f(x); g(a)`) are deferred TO THIS ISSUE and not to effort. block_body's all-lets-first shape stands because an expression statement in a language with no effects is a no-op -- there is nothing for `f(x);` to do -- so adding the form now would be adding a syntax whose semantics is 'discard a pure value', which is a lint and not a feature. The form becomes meaningful exactly when this issue decides what a statement IS, and the block expression that landed (ExprKind::Block over the existing Block node) is where it will go.
- 2026-09-24: Interaction-trees investigation: `docs/interaction-trees-fit.md` (Xia et al., `docs/3371119.pdf`). Headline for this issue's open question ("whether some weaker finitary notion suffices"): yes. Container events over fuel-cut trees plus the paper's §7 (eutt = finite-trace equivalence) fit `converges`/`fuel_monotone` with no kernel change, losing only coinductive liveness. Kernel coinduction, if ever, should be a negative `M` with β only and **no η arm** (η there semi-decides bisimilarity). Follow-ups are owned by [[interaction-trees-container-model]]. Partiality foundations worth knowing before deciding: Chapman–Uustalu–Veltri (`docs/chapman-uustalu-veltri-delay-quotient.pdf`): quotienting Delay by weak bisimilarity needs countable choice to stay a monad, which supports setoids. Uniform Elgot iteration without choice (`docs/2102.11828.pdf`). Escardó–Knapp dominances (`docs/2011.00272.pdf`), where partiality meets propositional resizing, the wall "predicative always" puts in the way. Neighbouring investigations filed the same day: [[cost-aware-semantics]], [[polynomial-functor-interfaces]], [[multimodal-modalities]].

- 2026-10-21: DECIDED (Minus): the surface is **uniqueness threading that denotes interaction trees**. Evidence: `ITree::run_state_bind` (`docs/itree-refinement-round.md`) shows interpreting state events is world threading and composes with sequencing, so the two leanings above compose. The surface's target is the effectful source of [[native-effect-source-compiler]] (`docs/native-program-logic-design.md` §7, §10). Coinduction is no longer deferred to a customer: the kernel round is planned now in [[kernel-coinductive-types]].
- 2026-10-28: Closed (tracker tidy): the choice this issue owned was made on 2026-10-21 (above), and the round it unblocked has run: the effectful source and its compiler ([[native-effect-source-compiler]]), the tree library, and kernel coinduction ([[kernel-coinductive-types]]) carry the denotation. Residue, with owners: building the surface, the `:=` assignment glyph and interleaved block statements go to [[effects-uniqueness-surface]]; partiality now goes through the coinductive tree library (`docs/coitree-design.md`). The links that say this issue "owns" the decision keep pointing here as its record.
