---
title: Design one sequencing surface: binding over any carrier, local state and loops in pure code
status: open
labels: [design,frontend,syntax,ergonomics]
area: language
milestone: [lang-sequencing]
created: 2026-10-31
updated: 2026-11-01
---

Round R1 of `docs/compiler-milestones-proposal.md` (§3, §7): the design round for `lang-sequencing`. Its output
is a design note that Minus decides on, plus R2 and R3 filed against it.

## Scope

- The carrier protocol for binding statements: a class or a field set (`bind`, `pure`), and how a block finds its carrier from the expected type. Minus decided on 2026-10-31 that any carrier with a `bind` qualifies, not only named ones.
- The binding spelling (`let x <- e;` is the candidate, since `=` is equality and `:=` is held for assignment, `docs/let-and-blocks-design.md` §3.1) and interleaved statements (`e;`, deferred there in §4.5).
- `let mut`, `:=`, `for` over lists and ranges, `while … decreases` and `while … fuel`, and `break`/`continue`/`return`: what each lowers to, in pure code and inside a carrier block.
- What proofs see (§3.3 of the proposal): folds with lemmas, generated unfolding equations, exposed step functions. Coordinate with [[proof-modularity-design]] on the invariant rules.
- The effects case: the same surface serves [[effects-uniqueness-surface]].
- Whether [[pipeline-operator]], [[function-composition-operator]] and [[prelude-option-and-friends]] layer 2 are still needed after binding statements.

## Done when

Minus has decided the note, and [[binding-statements]] and [[pure-imperative-statements]] state their scope against it.

## Log

- 2026-10-31: 2026-10-31: Design note written: docs/sequencing-surface-design.md (§11 lists the decisions for Minus). Carrier protocol = owner members M::bind/M::pure, since a class over a type constructor is not expressible (probe P1). R2 and R3 restated against it; R3 split into R3a and R3b, with R3b (while … decreases) waiting on [[unfolding-computed-scrutinee]]. Filed [[omega-certificate-bare-nil]] and [[decreases-measure-record-field-unspelled]] from the probes.
- 2026-10-31: 2026-10-31: Revised after Minus's PR comment (a Monad Heather cannot express should be fixed in Heather): the carrier protocol is now classes Bind<M>/Pure<M> over a type constructor, with the three missing pieces filed as R2a [[higher-kinded-classes]]. Probe P1 was too narrow: value-parameter inductives and λ A => Option<A> are already Type → Type values, and a record dictionary over M computes. Owner members stay as the fallback.
- 2026-10-31: 2026-10-31: Minus asked for fundamental improvements beyond this round; filed from the memo (https://claude.ai/artifact/Y2Jo9y9Mgd52QdguvaL43s): [[parametric-type-families]] (Minus unsure; decision round first), [[certificates-as-terms]], [[elaborator-glued-evaluation]], [[dependent-match-compiler]], [[proof-scripts-as-tac-blocks]], [[measure-inference]], [[partial-functions-coinductive]]; in-place update logged on [[ownership-discipline-over-code]].
- 2026-11-01: Layer 1 built as R2 ([[binding-statements]]); what building it changed is §13 of the note: lowered in the parser, the second class is Pointed, carrier from the first bound expression when it determines one.
