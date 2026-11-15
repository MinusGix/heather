---
title: Nested patterns give each clause its full equation
status: closed
labels: [elaboration,match,patterns,proofs]
area: language
created: 2026-10-31
updated: 2026-11-01
---

Slice 5 of [[dependent-match-compiler]] (docs/language/matching/dependent-match-compiler-design.md §7). Needs [[match-equation-in-every-arm]] and [[match-refines-computed-scrutinee]].

`prepare_arms` compiles deep patterns to nested matches on column variables. The outer equation mentions the columns, so refining it at each inner level (slice 2's rule over pending equations) makes it `s = C(x, D(y, t))` at the leaf, with no composition proof.

## Done when
- Probe P4 checks (design §12.1), which closes [[eqbind-deep-pattern-kernel-rejects]].
- [[deep-pattern-dependent-later-field]] is checked here.

## Log

- 2026-10-31: 2026-10-31, investigating after slices 1–3: P4's and nested-match-on-list-tail-motive's root cause is the same and is not the refinement rule. List lowers on W (tier 1/2): a Cons arm's recursive binder is an alias whose term reads the child out of the kids function f' (spelled through a Vec/Fin child read, §14 of the tier-2 note), while the arm's goal spells the value as supf(inj x; f'). So the inner generated match's scrutinee never occurs in the goal or in h's type, and neither motive synthesis nor refinement can abstract it. Tier 0 had the same gap and was fixed by rebuilding the constructor value around z (nested-match-on-field-binder-motive, Σ/Unit η). The W analogue does not convert: f' ≡ λy. child needs η at an Empty-domain sum (P = Unit + Fin 0), which the kernel lacks — the reason the leaf predicate exists. A correct fix transports along the canon predicate (J, as the leaf arm does) or rebuilds the value with its proof; this slice is blocked on that design, not on the dependent-match front end.
- 2026-11-01: Landed (docs/language/matching/dependent-match-compiler-design.md §7.1). The 2026-10-31 diagnosis was wrong: List is tier 1 (Wf, a children tuple), not W, and the Empty-domain η gap is tier 2's leaf, which has no recursive binder. The fix is the motive's child rewrap: abstract the children local(s) rebuilt around z together with the scrutinee. For Wf that is cs' ↦ tuple with z at position t (nth reduction + Σ-η); for a W plain child it is f' ↦ λy. fst z, c ↦ snd z (Π/Unit-η). P4 checks with h the clause equation. deep-pattern-dependent-later-field was checked here: it is still a kernel rejection, with a different root (a later field's alias keeps its unrefined type), so it stays open. The indexed-family analogue is filed as indexed-deep-pattern-kernel-rejects.
