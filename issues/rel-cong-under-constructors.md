---
title: rel_cong and relation rewrite under a constructor with a registered congruence
status: closed
labels: [setoids,relations,tactics,proofs]
area: tactics
milestone: [tac-general]
created: 2026-11-11
updated: 2026-11-11
---

`instance Respects2<Regex, Regex, Regex>(Regex::Same, Regex::Same,
Regex::Same, Alt)` is accepted, but a `calc` step

    Alt(a.deriv_simp(c), b) ≈ Alt(a.deriv(c), b) := rel_cong(ia)

is refused: "`rel_cong` context mismatch: the supplied proof does not
explain this change (only homogeneous unary/binary contexts are
supported)". The context here is a constructor application, where the
supported ones are designated operators and functions. Syntax types with
a semantic equivalence (regular expressions up to language, terms up to
conversion, programs up to behaviour) have constructors as their only
contexts, so every congruence step is a named lemma call
(`Regex::same_alt(ia, ib)`), and `rewrite` along the relation has nothing
to walk through.

Wanted: `rel_cong` and `rewrite` along a relation read a constructor
application as a context when a `Respects`/`Respects2` instance is
registered at that constructor (and, for a constructor of other arity,
whatever the general morphism registration becomes,
[[setoid-morphisms-and-transport]]).

Done when `Regex::deriv_simp_same` and `Regex::simp_same`
(`lib/std/text/regex/regex_dfa.hthr`) state their steps with `rel_cong`
or `rewrite` and cite no `same_seq`/`same_alt` by name.

## Log

- 2026-11-11: Built for `rel_cong` (and `rel_derive`'s walk): two sides that are one constructor with one or two carrier fields are a context, with evidence registered at the constructor's qualified name (`Respects2<T, T, T>(R, R, R, T::C)`, `PreservesRelation(R, R, T::C)`); fields are placed up to conversion, since a lowered field is spelled by where it sits (`Builder::under_constructor`, `Builder::field` in `crates/elab/src/relational_context/proof.rs`; `docs/tactics/equation-rewrite-design.md` §10.7). `regex_dfa.hthr` registers `Seq`, `Alt` and `Star` and its chains use `rel_cong`; probes in `regex_dfa_tests.hthr` and, for a parametric type, `algebra_rel_tests.hthr`. Remaining: `rewrite` along a relation still refuses a constructor ("a form that is no application or λ"), because its walk rebuilds the term; and constructors of three or more fields have no registration form.
- 2026-11-11: The relation walk of `rewrite` crosses inductive constructor values too (`RelationRewrite::inductive`, `GoalNodes` reading a lowered value's fields): one or two fields, evidence at `T::C` as `rel_cong` reads it. `Regex::simp_same` and `Regex::deriv_simp_same` now cite no `same_seq`/`same_alt`: their steps are `simp_only` over `seq_same`, `alt_same` and the induction hypotheses. Closing.
