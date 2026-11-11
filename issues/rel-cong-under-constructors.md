---
title: rel_cong and relation rewrite under a constructor with a registered congruence
status: open
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
