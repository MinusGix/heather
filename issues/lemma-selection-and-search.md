---
title: One selection language for search, hint sets, and the used-subset that comes back
status: open
labels: [tooling,frontend,design,metaprogramming]
area: tactics
created: 2026-08-05
updated: 2026-11-06
---

From the 2026-08-05 riff under [[ai-facing-tooling]]. Not scheduled —
wants a bigger library to be worth it.

Three coupled pieces:

1. **Search as a CLI**: `heather search --type 'List<A> -> Option<A>'`,
   eventually `--goal <statement>`; `--json` emits JSONL for shell
   chaining. Type-directed beats name-directed in a proof language: the
   thing you know is the goal shape. Results must resolve through the
   one resolution judgment — never aspirational.
2. **The same selection expression feeds hint sets**: "every Nat theorem
   with le in the name" is one grammar whether browsing or handing a
   solver its lemma pool (`solve --with 'Nat::* name(le)'`).
   [[type-owned-namespaces]] gives the language its best axis (subjects)
   for free. This is Sledgehammer's architecture with the roles
   reassigned: the model is the relevance filter (cheap, casual,
   over-approximating), the solver searches, and reconstruction is free
   because the kernel checks whatever term falls out.
3. **The used subset, minimized** (Lean's simp? move): over-supply wide,
   the solver reports the lemmas that were load-bearing, the committed
   artifact names exactly those. Wide at exploration, narrow at commit —
   without minimization, AI-scale hint-spraying rots the library.

Side effect worth a breadcrumb from day one: used-subset reports
accumulate into a goal->lemmas corpus (premise-selection data arising
from normal use, impossible to reconstruct later). A `--log-used` flag
is cheap; design nothing else around it yet.

## Requirement-aware ranking

Type compatibility is not enough once declarations carry generalized
assumption scopes and profiles ([[implicit-logical-assumptions]]). For every
matching candidate, search should return the **requirement delta** against the
cursor's real elaboration context:

1. solver requirements already discharged;
2. missing exact propositions or narrow typeclass capabilities;
3. requirements derivable only after activating or supplying a broader
   profile;
4. concrete axiom-backed providers and the provenance they would add.

Ranking prefers candidates that add no requirements, then narrow unresolved
obligations, then broader profile requirements. This is a relevance order,
not a visibility rule: down-rank candidates rather than hiding them, since a
caller may have an easy special proof of the missing proposition. Profile
expansion must run through the same resolver as elaboration; search may not
claim that `ClassicalOn<A>` supplies `Stable<P>` unless the real provider edge
checks at that goal.

Do not introduce a blanket “classical theorem” flag for ranking. The theorem's
exact solver parameters, the context's available providers, and any resulting
axiom impact are the truthful data. A classically named profile may have a
constructive implementation at a special type, while an innocently named
exact proposition may be the genuinely difficult obligation.

Search results should keep both a constructive theorem and a materially
different classical convenience corollary when their bounds, witnesses, or
API shapes differ. Mechanically duplicated wrappers whose only work is an
inferable profile application should group under or defer to the narrow
source theorem rather than occupy an equal-ranked slot.

## What it assumes from elsewhere
- **[[type-owned-namespaces]]** owns subject organization. Assumed here:
  only that members are enumerable per subject.
- **[[grind-port]]** and any simp-alike own the solvers that consume
  hint sets. Assumed here: only that they accept a lemma pool and can
  report which members they used.
- **[[implicit-logical-assumptions]]** owns requirement footprints, profile
  providers, and their resolution precedence. Assumed here: search can query
  the same checked provider graph without recreating a classicality taxonomy.

## Log

- 2026-08-25: Added requirement-aware ranking from the assumption-profile
  design: implicitly expand profiles through the real resolver, rank by the
  additional obligations at the cursor, expose axiom impact, and down-rank
  rather than hide candidates with unmet requirements.
- 2026-10-23: Evidence from Arend (`docs/arend-survey.md` §6). Arend's CLI,
  built for coding agents, ships symbol search (`-ss`), proof search by a
  statement pattern with `_` wildcards and infix (`-ps "_ + _ = _ + _"`,
  matching subexpressions of parameter and result types rather than unifying
  whole types), find usages (`-fu`), class hierarchy with instance sites
  (`-ch`), scope at a definition (`-sc`), all with `--json`, and a daemon
  holding the checked library in memory. The premise above ("wants a bigger
  library to be worth it") is met: at about 2,500 declarations agents
  already grep for lemmas. Suggested first slice: name search and pattern
  search over module images, `--json`, no ranking yet.
- 2026-11-02: Piece 3's used-subset report exists for grind: `grind_report(names, hints)` says which hints and named lemmas the proof cites and which it does not, as a `tactic-report` warning (the `Say` host request, docs/host-elaboration-interface-design.md §23; [[grind-e-matching]]).
- 2026-11-06: The used subset must be closed under what the search stood on, not only what the proof cites: a hint can be needed without being cited (a *lurking* hint, Axolocl, CAV 2025). `grind_report` now says so ("not cited, but needed to find it", [[grind-report-lurking-hints]], docs/grind-design.md §9.6); a minimizer should keep those, or re-run the narrowed call before committing it. Over-supply has a cost of its own: one more lemma can exhaust a call's fuel ([[grind-unrelated-lemma-fuel]]).
