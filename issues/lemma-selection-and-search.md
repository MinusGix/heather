---
title: One selection language for search, hint sets, and the used-subset that comes back
status: open
labels: [tooling,frontend,design,metaprogramming]
created: 2026-08-05
updated: 2026-08-05
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

## What it assumes from elsewhere
- **[[type-owned-namespaces]]** owns subject organization. Assumed here:
  only that members are enumerable per subject.
- **[[grind-port]]** and any simp-alike own the solvers that consume
  hint sets. Assumed here: only that they accept a lemma pool and can
  report which members they used.
