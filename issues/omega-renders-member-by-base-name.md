---
title: omega renders a member function by its base name, which is unbound at the goal
status: open
labels: [proofs,omega,elaboration,bug]
area: tactics
created: 2026-09-05
updated: 2026-09-05
---



Found by the mutual-recursion design pass (2026-09-05,
docs/mutual-recursion-design.md §7). A goal over `xs.len()` reconstructs a
certificate that names `len(…)`, which is unbound outside `list`
(``error: unbound name `len` ``); writing the measure as `list_len(xs)` avoids
it. The same renderer produces `unexpected character 'â'` when the context
holds a generated `f#grp(k)` hypothesis — an unspellable name rendered into
source text. Omega's certificate route is render-then-reparse
(docs/termination-measures-design.md §3 explains why `__dec_` names are not
`#`-hygienic), so any context or goal atom the renderer cannot spell
qualified is a silent hole in the default closer. Fix: render members
qualified (`List::len`) and skip or abstract unspellable context entries.

## What it assumes from elsewhere
- **[[omega-certificate-imports]]** owns how a certificate names imported
  lemmas. Assumed here: only that the renderer is the one place atoms are spelled.

## Log

- 2026-09-05: Half fixed (2026-09-05, mutual-recursion round): Elaborator::spell_term_source spells a global qualified wherever its base name does not resolve back to it, and omega_cert's reconstruction uses it; a context entry reflect_assumption cannot spell is skipped rather than aborting the goal. Test: omega_cases reconstructs_over_a_member_atom_spelled_qualified. The 'â' rendering could not be reproduced once obligations are lifted; stays open until a repro or a decision closes it.
- 2026-11-05: gardener: cites a file it shares with [[fn-recursion-means-the-function]] (`docs/termination-measures-design.md`).
