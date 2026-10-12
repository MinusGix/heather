---
title: Run a field's default where the construction has local bindings
status: closed
labels: [frontend,elaboration,defaults]
created: 2026-10-01
updated: 2026-10-12
---

A record field's default (`name: T := e`,
`docs/named-arguments-design.md` §9.5) is checked against the field's type
in the empty local context. That is right only when the construction has no
local bindings: the type is moved out of the construction's context as it
stands. Under locals the elaborator refuses ("give it by name"). Even a type
that mentions no local carries global references weakened to the context's
length, so a shift test is not a closedness test.

The fix is to close the goal over the construction's locals as Π binders,
check the default against the closed goal (`split_all` introduces them), and
apply the result to the locals. That is §9.4's mechanism 1 with a stored
goal, and the same machinery parameter defaults (`fn f(b: Nat := 0)`) need.

## Log

- 2026-10-01: 2026-10-01: Second gap, same machinery. A default whose failure only the kernel sees (`refl`, which the elaborator leaves to the gate) is reported at the record's declaration, where the default's syntax is, rather than at the construction. A failure during elaboration (an omega leaf, the bundles' case) is reported at the construction. Both are fixed by elaborating a default as a term owned by its construction site, which the Π-closing round does anyway.
- 2026-10-12: 2026-10-12: Landed with parameter defaults (docs/named-arguments-design.md §9.6). Not the Π-closing this issue proposed: the default is checked in the construction's own context made unreachable by name (`Cx::hygienic` renames each local to a reserved `__caller_<name>` spelling and drops the dictionaries and operator symbols). The goal stays open in those locals, a tactic default sees them as hypotheses by type, and no local can capture a default's name. `Pinned(k)` under a parameter `k`, and `pos: 0 < value := omega` under `hk: 0 < k`, now elaborate; the refusal is gone, and its test became a positive one. The second gap (a kernel-only failure reported at the record) moves to [[default-kernel-failure-reported-at-declaration]], shared with parameter defaults. Closing.
