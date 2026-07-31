---
title: LocalCtx/GlobalCtx are eagerly cloned Vecs; consider a shared-spine representation
status: open
labels: [kernel,performance]
created: 2026-07-31
updated: 2026-07-31
---

Every profile from the [[subst-visits-closed-subtrees]] round (2026-07-31,
`code/check-identity-recursor` and neighbors) shows `Vec<CtxEntry>` and
`Vec<GlobalBinding>` clone/drop at a steady ~5–8%, independent of that
round's changes: `LocalCtx`/`GlobalCtx` are plain `Vec`s, and typing/
conversion clone them wholesale to extend by one entry (binder descent
does this constantly).

Candidate: an `Rc`-shared spine (persistent snoc list, or `Rc<[Entry]>`
with copy-on-extend), so extending by one is O(1) and dropping a derived
context frees one cell. Contained representation change — contexts are
*outside* the term language, so no substitution/conversion rule is
touched — but it has real surface: `LocalCtx` appears in terms
(`CodeTy`/`CodeTm`/`TyPi`/letbox/recursors) and is compared structurally
by conversion at boxed types, so the representation must keep cheap
structural equality, and `PartialEq` cost is on the conversion path.
Indexing direction matters too: entries[0] is outermost, `LocalVar` 0 is
innermost — a snoc spine matches variable lookup but reverses iteration.

Trigger: a profile where context clone/drop is a top-5 line *after* the
schema round ([[schema-construction-caching]]) lands — much of today's
context cloning is inside the fresh telescope construction that round
would eliminate; measure again before paying the churn here.
