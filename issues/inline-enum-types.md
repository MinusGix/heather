---
title: Inline enum types in signatures: Result<T, enum EOF|Unexpected(Char)>
status: open
labels: [frontend,syntax,design]
created: 2026-08-13
updated: 2026-08-13
---

Sketch from the showcase critique (2026-08-13). Rust makes declaring a
fresh error enum annoying, so real code degrades to one Big Blob Enum;
narrow per-signature error types would fix the incentive:

    fn tokenize(src: String) -> Result<List<PTok>, enum EOF|Unexpected(Char)>

The cheap reading, and the recommendation: the syntax declares a **fresh
signature-scoped nominal type** (auto-named, tags as written). The kernel is
already structural underneath — a surface enum lowers to sums-of-Σs — so
this is sugar for a declaration, not a new type former. Deliberately NOT
the expensive reading: OCaml-style polymorphic variants with row
polymorphism (what would make narrow error types *compose* across `?`
automatically) are a type-system commitment out of proportion to the
ergonomic win; without rows, `?` needs From-style embedding, which the
trait layer can carry.

Parked with it (named in discussion, not designed): "condition detection
for theorem generation" — deriving per-condition lemmas from the error
type's tags is the row version's payoff and waits for it.

Open: naming/printing of the fresh type in diagnostics; whether two
syntactically identical inline enums in one file are one type or two
(leaning two — nominal means nominal).
