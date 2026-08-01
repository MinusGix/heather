---
title: A record type cannot be passed as a Val -> Type function value
status: open
labels: [frontend,elaboration,types]
created: 2026-08-01
updated: 2026-08-01
---

Found during [[cross-ir-refinement]] (2026-08-01): the clean general form of the cross-IR refinement family is `RefinesOn(dom: Val -> Type, p1, i1, p2, i2)`, but it is not writable today. `NatEnv(e)` in expression position is read as the record's *constructor*, and its value parameters become uninferable ("cannot infer the value argument(s) of `NatEnv`") — for both `λ (e: Val) => NatEnv(e)` and `fn NatArgs(e: Val) -> Type { NatEnv(e) }`.

This is the type-level sibling of [[constructors-as-function-values]] (closed): that round made *value* constructors first-class; a record used as a type-valued function hits the same constructor-vs-type ambiguity one level up. With types-as-expressions landed, a record type in expression position ought to denote the type, not the constructor — or at least be disambiguable.

Concrete consumer waiting: replace `RefinesNat2` in lib/ir_v1.hthr (see the comment above its definition) with the general `RefinesOn`.
