---
title: Move the declaration generators out of Rust and into the meta layer
status: open
labels: [metaprogramming,elaboration,design]
created: 2026-07-26
updated: 2026-07-27
---

Speculative / direction issue, not scheduled. Filed 2026-07-26 in the
priority discussion so the ambition is written down rather than assumed.

Every derived artifact today is **Rust that emits kernel terms**: the tier-0
and tier-1 lowerings, the recursor, no-confusion (disjointness and
injectivity), the `Wf` guard, the container schemas (`tab_cong`, `map`,
`tabulate`), `Acc`'s fording if it were ever generated. They are kernel-
checked, so they are not *trusted* — but they are not *in the language*
either. The project's thesis is a metaprogramming calculus with a modal
layer, and the kernel already carries it (`□(Δ ⊢ T)`, `letbox`, the code
recursors, `Trm_c`/`Typ_c` globals). The generators are the most obvious
thing that should eventually live there.

## The pull

- One less language. A user-written `deriving`-style generator, an
  optimization pass and a `Compile` instance are all the same kind of object
  ([[certifying-generator]], [[compile-typeclass-design]]), and today only
  the last of the three could be written by a user at all.
- It is what [[lsp-from-the-meta-layer]] and [[setoid-auto-lifting]] both
  assume exists.
- The elaborator stops being the place where language features live — the
  general complaint that motivated this priority round.

## The drag

- It wants [[surface-records]] and [[surface-polymorphism]] first: a
  generator is a generic function returning a record of code.
- It wants the implicit quotation / modal surface
  ([[surface-syntax]] round 2), which is a real syntax round on its own.
- [[box-synthesis-gap]] is closed but its conclusion binds here: elaborated
  code must emit `letbox`, not β-redexed meta-functions, and a generator
  written in-language is exactly the code that has to obey it.
- Migration is not all-or-nothing, and the honest first step is probably
  *one* small derived artifact (injectivity at a single field, say) written
  in-language and cross-checked against the Rust one, rather than a port.

## The question to answer before scheduling

Is the meta layer expressive enough to write the tier-1 lowering as it
stands — the `Wf` arity function, the code-valued predicates by large
elimination, the `Fin`-indexed ih — or does an in-language generator need
kernel/layer features that do not exist yet? That is a reading exercise
against `docs/delam/07` and `crates/kernel/src/rec.rs`, not a code round, and
it is what would turn this from "maybe" into a plan.

## Log

- 2026-07-27: Promoted from 'direction, not scheduled' to the ONLY route to a level-generic library, per [[surface-universe]] section 4. Checked against ch. 04 and the kernel rather than assumed: there is no encoding for universe-polymorphic functions (ch. 04 line 652) AND no code of any instantiation either, because UApp requires meta_layer (typing.rs:1425) while BoxTm checks its payload at Layer::Code (typing.rs:626) -- a layer-m term cannot sit inside a box. What IS well-formed is the flip, a polymorphic function returning code: 'forall l. box(|- T_l)', because code types live at level 0 (typing.rs:591,599) so UPi's body-at-its-declared-level requirement is met, and in_ctx preserves the universe context (typing.rs:275-277) so the boxed code may mention l. Ch. 04 (581-582) says that is WHY the layer-m restriction exists. Consequence for this issue: a universe-polymorphic library function is not compilable as such -- its generator is, once per level -- so 'fn f<l>' at the surface must elaborate to a layer-m generator plus auto-instantiation at each concrete level used. Caution: layers are not freely crossable (strict order and code promotion is a real operation), so 'a definition that moves between layers automatically' is a surface illusion the elaborator maintains and must be able to fail loudly.
