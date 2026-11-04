---
title: A comparison's Decide bit is its leb, so a guard is a decision
status: closed
labels: [stdlib,decidability,proofs,ergonomics]
area: tactics
created: 2026-10-30
updated: 2026-10-30
---

## Resolution (2026-10-30)

Landed as proposed, with one change to step 4:

1. `Decide<Nat::Le(n, m)>`'s bit is `n.leb(m)` (`Nat::leb_reflects`),
   `Decide<n = m>` at `Nat` is `n.same(m)`, `Int::Le`'s is `a.leb(b)` and
   `Rat::Le`'s `x.le_bool(y)` (their `le_of_*` / `not_le_of_*` pairs as the
   reflection). `dec` is unchanged. The `leb` bridge and `ne_of_same` moved
   up in `nat` so the instances can name them.
2. `instance<P: Decide, Q: Decide> Decide<P → Q>`, bit `!P.bit || Q.bit`,
   reflection `reflects_imp`. An arrow carrier had no canonical name; the
   elaborator now keys a non-dependent arrow by its class (`#Fn@class`,
   global `Decide::Decide#Fn`; `docs/traits-layer1-design.md` §4.1, amended).
3. `decide_intro` / `decide_elim` in `bool`.
4. `Format::canonical` is `decide_bit<…the four conditions…>()` with the
   proposition **spelled in the body**, not `decide_bit<F.Canonical(…)>()`:
   instance search does not unfold a defined proposition to reach the `∧`
   instance (filed as [[decide-at-defined-proposition]]). `Canonical` and
   `canonical_reflects` are gone; intro/elim are `decide_intro(…)` /
   `decide_elim(ok)` with the proposition inferred. `float/literal`'s
   `dy_exact` bits are `leb` with `leb_reflects`.

What moved: proofs that related an evidence-free `if a <= b` to `if h: a <= b`
or `match a.le_dec(b)` (the old bit was computed from `dec`, so a match on
`dec` reduced it). Only `Int`'s `min`/`max` lemmas did; they are
`decide_bit_split` now. The native frontend compiles only `BitVec`
comparison bits, which were already the comparisons, so its input is
unchanged. Closed `refl`s over `canonical` and `dy_exact` now evaluate the
kernel-accelerated `leb`/`same` directly; the whole library and its probes
check (`lib/_tests/std/core/bool_tests.hthr` is new).

`instance(n, m: Nat) Decide<Nat::Le(n, m)>` has `bit := or_bit(Nat::le_dec(n, m))`
(`lib/std/num/nat.hthr`), and `Int`'s, `Rat`'s and the equality instances the
same. A Bool guard a program writes uses `n.leb(m)`, so
`decide_bit<n <= m ∧ …>()` is never that guard, and a Bool-guarded record
field (`Finite`'s `ok: F.canonical(mag, bexp).IsTrue()`) has to build its
`Reflects` by hand: `Format::canonical_reflects` (2026-10-30), and the
`or_bit(…le_dec…)` bits in `float/literal`'s `Rat::dy_exact`.

Proposal, `docs/bool-guard-reflection-design.md` §3.1:

1. `Decide<Nat::Le(n, m)>` with `bit := n.leb(m)`,
   `reflects := Nat::leb_reflects(n, m)` (and the analogous `Int`, `=` bits);
2. `instance<P: Decide, Q: Decide> Decide<P → Q>` with bit `!P.bit || Q.bit`;
3. `decide_intro<P: Decide>(p: P): decide_bit<P>().IsTrue()` and
   `decide_elim<P: Decide>(h: decide_bit<P>().IsTrue()): P`, the `IsTrue`
   readings of `reflects_intro` / `reflects_elim`;
4. `Format::canonical := decide_bit<F.Canonical(mag, bexp)>()`, deleting
   `canonical_reflects` and making intro/elim `decide_intro` / `decide_elim`.

To measure before deciding: closed `refl`s over `canonical` and the literal
`exact` bits re-evaluate through the instance dictionaries
(`float_tests`, `arith_tests`, `literal_tests`); the kernel's stuck-`leb`
handling (`crates/kernel/src/conv.rs`) now applies to every decided `<=`;
and the native frontend lowers `if n <= m` through `decide_bit`
([[native-frontend-decided-matches]]), so the bit it sees changes from
`or_bit(le_dec)` to `leb`.

Related: [[omega-reads-bool-guards]], [[derive-decide-instances]],
[[class-ops-prop-vs-bool]].
