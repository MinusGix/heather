---
title: Make add, sub, neg, and toInt width-bounded by definition
status: open
labels: [library,bitvec,x86,performance]
created: 2026-09-07
updated: 2026-09-09
---

[[bitvec-bounded-add-sub]] proved `ripple_add`/`ripple_sub` equal to the
iterated `add`/`sub`, and the kernel round in [[bitvec-closed-reduction-cost]]
made structural consumers over ripple results cost the width. What still costs
the operand's magnitude is every definition that routes through the iterated
forms: `add` and `sub` themselves (`iterate_increment` over `toNat(b)`), hence
`neg`, `signed_overflow_add`/`_sub`, `signed_lt_bit`, `mul`
(`ofNat(toNat * toNat)`); and the negative branch of `toInt`, which is
`int::sub(OfNat(toNat(x)), OfNat(2^n))` — `subNat` one `ipred` per unit of
`2^n`. `signed_overflow_add(64, s, s)` over two sign-1 sums goes through
`add(64, s, s)` with a `2^63` count and aborts the checker with a native
stack overflow; `toInt(64, ·)` of a negative value exhausts fuel, and so does
`int::sub(OfNat(2^63), OfNat(nat::pow(2, 64)))` alone.

## Plan

- Swap the definitions rather than adding parallel ones: `add := ripple_add`,
  `sub := ripple_sub`, `neg` through `ripple_sub`; keep the iterated forms as
  `iter_add`/`iter_sub` with `ripple_add_eq_add`/`ripple_sub_eq_sub` renamed to
  the equations between them, so `toNat`-counted reasoning stays available.
- `toInt` stays as it is. Its negative branch stopped costing the magnitude
  when [[int-arithmetic-over-nat-primitives]] landed (one synchronous
  `subNatNat` descent), so the `complement` respelling this plan once carried
  — and the structural-induction proof it owed — is dropped (2026-09-09).
- `mul` is out of scope. The reason is not `mul`'s own spelling — `nat::mul`
  is one run multiplication since [[nat-run-algebra-primitives]] — but
  `ofNat` above `2^n`: `mod_succ` is a `decreases` loop subtracting `2^n` once
  per iteration, so a product above the width costs up to `2^n` iterations,
  and `nat::mod` is not a run class either. A width-bounded `mul` therefore
  wants either a shift-and-add spelling or a run-friendly `ofNat`; note which
  if left.
- Fallout, smaller than first expected (survey 2026-09-09): `ripple_add_comm`
  and `ripple_add_sub_cancel` already exist, so the two named transports are
  pre-paid. The x86 and FunctionIR customers (`lib/std/arch/x86_64/{block,
  calls,model}.hthr`, `crates/elab/src/function_ir_x86_lower.rs`) name
  `iterate_increment` directly with small literal counts for RIP advances, and
  it keeps its name, so those proofs do not move; the native call emitter
  (`crates/cli/src/native/calls.rs`) already goes through
  `add_eq_of_ripple_add`, which becomes definitional. What remains unknown
  until the build says: which proofs lean on the iterated forms' definitional
  behaviour (`iter_add(n, a, zero)` reduces to `a`; the ripple does not) and
  need a transport through the equations.

## Acceptance

- The consumer rail `consumers_over_computed_machine_width_producers_cost_the_width`
  in `crates/elab/tests/lib_std_bitvec.rs` gains the cases this round had to
  leave out: `signed_overflow_add(64, s, s)` over two sign-1 sums, a negative
  width-64 `toInt`, `signed_lt_bit` at the `2^63` boundary against computed
  operands, all by `refl` under ordinary fuel.
- Plain full `scripts/test` green; no x86 or FunctionIR certificate gets slower
  by more than noise (their warm generated checks are the timing datum in
  [[function-ir-x86-comparison-materialization]]).
- No new axioms; the iterated forms and their equations remain in the module.

## What it assumes from elsewhere

- **[[bitvec-bounded-add-sub]]** supplies the equations and the transport
  lemmas.
- **[[bitvec-closed-reduction-cost]]** owns the kernel side; the
  stack-overflow-instead-of-`OutOfFuel` behaviour is [[kernel-native-depth-budget]],
  not this issue.

## Log

- 2026-09-08: The reusable callee round (`cb877f2`) staged CALL displacement arithmetic in small proved increment/decrement steps and chose inputs 21 and 1 for its executable, while keeping the summary arbitrary-input. This predates the incoming kernel strategy fix; re-evaluate this customer before attributing residual cost or migrating its arithmetic.

- 2026-09-08: Merge integration is exercising `add_eq_of_ripple_add` and `sub_eq_of_ripple_sub` for native CALL displacement certificates, replacing staged increment/decrement chains without changing the canonical instruction semantics. This is an explicit proof consumer, not the default-operation swap owned here.
- 2026-09-09: The negative branch of `toInt` no longer costs the magnitude: `int::sub(OfNat(toNat(x)), OfNat(2^n))` is one synchronous `subNatNat` descent since [[int-arithmetic-over-nat-primitives]]; width-64 negative `toInt` is a rail in `lib_std_bitvec.rs`. `bitvec::add`/`sub`'s own `iterate_increment` is unchanged.
- 2026-09-09: Plan re-evaluated against the Nat/Int run work (coordinator survey): the toInt respelling is dropped (already cheap), mul stays out with the cause named as ofNat above 2^n, and the fallout list shrinks — the comm/cancel transports exist, the x86/FunctionIR customers name iterate_increment (unrenamed) with literal counts. The depth budget ([[kernel-native-depth-budget]], f5d73da) now refuses the 2^63 cases with OutOfFuel, so the acceptance rail's refusal control (nested_scrutinee_values_are_refused_rather_than_aborting in lib_std_bitvec.rs) must flip to a success control when the swap lands. Round chartered.
