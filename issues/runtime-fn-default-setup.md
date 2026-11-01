---
title: The runtime fn generator in Heather and the default setup's pure fragment
status: open
labels: [native,compiler,metaprogramming]
area: heather-in-heather
milestone: [nh-front]
created: 2026-10-31
updated: 2026-10-31
---

Round R5 of `docs/compiler-milestones-proposal.md` (§4.2 N1, §7): the `runtime fn` generator and the default
setup's pure fragment.

## Scope

Narrowed by `docs/runtime-fn-setups-design.md` (§13) to slice R5d, the
integration round. The other slices have their own issues:
[[runtime-body-reflection-requests]] and [[runtime-fn-reflected-language]]
(R5a), [[runtime-default-setup-soundness]] (R5b),
[[declaration-prefix-generators]] (R5c).

- The `runtime` generator (design §2.2): reflect, judge in the elaborator for
  located refusals, publish `f::rt`, `f::judged`, `f::reflects`, `f::code` and
  `instance Compile(f)` as one group.
- `compile-x86 file f` requires `runtime fn f` and reads the `Compile(f)` instance in place
  of the Rust reflector's `_agrees` (design §10); the `examples/x86-native`
  files gain the prefix (from [[runtime-compile-opt-in]]: `mix.hthr` opts in
  explicitly, and unmarked functions are refused with an actionable message).
- `crates/elab/src/function_ir_source/` deleted once every example passes
  through the generator.
- `heather reflect`'s output ([[native-build-reflected-helpers]], landed as calls to a reflected FunctionIR program) comes from a `Compile(f)` instance instead of the Rust reflector, so a tool's pure parts are runtime fns.

## What it assumes from elsewhere

- **[[runtime-default-setup-soundness]]** owns `Setup`, the judgment, the lowering and `sound`; **[[runtime-fn-reflected-language]]** owns `rt` and the reflector.

- **[[pure-imperative-statements]]** owns the imperative spellings. Until it lands, the fragment's examples are written with `match` and recursion.
