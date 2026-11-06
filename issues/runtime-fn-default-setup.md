---
title: The runtime fn generator in Heather and the default setup's pure fragment
status: open
labels: [native,compiler,metaprogramming]
area: heather-in-heather
milestone: [nh-front]
created: 2026-10-31
updated: 2026-11-06
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

## Log

- 2026-11-01: The prefix mechanism R5d uses is built ([[declaration-prefix-generators]]): `runtime` is called as `runtime("f", setup…)` after `f` is published, and `lookup("f")` gives its `GlobalRef` (docs/value-definitions-design.md §3.2).
- 2026-11-04 (round 1): the generator, the setup record and the `Compile` class
  (`lib/native/runtime/runtime.hthr`, design §16.8). `runtime fn f` publishes
  `f::rt`, `f::world`, `f::judged`, `f::reflects`, `f::code`, `f::agrees` and
  `instance Compile(f)` for N1's word fragment; callees are found by the walk
  (a global with a published `g::rt`) and answered by table index, so
  `f::agrees` assumes `Tm::CallsAgree`. Probes:
  `lib/_tests/native/runtime/runtime_tests.hthr` (calls, connectives, sharing,
  a convoy, instance search, five refusals). Host: `DeclForm::AsInstance`, and
  the numeral reader reads runs whole. Still open here: the program wrapper
  (one FunctionIR program from the callees' instances, discharging
  `CallsAgree`), `compile-x86` on `Compile(f)` (with `mix.hthr` opting in and
  unmarked functions refused), the Rust reflector's deletion (it also covers
  loops, which `rt_lower` does not yet: `Fold`, measured recursion), `heather
  reflect` from instances, and callees by instance search so a hand-written
  instance can be called. Filed [[class-carrier-as-term]].
- 2026-11-04: 2026-11-04 (round 2): the program wrapper and `compile-x86` on runtime fns
  (design §16.9). `runtime fn f` now also publishes `f::program`, one FunctionIR
  program of `f` and every runtime fn it reaches (callees first, each placed
  once, each from its `Compile` instance with its calls renamed,
  `Function::relabel`), and `f::agrees` is unconditional:
  `program_eval(f::program, last, [xs…]) = f(xs…)`, from `Compile::part` per
  instance and `program_eval_sources`. The rt lowering moves a call's result
  off the port the call writes (RAX does not survive the next call).
  `compile-x86` compiles a marked function through `f::program`/`f::agrees` and
  refuses an unmarked one by name, except programs with a loop or a test through
  a `Bool` helper, which stay on the Rust reflector. The loop-free examples are
  marked; `mix.hthr` became `word_mix.hthr` and `program.hthr` `levels.hthr`
  ([[runtime-fn-named-like-its-module]]). Filed [[runtime-generator-imports]].
  Still open here: `Fold` and measured recursion in the lowering, then deleting
  `crates/elab/src/function_ir_source/`; `Bool` helpers; `heather reflect` from
  instances; callees by instance search.
- 2026-11-05: gardener: cites a file it shares with [[compile-typeclass-design]] (`lib/_tests/native/runtime/runtime_tests.hthr`).
- 2026-11-05 (round 3): loops in the lowering, proved once (design §16.10).
  `rt` gains `Ty::Count` (a `Nat` held in a word, as its `toNat`),
  `Op::ToNat` and `Tm::Case` (a `match` on a count).
  `lib/native/runtime/rt_loop.hthr`: a pass is the body in tail mode
  (`Tm::tail_sound`), a fuel recursion is a `Loop` bounded by its fuel
  (`Fun::fuel_sound`, from its two structural equations, `refl` each), a
  measured one a `Loop` of `2^64 - 1` passes (`Fun::measured_sound`, from
  `Fun::Guarded`, which is the function's `f::ext` and `f::irrel`; both now
  spelled). Probes: `lib/_tests/native/runtime/rt_loop_tests.hthr`
  (`sum_down`, `count_down`, a wrong step refused). Not yet wired: the loops
  are not in `Fun::lower`/`Setup`, the reflector does not read a fuel
  `match` or a measured body, calls do not pass a `Count`, so `compile-x86`
  still sends loop programs to the Rust reflector. Still open here, in
  order: that plumbing (§16.10's last paragraph), `compile-x86` on the loop
  examples and deleting `crates/elab/src/function_ir_source/`; `Bool`
  helpers; `heather reflect` from instances; callees by instance search.
  `Fold` over buffers is not on this path (no x86 example folds a buffer)
  and still waits on buffers in `StructuredRegion::eval` (§16.6).
- 2026-11-06 (round 4): loops through `Setup` and `Compile` (design §16.11).
  `Fun::lower_any` dispatches on `RtShape` (plain, fuel, measured) and
  `Setup.sound` is over the shapes; `Setup::compile_fuel`/`compile_measured`
  are the loop instances, whose equations the generator proves (`refl` per
  word for a fuel, `f::ext`/`f::irrel` for a measure). A `Count` parameter
  crosses a call as a word read by `toNat`. The reflector reads a fuel's
  `ElimNat` (host `Arms`) and a measured function's `f::body`. A leaving
  pass now writes every `next` word, which the x86 emission needed. The six
  `loop_*` examples are runtime fns and `compile-x86` compiles them through
  their instances; the Rust reflector's loop code is deleted (an unmarked
  loop is refused, naming the marker). Probes:
  `lib/_tests/native/runtime/runtime_tests.hthr`'s loop section. Still open
  here: `Bool` helpers (then the rest of `function_ir_source/`), `heather
  reflect` from instances, callees by instance search, a `decreases` measure
  that is not a word's `toNat`.
