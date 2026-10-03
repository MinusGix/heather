---
title: A structured certificate declared what nothing read, spelled each carry quadratically, and proved preserves once per register
status: closed
labels: [x86, performance, certificate, compiler]
code: crates/elab/src/function_ir_x86_lower/structured_cert.rs @ ae0a338
created: 2026-10-03
updated: 2026-10-03
---

The `Fields` formatter's two certificates (`field_low`, `field_high`, from
`function_ir_x86_lower/structured_cert.rs`) were the largest line of a cold
`build-x86` of `examples/x86-native/wc.hthr` once [[goal-world-copies-psi]]
landed: ~15.7k generated declarations, ~47% of item time
([[x86-certificate-per-declaration-constant]], 2026-10-03 log). Attributed
per declaration, the cost was **not** a flat per-declaration constant: half of
it sat in the top thousand declarations, in a handful of families.

## What it cost, by family (cold wc build, width one, before)

| family | share of the formatter | what it was |
|---|---|---|
| `_preserves` | ~15% | sixteen arms per node; each arm converts `read_gpr(r, {n}_after(before).gprs)` against the children's states, i.e. evaluates the machine state once per register |
| leaf `_instructions_k` | ~10% | the instruction spine, read only by the leaf's execution chain |
| `_carry` | ~9% | `at_width(64, s, 0)` spelled inline: a 64-deep match, quadratic text (~18 KB per carry), elaborated per crossing |
| `_artifact`, `_rip` (inner nodes), leaf `execute_from_k`, `block_is_allowed`, `artifact`, `gprs_congruent`, `bytes`, `byte_length` | ~9% | declarations no parent and no exporter reads |

## Fix

- **Unread declarations are not emitted.** `generate_selected` takes a
  `LeafUse`; a structured leaf (`LeafUse::Structured`) emits its instruction
  list as one literal and none of the execution chain, `BlockArtifact`,
  register congruence or its own byte facts. The fold states execution as
  `structured_after` by `refl` and the bytes from its own literals, so none of
  them was read. Only the root publishes `_artifact` and `_rip` (tests and
  callers read the root's; no parent reads a child's).
- **A carry places its value through one helper per width.**
  `{root}_at_width_W(width, s)` is declared once per certificate and width;
  `_carry_at` still holds by `refl`, through one δ-step.
- **A composite node's `_preserves` is one proof at a neutral register**
  (`Frame::Any`): sequence, crossing, parts and branch nodes compose their
  children's `_preserves` under `λ protected`, with a `{child}_kept` lemma
  per child turning the node's `Protected` premise into the child's (a
  sixteen-arm split over `Protected` alone, which reduces to a constructor).
  The states then convert by unfolding `_after`/`structured_after`, once, at
  any register. A dataflow node keeps its per-register arms (`Frame::Each`):
  its leaf reaches a register's value only by evaluating the block.

What did not work: transporting the arms along one whole-state equation
`{direct} = {n}_after(before)` by `refl`. Converting two whole
`MachineState`s ran the kernel out of fuel at a leaf (it compares memory and
flags too), where a `read_gpr` projection stays lazy.

## Result

Standalone probes (each certificate dumped and checked with `heather check
--cache --timings` over the same library, width one, cloud box):
`field_low` 45.2 s → 25.1 s (6,712 → 5,759 declarations), `field_high`
58.8 s → 35.6 s (8,969 → 7,692).

The whole build, `scripts/perf ab --base 200fb73 --file
examples/x86-native/wc.hthr --samples 2 --kernel-workers 1` (cold, cloud box):
wall 305 s → 228 s (−25%, samples separate), kernel gate −24%, peak RSS
1.18 GB → 0.81 GB. The two formatter modules' item time 120 s → 70 s (−42%;
15,681 → 13,451 declarations). Counters moved as a smaller certificate moves
them (eval steps −21%, conversion misses −18%); no `conv_out_of_fuel` or
`conv_not_convertible` change.

## What is left in the formatter after this

`_decodes` (~12%), the dataflow `_graph` witnesses and `_correct` (~10% each),
`_layout`, `_byte_length`, `_bytes_are`. None is unread; each is one
conversion per node. Separately, elaborating `Cons`/`Nil` at
`List<Instruction>` spends a few ms per list in `instance_match`, growing with
the module: a frontend cost, not this generator's.

Overlap: the `wc`-as-a-command design ([[native-wc-as-a-command]]) replaces
`wc`'s generated `%7d` formatter with a library-proved loop. This round's
cuts are in the structured fold itself, so they apply to every structured
lowering (pieces, typed artifacts, the read profile's formatters), not only
`Fields`.

## Log

- 2026-10-03: filed and fixed in one round (this file).
