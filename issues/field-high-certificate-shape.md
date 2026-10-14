---
title: A structured certificate built each node's facts against its computed type and converted lookups at a literal width
status: closed
labels: [x86,performance,certificate,compiler]
code: crates/elab/src/function_ir_x86_lower/structured_cert.rs @ 71cf2dd
created: 2026-10-13
updated: 2026-10-13
---

Found 2026-10-13 while taking up the lead [[suite-iteration-chokepoints-2026-10]]
left for `field_high_certifies`: its cost was in the shape of what the
structured generator (`function_ir_x86_lower/structured_cert.rs`) writes per
node, not in the harness.

## How it was measured

The test's emission, dumped and checked standalone over a replayed library
(`heather check --cache`, width one, release binary), per
[[structured-certificate-cost]]'s probe method. One finding about the method:
**`--timings` is not free on a module this size** — the same check took
24.7 s without it and 34.7 s with it, the difference showing up as the
module row's `other`. Item rows still attribute correctly; whole-run seconds
should be taken without the flag.

`field_high` lowers to 247 structured nodes (124 leaves, 63 crossings, 30
branches, 30 sequences) and ~7.7k declarations. Before this round its item
time was ~40 s, spread over the per-node kinds (none past an eighth), with
leaves about 57% of it.

## What was found, by cause

1. **Composite nodes' facts were built against the node's computed type.**
   A branch's `_decodes` and `_layout` were anonymous constructors checked
   against `StructuredDecodes({n}_code(), start)`, so the elaborator reduced
   the node's type to its conjunction first; its `_byte_length` and
   `_bytes_are` spelled the append chain out, every jump's encoding included,
   and elaborated it per node. Branch `_decodes` was ~95 ms, `_byte_length`
   ~67 ms (body ~61 ms of it).
2. **Valuation lookups at a literal width ran in lockstep with the other
   side.** A leaf's graph `⟨refl, …⟩` and its `_correct` compared lookups
   `{n}_valuation(values)(64, id)` with a defined term (`{n}_value_k(values,
   64)`, `add(64, …)`, `read_gpr(…)`). The lookup's `leb` scrutinee is a
   δ-application, so conversion's stuck-elimination rule takes one δ-step on
   *both* sides per step (crates/kernel/DESIGN.md, the 2026-09-18 refinement):
   the other side's width-64 `add` unfolded once more for every step of the
   dispatch. One lookup ending in `{n}_value_2(values, 64)` took ~10k eval
   steps; the same lookup at a neutral width took ~130, at width 8 ~870.
   Not [[valuation-lookup-case-step-cost]]'s cost, which was the lookup's
   own: a lookup compared with a variable is cheap at any width; here the
   cost is the other side's unfolding. A two-instruction leaf's `_graph` was
   ~60 ms, 49 of it gate.
3. **A leaf's `_preserves` was sixteen arms at named registers**, each
   converting `read_gpr(R, {n}_after(before).gprs)` against the leaf's own
   state at that register, which evaluates the block's state per register.
4. **A structured leaf kept the standalone block's graph plumbing**: the
   region declaration (`_raw`), its `RegionHolds` proof, a `Context` record
   holding the graph, node lists and `NodesHold` stages that project each
   equation back out, and `_refines_function_ir` rebuilding the record. Only
   the node's `_correct` read them.
5. An empty leaf's instruction list was the literal `[]`, which resolves its
   collection instance first: ~38 ms, more than a two-instruction list.

## What changed

- `lib/std/arch/x86_64/x86_64_structured_block.hthr`: twelve lemmas state a
  node's `_byte_length`, `_bytes_are`, `_layout` and `_decodes` from its
  children's, one per fact and constructor (`structured_sequence_length`,
  `structured_branch_decodes`, `structured_near_branch_bytes`, …). The
  generator cites them; the elaborator meets the node's type at the
  constructor after one δ-step of `{n}_code()`. `lib/filter_step_piece.hthr`
  had its own `structured_sequence_length`/`_bytes` with the same
  statements; they are gone, its callers resolve to these.
- Each dataflow node's equation is a lemma `{n}_holds_{out}(values, w)`
  proved by `refl` at a neutral width and used at its own; the lookups a
  leaf's interface reads (its inputs and result) are `{n}_at_{id}(values,
  width)`, likewise. The exception is a comparison: its `_test_` Boolean
  is stated at the operand width, so its equation `{n}_holds_{out}(values)`
  is still `refl` at the literal width (one per branch, not per node).
- A leaf's `_preserves` is one proof at a neutral register,
  `{leaf}_preserves_protected(register, before, protected)`: the node and
  its leaf protect the same registers (`clobbered`), so their `Protected`s
  unfold to the same arms (a `_kept` lemma bridges them if they ever
  differ). `Frame::Each` is gone.
- `generate_selected` under `LeafUse::Structured` writes a `Context` whose
  fields are the inputs' placements and each node's equation
  (`holds_k: NodeHolds(values, node_k)`), read as `context.holds_k`; no
  region, graph stages, node lists or `_refines_function_ir`. The node
  builds the context from its `_at`/`_holds` lemmas. Standalone blocks are
  unchanged.
- The empty instruction list is `Nil<Instruction>`.

## Result

Standalone checks of the dumped emissions, release binary, width one, no
`--timings`, same cloud box, interleaved:

| piece | before | after |
|---|---|---|
| `field_high` | 39.3–39.9 s | 15.8 s |
| `field_low` | 28.6 s | 11.1 s |

`field_high`'s item time 39.8 → ~15.5 s (gate 12.9 → 4.9 s, body 11.9 →
5.5 s, elaborator `whnf` 5.0 → 0.4 s, instance matching 3.7 → 0.7 s);
text 6.35 → 5.69 MB.

## What is left

Spread thin again, the largest kinds ~1–2 s each over the whole piece: leaf
`_value_N_after_node_N` proofs, a one-instruction leaf's
`_preserves_protected` (fifteen arms by evaluation), `_bytes_are` of a leaf
with a 64-bit immediate (evaluating its encoding), branch `_correct` and
`_span`. The remaining structural lever is the node count: a `place` is six
nodes, two of them an empty true arm and its branch's sequence
([[structured-lowering-codewhen]] would remove the empty arm).

## Log

- 2026-10-13: 2026-10-13: the node-count lever is [[structured-lowering-codewhen]] (landed): a place is five nodes, field_high 15.8 → ~14 s standalone.
