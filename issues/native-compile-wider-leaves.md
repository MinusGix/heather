---
title: Compile every structured region as a leaf of the effectful source
status: closed
labels: [native,x86,proofs]
area: heather-in-heather
milestone: [hih-pl-source, hih-tools]
created: 2026-10-25
updated: 2026-10-29
---

`Stmt::emit` (`lib/native/native_compile.hthr`) compiles a `Compute` leaf
only when it is a `Dataflow` region whose inputs and outputs fit the
registers S4's `Region::lower` places them in (`Prog::leaf`, `leaf_checks`).
`Sequence`, `Compose`, `Conditional`, `Call` and `Loop` regions are refused,
and so is a dataflow region with more live values than registers. Found
while proving S3.2 ([[native-effect-source-compiler]], 2026-10-25).

## Scope

- Each structured region form compiled by S4's lowering of it, entering
  `Target::goes_leaf`'s place in `Stmt::emit_runs` with that lowering's
  theorem (`function_ir_lower`'s structured forms, the bounded loop of
  [[function-ir-lowering-loops]]).
- Leaves that spill: their contract changes memory below RSP, so the
  invariant `Target::Placed` must survive a frame. That is the footprint of
  [[wp-proved-memory-contracts]], or a frame range added to the region's
  layout.
- `Call` regions: a total function lowered by S4 and called from the leaf
  ([[wp-callee-from-lowered-function]] gives the callee side).

## What it assumes from elsewhere

- **[[function-ir-verified-lowering]]** owns the lowerings and their
  theorems; this issue only plugs them into the statement induction.

## Log

- 2026-10-26: Re-scoped by `docs/native/native-real-programs-plan.md` (§3.4, round 4): compile every region form memory-resident, as S3.2 compiles statements (each node loads its operands from slots, computes, stores), with no register-pool limit; S4's `Region::lower` stays as the better lowering where a dataflow leaf fits. `Call` regions stay refused (the builder, [[native-source-builder]], inlines). Done when `tr`'s byte map lowers as a bounded FunctionIR loop and a 40-node leaf compiles. Probe: a 15-node leaf is refused today with no reason given.
- 2026-10-26: [[native-source-bytes]] compiles a leaf that is all pure or exactly one byte node (`Prog::computes`); a leaf mixing pure nodes with `BufferLoad`/`BufferStore` is refused. Splitting such a leaf at each byte node, as the plan's §3.1 describes, belongs to this round's memory-resident compile.
- 2026-10-27: Leaves done (`lib/native/native_compile_nodes.hthr`). `Prog::computes` takes a leaf through S4 whole when it is all pure and fits (as before, `Prog::pure_leaf`); otherwise, when every node works at width 64 (`nodes_wide`), a node at a time (`Prog::each_node`): a byte node by its own code, any other node by S4 as a one-node region whose output is renamed to an id it does not read (`Prog::node_alone`, `Node::renamed`, `Node::spare`) and stored to the node's own slot (`Prog::leaf_into`, results stored to chosen homes). So the register pool, the byte-node-alone rule and "no read of a word the leaf writes" are gone, `Add(64, x, x, y)` included. Why width 64: the region keeps a result at every width (`Valuation::set`), a slot keeps it at its port's width (`Env::settle`); they agree on words when every node reads and writes words (a comparison's bit reads back as the word the region holds, `Node::run_word`), and not otherwise (a shift right at 64 read at width 1, a sum at 8 read at 64). The proof is one equation, `Env::steps_settle`: the leaf settles as its nodes do one at a time, a word written twice put over (`settle_put_over`). Refusal reasons 10 (a narrow node, so no node at a time) and 11 (S4 refused a node alone); 1, 2, 3 and 6 now come only from an all-pure leaf with a narrow node. Probes in `lib/_tests/native/native_compile_tests.hthr`: `long_leaf` (40 nodes, a running sum read and written over one word) and `mixed_bytes` (byte loads, a store back, arithmetic in one leaf) are written by `write-elf` and run in `crates/cli/tests/native_cat.rs` (`wider_leaves_run`). Left: the `Sequence`, `Compose`, `Conditional` and `Loop` regions memory-resident, and `tr`'s byte map as a bounded FunctionIR loop.
- 2026-10-27: [[native-source-builder]] landed. The builder cuts nodes into leaves with `List::fits_leaf` (lib/native/native_build.hthr), a copy of what `Prog::computes` takes today; when mixed or memory-resident leaves land, relax that predicate (and update the lowerings fixed in lib/_tests/native/native_build_tests.hthr).
- 2026-10-29: Regions done; closed. `Sequence`, `Compose`, `Conditional` and `Loop` compile memory-resident wherever the region is scoped from every word (`lib/native/native_structured.hthr`'s `StructuredRegion::scoped`: nodes wide, each word read written before it, a branch on a bit that is its word's low bit, a loop in counted form: distinct parameters and outputs, a count and bit apart from them, moves that read no word an earlier move wrote). `StructuredRegion::code` (native_compile) lays a loop out as leaves around its body: the count and parameters moved in, a zero test at the head, the body, the next state moved into the parameters, a test of the exit bit, the count less one and a JMP back, the outputs moved out at the end; its homes check is `Homes::region_checked` (native_alloc), the loop's set closed over its head as a `Repeat`'s is. The proof is once, in the statement induction: `StructuredRegion::code_runs` (`lib/native/native_compile_structured.hthr`) runs each region's code as its meaning (`StructuredRegion::meaning`, native_structured_meaning), a loop by induction on its count (`Target::loop_head`), each pass the body's run from the pass's own valuation (`faithful` over `Scope::pass`); `compute_same` makes the meaning the region's run settled, which is what `Stmt::denote` says. `tr a-z A-Z` with the byte map as one loop region (a conditional in its body) is written by `write-elf` and runs (`crates/cli/tests/native_cat.rs`, `structured_regions_run`); refusals name a region not scoped (reason 0, its kind) and a loop whose live-after words it clobbers (13), probes in `lib/_tests/native/native_structured_tests.hthr`. `Source::refusal`'s scan now carries what is live after each statement, as `emit` does, since a region's code depends on it. The builder's `List::takes` needs no relaxing: it already takes what `Prog::computes` does; the builder emits no regions (follow-up [[native-build-loop-regions]]). `write-elf`'s Rust allocator reads only dataflow leaves, so a region source falls back to the Heather allocator on the fork ([[native-region-spelling]]).
