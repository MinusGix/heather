---
title: Make generated FunctionIR x86 refinement scale past small DAGs
status: open
labels: [compiler,function-ir,x86,proofs,performance]
created: 2026-09-01
updated: 2026-09-12
---

The binary-ALU expansion probed the generated x86 refinement at 20 FunctionIR
nodes and 22 selected instructions. Selection and allocation were effectively
instantaneous, but the end-to-end Heather module had not completed after five
minutes when run alone. The same mixed graph at five nodes and seven
instructions checks in about 64 seconds on the same debug build.

The generator already names machine states and instruction-local result/frame
facts. The remaining suspicious shapes are repeated theorem parameters that
carry the entire `RegionHolds` spine and node equations selected by increasingly
deep `.right` projections. Measure item/frontend/kernel time before changing
the proposition. Likely experiments are named graph-suffix facts, factoring
graph equations out of every placement theorem, and a generated placement-state
certificate whose steps refer to opaque predecessor facts.

## Acceptance

- A mixed 20-node binary-ALU DAG checks comfortably inside the normal test rail.
- A 100-node chain or layered DAG has a bounded stress rail and does not show
  superlinear proof-composition growth.
- Measurements separate selection, source rendering, frontend elaboration,
  and kernel checking.
- The allocator and renderer remain untrusted; stale graph or machine facts
  are still rejected by ordinary elaboration/kernel checking.

## What it assumes from elsewhere

- **[[function-ir-alu-core]]** supplies the mixed-operation workload.
- **[[frontend-large-proof-composition-cost]]** owns general frontend sharing;
  this issue owns generator-side proof factorization that is useful even before
  a general frontend improvement lands.
- **[[x86-block-normal-execution-proof-fuel]]** owns replacing per-instruction
  execution stages with the natural generic functional-to-relational theorem.

## Progress, 2026-09-01

The first scaling cut is implemented and changes the shape rather than raising
fuel. Internal placement theorems now take one compact context record; node
semantics advance through persistent opaque `NodesHold` suffixes; instruction
execution advances through persistent instruction suffixes and opaque stages;
and immutable input-register placements are instantiated directly at their
use state instead of being copied through every intervening instruction.

Measured alone with item timing enabled, debug build:

- the original 20-node/22-instruction module exceeded 300 seconds;
- the staged 5-node module takes 25.3 seconds;
- 20 nodes take 64.5 seconds; and
- 50 nodes take 154.1 seconds.

The 20-to-50 ratio is 2.39× for 2.5× as many nodes. Late node facts remain
flat (roughly 1.5--1.75 seconds each), so the former superlinear projection and
frame-propagation shapes are gone. At 20 nodes, machine framing fell from 80
generated facts/18.4 seconds to 2 facts/0.46 seconds, while value-placement
facts fell from 102/49.9 seconds to 22/30.2 seconds. Execution staging remains
about 1 second per selected instruction and value placement about 1.5 seconds
per node; these linear constants keep this issue open for the 100-node rail.

The ordinary five-node acceptance remains fast enough for the default suite;
the 20-node case is an explicit ignored stress test. Set
`HEATHER_TIMINGS=<file|->` for per-declaration attribution (the switch was
`HEATHER_FUNCTION_IR_X86_TIMINGS` before [[perf-instrumentation-consolidation]];
`docs/instrumentation-design.md` has the schema) and
`HEATHER_FUNCTION_IR_X86_NODES=N` to probe another size.

As an integration-level result, the complete serial `function_ir_x86` test
binary fell from 163.7 seconds before this cut to 106.2 seconds after it, while
adding the larger mixed-operation machinery and retaining stale-model and
alternate-schedule controls.

## Follow-up, 2026-09-02

The full-suite audit after compact-Nat compatibility repairs found one stale
emission assertion: the structured Heather emitter formats a theorem's
proposition on the line after `byte_length():`, while the test still searched
for the legacy one-line spelling. The emitted theorem still states and checks
that the constant/Add block is 13 bytes; the assertion now pins the structured
format, and its focused test passes.

The same full run also shows this target has again outgrown its process rail as
a *collection*: libtest runs two heavy cases inside the binary, and the process
was killed at 152.85 seconds wall by the cumulative 300-CPU-second/4-GiB
envelope before printing a result line. The focused repaired case passes in
22.28 seconds, and all earlier completed FunctionIR targets were green. Do not
hide this by raising the rail: either continue reducing the execution/
placement constants owned here or shard the now-independent test groups as
`issues/integration-test-prefix-reelaboration.md` did for Omega.

The suite is now split into model, checked lowering, source, binary-ALU, and
control-flow test processes, with the explicitly ignored large-DAG probes in a
sixth scaling target. The old `function_ir_x86.rs` is shared fixture code and
deliberately contains no tests of its own. This keeps one canonical
workload/emitter while giving each independent semantic group its own unchanged
process rail; the content-addressed semantic module store prevents the split
from multiplying the expensive checked-library prefix.

The next plain `scripts/test` validates the process boundary under actual
parallel suite load: model 85.4 s, checked lowering 27.1 s, source 79.8 s,
binary ALU 160.5 s, and control flow 213.5 s, all inside their unchanged
individual rails. The former aggregate target now contains no tests and exits
immediately. The run reached 2,289 passes and zero failures; it was formally
incomplete only because the separately owned `omega_div_mod` target was
SIGKILLed near its existing single-workload rail. The accumulated FunctionIR
x86 process failure described above is therefore resolved; the issue remains
open for its original 100-node proof-constant acceptance target.

The 2026-09-02 block-argument round gives a useful noisy-host distinction.
Under a five-child full run, control flow was SIGKILLed at 319.17s at almost
the exact moment `omega_div_mod` was also killed; the runner correctly marked
the 2,291-pass run incomplete.  Re-running control flow alone under unchanged
rails passed in 152.42s.  No semantic/proof failure is present, but full-suite
co-scheduling is now tracked separately by
[[parallel-test-memory-headroom-under-heavy-prefixes]].

## Full control certificate, 2026-09-03

The first complete block-argument diamond provides a realistic 165-boundary-
declaration workload. After factoring machine computation, dependent join
selection, scalar arithmetic, and final composition, the honest generated
module checks under default fuel in 94.9s on a quiet debug run (50.7s kernel,
44.2s frontend). The final linked/result theorems are no longer dominant.

The largest items are now the linked conditional true-target/RIP theorem
(7.2s), taken-target theorem (6.7s), conditional decode (4.0s), and layout
(3.3s), followed by four protected-register facts around 2.7--3.1s each.
This issue should therefore target reusable decode/layout endpoint sharing and
protected-register framing before further hand-factoring of the final
FunctionIR theorem. Per-item timing is enabled for the focused control-region
fixture when diagnosing this path.

## Log

- 2026-09-04: The control-flow shard split three ways (2026-09-04): it was dying at the 300 CPU-second rail in the parallel full lane (231 s alone, ~1.9x under three-way contention) and had done so since the shard split, so every full run read INCOMPLETE. Measured alone: control region 84 s, comparison-prefixed conditional 63 s, structured conditional 29 s, unsigned/signed comparisons 25 s + 20 s. Now function_ir_x86_control_flow (the control region), function_ir_x86_conditionals (structured + comparison-prefixed), function_ir_x86_comparisons (unsigned + signed); each stays under ~100 s alone.
- 2026-09-06: Kernel round (2026-09-06, this machine, dev profile, noisy): the per-node constants were kernel pathologies, not proposition shape. Attribution: 89% kernel; a frame-pointer profile put the time in deep ty_nf/ty_w walks and 48 M type-closure allocations. Four kernel levers landed: (1) typed neutral application — no stored Π annotation comparison (was: every App node of a 15-ary spine re-compared the remaining Π, recursing into each neutral domain); (2) typed fst/snd — no stored Σ comparison (was: each snd of a Wf record's children chain re-compared the remaining tuple type, 2,200 nodes per refl); (3) neutral-first at Σ (η on two neutral 64-bit vectors was O(64²)); (4) Level::join at inference (`Ty (0 ⊔ 0)` vs `Ty 0` defeated the == shortcut 55 K times per module) plus a pointer hasher for the value caches. Wall: 5 nodes 16.3 s -> 8.5 s; 20 nodes 30.9 s; 50 nodes 66.9 s (furnace before: 40.8 s / 101.9 s on a ~15% slower box). Per-item: value placement ~1.4 s -> ~0.35 s at 5 nodes; machine-result 0.85 s -> 0.18 s. What remains: ~4.6 s of the 5-node kernel time is the elaborator spelling one inductive shape three ways ([[inductive-spelling-codes-nonrecursive]]); ~30% of module kernel time is malloc/free in per-query arenas ([[value-domain-allocation-constant]]); and the FRONTEND grows superlinearly (1.5 s / 6.1 s / 20.3 s at 5/20/50 nodes, boundary items 11.8 s at 50) — [[frontend-large-proof-composition-cost]] is the next wall for the 100-node rail, not the kernel.
- 2026-09-06: Five-node module kernel time 8.45 s → 2.86 s (module wall 10.2 s → 3.8 s, furnace dev profile) from [[inductive-spelling-codes-nonrecursive]]'s round: flat declarations' spines named, monomorphized Wf copies spelled consistently. What remains of the typing-seam misses (~1.3 s) is [[unnameable-annotation-occurrences]]'s family; the rest of the kernel time is not conversion misses at all ([[value-domain-allocation-constant]] next).
- 2026-09-11: 2026-09-11, first reading with heather build-x86 --timings (release, furnace, reused_callee --callee leaf, the native_summary workload): wall 128 s, RSS 0.98 GB, certificate source 1.0 MB, 3474 item rows in caller_native_certificate summing to 118 s = kernel_gate 86 s + elaborator 'other' 32 s (no named timer claims it; resolve 0.2 s); the 28 library modules replay in ~8 s. Zero OutOfFuel and zero NotConvertible: every conversion succeeds, and the kernel time tracks evaluator steps at roughly 1.7 M steps/s — ~150 M eval steps over the top 30 families. Largest families (n, total, kernel, eval steps): store_equal 54 / 11.3 s / 9.0 s / 24.5 M; byte 36 / 10.2 / 8.7 / 12.7 M (34.5 k conv misses); read_literal 32 / 8.8 / 6.2 / 5.4 M; return_read 32 / 7.7 / 7.0 / 15.2 M; step 19 / 5.3 / 3.4; write_permission 48 / 5.0 / 4.8 / 12.6 M; successor 35 / 4.4. No single item is above 1 s; the cost is ~3.5 k generated theorems at ~34 ms each, so the levers are fewer/cheaper generated items per family (generator side) and evaluator step counts per item (kernel side), not any one conversion.
- 2026-09-12: 2026-09-12 shard attribution (furnace, dev profile, alone, exact warm images): the seven binaries were 6–19 s solo, so the ~52 s the parallel full lane reports is ~3x contention, not their work. Two findings. (1) Every generated-certificate test built its elaborator with base.clone(), and a cloned KernelPool resets to width 1 by design (pool.rs), so these shards never used the eight-worker gate: user ≈ wall, kernel_gate 11.7 s of conditionals' 18.5 s. Switched the 15 sites to base.fork(): conditionals 18.8 → 10.8 s, control_flow 17.7 → 9.9 s, CPU flat. (2) The 18-module prefix replay is 5.4 s per binary, serial ([[semantic-replay-phase-attribution]] log), and five of seven suffixes had fallen under 3.5 s (alu 2.5, source 3.3, comparisons 0.8, lowering 0.1, model 0.3), so the 2026-09-04 seven-way split was paying ~27 s of replay to separate work that no longer needs separating: lowering/source/alu/comparisons are one binary again (function_ir_x86_dataflow); conditionals, control_flow and model (different prefix length) stay. Remaining tail, both conditional modules: linked_taken_at 2.6 s, true_reaches_join 2.2 s, layout 1.6 s, decodes 1.6 s, all kernel; with the gate wide, taken_at is the critical path.
- 2026-09-12: 2026-09-12 certificate-wide attribution after the last three rounds (release, furnace, W=1, reused_callee --callee leaf): certificate module 51.6 s wall, kernel_gate 41.8 s (was 86 s on 2026-09-11), 236,914 conversion misses, 6.64 M shortcut hits, 36.4 M evaluator steps; the conv-miss sidecar (--timings writes <stem>.conv-miss.txt) sums the misses to 32.6 s, i.e. 78% of the kernel is the typing seam. Two buckets: Id/Id 2,629 misses / 15.7 s (refl at Pair sites — genuine evaluation, dominated by memory reads through the call_memory_write λ-chain, one 64-bit bxor+is_zero_bits per link: read_literal_28_* 0.47 s each because the contract route compares state_28.memory with state_18.memory, 188 k steps vs 15 k for a refl read at state_17), and Sigma/El(?) 14,740 misses / 9.7 s (projections Fst/Snd out of an application whose type is El(app(code, arg)) — a parameterized record instantiation, MachineState<CallMemory> — against an inline Σ annotation; the residue [[elaborator-canonical-type-spelling]] owns). The remaining ~20 buckets are under 2.2 s each; El^δ/Sigma 41 k misses / 2.1 s and El^δ/Sum 119 k / 0.3 s are the numerous-but-cheap ones. conv_memo_hits is 0 across the whole certificate: the memo's anchors are Rc pointers and the repeats are re-spelled per site (e.g. byte_34_0: 2,165 misses / 147 ms of its 260 ms, the same closed pairs at different weakening depths).
- 2026-09-12: 2026-09-12 probe (release, warm library, one theorem each, --timings): a closed width-64 compare is_zero_bits(64, bxor(64, a, b)) = 16.8 k evaluator steps / 38 ms when equal and 7.3 k / 14 ms when the low bit differs; bitvec::add(64, a, b) on literals 30.1 k / 54 ms; the stack_page test (52-bit) 14.6 k / 35 ms. That is ~250 steps per bit per operation at ~2.3 µs per step, and it is the unit the Id/Id bucket is made of: a memory read through W stack-write links costs W such compares, and the contract route at step 28 compares two memories with all their links. Levers, unranked: (K1) a native closed-bitvector value in the evaluator with an adequacy argument, the runs precedent ([[kernel-acceleration-policy]]); (K2) fewer compares per read — a word-granular exclusion lemma so a read skips an 8-byte write in one compare instead of eight; (K3) the step constant itself ([[value-cache-memo-in-arena]], [[kernel-arena-terms-frozen-prefix]]).
- 2026-09-12: K1 from the 2026-09-12 probe is now its own issue, [[kernel-native-bitvector-values]]; K2 (word-granular exclusion, a contract route that does not compare two memories) stays here as generator/library work.
- 2026-09-12: Round chartered (user, 2026-09-12): K2 — fewer, cheaper compares per stack read/store, generator and library only, no kernel change; K1 ([[kernel-native-bitvector-values]]) queued behind [[kernel-arena-terms-frozen-prefix]] so a new Val variant lands on the representation it will live on. Chartered mechanisms: the contract read route stated over stack_observation with the read closed by the certified store instead of two call_memory_read evaluations (read_literal_28_* 188 k steps each); a word-granular exclusion lemma replacing 64 compares per WordOutside; the store_equal spelling (24.5 M steps / 54 items). Bar: whole-certificate kernel_gate and item total at or below 41.8 s / 51.6 s on the same box, every family row recorded; design doc docs/call-memory-read-spelling-design.md first, then implementation.
- 2026-09-12: K2 design pass (docs/call-memory-read-spelling-design.md): fresh before column on a new box, release W=1: item total 49.06 s, kernel_gate 39.10 s, 36.4 M steps. The brief's family table was the 2026-09-11 one and misranked two of three mechanisms (store_equal is 4.86 M steps not 24.5 M; write_permission 0.64 s not 5.0 s). Finding: read_literal_28_* (0.51 s each, 8 items, 4.1 s) are six unary walks of the 399-byte file list each, because static_elf64_read's 64 KiB window admits the stack page and nth runs off the end for its None ([[call-memory-read-file-walk]]); the write-chain compares are a twentieth of one lookup. Probe: contract over call_memory_read 362 ms / 115 k steps vs over stack_observation 19 ms / 11 k. Mechanism 1 (contract over stack_observation + file-constancy conjunct + open lemma memory_writes_of_stack_writes) projected −3.8 s item / −9.7% kernel. Refuted: word-granular exclusion (the whole WordOutside output is <0.9 s; 0.7 ms per closed compare since addresses differ in low bits) and the store_equal spelling (its largest item is 50 ms Sigma/El(?) residue vs 2 ms Id/Id — [[elaborator-canonical-type-spelling]]'s). byte_page/byte_wrap (4.1 s kernel, 298 closed 48/64-bit compares by refl) are [[kernel-native-bitvector-values]]'s shape.
- 2026-09-12: K2 landed (docs/call-memory-read-spelling-design.md §9): the leaf callee contract is stated over stack_observation with an after.memory.file = before.memory.file conjunct, and memory_writes_of_stack_writes (lib/elf64_calls.hthr, open) recovers the call_memory_read-level footprint so the interface is unchanged. Paired job, release W=1, one instance: item total 51.999 → 47.631 s (−8.4%), kernel_gate 42.709 → 38.490 s (−9.9%), read_literal_28_* 0.53 → 0.055–0.061 s each (188 k → 63 k steps); every other family within 0.03 s; two new callee_preserved_file items at 0.03 s. Full scripts/test 2581 passed twice by the implementer and once by the coordinator. Not met: the bar's 0.05 s per read — 22 ms of the residue is Sigma/El(?) projection off callee_post ([[elaborator-canonical-type-spelling]]), 13.6 ms the write-chain refl. dead_frame_byte's file walk stays ([[call-memory-read-file-walk]]). Largest remaining rows: byte 4.8 s (fetch route, Vec/Wf spelling), store_equal 3.6 s and successor 2.5 s (Sigma residue), byte_page + byte_wrap 4.4 s ([[kernel-native-bitvector-values]]'s shape).
