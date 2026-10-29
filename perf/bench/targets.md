# Probe targets, ranked (cloud, 2026-10-29)

Where checking time goes, found without running the suite, and what to
hillclimb on first. Native first, as asked. The numbers are a dated diary
entry (`perf/README.md`'s rule: numbers live under `perf/` and in issue logs,
not in docs). The convention is `docs/cloud-benchmarks.md`. Each target names
its probe cases (`perf/bench/cases.tsv`, recorded in `results.tsv`) and the
issue that owns the work.

**Environment.** A 4-vCPU, 16 GiB Claude Code cloud container, master
709e71c, the dev-profile `heather` the suite runs (hot crates at opt-level
3), kernel width one, the suite's memory rail. Nothing else ran beside a
measurement, except where noted.

**How it was measured.**

1. **The cold library gate, by hand.** The gate's own command (`heather
   check --cache --expectations --world lib <folder>`), one process per
   folder, three at a time, into an empty store, each with `--timings`.
   That is about 1180 CPU-s in all. By folder: `lib/std/arch` 401 (it built
   most of the shared prefix), `lib/native` 302, `lib/_tests/std/tactic`
   135, `lib/std/os` 72, `lib/_tests/std/num` 62, `lib/std/num` 47,
   `lib/std/algebra` 41, `lib/_tests/native` 33.
2. **Every native tool's `write-elf`, cold certificate.** Each tool was
   written over a fresh copy of that store, so the library replays and the
   certificate is kernel-checked from scratch, as the native gates do on a
   fresh box.
3. **`--only` on the heaviest items**, to see which reproduce alone.
4. **A second `write-elf` of `yes_tool` over the same store**, for the warm
   floor.

Module and item totals below are self time from the `--timings` rows.
"Kernel" is the gate, "merkle" is the cache's interface and check-key walks,
and "image" is decode, recheck, relocation and publication.

## The suite-level picture

The native certificate gates were about 1640 of 3649 target CPU-s on the
2026-10-29 `--pr` run (`issues/pr-lane-cost-2026-10-29.md`): `native_tools`
1078, `native_cat` 370, `native_branches` 195. `--pr` now skips them unless
native paths change, and the sentinel runs them nightly. Each of their tests
is one or more `write-elf` processes, and each process costs the following
(CPU-s, cold certificate):

| tool | total | kernel (certificate) | merkle | image | rest (write-elf's reads, elaboration) |
|---|---|---|---|---|---|
| `yes_tool` | 36 | 3 (3) | 14 | 12 | 7 |
| `cat_source` (native_cat) | 36 | 4 (4) | 12 | 12 | 7 |
| `wc_l_tool` | 38 | 4 (3) | 14 | 12 | 9 |
| `head_c10_tool` | 39 | 4 (3) | 14 | 13 | 8 |
| `tr_upper_tool` | 42 | 5 (5) | 14 | 12 | 11 |
| `echo_tool` | 47 | 7 (7) | 14 | 12 | 14 |
| `yes_args_tool` | 50 | 9 (8) | 14 | 12 | 15 |
| `head_n_tool` | 104 | 31 (30) | 14 | 13 | 47 |
| `decimal_echo_tool` | 111 | 34 (30) | 14 | 14 | 49 |
| `wc_counts_tool` | 117 | 34 (33) | 14 | 13 | 56 |
| `cat_files_tool` | 222 | 76 (75) | 15 | 16 | 115 |

Two costs, in about equal measure over the suite: a fixed floor of about 30
CPU-s per process (merkle plus image plus the module that misses, T1), and a
certificate that grows with the code (T2, T3).

## T1. The fixed floor of every native process (owner: `issues/native-process-fixed-cost.md`)

- A **fully warm** `write-elf yes_tool` took 18 CPU-s, all verdicts stored and
  zero kernel work. Of that, the merkle walk was 8.3 s: the replayed
  certificate module 2.8, the probe module's one-line first declaration
  `yes_tool_elf_a_0` 2.6, and `native_build_parts` 1.2. `image_recheck` was
  6.0 s, mostly the `native_compile_*` modules at hundreds of thousands of
  evaluator steps each, even with every verdict present. Decode was 1.6 s.
- The **first `write-elf` after the gate misses** `native_build_parts` and
  `native_tools` (relocation 4 s, merkle 4 s, plus their elaboration), and
  later runs hit. So the cold runs above carry about 10 s that the warm run
  does not.
- A warm `heather check` of a root that only imports `native_tools` costs
  9.5 CPU-s: image 6.7 (recheck), merkle 1.5, elaboration 1.3. That is the
  floor without `write-elf`.

**Update 2026-10-29:** the recheck (theorem statements with no verdict) and
the merkle walk's re-hash of the world at each fork switch are fixed; the
warm floor is about 8 CPU-s and the world replay about 5
(`issues/native-process-fixed-cost.md`, log). The first-run miss is fixed
too: `write-elf` after the gate replays every library module (first run
after a `lib/native` gate 49 to 31 CPU-s).

Leverage: about 11 `write-elf` processes in `native_tools` alone, plus
`native_cat`'s, at 18 to 30 s each before any tool-specific work
(`native_branches` runs `compile-x86`, not measured here). Cases: `native/world-replay`, `native/elf-floor-yes`,
`native/elf-cold-yes` (heavy).

## T2. The certificate's kernel families (owner: `issues/native-tool-test-cold-certificate-rail.md`)

`cat_files_tool` (the largest), by family:

| family | items | kernel s | evaluator steps | what it is |
|---|---|---|---|---|
| `piece_#_is` | 195 | 35.1 | 20.3M | `asm_code_after(…) = piece` by `refl`: the assembler run by the kernel, about 100K steps per piece, flat in the program's size |
| `at_#` | 335 | 18.6 | 7.4M | the label prefixes, gated as `Prog` literals (plus 5.7 s of `instance_match` in elaboration) |
| `e_#` | 104 | 6.2 | 4.9M | entry statements |
| `ib_#_#_is` | 22 | 5.4 | 3.3M | initial bytes |
| `piece_#` | 195 | 3.5 | 0.9M | the piece literals themselves (elab whnf 4.4) |

The per-item cost is the same in `yes_tool`'s certificate as in
`cat_files_tool`'s (a piece costs about 0.1 s in both), so the small
certificate is a faithful unit. Cases: `cert/yes-pieces` and
`cert/yes-labels`, over a frozen copy of `yes_tool`'s certificate. Levers:
fewer steps per assembled instruction (what `asm_code_after` evaluates), or
kernel per-step cost (about 1.2 µs per step here).

## T3. `write-elf`'s own reads (owner: `issues/native-tool-test-cold-certificate-rail.md`)

Not the kernel. In `cat_files_tool`, `bytes_#_#` (158 reads) took 37 s and
`read_#_entry` (2) took 19 s, as evaluation in the elaborator's fork (18.7M
and 6.3M steps). `read_#_part` took 5 s. This is most of the "rest" column
for the large tools. Case: `native/elf-cold-head-n` (heavy) carries it at
mid size.

## T4. lib/native's cold gate child (owners: `issues/native-gate-child-cold-at-rail.md`, `issues/native-lemma-kernel-steps.md`)

At 302 CPU-s (299 user plus 3 system), the child is over the suite's 300 s
rail on a cold store. Cold module totals (s): `native_compile_args` 62.5
(kernel 52), `native_compile_bytes` 46 (kernel 40), `function_ir_lower_calls`
28.8 (kernel 17), `native_build_parts` 22 (image 8), `native_compile_correct`
20.5, `native_compile_calls` 20, `native_compile_opens` 15.7,
`native_compile_region` 12.7.

Alone with `--only` (the marginal cost), two items reproduce their cold cost:

| item | kernel s | steps | queries | note |
|---|---|---|---|---|
| `native_compile_args::Target::goes_arg_found` | 9.2 | 5.2M | 53K | the same steps cold, within about 1% |
| `function_ir_lower_calls::call_step` | 7.8 | 4.6M | 43K | one gated term |

Others do not reproduce: `Target::arg_cells_store` is 11.0 s of kernel cold
but 0.27 s alone; `goes_args` is 6.9 cold and 0.16 alone; `goes_byte_init`
is 9.1 cold and 0.18 alone. Their cold rows carry the module's shared
generated items, gated where they were first used (12 gated terms cold
against 2 alone, for `arg_cells_store`). So the module's cold cost is in
part what it generates once, which an `--only` case cannot see. A cold
module check with a fresh verdict store would show it, and is a follow-up
case. Cases: `native/goes-arg-found`, `native/call-step`,
`native/arg-cells-store`, `native/emit-extends` (elaborator-bound, 0.7 s of
whnf and substitution).

**2026-10-29, after the spelling fix** (`issues/native-lemma-kernel-steps.md`, closed):
both items were conversions between a coded declaration's inline lowering
and its `El(D#tycode)` spelling, at record projections and at lifted `omega`
slots, not proof work. Same tree, cold `lib/native` child at width one: kernel
steps fell from 78.8M to 16.1M and the kernel gate from 335 to 118 s, nearly
every `Target::*` lemma by 85 to 98% of its steps. The tree had grown past
the 302 CPU-s above (507 CPU-s on master at this commit, 304 with the fix), so the child's
margin is read off `issues/native-gate-child-cold-at-rail.md`'s log. What
leads the child now is elaboration: `Stmt::emit_extends`, the
`native_build_parts` `packs_*_of` family, `loop_head`.

## T5. The rest of the library, for breadth

| item | cost alone | where | case |
|---|---|---|---|
| `x86_64_stack_runs::Site::moves_spills` | 4.8 s | elaboration (omega reflection over stack layouts); the heaviest x86 item, 16.7 s cold | `x86/moves-spills` |
| `tactic::attempt_from` | 4.3 s | one kernel check of 287K conversion queries | `tactic/attempt-from` |
| `ordered_field::OrderedField::pos_of_mul_pos_nonneg` | 2.3 s | `projection_subst` (2.0 s): class-carrier projections; the module is 31 s cold, 21 of it `projection_subst`, and `linarith` pays 12 s the same way | `algebra/pos-of-mul-pos-nonneg` |

Not cased yet, because a `lib/_tests` module's image is keyed to its
folder's world and `--only` on the lone file finds none (a copy into a
fixture is the way):

- `interval_tactic_real_tests::inline_apart`: 22.7 s of kernel cold.
- `mono_tests::group_neg_le`: 4.2M elaborator steps for 27 ms of gate (a
  tactic run in the elaborator).
- `elementary_tests::exp_355_113` and `exp_apart`: about 3 s of kernel each.
- `native_decimal_tests::formats_*`: 0.6 to 1.4 s of kernel each, closed
  evaluation (the cheapest per-step kernel probe in the tree).

## What was not measured

The suite itself. The sentinel's per-target times (the published manifest
is still 657094c's, 2026-10-26, because publishing failed until #260). The
showcase gate. Release-profile timings.
