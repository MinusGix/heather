---
title: Attribute a native tool's write-elf now that the per-process floor is gone
status: closed
labels: [performance,native,testing]
area: heather-in-heather
created: 2026-11-11
updated: 2026-11-11
---

The native tool tests are the largest remaining suite cost after the library gate, and nobody has attributed one since the per-process floor fell. Found while writing [[performance-overview-2026-11-11]].

## Measured

2026-11-11, four-core cloud box, test-profile binary at width one:

- `crates/cli/tests/native_tools.rs`: 216 and 251 s in two exact-lane runs, 150 s in a `--pr` run, 76 s in the fast lane. `compiled_sort_runs_as_gnu_sort` 85 and 111 s, `compiled_tac_runs_as_gnu_tac` 71 and 97 s, `compiled_cat_files_runs_as_gnu_cat` 40 to 60 s, `compiled_decimals_round_trip_the_widest_words` 43 s.
- All native targets together are a quarter of the exact lane's CPU, about half of a `--pr` run's summed target time and a third of the fast lane's.
- `scripts/bench-probes --heavy`: loading the native world warm is 1.1 s (8.3 s on 2026-10-29), a warm `write-elf` of `yes_tool` 2.3 s (14.0 s), a cold one 4.8 s (43.7 s), and `head_n_tool` cold 21.3 s (127.5 s): 12.9 s of elaboration, 5.2 s of kernel, 3.2 s of image work, 1.0 s of hashing.

So the fixed floor is no longer the cost. What is left grows with the tool, and on `head_n_tool` 60% of it is the elaborator building the certificate.

## To do

Take a `--timings` table of `write-elf` for `sort_tool` and `tac_tool` cold and warm, and name the declarations and phases their time is in. Add the heavier one to `perf/bench/cases.tsv` ([[bench-probe-cases-stale-2026-11]]).

## Done when

The table exists in this issue's log and the follow-up it points at is filed.

## Log

- 2026-11-11: attributed, and the largest part fixed in the same round.

  **The table** (`sort_tool` cold, four-core cloud box, dev-profile binary at width one, `--timings` on, master 56164d3; seconds are self time of the family's rows, and a read is two rows, its definition and its evaluation):

  | family | rows | s | evaluator steps | what it is |
  |---|---|---|---|---|
  | `{p}_read::bytes_#_#` | 406 | 13.95 | 32.7 M | the fork's read of each span's bytes |
  | `{p}_parts::read_#_part` | 254 | 11.50 | 31.6 M | the fork's read of each part's emission |
  | `{p}_parts::o_#` | 520 | 10.51 | 29.0 M | the fork's read of each part's live-out set |
  | `{p}_certificate::e_#` | 260 | 10.00 | 23.5 M | the kernel's check of each part's emission (9.1 s of gate) |
  | `ck_#`, `piece_#_is`, `t_#`, `checked_#`, `at_#` | | 6.7 | | the rest of the certificate, 0.8 to 1.9 s each |
  | `live_sets`, `allocation`, `trace` | | 2.3 | | one read each over the whole program |

  The run: 67.0 s, of it 14.3 s in the kernel gate, 4.1 s image work, 1.3 s hashing and 50.4 s everything else (the reads and elaborating the certificate); 137.0 M evaluator steps. `tac_tool` has the same shape at 46.8 s and 91.4 M steps.

  **Why the reads cost 36 s.** `function_ir_source::evaluate_numbers` built a fresh value arena for every read. A part's statement, its live-out set and what is known as it starts are spelled from its parent's (`{p}_s_`, `{p}_o_`, `{p}_kn_`), so every read worked each of them out from the root of the program again: a read of one eight-leaf part was 130 to 530 thousand steps of which 50 to 230 thousand were that chain. The byte reads then evaluated every part's emission a second time, to encode it once the labels were known.

  **Fixed.**
  - The reads of a tool's parts run in sessions that share one arena (`function_ir_source::read_sharing`), in the plan's order, so a part's set and known words are a step from what was read before. One arena for the whole tool ran past the suite's 6 GiB rail (a step keeps a few hundred bytes), so a session ends after two million evaluator steps and the next starts over; the bound is counted in steps so the kernel needed no edit.
  - A whole part's read ends with its bytes, unlinked (`Prog::unlinked`, native_compile: a jump's displacement is the only thing in an item's bytes that reads the labels), and `labels::link` writes each displacement in Rust once the program is laid out. Untrusted like the reads: bytes linked wrong are a piece the kernel refuses. This is the first direction of [[native-certificate-fork-byte-reads]], which it closes.

  **Measured** with `scripts/bench-probes --heavy --filter native/elf-cold`, two samples a side in the same hour, the before side in a worktree of master, minimum of the samples (spread within 7%):

  | case | before s | after s | steps before | steps after |
  |---|---|---|---|---|
  | `native/elf-cold-sort` | 66.97 | 39.05 | 136,993,448 | 61,482,271 |
  | `native/elf-cold-tac` | 46.83 | 27.07 | 91,409,523 | 39,793,202 |
  | `native/elf-cold-head-n` | 20.14 | 17.76 | 27,943,304 | 19,843,842 |
  | `native/elf-cold-yes` | 5.88 | 5.46 | 1,381,140 | 1,104,108 |

  All four ELFs and certificates are byte-identical to master's. `sort_tool`'s peak resident memory is 1.05 GB before and after (the `trace` read sets it).

  **Tried and dropped.** Parts of at most four and two leaves instead of eight: 48 and 55 s against 44.6 on `sort_tool`, because the reads' steps do not move (a leaf costs what it costs) and every extra join costs the kernel about 35 thousand steps.

  **What is left on `sort_tool` (41.7 s with `--timings`)**: the kernel gate 13.9 s (`e_#` 8.9 s: the 127 whole parts 6.3 s and 14.8 M steps, the 133 joins 3.2 s and 8.7 M steps), the reads 9.5 s (parts 4.5, live-out sets 2.2, `live_sets` 1.2, `allocation` 0.9, `trace` 0.7), elaborating the certificate about 6 s, image work and hashing 5.2 s.

  **Follow-ups.**
  - [[native-emission-membership-scans]]: two thirds of a leaf's emission, in the read and in the kernel alike, is `absent` over lists of word ids through `Nat::differs`, `Nat::eq_dec` and `Nat::same`.
  - [[native-write-elf-join-liveness]] (open since 2026-11-02): the joins' third of `e_#`, and the live-out reads, are liveness over a sibling.
  - [[native-process-fixed-cost]]: `yes_tool` cold is 5.5 s of which 4 s is image work and hashing over 105 modules, paid by every `write-elf` process.

  `perf/bench/cases.tsv` gained `native/elf-cold-sort` and `native/elf-cold-tac`.
- 2026-11-11: the certificate's elaboration, attributed (the "about 6 s" above). A fresh-named copy of `sort_tool`'s certificate checked over a store that holds its verdicts, release binary: 8.2 s against 2.2 s for the replay of the same file, so 6 s is elaborating, hashing and publishing 3,315 declarations with no kernel work. By phase (`--timings`): the elaborator's own evaluation 1.3 s (3.75 M steps; `checked_#` and `ck_#` most of it), bodies 1.0 s, forming the gate's keys 0.9 s, declared types 0.6 s, instance matching 0.5 s (`at_#` and `f_#`), the interface walk 0.4 s, name resolution 0.3 s, and about 1.2 s outside any declaration. By family: `e_#` 1.2 s, `ck_#` 0.6, `checked_#` 0.5, `t_#` 0.5, `at_#` 0.5, `a_#` 0.3 (all of it the interface walk). Nothing in it is a quarter of the whole, so there is no one fix; the candidates are the 0.5 s of instance matching on declarations a generator wrote (it could name the instance) and the `checked_#` evaluations.
