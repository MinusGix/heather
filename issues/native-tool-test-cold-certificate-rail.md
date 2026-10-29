---
title: Keep cat's native test under the CPU rail when its certificate is not cached
status: open
labels: [native,tests,perf]
area: heather-in-heather
milestone: [hih-tools]
created: 2026-10-28
updated: 2026-10-29
---

`compiled_cat_files_runs_as_gnu_cat` (`crates/cli/tests/native_tools.rs`)
dies at the suite's 300 CPU-s rail on a cloud box the first time it runs
after any library change, and passes on the next run. It died with only
"checking `cat_files_tool`'s compile and its 21896 bytes" printed, so the
kernel's check of the certificate was what was running.

Why, measured on 2026-10-28 with the test-profile binary
(`--timings`, after #251 and #255): write-elf's own reads (the parts, the
byte reads, the probe) cost about the same either way, roughly half the
rail. The check of `cat_files_tool_elf_certificate` costs more than the
rest of the run together, and runs only when the verdict store does not hold
it. A library edit changes the certificate's imports, so the next run checks
it cold. Warm, the whole write-elf run is about half the rail. On the
pre-#251 sources the cold certificate cost more again, though that run also
elaborated the library cold beside it, so it shows only that this is not a
regression from #251 or #255. The certificate check, by kind
of statement, is mostly the per-statement `{p}_at_` and `{p}_checked_`
parts.

## Scope

- Find what the `{p}_at_` and `{p}_checked_` statements spend: there are
  hundreds of each. Either a shared lemma is re-proved per statement, or
  each re-derives something the parts could state once.
- Or, if that is the price, raise this test's rail deliberately (as the
  Linux tests did, PR #133), saying why in `scripts/test`.

## Done when

A cold run of the test (a fresh verdict store) passes under the suite's
rails on a cloud box.

## Log

- 2026-10-29: Cold cost attributed and cut (2026-10-29, branch claude/project-thread-xnpxz6). Cloud box, test-profile binary, width one, `write-elf … cat_files_tool --world lib` over a store the cold gate had just written (so the library replays and the certificate checks cold):

  - `{p}_checked_#` was not kernel time: it was `carries_data` (`crates/elab/src/sealing.rs`) running each statement's `checked(…).IsTrue()` to its whole fuel to learn that `True`/`False` carry no data. A family no instance of which carries data is now settled at fresh variables without running its argument (`docs/theorem-witness-unfolding-design.md` §2). The family left the top of the table.
  - `{p}_at_#` was half `instance_match`: fixed under [[constructor-literal-respell-cost]]. The `bytes_#_#` reads shrank with it.

  Whole run about 30% fewer CPU-s than before, and now well under the 300 CPU-s rail on its own (it was just over). What is left, largest first: `piece_#_is` (kernel, flat), `bytes_#_#` (the fork's reads), `at_#` (kernel, now most of it), the two `read_#_entry` reads. Leaving this open until a cold `scripts/test` run of the test itself passes in CI-like conditions; the measurement here is the write-elf run the test makes, not the test.
- 2026-10-29: Cloud cold numbers for every tool and the certificate's families by kind are in `perf/bench/targets.md` (T2, T3; [[cloud-benchmarks]]). `piece_#_is` and `at_#` cost the same per item in `yes_tool`'s certificate as in `cat_files_tool`'s, so `scripts/bench-probes --filter cert/` measures them over a frozen copy of yes's certificate in about a second each. A warm write-elf's floor (no kernel work) is filed as [[native-process-fixed-cost]].
- 2026-10-29: What a piece and a label spend, per instruction (cloud box, `scripts/bench-probes --filter cert/` and `--only` probes over the same instructions in a scratch module; branch claude/project-thread-n0z5jm). Baselines: `cert/yes-pieces` 607,244 steps over its 7 items, `cert/yes-labels` 377,026 over 14.

    - `piece_#_is` is the bytes of each instruction built bit by bit. `piece_0_is` is 78 K steps. One `canonical_bytes(MovRI(Rax, ofNat(60)))` against its literal bytes is 9,821 steps; a `MovRR` is 1,456; the two REX/opcode header bytes alone are 1,541; an `add_nat` address is about 8.5 K. Comparing two byte literals costs about 61 steps per byte pair, so the floor is building each `BitVec(8)` as a `[Bool; 8]` and reading it back, at every byte (`ofNat` is about 25 to 45 steps per bit whatever the value). Restating `mov_ri_bytes` with its shared tail in a `let` saved about 3%, so a library respelling of the encoder does not reach it: the lever is the closed-bitvector line ([[kernel-native-bitvector-values]], [[bitvector-literal-entry-cost]]: `ofNat` and byte literals still enter structurally).
    - `at_#` is not the label arithmetic either. In `at_8` (17.5 K steps) most of the steps evaluate the `Gpr` balanced-sum layout's generated definitions (`sum_layout.rs`), each about 114 times: every register in a `Prog` literal is re-decoded from its sum injections per use. A register literal that stays decoded, or a per-query value for a closed generated definition, is the lever there; not attempted in this round.

    Neither was cut here: the round spent itself on T4 ([[native-lemma-kernel-steps]], closed), and both levers are kernel or representation work.
