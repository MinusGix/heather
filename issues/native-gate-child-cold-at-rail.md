---
title: The library gate's lib/native child is at the 300 CPU-s rail again from a cold store
status: closed
labels: [testing,performance,native,images]
area: infrastructure
created: 2026-10-29
updated: 2026-10-29
---

[[library-gate-native-cold-rail]] (closed 2026-10-27) brought the gate's
`lib/native` child under the rail by making module images DAGs. On master
709e71c, a cold run of the gate's own command for that folder (`heather
check --cache --expectations --world lib lib/native`, kernel width one, the
dev binary, a 4-CPU cloud box, run after the `lib/std/*` folders had built
the shared prefix) took 299 s user plus 3 s system. That is just over the
suite's `ulimit -t 300`, which counts both. The run was made with a looser
rail, so it finished; under the suite's it would have been killed.

Where it goes (cold module totals, `perf/bench/targets.md` T4): the
`native_compile_*` modules and `function_ir_lower_calls`, mostly kernel.
The two heaviest declarations reproduce alone ([[native-lemma-kernel-steps]]).
Several others are cheap alone and costly cold, because the cold gate charges
the module's shared generated items to their first user
(`docs/infrastructure/cloud-benchmarks.md` §3).

The order here was not quite the gate's: the gate sorts folders by the
world's order, and this run built the prefix in `lib/std/arch`'s child. The
`lib/native` child's own modules are most of its time either way.

## Done when

A cold gate on a fresh cloud box (the sentinel's configuration) leaves the
`lib/native` child with a margin under the rail, read off the sentinel's
per-target times or a by-hand cold folder run like the one above.

## Log

- 2026-10-29: Measured around the spelling fix of [[native-lemma-kernel-steps]] (cloud box, branch claude/project-thread-n0z5jm, master e208de4). The tree has grown since 709e71c (`native_compile_structured` and others), so the child was re-measured on both binaries at this commit: dev binaries, kernel width one, 6 GiB address-space limit, `lib/std`, `lib/lang` and `lib/kernel_model` built first into a fresh store, then `check --cache --expectations --world lib lib/native` timed by rusage.

    | binary | CPU-s (user + sys) | kernel steps | kernel gate s |
    |---|---|---|---|
    | master e208de4 | 506.9 | 78.8M | 335 |
    | with the fix | 304.2 alone (294.9 in a run beside other work) | 16.1M | 123 |

    So master was far over the rail at this commit, not just over it, and the fix takes about 200 CPU-s out of the child; nearly every `Target::*` lemma lost 85 to 98% of its steps, not only the two named ones. It still sits at the rail. What leads the child now is not the kernel's arithmetic: `Stmt::emit_extends` (9 s, half elaborator whnf), the `native_build_parts` `Act::packs_*_of` family (4 to 7 s each, which a re-run with `--only` over the warm store does not reproduce, likely shared generated items gated at their first user; not confirmed), and the `native_compile_structured` lemmas (1 to 1.5 s of projection substitution each). Leaving this open for a next round on those.
- 2026-10-29: Under the rail with a margin on master e23e767 (#264 and #265 in), same method as the entry above (dev binary, width one, 6 GiB, fresh store over the built prefix): **274 CPU-s** (272.1 user + 1.9 sys), kernel steps 16.1M, gate 107 s. The warm-world change in #264 took about 30 CPU-s off the cold child as well. Closing on that: the margin is about 9%.

    What leads now, for whoever widens it (stack samples of a cold run, a value-metrics run with the miss trace on `Act::packs_seq_of`, and `HEATHER_IMAGE_ATTRIBUTION`):

    - `native_build_parts` (46 s, 27 s of gate on only 1.6M steps). Its `Act::packs_*_of` lemmas match on `Act`, a tier-2 inductive (`Seq(parts: Bool → Act)`), with 14 constructors. About 3.5 s of `packs_seq_of`'s 5 s gate is 290 conversion misses, two thirds of them `El(?)/Id`: the leaf equation of a leaf constructor's value, `refl(f₀)` checked against `El(Act#canon(sup(ℓ; f₀)))`, about 31 ms each. Samples show the rest in conversion-arena teardown and in the verdict store hashing the terms (`admits` → `merkle`).
    - Tried and not kept: spelling a tier-2 shape's payload field types by name (`El(Val#tycode)` for the 17 `Val` fields of `Act`'s `W₀`, a respell of each payload `Σ` chain in `lower_instance_w`). Cold child 274 → 266 CPU-s, steps −5%, but conversion queries +25% and the `Act::*` items' gate up to twice as slow (`traced`, `shape`, `part`), with the misses unchanged. It is not what the misses cost, and within the run's noise overall.
    - Next in line: `Stmt::emit_extends` (9 s, half elaborator whnf), `emit_runs`, the `native_compile_structured` lemmas (1 to 1.5 s of projection substitution each).
