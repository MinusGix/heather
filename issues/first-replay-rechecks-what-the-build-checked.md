---
title: The first replay after a build re-checked statements and mints the build had checked
status: closed
labels: [cache,performance,elab]
area: infrastructure
created: 2026-11-11
updated: 2026-11-11
---

The first `heather check --cache` after a build replays every module from the image the build just wrote, and asks the verdict store about each stored binding. The build's own gate had checked all of them a moment before. The store answered for most and not for two kinds, which the replay then checked again with the kernel.

Found in a callgrind profile of the first replay of `docs/showcase/calc_parser.hthr` (the second run over a fresh cache directory), where the kernel was 577 M of the 1,783 M instructions that are not the profiler's SHA-256, in a run that is supposed to check nothing.

## The two kinds

**Theorem statements, 836 of them.** A theorem is stored without its proof, so its replay asks `KernelGate::admits_statement` about the statement alone, under `merkle::statement_key`. The build asked `admits` about the theorem, checked statement and proof, and recorded one verdict under the check key. Nothing wrote the statement key until a replay had checked the statement itself. So the first replay re-checked every statement, recorded it, and the second replay was the first one to find them.

**Minted derivations, 147 of them.** The resolver commits a closed class derivation as a global of its own between declarations (`#openN`, `#derivedN`; `resolve.rs`, `mint_open` and `mint_one`). Those two sites called `typing::check_term` directly and never spoke to the gate's oracle, so no verdict about a mint was ever kept by a build. `gate.rs`'s module docs said the gate had "exactly three sites"; these were a fourth and fifth outside it. At replay a mint is a bodied binding like any other and asked `admits`, which missed.

A probe ruled out the other explanation (that the build and the replay hash the bindings differently): over the cold run's 5,009 `sync`s the interface hash a question left pending always equalled the hash of what landed.

## The fix

- `Elaborator::mint_passes` (`resolve.rs`): a mint is a `GateItem` in the empty context and goes through `admits` / the kernel pair / `accepted` or `abandon`, as a generated definition does. The kernel is asked what it was asked before (the statement, then the body against it).
- `Cache::accepted` (`crates/cache/src/lib.rs`): the verdict about a theorem that lands in Ψ with an empty context and nothing withheld is also written under its statement key. The gate checked that statement as the first half of the verdict, and the key is one hash of the interface hash already in hand. A check that opened a sealed proof keeps neither verdict, as before.
- `Cache::abandon` forgets the pending interface hash of the question it abandons. Before, a refused question left its hash waiting for whatever landed next at that index; mints are the first askers whose refusal is routine (a derivation that reached into a scope is refused and simply not shared), so this had to hold. `an_abandoned_question_does_not_describe_what_lands_in_its_place` pins it.

## Result

`heather check --cache docs/showcase/calc_parser.hthr`, cloud box:

| | before | after |
|---|---|---|
| cold run, kernel-checked + accepted | 4,078 + 513 | 4,225 + 514 (the mints are counted now) |
| first replay | 983 questions go to the kernel | "0 declarations kernel-checked, 3637 accepted from cache" |
| first replay, callgrind, without the profiler's SHA | 1,783 M | 1,278 M |
| of that, kernel | 577 M | 132 M |

`scripts/perf ab --mode warm` (a seed run, then the measured first replay), width one, seven interleaved samples, against the import-lines change (`issues/import-lines-read-by-whole-parses.md`):

- counters: `check_terms` 168 to 21, `conv_misses` 4,419 to 26, `eval_steps` 40,528 to 231. What is left is the built-in prelude, which every process checks: the steady state (the third run) has the same 21, 26 and 231.
- wall 0.47 / 0.49 / 0.47 / 0.45 / 0.48 / 0.45 / 0.52 s to 0.34 / 0.33 / 0.37 / 0.43 / 0.34 / 0.40 / 0.45 s: median −20.7%, one after-sample inside the before set, so no verdict on wall. The run's `total` column is −21.6% with the sets apart.
- `--mode edit`: median −9.7%, sets overlap, no result.
- peak resident 108 MB to 110 MB, which is the steady state's own peak in both binaries: the first replay now takes the path the third run always took.

`--mode cold`, six interleaved samples on a quiet box: wall 10.07 / 10.31 / 10.14 / 10.52 / 10.12 / 10.40 s to 10.27 / 10.31 / 10.31 / 10.81 / 10.30 / 9.62 s, median −0.0%, no change; peak resident +0.3%, no change. The build writes 836 more store entries and asks about 147 more items. Its counters move a little for a reason of their own: `cache_hashes` 4,591 to 4,739 (the mints ask), `decls_gated` 62,850 to 62,702 (a mint was two timed kernel calls and is one), and one mint is answered by an identical one minted in an earlier module, which is `check_terms` 5,797 to 5,796 and `conv_misses` 127,089 to 126,204.

## Tests

`crates/cache/tests/end_to_end.rs`: `the_first_replay_of_a_build_asks_the_kernel_nothing_the_build_asked` (a fixture with a minted derivation and two theorems, widths one and four, with the same replay over another store as the control), `a_build_keeps_no_statement_verdict_that_opened_a_sealed_proof`, `an_abandoned_question_does_not_describe_what_lands_in_its_place`.

## Not done here

The first replay still hashes every binding's interface to ask its questions, where the steady state is vouched for whole by one replay verdict per module (`REPLAY_ENTRY`). The build could record that verdict itself, after decoding the image it wrote and comparing it with what it checked. That moves trust from "the kernel or a verdict saw each binding" to "the encoder round-trips", so it is a decision about the trust argument (`docs/cache-v1-design.md` §6) and not a constant to shave.
