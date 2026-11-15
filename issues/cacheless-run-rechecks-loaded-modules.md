---
title: A run without a cache kernel-checks a module again in every world it is loaded into
status: closed
labels: [infrastructure,performance,caching,kernel]
area: infrastructure
created: 2026-11-10
updated: 2026-11-10
---

A `heather check` run with no `--cache` checked a module in the kernel once
where it was elaborated, and then again each time the module was loaded into
another module's world. Found in a stack profile of the cold showcase taken
for [[psi-references-by-level]]: `load_into` → `replay_module_delta_keyed` →
`recheck_extension` was an eighth of the busy samples, in a run that had
elaborated and gated every one of those modules itself a moment earlier.

## Why

A module's world is its largest import's finished state with the rest of its
import closure loaded into it (`docs/infrastructure/module-dag-design.md` §6), and a load is
a replay: the delta is moved onto the new world and every binding is judged
again, by the kernel or by a verdict the gate holds
(`Elaborator::recheck_extension`). With `--cache` the gate holds the verdicts
the source gate recorded a moment ago, so a load costs hashing. Without it
there was no gate, and `recheck_extension` took its one-call form: the whole
extension through `check_signature_extension`, once per world the module was
loaded into. The same binding, over the same referents, by the same kernel,
in the same process.

`crates/cli/src/native.rs`'s `the_bundled_library_checks` had already met
this and installed a verdict store with no file behind it
([[grind-closure-cost]]). The commands themselves had not.

## What was done

`heather_cache::Cache::in_process()`: a verdict store with nothing loaded and
nothing saved. `check`, `compile-x86` and `write-elf` install it when no
cache directory is named. Every declaration still faces the kernel once in
the process, which is what the bare `ok` line promises; what the store
vouches for is that binding met again, identified as `--cache` identifies it
(the elaborated term with its dependencies' interface hashes,
`docs/infrastructure/cache-v1-design.md` §5). A moved delta whose relocation went wrong has
other hashes, misses, and is checked.

The inspection commands (`axioms` and the rest, `check_inspection_modules`)
are left as they were: their comment says they replay without the quick gate
on purpose.

## Acceptance

- `crates/cli/tests/timings.rs`,
  `a_run_without_a_cache_checks_a_loaded_module_once`: a run without a cache
  and a cold run over an empty directory report the same `check_terms`,
  `eval_steps`, `conv_misses` and `decls_gated`, on a root that imports two
  unrelated modules. Before, the bare run's `check_terms` was one higher
  there.
- `scripts/perf ab --mode bare` (added for this: every other mode names a
  cache directory, so the plain command had no A/B).

## Log

- 2026-11-10: Built as described above. `scripts/perf ab --mode bare`, cloud box, width one, three interleaved samples of the showcase, master against the change: wall 22.4 / 21.0 / 19.5 s → 16.0 / 15.2 / 17.3 s (median −23%, the sample sets separate). Counters, exact: `eval_steps` 11,187,860 → 7,093,639, `conv_misses` 149,735 → 96,673, `check_terms` 4,372 → 3,904, `syntax_eq_nodes` 9.50 M → 7.08 M, `cache_hashes` 0 → 4,021. The after column is to the digit what a cold run over an empty cache directory reports, which is the invariant the test holds. So over a third of the evaluator's steps in a bare showcase run were second and later checks of modules the run had already checked. The attribution docs measured with "no `--cache`" (`docs/elaborator/complete-post-attribution-design.md` and the others that say so) carry that share in their run rows; their per-declaration rows are unaffected, since a replay is charged to the load.
