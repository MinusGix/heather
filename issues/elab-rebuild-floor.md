---
title: The elab rebuild floor: a second O3 compile for unit tests and a 22 s lib rebuild per edit
status: open
labels: [testing,performance,build]
created: 2026-09-24
updated: 2026-09-24
---

What remains of a Rust edit's build once
[[elab-unit-tests-wait-on-cli-dev-dependency]] lets the unit-test compile run
in parallel ([[rust-edit-loop-build-bound]] owns the numbers):

- elab's unit-test compile, a second full O3 compile of the crate under
  `cfg(test)`, ~40 s: the floor of the build's wall.
- the elab lib rebuild, ~22 s at `opt-level = 3`, for any edit to elab *or*
  the kernel.

Levers, not yet costed: move unit tests that use only the public API out of
`src/` (shrinks the second compile); split `heather-elab` into smaller crates
(the only lever that also shrinks the lib rebuild); reconsider elab's dev
`opt-level = 3`, which trades against test runtime and needs a
`scripts/perf ab`-style comparison of the loop, not of the tests alone.

Re-measure after the first lever lands before choosing.

## Log

- 2026-09-24: **Re-measured after both levers landed, and attributed** (same desktop). Build after a one-line edit, `cargo test --workspace --no-run --timings`: elab edit 24.2 s wall, kernel edit 26.8 s. It is now two parallel O3 compiles of elab's sources and nothing else: `heather-elab` lib 22 s (codegen 20 s) and `heather-elab-unit`'s `--lib` test 22–24 s. Integration tests are off the critical path. Probes on the lib alone (`cargo build -p heather-elab --lib`, counting rewritten CGU objects in the incremental session dir; 214 CGUs; a full O3 build of the lib is 30 s):

  | edit | time | CGUs rewritten |
  |---|---|---|
  | comment appended at the end of lib.rs | 2 s | 0 |
  | same-line edit in lib.rs (`kernel_workers_from_env`) | 18 s | 33 |
  | same-line edit in measure.rs (`lt_ty`) | 12 s | 5 |
  | comment line inserted at the top of lib.rs | 20 s | 147 |
  | same, with `debug = 0` for elab | 18 s | 146 |

  - **Wall is the largest rewritten CGU, not their count.** With `-Zhuman-readable-cgu-names`, the largest object by far is the crate-root CGU, `heather_elab` (10.8 MB): lib.rs's single 6,367-line `impl Elaborator` block (lines 1500–7867). The measure.rs edit still rewrote it, as did every probe. Next come the generic-instantiation buckets `alloc::vec` (6.1 MB), `core::iter::adapters::map` (4.4 MB) and the `fallback` CGU (4.5 MB); the first two were rewritten in both same-line probes.
  - **Line shifts invalidate every later item.** Inserting a line recompiles everything whose spans moved. Debug line tables are not the cause (`debug = 0` changes nothing); panic `Location`s embed lines too. This is inherent, not a lever.

  Levers, re-ranked:
  1. **Split lib.rs's `impl Elaborator` into modules**, the way `application`, `matching` and `expr` already hold their own `impl Elaborator` blocks. rustc partitions incremental CGUs by source module, so this breaks up the 10.8 MB root CGU. It helps both compiles (lib and unit tests), and an edit then rewrites only the pieces it touches. The floor after it is set by the `vec`/`iter-map` generic buckets, which a module split does not divide. Estimated (not measured) lib rebuild: 12–18 s → roughly half.
  2. **elab's dev opt-level** (O3 → O2 or O1): a loop-level trade against the test phase's elab-heavy CPU. Measure build + fast lane together, never the build alone.
  3. Moving public-API-only unit tests out of `src/`: small now, since the unit compile runs in parallel and is no longer the tail on its own.
- 2026-09-24: **Lever 1 (split lib.rs's `impl Elaborator` into modules) is refuted by a pilot, and reverted.** Moving `elab_infer`/`elab_infer_at` into a submodule left the CGUs unchanged: 214 CGUs, root still 10.8 MB, no new CGU, identical rewrite counts on all three probes. `nm` over `-Zhuman-readable-cgu-names` objects shows why: rustc places an inherent method in the CGU of its **self type's** module, not the module that writes it. So the root CGU is every `Elaborator` method crate-wide (446 of them, including `dispatch/operator.rs`'s and `matching/routes.rs`'s), and the existing `application`/`matching`/`expr` submodules never had CGUs of their own for their methods either. The previous entry's reading ("lib.rs's single 6,367-line block") was wrong.

  The only structural ways to move that code into other CGUs are to change the code's shape for the compiler's sake: free functions taking `&mut Elaborator` behind one-line shim methods, or a wrapper type per submodule (`struct Infer<'a>(&'a mut Elaborator)` with `DerefMut`). Both mean distorting the design for build speed, which perf policy rules out; not pursued. (Recorded here as the mechanism, not as a queued lever.)

  What remains without distorting code: elab's dev opt-level (a loop-level trade, measured as build + fast lane), and nothing for the generic buckets (`alloc::vec` 6.1 MB, `iter::adapters::map` 4.4 MB, `fallback` 4.5 MB), which every same-line probe rewrote.

  Correction to [[rust-edit-loop-build-bound]]'s kernel-edit numbers: they were confounded. The measuring script reverted the elab probe edit just before applying the kernel one, so every "kernel body edit" build also rebuilt elab. A kernel body edit alone (`nat_residual`, not inlined into elab) builds in ~7 s (elab lib 2.4 s, elab-unit 4.4 s). The elab-edit column stands.
