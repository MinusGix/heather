# Elab test families: fewer binaries, unchanged granularity

Owner issue: `issues/elab-integration-test-binaries-merge.md`. Numbers and
the lever ranking: `issues/rust-edit-loop-build-bound.md`.

## Problem

`crates/elab/tests/` holds 178 files, and Cargo makes each one its own test
binary. Every one of them statically links the whole compiler, and every one
builds at `opt-level = 3` (the `heather-elab` package override covers its test
targets too). A Rust edit to elab or the kernel therefore rebuilds and relinks
about 180 binaries. Link work and disk both scale with the binary count, not
with the tests.

## Goal and non-goals

The goal is to cut the number of elab integration-test **binaries** to about
12–16, and to change nothing else a developer or the runner can observe:

- **Rails.** Every file's tests still run in a process of their own, under
  their own `ulimit -v`/`-t`.
- **Fixtures.** Per-process fixtures (`support::library`'s `OnceLock`, the
  semantic-image warm-ups) are still paid once per former file. Coarser
  sharing is a separate, later choice (§Later).
- **Timing history.** Each former file still gets one timing row, under its
  old label (`crates/elab/tests/<file>.rs`), so `test-target-timings-*.tsv`
  history stays continuous.
- **Paths.** Every file keeps its path. Docs and issues cite these paths
  hundreds of times.
- **Commands.** `scripts/test -p heather-elab --test <file> [filter]` keeps
  working.

Out of scope: the cli and cache test binaries (17 + 4), the O3 question for
test code (`issues/elab-rebuild-floor.md`), and moving tests out of the elab
package.

## Design

### D1. Family entry points; files stay put

`crates/elab/Cargo.toml` gets `autotests = false` and one `[[test]]` per
family:

```toml
[[test]]
name = "family_lib_std"
path = "tests/families/lib_std.rs"
```

A family file mounts its members by path, together with the shared
modules, once each:

```rust
#[path = "../support/mod.rs"] mod support;
#[path = "../function_ir_x86.rs"] mod common;   // only where members use it
#[path = "../lib_std_list.rs"] mod lib_std_list;
#[path = "../lib_std_string.rs"] mod lib_std_string;
```

The module name is the file stem. That keeps test names `lib_std_list::<test>`
and makes the first path segment the shard key (D3).

**Standalone targets stay standalone.** A target with its own reason to be a
separate binary keeps its own `[[test]]` entry: `frontend_bench_smoke` (an
EXCLUSIVE_TARGET that times itself), the two `semantic_*_warmup` targets
(scripts/test runs them before the parallel phase), and anything the pilot
(D6) finds pathological.

### D2. Member files: shared modules by `use`, not by `mod`

A member file mounted by `#[path]` resolves its own `mod support;` relative
to itself. Each member would then compile a private copy of `support`, with
a private `OnceLock`. Replace the declaration in every member:

- `mod support;` becomes `use crate::support;`
- `#[path = "function_ir_x86.rs"] mod common;` becomes `use crate::common;`
- `#[path = "support/structured_composition.rs"] mod …;` is mounted once in
  the family file and `use`d the same way.

Module-level `#![allow(dead_code)]` stays legal in a module. It is the only
inner attribute in the directory. `function_ir_x86.rs` has no tests. It stops
being a zero-test binary and becomes only `crate::common`.

Warnings: a family has one `support` for many members, so `dead_code`
warnings from `support` change shape. Silence them at the family's mount
point, not per helper.

### D3. The runner shards a family binary by module

`scripts/run-test-targets.mjs` gains one step between `parseArtifacts` and
scheduling. For every artifact whose target name starts with `family_`, it:

1. runs `<exe> --list --format terse`, passing the lane's `--skip` args so
   skipped tests don't count;
2. groups the names by first `::` segment;
3. emits one shard per group. The shard's `name` is the segment, its `label`
   is `crates/elab/tests/<segment>.rs`, and its extra libtest args are
   `--exact <name>…` with every test name in the group. A group whose tests
   are all skipped emits no shard. Today such a target runs, reports 0
   passed, and costs nothing.

Everything downstream works per shard exactly as it did per target: the
rails in `limitedCommand`, CPU accounting and the warning line, the timings
TSV, `EXCLUSIVE_TARGETS` (matched on the shard name), `--keep-going`, and the
INCOMPLETE detection. Checked 2026-09-24: libtest accepts several `--exact`
filters in one invocation.

`scripts/test-target-runner.test.mjs` gets a case for the sharding: a fake
`--list` output with two modules and one all-skipped module yields two shards
with the right labels and args.

### D4. `scripts/test --test <file>` still means the file

The focused path passes `"$@"` to `cargo test` unchanged. Add a translation
before that. For each `--test X` where X is not a `[[test]]` name, find the
family whose file mounts `mod X;`, rewrite the arg to `--test <family>`, and
add `X::` as a libtest filter. Most elab member tests are top-level functions
named uniquely, so `X::name` works as a substring filter. Keep any
user-supplied filter. When the user gives both, the filter becomes `X::name`.

The semantic warm-ups call `cargo test -p heather-elab --test "$target"`
directly. They are standalone (D1), so they need no change. Check every
other direct `--test` use in `scripts/` (`measure-x86-conv-miss`, `perf`,
`probe-*`) and route it through the same lookup or update it to the family
spelling.

### D5. A lint that no file is left out

`autotests = false` means a new `tests/foo.rs` would silently never compile.
Add `scripts/check-elab-test-families.mjs` and run it in `scripts/test`'s
preamble, next to `check-tree-sitter-inventory.js`. It fails unless:

- every `crates/elab/tests/*.rs` that isn't a shared module is either a
  standalone `[[test]]` or mounted in exactly one family;
- every mounted path exists;
- no member still declares `mod support;` or `mod common;`.

Name the files the lint treats as shared modules in the script itself.

### D6. Pilot first, then sizing

Build a family's cost in before converting everything. Convert one mid-sized
family first (about 10–15 members, e.g. the `lib_std_*` files plus a few
neighbours) and measure it with `cargo test --no-run --timings`:

- **elab body edit**: the family unit's duration next to the sum of its
  former members' units (cargo timings, same edit as the owner issue).
- **member-file edit**: a one-line change in one member. This is the new
  cost: the whole family recompiles at O3, with incremental reuse.
- **no edit**: `scripts/test --fast` wall and summed CPU, unchanged within
  noise.

If the member-file edit or the family unit's wall is bad (say, over about 20
s, or longer than the elab lib rebuild on the critical path), shrink the
families. Don't reach for opt-level. Report the pilot's numbers before
converting the rest. Size the remaining families by the pilot's per-member
compile cost, so that no family is the build's last unit. Group by name
prefix and topic where that falls out naturally (`function_ir_*`, `traits_*`,
`indexed_*`/`branching_*`, `omega_*`, `certgen_*`, `lib_std_*`); grouping
matters to people reading `--test family_x`, not to the runner.

### D7. Verification

- The total test count is unchanged: `== suite: N passed` against the base
  run, and fast-lane N the same.
- The `test-target-timings-full.tsv` rows for elab files keep their labels.
  Diff the set of labels before and after; only the removed zero-test
  `function_ir_x86.rs` row should differ.
- The owner issue's measurement redone: an elab body edit and a kernel body
  edit, build wall and summed unit CPU, before and after.
  `du -sh target/debug/deps` before and after.
- `scripts/test -p heather-elab --test lib_std_list` and `--test lib_std_list
  <name>` run exactly that file's tests, and exactly that one test.
- `scripts/test --long` is not needed. No kernel code moves.

## Later (not this round)

- Coarser shards: one process per family to share `support::library`
  across members. This changes rails and fixture granularity, so it's its own
  decision.
- A separate test package at a lower opt-level for test code
  (`issues/elab-rebuild-floor.md`).

## As landed (2026-09-24)

13 families (`crates/elab/tests/families/`) and 3 standalone targets. The
implementation departs from the sections above as follows:

- **D2.** There are three more shared modules. `omega_cases/` and
  `support/structured_composition.rs` (mounted as `composed_fixture`) are
  mounted once per family, like `support`. `function_ir_x86.rs` becomes
  `crate::common`. `omega.rs`, `omega_logic.rs` and `omega_reconstruction.rs`
  drop `mod support;` altogether: they declared it only so `omega_cases` could
  reach `super::support`.
- **D3.**
  - Under `--exact`, libtest also matches `--skip` exactly. The runner
    therefore applies the lane's skips when it lists a family's tests, not
    when it runs them.
  - A test outside every member module is an error.
  - Per-test rows in `test-times-*` drop the member prefix, so their history
    continues.
  - The five `certgen_*` files whose tests are all fast-lane skips have no
    fast-lane row now. Before, each reported 0 tests.
- **D4.**
  - The lookup lives in the lint (`check-elab-test-families.mjs
    --rewrite-args`), so one parser reads the family files for both jobs.
  - A member can't share a run with another `--test`.
  - `--test family_x` given directly is allowed. It prints a note that the
    family runs as one process under one rail. The focused path doesn't
    shard.
  - `instrumentation.rs` builds its re-exec names from `module_path!()`.
- **Build.** Link work and executable disk now scale with the family count
  instead of the file count. The dated numbers are in the owner issue's log.
  Cargo doesn't delete the old per-file executables, so an existing target
  dir keeps them until it's cleaned.
