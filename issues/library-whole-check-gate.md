---
title: Check every lib/ module in the suite, and flag orphans
status: closed
labels: [testing,library,tooling]
area: infrastructure
created: 2026-10-24
updated: 2026-10-24
---

No test checks the library as a whole. The suite checks a `lib/` module only
while some Rust test lists it in a `MODULES` closure, so every library PR
writes a Rust test file whose first job is to get its module checked at all
(`docs/test-value-audit.md` §3.1, owner of the reasoning).

The gap is not hypothetical: at 87348e3, `lib/std/os/linux/elf64_load.hthr`
is imported by no module and listed by no test. The B2 burn (#156) removed
its last test. It still checks (`heather check --cache -L lib/std`), but
nothing would notice if it stopped.

## Proposal

1. One test that checks every module under `lib/` through the CLI with
   `--cache`, the way `crates/cli/tests/showcase.rs` checks a manifest row
   (images replay warm; cold it is one library elaboration, which a fresh
   box's suite already pays more than once, `docs/testing-architecture-design.md` §1).
2. A lint: every `lib/` module is imported by another module or named as a
   root (a `lib/_tests` module, a showcase dependency). An orphan fails until
   it says which.
3. A second lint: nothing outside `lib/_tests` imports a module in it.
4. Decide `elf64_load`: delete it as burn residue, or give it an importer.

With (1) in place, the "the X module checks" tests in
`crates/elab/tests/lib_*.rs` are redundant
([[library-tests-as-theorems]]).

## Log

- 2026-10-24: Implemented: `crates/cli/tests/library.rs` checks every `lib/` folder through the CLI (one child per folder, three at a time: one process for all of `lib/` takes about the whole CPU rail cold), and lints that every module is reached and nothing outside `lib/_tests` imports a test module. `elf64_load` stays as a kept root: `docs/native-program-logic-design.md` §3 keeps it for the native rebuild.
