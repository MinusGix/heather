---
title: Every Type::member name walked the prelude's import closure
status: closed
labels: [elaboration,performance,names]
area: language
created: 2026-11-11
updated: 2026-11-11
---

A qualified name `q::x` is a module path when `q` is a module the scope can see, and one way to see a module is through the common prelude: its closure is visible qualified (`names.rs`, `common_reaches`). That test walked the prelude's import closure at every asking.

## What that cost

The test is reached only when `q` is not the scope's own module, not one of its imports and not the prelude itself. For a name written against a **type** (`Nat::le_add`, `Site::moves_spills`, every method and every constructor spelled with its type), `q` is no module at all, so the answer is no, and it is no only after the whole closure has been walked.

Checking `examples/x86-native/levels.hthr` cold at width one, under callgrind:

- `common_reaches`: 248,884 calls, 3,665 M instructions inclusive (3.3% of the run), 14.7 K per call.
- 3.65 M `Names::module_scope` lookups under it (14.7 per call, each one a layered-table find and a note in the early cutoff's record), 23.5 M string compares in its `seen` list, and a `Vec` grown 1.29 M times.

On the showcase: 540 M of 40,434 M (1.3%).

## What is built

The walk is a function of the module scopes, and `Names::enter_scope` is their one writer. So the registry keeps the walk (`CommonClosure`, in `Names::common`): the modules it pops, in order, and for each module some popped module imports, how many had been popped when it was first met. An asking reads the table. `enter_scope` drops the walk when it writes a scope; a snapshot carries the walk of the tables it carries.

**The record of name lookups is unchanged.** The per-asking walk noted every module it popped (`note`, the early cutoff's account of what an elaboration could have observed, `docs/module-interface-cutoff-design.md` §2): the whole closure for a no, and the modules popped up to the import that named `q` for a yes. The kept walk has that count per module, and notes the same prefix. A noted name stays noted, so it does it once per record (`RECORD` steps when a record starts or is taken, and `WALK_NOTED` holds how much of which walk this record already has).

## What holds it

- A debug build does the per-asking walk again behind a sample of askings and compares the answer and the modules popped (`common_walk_per_asking`), so the suite is a differential test.
- `the_preludes_closure_is_walked_once_and_reads_as_the_walk`: a diamond with a cycle, a module imported and never entered, one the prelude does not reach, the root and a non-module; the answer and the record against the per-asking walk; the same record asked again; a later record told again; a snapshot keeping its own walk when the registry enters a scope.
