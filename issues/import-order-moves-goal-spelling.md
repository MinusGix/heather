---
title: An import in a dependency changes whether bv_omega can spell an importer's goal
status: open
thread: Rebuild loops on one combinator
labels: [elaborator,tactics]
area: language
created: 2026-11-20
updated: 2026-11-20
---

Adding `import loop;` to `lib/native/runtime/rt.hthr` (which already reached
`loop` by written paths) made
`lib/_tests/native/runtime/bytes_loop_combinator_tests.hthr`, which imports
both `rt` and `loop` itself, fail: a `put`'s default `inside` proof by
`bv_omega` refused with "could not spell the goal"
(`crates/elab/src/bv_omega.rs`, `spell_type_source` fell back somewhere in
`run(Loop(left, λ (x: Hole) => sift(…), …)).j < len(….s)`).

Reproduction: on master as of 2026-11-20, add `import loop;` after
`import function_ir_operation;` in `rt.hthr` and check the probe. A
`loop::Loop::passes()` written in `rt.hthr` instead of the import leaves it
passing.

So an import in a dependency changes how a goal in an importer spells.
Likely a base name (`Loop`, `run`, `Pass`, …) that now resolves to another
global, or a qualified spelling that does not resolve back, depending on the
order of the import closure. A goal's spelling should not depend on what a
dependency imports. Worked around in round 3b by not importing.
