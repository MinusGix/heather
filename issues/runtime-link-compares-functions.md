---
title: A link between two runtime fns of one type compared the functions themselves
status: open
labels: [native,runtime-fn,performance,kernel]
area: heather-in-heather
milestone: [nh-library,crypto-hash]
created: 2026-11-12
updated: 2026-11-12
---

Found writing SHA-256's compression function over spans ([[sha2-compress-native]], `lib/native/crypto/sha256_block.hthr`). The round is three `runtime fn`s, and two of them, `sha256_step` and `sha256_turn`, have one Heather type (`List<BitVec(8)> → BitVec(64) → BitVec(64) → Mutated<…>`). The generator refused the caller: its link check (`Compile::part`'s `linked`, `CompileSpan::spanned`'s `written`) ran out of the conversion budget. A parameter of padding on either function, so that the two types differ, made everything pass.

## What the kernel was doing

`Conv::tm_w` (`crates/kernel/src/conv.rs`), where both sides are stuck at the same defined global, first compares the two applications argument by argument (`delta_lazy`) and unfolds only when that fails. A failed attempt is not refunded.

In a link, a caller's table entry for a callee meets the callee's own source, and both are spelled through the instance: members of the class, the builder that made the instance, the table at a world. Where the two sides were two applications of one of those, the attempt compared their arguments in order, and one argument was the function: `sha256_step` against `sha256_turn`. Two constants of different types are told apart at once. Two of one type are not: the kernel unfolds both bodies under their binders and evaluates them until they differ, which for a SHA round is a comparison of two large open bit-vector terms. Measured 2026-11-12 with a counting build ([[conversion-fuel-failure-says-where]]): the failed attempt at `FFun::compile` cost about 1.9 million steps against a budget of 1,048,576; two reader probes cost 1.37 and 1.94 million.

Three pairings did it, each found by the next trace after the last was removed:

1. `Compile::table` spelled at `c.world` (the table at no file) against a callee's source at `c.world.at(c.callees, b)`: one function at no file against at the file.
2. The class's named members (`Compile::world<F>(f, c)`, `CompileSpan::world<F>(f, c)`): arguments `F`, then `f`.
3. The builders (`Setup::compile<F>(s, rt, w, callees, f, …)` and its fellows, `FFun::compile`): two applications of one function, with `f` an early argument.

## What changed in the library

- `Compile::table` is read off the world at the file (`World::at`'s one spelling).
- `Compile::uncurried` and `CompileSpan::source` read the instance by pattern, not through members.
- Every builder takes `f` after the reflection and the table (`Setup::compile`, `compile_fuel`, `compile_measured`, `FFun::compile`, `compile_measured`), and the generator's calls follow. Two different functions are then told apart at their reflections, which are data.

With these, `sha256_block` passes with no padding, and no checked-in assembly changed (`scripts/linked` rewrote nothing but the new export). The regressions are `sha256_block` itself (the writing pairs, plain and measured) and `probe_t1`/`probe_sum` in `lib/_tests/native/crypto/sha256_block_tests.hthr` (a reading pair).

## What is left

The change orders arguments so that data is compared first; it does not stop the comparison. These would meet it again:

- Two different functions with one type **and identical reflections** up to the point of difference being deep, or corresponding entries of two compared tables (`Setup::lent_callees<F>(f, …)`, `FTm::sems_cons<F>(f, …)`, `World::of` with equal `sigs`), where `f` is still an argument of the thing compared.
- Any later library function that takes a `runtime fn` as an argument before something that distinguishes it.

Remedies, neither done:

- **In the library**: a numeral tag per function as the first argument of whatever takes `f` (the function's index in its program), so that an attempt fails at a literal.
- **In the kernel** (Minus's to decide): a budget for the speculative attempt, with the spent steps charged but capped, so a failed attempt costs at most a fraction of the fuel before the kernel falls back to unfolding; or, inside an attempt, treating two distinct defined constants met as arguments as a failed attempt and not as a thing to settle. Either changes only which route conversion takes, not what is convertible.

## Done when

Two `runtime fn`s of one type link at a cost that does not depend on how long their bodies take to tell apart, by a rule (a tag or the kernel's) and not by the order of each builder's parameters; and the comment at `Setup::compile` is then history.
