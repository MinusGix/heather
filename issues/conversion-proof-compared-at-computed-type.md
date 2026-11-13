---
title: Two proofs of a computed proposition are compared by computing it
status: open
labels: [native,runtime-fn,performance,kernel]
area: heather-in-heather
created: 2026-11-12
updated: 2026-11-12
---

Found scaling a `runtime fn` of a laid record ([[sha256-context-type]]). A function of seventeen field statements compiled, pinned and proved, and then its link (`program_spanned_answers`'s `linked` argument) ran out of the elaborator's comparison budget. Thirteen statements passed.

The cause was one argument of the instance. `FFun::compile` took `ok: Setup::lowers(rt.lower(w, fsigs, n)).IsTrue()`, given `trivial`. A link names a function's instance several times in one statement (its code, its arity, its source), and the kernel compares two mentions argument by argument, each at the argument's type. To compare `trivial` with `trivial` at `b.IsTrue()` it first computes the type, which is the whole lowering of the function, again at every mention. Measured on a twelve-statement function with probes in a scratch module: two copies of the instance compared cost about a quarter of a comparison's budget, and each argument compared by itself (the reflection, the worlds, the written function, the pin's proof) a hundredth or less. Two `trivial`s at that type, in declarations of their own, cost what the instance did.

What this round did, in the library: every compile entry point (`Setup::compile`, `compile_fuel`, `compile_measured`, `FFun::compile`, `FFun::compile_measured`, and the theorems they apply) takes the verdict as `check = True`, proved by `refl`. An equation's type is an equation whatever its sides, so nothing is computed to compare its proofs. This is `docs/proof-patterns.md`'s rule for closed verdicts, which these signatures predated.

What is left for the kernel or the elaborator to decide:

- Two terms that are one closed syntax node evaluated in two environments are compared structurally. A closed term has no environment to differ in, and the kernel already keeps free-variable bounds on each node, so "same node, closed" could answer at once. That would have made this cost invisible, and the pin's proof and the reflection beside it.
- A proof argument is compared at all. Where the type is a proposition by construction (`IsTrue`, an equation) two inhabitants need no comparison. The kernel has no proof irrelevance today and this issue does not ask for it, only records that the cost was paid for nothing.
- The other `IsTrue` premises of the link's theorems (`named`, `fitted`, `fits`) sit in proofs, which are compared only if two copies of a proof meet. None has been seen to. If one does, the same change applies.

Related: [[runtime-link-compares-functions]] (the same statement, a different pair compared), [[conversion-fuel-failure-says-where]] (this took a day of probes to find, and a counter per argument would have named it).
