---
title: Rewrite the statement compiler's proofs in the forms the language has now
status: open
thread: Make compiler correctness proofs elegant
labels: [native,proofs,readability]
area: heather-in-heather
created: 2026-11-16
updated: 2026-11-16
---

`lib/native/native_compile_correct.hthr` (2,158 lines) and the `native_compile_*` files beside it (about 18,800 lines with `native_structured*` and `native_build*`) were written before most of the proof forms the language has now, and use none of them: no `calc`, no `simp`, no `induct`, no `rewrite` (one), no implicit points. Minus, 2026-11-16: "inelegant and verbose". This issue is the rewrite with what exists; the gaps it would still leave are filed separately and listed at the end. Probes for every claim below: `/mnt/project-files/compile-proofs/`.

No statement changes and no proof is re-argued: each step replaces a spelling by a shorter one for the same term. It still wants Minus's go-ahead, since the compiler's proofs are not edited by hand without it.

## What exists and is not used

| Today | Count (main file / all) | Form that exists |
|---|---|---|
| `p.within_trans(r0, whole, a, r0.within_trans(r1, whole, b, …))` | 66 / 147 | `designation <= at Prog := Prog::Within`, a `Transitive` instance, and `calc { p <= r0 := a, <= r1 := b, … }` (checked on the model and at `Prog`) |
| `j(Option::some_inj(x, c, same), λ x _ => <goal again>, e)` | 25 / 81 | `subst(Option::some_inj(x, c, same), e)` (checked) |
| `Bool::is_true_and(…)` chains feeding `layout.word_inside(…)` | 32 / 140 | `omega(fit)` reads a guard written with `&&`; at `words_fit([…])` it reads the first word only ([[bool-guard-facts-by-known]]) |
| `j(sym(fit), λ v _ => v.IsTrue(), trivial)` | 16 / 55 | take the test as `.IsTrue()` or let `omega` read `fit` |
| seven arms `Compute(_) => false_elim(is), Invoke(_) => false_elim(is), …` | 42 / 42 | `_ => false_elim(is)` |
| seven identical arms over `StructuredRegion`'s constructors, each respelling the constructor with its fields | 4 blocks | `_ => region.region_extends(…)`, done (closed [[wildcard-arm-sees-its-constructor]]) |
| every point explicit: `t.then_nil(leaf, rest, call, perform, ih, ih_rest, p, out, names, c, emitted, within, checked)` | everywhere | implicit points for what a hypothesis names (`{p, out, names, c}` from `emitted`), per `docs/proof-patterns.md` and [[generic-theorem-implicit-points]] |
| `(match test as λ b => test = b → <callee body> = Some(c) → <goal>) { … })(refl, emitted)` | 84 / 204 written motives | `match h: test` where the goal alone mentions the test; the rest wait on [[case-split-refines-hypotheses-under-calls]] |
| `λ (s: MachineState<X86Memory(t.r.profile)>) => …`, `Flow → ITree<BitVec(64)>(Events::linux())` | 100+ | named types (`Target::State`, `Target::Rest`); annotations dropped where the expected type gives them |
| `then_nil`, `then_known`, `then_pair`: one argument three times | 120 lines | one lemma over the first part's claim, the three as its uses |

## Order

1. `Prog::Within` as `<=` with `calc`, and the `within_<builder>` lemmas restated through it (`native_compile_correct.hthr` lines 72–155 first: six theorems, all chains).
2. `subst` for the `some_inj` transports; `_` arms.
3. Implicit points on the lemmas of `native_compile_segments.hthr` and `native_compile_correct.hthr` that every other file calls.
4. Named types, and the three `then_` lemmas as one.

Each step is its own PR, checked with `scripts/test --pr` (it touches `lib/`), with the line count and the heaviest declaration's time before and after in the PR, since a shorter spelling can cost the kernel more (`docs/proof-patterns.md` §2).

## Progress (2026-11-16, PR #723)

Steps 1 to 4 are written, the procedures part included, since stating it is the test of the forms whether or not U5 deletes it.

- Step 1: `Prog::Within` is `<=` with a `Transitive` instance; every chain is a `calc`, and `Prog::within_trans` takes its three programs implicitly (216 callers).
- Step 2: 23 `subst(same, e)` (through `Option::some_inj` until [[constructor-equations-in-context]] landed); `_` arms for the refuted constructors.
- Step 3: `goes_weaken`, `at_sub`, `held_sub`, `held_same` and `at_similar` take their points implicitly. A caller in a `let` with no expected type then states the type it builds, which reads better than the five arguments did. `at_sub` takes its hypothesis before the inclusion so the inclusion is checked against a known set.
- Step 4: 95 of 143 `λ (s: MachineState<X86Memory(t.r.profile)>) =>` binders left to the expected type (the 48 left are `let`s with none). The three `then_` lemmas share `Target::then_at` over `Stmt::and_then`; their inversions of `emits` stay three ([[induct-through-result-matches]]).
- `Bool::both({a, b}, h: (a && b).IsTrue())` beside `Bool::is_true_and(a, b, h)`: all 91 splits in the `native_compile_*` files infer their tests, the four- and five-rung ladders included. The other 433 callers in `lib/` are left to their owners; nothing needed `is_true_and`'s explicit form.
- Procedures: `Hosted`, `Hosts`, `CallsBuilt`, `CallFits` and `ProcedureFits` are records with named fields in place of nested `Exists` and `∧` read as `proof.proof.proof.right.left`.

A named type for the machine state was not added: once the binders are inferred the spelling is left in 97 places, most of them signatures, where an abbreviation would have to unfold for field access and for inference.

Measured over the `native_compile_*` files: 14,377 lines to 14,140, 1,013 KB to 973 KB; the main file 2,158 lines to 2,105. The forms that exist take about four percent off. What is left is what the filed gaps cover: the main file still has 78 written motives and 64 `absurd(none)` arms, all inversions of a `None`/`Some` pipeline.

What the procedures part shows: its statements read well as records and `calc`, and its proofs are then mostly the positions (`Within`, `prog_len`, the `w_*` witnesses passed to each `goes_` lemma), which is [[emitted-code-claims-without-positions]].

## What this leaves, filed

- The hand inversion of every `None`/`Some` pipeline, and the inversion lemmas written for the certificate reader: [[induct-through-result-matches]].
- Written motives that restate a callee's body because a hypothesis is not refined: [[case-split-refines-hypotheses-under-calls]].
- `λ none => absurd(none)` and injection: [[constructor-equations-in-context]].
- Guards past their first conjunct, and guard goals: `known` reads them ([[bool-guard-facts-by-known]], closed 2026-11-16); native_compile_correct has no split left.
- The seven-arm blocks over `StructuredRegion`: [[wildcard-arm-sees-its-constructor]].
- `ITree::bind(Events::linux(), …)` and moving a claim along `≈`: [[itree-surface-implicit-events]].
- Positions (`Within`, `prog_len`) in every code lemma: [[emitted-code-claims-without-positions]], a design question.
- U5 of [[native-one-compiler]] moves procedures onto the function compiler; lines 1528–2128 (procedures, a third of the file) should not be polished ahead of it.

## Done when

Steps 1–4 are merged, `native_compile_correct.hthr` has no `within_trans` nest deeper than one and no `j` whose motive repeats its goal, and the file's line count and check time are recorded here before and after.
