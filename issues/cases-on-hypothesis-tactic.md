---
title: "`cases h`: take a call-result hypothesis apart along the call's own tests"
status: open
thread: Refine hypotheses through calls in case splits
labels: [tactics,elaborator,matching,proofs]
area: tactics
milestone: [lang-proof-modularity]
created: 2026-11-17
updated: 2026-11-17
---

A proof about a program that returns `Option` (or a `Bool` verdict) mostly
inverts it: from `emitted: p.call(…) = Some(c)` it learns which branch
the call took, with every test on the way named. Since
[[case-split-refines-hypotheses-under-calls]] the elaborator can read such a
hypothesis reduced and find the test it is stuck on, so each step is one
`match fit: test { False => absurd(emitted), True => … }`.
`Target::call_runs` in `lib/native/native_compile_correct.hthr` is that
step three times by hand, and most of the remaining written `as λ` motives
in `native_compile*` are the same loop written out
(`docs/tactics/program-proof-tactics-design.md` §3 A2 is the `split_all`
half of the same wish).

## Wanted

`cases emitted` (spelling to settle with Minus) runs the loop:

1. read `emitted`'s type reduced, as `matching::hypothesis_through_calls`
   does, and find the test it is stuck on;
2. split on that test with its equation named, refining `emitted` (and the
   goal) in each arm;
3. close each arm where `emitted` now reads `C(…) = D(…)` for distinct
   constructors; where it reads `Some(x) = Some(c)`, substitute `c := x`
   (injectivity then `subst`) and stop;
4. repeat on what remains until `emitted` is no longer stuck.

What it leaves is the real arm(s): the goal with `c` replaced by the
call's value, and each test's equation in scope under a name the user can
refer to (default: derived from the test's head, `fits`, `nth`; or given,
`cases emitted as fit, found`).

## Shape of the proof it builds

The same terms the hand proof writes: nested motive-less matches with
`h:` binders, `absurd` in the refuted arms, `subst` in the last. No new
kernel rule, and the kernel checks what it builds as it checks the hand
proof.

## Done when

`Target::call_runs` (and `Prog::laid_of`, `Source::calls_laid`) read as one
`cases` line followed by the real arm's proof, and probes in
`lib/_tests/std/tactic/` cover: a literal and a neutral test, an open
element type, a nested `Option` pipeline, a `Bool` verdict (`= True`), a
hypothesis that is not stuck (refused with a reason), and one whose last arm
needs a further split of the goal.

Related: [[split-all-revise-hypotheses]], [[case-split-refines-let-bound-call-values]].

## Log

- 2026-11-17: Built as a block statement `cases h;` / `cases h as e1, e2(x, y);` (docs/tactics/goal-combinators.md, `cases h`; crates/elab/src/hypothesis_cases.rs). Each step is absurd / subst / a motive-less `match e: test`, re-entered in each arm; the test is `split_all`'s blocker search with `deep` off, which takes the stage call the callee wrote and unfolds the callee before searching its arguments. Names bound the splits taken (`region_extends` stops at `region.code(…) = Some(c)`). Rewritten: `call_runs`, `laid_of`, `calls_laid` (two lines), `region_extends`, `within_leaf_into`. Not yet covered: a case whose surviving arms need different proofs (`within_one_node`, `within_computes_best`): the rest of the block is one proof for every surviving case.
- 2026-11-17 (second round): each step now splits `Π(h). goal` with the motive the blocker search built and applies the split to `h` (`hypothesis_cases::Stepped::Split`, elaborated in `checking.rs` as `split_all`'s splits are), instead of a motive-less match that relied on §4.7's reading of `h`. In each case `h` is the reduct the test was found in, so a structural recursion's later call reads as the call (`yes.emits(…)`, the root's refolded `(λ i q̄. g(nth(cs; i), q̄))(0, …)` read as `first.emits(…)` by `readable_call`) and is split and named in turn; a hypothesis passed beside an equation is no longer kept as written; a hypothesis whose type a definition computes (`t.EmitsRun(s, …)`) is decoded to its equation first. The goal is refined where it spells the test as the split does; through a definition (`s.checks(…)`) it is not, and the named equation is used (`Bool::is_true_of_eq(apart)`). Rewritten: `Stmt::emits_extends` (every arm), `Stmt::emits_runs` (Branch, Repeat, Exit, Arg, Perform), `Prog::within_byte_node`, `Target::goes_byte_node`, `Stmt::checked_sound`, `Homes::nodes_checked_sound`, `StructuredRegion::ok_of_scoped`, `StructuredRegion::faithful`, `Region::paired` (60 lines to 7), `Source::compile_laid`. Surviving cases that need different proofs compose: a plain `match` on what tells them apart (refining `h` by §4.7) with `cases` in the arm that needs it (`within_one_node`, `goes_one_node`, `within_computes_best`, `goes_computes_best`, `compile_laid`). Left: a `Then`'s `Dataflow` arm in `emits_runs` splits on `pair_known`, which `emitted` reaches only through a let-bound argument (no test of `emits` itself).
