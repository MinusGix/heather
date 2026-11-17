---
title: A Bool guard's conjuncts as facts: past the first, and for guard goals
status: closed
thread: Make compiler correctness proofs elegant
labels: [tactics,omega,proofs]
area: tactics
milestone: [tac-general]
created: 2026-11-16
updated: 2026-11-16
---

The compiler's checks are `Bool` guards (`layout.words_fit([fd, at, len, result])`, `s.checks(homes, out)`, `layout.call_fits(…)`), and a proof that passed one needs its conjuncts. They are taken apart by position:

```
let ok = Bool::is_true_and(layout.word_fits(fd), layout.word_fits(at) && (layout.word_fits(len) && (layout.word_fits(result) && True)),
    j(sym(fit), λ v _ => v.IsTrue(), trivial));
let ok2 = Bool::is_true_and(layout.word_fits(at), layout.word_fits(len) && (layout.word_fits(result) && True), ok.right);
let ok3 = Bool::is_true_and(layout.word_fits(len), layout.word_fits(result) && True, ok2.right);
let ok4 = Bool::is_true_and(layout.word_fits(result), True, ok3.right);
… layout.word_inside(fd, ok.left), layout.word_inside(at, ok2.left), …
```

`native_compile*.hthr` has 140 `is_true_and` and 55 `j(sym(fit), λ v _ => v.IsTrue(), trivial)`.

What exists (probed 2026-11-16, `/mnt/project-files/compile-proofs/`):

- `omega(fit)` reads a guard written with `&&` when the wanted fact is arithmetic ([[omega-reads-bool-guards]]): `(fits(a) && (fits(b) && (fits(c) && …))).IsTrue()` proves `c <= 8`.
- At the real guard it reads one conjunct. `layout.words_fit([fd, at]) = True` proves `fd < layout.words` by `omega(fit)` and not `at < layout.words`: `words_fit` recurses over the list, and the guard round opens a definition by one δ step, so the tail `words_fit([at])` stays an atom (CutSat's model: `layout.words = 1, at = 1, fd = 0`).
- Nothing closes a goal that is itself a guard: from `h: (fits(a) && (fits(b) && (fits(c) && (fits(d) && True)))).IsTrue()` the goal `fits(c).IsTrue()` is refused by `by grind()` ("the goal is not an equation"), by `by sets()` ("not a membership"), and by `split_all; all_goals { known }`.

## Wanted

- `omega`'s guard round opens a recursive `Bool` definition at a constructor-headed argument until it is stuck (to a budget), so `words_fit([fd, at, len, result])` is four facts.
- `known` reads a `Bool` guard in scope by structure, as `omega` does: `(a && b).IsTrue()` and `(a && b) = True` are both sides, through a definition by one δ step and through a recursion over a list literal (`words_fit([x, y])`); `e = True`, `e.IsTrue()` and `Bool::IsTrue(e)` are one fact. A guard goal is proved from conjuncts in scope the same way.
- Or the truth table `by sets()` already builds, opened to any `Bool` atom (`by bools()`): atoms are the maximal non-`&&`/`||`/`!` subterms.

## Done when

`ih_first(…, ok.left)` in `Target::then_nil` is written `ih_first(…, known)` (or with an implicit found proof) from `checked: (first.checks(…) && rest.checks(…)).IsTrue()`, and no `Bool::is_true_and` is left in `native_compile_correct.hthr`.

## Log

- 2026-11-16: Built: `known` reads Bool guards in scope by structure and proves guard goals from their parts (`crates/elab/src/known_guards.rs`, docs/language/when-design.md stage 3). native_compile_correct.hthr has no `Bool::both`/`is_true_and` left: `then_nil`'s `ih_first(…, known)` and the syscall cases' `layout.word_inside(fd, known)`. The lambda parameters named `known` (a `List<Fact>`) in the `then_*` lemmas and `Stmt::emits_runs` are `facts` now, so the name reaches the search. The `omega` bullet moved to [[omega-guard-opens-recursion-and-case-arms]]; the truth-table alternative (`by bools()`) was not needed.
