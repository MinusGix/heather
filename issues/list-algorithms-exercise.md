---
title: Prove basic list algorithms: the file that ranks the sugar
status: closed
labels: [frontend,stdlib,testing,ergonomics]
created: 2026-08-05
updated: 2026-08-10
---

Small round item (2026-08-05 ergonomics round). Write a `lib/std`-adjacent
file of small algorithms with real proof content — reverse involution,
append associativity, `nth`-after-`append`, insertion sort sortedness (and
permutation if it fits the budget) — written FIRST in today's language,
then revised as the round's sugar lands.

The point is the method that found [[prelude-option-and-friends]]: the
first real library file exposed the propagation noise no design session
predicted. This file is the falsifier and ranking function for
[[call-site-overapplication]], [[auto-refl-empty-block]],
[[type-owned-members-receiver-slice]], and for whatever it hurts to write
that none of them fix (candidates it may promote: `apply` from
[[surface-proof-automation]], Option chaining from
[[prelude-option-and-friends]], expected-type resolution from
[[type-owned-namespaces]]). Record the before/after of each proof as the
evidence.

Also doubles as a regression/scaling datum: check the file's
`heather check` time against the [[ih-generalization]] cost log's warning
about explicit-motive term size (all runs ulimit-wrapped per CLAUDE.md).

## The file, and what it ranks (2026-08-05)

`lib/list_algos.hthr`, 276 lines, 23 declarations: `rev` + `append_nil` +
`append_assoc` + `rev_append` + `rev_involutive`; `len` + `plusl` +
`nth_append_r` + `nth_append_l`; `andb`/`le_head`/`sortedb`/`ins_pick`/
`insert`/`isort` with the `Bool` conjunction kit, four congruences,
`leb_false_flip`, `le_head_insert`, `insert_sorted`, `isort_sorted`.
Permutation was not attempted (budget). `heather check`: **0.83 s before, 0.86 s
after** — the round costs nothing measurable, and both are two orders below
`lib/ir_v1.hthr`'s 26.9 s, so [[ih-generalization]]'s explicit-motive warning
does not bite at this size (this file writes two motives, both convoys, and
neither generalizes an argument).

### Before / after, per proof

| proof | before | after |
|---|---|---|
| `append_nil`, `append_assoc`, `rev_involutive`, `nth_append_r`, `isort_sorted` | `Nil => refl` | `Nil => {}` |
| `insert_sorted`, `leb_false_flip` base arms | `λ hs => refl` / `λ p => refl` | `λ hs => {}` / `λ p => {}` |
| `nth_append_r` statement | `nth(append(xs, ys))(plusl(len(xs))(i)) = nth(ys)(i)` | `append(xs, ys).nth(plusl(len(xs), i)) = ys.nth(i)` |
| `nth_append_l` statement | `nth(xs)(i) = Some(a) -> nth(append(xs, ys))(i) = Some(a)` | `xs.nth(i) = Some(a) -> append(xs, ys).nth(i) = Some(a)` |
| `nth_append_l` ih | `nth_append_l(t, ys)(k, a, p)` | `nth_append_l(t, ys, k, a, p)` |
| `leb_false_flip` statement + ih | `leb(x)(y) = False -> leb(y)(x) = True`, `leb_false_flip(k)(l, p)` | `leb(x, y) = False -> leb(y, x) = True`, `leb_false_flip(k, l, p)` |
| `le_head_insert`, `insert_sorted` motives | `leb(x)(h2)`, `leb(x)(h)` | `leb(x, h2)`, `leb(x, h)` |
| `insert_sorted` body | `andb_true_l(a, b)(hs)`, `leb_false_flip(x)(h, e)`, `le_head_insert(h, x, t)(hx, ht)`, `andb_true(a, b)(p, q)`, `insert_sorted(x, t)(hst)` | one argument list each |
| `isort_sorted` | `insert_sorted(h, isort(t))(isort_sorted(t))` | `insert_sorted(h, isort(t), isort_sorted(t))` |
| the six `cong_*` | `j(p, λ y q => …, refl)` | unchanged — `{}` works there but is not an improvement over `refl` |

Counted: **19** `f(a)(b)` sites collapsed (9 curried `leb`/`plusl` calls, 10
partial-application chains, of which 5 are induction hypotheses), **4** `nth`
calls turned round onto their receiver, **8** `refl`s that became `{}`.

### Ranked: what still hurts, that none of the three features fixed

1. **Rewriting under a context — the missing `cong`.** Six of the file's
   23 declarations are congruence lemmas that exist only to move an equation
   into one argument position (`cong_sortedb`, `cong_le_head`, `cong_andb_l`,
   `cong_ins_pick`, `cong_cons`, `cong_append_l`), and every rewrite step is a
   hand-written `trans(cong_f(…, p), q)`. This is the single largest tax in the
   file by a wide margin, and it is [[congruence-by-anti-unification]]'s
   subject: the function is recoverable from the *expected type*, so the
   author should not be naming it. `apply` from [[surface-proof-automation]]
   helps the *spelling* of the composition; it does not remove the six lemmas.
2. **Dependent case analysis on a decided predicate (the convoy).** `insert`
   branches on `leb(x, h)`, so every lemma about `insert` needs the scrutinee's
   equation, which today means writing
   `match leb(x, h) as λ b => (leb(x, h) = b) -> Goal { … }(refl)` **and**
   hoisting the branch into its own `fn` (`ins_pick`) with the recursive call
   passed in as an argument, because a `match` written inline is stuck under a
   `Bool` no equation can reduce. Two devices, both mechanical, both invented
   by the author. This is the second-largest tax and it has no issue yet.
3. **`absurd` cannot refute an equation on the scrutinee itself** —
   [[absurd-on-branch-scrutinee]], filed off this file. It made the natural
   statement of `andb_true` unprovable by cases and forced a rewrite-based
   proof instead. Small in this file, load-bearing for any decided predicate's
   inversion kit.
4. **Expected-type resolution for members** ([[type-owned-namespaces]]' other
   half). `Nil` and `Some(h)` are constructors reached by expected type
   already; nothing else is. With `List::nth` now a member, its *lemmas* have
   no home — `nth_append_l` is about `List::nth` and is still an ambient name,
   so the ambient namespace shrank by exactly one name and grew by four.
5. **Option chaining** ([[prelude-option-and-friends]]) — ranked last, and the
   surprise of the exercise. `nth_append_l` states its result as
   `nth(…) = Some(a)` and never needs to *chain*, so `and_then`/`map` never
   came up. The Option pain that issue predicted is not visible at this size;
   what would provoke it is a `find`/`lookup` algorithm, not indexing.

Two smaller notes that are not rankings: `nat::add` recurses on its second
argument while list indexing needs a left-recursive `+`, so the file declares
`plusl` — a second addition, with no lemmas relating it to `add`. And `map` is
declared bare in *both* `list` and `option`, so it is already ambiguous at use
for any file importing both; members would fix that (`List::map`,
`Option::map`) and this round did not move it.

## What it assumes from elsewhere
- **[[ih-generalization]]** owns the varying-argument recursion tax.
  Assumed here: only that insertion sort's inner recursion may hit it and
  the workaround (curried return) is acceptable in this file.

## Log

- 2026-08-05: LANDED: lib/list_algos.hthr, 276 lines / 23 declarations, written first in today's language and then revised onto the round's three features. The body of this issue now carries the file's inventory, the per-proof before/after table, and the ranked still-hurts list; three findings are worth repeating here. (1) The exercise found a live defect nobody predicted: absurd cannot read a constructor equation whose endpoint is the match's OWN scrutinee, because an arm's motive is instantiated at the injected binder rather than at the constructor literal — filed as absurd-on-branch-scrutinee, with a workaround in the file (state the hypothesis over a computation, not over the scrutinee). (2) The three features are unevenly valuable at this size. Over-application is the big one: 19 collapsed call sites, 5 of them induction hypotheses (which needed a deviation in call-site-overapplication to reach). Receiver-reached members turned 4 nth calls round and read well. Auto-refl fired 8 times and saved nothing — every site it replaced already said refl, which is no longer than {} and says more; its real customers are whole-theorem computation lemmas, of which this file has none. (3) The ranked list puts REWRITING UNDER A CONTEXT first by a wide margin — six of the 23 declarations are congruence lemmas that exist only to move an equation into an argument position — and dependent case analysis on a decided predicate (the convoy, plus hoisting the branch into its own fn so the recursive call can be an argument) second. Option chaining, a predicted candidate, ranked LAST: nth-shaped lemmas state their result as = Some(a) and never chain. Cost datum for ih-generalization's warning: heather check is 0.83 s before and 0.86 s after, two orders below lib/ir_v1.hthr's 26.9 s; the file writes two explicit motives, both convoys, neither generalizing an argument, so the explicit-motive term-size tax does not appear at this size.
- 2026-08-05: Still-hurts item 2 got its owner after close: [[decided-case-convoy]].
- 2026-08-10: The branch-scrutinee workaround is retired by [[absurd-on-branch-scrutinee]]: `andb_true` now uses the direct case split originally refused. The exercise’s historical finding remains accurate; the live file no longer carries the workaround.
