---
title: Describing the type of a record's k-th field cost k² eliminations per query, and a shift of the record's type per spine
status: closed
labels: [kernel,typing,conversion,performance]
area: kernel
created: 2026-11-10
updated: 2026-11-10
---

Found by stack-sampling the kernel gate of a cold
`docs/showcase/calc_parser.hthr` after the prelude came to import
`ordered_field` (#543), which put class dictionaries, records of records, in
front of every arithmetic lemma: 13% of the gate's wall time was under
`conv::dom::values::select_ity`, and almost all of that in
`Eval::eval_tm → step_eval → eval_tm → …`, the evaluator walking down a
projection spine.

## What it did

`Tc::projection_at_spine` types `snd@(snd@(… p))` as a chain of selections
over `p`'s type (`ITy::Sel`, `docs/elaborator/intro-by-type-design.md` §3.2). Selecting
the second component of a Σ instantiates its codomain at the first, so the
`j`-th selection carries the term `fst@(snd@ʲ⁻¹(p))` (`Sel::Snd`).

A description is arena-free, so every query that looks at such a type
evaluates the chain again from `p`'s type (`eval_ity`): `conv_ity_cached`,
`head_ity_cached` (the checker's `view`), `projection_heads_cached`. And
`select_ity` evaluated each selection's term **eagerly and by itself**:
`fst@(snd@ʲ⁻¹(p))` is `j` eliminations pushed onto `p`, each a neutral and a
spine node in the arena. A chain of length `k` was `k²/2` eliminations, per
query, whether or not the component's type mentions the field at all.

The head of the spine paid a second cost when it was a variable: the `var`
rule answers the entry's type shifted into the ambient scope, a walk of the
whole type per spine, for a type the selections then only evaluate. In the
value domain a type scoped in a prefix of Γ needs no shift.

## What was built

- **One closure per term node per query** (`ValueArena::subject`). A
  selection's term is handed to the codomain unevaluated, and a checked
  projection `fst@(q)`/`snd@(q)` is the pending elimination of `q`'s closure
  (`TmClo::Elim`), which is what evaluating it does. The selections of one
  spine share their receivers' nodes, so each is one elimination of a value
  the query already holds, forced only if the codomain reads it.
- **A description for syntax scoped in a prefix** (`ITy::At`). A variable at
  the head of a projection spine is its entry's type at the entry's depth,
  never shifted. It is formed only there and only as the `of` of a
  selection; `Tc::materialize` shifts it if a rule ever needs the spelling.

## What has to hold

- `fst@`/`snd@` evaluate to the unannotated elimination of their receiver
  (`Eval::elim_of`), so the pending elimination is the same value.
- A closure's value is a function of the closure, and the argument was a
  value of the same term in the same identity environment: laziness changes
  what a query spends and when a failure of the argument is met, not a
  verdict.
- A description's reflexivity shortcut may say no (`ITy`'s `==`): a prefix
  type against an ambient spelling goes to conversion.
- `tests/typing_differential.rs` holds the checker to the eager oracle on
  projection spines, and
  `a_projection_spines_description_is_linear_in_its_length` fails without
  the first change (a spine four times as long cost sixteen times the
  drives).

## Log

**2026-11-10.** Cold `docs/showcase/calc_parser.hthr` on the cloud box, width
one, over master at ab57366 with the lockstep walk, the one hasher, identity
environments and the per-call memos already in.

The shared closures alone (`scripts/perf ab --mode cold`, five interleaved
samples, quiet box):

| | before | after | |
|---|---|---|---|
| kernel gate | 5.74 / 5.62 / 6.02 / 5.81 / 5.54 s | 5.27 / 5.42 / 5.22 / 5.25 / 5.06 s | median −8.6%, the sample sets separate |
| `eval_drives` | 11,582,182 | 7,068,996 | −39.0% |
| `eval_steps` | | | −0.2% |

39 other columns are identical: the queries, their verdicts and what they
unfold are the same, and the evaluator is entered less.

The prefix description on top of that, one run each (the column varies by
about 0.05% between runs of one binary, `scripts/timings`):

| | before | after | |
|---|---|---|---|
| `local_subst_nodes` | 25.88 M | 22.29 M | −13.9% |

The conversion columns do not move.

Both together, instructions inside the kernel gate (callgrind,
`--toggle-collect='heather_elab::stats::time_kernel*'`): 21,498 M to
18,169 M, −15.5%.

What a selection costs now, from the same profile: 491,000 selections make
1.5 M pending eliminations, three per selection, and `ValueArena::subject`
is 4.0% of the gate, of which a third is the table past the map's four
inline entries and a tenth the walk's stack. Not chased here.
