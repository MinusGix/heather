---
title: Every conversion query built a neutral per variable of Γ, and rebuilt the identity environment wherever it read a prefix
status: closed
labels: [kernel,conversion,performance]
area: kernel
created: 2026-11-10
updated: 2026-11-10
---

Found in the whole-gate instruction profile taken after
[[conversion-closed-pair-memo]] (callgrind over every `time_kernel` scope of
a cold `docs/showcase/calc_parser.hthr`): `conv::Env::new_with` was a
twentieth of the kernel's instructions and did nothing but allocate.

## What it did

A conversion starts in the identity environment of Γ: entry `j` is the
neutral variable at level `j`. `value::Env::identity(arena, n)` built it as
a list, four allocations a variable (a neutral, its value, its closure, a
list cell), and it was called

- once per query, for all of Γ (`conv::Env::new_with`), whether or not the
  query read a variable: on the showcase 176,000 queries built 2.7 M
  entries, fifteen each;
- again in `Dom::var_type` for **every** read of a variable's type, for the
  prefix that type is scoped in;
- again in `eval_ity_syn` and `select_ity` whenever a description denoted at
  another Γ-length than the scope's.

Each call made new closures for the same variables, so two closures over
"the same" identity environment from two calls were different objects to
`Env::ptr_eq` and to every memo keyed by an environment's identity.

## What was built

- **An environment's list may stop short of its length** (`value::Env`).
  The entries it does not hold are the outermost ones and each is the
  neutral variable at its own level. So `Env::identity(n)` is a length:
  no allocation, and two of one length are one object.
- **One closure per variable per arena** (`ValueArena::var`), which is what
  `Env::lookup` answers for an entry the list does not hold and what a
  binder is opened with. `Env::push` of that closure onto an identity
  environment of that length is the next identity environment and not a
  cell, so there is one spelling of each.
- **The conversion scope carries no value environment.** `conv::Env::rho`
  was the identity environment of `gamma` by invariant, kept in step by
  `push_entry`, shifted (to itself) by `push_tele` and rebuilt by `in_ctx`.
  It is now `Env::rho()`, computed from Γ's length. `value_scope`, `fresh`
  and `var_at` are gone.
- `Env::lookup` takes the arena, since it may have to name a variable's
  closure; the identity checks (`clo_identity`, `tm_identity_fast`) and the
  withheld-evidence walk pass it. The elaborator's readback reads the
  identity prefix as variables directly (`Env::held`).

## What has to hold

- A held entry is never below an unheld one: cells are pushed innermost.
- An unheld entry at index `i` of an environment of length `n` is level
  `n - 1 - i`, whatever cells sit above it (unit tests in `value.rs`).
- No outer shift moves a local variable, so `value::shift::env` keeps the
  identity prefix and maps the held cells.
- More identity is only more reflexivity hits: two closures of one variable
  denote the same value. The differential suites
  (`tests/conv_differential.rs`, `eval_differential.rs`,
  `typing_differential.rs`) hold the verdicts.

## Log

- 2026-11-10: Built (2026-11-10). Cloud box, cold `docs/showcase/calc_parser.hthr`, width
  one, callgrind collecting inside `heather_elab::stats::time_kernel*`, on top
  of the lockstep walk and the one hasher ([[conversion-memo-hash-cost]]):

  | | kernel instructions |
  |---|---|
  | lockstep walk and closed pairs | 12,989.7 M |
  | with one hasher | 12,276.5 M (−5.5%) |
  | with identity environments as a length | 11,716.6 M (−4.6% more, −9.8% together) |

  `conv::Env::new_with` went from 4.24% of the first row to 0.22% of the last;
  `head_ity_cached` (the checker's `view`) from 4.5% to 3.3%. Counters on the
  same run: `eval_steps` 3,992,405 → 3,992,033 and `eval_drives` −0.06% (the
  shared variables are a few more reflexivity hits). `conv_misses`,
  `check_terms` and the query counts identical. (An earlier draft of this
  entry also credited a fall in `shift_global_nodes` and in peak memory to
  the change. Both vary run to run on one binary, being address-keyed, and
  the A/B below shows no move in either.)

  What a query still pays before it reads anything: eight arena chunks made
  and dropped (`ValueArena::new`, about a thousand instructions, and the
  drop of whatever it allocated, 5% of the last row).
- 2026-11-10: `scripts/perf ab --mode cold`, cloud box, quiet, width one, six
  interleaved samples, both changes together against the lockstep commit, on
  master's showcase at ab57366 (whose prelude now imports `ordered_field`, so
  its gate is larger than in the entry above):

  | | lockstep commit | with both |
  |---|---|---|
  | kernel gate | 6.97 / 6.61 / 6.72 / 6.57 / 6.49 / 6.45 s | 6.30 / 6.31 / 6.41 / 6.20 / 5.63 / 6.07 s |
  | `eval_steps` | 4,890,238 | 4,889,866 |
  | `eval_drives` | 11,585,126 | 11,582,182 |
  | `eval_delta_steps` | 688,596 | 688,509 |

  Median −4.8% and the sample sets separate. Wall (about 22 s) moves less
  than its spread. 37 columns identical; `syntax_eq_nodes` +0.02%;
  `local_subst_nodes`, `shift_global_nodes`, `subst_memo_hits` and peak
  growth differ between runs of either binary and show no move. So about
  half of the instruction saving is seen in seconds, which says what is left
  is bound more by memory than by instructions.

