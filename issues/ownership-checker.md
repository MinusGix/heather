---
title: Ownership: the run, the checker and check_sound over the interfaces (first fragment: no holes)
status: open
labels: [ownership,library]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-26
---

The ownership checker built once over the fixed interfaces (`docs/language/ownership-design.md` §21, §22): the run, the checker and `check_sound`, for objects whose nested parts are plain (no holes). Within that fragment: several objects per function, places with steps (fields, elements, windows through the three sequence instances), views to read and to write with eager write-back, calls with modes and returned views, `fresh` with its value, joins (packed and with a returning arm), a function with a `Jump`, calls of itself and of others on fuel. §23 of the design doc says what was built.

## Scope, in order, each landed and pushed before the next

1. **The run** (`lib/lang/ownership/run.hthr`): level 2's reading of a body on fuel, answering `Ran`; probes by evaluation (`lib/_tests/lang/ownership/run_tests.hthr`).
2. **The checker**, an inhabitant of `Checker`: one forward pass, the licence by `Steps::apart`, the residuals, the join as the meet, the code check folded in; the experiments' programs restated as verdicts; measured linear at doubling sizes.
3. **`check_sound` for straight-line bodies and calls**: the invariant (the experiment's `Sim` its ancestor), one stage lemma per statement kind, `SafeAt` relative to callees at less fuel.
4. **Joins, loops and recursion**: the join's case split, the `Jump`, the induction on fuel giving `Safety`, `Done` from `need`; `CheckSound` inhabited for this fragment.
5. **Retire the experiments** (`call_check.hthr`, `place_check.hthr` and their tests) and close the issues this build answers.

Items 1 and 2 are definitions and evaluation; item 3 waits for the coordinating session's reading of their report.

## What it assumes

- [[ownership-interfaces]]: the interfaces, fixed; a change to them goes to the coordinating session with the smallest declaration that shows it.
- [[ownership-pin-after-join]], [[ownership-world-depth-zero-postconditions]], [[ownership-branch-on-object-length]], [[ownership-write-bounds]], [[ownership-checker-several-objects]]: requirements on this build, closed by it.

## Done when

`CheckSound` has an inhabitant for the fragment, the experiments' programs are probes or theorems of the real modules, and the experiment modules are gone.

## Handoff (2026-11-26, third session: item 2 of its brief, the writes, in progress)

Continue on branch `claude/ownership-checker-sound`. Everything is in
`lib/lang/ownership/sound.hthr`; design §23.11 says what was built this
session and why (read it, then §23.8–§23.10).

**Done**: the stages `Lit`, `Op`, `Read`, `Fresh`, `Take` (part, plain,
holder), `Death` (part, plain, holder), `View` (all four), `Write` to a plain
root (`stage_write_plain`), through a holder (`stage_write_hold`, both
cells) and through a view (`stage_write_view`, both cells, the pending chain
walked by `CSt::up_sim`). Each concludes `Stepped` from `none`.

**The invariant as it now stands** (`Inv`): `sim` is against
`s.patched(e, m)`, which writes a pending view's value up its chain only
where the view's cell refers, by level-count fuel; new clauses `wpar` (a
live view to write whose parent is a view has that parent with one entry, to
write) and `uni` (an entry's cell and its parent's both refer or are both
copies). `Inv::touch` is the identity; `Inv::unback` carries every clause
but `sim` to a state where one view's entry is no longer written back.

**Next, in order**:

1. **The write-back** (`is_back(l, xs, lv)`: `ents(lv) = [ce]`, `ce.par = l`,
   `ce.at` the written steps; no licence residuals). It is a write through
   the parent `l` at `ce.at` of the child's value. Two clauses first:
   - `pone` (all pending entries are at one level): `patched` follows the
     first pending entry `find` returns, and the stage needs it to be `ce`.
     Every builder proves it from its new state's `none`
     (`CSt::pone_none`); `Inv::unback` from `none` before (only the written
     view's entries change); the write-back keeps it (the child is written
     back, only the parent's entry becomes pending).
   - **A fit for copies** (asked of the coordinating session, see below): a
     plain chain's write-back runs `Sel::put` into the parent's cell, stuck
     unless the child's place fits the parent's value, and nothing records
     that for a copy (for a referring chain it follows from the child's
     reference reading the block).
   Then: referring chain: the block is unchanged (`put_back` along the
   child's path: the child's reference reads what the block holds there),
   the meaning's parent becomes what the run's parent reads (the walk's
   first step, `CSt::up_step`); before, the patch is `up(s, e, lv)`, after,
   `up(s3, e3, l)` (parent a view) or `e3` (a holder), so the lemma to add
   is `up`'s independence of the written-back flags (as `anc_unback`) and
   of fuel past the chain (as `anc_more`). Plain chain: the parent's cell
   set, `Inv::set_cell` generalised from `none` to `patched = e` (a copy's
   pending patch is the meaning itself).
2. `Death` and `Take` of a view's root (`Death` of a view written back:
   `Inv::gone` with the view's entries removed from `views`; no entry has it
   as parent, `has_children`), and `Ret`.
3. Item 3 of the brief (`Call`), with the two decisions recorded there.

**Costs and traps found this session**:

- One undivided stage (`stage_write_view`) exhausted the 8 GiB rail though
  each lemma it used checked in well under a second; the `--timings`
  `<stem>.open.tsv` named it. Split into lemmas whose statements spell their
  objects out (no `let` in a statement), it checks in under a second.
- A run that dies at the rail prints no `error:` line: read the last line
  (`ok`) or the `.open.tsv`, never only grep for errors.
- `heather check --cache` here replayed a stale image and reported
  "0 declarations kernel-checked … ok" after edits; check without `--cache`
  (about 50 s for `sound.hthr`).
- A `let` whose type holds a lambda with `=` in its body needs the equation
  parenthesised (`λ y => (a = b)`), or the parser stops at the `=`.
- `scripts/fmt` (the Heather formatter, whitespace only) is what
  `scripts/fmt --check` gates; run it on the file, never `cargo fmt`.
- Do not edit `lib/` while `scripts/test` runs: the library gate reads it.

## Log

- 2026-11-25: Items 1 and 2 landed (`d374128`, `7724f92`). The run (`run.hthr`): level 2's reading over a heap, primitives native, stuck at an unfit selection or a dead or dangling block; each pinned function of `body_tests` answers its meaning at closed arguments. The checker (`checker.hthr`): roles per variable in the meaning's shape, a table of live views with parents and write-back state, the licence by `Steps::apart` (a view meets only the views opened through it), calls binding written parameters as views to write of the argument lent, the meet; the experiments' programs restated with verdicts by `refl` (`checker_tests.hthr`), every refusal refused and coded. Measured linear (§23.6): straight loans 131k to 836k, joins 44.5k to 262k, calls 104k to 627k at N = 8 to 48. One interface change made (a call binds its written parameters, `Stmt::code_step`); the rest proposed in §23.4, item 3 waits on them. Item 1's own `--pr` run (`== suite: 4139 passed, 1 failed, 3 ignored ==`) failed only on `library.rs` checking the untracked, in-progress `checker_tests.hthr` of item 2, since fixed.
- 2026-11-25: Items 1 and 2 verified: `scripts/test --pr` at `7724f92` (with `66c2d1d`, docs): `== suite: 4140 passed, 0 failed, 3 ignored ==`. Reported to the coordinating session; item 3 waits on its decisions on §23.4.
- 2026-11-26: Item 3 step 0 (`72734c8`): the interfaces as the coordinating session decided (primitives in `Prog`, the defined run, `SafeAt` under the precondition and `Lendable` inputs, the `Frame`, `ViewIs`, `Written` and `ReadAll` corrections, pins in `CheckSound`, views over result words, copy by sharing class, the sequences' `pre_inside`/`inside_len`). `scripts/test --pr`: `== suite: 4140 passed, 0 failed, 3 ignored ==`.
- 2026-11-26: Item 3, the checker's eager write-back and `check_sound`'s first lemmas (`98fe0d1`): `scripts/test --pr`: `== suite: 4140 passed, 0 failed, 3 ignored ==`.
- 2026-11-26: `put_back` and `Lendable.arity` (`79edd30`): `scripts/test --pr`: `== suite: 4140 passed, 0 failed, 3 ignored ==`.
- 2026-11-26: Item 3: `Dyn::Coded` added to `SafeAt` and `CheckSound`'s premise (the coordinating session's decision, after the `get_x` witness, §23.7); the `Read` stage, the invariant `Inv` stated whole, and its entry `Inv::start` proved. Handoff above.
- 2026-11-26: `a4b01b5` and `30f7de1` (the `Read` stage, `Inv`, `Dyn::Coded`, `Inv::start`, the handoff): `scripts/test --pr` at `30f7de1`: `== suite: 4140 passed, 0 failed, 3 ignored ==`.
- 2026-11-26 (second session, branch `claude/ownership-checker-sound`): items 1 and 2 of the coordinating session's list (`366636f`): `Heap::Frame` exempts only blocks lent to a parameter that changes them (`Value::lends` takes the parameters); `Lendable.whole` (a taken object is a whole block no other argument refers to; without it `CheckSound` was false, design §23.8); the code conditions in the checker's pass (`Stmt::code_ok`, `Why`, `Func::refusal`; `Func::coded`, `CEnv`, `CheckRefusesIllCoded` gone; `refusals_owned` replaces `refusals_coded`); a plain variable a live region reads does not die; `Inv` per object over `root: Nat → Option<Ref>` with `own`, `one`, `words`; `Inv::start` re-proved; `Inv::push_plain`; the `Lit`, `Op` and `Read` stages conclude the whole invariant. `scripts/test --pr` at `366636f`: `== suite: 4140 passed, 0 failed, 3 ignored ==`.
- 2026-11-26: item 3 in progress: stages `Fresh`, `Take` (part, plain, holder), `Death` (part, plain, holder), `View` (plain; to read and to write, of a holder and of a view), with `Inv::push_hold`, `Inv::push_view`, `Inv::gone`, `Inv::kill` and the licence's soundness (`CSt::license_sound`, `Inv::lic_apart`); the invariant gained `young`, `held`, `vents`, `bare`, `chain`, `excl`; the checker's `anc_of` takes the level count as fuel and follows every entry of a parent; `CSt::set` restructured (design §23.9).
- 2026-11-26: `b771b8e` (the `Fresh`, `Take`, `Death` and `View` stages): `scripts/test --pr`: `== suite: 4140 passed, 0 failed, 3 ignored ==`.
- 2026-11-26: item 3, the write's groundwork: `Sel::Apart` keeps fits (`SelApart`, model law `fits_over`, `Steps::apart_fit`), `CSt::write_last` split out, `Stmt::stage_write_plain` and the lemmas the holder and view writes use (design §23.10).
- 2026-11-26: `187e2f5` (apartness keeps fits, the plain write): `scripts/test --pr`: `== suite: 4140 passed, 0 failed, 3 ignored ==`. Handoff rewritten.
