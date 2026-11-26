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

## Handoff (2026-11-26, end of the third session: the writes but the write-back)

Continue on branch `claude/ownership-checker-sound`. Everything is in
`lib/lang/ownership/sound.hthr`; design §23.11 says what was built this
session and why (read it, then §23.8–§23.10).

**Done**: the stages `Lit`, `Op`, `Read`, `Fresh`, `Take` (part, plain,
holder), `Death` (part, plain, holder), `View` (all four), `Write` to a plain
root, through a holder (`stage_write_hold`) and through a view
(`stage_write_view`, split in three), both cells each. Each concludes
`Stepped` from `none`. The decider law `Steps::apart_prefix` (a common prefix
decides nothing) is in `steps.hthr` with probes.

**The invariant now** (`Inv`): `sim` against `s.patched(e, m)` (a pending
view's value written up its chain only where its cell refers; level-count
fuel); clauses added this session: `wpar` (a view to write whose parent is a
view: that parent has one entry, to write), `uni` (an entry's cell and its
parent's both refer or are both copies), `pone` (pending entries are at one
level). `Inv::rekin` carries every clause but `sim` and `pone` across any map
of the entries that keeps all fields but `back` (`Kin`), into
`s.rekin(f, tl, wl)`; `Inv::unback` is its instance for a write.

**Lemmas ready for the write-back**: `Sel::put_back_path` (writing back what a
path reads changes nothing), `CSt::up_step`/`up_stop`/`up_nil` (one step of the
walk), `CSt::up_rekin` (the walk reads no written-back flag), `CSt::up_more`
(fuel past the level changes nothing), `CSt::up_sim` (the walk agrees with the
run, from `UpAt`), `Inv::store_rest`, `Value::get_store`.

**Next, in order**:

1. **`cfit`** (decided by the coordinating session: option (a)): a live entry
   whose parent's cell is a copy `Plain(d)` has its place fitting `d` at the
   run's words. Add it to `Inv` and to every builder (as `uni` was: push
   builders shift variables with `CSt::push_lvl`; `Inv::rekin` carries it;
   `set_cell` must show it for the written cell, from the licence's apartness
   of the write's path from each child's place: for a view parent the
   licence speaks of `parent.reg ++ xs` against `child.reg = parent.reg ++
   child.at`, so take the decider's verdict on the suffixes by
   `Steps::apart_prefix` and use `SelApart.fit2`). Opened by `Sim::place` in
   `Inv::push_view` (a copy view's parent is a copy, `uni`).
2. **The write-back stage** (`is_back(l, xs, lv)`: `ents(lv) = [ce]`,
   `ce.par = l`, `Steps::same(ce.at, xs)` so `unsteps(xs) = p.steps`; no
   licence residuals; the checker allows it while pending only if
   `ce.back = False`, `writes_back`). The state after is
   `s.backed(lv).wrote_to(l)`. It is a write through the parent at the
   child's place of what the child holds. Four cases, split from the start
   (an undivided stage hits the memory rail):
   - **referring, nothing pending**: the run stores `B` back (`put_back_path`:
     the child's reference reads the block at the parent's reference ++ its
     place), so every reference reads as before (`Value::get_store` with
     equal values); the meaning's parent becomes `write(at, e(child),
     e(parent))`, which is `e(parent)` by `put_back_path` again (the child's
     and parent's runs read the same block). Parent a holder: the state is
     `s` up to `touched`/`wrote` (`backed` is the identity on a written-back
     entry; `Inv::touch`). Parent a view: its entry becomes pending; walk from
     it with `up_sim` at `s` (the child is not an ancestor of the parent, so
     `UpAt.hv` holds) and finish with `Inv::rekin`.
   - **referring, pending** (`ce` is the pending entry: `pone` and
     `writes_back`): before, the patch is `up(s, e, lv)` (`patched`'s `find`
     gives an entry at `lv`, which is `ce`), which is `up(s, e3, l)` after
     one `up_step`, `e3` being the meaning's write-back. Parent a holder:
     that is `e3`, nothing is pending after. Parent a view: the patch after is
     `up(s3, e3, l, F)`, equal by `up_rekin` and `up_more`. The state after is
     a `rekin` of `s` (`backed(lv)` then `unback(l)`; fuse the two maps).
   - **plain chain, either**: the parent's cell is set (`Sel::put` fits by
     `cfit`); generalise `Inv::set_cell` from `none` to `s.patched(e, m) = e`
     (a copy's pending patch is the meaning itself), then `Inv::rekin`.
3. `Death` and `Take` of a view's root, then `Ret`, then the brief's item 3
   (`Call`, with its two decisions).

**Costs and traps found this session**:

- One undivided stage (`stage_write_view`) exhausted the 8 GiB rail though
  every lemma it cited was cheap (the next stages, the call especially, will
  be larger: split them from the start, statements spelling their objects
  out, no `let` in a statement); the `--timings` `<stem>.open.tsv` named it.
- A run killed at the rail prints no `error:` line: read the last line
  (`ok`) or the `.open.tsv`, never only grep for errors.
- `heather check --cache` replayed a stale image here and reported
  "0 declarations kernel-checked … ok" after edits; check without `--cache`
  (about 50 s for `sound.hthr`).
- A `let` whose type holds a lambda with `=` in its body needs the equation
  parenthesised (`λ y => (a = b)`).
- Lambdas inside `Inv`'s clauses bind `w`, `t`, `k`: a lemma's own parameters
  named so clash when its body is built by substitution.
- `scripts/fmt` (the Heather formatter, whitespace only) is what
  `scripts/fmt --check` gates; never `cargo fmt`.
- Do not edit `lib/` while `scripts/test` runs: the library gate reads it.
  This clone has no merge base with `origin/master`, so `--pr` runs every test
  file (about an hour).

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
- 2026-11-26 (third session): the writes through a holder and through a view (`131aef7`…`fcf1a1c`, split stage `stage_write_view`); proof-side invariant changes: `patched` only along a referring chain, `wpar`, `uni` (design §23.11). `scripts/test --pr` at the whitespace commit after them: `== suite: 4140 passed, 0 failed, 3 ignored ==`.
- 2026-11-26 (third session, end): `Steps::apart_prefix` and probes, `Inv.pone`, `Inv::rekin` (the flag-change lemmas generalised), `Sel::put_back_path`, `CSt::up_rekin`/`up_more`/`up_stop`; handoff rewritten at the write-back. `scripts/test --pr` at the commit before the handoff: `== suite: 4140 passed, 0 failed, 3 ignored ==`.
