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

## Handoff (2026-11-26, end of the sixth session: D2 done, then Like and the call)

Continue on branch `claude/ownership-checker-sound`. Everything is in
`lib/lang/ownership/sound.hthr`. Read design §23.15 (this session) first,
then §23.13 and §23.14. The coordinating session's order: item 2 (`Inv::back_like`
and `Like`'s step per statement kind), item 3 (the call, P1 to P9 below),
item 4 (`SafeAt` for a body with no join and no `Jump`), then report.

**Done this session** (D2, item 1 of the coordinator's list):
- **The patch is a fold over levels** (`CSt::patched` = `CSt::pfold`, the
  highest level first; `CSt::pend_in` marks a level on a pending chain whose
  cells refer, through `anc_of`; `CSt::wstep` writes the level's entry to
  write into its parent). With one chain it is the walk
  (`CSt::pfold_walk`, over `Walkable`), so every lemma over `CSt::up`
  stands. The designed disjointness was false (`nested_two_checked`), and a
  fold of walks needed like-ness of every link; both are explained in §23.15.
- **The commuting lemma** is `CSt::patched_back` (record `BackAt`, built by
  `Stmt::back_at`): a write-back with other chains pending keeps the patch.
  It uses `sib`, `uni`, `Walkable`, `words`, and `Stmt::back_nk` (a view
  written back has no live child to write, from the write's read licence;
  `nested_two_late_refused`).
- **The write-back stages** are restated for several chains: `ref_pend` over
  `patched_back`; `ref_none` unchanged (nothing pending); the copy write-back
  over `CSt::patched_copy_set` and `CSt::patched_reback_copy`, with
  `Inv::set_cell` now over the patched meaning (`px`, `pn2`). `Inv.pone` and
  its lemmas are gone. Tools for the call's slots (P6): `CSt::pfold_set` (the
  patch commutes with setting a variable on no referring chain),
  `CSt::pfold_plain`, `CSt::pend_refers`, `CSt::pfold_agree` (the patch
  keeps plain variables) and `Inv::at_sels`.

**Next: item 2**, `Like`'s steps. `Like.pend` (a pending view is like its
place in its parent) is what a write-back's like-ness needs where the child
is pending; `Inv::back_like` is for the rest. With several chains now
pending, check that `Like.pend` is kept by a write-back whose parent was
already pending: the parent's new meaning has the child at its place, and
its own place in its parent is unchanged.

**Then the call**, in this order:
- **P1** `Inv::pass`: `pass_all` succeeds and `ReadAll` holds of the passed
  values; `Coded` from the code check; `pres` from `RPre`.
- **P2** `Inv::lendable`, one lemma per clause. `apart` for one object comes
  through `apart_args` and the licence chain generalised from
  `Inv::lic_apart`.
- **P3** `Call::callee`: the callee's `SafeAt` at the fuel below. A primitive
  is `Call::prim`.
- **P4** `Inv::call_frame`: from the callee's place frame.
- **P5** `Inv::bind_results`: fresh results in distinct blocks;
  `returns_all` refusing one object twice is already decided.
- **P6** `Inv::bind_slots`: several pending slots. Before the call nothing
  is pending (the checker allows only write-backs while anything is), so the
  patch after is the fold over the slots' chains alone. Each slot is a view
  at `Nil` of its argument. A slot whose argument is a copy is on no
  referring chain (`pfold_plain`). Where arguments meet under one view, the
  places are apart by `apart_args`, which is `sib` for the slots' parents.
- **P7**: the moved arguments.
- **P8** `Like::call`.
- **P9** `Stmt::stage_call`, split into run, invariant and `Like`.

**Traps found this session:**
- A recursive theorem's recursive call must be at the predecessor the match
  bound (`j1`), not at an equal variable (`c` with `j1 = c`); rewrite the
  other way.
- `Nil` in a type position needs its argument: `Nil<Step>()`.
- A `let` bound to a lambda whose binder is used in `Dyn::write` needs its
  binder typed (`λ (d: Dyn(tys)) => …`).
- Declarations must come before use: the write-back block now sits after
  `CSt::patched_back`, and `ent_mem`, `ent_only`, `anc_not` and
  `member_foldr_false` were moved up.
- `scripts/test --pr` reads the working tree. Editing `lib/` while it runs
  fails its fmt test spuriously.

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
- 2026-11-26 (fourth session): `cfit` (with like-ness) and `sib` through every builder; the licence's soundness after a common prefix (`6f6c923`). `scripts/test --pr` at `6f6c923`: `== suite: 4140 passed, 0 failed, 3 ignored ==`.
- 2026-11-26: the write-back stage in its four cases; `Inv::set_cell` over a patch that is the meaning (`b52c3a6`). `scripts/test --pr` at `b52c3a6`: `== suite: 4140 passed, 0 failed, 3 ignored ==`.
- 2026-11-26: the death and the take of a view (`62a8529`, `ea53353`); handoff rewritten at `Ret`. `scripts/test --pr` at `ea53353`: `== suite: 4140 passed, 0 failed, 3 ignored ==`.
- 2026-11-26 (fifth session): the `sig_atom` and `returns` checker fixes; the measure for measured functions only (`WMeasure`); `ViewIs` plain where the argument was, `Written` the slot as the argument, `Heap::Frame` by place; `Inv` gains `args`, `href`, `made`, `nbase`; `Stepped.kept`; `Like` with its start and steps; the `Ret` stage (`Body::stage_ret`). Design §23.13, §23.14. Handoff rewritten at D2.
- 2026-11-26: `scripts/test --pr` at `1dcfe82` (the last code commit of the fifth session; `906374b` after it is docs and this issue only): `== suite: 4140 passed, 0 failed, 3 ignored ==`.
- 2026-11-26 (sixth session): D2, several pending chains. `patched` is a fold over levels (`106cfce`); `CSt::patched_back`, the write-back keeping the patch with other chains pending, and the probes `nested_two_checked` and `nested_two_late_refused` (`d40e77b`); the write-back stages restated, `Inv.pone` dropped, and `Stmt::back_nk` (`947121b`). Design §23.15. `scripts/test --pr` at `947121b`: `== suite: 4140 passed, 0 failed, 3 ignored ==`. Handoff rewritten at item 2.
