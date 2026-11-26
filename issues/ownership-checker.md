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

## Handoff (2026-11-26, end of the eighth session: the frame restated, D and the bare fresh block, P4's frame)

Continue on branch `claude/ownership-checker-sound`. Read design §23.17 (`SafeAt`
clause by clause) and §23.18 (this session: the frame as the lens equation,
`LentFrame`, P4's frame) first. Everything is in `lib/lang/ownership/sound.hthr`
(the lens lemmas after the moved selection lemmas, before `// The invariant`;
the call's parts at the end) and `verdict.hthr` (the interface).

**Done this session (the coordinating session's items 1–3, and P4's frame):**
- Item 1. `Heap::Frame` restated as §18.3's lens equation: a fold of puts
  (`Sel::put_ref`, `Sel::put_lent`, list order; `Sel::put_ref_comm`), live
  after at every block live before that nothing was lent whole. Derived:
  `Heap::frame_apart` (a path apart from every lent reference reads and fits
  as before), `Heap::frame_whole` (a block lent nothing is its value before).
  `Inv.frame` is a `LentFrame`: `eq` (the equation from `h0`), `pw` (the lent
  references pairwise apart, `Ref::Pairwise`, from `Lendable.apart` by
  `Value::lent_pairwise`), `like` (at a block not lent whole, each lent
  reference fits the entry and reads now its code and length: a gap in the
  proof's own invariant, fixed; §23.18 says why). `Inv::start` takes
  `StrsLaws`. `Inv::store_rest` (and `Inv::store`) take the store as `ff`
  applied at the root's selections keeping code and length; the frame is
  `Inv::store_frame` (`Sel::put_lent_store` over `Sel::put_lent_set`).
  No statement kind lacked the like-ness: no finding.
- Items 2, 3. `Value::ViewIs`/`Views` take the heap after; a referring fresh
  result's block is `Heap::Bare` (live, no holes; this fragment's clause).
  `Value::FreshApart` beside `Views` in `SafeAt` and `RetOk`: two fresh
  results are in different blocks (`Inv::ret_fresh_apart` from `one`, `made`,
  `apart`; `Sel::apart_nil_nil`). **Checker defect found and fixed**: `CSt::ret`
  accepted `Ret([x, x])` against two fresh results, one owned object as two;
  now `CSt::fresh_once` refuses it (`fresh_twice_refused`,
  `fresh_two_checked`). §23.17 has both programs.
- P4's frame (`LentFrame::call`, over `Sel::put_lent_compose`): the caller's
  `LentFrame` after a call, from its own before, the callee's `Heap::Frame`,
  `un` (each callee reference lent to change into a block live at entry
  extends a caller lent reference) and `lk` (each reads after the code and
  length it read before).

**Next, in this order (items 4–7 of the coordinating session's list):**
1. **P4, the rest**: `Inv(nl.st, e_upd, Mach(a.heap, m.env, a.io), h0, lent)`
   with nothing pending.
   - The state after the lends: `CSt::lend` changes only a moved owned holder
     (`set(l, KGone)`, no views of it); an `Inv` at `nl.st` on the same machine
     and meaning is `Inv::gone`'s shape (the root stays; the callee owns the
     block now, so `own`/`one` lose nothing). `Thin`/`CSt::lend_all_at` (P2)
     walk the lends.
   - `un` for `LentFrame::call`: a lent-to-change argument's reference is its
     object's root narrowed (`ArgAt`, `Inv::arg_at`), the object `Changes`, so
     `owned` puts the root in `lent` or past `h0`; for a block live at entry
     it is in `lent` (`made`/`inheap` exclude the other). A taken argument is
     a whole owned root (`own`), so never under a part-lent block.
   - `lk`: `Value::Written` (slot = the argument's reference, its meaning
     after `Dyn::Fits` the argument's) with `ReadAll` at both heaps; no holes
     (`Heap::Stays`, `Inv.bare`) so `Obj::read` is the block's value.
   - `Sim` at `e_upd` (each written argument's chain written up with its
     slot's value, as `CSt::patched` will write it up once P6 marks the slots
     pending): a live variable is the lent argument (`Written`, `ReadAll`), an
     ancestor on its write chain (`wpar`; the equation), or apart from every
     callee reference into its block (licence at the lend: `CSt::lend` ByWrite
     is `write_at(l, Nil)`, which meets every live entry of a lent holder's
     object and every descendant of a lent view; `excl`/`apart` for the rest)
     and reads as before (`Heap::frame_apart`).
   - `Heap::Kept` gives `grows`, `inheap`, `stays` (`Heap::stays_trans`), and
     `bare` at old blocks (`Heap::Stays`' no-holes part).
   Then report P4 to the coordinating session.
2. P5–P9 as planned (the old Handoff's item 3, unchanged): results pushed
   (generalise `Inv::fresh` to a given block past every root; `Heap::Bare` and
   `FreshApart` now give `bare` and `own` for the new roots), slots pushed as
   written-back views then `Inv::rekin`, the moved argument (P7), `Like` at the
   call with `CallFits` (P8), the stage split (P9). Report after P9.
3. Items 5–7 of the coordinating session's list (the body induction without
   joins, joins and `Jump`, the walk retired).

**Traps found this session:**
- `SafeAt`'s `Done` part now ends `Kept ∧ (Views ∧ FreshApart)`; anything
  destructuring it positionally moves.
- A worktree's `scripts/fmt` builds its own `target/` from scratch; run
  `/home/user/heather/target/release/heather fmt --limits dev,cpu=300 --check lib`
  there instead, and give the worktree its own `HEATHER_CACHE_DIR`.
- `Sel::Apart` is semantic: two "apart" paths may be degenerate (one reads a
  constant). Every lemma over the fold uses only the laws, never syntactic
  disjointness; the composition needs the callee's references under the
  caller's, not apart from each other.
- The lens laws (`over_over`, `over_at`) hold only where what is put keeps the
  code and length there (a window's length): every set-set step carries a
  `Sel::LikeAt`.

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
- 2026-11-26 (seventh session): item 1 of the coordinating session's list: `Inv::back_like`; `Like.pend` over every view to write on a pending chain (`CSt::on_chain`; the gap and its probe `back_under_checked`, design §23.16); `Like`'s steps for every statement kind but the call (`Like::plain`, `fresh`, `take_hold`, `take_view`, `view`, `death`, `death_view`, `Like::stage_write`, `Like::stage_back`). `scripts/test --pr` at `54e6502`: `== suite: 4140 passed, 0 failed, 3 ignored ==`.
- 2026-11-26 (seventh session): the call's P1–P3 (`Sim::pass_all`, `Inv::lendable` with a lemma per clause, `Run::calls_body`, `Run::calls_prim`) and the agreed interface additions (A) a plain written parameter comes back plain, (B, C) `Heap::Kept` (`1adccde`). `scripts/test --pr` at `1adccde`: `== suite: 4140 passed, 0 failed, 3 ignored ==`. Then probes `lend_plain_back_checked`, `lend_under_checked`, design §23.17 (`SafeAt` clause by clause), handoff at the lens-equation frame.
- 2026-11-26 (eighth session): item 1, the frame as §18.3's lens equation (`00e9be0`): `Heap::Frame` restated as a fold of puts, `Inv.frame` a `LentFrame` (equation, pairwise, like), `Inv::store_frame`. `scripts/test --pr` at `00e9be0`: `== suite: 4140 passed, 0 failed, 3 ignored ==`.
- 2026-11-26 (eighth session): items 2 and 3 (`0d165b3`): `Heap::Bare` in the fresh case of `Value::ViewIs`, `Value::FreshApart` in `SafeAt`; checker defect `Ret([x, x])` fixed (`CSt::fresh_once`). P4's frame (`f278a42`): `LentFrame::call` over `Sel::put_lent_compose`. Handoff rewritten.
