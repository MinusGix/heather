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

## Handoff (2026-11-26, end of the eleventh session: step 0 landed, P5 begun)

Continue on branch `claude/ownership-checker-sound`. Read design §23.21
(this session) after §23.17–§23.20. The call's parts are at the end of
`lib/lang/ownership/sound.hthr`, after `LentFrame::call`. The coordinating
session's branch (`origin/claude/focused-darwin-it31c1`, design §24) is
merged in: put new §23 subsections **before the line `## 24.`**. Findings
from its soundness search arrive batched, each to be landed as its own
commit before continuing.

**Done this session:**
- **Step 0, the four rulings** (§23.21; suite green at da2faef):
  - A. `SafeAt`'s Done part concludes the results coded
    (`Dyn::Coded(…, (p.w(g, ds)).take(nres), sig.res_params())`); a
    primitive's by the world's law `Prog::Coded`, a premise of
    `CheckSound`; a body's from `Ret` (`RetOk.coded`, `Sim::coded_res`).
  - B. `Value::OwnedApart` (every owning result, fresh or a moved
    parameter) replaces `FreshApart`, proved at `Ret`
    (`Inv::owned_hold`, `ret_not_owned`, `ret_owned_apart`). The
    caller-side `CSt::holds` is gone. `CSt::returns` asks a parameter
    answered back to be held `AcOwn` (`CSt::returns_param`): a test that
    never refuses under `Sig::ok`, standing in for an invariant.
  - B′/C. **`Sig::ok`** (checker.hthr), tested in `Func::verdict` and at
    each call: `OParam` names a taken parameter, `OView` a read one; a
    result's code is what its origin gives (the parameter's, or the code at
    the view's steps by `Shape::steps_ok`); a view's steps name parameters
    and earlier results only (the telescope).
  - D. `CSt::result`'s `OView` case runs `atoms_ok` on the levels its
    region names.
  - `Body::stage_ret` now takes `ld: Lendable`, `sok: Sig::ok` and `cd`
    (the `Ret` code check).
- **P5 begun**: `Ref::Grown` (how a binding leaves the roots: all kept, a
  new one the block of the result that owns it) and
  **`Inv::bind_fresh_result`**: a fresh result bound, all three kinds
  (plain value; holder with no root; holder of the callee's block), from
  per-result facts `SafeAt` gives.
- **`Inv.hown`** (`CSt::HOwn`, a gap in the proof's own invariant, §23.21):
  a level holding an object to own whose object has a root has an owned
  cell; added at all fourteen `Inv` builders (`hown_push`, `hown_sub`,
  `hown_gone`, `Cell::args_owned`; `push_hold` takes `hwn`).

**Next, in this order:**
0. **The coordinating session's run ruling (2026-11-26), its own step,
   before P6** (it changes what P6 is built on; two other sessions wait to
   merge it). The principle: **level 2's run is the machine's reading**;
   where the run transports, stores or allows a store the machine does not,
   the run changes once and `check_sound` says it of every checked program.
   For each item: probes by evaluation in `run_tests` first (a program
   whose run differs before and after, and one whose run does not), then
   the proof repaired. If any of 1–3 costs more in the proved stages than
   it reads, stop and tell the coordinating session with counts. Report
   when landed, with the suite line.
   1. **A referring written parameter is not transported back**: after a
      call, the caller's slot for a written parameter whose argument refers
      is the argument's own cell, whatever the callee's `Ret` listed; a
      plain one's value comes back as now. `Answer` and `SafeAt`'s `Written`
      keep their shape. For P6 a simplification: the slot's cell is the
      argument's by the run.
   2. **The run's `Back` of a cell that refers is the identity** (the writes
      went through in place; the meaning does the put). A plain copy's
      `Back` stores as now. The write-back stage's referring cases lose
      their store; say which of the four cases change.
   3. **A store is stuck outside what the activation may change**: a store
      through a reference is stuck unless the reference is under one of the
      activation's references lent to change (`Value::lent` of the entry's
      arguments) or its block was made since the activation's entry. The
      invariant has both as indices (`lent`, `h0`) and `owned` says a
      changing object's root is in one or past the other, so each write
      stage gains one obligation it can meet. Carry the two as parameters of
      the body's run, not fields of `Mach`, unless a cleaner place shows.
      (`Heap::Frame` says a block not lent keeps its value, not that it was
      never stored to; the bytes level needs the second.)
   4. **A statement reading a place's length as a word** (the body has none;
      `issues/ownership-branch-on-object-length.md`): checker, meaning, run
      and stage as for `Read` of a plain part, through the sequence
      instance's own length. Not necessarily in the commit of 1–3, but
      before the body induction. **Send the coordinating session its name
      and shape in one line before building.**
   Do not edit `lib/lang/ownership/sequences.hthr` until the coordinating
   session says (the slice session is adding an instance at its end).
1. **P5, the moved result** (finish P5 first only if it is cheaper than
   rebuilding it on the changed run; the ruling says "finish the piece of P5
   you are in, then do this", and the eleventh session stopped at a piece's
   end): `Inv::bind_param_result` beside
   `bind_fresh_result`, on `CSt::result` at `OParam(i)` (decided by the
   parameter's code since 416d51b):
   - plain code: the argument was passed by value (`Lendable.plain`), so
     `ViewIs` gives a plain cell: `push_plain`;
   - moving, `s0.role(l) = KHold(o, AcOwn)` at the argument's level, two
     cases by the object's root before the call:
     - `root(o) = Some(r)`: the holder's cell is owned (`Inv.hown`, new
       this session) and refers to `r` (`href`), so `Cell::pass` handed `r`
       over and `ViewIs` says the result is `Refer(r)`, owned by
       `Cell::results`: `bind_moved` (generalise it to a cell `c` with
       `c.v = Refer(r)`, `c.own = True`; record eta holds by `refl`);
     - `root(o) = None`: the cell is plain (`refs`), so is the result:
       `push_hold` with `rf`/`hrf`/`hwn` vacuous.
   - The facts about `o` at the binding state (`o < s.nobj`, no level
     holding it, its root alone in its block, lent or made, apart) are the
     fold's: the moved holder is gone after the lends (`CSt::lend_take`); no
     other old level holds `o` (`one`); an earlier result holding `o` would
     be a second owning result in `r.b` (`OwnedApart`, both `Refer(r)` by
     `ViewIs`); an earlier fresh result's block is at or past the call's
     heap length, the argument's below it (`Lendable.live`).
2. **P5, the view result**: from `Inv::push_view`, its region's levels
   plain by `atoms_ok` (ruling D) and bound before it (the telescope).
3. **P5, the fold** over `CSt::results` and `Cell::results`/`Dyn::take_n`
   (split lemmas: the first `nres` cells are the results', the rest the
   slots'). Carry, from the pre-call `s`: the same `na`; the old levels'
   roles as after the lends; the old views kept, new entries at new levels,
   `Reading` and back; `Ref::Grown` step by step, which with `OwnedApart`
   discharges the next fresh result's `fr`. `SafeAt` gives per result:
   `ReadAll` (the cell reads `d`), `Coded` (`d.code = r.code`), `Views`
   (`ViewIs`), the cell's `own` by `Cell::results` (`owns && refers`).
4. P6 by peeling (§23.20: `BackAt.nk` weakened to pending children, through
   `step_keeps` and `CSt::noanc`), P7–P9, then report to the coordinating
   session.

**Traps found this session:**
- `fn Roots::Grown` fails: a member needs an existing owner type
  (`Ref::Grown`).
- A `let` typed `(match … ) = True` must be parenthesised whole:
  `let h: ((match …) = True) = …`.
- A value `Cell(Refer(Ref(b, Nil)), True)` in a type cannot infer `tys`
  even under `let x: (… = c)`; bind `let mk = λ (u: Value(tys)) (z: Bool) =>
  Cell(u, z)` and a typed `let rq0: Value(tys) = Refer(…)`.
- `j(eq, P, P(a))` rewrites forward to `P(b)`: to get a property of `c.v`
  from one of `Refer(q)` use `sym(cq)`.
- `git checkout <file>` to clean a scratch edit reverts all of the file's
  work: copy scratch files to the scratchpad instead.
- The full `sound.hthr` check **without** `--cache` takes about three
  minutes; with the cache after an edit it took ten or more. Check without
  it; `--timings` with `.open.tsv` names the item running.
- Before naming a lemma, grep: `CSt::role_of_own` and `Cell::args_own`
  already existed (a duplicate name is an error, not a shadow).

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
- 2026-11-26: `scripts/test --pr` at `f278a42` (items 2, 3, P4's frame; `de9bc47` after it is docs and this issue): `== suite: 4140 passed, 0 failed, 3 ignored ==`. Probes `fresh_and_its_view_refused`, `fresh_and_its_view_fresh_refused` (one made object answered as owner and as a view under it: refused, a returned view must be of a parameter).
- 2026-11-26 (ninth session): P4 built but for the swap and the assembly: the lends (`Inv::lends`), the frame's premises (`Inv::call_un`, `Inv::call_lk`), `Inv::heap_rest`, the licence across the lends (`CSt::license_eq`, `Inv::view_off_by`), the puts (`Inv::put_arg`, `Inv::puts`, `Inv::put_at_arg`), the swap's block and list lemmas; design §23.19. `scripts/test --pr` at `0ba781f`: `== suite: 4139 passed, 1 failed, 3 ignored ==`, the failure `native_linked.rs` (`linked_exports_are_what_the_compiler_emits`, the sha256 certificate check), which this branch does not touch (only `sound.hthr` changed); rerun alone (`scripts/test --pr --test native_linked`): `== suite: 2 passed, 0 failed, 0 ignored ==`, a flake under the suite's load beside the library gate. `f535c5a` (list lemmas) after it is checked by `heather check --cache` only.
- 2026-11-26 (tenth session): P4 complete (`Inv::call_swap` over `Heap::call_block` and `Inv::call_untaken`; `Inv::call_after`); roots an index of `Inv`/`Stepped`; `Inv::fresh` as growth then `Inv::bind_fresh`; P5's builders `bind_fresh_plain`, `bind_moved`; checker fix: a moved parameter answered twice refused (`CSt::holds`, `twice_param_refused`). Issues `native-linked-gate-fails-under-load` (a resource kill, not a nondeterminism) and `ownership-sound-consolidate` filed; three questions for the coordinating session (results' codes, forward atoms, non-plain atoms in a result view's region). Design §23.20. `scripts/test --pr` at 42e9bfd: `== suite: 4140 passed, 0 failed, 3 ignored ==`.
- 2026-11-26 (tenth session, after the rulings): native_linked prints a failed compile's exit status (a5405d9, issue closed); the callee's `Ret` answers an owned object once, `twice_param_refused` at the callee (e1f701d); rulings recorded in §23.20 and the handoff. `scripts/test --pr` at dfdc63c, clean tree, nothing else running: `== suite: 4140 passed, 0 failed, 3 ignored ==`.
- 2026-11-26 (eleventh session): step 0, the four rulings (§23.21): results coded (`Prog::Coded`), owning results apart (`Value::OwnedApart`), `Sig::ok` (modes, codes by origin, the telescope), atoms plain at a view result; `scripts/test --pr` at da2faef: `== suite: 4140 passed, 0 failed, 3 ignored ==` (the run before, at dde16c0, `4138 passed, 2 failed`: `scripts/fmt` on checker_tests, and native_linked's compile killed by signal 9 under the suite's own load, passing on the rerun). Then `Sig::ok`'s code clause and P5's `Inv::bind_fresh_result`: `--pr` at 6af0289: `== suite: 4140 passed, 0 failed, 3 ignored ==`. Merged the coordinating branch (design §24).
- 2026-11-26 (eleventh session, later): `Inv.hown` at every builder (daa35a1); `sound.hthr` checked whole without the cache. Handoff rewritten.
- 2026-11-26: `scripts/test --pr` at 66a7bf2 (after `Inv.hown`): `== suite: 4140 passed, 0 failed, 3 ignored ==`. The coordinating session's run ruling recorded as Next item 0.
