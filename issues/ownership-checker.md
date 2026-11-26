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

## Handoff (2026-11-26, end of the seventh session: item 1 done, the call P1–P3 done, the frame to restate)

Continue on branch `claude/ownership-checker-sound`. Everything is in
`lib/lang/ownership/sound.hthr` (the call's parts at its end) and
`verdict.hthr` (the interface). Read design §23.16 and §23.17 (this session)
first: §23.17 is `SafeAt` clause by clause with the program that forced each
clause; the coordinating session reviews it before the body induction.

**Done this session:**
- Item 1. `Inv::back_like`; `Like.pend` over every view to write on a pending
  chain (`CSt::on_chain`; probe `back_under_checked`); `Like`'s step per
  statement kind but the call (`Like::plain`, `fresh`, `take_hold`,
  `take_view`, `view`, `death`, `death_view`, `Like::stage_write`,
  `Like::stage_back`, over `Like::rekin_write` and `Like::pp_write`).
- P1: `Sim::pass_all` (pass_all succeeds; `ReadAll` and `get_all` of the
  passed values; the state after the lends still agrees), `Sim::coded_args`,
  `CSt::lend_all_live`.
- P2: `Inv::lendable`, one lemma per clause (`lend_live`, `lend_plain`,
  `lend_apart`, `lend_whole`). Tools: `Sel::apart_under` (apart under a common
  prefix, the degenerate empty path included), `ArgAt` (a referring variable
  anchored at its object's root and region), `Inv::arg_changes`, `Thin`/
  `CSt::lend_all_at` (the state a lend at index i ran in), the `apart_args`
  pair lemmas. `Inv::lend_apart` is the dearest declaration (2.6 s, 1.3M
  steps): split it if it grows.
- P3: `Run::calls_body` (a callee with a body runs at the fuel below:
  `SafeAt(g, f)` applies as it is), `Run::calls_prim` (a primitive's answer is
  `w(g, ds)` plain, the heap as it was; its `get_all` from `Sim::pass_all`).
- Interface, agreed: (A) `Value::Written`: a written parameter passed by
  value comes back plain (probe `lend_plain_back_checked`); (B, C)
  `Heap::Kept` (no shorter; `Heap::Stays`: an old block live only where it
  was, no holes where none) in `SafeAt`'s answer, marked as this fragment's
  clause, with `Inv.stays` and its maintenance.

**Next, in this order (all agreed by the coordinating session):**
1. **The frame as §18.3's lens equation, restating `Heap::Frame`** (not
   beside it). Probe `lend_under_checked` is the program the frame by place
   could not carry (`x[0]` lent, written back, `Ret` reads all of `x`); keep
   it, and make it a theorem once the call is proved. Design:
   - `Sel::put_lent(rs, b, after_v, d)`: fold over `rs` in list order; at a
     reference into block `b`, `Sel::write_at(r.sels, λ _ => Sel::read_at(r.sels, after_v), ·)`.
     The coordinating session asks to say which form was chosen: the fold in
     list order, with the commuting of apart puts proved once beside it.
   - `Heap::Frame(before, after, rs)`: at every block `b < before.len()` with
     no reference lent whole into it (as now), live before ⇒ live after with
     `ob2.val = put_lent(rs, b, ob2.val, ob.val)`. A block lent whole is
     unconstrained.
   - Derived lemmas: the reads at apart paths (today's statement:
     `Sel::get_apart` per put), and the whole block lent to nothing
     (`Heap::frame_whole`).
   - `Inv` needs one more clause: the lent references into one block are
     pairwise apart by position (from `Lendable.apart` at entry; constant).
   - `Inv.frame` restated the same way from `h0`. `Inv::start`:
     `put_back_path` per put (it needs `StrsLaws`, so `Inv::start` takes `sl`).
     Same-heap builders: unchanged. `Inv::fresh`: the new block is past
     `h0.len()`. `Inv::kill`: the killed root is lent whole or made here.
     `Inv::store_rest`: the hard one. It needs `nw` to be `old` with
     `r.sels`'s part replaced by something like what was there:
     `nw = Sel::write_at(r.sels, F, old)`, with `F(x)` like `x`. Both callers
     store `Sel::write_at(r.sels ++ ss, g, old)` (`write_append`); like-ness is
     `ml.keeps` where the rest of the path is non-empty, and `WriteVal`
     (`RFits`, the code check, `Dyn::len_non_seq`) where it is empty. Then
     `put_lent` with the `r` entry's read changed is the old fold
     with `r` overwritten (commute apart puts, `over_over` with like-ness).
     If some statement kind lacks the like-ness, that is a finding for the
     coordinating session with the smallest program.
   - `Body::stage_ret`'s `frame` follows as now (`inv.frame`).
2. **D, distinct fresh results** (agreed in principle: §23.17 lists it as
   being added): in `Value::Views` or beside it, two referring `OFresh`
   results are in different blocks. Callee side: `own` puts each owned root
   alone in its block.
3. **P4–P9 over the equation.** The call's invariant is assembled like this.
   The binding is a sequence of pushes. First, an `Inv` with nothing pending
   at `(nl.st, e_upd, Mach(a.heap, m.env, a.io))`. Here `nl.st` is the state
   after the lends (moved arguments gone), and `e_upd` is the meaning with each
   lent argument's chain written up with its slot's value, i.e. the patch of
   the final state restricted to the old levels. P4 shows it: for a variable
   not on a lent chain, the frame's apart reads; for a lent argument,
   `Written` (slot = argument) and `ReadAll`; for its ancestors, the
   equation. Then P5 pushes the results with the existing builders, plus a
   builder for a fresh result whose block the callee made (generalise
   `Inv::fresh` to a given block past every root rather than copy it).
   Then P6 pushes the slots as written-back views (back = True), with
   `push_view` (a slot is a view at `Nil` of its argument, its cell the
   argument's reference by `Written`). Then `Inv::rekin` marks them pending.
   Its `Sim` premise is `patched(final) = push_all(e_upd, values)`, which is
   the fold's definition (slots at `Nil` write their whole value; `sib` for
   two slots under one view is `apart_args`). P7 is the moved argument: its
   holder is gone in `nl.st`, its root stays; `Kept` keeps `inheap` and
   `bare`. P8 is `Like` at the call (the slot's like-ness is `Written`'s
   `Fits`; the chain's is `Inv::back_like` before the call). P9 joins them.
   The call's run is `Going` at fuel 0 and the callee's `SafeAt` at `f` for
   fuel `Succ(f)`; the stage exposes the callee's `need` and going clauses for
   item 4.

**Traps found this session:**
- `j(proof, motive, base)` rewrites `a` to `b` given `a = b` and `P(a)`; with
  a record-valued step (`Option::map_some_inv`'s `f(a) = b`) use the equation
  as it comes, not `sym`.
- A `let` bound to a lambda whose result is a proposition needs its type
  written (`let P: (Next → Type) = λ q => …`). The annotation must be
  parenthesised when it ends in `= …`.
- `Next` is ambiguous with `list`'s; write `checker::Next(...)` in values.
- A name `Heap::Live` collides with the block constructor `Live` inside
  `Heap` members (hence `Heap::Stays`).
- `prest.drop(0)` is not `prest` by conversion (`List::drop_zero`), and
  `ps.drop(1).nth(k)` is `List::nth_drop_add`.
- Recursion must be on the matched variable itself; generalise the motive
  over it (`Sel::fit_write_self`) rather than rebuild `Cons(b, rr)`.
- `heather check --cache` keeps the declarations of a failed run, so the next
  run's "kernel-checked" count is small. Use `--only <item> --timings` to see
  a declaration's cost.
- `scripts/test --pr` reads the working tree: run it in one worktree and edit
  in a second (`git worktree add`, its own `HEATHER_CACHE_DIR`, the same
  `target/release/heather` binary), then `merge --ff-only`.

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
