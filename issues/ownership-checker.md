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

## Handoff (2026-11-26, end of the ninth session: P4 built but for the swap)

Continue on branch `claude/ownership-checker-sound`. Read design §23.19 (this
session: the callee's heap as puts) after §23.17–§23.18. Everything is at the
end of `lib/lang/ownership/sound.hthr`, after `LentFrame::call`, in the
order the parts are listed below.

**Done this session (P4 but its last two steps):**
- The lends: `CSt::lend_gone`, `Inv::lend_one`, `Inv::lends` (generic in
  meaning and machine).
- The frame's premises: `Value::lent_mem_p`, `Inv::call_un`,
  `Inv::call_lk` (`LentFrame::call`'s `lk` now only under a selection).
- `Inv::heap_rest`: the invariant on any heap with `Sim` there, a
  `LentFrame` there and `Heap::Stays`/growth from the current one.
- The licence across the lends: `Thin` records `na`/`nd`;
  `CSt::unatom_eq`, `owed_all_eq`, `against_eq`, `against_all_eq`,
  `meets_eq`, `license_eq`. `Inv::view_off_by` (the licence as the
  descendants' apartness); `Inv::view_off` is its wrapper.
- One put: `Inv::put_view_upat`, `Inv::put_view`, `Inv::put_view_mean`,
  `Inv::put_hold`, `CSt::put_mean`, `Heap::put_at`, `Inv::put_arg`.
- The puts in turn: `Heap::puts`, `CSt::puts_mean`, `Inv::puts` over
  `PutAt`; `Nat::Incr`, `Param::written_in`, `Param::written_incr`;
  `Heap::put_at_apart`, `Heap::put_at_holes`.
- Each `PutAt` from the lend: `CSt::lend_all_res`, `CSt::lend_write_rw`,
  `Inv::put_at_arg`.
- The swap's block lemmas: `Sel::put_lent_whole_in`, `Value::wrefs`,
  `Value::OutsRead`, `Heap::puts_block`; the list lemmas `Value::wlent`,
  `Value::wrefs_wlent` (the written list's references are the written
  parameters', by position), `Value::lent_put_w` (at a block no taken
  argument reaches, `Value::lent` puts as `Value::wlent`).

**Next, in this order:**
1. **P4's swap.** `Sim(nl.st, e_K, Mach(a.heap, m.env, a.io))` from the
   puts' `Sim(nl.st, e_K, Mach(h_K, m.env, m.io))` (`h_K =
   Heap::puts(m.heap, vs, sig.written(), outs)`, `outs = (w(g, ds)).drop(nres)`):
   for every block a live variable of `nl.st` reads, the callee's block
   equals the puts' block (both bare), then `Cell::agrees_store`'s pattern.
   At a block `b`:
   - no reference of `ks = Value::lent(ps, vs)` whole into `b`: the frame's
     equation gives `put_lent(ks, b, aa_b, mm_b)`; `Heap::puts_block` gives
     `put_lent(Value::wrefs(vs, written_from(ps)(0)), b, aa_b, mm_b)`. The two
     lists put alike at `b`: the taken references are whole (`Lendable.whole`),
     so none is into `b`, and the rest are the written ones in the same order.
     Needs a list lemma with an offset (say `Value::wlent(ps, vs)` beside
     `Value::lent`, and `wrefs(vsf, written_from(ps)(k)) = wlent(ps, vsf.drop(k))`).
   - a written whole reference into `b`: both are `aa_b`
     (`Sel::put_lent_whole_in`; `aa_b` live by `ReadAll`).
   - a taken reference into `b`: no live variable of `nl.st` reads `b`
     (the moved holder is gone, `own` puts no other root there, and the
     lend saw no view of it).
   `OutsRead` comes as in `Inv::call_lk` (slot = argument by `Written`,
   `ReadAll` at the callee's heap, no holes by `Heap::Stays`).
2. **P4's assembly** (`Inv::call_after`): `Sim::pass_all` (P1),
   `Inv::lendable` (P2: `apart` gives `Inv::puts`' `apb`, `live` its
   bareness), the callee's `SafeAt` parts (P3), `Inv::puts` with `arg :=
   Inv::put_at_arg`, `rd` from `ReadAll` at the call (`Value::get_of_read`),
   `written_incr`/`written_in`; then `Inv::lends`; then `Inv::heap_rest`
   with `LentFrame::call(inv.frame, aa, ks, frame, Inv::call_un, Inv::call_lk)`
   and `Heap::Stays(h_K, aa)` from `Heap::Kept` (the puts keep length,
   liveness and holes). Report P4 to the coordinating session.
3. P5–P9 as planned. **P6's trap (new)**: the meaning after P4 is
   `CSt::puts_mean`, a fold in the written list's order; the final state's
   invariant reads `CSt::patched`, a fold by levels. Show they agree at
   every variable (peel the slots' write-backs with `CSt::patched_back`, or
   commute walks at places `sib` says are apart). Report after P9.
4. The consolidation (the coordinating session's item 3:
   `issues/ownership-sound-consolidate.md` is not filed yet), then the body
   induction.

**Traps found this session:**
- A recursive theorem recurses only on a parameter declared before the
  colon; one bound by a `λ` after it is not a guard (`Inv::puts` takes `is`
  as a parameter).
- A `match` on a theorem's parameter takes no nested pattern (`Inl(⟨a, b⟩)`);
  nest the matches.
- `absurd(…)` and `⟨…⟩` need an expected type; annotate the `let`.
- A builder that ends in `j(…)` hides its record's fields (`root`) from
  conversion; recompute what a later step needs from `inv.refs` at that
  step, as `Inv::put_arg` does, rather than carrying `root` facts across.
- `--cache` makes an edit's check take seconds; the whole file uncached is
  about a minute and a half at this size.

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
