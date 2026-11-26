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

## Handoff (2026-11-26, end of the twelfth session: the run as the machine's reading, `Back`, `Len`, `Sig::ok`, the split)

Continue on branch `claude/ownership-checker-sound`. **The plan changed**
(the repository owner's decision, through the coordinating session): the
proof is to be made compositional now, as restated in §26 of the design note
on the coordinating branch (`origin/claude/focused-darwin-it31c1`, read it
with `git show`, do not merge): agreement per variable outside the places of
its live write views plus a sync clause for a written-back view, instead of
`Sim` of the patched environment; one disjointness clause over footprints;
shape-stability as one invariant. Under it a written argument's slot is a
write view of the argument at the whole place, so the call's P4–P6 as built
are not needed. §26.5 (the run stuck wherever the meaning takes a fallback)
belongs with the restated stages. P5 on the present invariant was dropped:
`Inv::bind_param_result`, `Inv::bind_view_result`, `MovedArg`, `ViewArg`
are in history at `0e42cd2`, `f3925c5` (reverted by `1a47948`, `320b40f`).

**Done this session** (design §23.22, §23.23):
- The run as the machine's reading (`b4becf9`): a written parameter's slot
  after a call is the argument where it refers (`Value::slots`); a store is
  stuck outside the activation's `Act` (`lent` of the entry's arguments,
  `h0` its heap length; `Act::may`), the write stages meeting it from
  `Inv.owned` (`Act::may_owned`); `Stepped.runs` at `Act(lent, h0.len())`.
- `Back(p, x)`, the write-back as its own statement (`5070b13`): meaning a
  write; checker `CSt::back_of` (`Write` refused where it would be a
  write-back, `Back` where not; `writes_back` names `Back`); run the identity
  where `x`'s cell refers, `Stmt::write_run` where it is a copy. The run's
  reference test of `b4becf9` is gone.
- `Len(p, w)` (`c512fee`): a place's length as a word, checked as `Read` of
  a sequence, owing `RLen(p, w)` (a new residual kind, `Width::Holds`) at a
  bounded width; `Stmt::stage_len`.
- `Sig::ok`: `Sig::once` (no parameter answered twice) and `OParam` only of a
  taken parameter whose code moves (`c512fee`, `fc573b0`).
- `Inv.cfit` over views to write only (`65d5c1a`, a proof-side gap).
- `sound.hthr` split mechanically (`c583fcd`), no statement changed:
  `sound_paths` (1364 lines), `sound_state` (1565), `sound_heap` (2818),
  `sound_inv` (3844), `sound_write` (2055), `sound_stages` (1340),
  `sound_like` (864), `sound_ret` (533), `sound_call` (1941); `sound.hthr`
  is the map and imports them all. With `--cache`, an edit to a module's last
  declaration checks in one to two seconds for each module. A declaration
  sits in the earliest module its kind and its dependencies allow (the
  splitter is a script; regenerate nothing by hand: edit the modules now).
  Where std declares the same name (`Bool::or_false_parts`, …) the uses are
  qualified by their sound module (`sound_paths::Bool::…`); `Slot` is
  `sound_heap::Slot` past `sound_heap` (store.hthr has an `inductive Slot`).

**Probes whose bodies changed from `Write` to `Back`** (for the seam's
session, to find its own write-backs): in `checker_tests.hthr` the functions
`after_call`, `back_under` (its two write-backs onto parents; its first
write stays a `Write`), `between`, `between_after`, `calls_wprim`,
`copy_caller`, `lend_plain_back`, `lend_under`, `lends_one`, `loan`,
`moved`, `nested_two`, `one_window`, `outer`, `outer2`, `peek`,
`unreturned`, `written`, `zero_caller` (and the new `back_one`,
`back_not_back`); in `run_tests.hthr` the new `back_read_r`,
`back_copy_read_r`, `back_copy_plain_r`. Rule: a write whose value variable is a view to write
opened on the written root at the written steps is a `Back`.

**The invariant's clauses sorted** (for the restatement; `Inv` in
`sound_inv.hthr`, with the statement kind that first needed each):
- *The checker's state alone*: `one` (a holder per object: `Take`, the
  call's moved result), `words` (region levels plain and bound: `View`'s
  atoms), `held` (holders' objects exist: `Fresh`), `vents` (entries at live
  view levels: `View`), `chain` (an entry's parent below it and its region
  the parent's extended: `View`), `wpar` (a view to write's parent view is a
  view to write: the writes through views), `nbase` (`Ret`).
- *The roots index against the state* (no heap, no cells): `apart` (objects
  that change are apart: writes), `owned` (a changing object's root lent or
  made: `Ret`'s frame, and now `Act::may`), `young` (`Fresh`), `made` (made
  objects whole and past `h0`: `Ret`).
- *The heap*: `inheap` (roots in the heap: `Fresh`), `bare` (roots' blocks
  have no holes: `Fresh`, writes), `frame` (`LentFrame`, the lens equation
  against `h0`: writes, `Ret`), `grows`, `stays` (the call).
- *The cells*: `refs` (a cell's reference is its root narrowed: `View`,
  writes), `own` (an owned cell's block is its object's alone: `Death`,
  `Take`), `uni` (a view refers iff its parent does: the write-back), `excl`
  and `sib` (live views to write apart from the rest at the run's words: the
  writes, the write-back), `cfit` (a view to write over a copy fits it: the
  write-back of a copy), `args` (`Ret`'s arguments as passed), `href` and
  `hown` (a holder's cell refers to and owns its root: the call's moved
  results, P5).
- *Only for the patched meaning*: `sim` (`Sim` of `s.patched(e, m)`: a
  pending chain's ancestors read as if written up, D2 §23.15), with `Like`
  (a separate record, §23.16) carrying what the meaning keeps of a view to
  write on a pending chain. The restatement replaces both with agreement
  outside live write views and a sync clause.

**Next, in order** (the coordinating session's list; ask it for the order
of the restatement's pieces): the restatement of §26 on the split modules,
starting from the clauses above; the body induction; joins, `Jump`, fuel,
`CheckSound`; the experiments retired.

**Traps found this session:**
- An imported name that std also declares is ambiguous across modules (a
  local one used to win): qualify by module, or drop an identical duplicate.
- A bare `Slot`/type name may silently resolve to std's type when two
  imports define it: qualify by module.
- `let G = λ (st: CSt) => Exists<…>(λ root2 => …)` needs the inner binder
  annotated and the `let` typed (`let G: CSt → Type = …`).
- `absurd` sees only an outer constructor clash: `Some(Plain x) = Some(Refer
  r)` needs `Option::some_inj` first.
- A run lemma that mirrors the run's match by `j` must mirror its exact
  shape (factor the run's arms into a `fn`, as `Stmt::write_run`, so the
  mirror is one call).
- `scripts/test --pr` with no merge base runs every file and the native
  gates get killed (`signal: 9`): use `HEATHER_PR_BASE=4edbd21` (the
  coordinating branch's `47939344` is cherry-picked here).

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
- 2026-11-26 (twelfth session): step 0 items 1–3, the run as the machine's reading (`b4becf9`, design §23.22): a written parameter's slot is the argument where it refers (`Value::slots`); a write whose source is the very place stores nothing (`Value::is_ref`, `Ref::same_sound`); a store is stuck outside the activation's `Act` (lent to change, or made since entry; `Act::may`), met in the write stages by `Inv.owned` (`Act::may_owned`); probes in `run_tests`. `scripts/test --pr` at `b4becf9` (no merge base with `origin/master`, so every file ran): `== suite: 4139 passed, 1 failed, 3 ignored ==`, the failure `native_linked.rs` killed by `signal: 9` under load; rerun alone (`scripts/test --pr --test native_linked`): `== suite: 2 passed, 0 failed, 0 ignored ==`.
- 2026-11-26 (twelfth session, after the coordinating session's change of plan): P5's two builders reverted (`1a47948`, `320b40f`; the code stays in history at `0e42cd2`, `f3925c5`), `Inv.cfit` over views to write only (`65d5c1a`); `Back(p, x)` as its own statement replacing the run's reference test (`5070b13`); `Sig::once` and `Len(p, w)` with `RLen` (`c512fee`); design §23.23. `HEATHER_PR_BASE=4edbd21 scripts/test --pr` at `c512fee` (with the coordinating branch's `47939344` cherry-picked): `== suite: 4070 passed, 0 failed, 3 ignored ==`.
- 2026-11-26 (twelfth session, end): `sound.hthr` split into nine modules (`c583fcd`); `Sig::ok`'s `OParam` only of a moving taken parameter (`fc573b0`). `HEATHER_PR_BASE=4edbd21 scripts/test --pr` at `400d526`, clean tree: `== suite: 4070 passed, 0 failed, 3 ignored ==`. Handoff rewritten (the clauses sorted for §26's restatement).
