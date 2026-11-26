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

## Handoff (2026-11-26, item 3: the write stages in progress)

Continue on branch `claude/ownership-checker-sound` (the coordinating
session's item list and rails are in its brief; this section is the state).
Everything is in `lib/lang/ownership/sound.hthr` unless named. Design
§23.8–§23.10 says what changed and why; read them first.

**Done in item 3**: the stages `Lit`, `Op`, `Read`, `Fresh`, `Take` (part,
plain, holder), `Death` (part, plain, holder), `View` (plain; to read and to
write, of a holder and of a view), and `Write` whose root is plain
(`Stmt::stage_write_plain`), each concluding `Stepped` against the whole
`Inv` from `none: s.pending() = False`.

**Next, in order**:

1. **Write through a holder** (`KHold(o, a)`, `a.writes()`). Two cells:
   - the holder's cell is `Plain(d)` (an object held by value, no root):
     as `stage_write_plain`, but the role is a holder, so `Cell::Agrees` is
     `Value::Reads` (`Value::get(h, Plain(nw), Nil) = Some(nw)`).
   - `Refer(r)`, `r = root(o)` (from `refs`): the run stores
     `write_at(r.sels ++ ss, λ _ => vd, old)` into block `r.b`
     (`Stmt::write_runs_ref`, `Heap::val_store_here`, `bare`). Every other
     live reference reads as before: another object's in the same block by
     `apart(o, …)` (`Changes(o)` from the holder's `a.writes()`) widened
     with `Sel::apart_ext_l/_r`, then `Sel::get_apart`; a view of `o` by
     the licence (`CSt::write_lic_hold` then `Inv::lic_apart` with
     `pl = Pl(o, xs)`, `CSt::unsteps_steps` to get `p.steps` back), then
     `Sel::get_under` with prefix `r.sels`; other blocks by
     `Heap::val_store_other`. The holder itself reads `write_at(ss, …, R)`
     by `Sel::write_get`, which is `e2`'s root by `Steps::write_sels`.
     `frame`: the block is `owned` (lent or new); `grows`, `inheap`,
     `bare` by `Heap::store_len`, `Heap::obj_store_holes`.
   - The state after is `s.written(l).unback(l)`: equal views (no entry's
     level is a holder's: `vents`), different `touched`/`wrote`. `Inv`
     must be rebuilt for it (§23.10: `unsteps`, `anc_of`, `Parent`, `up`
     do not convert between the two states); write `Inv::touch` once,
     with `refok_keep`, `excl_keep`, `parent_keep`, as `Inv::gone` does.
   - The words regions read are unchanged at `m2`: plain levels' cells are
     not touched and a plain cell reads without the heap; copy
     `stage_write_plain`'s `wsame` (via `Sim::lvl_ix` on the new `Sim`).
2. **Write through a view** (one writing entry `pe`): the heap changes in
   the root's block at `root(pe.obj).sels ++ unsteps(pe.reg) ++ ss`; the
   state becomes pending (`unback`), so `Sim` is against
   `s2.patched(e2)`, the chain written up by `CSt::up`. Ancestors read the
   new heap, which is what `up` writes into them; needs lemmas on `up`
   (one step: `Env::set` of the parent at `en.at`) and `put_back`.
   Entries not related to `l` are apart by `excl`; descendants by the
   licence (`write_lic_view`, `meets_view`).
3. **The write-back** (`is_back`): a pending state's stage; `backed(lv)`;
   the heap does not change, the meaning catches up one ancestor.
4. Death and Take of a view's root; `Ret`; then item 4 (`Call`, with the
   defects B and C reported to the coordinator: written slot is the
   argument where it refers; distinct fresh results).

**Costs and traps found this session**:

- Re-spelling a checker definition's nested `match` inside an inversion
  (`and_then_some` lambdas) made the kernel's conversion overflow its
  stack (abort 134, `--timings` `.open.tsv` named the item). Split the
  checker function so the inversion names the tail (`CSt::write_last`).
- A `let` whose value is a `match` (even in a lambda) needs its type or a
  motive (`as λ _ => T`). Constructors `Plain` need `level2::Plain` in
  expressions.
- Before adding a lemma, grep: `Sel::get_fit`, `Sel::get_parts`,
  `Sel::fit_append`, `CSt::var_in` (a function) already existed.
- Whole-folder check without the cache: about a minute for `sound.hthr`.

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
