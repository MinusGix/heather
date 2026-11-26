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

## Handoff (2026-11-26, end of the fourth session: Ret, then the call)

Continue on branch `claude/ownership-checker-sound`. Everything is in
`lib/lang/ownership/sound.hthr`; design §23.12 says what was built this
session and why (read it, then §23.8–§23.11). The coordinating session's list
for this session was: 1 `cfit`; 2 the write-back; 3 `Death`/`Take` of a view's
root, `Ret`; 4 `Call` (plan it as named parts first and send the parts to the
coordinating session); 5 `SafeAt` for a body without joins or `Jump`, then
report; 6 joins, `Jump`, the induction. Items 1 and 2 are done, and so is the
`Death`/`Take` half of item 3.

**Done this session**:
- **`cfit` and `sib`**, carried through every builder. `cfit`: a copy's place
  fits its parent's copy, and the copy is *like* what is read there, i.e.
  the same code and length; fit alone is not kept by the child's own
  write-back at a place of several steps. `sib`: two siblings, one to write,
  are apart at their *places*. `excl` only says so of whole regions, and
  apartness under a shared prefix does not cancel at the `Sel` level; the
  decider cancels it (`Steps::apart_prefix`). The licence's soundness chain
  now takes a common prefix (`against_sound`, `license_sound`,
  `Inv::lic_suffix`; `Inv::lic_apart` is its Nil-prefix instance;
  `Inv::sib_lic`).
- **The write-back**: `Stmt::stage_back` dispatches to three stages:
  - `stage_back_ref_none`: the chain refers, nothing pending; the run stores
    what is there (`Heap::store_val`), and the meaning is unchanged
    (`Env::set_fix`).
  - `stage_back_ref_pend`: the chain refers, the child pending; the meaning
    is the walk's first step (`up_step`), the patch afterwards its rest.
  - `stage_back_copy`: a chain of copies, through `Inv::set_cell`.

  The parent is a holder or a view in each: `CSt::back_patched_hold` and
  `_view`. The state after is one `rekin` (`CSt::back_state`,
  `VEnt::reback`), finished by `Inv::back_finish`. `Inv::set_cell` takes
  `s.patched(e, m) = e`, before and after, instead of `none`.
- **`Stmt::stage_death_view`** (`Inv::drop_view`, `CSt::drop`): also valid
  while another view is pending (`CSt::patched_drop`, `up_drop`, `anc_drop`).
  **`Stmt::stage_take_view`** (`Inv::take_view`, `CSt::moved`, `VEnt::rn`, the
  `Alike` record; ancestry through `anc_moved`, `anc_par_eq`, `anc_not`).

**Next: `Ret`**, the open question first. `CSt::ret` passes when nothing is
pending, the results are as their origins say (`returns_all`), and each
written parameter's object is held and synced (`gives_back`).
`SafeAt` then wants four things:
- `ReadAll` of the cells against the meaning: Sim with bare blocks
  (`Value::get` to `Value::read`).
- `Frame`: `inv.frame`, since `lent` is `Value::lends` at the start.
- `Views`: from `returns_all` and `refs`.
- `Written`: the argument's block reads the final meaning, and
  `Dyn::Fits(ds_i, o)`.

Two of these need facts about the start that `Inv` does not keep:
- **an argument's reference is its object's root**. This one is cheap: a
  clause over `m.env` alone, since a referring cell is never set
  (`set_cell` is for plain cells only), and every builder keeps it.
- **a written parameter's meaning keeps the code and length of the argument
  as passed** (`Fits`). The original `ds` is not a parameter of `Inv`.

  For a referring argument it is what the root read in `h0`, so it can be a
  clause over `h0`. For a plain argument nothing in `Inv` holds the original
  value. Every write keeps the root's code and length (`write_keeps`, and
  `WriteVal` for a write of the whole), so it is a fact of the meaning
  alone, and could be carried by the body's induction instead.

This is a design decision: put it to the coordinating session before
building `Ret`.

**Then** the brief's item 4 (`Call`): plan it as named parts and send the
parts to the coordinating session before writing any of it.

**Costs and traps found this session**:
- No declaration written this session is dear: each takes under 0.3 s. The
  dearest in `sound.hthr` are still `CSt::write_inv` and `CSt::up_next`. The
  file checks in about 60 s without `--cache`.
- A `let` whose type is not stated cannot hold a `match`. The elaborator
  needs the motive: state the `let`'s type.
- `λ (a, b: T)` is not a lambda binder; write `(a: T) (b: T)`. In a Π-type
  `(a, b: T) →` is fine.
- A local named like a method (`rn` beside `VEnt::rn`) is refused as
  ambiguous at `en.rn(…)`.
- `match e: p(h)` is in the standard library, but stating the equation
  through `j` (as `List::filter_keep` does) needs no goal refinement.
- Record eta holds by conversion (`Mach(m.heap, m.env, m.io) = m`, and the
  same for `VEnt`), so a stage may answer `Stepped(m, …)` where the run
  answers `Mach(…)`.
- `scripts/test --pr` runs every test file here (no merge base) in about
  37 minutes. Run it from a second worktree
  (`git worktree add ../heather-wt <rev>`) so `lib/` can be edited
  meanwhile.

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
- 2026-11-26: the death and the take of a view (`62a8529`, `ea53353`); handoff rewritten at `Ret`.
