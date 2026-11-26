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

## Handoff (2026-11-26, item 3 in progress)

Item 3 continues in a fresh session from branch `claude/ownership-checker`.
Everything below is in `lib/lang/ownership/sound.hthr`, in this order:
selection lemmas, levels, `Sim`, reads and fits, `ReadInv`, the stages, the
words, the read stage, `Inv`, the entry.

**The invariant, clause by clause** (`Inv(tys, strs, s, e, m, h0, lent)`):

- `sim: Sim(s, s.patched(e), m)`. `Sim` holds the environments' lengths
  (`eargs`, `margs`, `elocs`, `mlocs`: a level names one slot in each),
  `vars` (each live variable's cell agrees with its meaning as its role
  says: plain holds `Plain(d)`; holder or view `Value::Reads`, the run's
  read at no selections, so block live and selections fitting; gone
  nothing), and `codes` (each live variable's meaning has the checker's
  code; the stage lemmas need it to discharge `is_word`, part codes and
  `Dyn::read_code`). `patched` is the meaning with the pending chain
  written up: the write through a view changes the heap at once, but the
  meaning only that view, until each write-back carries it one ancestor
  up. Eager write-back (§15.2, a refusal in the checker) keeps one chain
  at most. When nothing is pending, `Inv::sim_now` gives `Sim(s, e, m)`.
- `root`, `refs`: one run reference per object; a live holder's reference
  is its root, a live view's its root narrowed by one of its entries'
  region (`CSt::RefOk`; regions are at levels, read at the body's words by
  `CSt::unsteps`). The licence decides apartness of regions of one object.
  This clause is what makes that apartness of the run's references, which
  is what a write needs to leave every other live variable's read alone.
  A plain cell has no reference, so `RefOk` is `False` at `KPlain`; a
  holder or view of a value held plain (a copy) has `Plain` cells, and
  the clause says nothing of it.
- `apart`: two live references to different objects, one of which
  something live may change through (`CSt::changes`), are `Ref::Apart`.
  At entry this is `Lendable.apart`; a fresh object is a new block.
- `owned`: every live reference is to a lent block or one made here
  (`h0.len() <= r.b`). With `frame` (`Heap::Frame(h0, m.heap, lent)`) and
  `grows`, this gives `SafeAt`'s `Frame` at `Ret`.

**Proved**:

- The entry, `Inv::start`, from `ReadAll`, `Dyn::Coded` and `Lendable`
  (with `Slot`, `Sim::start`, `CSt::start_*`, `Value::get_of_read`).
- Stages against `Sim`: `Stmt::stage_lit`, `Stmt::stage_op` (with an
  `is_word` hypothesis on the first operand's code), `Stmt::stage_read`.
  Each gives `Stepped`: the run continues as `k(m2)` and `Sim` holds after.
- Words: `Sim::atom_ix` and `Sim::steps_same` (atoms at plain levels: one
  list of selections in the run and the meaning); `Sim::place` (the run
  reads a place the checker read at the meaning's value, given the read's
  residuals).

**Stated but open**: nothing is stated without a proof. Still to state and
prove:

- the stages against `Inv` (lift `Lit`, `Op` and `Read` through
  `Inv::sim_now`: `Do` runs them only when nothing is pending; every other
  clause is untouched by a push of a plain cell);
- `Fresh`; `Take`; `View`; `Write` through a holder and through a view, and
  the write-back (needs `put_back` and lemmas on `CSt::up`); `Death`;
  `Call`; `Ret`; then `SafeAt` for a body with no join and no `Jump`;
- `Dyn::Coded` at each callee from `Stmt::code_step`'s `Call` case.

**The proof shape that worked** (the `Read` stage, end to end; the model
for the rest):

1. Invert the checker's verdict once into a record (`ReadInv` from
   `CSt::read_inv`, through `Option::and_then_some` at each `and_then`, the
   last `map` closed by a `_close` lemma). The stage never re-reads the
   checker's definition.
2. Split the residuals the verdict owes (`Residual::all_app`,
   `Residual::all_true`) and feed them to the meaning-side lemma
   (`Place::fit_from`: a fit in the meaning).
3. Carry the meaning's selections to the run's (`Sim::steps_same`), then
   read through the cell (`Value::get_more` from `Sim::val`).
4. The run's step is then `j` on the run's own `match` (`λ k => j(sym(at),
   λ o _ => (match o {…}) = k(m2), refl)`), and `Sim::push` gives the
   invariant after (with `okc` from the code lemma).

Each step is a lemma with neutral parameters. A `match` on a
generalized scrutinee (`match x as λ b => x = b → …`) is the one tool for
every case split on a computed `Bool` or `Option`.

**What cost more than expected, and how it was staged**:

- The indices of atoms (arguments, then locals newest first) against
  levels: `Sim::atom_ix` splits the argument and local cases. The local
  case needs `nth_append_r` with an index rewritten by `j` on an `omega`
  equation.
- `ReadInv` first lacked the atom residuals and the `rs` split. Extending
  it meant threading `ha` through `read_inv_close`. Put every fact a later
  stage needs into the inversion record when you first write it.
- Method-call syntax on `self` parameters after leading `tys, strs`
  arguments is mis-resolved. Call `Sim::val(tys, strs, sim, …)`
  explicitly. `Plain` is ambiguous in expressions (`level2::Plain`), but
  not in patterns.
- Recursion that varies a parameter must put the matched parameter first
  (`Sim::steps_same(self ps, …)`).

**In the interfaces, possibly wrong, not yet raised**:

- `Heap::Frame` exempts every lent block, including those lent to read.
  A read-lent block is never written (the checker refuses it), so the
  clause is weaker than it could be, not unsound. The caller's side of a
  call (its other variables' reads of a read-lent block) then rests on
  `Written`, `ReadAll` and the licence, not on `Frame`.
- `Stmt::stage_op` needs the operand's code to be a word. That comes from
  the code check (`Func::coded`), a separate pass whose results the
  checker's state does not record. Either fold the code conditions into
  the checker's pass (planned in §23.7; then the stage gets them from the
  verdict's inversion), or prove that `Func::coded`'s `CEnv` agrees with
  the checker's codes at each statement. The first is cheaper.
- `CSt::RefOk` at a view takes any entry. For straight-line code there
  is one; after a join a read view has several (its region the union).
  This should be right, since the licence checks every entry, but item 4
  will tell.

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
