# A model of the kernel in Heather

Status: two rounds, both 2026-10-24 (milestone `hih-kernel-model`,
submilestones `hih-km-probe` and `hih-km-runs`, `issues/kernel-model.md`).
The modules are `lib/kernel_model/kernel_reduction.hthr` (the model and the
probe lemma) and `lib/kernel_model/kernel_runs.hthr` (reduction as a
relation and the run folds, §7). Their tests are
`crates/elab/tests/lib_kernel_model_reduction.rs` (the probe lemma's, and
its refusals) and `lib/_tests/kernel_model/kernel_runs_tests.hthr` (the run
folds'), and their export test is `kernel_model_exports` in
`crates/export/tests/library_sweep.rs`.

## 1. Why

Minus framed the testing work of 2026-10-23 this way
(`docs/testing-architecture-design.md` §5): modules should be trusted and
shipped, and the arcane optimisations that would make that cheap want
Heather-in-Heather's proofs. Until then there are two tiers of trust. A fast
lane may use an optimisation nobody has proved, and the nightly sentinel runs
the reference path and compares. Heather-in-Heather later **promotes an
optimisation from "checked nightly" to "proven"**.

None of the roadmap's Heather-in-Heather milestones could do that promotion.
They are about native programs: the program logic, memory, passes, and the
lexer. To promote an optimisation of the kernel, you need a model of the
kernel to state it against. This note starts that model.

The kernel already relies on one argument that nobody has proved. A `Nat`
fold over a run (`Val::NatRun`, `Succ^c(tail)`) is not taken one step at a
time. Instead, its step is **classified by evaluating it on fresh neutral
probe variables** (`crates/kernel/src/eval/probe.rs`), and the class is
iterated over the run (`value/algebra.rs`). The bit transducers of
`eval/transduce.rs` work the same way. Both rest on two sentences in
`probe.rs`:

> Soundness is the substitution property of reduction: a value with no stuck
> case split on `k`, `ih`, or `x` was reached by a reduction that holds for
> every instantiation of them.

> Its reductions charge the ordinary fuel — they are the ones the fold's own
> first step would perform — so a probe never manufactures a verdict fuel
> would have refused.

`crates/kernel/DESIGN.md`'s acceleration policy calls this "the adequacy
argument". It is the obvious first thing to prove. It is load-bearing today,
it is small, and every later acceleration proof needs it as a lemma.

## 2. The model

**Fragment.** Untyped terms with functions and `Nat`'s eliminator, which is
what a fold's step is made of:

```
Tm ::= Bv(i) | Fv(a) | Lam(b) | App(f, a) | NZero | NSucc(t) | NRec(z, s, n)
     | SPair(a, b) | SProj(p, t) | NRun(c, t)          (p ::= PFst | PSnd)
```

The second round added the last line: pairs and their projections, which
the affine class's course-of-values windows are made of, and runs.
`NRun(c, t)` is `Val::NatRun`, `Succ^c(t)` held as one node. It means what
its unpacking says: `NRun(c+1, t)` reduces to `NSucc(NRun(c, t))` and
`NRun(0, t)` to `t`, so a run is never a weak head value of the model, and
the model's unary fold over a run takes one successor at a time.

**Locally nameless.** Bound variables are de Bruijn indices. The probe
variables are free atoms `Fv(a)`, which no binder captures. This matches the
kernel, whose probes are `Head::Var` at reserved levels that no real context
reaches. It also removes all shifting:

- an instantiation `t.inst(σ)` replaces atoms by locally closed terms, so it
  never shifts;
- reduction only opens a binder with a locally closed argument (call by name
  on locally closed terms), so `open` never shifts either.

**Reduction.** ch. 06's untyped weak-head reduction, call by name, as a
fuelled function. `Tm::whnf(fuel, t) : Option<Tm>`, where `None` means out of
fuel and one unit of fuel is one call of `step`. The function is written as
`step(ev, t)`, parametric in its recursive call, like `ir_v1`'s evaluator.
That makes the induction on fuel a two-line wrapper around a lemma about one
step. A stuck elimination is a value: `App(h, a)` with `h` not a `Lam`, or
`NRec(z, s, h)` with `h` neither `NZero` nor `NSucc`.

**Blocked.** A result is *blocked* when it is an elimination whose spine is
headed by an atom (`Tm::blocked`, via `Tm::rigid`). This is `probe.rs`'s
"stuck case split on a probe variable". It is the only place an instance can
take a different path from the probe: the atom's image may be exactly the
introduction form that the eliminator was waiting for.

## 3. What is proved

- **`Tm::whnf_inst`**: let σ send every atom to a locally closed *value*
  (`Fv`, `Lam`, `NZero`, `NSucc`). If a run is not blocked, then at the same
  fuel the instance's run is the instance of the result. This holds for an
  out-of-fuel run too, which includes both of `probe.rs`'s claims: the class
  holds at every instantiation, and the probe charges exactly the fuel the
  fold's own step would. An instance runs out of fuel exactly where the probe
  did.
- **`Tm::whnf_inst_settled`**: the same for σ into **any** locally closed
  terms, on runs that are *settled*: neither blocked nor a bare atom. This is
  the form the kernel needs, because its `ih` is a thunk of the recursive
  call and not a value. The value hypothesis is used at one place only: a run
  that ends at a bare atom, where the instance would go on to reduce the
  atom's image. A σ whose image mentions another atom is also allowed. That
  gives the "peeled" reading (`k := Succ x`) for free.
- **`Tm::probe_step` / `Tm::probe_step_settled`**: the corollaries as the
  kernel uses them. A closed (atom-free) step is applied to atoms `0` (`k`)
  and `1` (`ih`). Whatever that probe reduces to unblocked is what the step
  reduces to at any `k` and `ih`, at the same fuel.

The tests vary the four axes of `docs/testing-generated-terms.md`:

- the model runs at literal terms by `refl`;
- the lemma is applied at an **open** `ih` in checking position, for values,
  thunks and the peeled reading;
- an instance runs out of fuel where the probe did;
- three negative controls show that each hypothesis is needed:
  - a step that cases on `k` is blocked, and its instance at `k := 0` really
    differs from the instance of its probe;
  - an instance by a non-value really differs when the probe ends at a bare
    atom;
  - the lemma cannot be applied to a blocked probe.

Weakening `blocked` to ignore applications breaks the proof. I checked this
by hand during the round, as a mutation of the module.

The module checks quickly (its proofs are one arm per constructor, with no
search) and exports to Lean with no refusals (the export test). `scripts/export-recheck` now also
hands `KernelModel.hxk` to Lean's kernel, so the proofs can be checked by a
kernel that is not the one they are about (§5).

## 4. What it does not prove, yet

The model and the kernel are still different machines. Closing that gap is
the rest of the milestone (§6).

- **The kernel is not ch. 06 by substitution.** It evaluates into a value
  domain with closures, glued neutrals, thunks memoized in an arena,
  δ-unfolding of globals, and run values. The theorem is about the reference
  relation that the kernel claims to implement. So the claim "the
  classifier's step is sound" now rests on "the kernel implements ch. 06 on
  this fragment", which is the differential suites' job, and no longer on an
  unproved sentence.
- **The fragment is small.** There are no globals (δ), no types or levels,
  and no `Vec`/`W` eliminators (Σ, projections and runs came with the
  second round, §7). Extending the syntax is mechanical. Every lemma here is
  one arm per constructor.
- **Classification is not iteration.** This section's lemma proves that a
  class read off a probe holds at every instance. That iterating the class
  over a run computes the unary fold is the second round's (§7).

## 5. Who checks the checker

Using Heather's kernel to justify an optimisation in Heather's kernel is
circular in one specific way. If the optimisation (or anything else in the
kernel) were unsound in a way the model's proofs happen to exercise, a false
lemma could be accepted. There are two mitigations, and both are cheap here:

- **The theorems do not lean on the optimisation they justify.** They are
  proved at an open fuel and open terms, so their proofs never fold over a
  literal run. Only the tests' literal runs of the model can, and they are
  examples, not lemmas.
- **The proofs export.** They are layer-free and use only `Nat`, `Bool`,
  `Option` and the module's own inductive, so `scripts/export-recheck` hands
  them to Lean's kernel, which shares no code with Heather's. That is the
  roadmap's reason for wanting export more than import (`heather-in-lean-coq`).

The metatheory of the calculus itself (that ch. 06's rules are sound for
DeLaM) stays heather-coq's job. This model takes the reference relation as
given and proves implementation-level facts relative to it.

## 6. The ladder

Each rung is a fact some part of the kernel or the caches relies on, stated
against this model, in roughly increasing cost. The first one is this round.

1. **Probe soundness** (`hih-km-probe`, done here).
2. **Run-fold adequacy** (`hih-km-runs`, done in the second round, §7):
   iterating an affine or synchronous class over a run is the unary fold.
   It needed a deep reading, Σ and projections, and runs as a value
   representation with their unpacking; reduction as a relation took the
   place of fuel additivity. With it, `Val::NatRun`'s acceleration is
   proved rather than argued, up to the gaps in §7.4.
3. **Bit transducers**: rung 1, plus a finite enumeration of head bits and
   state.
4. **Strategy changes**: two evaluation strategies (δ-lazy unfolding,
   same-head spine comparison, single-step on the newer head) agree on
   verdicts. This needs conversion in the model, not just reduction.
5. **The evaluator itself**: an environment machine with sharing, as the
   kernel builds it, proved to compute what `whnf` computes. Its native
   compilation (`hih-program-logic`'s compiler) is then the compiled
   evaluator of `docs/testing-architecture-design.md` §3.3.9, with this as
   its adequacy theorem.
6. **Caches and invalidation** (§3.3.10, early cutoff). What a model can
   prove here is narrower than it looks. It can show that a checker
   *defined in Heather* reads only a module's interface. The risk in the Rust
   loader is that it reads more than its hash covers, and no model of the
   kernel reaches that until the loader is itself the modelled code. So this
   rung waits for rung 5, and until then the sentinel's comparison is the
   guard.

## 7. Run-fold adequacy (second round)

`eval/runs.rs` folds over a run by the class of its step. An affine step's
tree is iterated over the run's program and built at the fold over the tail;
a synchronous fold applied to a run cancels the two runs' common prefix.
This round proves both against the model: what the kernel builds is
convertible with the fold the reference reduction takes one successor at a
time.

### 7.1 Reduction as a relation

The probe lemma is about `Tm::whnf` and needs its runs unblocked, because it
claims that a probe's weak head value *is* the instance's. A run fold is a
statement about deep values: the kernel reads a tree by forcing a probe's
components, and builds its answer under pairs and successors. So this round
states everything with one-step reduction `t.Red(u)`: β, `elim_Nat`'s two ι
rules, a projection out of a pair, a run's unpacking, and their congruences
in head position, under `NSucc` and `SPair`, and in an application's
argument. `t.Reduces(u)` is its reflexive-transitive closure (a count of
steps and an existential), and `a.Joins(b)` says both reduce to one term.
Every step of `Red` is a conversion of the calculus, so joinable terms are
convertible; no confluence is needed for that direction, which is the one
soundness wants.

Two facts connect the relation to round 1's evaluator and probe:

- **`Tm::whnf_sound`**: whatever `whnf` returns is a reduct of its input.
- **`Tm::reduces_inst`**: reduction is closed under instantiating atoms by
  closed terms. Unlike `whnf_inst` this needs no unblocked or settled
  hypothesis. A reduction says where a term goes, not that it stops there,
  and an instance may go on further.

### 7.2 The readings

The kernel reads a probe value as an affine tree (`read_affine`) or a
synchronous increment (`probe_sync`). The model's readers do the same over
`whnf`, sub-term by sub-term:

- **`Tm::read`**: a pair reads as a pair of readings, successors are
  stripped, and what they sit on must be `NZero` or atom `1` (`ih`) under
  projections. The tree is `Aff` (`Leaf(inc, path)`, `Lit(inc)`,
  `Branch`), with increments as counts. Run against the uniform probe
  `s(k, ih)` or the peeled one `s(Succ x, ih)`.
- **`Tm::read_sync`**: the probe's weak head is a `Lam`, and applied to
  `Succ x` it strips to `q` successors on `ih x` exactly.

Their soundness (`Tm::read_sound`, `Tm::read_sync_sound`) says that a term
read as a tree reduces to the tree's term at `ih`. Instantiated, a ground
step at any closed `k` and `ih` reduces to the tree at `ih`
(`Tm::probe_affine`, `Tm::probe_peeled_affine`, `Tm::probe_sync`).

The tree arithmetic follows `value/algebra.rs`: `Path::at` (descending
through a successor-free leaf extends its path, anything else ill-typed is
declined), `Aff::compose` (outer at inner, increments added, successors on a
pair declined), and `Aff::iter`. `Aff::compose_sound` is the substitution
lemma: the outer tree's term at the inner tree's term reduces to the
composite's term.

### 7.3 What is proved

With `s` ground and closed, `z` and the tails closed, and `Aff::term` the
tree with its successors spelled out (`Aff::build` is the same tree with
every increment a run, as `eval/runs.rs` builds it):

- **`Tm::fold_affine`** (uniform): if the probe reads as `tree` and
  `tree.iter(c) = Some(r)`, then `NRec(z, s, NRun(c, x))` joins
  `r.build(NRec(z, s, x))`.
- **`Tm::fold_affine_peeled`**: if the peeled probe reads as `tree` and
  `tree.iter(c) = Some(r)`, then `NRec(z, s, NRun(c+1, x))` joins
  `r.build(s(x, NRec(z, s, x)))`: the innermost step is taken as written.
- **`Tm::fold_sync`**: if `read_sync` gives `q`, then
  `NRec(z, s, NRun(a+m, t))` applied to `NRun(b+m, x)` joins
  `NRun(q·m, NRec(z, s, NRun(a, t)) applied to NRun(b, x))`: the common `m`
  cancelled, `q` successors per pair, residuals as runs.

Each has a `_unary` form that is the induction: the fold reduces to `r`'s
term. The kernel's value reduces to the same term by unpacking its runs
(`Aff::build_unpacks`, `Tm::run_unpacks`).

The probes in `lib/_tests/kernel_model/kernel_runs_tests.hthr` evaluate the
readings at the kernel's own example steps (`add`, `half`'s window, a step
that matches on `k`, `min`, and a counter that cancels without
successors), check that too little fuel reads nothing and that successors under
a pair are declined, and apply each theorem at an open run and tail. During
the round, six hand mutations of `kernel_runs.hthr` were each rejected: an
extra successor in `graft`, `at` extending a path in the wrong order or
ignoring the projection, a reader that drops a successor or accepts any
atom as `ih`, and a synchronous reader that accepts any argument.

The module exports to Lean with no refusals (`kernel_model_exports` loads
it, and `kernel_reduction` with it). The Lean recheck itself
(`scripts/export-recheck`) did not run in the cloud box that did the
round, which has no Lean and cannot fetch one.

### 7.4 What it does not prove, yet

- **Programs and powering.** Increments are counts. The kernel's increments
  are `ContextProgram`s, its `iterate` is binary powering over a program's
  DAG with identity short cuts and compaction, and the model's `iter` is
  one composition per step. That they compute the same tree is
  `value/algebra.rs`'s randomized reference test. A proof needs
  composition's associativity and identity laws; it is model arithmetic,
  with no reduction in it.
- **The kernel's other synchronous heads.** `probe_sync` also accepts a
  `WfIh` or `WIh` probe value (a fold whose motive's functions come from
  the W route); the model reads only a `Lam`.
- **The evaluator.** As in §4, these are facts about the reference relation
  that the kernel claims to implement, not about the kernel's machine.
