# WP-preserving compilation: what the paper means for Heather

Status: **survey**, 2026-10-28. Source: Carmine Abate, Kleio Liotati,
František Farka, Sebastian Ertel, *Preserving Separation Logic
Specifications through Compilation*, arXiv:2610.37244v1 [cs.PL], 27 October
2026 (CC BY 4.0), committed beside this note as `docs/papers/2610.37244v1.pdf`.
Section, lemma and theorem numbers below are the paper's. The Rocq
development is mentioned but has no public link in v1. Read against master
at `0db0151`. Follow-up is in §8.

The paper asks what a compiled program's *specification* is, not only its
behaviour. CompCert-style correctness says every behaviour of `⟦P⟧` is one
of `P`'s. That gives a client of the compiled code nothing to reason with:
no assertion about target memory and registers, no footprint, and no frame
rule. The paper proves a stronger statement instead, **WP-preservation**.
If a source program satisfies a weakest precondition in an Iris separation
logic, the compiled program satisfies the corresponding weakest
precondition in a separation logic for the target, owning only the cells of
the variables the code uses and the registers it needs. The vehicle is a
simulation between the interaction trees of source and target. The test
bed is the IMP→ASM compiler of Xia et al.'s ITree paper. The result then
extends to modules, calls and separate compilation.

This is the closest paper yet to Heather's native lane. Both build the
compiler's meaning on interaction trees, both target a register-and-memory
machine, and both want the compiler proved once.

---

## 0. The answer in brief

1. **For the target set of `hih-tools`, Heather needs nothing from this
   paper.** The paper says so itself (§5.3): for a closed program, the
   target facts WP-preservation gives "could also be derived from the
   adequacy of the source logic and a behavioral correctness theorem for
   the compiler". That is exactly Heather's route. `native_compile_correct`
   gives `SimProgram(io, src.denote(args), s)`. A spec is a tree that the
   source refines (`Program::sim_refines`). Facts about runs follow from
   traces (`cat_native_sends`). Every tool in
   `docs/native/native-real-programs-plan.md` is a closed whole program with
   procedures inlined, so there is no second piece of target code for a
   target-level specification to serve.
2. **Heather already has most of the machinery, in a different
   vocabulary.** Here is the mapping:
   - The paper's generic transfer interface (SIMret/SIMtau/SIMvis,
     Lemma 1) corresponds to `ITree::Sim` over a `TraceMap` and `Contract`,
     which is already generic in the two event containers.
   - Its `νG. µL` stutter bound corresponds to `Sim` being closed backward
     under finite `LinuxSteps`, and to `Eutt`'s finite drop counts.
   - Its closure under bind and iteration corresponds to `sim_bind`,
     `simk_bind`, `sim_iter` and `simk_iter`.
   - Its target WP in continuation form corresponds to `Target::Runs` and
     `Callee::Returns`. Both are already stated as "the code runs as `t`
     bound to `k`, given that `k` holds wherever it goes on".

   §2 sets this out.
3. **What Heather lacks is the footprint, and the paper shows the shape it
   should take.** Heather's statement-level invariant `Target::Placed`
   relates the *whole* environment to the *whole* data region. The paper's
   correspondence is per variable: `Cell(x)` owns one source variable's
   authority and one target cell. Each piece of code owns only the cells
   of the variables it uses, plus its registers. That small footprint is
   what lets a compiled function carry a contract that other compiled code
   can rely on (Theorem 2). It also lets the frame rule apply at the target
   (§4).
4. **The paper's main result becomes Heather's design reference when
   procedures arrive.** Procedures that make calls are deferred on purpose
   (plan §7; program-logic design §10 item 2). When they come, three
   results each have a direct Heather counterpart:
   - Theorem 2: each compiled procedure's target contract is *derived*
     from its source contract by the compiler theorem.
   - Corollary 1: per-module contract preservation.
   - Theorem 3 item 2: link once, verify each module against contracts
     only.

   The paper's limitations line up with things Heather already does better.
   Heather has a real stack, where the paper has no activation records and
   a resolver that saves and restores locals. Heather's `Callee` contracts
   can name a per-procedure clobber set, where the paper clobbers a
   link-wide register pool. Heather's fuel stands in for the paper's Löb
   induction. Filed as `issues/native-procedure-contracts.md` (§8).
5. **Two things not to adopt.** Heather does not need Iris, ghost
   authorities or step-indexing. Heather does not need internal state as
   tree events: the paper's `GetVar`/`SetVar` events are exactly what
   design §10 item 6 decided to keep out of the trees. §5 explains why each
   choice stays right for Heather and what it costs.

---

## 1. What the paper contributes

**Program logics from ITrees (§2, after Vistrup et al.'s "Program Logics à
la Carte").** A *logical handler* gives each event a specification: what
must be owned to trigger it, and what comes back. A generic
`wpi_H t {Φ}` lifts the handler to the whole tree. `Ret` establishes `Φ`,
`Tau` continues, and `Vis(e, k)` delegates to `H(e, λa. wpi k(a) {Φ})`. A
language gets its separation logic by giving a denotation into
`itree E R` and one handler per effect. The paper's target logic for ASM
has **no proof rules of its own**. Its WPs exist only as conclusions of
WP-preservation.

**The transfer lemma (§5.1, Lemma 1, Appendix A.1).** Take an Iris-valued
simulation `SIM_R(s, t)` between a source and a target tree, over
different event types, return types and handlers, that satisfies three
local conditions:

- a source `Ret` is matched by a target that may emit handler-neutral
  events before returning;
- a source `Tau` can be dropped;
- a source `Vis` is matched by a target `Vis`, possibly after target steps,
  with a *handler-transport wand* turning the source handler's obligation
  into the target's.

Then `SIM_R(s, t) ∗ wpi s {Φ} ∗ (∀u v. R(u,v) ∗ Φ(u) −∗ Ψ(v)) ⊢ wpi t {Ψ}`.
The lemma knows nothing about IMP, ASM or the compiler.

**The resource-aware simulation (§5.2, Figure 4).** It is defined as
`Sim_R := νG. µL. F_R(G, L)`.

- **Matched events go through `G`.** These are `GetVar(x)`↔`Load(a_x)`,
  `SetVar(x,w)`↔`Store(a_x,w)`, step↔step and UB↔Exit. The greatest fixed
  point allows unboundedly many of them.
- **Everything else goes through `L`.** This covers silent steps and the
  target's register traffic, which has no source counterpart (the source
  "stutters"). The least fixed point bounds each stretch between matched
  events, so the target cannot do bookkeeping forever.
- **Resources travel with the steps.** Each matched pair lends
  `Cell(x) := ∃w. Auth_x(w) ∗ a_x ↦ w`. The *source authority* of `x`
  agrees with the client's points-to `x ↦ v`, so the target cell holds the
  same value. A register step needs the register's ownership and returns
  it.

The relation is closed under bind and iteration. Iteration needs a
well-foundedness condition: the source loop cannot silently restart
forever (Lemma A2.3).

**WP-preservation (§5.3, Theorem 1).** The theorem reads
`Corr_c ∗ WP_IMP(c, Φ) ⊢ wpi T(compile(c))(0) {Corr_c ∗ Φ(tt)}`.
`Corr_c` owns the cells of `c`'s variables and the registers of its
compiled code, and nothing that ranges over the whole store or memory. So
the target frame rule keeps any other cell. Points-to assertions in `Φ` can
be *extracted* to target points-to, as in
`x ↦ v ∗ Cell(x) ⊢ a_x ↦ v` (Lemma A3). An arbitrary assertion cannot,
which is why the theorem returns `Φ` together with `Corr`.

**Separate compilation (§6, Appendix C).** IMP and ASM gain modules,
`x := call f(a)`, and an `acall` instruction. Calls are `FnCall` events,
resolved by `interp_mrec` over a function table. A contract is a pre/post
pair with a caller-chosen witness, and a context `Γ` maps names to
contracts. The results:

- **Lemma C4.** An open simulation relates each function to its
  compilation. Calls stay related events.
- **Lemma C5.** A linking law: pointwise-related resolvers give related
  closed programs.
- **Theorem 2.** It derives each compiled function's **target contract**
  `⟦γ⟧ = ⟨Corr ∗ LocalsAt(W) ∗ pre, post ∗ LocalsAt(W) ∗ Corr⟩` from the
  function's source proof.
- **Theorem 3 item 2.** Linked compiled modules satisfy the WP proved
  against contracts only. Löb induction discharges the mutual assumptions,
  with the resolver's step at each call as the guard.
- **Case study.** Two modules whose mutually recursive functions pass
  ownership of a shared counter (§6.4).

**Limitations the authors state (§8).**

- The calling convention lets a callee clobber the *whole link-wide
  register pool*.
- ASM has **no activation records**. A local is one shared memory cell, and
  the resolver saves and restores it around calls, which is not proved
  against a stack semantics.
- The correspondence is identity per cell. A value relation `ρ` and a
  location map are future work. Register allocation would need a location
  map that depends on the program point.
- No optimisation, and no adversarial target contexts.

---

## 2. Where Heather already stands

| Paper | Heather | Where |
| --- | --- | --- |
| ITree denotation of source and target | `Source::denote(args) : Program<…>(Events::linux())`. The target is the x86 machine itself, not a target tree | `lib/native/native_source.hthr`, `lib/std/os/linux/linux_x86_64_sim.hthr` |
| Target logic = generic `wpi` over target events | `Wp`, a computed weakest precondition over `Asm` items, with views and `Contract`/`Callee` tables | `lib/std/os/linux/linux_x86_64_wp.hthr` |
| Transfer interface between different event signatures | `ITree::Sim`/`SimK` over a `TraceMap(E, F)` (commands forward, answers mapped) plus a `Contract` | `lib/std/itree/itree_sim.hthr` |
| `νG. µL`: unbounded matched events, bounded stutter | Machine side: `Sim` is closed backward under finite `LinuxSteps`, so target bookkeeping between syscalls is a finite run. Tree side: `Eutt`'s constructors carry finite drop counts `nl`/`nr` | `linux_x86_64_sim.hthr`, `lib/std/itree/coitree_eutt.hthr` |
| Closure under bind and iteration | `ITree::sim_bind`, `simk_bind`, `sim_iter`, `simk_iter`. Loops are related at the same fuel, so no well-foundedness side condition is needed | `itree_sim.hthr` |
| Compiler simulation by induction on the command | `Stmt::emit_runs`, by induction on the statement. `Repeat` is by induction on loop fuel | `lib/native/native_compile_correct.hthr` |
| Target WP in continuation form | `Target::Runs`: from every placed environment, the code runs as `bind(s.denote, k)`, given `k`'s claim at the end and at every exit. `Callee::Returns` has the same continuation form | `native_compile_correct.hthr`, `linux_x86_64_wp.hthr` |
| State correspondence `Corr_c`, per variable | `Target::Placed(env, m)`: the region's bytes hold the *whole* `Env` (`Layout::Keeps`), plus the stack facts | `lib/native/native_compile_region.hthr` |
| Register ownership `RegOwn(X_c)` | None needed. Statement code passes nothing in registers between statements (`native-compiled-code-shape`), and leaf contracts are over `Gprs` | `native_compile_leaf.hthr` |
| Frame rule at the target | None. `Contract::Runs` asks `e.memory = s.memory`. Footprints are open issues: `wp-proved-memory-contracts`, `wp-view-separating-product` | `linux_x86_64_wp.hthr` |
| Contracts for calls; derived target contract per function | Pure callees: the S4 lowering's theorem *is* the `Proved` contract (`compiled_returns`). Effectful procedures: inlined at build, deferred | `lib/native/function_ir/function_ir_compile.hthr`, plan §7 |
| Linking by `interp_mrec` | Not built. `mrec` is named as procedures' denotation (effect-source design §9) | `docs/native/native-effect-source-design.md` |
| Mechanised in Rocq + Iris | Kernel-checked Heather, with no separation logic and no step-indexing. Partiality is by fuel-cut trees | — |

Two parts of the table deserve a sentence each.

**`Target::Runs` is already a target WP.** The paper's point (§5.3, after
Example 2) is that the *form* of the conclusion matters. A target WP
composes with further target reasoning, and a behavioural statement does
not. Heather's statement claim already has that form. It quantifies over
the continuation `k` and asks only that `k`'s claim hold wherever the
statement ends. So `Then` is `bind_assoc` and `Repeat` takes the test and
the JMP back as its continuation. What it does not have is a small
precondition: `Placed` is the whole region.

**Heather's trees carry no internal state.** IMP's tree has a `GetVar` and
a `SetVar` per variable access. That is why the paper needs a ghost
authority per variable to correlate a source event with a target load. In
Heather's source, `Env` is a value threaded through `denote`. The tree's
only events are Linux's. So the compiler's simulation never matches an
internal event, and the correspondence is a plain function (`Keeps`). §5
returns to this.

---

## 3. Why the closed-program route is enough now

The paper's Theorem 1 quantifies over *every* source postcondition `Φ`
proved in the source logic. Heather's specification of a program is a tree.
`cat_implements` proves cat's source simulates `tr_spec` up to a
continuation (`SimK`), and the compiled program inherits any refinement
through `Program::sim_refines` and the trace bridge (`sim_run_sends`). For
a closed program those two routes prove the same facts, up to what each
logic can state:

- **What the client gets.** Paper: a target WP whose postcondition, read
  through `Corr`, is `Φ`. Heather: `SimProgram` at every fuel. Every finite
  run Linux can produce is a trace of the source tree.
- **What a spec is.** Paper: an Iris assertion over the store at exit,
  given ownership. Heather: a tree, with refinement between trees.
- **What carries to the target.** Paper: points-to on variables the code
  uses (Lemma A3). Heather: everything a trace can observe, which for a
  Linux process is its syscalls and exit status.

For a process whose only observable is its syscall trace, the second
column is the whole story. No client reads the data region after the
process exits, and no other code shares the address space. That is the
case for every tool in plan §2.

---

## 4. Where it will matter, and what to adopt then

WP-preservation earns its keep when compiled code has a *client that is
also code*. Heather has four such futures, all open or deferred:

1. **Procedures that make calls** (plan §7; program-logic design §10
   item 2; effect-source design §9: "a later `Stmt` constructor … denote
   by `mrec`, and their code enters by a `Proved` contract whose post is a
   `Sim`").
2. **A compiled function as the callee of a `Wp` program**
   (`wp-callee-from-lowered-function`).
3. **Leaves that spill or call**, which enter as `Proved` items with
   memory (`wp-proved-memory-contracts`, on the path of
   `native-compile-wider-leaves`).
4. **Heap allocation** (`hih-memory`). Compiled code will then share the
   address space with an allocator's state.

For these, the paper gives a concrete and checked recipe. Five pieces fit
Heather:

- **Derive the target contract and never prove it per procedure
  (Theorem 2).** The compiled procedure's `Callee` contract should be an
  instance of `Stmt::emit_runs` for its body, read through the
  correspondence, just as the pure `Proved` contract is an instance of
  `compiled_returns`. Minus's 2026-10-21 direction already asks for this:
  "a compiler proved once, not per-program hand proofs". The paper is
  evidence that it extends across calls without per-function proof.
- **Use a per-slot correspondence, so the footprint is what the code
  uses.** Today `Placed` is "the region holds `env`". The paper's `Cell(x)`
  says to split it into one conjunct per slot or buffer, `Keeps_S(env, v)`
  over a set `S`, with a frame clause: the region's bytes outside `S`'s
  cells are unchanged. Then a procedure's contract owns only its slots,
  and a caller keeps the rest by framing. Heather has no separating
  conjunction, so the frame is relational ("agrees outside"), as
  `lib/std/machine/memory.hthr`'s `Agrees` and the open
  `wp-view-separating-product` already plan. This piece is the expensive
  one: every `goes_*` rule would carry the frame clause. Price it in the
  first procedures round, not now.
- **Scoped contracts for the caller's locals (`Call-Scoped`, Appendix
  C.2).** The caller lends its locals at known values, and the callee
  returns them unchanged except the result slot. With a real stack frame
  per activation, Heather gets this from the frame discipline, where the
  paper gets it from the resolver's save and restore. The contract shape
  (`LocalsAt(W)` lent and returned) is still the right statement.
- **A clobber set per procedure, not per link.** The paper's limitation
  (§8: "target-level clients cannot keep values in registers across
  calls") comes from one register pool for the whole link. `Callee`'s
  post is a relation over states, so it can say which registers survive.
  This matters as soon as `native-compiled-code-shape` keeps words in
  registers.
- **Recursion through contracts by fuel, not Löb.** Theorem 3 item 2
  discharges mutually recursive contracts by Löb induction, with one later
  per call. Heather's trees are cut at fuel, and `mrec` unfolding a call
  can consume fuel. So the same circularity should become induction on
  fuel, the way `simk_iter` indexes its invariant by fuel left. That is a
  claim to check, not a result: whether `mrec` over Heather's fuelled
  `Program` spends fuel per call is the first question of the procedures
  round.

The paper's future-work item on **register allocation** ("a location map
that depends on the program point") is the same observation
`native-compiled-code-shape` makes from the other side. Keeping words in
registers between statements means `Placed` must say which registers hold
which words at each point, so the correspondence varies along the code.
The value relation `ρ` already exists in Heather: `Keeps` reads a word
through `word_in`, which is a relation between a slot's bytes and a
`BitVec(64)`, not identity on cells.

---

## 5. What not to adopt

**Iris, ghost state and step-indexing.** The paper needs them for three
jobs:

- an authority/fragment split, so that the client and the simulation can
  each hold part of a variable;
- the later modality, for loops and recursion;
- fancy updates, for the matched write.

Heather's correspondence is a plain function from slots to bytes, so the
first job never arises (§2). Fuel does the second, consistent with
Heather's partial-correctness reading. The coinductive library
(`coitree`, `Eutt`) is the route to liveness, not guarded recursion. The
third is an artefact of ghost state. A separation logic in Heather, if it
comes, belongs to `hih-memory` (roadmap) and the Rust area, which names
"separation-logic approaches" as prior art to read. It should be designed
there, for heap and ownership, not imported to state compiler frames,
which relations already state.

**Internal state as tree events.** Design §10 item 6 decided that external
effects are tree events and internal ones are FunctionIR state edges with
pure semantics. The paper shows the price of the other choice: a
per-variable event forces a per-variable ghost correlation, and the
simulation must interleave register bookkeeping with matched internal
events. It also shows what that choice buys, which is a source-level frame
rule for free (`{x ↦ n} M {x ↦ n+1}` frames `y ↦ 0`). Heather's analogue is
a fact about `Stmt::denote` on `Env` ("the statement's result `Env` agrees
with its input outside its writes"). It is a lemma per construct, needed
only when the procedure contracts of §4 need it.

**The resolver's save and restore.** That is a stand-in for a stack, and
Heather already has the stack: S4 lowers functions with a real frame
(`Site::Returns`), argv is read at RSP since round 6, and mapping the
process stack region is `io-image-process-stack`'s. The paper's §8 names
this exact gap as unproved on its side.

**A bespoke simulation per language pair.** The paper's own future work
wants a "parameterized resource-aware ITree relation, in the style of
eutt, rutt or xrutt", proved once. Heather's `ITree::Sim` over a `TraceMap`
is already that for trees. The machine-side `Sim` is one relation for
every program. Nothing to adopt here. If anything, Heather is ahead.

---

## 6. What Heather's experience says back

- **The target can be the machine, not a target tree.** ASM in the paper
  is itself an ITree denotation with register and memory events, so both
  sides of the simulation are trees. Heather's target is an x86 state
  stepped by fetch and decode, and `Sim` relates a tree to that machine
  directly. One layer fewer to trust, but the stutter bound comes from the
  machine's own finite runs, not from a `µ`.
- **Fuel removes the iteration side condition.** The paper's loop rule
  needs "the source loop cannot silently restart forever"
  (well-foundedness of `i' ≺ i`). Heather's `sim_iter` relates two loops
  at the same fuel, so a silent restart costs fuel and the side condition
  disappears. The price is that liveness is not stated, which plan §7
  accepts.
- **Continuation form serves the compiler proof, not only clients.**
  The paper uses its target WP form to compose compiled modules. Heather
  adopted the continuation form (`Target::Runs`, `Callee::Returns`) for a
  different reason: it lets `Then` be `bind_assoc` and a loop's back edge
  be the body's continuation, so the compiler proof is one induction. The
  two motivations meet: the form a compiler proof wants is the form a
  linker wants.
- **The cost to watch is kernel fuel, not proof size.** The paper reports
  no cost figures. In Heather, the analogous statements are checked by
  kernel evaluation under per-declaration fuel, and the walls met were
  certificate size and depth (`docs/kernel/native-depth-budget-design.md`, and
  round 7's one-`refl` certificate statements under fixed kernel fuel).
  A per-slot correspondence (§4) adds
  conjuncts to every `goes_*` rule. Before adopting it, a round should
  measure what that does to the gate.

---

## 7. Smaller observations

- The paper's adequacy result (Corollary C1) stops short of a pure
  statement about final states, because Iris adequacy is not mechanised
  there. Heather's chain from compiled program to Linux runs is complete
  and kernel-checked: `SimProgram`, then `sim_run_sends`, then the ELF
  theorem (`Source::elf_runs`).
- UB↔Exit is the paper's choice: a target exit may match source undefined
  behaviour, which the source WP excludes anyway. Heather's source has no
  undefined behaviour to match. What the compiler cannot place it refuses
  at build time (`Source::compile` returns `None`, with a numbered refusal
  in `native_compile.hthr`), so the theorem is only ever about code that
  exists.
- The authors' footnote convention (blue sans-serif for source, red bold
  for target) is a good one for design notes that mix both sides. Heather's
  docs mostly disambiguate by name (`src`, `t: Target`), which works in
  plain text.

---

## 8. Follow-up

Filed:

- `issues/native-procedure-contracts.md` (`heather-in-heather`): when
  procedures arrive, give each compiled procedure a `Callee` contract
  derived from its source contract by `emit_runs`. The contract has a
  per-slot footprint, scoped locals and a per-procedure clobber set. A
  linking theorem discharges recursion by fuel. The paper's shared counter
  (§6.4) is the control. It is deferred with procedures (plan §7) and is
  not on `hih-tools`.

Logged:

- `issues/wp-proved-memory-contracts.md`: the paper's target contracts
  are `Corr ∗ pre` with a per-cell footprint. That supports the
  view-relative footprint the issue's 2026-10-24 log proposes.
- `issues/native-compiled-code-shape.md`: register-resident words need a
  correspondence that depends on the program point. The paper names the
  same need for register allocation (§8).
- `issues/x86-call-memory-footprints.md`: the implementation its log
  records (`WritesOnly`, `CallMemoryPolicy`, `NativeIntegerCallContract`)
  is no longer in `lib/` or `crates/`. It went with the per-function call
  path in the burns, and survives only under `probes/` and in older docs.
  Its live successors are `wp-proved-memory-contracts` and
  `native-procedure-contracts`.

Not filed, for want of a customer: a source-level frame lemma for
`Stmt::denote` (§5), wanted only by procedure contracts, and a per-slot
`Placed` for today's whole-program compiler (§4), whose cost should be
measured in the round that needs it.
