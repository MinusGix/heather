# Interface definitions: what a client's proof may unfold

Design for `issues/interface-definitions.md`, round P2 of
`docs/compiler-milestones-proposal.md`. §6.3 there settles the idea and
Minus settled the opt-in question (decision 5, 2026-10-31: `interface fn`
per definition, not a default). This note answers what §6.3 left open for
this piece, the parts the P1 design round (`issues/proof-modularity-design.md`)
would otherwise own: the surface, where the boundary sits, how "closed
values still compute" is decided, the escape, the generated equations, and
which elaborator routes obey it. Registries (P3) and invariant rules are
not here.

**Status: built (2026-11-02).** §9 records Minus's decisions; §11 records
what the build found that the proposal did not foresee, and the gaps it
leaves.

## 1. Surface

```heather
interface fn List::sorted_insert(self xs: List<Nat>, x: Nat) → List<Nat> {
    match xs {
        Nil => [x],
        Cons(y, ys) => if x <= y { Cons(x, Cons(y, ys)) } else { Cons(y, ys.sorted_insert(x)) },
    }
}
```

- `interface` is a declaration flag, parsed like `meta` and `evidence`
  (`Decl::is_interface`), on `fn` only. A `theorem` is already opaque
  (`docs/have-design.md`); a `def` is nullary, so it is always closed and
  the flag would do nothing. Both are refused with that reason.
- It composes with what a `fn` already takes: `decreases`, type
  parameters, and a prefix generator (`runtime interface fn f`). The
  generator receives the declaration with the flag set and its output
  keeps it (§7).
- **A `fn` whose result is a universe (`→ Type`, `→ Prop`) is refused in
  this round.** A client reads a defined proposition's *shape*: `h.left`
  on `h: I.Has(x)` and a `match` on it need the body's `Σ`. Withholding
  it would turn every such projection into a refusal or an equation cast,
  and that is a different design (it is where `omega-unfolds-defined-propositions`
  and the registries meet). The refusal says this and names the issue it
  files.

## 2. The boundary

The defining module is the Ψ suffix the elaborator is committing: every
binding it pushed while elaborating this file. Inside it an interface
`fn` is an ordinary `fn`, so its lemmas can be proved by unfolding.
Everywhere else (every importing module, and `lib/_tests` probes, which
are other modules and so exercise exactly the interface clients get) the
elaborator **withholds** its body at open arguments.

The module image records the flag per binding, so a client knows which
imported globals are interfaces without reading their source. That is an
image-format change, so the format version moves and, since 2026-11-02,
the cache key with it (`image-format-in-cache-key`).

## 3. What "withheld" means: the gluing rule

The elaborator does not reduce with its own code. Its conversion,
unification and whnf go through the kernel's evaluator over `delta_psi`
(`oracle::SemanticOracle`, `Defs::transparent`), where a global `u` is a
**glued neutral**: the head, its spine, and a lazy unfolding that is
forced only when a comparison or a shape read needs it
(`Eval::global_tm`). A sealed theorem is already handled the other way
round (`Eval::unseal`): it starts *unglued*, and only an elimination
stuck on a saturated application of it glues the proof on.

An interface global gets the same treatment with a different trigger:

- In the elaborator's worlds, `Defs` carries a **withheld set** (the
  imported interface globals). `global_tm` leaves a withheld global
  unglued, so it compares by head and spine and reads as an atom.
- When an application of it becomes **saturated** (its spine covers the
  declared parameters) and **every argument value is closed**, it is
  glued exactly as a definition is. From there it computes as today.
- **Closed** means no free local variable, decided by a walk over the
  argument values (and the global's universe substitution) that does
  *not* force them: a syntactic closure is closed when every variable its
  body uses is bound to a closed entry of its environment, and a value is
  closed when its parts are, under a node budget. **Unknown means atom**,
  as in `sealing.rs`: a spent budget, an induction hypothesis, a fold,
  codata, or a value form the walk does not open all leave the call
  withheld, so the value machine is never more permissive than the syntax
  reducer, whose test is `term_local_use(arg).bound == 0`. A substitution
  tail is no sign of a variable (every `u^δ` carries one), so tails are
  ignored. A withheld call inside an argument is not itself a reason to
  withhold: if it is closed it glues and computes in turn. A verdict over
  a huge computed argument is stated inside the defining module or under
  `unfolding` (§4). §11 lists what this test does not see.
- Each gluing of a withheld global is recorded beside the unsealing
  record (`crate::unseal`), so a declaration knows which interface bodies
  it observed (§8).

This is the reading of §6.3's "at an open argument as an atom":
`sorted_insert(Cons(y, ys), x)` is an atom even though its scrutinee is a
constructor, because `y` and `ys` are open. A proof about it cites
`sorted_insert_unfold_Cons` (§5). The alternative reading, "unfold when
the match would make progress" (Lean's smart unfolding, Coq's `simpl`),
would make that call reduce to its arm, and a client's proof would again
depend on the body.

**What this touches in the kernel crate.** `GlobalCtx` (Ψ) carries the
withheld set, `Option<Rc<Withheld>>` mapping each withheld global's
absolute index to its arity, and every `Defs` over that Ψ reads it:
`Defs::body`, `body_unshifted` and `is_defined` answer as for an opaque
global, `Eval::global_tm` leaves the neutral unglued, and `step_neutral`
glues at the saturating application (`crates/kernel/src/eval/withheld.rs`).
The syntax reducer and the syntactic δ test agree (`reduce::withheld_call`,
`step_term_frame`, `conv::delta_head_in`). A gluing is recorded on a
thread-local beside the unsealing record (`crate::withheld::record`).

**The gate withholds too** (Minus's second card, §9). The first probe
found that the elaborator never decides `refl` itself: it leaves a note
and the kernel gate decides by its own conversion (`expr.rs`,
`note_refl_mismatch`). So does every proof accepted up to conversion.
Withholding only in the elaborator would therefore change almost nothing,
neither robustness nor cost. The gate checks a client module's
declarations under the same set (`gate_bodied` takes
`psi.withholding(delta_psi.withheld)`). This can only refuse more, never
accept more, since a gluing unfolds the body ordinary δ would; the gluing
code is now part of the trusted check. The withheld set is mixed into the
verdict cache's check key (`crates/cache`, `identify`), so a verdict
reached under one boundary is never replayed under another.

**Which routes obey it.** The set lives on Ψ, so every `Defs` built over
`delta_psi` reads it, whichever constructor builds it: the semantic
oracle's worlds derived from `delta_psi`, and with them conversion,
unification, `whnf`, `whnf_tm`, instance search, `decide`/`trivial` and
every Heather tactic through its host requests, and the other direct
`Defs::transparent` sites (`readback.rs`, `wf.rs`, `sealing.rs`,
`host.rs`) when they read `delta_psi`. Boxing (§7) reads declarations, not
Ψ. §11 lists the worlds that do not take the set yet.

## 4. The escape: the `unfolding` clause

```heather
theorem client(xs: List<Nat>, x: Nat): xs.sorted_insert(x).length() = Succ(xs.length())
    unfolding List::sorted_insert
{
    …
}
```

A declaration clause after `decreases`: this declaration, elaborated and
gated, does not withhold the named interface definitions (`unfolding f,
g` for several). The proposal had a block statement `unfold f;` scoped to
the rest of a block. That cannot work once the gate withholds too (§3):
the gate checks a declaration as one term, so a boundary that moved
part-way through a body would be a boundary the gate cannot see. The cost
and the dependence on the body stay visible at the declaration that pays
them. A name that is not an interface definition is refused (`… is not an
interface definition`).

Outside `unfolding`, a gate refusal over a term that mentions a withheld
global says so (`interfaces.rs`, `withheld_note`):

```
error: the kernel rejected `client`: NotConvertible. …
note: `List::sorted_insert` is an interface definition of `list`, so its body
      is withheld here at open arguments: cite `List::sorted_insert_unfold_Nil`,
      `List::sorted_insert_unfold_Cons` or a lemma about it, or declare the
      proof `unfolding List::sorted_insert` (docs/interface-definitions-design.md §4)
```

That note is the usability half of the round; without it a client sees a
plain mismatch where yesterday's proof went through.

## 5. Generated equations

Every interface `fn` gets its unfolding equations beside it, as ordinary
theorems in its module, elaborated and gated there before the withheld set
applies (so clients cite them like any lemma, `rewrite` uses them, and
P3's registries can list them):

- `f_unfold(x̄): f(x̄) = body` when the body does not call `f`, by `refl`.
  For a `decreases` function the companion it already gets
  (`docs/decreases-unfolding-design.md`) is reused, not doubled. A
  structurally recursive body gets **no** `f_unfold`: at open arguments
  `f(x̄)` reduces through the recursor, whose arm reads the induction
  hypothesis, not `f`, so the equation is not `refl` and the generator
  does not invent a proof.
- When the body is a top-level `match` on one parameter of a declared
  inductive type (or `Nat`), one equation per arm whose binders are all
  variables, `f_unfold_<Ctor>(…): f(…, Ctor(ȳ), …) = arm`, named by the
  constructor as written (`sorted_insert_unfold_Nil`,
  `sorted_insert_unfold_Cons`). Each is `refl` in the module: the match
  reduces on a constructor scrutinee, and the self-call's recursor reduct
  is convertible with `f(ȳ)` by δ. The arm's own mentions of the
  scrutinee are replaced by `Ctor(ȳ)` and its self-calls are qualified.
  Nested matches and guards stay in the right-hand side; a client splits
  them with the arm equation and its own case analysis.

Wildcard arms and arms with nested patterns get no per-arm equation in
this round; `f_unfold` covers a non-recursive body.

## 6. What still computes

- `[3, 1].sorted_insert(2) = [1, 2, 3]` by `refl` outside the module: the
  call is saturated at closed arguments, so it glues and runs.
- A closed verdict `b = True` whose `b` calls interface functions at
  closed arguments, the `docs/proof-patterns.md` §1 shape, is unchanged.
- Comparing two separately computed closed values still unfolds both in
  lockstep, so that §1 rule stays. What changes is the open side: a goal
  over `f(x)` with `x` a parameter no longer spells `f`'s body, so the
  goal-spelling growth that §1's "read a compiler's promise off at an
  abstract output" and §2's computed-binder rule warn about stops at the
  boundary for interface functions.

## 7. What is not affected

- **Boxing.** A `runtime fn` setup reads the declaration it is given (a
  prefix generator receives the `Decl`) and boxes code through the pull
  API. That is intensional analysis, not conversion in a proof, so
  `runtime interface fn` is still compiled and checked by its discipline.
- **Evaluation in `heather run` and reflection**: `Defs::transparent`
  over the real Ψ.

## 8. Early cutoff

A client whose elaboration never glued `f` (§3's record) did not observe
`f`'s body, only its type and its equations' statements. That is the
observation set early cutoff wants (`docs/module-interface-cutoff-design.md`),
and since the gate withholds too (§3) it is the gate's observation set as
well: a body edit can change a client's acceptance only through a closed
call, which glues and is recorded.

**Measured (2026-11-02): the boundary is not used yet.** A two-module
probe: `dependency` declares `interface fn twice` by a match on `Nat`, and
`consumer` proves `twice(Succ(k)) = Succ(Succ(twice(k)))` by citing
`twice_unfold_Succ`. Editing an unrelated plain `fn` in `dependency`
replays the consumer's theorem (`1 declaration replayed after an edit`).
Editing `twice`'s `Zero` arm, which leaves the cited equation's statement
unchanged, re-elaborates and re-gates the consumer (`0 declarations
replayed`). The slice replay counts the consumer as observing `twice`'s
binding, body included, because the statement mentions `twice`. Using the
boundary means counting a withheld global by its type alone unless the
gluing record says it was glued; that is
`issues/interface-body-early-cutoff.md`. An edit that changes an arm
changes that arm's equation's statement, so clients citing it are
re-checked either way, as they should be.

## 9. Decisions

1. **Where withholding lives** (§3): a withheld set on the kernel's Ψ,
   read by every `Defs`, with gluing at a saturated closed application
   (Minus, 2026-11-02). The alternative, dropping bodies from `delta_psi`
   and retrying a failed comparison at full transparency, was coarser,
   paid every failed comparison twice and gave no gluing record.
2. **The gate withholds too** (§3), the build's finding and Minus's
   second card: recommended because `refl` and every proof accepted up to
   conversion are decided by the gate, so an elaborator-only boundary
   would neither make client proofs robust nor save the conversion cost.
   The alternative kept the gate transparent and taught the elaborator to
   check `refl` itself. *Built as recommended; the card is open at the
   time of writing, and backing it out is `gate_bodied` and the cache key.*
3. **Closedness** (§3): deep closed with a budget, unknown means atom.
4. **Names and smaller choices**: `interface fn`; the `unfolding f`
   declaration clause (§4, replacing the proposal's block statement);
   `f_unfold` and `f_unfold_<Ctor>` (§5); universe-valued interface
   functions refused this round.

## 10. Build

1. Parser flag and refusals (§1), `Decl::is_interface`, the `unfolding`
   clause (`Decl::unfolding`), the tree-sitter grammar and inventory.
2. The registry: `crates/elab/src/interfaces.rs` keeps each interface's
   module, arity and equations; a `DeltaEvent::Interface` journals it into
   the module image (format bumped, so the cache key moves with it).
   `refresh_delta_psi` sets the withheld set to the interfaces of *other*
   modules not named by the current declaration's `unfolding`.
3. The kernel's withheld set, gluing and record (§3); the gate takes the
   set and the verdict cache keys on it.
4. Equation generation (§5) and the refusal note (§4).
5. Probes in `lib/_tests/std/num/float/interval_tests.hthr` (another
   module, so they see the interface): open-argument refusals under
   `// expect-error(kernel):` with the note's text, at a constructor
   scrutinee, in a checking position (a lemma's statement over the open
   call), and at a neutral scrutinee (`npow` at `Succ(k)`); the same goals
   closed by the equations and by `unfolding`; closed `refl` verdicts,
   including the interval checker's `lt_search`, which reaches the
   interface functions through recursive helpers; `unfolding` of a
   non-interface refused.
6. The migration: `Interval::neg`, `add`, `sub`, `mul` and `npow` in
   `lib/std/num/float/interval.hthr` are interface definitions. Of their
   clients, two proofs in `creal_interval.hthr` read a body at open
   arguments (`recip_bnd_has_real` leaned on `neg` at `Bnd(lo, hi)`,
   `npow_has_real` on `npow` at `Zero` and `Succ(k)`) and now cite the arm
   equations through `rewrite`; one probe (`whole_absorbs`, at an open
   precision) cites `add_unfold_Whole`. Everything else went through
   unchanged: the clients already reasoned through the `*_has` lemmas.

## 11. What the build found, and what it leaves

- **Closedness has to force.** The first walk classified arguments without
  forcing them, and refused every closed verdict whose interface calls sit
  inside a recursive helper (`IntervalExpr::lt_search`): there the
  arguments are induction hypotheses and calls in flight, which only
  forcing can classify. Forcing is what the call would do anyway once it
  reads them. A binder's body is read as syntax, and the environment
  entries it uses are forced like arguments.
- **The walk visits each node once.** A real number's closures capture
  the same computations many times over; walked as a tree, the closed
  `sin`/`cos` verdicts of `trig_real_tests` spent the node budget and were
  refused. A visited set makes the walk linear in the shared graph.
- **`refl` is the gate's** (§3, §9.2).
- **Not withheld yet**: the gate's other entry points (generated
  definitions, quotation, well-founded probes) and replay, and the
  elaborator's `goal_oracle` and `committed_oracle` worlds; only
  `delta_psi`, the worlds derived from it, and `gate_bodied` take the set.
  Each is a place where a client could still see a body; none can make
  the kernel accept more.
- **Argument syntax holding a metavariable or a goal-world global** is not
  recognised as open by the syntax reducer's test; the value walk sees a
  stuck head and answers open.
- **The refusal note** looks at the globals the refused statement and
  proof mention, and at those their statements mention, one level deep.

