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

**Status: proposed.** §9 lists what Minus decides before the build.

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
- **Closed** means: no free local variable, no metavariable, and no
  withheld application inside, found by a walk over the argument values
  that forces what it visits, under a node budget. **Unknown means
  atom**, as in `sealing.rs`: an argument too large to classify within the
  budget leaves the call withheld. The budget is generous next to the
  literals a verdict is stated over; a verdict over a huge computed
  argument is stated inside the defining module or under `unfold` (§4).
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

**What this touches in the kernel crate.** `Defs` gains the withheld set
and `global_tm` and the elimination path gain the gluing test. The
trusted check never sets the set: the gate calls `Defs::transparent` over
the real Ψ as now, so what the kernel accepts is unchanged. Withholding
only removes δ-steps from the elaborator's conversion, which is the
kernel's conversion with fewer unfoldings, so anything the elaborator
accepts the gate still accepts. §9 asks Minus whether this is the right
place (the alternative is an elaborator-only retry, which is worse).

**Which routes obey it.** The semantic oracle is the choke point: its
worlds (`semantic_oracle`, `goal_oracle`, `committed_oracle`) take the
set, and everything built on them (conversion, unification, `whnf`,
`whnf_tm`, instance search, `decide`/`trivial`, and every Heather tactic
through its host requests) inherits it. The other direct
`Defs::transparent` sites are `readback.rs`, `wf.rs`, `sealing.rs`,
`host.rs` and `function_ir_source/program.rs`; the build reads each and
records in this section whether it is a proof-facing read (takes the set)
or an intensional one (does not, as boxing in §7).

## 4. The escape: `unfold f;`

```heather
theorem client(xs: List<Nat>, x: Nat): xs.sorted_insert(x).length() = Succ(xs.length()) {
    unfold List::sorted_insert;
    …
}
```

A block statement, like `let`: from that point to the end of the enclosing
block, `f` is not withheld in this declaration (`unfold f, g;` for
several). It is scoped, so the cost and the dependence on the body are
visible where they are paid. A Heather tactic called after it runs in the
same world. Outside any `unfold`, a conversion that fails with a withheld
application on either side says so:

```
error: cannot convert … with List::sorted_insert(Cons(y, ys), x)
  note: List::sorted_insert is an interface definition; cite
        List::sorted_insert_unfold_Cons, or write `unfold List::sorted_insert;`
```

That note is the usability half of the round; without it a client sees a
plain mismatch where yesterday's proof went through.

## 5. Generated equations

Every interface `fn` gets its unfolding equations beside it, as ordinary
theorems in its module (so clients cite them like any lemma, `rewrite`
uses them, and P3's registries can list them):

- `f_unfold(x̄): f(x̄) = body`, always. For a `decreases` function this
  is the companion it already gets (`docs/decreases-unfolding-design.md`),
  not a second one. For a structural one it is `refl`.
- When the body is a top-level `match` on one parameter, one equation per
  arm, `f_unfold_<Ctor>(…): f(…, Ctor(ȳ), …) = arm`, named by the
  constructor as written (`sorted_insert_unfold_Nil`,
  `sorted_insert_unfold_Cons`). Each is `refl` inside the module for a
  structural function (the match reduces on a constructor scrutinee, and
  the self-call's recursor reduct is convertible with `f(ȳ)` by δ), and
  `f_unfold(…)` at the constructor for a `decreases` one. Nested matches
  and guards stay in the arm's right-hand side; a client splits them with
  the arm equation and its own case analysis.

The equations are generated in the defining module, so their proofs are
the one place the body is read, and the kernel checks them like any
theorem. Arms with a wildcard pattern get no per-arm equation in this
round (the whole `f_unfold` covers them).

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

- **The kernel gate**: full transparency, unchanged (§3).
- **Boxing.** A `runtime fn` setup reads the declaration it is given (a
  prefix generator receives the `Decl`) and boxes code through the pull
  API. That is intensional analysis, not conversion in a proof, so
  `runtime interface fn` is still compiled and checked by its discipline.
- **Evaluation in `heather run` and reflection**: `Defs::transparent`
  over the real Ψ.

## 8. Early cutoff

A client whose elaboration never glued `f` (§3's record) did not observe
`f`'s body at all, only its type and its equations' statements. That is
the observation set early cutoff wants
(`docs/module-interface-cutoff-design.md`). The kernel gate still unfolds
`f` freely while checking the client, so a body edit can still change the
client's gate cost, never its acceptance unless the edit changes a closed
value the client computed (and then it was glued and recorded). Whether
images can skip re-elaborating a client on an interface body edit is
measured on the migrated module and recorded here, not promised.

## 9. Decisions for Minus

1. **Where withholding lives** (§3). Recommended: a withheld set on the
   kernel's `Defs`, set only by the elaborator's oracle, with gluing at a
   saturated closed application (the `unseal` mechanism, a new trigger).
   It edits `crates/kernel` without changing what the kernel accepts.
   The alternative keeps the kernel crate untouched: drop the bodies from
   `delta_psi`, and when a conversion fails with a withheld call on a side,
   retry the whole comparison at full transparency if that call is closed.
   It is coarser (the retry unfolds the open calls too), pays every failed
   comparison twice, and gives no gluing record for §8.
2. **Closedness** (§3): deep closed with a budget, unknown means atom,
   versus unfolding whenever the match would make progress. Recommended:
   deep closed, the reading of §6.3.
3. **Names and smaller choices**, recommended unless Minus objects:
   `interface fn` spelling; `unfold f;` as a scoped block statement;
   `f_unfold` and `f_unfold_<Ctor>`; universe-valued interface functions
   refused this round.

## 10. Build and acceptance

1. Parser flag and refusals (§1); image flag and format bump (§2).
2. `Defs` withheld set, gluing at saturated closed applications, the
   gluing record (§3); the oracle worlds take the set; each other
   `Defs::transparent` site classified.
3. `unfold f;` and the withheld-mismatch note (§4).
4. Equation generation (§5).
5. Probes in `lib/_tests` (another module, so they see the interface):
   open-argument refusals under `// expect-error:` with the note's text;
   the same goals closed by the equations and under `unfold`; closed
   `refl` verdicts; an open element type and a checking position, per
   `docs/testing-generated-terms.md`; `runtime interface fn` still boxes.
6. Migrate one module. Candidates: `lib/std/num/float/interval.hthr`
   (`Interval::add`, `mul`, `npow` and the bound helpers, whose clients in
   `creal_interval` and the interval tactic reason at open intervals) or
   the x86-64 layout lemmas. Measure with `--timings` (conversion columns
   through `scripts/timings`) and `scripts/perf ab --source-patch`; record
   the §8 cutoff observation.
7. Retire or narrow one `docs/proof-patterns.md` rule, the one the
   measurement supports.
