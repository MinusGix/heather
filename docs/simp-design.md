# simp: a simplifier whose results are stated, pinned and explained

Design proposal, 2026-11-11, for `issues/simp-tactic.md` (milestone
tac-general). Nothing here is built. §0 lists the decisions that are
Minus's; the rest argues for the recommended answers.

The issue already fixes what a simplifier is: a directed rewriter to a
normal form, over a set of lemmas, with conditional lemmas, unfolding and a
residue. This note is about where Heather's should differ from the one
Lean, Isabelle and Rocq users know, and why. The short version: the usual
simplifier is designed around a person typing as little as possible, and
pays for that with proofs that depend on a global, growing lemma set and
say nothing about what they did. The people and programs writing Heather
proofs now find text cheap and silent breakage expensive. So the design
moves cost from *maintenance and diagnosis* to *what is written down*.

---

## 0. The decisions

**Decided, Minus, 2026-11-11.** Agreed in general. (2) is amended: there
*is* a default, and it is by type. A type may associate a default set with
itself, and a call's default search includes the sets of the types its
expression mentions (`Nat`, `Int`, `List` show up everywhere, and "this
fails, no idea what we need" is the failure to avoid); §3.1. (4) as
recommended: host engine, Heather policy, and the engine moves into
Heather once tactics compile to runtime code. The failure report is
wanted, and the route a run took must be easy to see; §6.1. Build it for
relations as well, not `=` only.

1. **A non-closing `simp` states its result** (§2). The committed form of
   "simplify, then continue" names the simplified goal, and `simp` proves
   the two join. A bare residue exists for exploration and prints the
   statement to paste. *Alternative:* residual goals as in Lean, which
   waits on the goal model of `issues/proof-scripts-as-tac-blocks.md` and
   keeps the fragility.
2. **No global default set** (§3). Lemma sets are named values a module
   registers, owned by the type or theory they normalise, and a call names
   the sets it uses. *Alternative:* one `@[simp]` set, which is what makes
   proofs depend on everything imported.
3. **A set is checked when it is built** (§4): every lemma is oriented by
   the set's order, and overlaps that do not join are reported. Recommended
   as a refusal for orientation and a warning for overlaps. *Alternative:*
   check nothing and find loops at use, as the usual simplifier does.
4. **The walk and its proof are host work; the policy is Heather** (§7).
   The Rust rewrite engine already owns a memoised bottom-up walk with
   shared proofs along any relation. Lemma sets, dischargers and
   procedures are Heather values. *Alternative:* all of it in Heather over
   the tactic interface, as `grind` is, at the interpreter's cost on the
   tactic the library will call most.
5. **Relations from the first round that has sets** (§5): a set normalises
   along `=`, `↔` or a designated `≈`, by the evidence `rewrite` and
   `rel_cong` already read.

---

## 1. What goes wrong with the usual simplifier

Four things, each observed in large libraries built on one.

**The lemma set is ambient.** `simp` means "rewrite with whatever is tagged
in everything I import". A proof's meaning changes when an unrelated
module tags a lemma. Libraries answer with a convention: `simp` only where
it closes the goal, `simp only […]` elsewhere, and a tool (`simp?`) that
prints the list. The convention is the real interface; the default is a
trap that reviewers enforce by hand.

**A non-closing call hides its result.** `simp; exact h` records neither
what the goal became nor what `h` is about. When the normal form moves, the
failure is at `exact`, far from the cause, and the reader of the proof
never knew the intermediate statement at all. This repository met the same
failure today with a different tactic: a motive rung changed what three
`match` arms were asked to prove, and each broke at a line that looked
unrelated (`docs/goal-motive-synthesis-design.md` §4.5).

**Nothing says the set is a rewrite system.** Orientation is each author's
choice, termination is found by a timeout at some later use, and two
lemmas that rewrite one term two ways make the result depend on matching
order. "Normal form" is a hope.

**Failure is silence.** The simplifier fails to make progress, or makes
some and stops, and says neither which lemma almost applied nor which side
condition it could not prove.

A human author works around all four by experience. A program writing
proofs does not have the experience, does have the patience to write
everything down, and reads diagnostics literally. `issues/lemma-selection-and-search.md`
already has the principle: wide at exploration, narrow at commit.

---

## 2. Three forms, and what may be committed

```heather
// (a) closing: both sides normalise to the same term
theorem len_app3(xs, ys, zs: List<A>): (xs ++ ys ++ zs).len() = xs.len() + (ys.len() + zs.len())
    by simp(List::shape)

// (b) stated: the step is a line of a calc or a `have`, both ends written
calc {
    run(set(vals, next, sum), prog)
      = run_from(sum, rest)            := by simp(Valuation::store, [loop_finish]),
    _ = answer                         := ih,
}

// (c) exploring: prints the result; refused in `lib/`
by simp_show(Valuation::store, [loop_finish])
```

**Closing and stated calls are the same operation**: normalise both sides
of the goal's relation and compare. That is the whole trick. A stated step
does not depend on the normal form being any particular term, only on the
two written ends having the *same* one, so it survives a lemma added to
the set unless the addition breaks confluence, and §4 reports that where
the lemma is added. The written ends are what a reader wants anyway: the
complaint that started this thread's proof rewrites was that hand chains
hide the argument, and a `calc` whose justifications are `by simp(S)`
shows every intermediate statement and none of the bookkeeping.

For a goal that is not a relation, the stated form is
`have h: G' := …; by simp_from(h, S)`: `simp` normalises `G` and `G'` and
closes one from the other.

**Exploring** is how the ends get written. `simp_show` simplifies, fails
the proof, and reports through `Say` (host interface §23):

- the simplified goal, as text that parses where it is pasted;
- the lemmas used, as the pinned list (below);
- what blocked (§6).

A fix-it turns `(c)` into `(b)` mechanically. The author never has to
guess the normal form; they have to read it once and commit it.

**Pinning.** `simp(S)` reads the registered set `S`. `simp(only := [l₁, …])`
uses exactly the lemmas written, as `grind_using` does. A report always
includes the `only` list the run used, minimised, so a caller who wants a
proof that no registration can move pins it. Recommended rule for `lib/`:
closing and stated calls may name sets; nothing may use `simp_show`; a
module that a set's owner cannot see breaking (anything under
`lib/native`) pins. Unused entries in an `only` list are a warning, as a
misspelled name is already an error at a registered table
(`docs/registered-values-design.md`).

What this gives up: the two-word proof `by simp`. The call always names
what it normalises with.

---

## 3. Sets are named, owned and small

A set is a registered value (`register def`, the mechanism `mono` reads):

```heather
register def List::shape: SimpSet = SimpSet::of(
    order := SimpOrder::by_heads([name_of(List::len), name_of(List::map), name_of(List::append)]),
    lemmas := [name_of(List::len_append), name_of(List::map_append), name_of(List::append_assoc), …],
    procs := [],
);
```

- **Owned by a type or theory**, in its module, named for the normal form
  it produces (`List::shape`: appends nested to the right, `len`/`map`
  pushed to the leaves; `Valuation::store`: reads resolved against writes;
  `Regex::laws`: units and zeros of `Seq`/`Alt`). Facts live in their
  type's file; so does the statement of which way they are used.
- **Composed by the caller**: `simp(List::shape + Nat::arith_shape)`. The
  union is checked like any set (§4) the first time it is formed in a
  module, and cached with the module's image.
- **Extended only by the owner.** A client adds lemmas at the call
  (`simp(S, [extra])`) or defines its own set containing `S`; it cannot
  push a lemma into `S` from outside. So a set's contents are one
  declaration to read, and its history is that declaration's history.

A registration is a module event already, so it is in the interface digest
and dependents re-elaborate when a set changes. That is the property the
PR lane lacked for the motive rung; here it comes from the mechanism.

### 3.1 Default sets belong to types

A set registered with `default_for := name_of(T)` is `T`'s default.
`by simp()` with no set named uses the union of the defaults of every
type whose values occur in the goal: the types of the subterms the walk
visits, read from the heads' result types, not the whole import closure.
A goal about `List<Nat>` lengths gets `List`'s and `Nat`'s defaults and
nothing of `Regex`'s, wherever it is written. Naming sets adds to the
defaults; `only := […]` replaces them.

This keeps what the ambient set is good for (the common carriers work
without knowing their lemma names) and drops what makes it fragile: the
set a call uses is a function of the goal's types, a type's default is one
declaration in the type's module, and a module that tags a lemma about its
own type cannot change a proof that does not mention that type. A report
names the defaults that were included and why ("`List::shape`: `xs ++ ys`
has type `List<A>`").

Apart from the per-type defaults there is no "all sets" set. `issues/lemma-selection-and-search.md`'s
selection language can *propose* sets for a goal by the heads it mentions
(`heather search --simp-sets-for <goal>`), which is exploration.

---

## 4. A set is checked as a rewrite system

At the `register def`, in the owner's module, once:

1. **Orientation.** Each lemma's left side must be greater than its right
   in the set's order. The default order is a lexicographic path order
   from a precedence on heads that the set declares (or that is inferred
   from the lemmas and printed); a set may instead give a measure
   function and its decrease lemmas. A lemma that cannot be oriented
   (commutativity) is refused as a rule and offered the two usual homes:
   a procedure that sorts arguments (§5), or a normaliser tactic (`ring`,
   the monoid normaliser) called as a procedure.
2. **Overlaps.** For each pair of rules whose left sides unify at a
   non-variable position, both results are normalised and compared. A
   pair that does not join is reported with the term, the two results and
   the equation that would join them, stated as a lemma to prove. That is
   Knuth–Bendix completion with the completion left to the author, who is
   told exactly what to add.
3. **Conditional lemmas** are checked for orientation on their conclusion;
   their premises must be in the discharger's language (§6) or the lemma
   is flagged "fires only with a hint".

Recommended severity: orientation is a refusal (a set that may loop is not
a set), overlaps are a warning with `allow_overlap(l₁, l₂)` to record a
deliberate one. With both clean, every term has one normal form, the
closing form of §2 is a decision procedure for the set's equations, and
"`simp(S)` could not close it" means the equation does not follow from `S`
by rewriting, which is worth being able to say.

Cost: the checks are quadratic in the set and run when the set's module is
elaborated, which is an argument for small sets as much as §3's.

What it does not check: that the union of two clean sets is clean. Forming
the union re-runs the overlap check across the two (§3), and its report is
attributed to the module that formed it.

---

## 5. Relations, conditions, procedures

**Relations.** A lemma `a ≈ b` (or `P ↔ Q`) is a rule along that relation,
and a step under a context needs the context's congruence: `Respects2`,
`PreservesRelation`, the evidence `rewrite` and `rel_cong` resolve today
(`docs/equation-rewrite-design.md` §9–§11). A set declares its relation;
`=` rules may be used inside any. `Regex::laws` along `Regex::Same` and a
Kleene-algebra set are then ordinary sets, and so is rewriting along
`Eutt`.

**Hypotheses.** Equations among the goal's locals are used when asked
(`simp(S, locals)`): `x = t` with `x` a variable is a substitution, others
are oriented by the set's order and refused if they cannot be. Inside an
arm of `match h: test { … }`, `h` is such a local. `simp_at(h, S)` returns
the normalised hypothesis under a stated type, by §2's rule.

**Unfolding.** `[f, g]` unfolds those definitions where they are applied,
one δβ step each, never an `interface fn`. A definition that branches on a
test is unfolded only when the test then reduces or a rule decides it;
otherwise the call is left folded, so a residue never contains a stuck
`match`.

**Procedures.** A `SimpProc` is a Heather function from a term to an
optional replacement with its proof, keyed by head: literal arithmetic
(`norm_num`'s evaluator), argument sorting for an AC operation, read-over-
write with the key comparison decided by evaluation. Domain simplifiers
are a set plus procedures plus a discharger behind one name:

```heather
fn store_simp(extra: List<Expr>) → Tac<Proof> { simp(Valuation::store, extra, discharge := ne_by_omega) }
```

Software is cheap: a variant that is stronger for one domain is a ten-line
wrapper, not a fork of the loop.

---

## 6. Side conditions and the failure report

A conditional rule fires when its premise is proved at the instance. The
default discharger tries, in order: a local, the set itself on the premise
(depth-bounded), `decide`/`norm_num` when the premise is closed. A call
names another (`discharge := omega_goal`).

A premise that is not discharged is not dropped. The run records a
**blocked instance**: the rule, the position, the premise. The report of a
failed or exploring run lists, in this order:

1. the two normal forms and the first position where they differ;
2. blocked instances whose firing would change that position, each with
   the premise as a statement ("`Valuation::set_other` at `…` needs
   `next ≠ id`");
3. near misses at that position: rules whose left side matches up to one
   argument, with the argument (`grind`'s near-match report);
4. the equation between the differing subterms, generalised over their
   free variables, as the lemma that would close the gap;
5. on budget exhaustion, the rules fired most and, when a term repeats,
   the cycle.

Each item is a parseable statement or a qualified name. `--json` on the
checker emits the same list as data. This is the part of the design that
matters most to a program writing proofs: every failure names its next
action, which is one of *prove this premise*, *add this lemma*, *state the
other normal form*, *this is not a consequence of the set*.

### 6.1 The route

Every run can show the route it took: the sequence of steps, each with its
position in the term, the rule or procedure, the instance, and the term
before and after, in the order the engine took them, ending with the
normal form. `simp_show` prints it; a failed closing or stated call prints
the route of each side up to the first position where the sides differ,
which is usually short. The route is also the `calc` chain the run stands
for, so it can be pasted as an explicit proof where a pinned call is still
not explicit enough.

`--log-used` appends (goal heads, set, lemmas used) per successful run:
the premise-selection corpus `issues/lemma-selection-and-search.md` asks
for, which cannot be reconstructed later.

---

## 7. Where it runs, and the proof

The walk is `issues/rewrite-every-instance.md`'s: each node once, children
first, a node matched again in its rewritten form, one result per shared
node. `crates/elab/src/rewrite/relation.rs` already does this for one law
along any relation, builds each step as one shared kernel term, and leaves
missing congruence evidence as labelled obligations. A simplifier is that
walk over an indexed set, to a fixpoint.

**Recommended split.** The host gains one request, roughly
`Normalise(term, rules, unfold, budget) → (term', proof, blocked)`, where
`rules` are handles to instantiated or unapplied lemmas with their
direction. It runs the walk to a fixpoint with unconditional rules, and
returns blocked conditional instances as data. The Heather side owns the
loop around it: build the rule list from the sets, call `Normalise`, hand
blocked premises to the discharger, add the proved instances as rules,
call again (the per-node memo makes the second call proportional to what
changed), run procedures at the heads that have them, compare the two
sides, and assemble the report. Sets, orders, the overlap check,
dischargers and procedures are all Heather values and functions.

Why not all in Heather: a tactic run costs interpreter time per request
and per force, `grind` runs out of fuel on native terms after about a
thousand requests, and `simp` is the tactic `lib/native` would call on
every step of a chain. Matching every node of a large term against an
indexed set is exactly the loop that should not be interpreted. Why not
all in Rust: every policy above is something a library author changes, and
`mono`'s move from a Rust table to registered values is the precedent.

The proof is what `rewrite` produces today: `trans` over rule instances
under congruence steps, shared per node, checked by the kernel like any
term. No reflection, nothing trusted. The certificate cites only the
lemmas used and the congruence evidence, so a client of a proved theorem
does not import the tactic (`issues/tactic-only-imports.md` remains about
the import at the `by`).

Verification follows today's rule in `CLAUDE.md`: `simp` is a rewrite the
library will call, so any change to its engine re-elaborates the library.

---

## 8. Rounds

Each leaves something usable.

(Minus, 2026-11-11: build it more fully than `=` only; rounds 1 and 4
are taken together.)

1. **Engine, pinned lists, closing and stated forms.**
   `Normalise` over `rewrite`'s walk with a list of unconditional laws and
   unfolding; `simp(only := […])`; the report's items 1 and 5. Closes
   `issues/rewrite-every-instance.md`. Done when a `len`/`append` chain
   from `lib/native` is a `calc` with `by simp(only := …)` steps.
2. **Conditions and the report.** Blocked instances, the default
   discharger, `discharge :=`, report items 2–4, `simp_show` and its
   fix-it, `--json`. Done when `rt_loop`'s `Fun::post_left`,
   `Fun::post_exhausted` and `Fun::state_kept` close (the issue's target).
3. **Sets.** `SimpSet`, registration, the orientation check, the overlap
   check, union. First sets: `List::shape`, `Valuation::store`,
   `Regex::laws`. Done when those three are registered clean and the
   round-1 and round-2 proofs name sets instead of lists.
4. **Relations and hypotheses.** Sets along `≈` and `↔`, `locals`,
   `simp_at`. Done when `regex_dfa.hthr`'s `deriv_simp_same` and
   `simplify_same` are `by simp(Regex::laws)`.
5. **Procedures and wrappers.** `SimpProc`, AC sorting, literal
   arithmetic, `store_simp`, a `sets`-backed and a substitution-calculus
   instance as the mathematics milestones need them.

A bare residue as a goal (`simp; next_tactic`) is not in these rounds. If
the goal model of `issues/proof-scripts-as-tac-blocks.md` lands, it is a
small addition; §2 argues the library should rarely want it.

---

## 9. Rejected or deferred

- **One default set with attributes.** §1, §3.
- **Completion run automatically.** Knuth–Bendix can diverge and invents
  rules nobody named; reporting the unjoined pair and letting the owner
  add the lemma keeps every rule a theorem someone stated.
- **An e-graph simplifier** (equality saturation with extraction). `grind`
  is the e-graph tactic and closes goals; a normaliser wants direction, a
  small proof and a predictable result. Saturation as an *exploration*
  tool that proposes rules for a set is a possible later use of
  `lib/std/data/egraph.hthr`.
- **Reflection for the whole simplifier.** A reflective normaliser is
  right for a fixed theory (`ring`); a set that modules extend would need
  the interpreter and every rule's soundness inside the kernel's
  conversion. Per-domain reflective procedures are §5's `SimpProc`.
- **Rewriting under binders along `=` without extensionality.** The
  relation walk's binder rules (§10 of the rewrite design) apply where
  the pointwise relation has evidence; elsewhere a rule does not fire
  under a λ and the report says so.

## 10. What is built

Round 1, with relations (2026-11-11). `simp_only(r₁, …, rₙ)` and
`simp_show(…)` are term forms beside `rewrite`
(`crates/elab/src/rewrite/simp.rs`); probes are
`lib/_tests/std/tactic/simp_tests.hthr`.

- **Laws.** A proof of `a = b` or of `R(a, b)` for a designated relation,
  under any hypotheses: a named lemma, a lemma applied to some arguments, a
  hypothesis. The first law in the list with an instance fires, at every
  occurrence of that instance; then the list is tried again from its start.
- **Computation.** Before each match, a call at a constructor computes
  (`xs.len()` at `Cons`, `r.simplify()` at `Seq(a, b)`), a structural recursion
  with its recursive calls kept as calls. A definition's own equations are
  not laws to list.
- **Closing.** With no named argument the call closes the goal: both sides
  are normalised and compared, and the run stops as soon as they are one
  term, so a commuting law that would move both for ever does not.
  `then := e` proves the normal form; `using := h` normalises `h`'s
  statement and requires the two normal forms to convert.
- **Side conditions.** A law's non-dependent hypothesis is found among the
  hypotheses in scope (parameters and `let`s), or proved by
  `discharge := e`. A law whose condition is unmet is reported as blocked,
  with the condition.
- **Relations.** The relation walk crosses calls with registered
  `PreservesRelation`/`Respects2` evidence, and now inductive constructor
  values of one or two fields, with evidence at `T::C`.
- **The report** (§6, §6.1). Each refusal carries the route, one line per
  step, `law: lhs ⟶ rhs`; the laws blocked at the normal form; a loop
  at its first repeat (the goal after step *n* is the goal after step *k*),
  and the 256-step budget only behind that.

Sets and defaults: §11.

## 11. Sets and per-type defaults, as built

Round 3's sets, without the checks (2026-11-11).

- **A set** is `register def …: SimpSet = simp_default(name, name_of(T),
  [name_of(l₁), …]);` (a type's default) or `simp_set(name, […])` (named at
  a call), in `lib/std/tactic/simp_laws.hthr`'s record: a report name, the
  types it is the default of, the laws. It is written beside the lemmas,
  so each name is checked where it is in scope. `Nat::arith` and
  `List::shape` are in `simp_laws` itself (their modules sit below
  `string`); `Regex::same` is in `regex_dfa`.
- **`by simp()`** (`lib/std/tactic/simp.hthr`) walks the goal's views,
  infers each subterm's type, and takes every registered set that is the
  default of a type met (§3.1): by the global a `name_of` key denotes
  where the call is, or by name for a builtin. `extra := [h, …]` adds the
  call's own laws, tried first; `defaults := False` leaves the type
  defaults out; `by simp_with([S, …])` names sets (a defaulted parameter
  has no positional slot, so the form that takes sets by position is its
  own name).
- **The run** is the host's, asked for with `Simp(laws, goal)`
  (`docs/host-elaboration-interface-design.md` §27): the chosen sets'
  lemmas resolved to terms, then the same driver as `simp_only`.
- **The report** is the driver's, followed by one line per set used and
  the type that brought it (``tried the set `Nat::arith`: the default of
  `Nat`, which the goal has a value of``), or the statement that no type in
  the goal has a default.

Differences from §3 as proposed: sets are composed as a list at the call,
not with `+`; `only := […]` is `simp_only`, the term form; a set has no
order or procedures yet, because nothing checks or runs them.

A free function named `simp` makes `e.simp()` ambiguous wherever both are
in scope (the member-or-name rule), so `Regex::simp` became
`Regex::simplify`.

**The checks of §4, as far as running a set shows** (`by
simp_check([S, …])`, the host request `SimpCheck`). Each law's own
statement, with its binders as fresh variables, is normalised by the whole
list. A run that loops refuses the list: it has no normal form at that
law's instances (commutativity, two laws that undo each other). A run
whose two sides do not meet means another law rewrote the left side first
and the results do not join; the refusal prints the two normal forms,
which is the equation to add. A check is a theorem of `True` beside the
set (`simp_list_shape_checked` in `simp.hthr`,
`Regex::simp_regex_same_checked`), or beside the sets a module uses
together, so it is re-run when a set or a lemma changes and not at every
call.

This is weaker than §4 in three ways, each left open on
`issues/simp-tactic.md`: there is no order, so termination is tested at
each law's generic instance and not proved; an overlap that needs both
left sides instantiated (associativity against a unit) is not found, since
that is unification of the two; and nothing forces a registered set to
have its check, so an unchecked set is only caught by the loop report at a
call.

Not built: the `--json` report, unfolding by name. Known gaps: a goal a named case split left unfolded
past its relation, which is restated in a one-step `calc`
(`issues/case-split-unfolds-the-goals-relation.md`). Each step is one walk
of the goal (`issues/rewrite-every-instance.md`), and a default set is
tried law by law at each step, so a set's size is a cost at every call.

## 12. Laws between statements, as built

`P ↔ Q` as a law (2026-11-11, `crates/elab/src/rewrite/statement.rs`,
`issues/simp-iff-laws.md`).

- **The positions** are a statement's, not a term's: the goal itself, the
  operands of `∧`, `∨`, `↔`, `¬` and a non-dependent `→`, and the body of a
  `∀`, one binder down. Each is matched against the law's left side on its
  own, so two positions may be two instances and an instance may mention a
  bound variable. A position that is an instance is not walked into; the
  next step sees what replaced it.
- **The proof** is `goal ↔ next`, built from `logic`'s congruences for `↔`,
  one per former (`iff_and_congr`, `iff_or_congr`, `iff_imp_congr`,
  `iff_not_congr`, `iff_iff_congr`, `iff_forall_congr`), with `iff_refl()`
  at an operand that did not change. A closing call uses its `mpr`, a
  `using :=` fact its `mp`.
- **The left side** is matched by its shape: an application along its spine
  (`Mem(a, xs ++ ys)`), an equation side by side (`Succ(a) = Succ(b) ↔ a =
  b`), a connective operand by operand, a statement variable by the whole
  statement (`P ∧ True ↔ P`). `¬` is the call `Not(P)` as written, never a
  definition that unfolds to an implication into `False`; and a relation
  that is defined as a `↔` (`Regex::Same`) is that relation, read by §5.
- **Equations and relation steps reach the same positions.** A connective
  lowers to a record or a sum whose operands sit below the lowering's own
  binders, where the equation form's motive does not look, so before this
  an equation fired at `Mem(a, xs ++ Nil)` and not at `Mem(a, xs ++ Nil) ∧
  R`. A law that has no instance at the goal as a whole is now tried at
  each operand; where it fires, its two directions are that operand's `↔`,
  and the same congruences carry it out. This also takes an equation below
  a `∀`.
- **Sets and checks** take such laws unchanged: `List::shape` has
  `List::mem_append_iff`, the types inside a statement bring their
  defaults (a record's type arguments are now read through a field typed
  as an arrow between them, which is also why a diagnostic prints
  `Iff<P, Q>` where it printed `Iff<…>`), and `simp_check` compares the
  two sides of a `↔` law as statements.

Not reached: a statement inside a user's own predicate former. A law's two
sides have to live at one universe level.

## 13. Under binders, as built

A law whose instance sits under a binder (2026-11-11,
`issues/simp-under-binders.md`). There are three kinds of binder and each
is crossed its own way.

- **`∀`**: the body is a statement one binder down (§12).
- **`∃`**: `Exists(λ x => B(x))` holds its predicate as a value. The
  statement walk reads the λ off the record's lowering, walks `B(x)` as a
  statement one binder down, and crosses back by `logic`'s
  `iff_exists_congr` over the pointwise `↔`. Laws of every kind fire there.
- **A λ handed to a function** (`xs.map(λ x => …)`). Heather assumes no
  function extensionality, so two λs equal at every point are not equal,
  and nothing crosses a λ for free. What is true is a theorem about each
  consumer: `xs.map(f) = xs.map(g)` when `f` and `g` agree pointwise. So an
  equation that the transport finds no instance for, at a goal with a term
  under a λ, is walked as a step of the identity relation `RelId` by the
  relation walk (`Relations::identity_step_or`), which already finds an
  instance under a binder and relates the two λs by `Pointwise(RelId)`
  (`docs/equation-rewrite-design.md` §10). Every ordinary context preserves
  `RelId` with no evidence; the λ's consumer needs
  `PreservesRelation(Pointwise(RelId), RelId, λ f => xs.map(f))`, an
  `evidence theorem` beside the function. `lib/std/data/list_pointwise.hthr`
  has it for `map`, `filter`, `count`, `foldr`, `foldl`, `any_bit`,
  `all_bit`, `find`, `split_by` and `update`, each with the lemma a proof
  cites (`List::map_ext`); a step of two arguments (a fold's) is related by
  `Pointwise(Pointwise(RelId))` and crossed one binder at a time.
  `big_operator` has it for `∑`/`∏` along the carrier's relation
  (`range_pointwise`) and along `=` (`range_pointwise_eq`). A consumer
  without it is named in the report's blocked line, with the statement it
  needs.

The route spells an instance where it was found, with the walk's name for
the binder (`f(x0) ++ []`).

`by simp()` finds the default sets of types that occur only inside an
`∃`: the host's view of a value-parameterised record reads a value
argument the unifier leaves unsolved where the template applies it
(`El(?P(witness))` against `El((λ x => …)(witness))`), so `Exists(P)` views
as `Exists` with `A` and `P`, and `P` as a λ that `Open` enters.

Gaps left: a side condition of a law fired under a binder is not
discharged there; and each further consumer of a λ is one lemma and one
evidence theorem.

A call at a constructor computes to its arm with the recursive call
written as a call (`goal_combinators::recursion_at_constructor`, over the
reduct walk's refolded firing in `refold.rs`), so a law over the call
matches what is left. Two shapes used to fall through to a law that found
its instance by unfolding, which leaves the raw recursor that no source
spells: a tail call on an accumulator (`foldl`'s arm is the recursion
itself, which the check that an arm was selected read as stuck), and a
recursion on `Nat` (`range`), whose `elim_Nat` the walk did not refold
(`issues/simp-unfolded-call-loses-spelling.md`).

## 14. Unfolding by name, as built

A definition named among the laws (`simp_only(Node::step, Valuation::set_here)`)
is unfolded wherever it is called while the goal is computed: its body at
the call's arguments, the β-redexes that leaves contracted, no other
definition unfolded (`goal_combinators::simplify_goal_unfolding`). It never
fires as a rewrite and the route does not list it, as a call computed at a
constructor is not listed. The goal before and after convert, so the
unfolding costs no proof term.

What counts as a definition: a transparent global (a theorem's proof is
opaque, so a theorem is always a law) whose type's conclusion is not an
equation, a relation or a `↔`. A local function is neither a law nor
unfolded, and is refused as before. An unfolding the source cannot spell is
not taken, with one exception: a body that is a match on what the arguments
do not decide yet (`Tm::leave` on `after(64, flag).eq_bit(1)`, `loop_pass`
on its exit bit) is taken when its scrutinee spells, so the other laws can
rewrite the scrutinee until the match selects its arm. A recursive
definition's body is its recursor, never such a match, so this admits no
raw recursion.

### 14.1 What the native chains needed besides (2026-11-12, second pass)

Each of these was found by converting a chain in `rt_loop.hthr` and is
probed in `lib/_tests/std/tactic/simp_tests.hthr` or
`lib/_tests/native/runtime/rt_loop_tests.hthr`.

- **A comparison of two closed words computes.** A match whose scrutinee is
  `eq_bit` of two locally closed words (a flag read back from a written
  `Const`) is run to its constructor with a budget linear in the width, which
  the split's small budget does not reach when the words are equal.
- **A match at a literal constructor reads the fields written.** The arm
  `matched_at_constructor` selects reads a constructor's fields as
  projections out of its label's payload (`node_output(Const(64, flag, 1))`);
  when that arm does not spell, it is contracted to the fields. Only then: an
  arm that already spelled is left as it was, because contracting it changed
  what `omega` read in `CReal::archimedean`.
- **A stuck match's arms are computed and rewritten.** For `simp` only, an
  arm that ignores its constructor's payload (a `Bool` match's) is computed
  where the match is; a law's instance is searched for there as well
  (`rewrite::reachable_terms`), and an equation's step crosses the match as
  the context `λ z. match …`, which every function preserves `=` through
  (`RelationRewrite::stuck_match`).
- **β and pair projections under a function literal.** A law's instance can
  put a λ into a λ (`λ ys => out(again(ys))` at `again := λ ys => into(…)`);
  the computing step contracts those redexes and projections syntactically,
  for `simp` only.
- **An equation's step chains as `=`.** Crossing a consumer by pointwise
  evidence into the rewrite's own carrier used to ask for `Transitive` at
  that carrier (instances exist for `Nat`, `Int`, `Bool`); an equation's
  step now chains by `trans_relid_l`/`_r` at any carrier.
- **Evidence for a continuation.** `Tm::leave_pointwise` lets `simp` rewrite
  inside what a pass's continuation does.

Still open, in `issues/simp-adoption-native-gaps.md`: a law whose left side
has a variable head (`finish(LoopEnd(…))`) is not matched under a binder and
is passed applied; a side condition proved from a list membership
(`absent_mem`) has no discharger; `fuel_pass_sound`'s final chain stays,
because a `Sub` node's value computes through width casts that its proof's
own `pred` does not have.

Found by the adoption round on the native chains (2026-11-12): a law about
a definition's body (`Valuation::set_here`, about `Valuation::set`) does not
match a call of a definition that is that body (`Node::step(Move(…), v)`)
until the call is unfolded. Before this, the proof wrote the unfolding as a
`refl` equation and passed it as a law.

## 15. Computing, matching and defaults for the stream proofs, as built (2026-11-14)

Found by converting the chains of
`lib/native/crypto/sha256_stream_agreement.hthr` and
`lib/std/crypto/sha2_stream.hthr`; probed in
`lib/_tests/std/tactic/simp_tests.hthr`.

- **Laws that the computing would take away fire first.** Each step
  computes the goal; a law that fires on the goal as written and not on the
  computed goal fires before the computed goal replaces it. A law about a
  call (`Sha256::run_spec` at `Sha256::run(s).after`) is otherwise lost once
  the call computes into its body. A law that fires on both waits, so the
  pattern children the computing names (`h(a)` at a pointwise body) are
  what it meets.
- **An applied law's terms are frozen.** The application and projection
  terms of each applied law's left side (`zeroed(R, 0, 64).hash` names `R`)
  are not computed while the goal is, so the law can meet them. A call of a
  definition the call lists to unfold is not frozen: listing it asks for its
  body.
- **What computes, for `simp`.** A `decreases` function's recursion at a
  constructor is not taken (its arm is `f#body(…)`, which no law meets
  again; its `f::step` equations are the laws). A field read is taken only
  when the result spells; a field of a definition that unfolds to a
  constructor is otherwise left as the call. A conjunction's sides and an
  equation's two sides are computed (`And<a = b, c = d>` goals, a record's
  Σ, non-dependent second components), and `And(refl, refl)` closes a
  conjunction of met equations.
- **A `mut self` function is a definition.** Its result is `Mutated<S, R>`,
  which looks like a relation's carrier; a "relation" whose carrier is a
  type is a function, so the call unfolds when named.
- **Matching reaches values.** A pattern's variable under a λ (matched up
  to the bound variables), a sum's injection, a pair, a projection, or a
  constructor's label and children is matched there; a bare projection's
  key compares its kind and its pair.
- **A registered set's names resolve wherever their module is reached.**
  `name_of` spells a qualified key; the host's `Resolve` takes a key whose
  module is in the import closure, as `Lookup` already did, so a set
  registered in `simp_laws` reaches a `by simp()` in a module that does not
  import the lemma's.

**Defaults.** `List::windows`, `Vec::entries` and `BitVec::nat` are in
`simp_laws` (their modules sit below `string`); `Stored::bytes`
(`stored.hthr`), `Part::fields` (`part.hthr`) and `Valuation::reads`
(`function_ir_eval.hthr`) are in their types' modules. Each has its
`simp_check` theorem: the core ones in `simp.hthr`, the others in their
modules' `lib/_tests` files. A builtin is keyed by its name (`"Vec"` for
`[A; n]`). A law with a hypothesis fires where the call's discharger proves
it; the default discharger reads the locals only.

Not built: a default discharger for arithmetic side conditions, or for a
theorem body or a `found` condition with no tactic written; what each would
need is in `issues/simp-adoption-native-gaps.md`.
