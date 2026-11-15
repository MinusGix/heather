# grind: congruence closure whose failure is the graph

Issue: [grind-port](../../issues/grind-port.md) (milestone `tac-general`).
Round 1 built `lib/std/tactic/grind.hthr`, the `Spine` host request, and the
probes in `lib/_tests/std/tactic/grind_tests.hthr`. Round 2 added lemmas
instantiated by e-matching, the `Say` host request and `grind_report` (§9).
Round 2½ proves lemmas' premises at their instances (§11), the
reader takes conjunctions and records of equations apart (§12), and a
pattern's argument may match up to a definitional step (§13).

The milestone asks for "a general-purpose rewriting and congruence-closure
tactic (grind-like) [that] closes the routine goals that today need hand
`trans`/`cong` towers, and hands back its search state when it fails". The
issue adds the centrepiece: the stuck state is the interface. This note
records the decisions round 1 made, and the rounds after it.

---

## 1. Where it sits among the tactics

Checked against master on 2026-11-02:

| tactic | what it decides | search | proof |
|---|---|---|---|
| `omega` (CutSat), `bv_omega` | linear integer arithmetic | Rust | Heather certificate |
| `ring`, `linarith`, `nlinarith` | commutative-ring identities, linear/nonlinear order | Rust | reflection |
| `norm_num` | closed numeric facts | Heather `Tac` | `Bool` verdicts by `refl` |
| `mono` | orders by monotonicity | Heather `Tac` | the carriers' laws |
| `rewrite(h, …, e)` | one transport along given equations | elaborator form | `j` |
| `cong(p)` | one congruence step | anti-unification at the expected type | `cong` |
| `split_all`, `apply`, `first_of` | case splits, backward steps | Heather `Tac` | `Close`, the lemma |

None of them combines equations: given `h1: a = b` and `h2: f(b, c) = c`,
proving `f(a, c) = c` is a hand `trans(cong(…), h2)`, which is the tower the
milestone names. Congruence closure is that combination, and it is the core
grind is built on; e-matching, case splits and the arithmetic deciders are
what it calls later (§6).

The roadmap says `tac-general` is written in Heather once `tac-first-port`
landed, and it has: grind is a `Tac<Expr>` over the host interface
(`docs/metaprogramming/host-elaboration-interface-design.md`), like `mono` and `norm_num`.
Congruence closure over a goal's terms is small search (tens of terms), so
there is no case yet for a Rust search with a Heather certificate the way
`omega` has one; if a client grows past that, the R3½ oracle tier of the host
design is where a native closure would go.

## 2. The decisions

1. **The graph is never trusted.** The tactic returns a proof term built from
   `trans`, `sym`, `cong` and two lemmas of its own (`grind::congr`,
   `grind::congr_fun`), and the kernel checks it at the `by` like any other
   tactic's result.
2. **Proofs are explanations.** Each merge of two classes records one edge:
   an equation given (a local or a hint, by its proof) or a congruence of two
   applications. Merging only distinct classes keeps the edges a forest, so
   the path between two nodes of one class is unique and uses only edges
   older than the classes' meeting. The proof of `a = b` is that path, each
   edge oriented by `sym`, joined by `trans`; a congruence edge is proved from
   the explanations of its parts. (This is the proof-forest scheme of
   Nieuwenhuis and Oliveras, written without path compression.)
3. **Terms are curried applications.** A term is read as a head applied to
   arguments, every argument included, as the kernel has them (§3). The
   graph's application nodes are binary, `f(a)` with `f` possibly a partial
   application, so one lemma per shape covers every arity:
   `congr: f = g → a = b → f(a) = g(b)`, `congr_fun` when the arguments are
   one node, `cong` when the functions are.
4. **Dependent arguments belong to the head.** Where the function's type is
   dependent at an argument (a type argument `List::append<A>`, an index),
   congruence would need a dependent `congr` and, for type arguments, an
   equation one universe up, which the prelude's lemmas (`A : Ty 0`) do not
   state. Such an application is hash-consed but never merged by congruence:
   `append<Nat>` is one node however often it occurs, and two `append`s at
   different element types are two nodes.
5. **Atoms are compared once.** A term read no further is an atom. A global,
   a local and a literal are compared by identity (no request); any other
   atom is compared by `Defeq` with the atoms of the same kind. Equal atoms
   are one node, so the graph works up to the elaborator's conversion at its
   leaves and syntactically above them.
6. **Constructor values are applications.** The kernel's constructor value
   (`Cons(x, xs)`, `Some(y)`) is no application, so `View`'s `HCtor` reads its
   fields and `Ctors` gives the constructor as a function of them; the value
   is that function applied to the fields, and its proof steps are checked
   up to β.
7. **The failure is the graph** (§4).

Not decided here, and left to the issues that own them: the hint-pool
selection language ([lemma-selection-and-search](../../issues/lemma-selection-and-search.md))
and a machine-readable diagnostics stream
([ai-facing-tooling](../../issues/ai-facing-tooling.md)).

## 3. `Spine`

`View` lists only the arguments a call writes (`List::append(xs, ys)`, with
the element type left out), which is right for display and wrong for
congruence: a node must stand for exactly one kernel term. Round 1 adds one
host request:

```heather
Spine(h: Handle)                // → Checked<SpineInfo>
record SpineArg { arg: Handle, dependent: Bool }
record SpineInfo { head: Handle, args: List<SpineArg> }
```

It peels the kernel's applications (`App` and `app@`) with nothing reduced,
and marks an argument dependent when the function's type at it has a codomain
that mentions it (read off a checked `App`'s codomain, or the head's type for
`app@`). A term that is no application is its own head with no arguments; a
type is refused. A subterm the term shares is one handle wherever it occurs,
as for `Arms`; equal subterms built apart are not, so identity beyond sharing
stays `Defeq`'s (decision 5).

`Spine` is general: any Heather tactic that rebuilds or compares
applications (a future `simp`, a congruence-aware `rewrite`) wants the full
argument list, and `norm_num`'s hole-at-the-next-domain workaround for
`x⁻¹`'s unwritten proof argument is the same gap from the other side.

## 4. The stuck state

When the two sides end in different classes, `grind` fails with:

- each side, spelled, with its class;
- every class of more than one term the equations or the goal mention, with
  its members (partial applications are left out: no one wrote them);
- each local and hint read as an equation, each equation under binders that
  was not instantiated (round 1 does not instantiate; §6), and in one line
  the locals that are no equation;
- the step that closes it: one more equation between a member of the left
  side's class and a member of the right side's.

For example (`lib/_tests/std/tactic/grind_tests.hthr`, the shape of
`Format::down_of_le` in `lib/std/num/float/eft.hthr` with one hint left out):

```text
error: `by grind_with(…)`: the tactic failed: grind: the two sides are not in one class
  at `h`
    tried the left side: in class #0
  at `mul(mul(k, pow(2, sub(b, e))), pow(2, Succ(e)))`
    tried the right side: in class #17
  tried class #0: 2 terms
    at `h`
      tried member: of class #0
    at `mul(k, pow(2, Succ(b)))`
      tried member: of class #0
  tried class #18: 2 terms
    at `Succ(b)`
      tried member: of class #18
    at `add(sub(b, e), Succ(e))`
      tried member: of class #18
  tried class #19: 3 terms
    at `pow(2, Succ(b))`
      tried member: of class #19
    at `pow(2, add(sub(b, e), Succ(e)))`
      tried member: of class #19
    at `mul(pow(2, sub(b, e)), pow(2, Succ(e)))`
      tried member: of class #19
  tried hk: read as an equation
  tried s: read as an equation
  tried hint 0: read as an equation
  tried not equations, not read: e, b, k, h
  tried to close it: one more equation between a member of #0 and a member of #17, as a hint: `grind_with([…])`
```

(The host spells a goal's subterms in prefix form, `mul(k, …)` for `k * …`;
that is the speller's, not the report's.)

A reader sees that `h` is `k * 2^(b+1)`, that `2^(b+1)` is
`2^(b-e) * 2^(e+1)` (so `h` is `k * (2^(b-e) * 2^(e+1))`), and that
the missing step is associativity of `*`:
`grind_with([…, sym(k.mul_assoc(…))])` closes it. That is the loop the issue
describes (run, read the state, add one hint, rerun), and each step of it is
mechanical.

The report is `Note` data, which the host renders the way every tactic's
trace is rendered. It is already structured (each line a term handle and a
verdict); serializing notes as JSON for a model is
[ai-facing-tooling](../../issues/ai-facing-tooling.md)'s, and when it lands the
report needs no change. The 2026-08-06 cross-reference in the issue asks that
the handed-back e-graph be (a serialization of) the goal-keyed decision tree
of [parallel-checking-and-caching](../../issues/parallel-checking-and-caching.md);
round 1's state is the graph at one goal with no decisions in it, and the
decision tree becomes real when case splits do (R4).

## 5. Cost

Reading a term costs one `Spine` and one `View` per subterm and, for an atom
that is neither a global, a local nor a literal, one `Defeq` per atom of its
kind; reading is linear in the terms' size times the atoms compared. Closure
is passes over the application nodes, each pass quadratic in their number
(signatures compared pairwise, classes looked up in lists), and the number of
passes is the depth congruence propagates through. Explanation is a depth-first
search per equality asked, in a forest of at most as many edges as nodes. For
the goals the probes hold (tens of nodes) the tactic's own evaluation
dominates and the per-invocation floor of a Heather tactic is most of it.

What to change when a client outgrows that, in order: a signature table keyed
by class pair instead of the pairwise pass; union by rank with the edge
forest kept separately; a native closure behind the oracle tier with the same
proof reconstruction.

That was round 1's graph. Since 2026-11-08 the nodes and classes sit in
`NatMap` tries, the signature table exists, and closure is incremental
(§15.2): a lookup is logarithmic in the graph, a close reads only the dirty
nodes against their bucket, and a round's matching walks each pattern root
from the uses index through class rows that hold no congruent copies. What
bounds a run is its total fuel across evaluations, since the arena is not
freed during a tactic run (§15.3). Union by rank and a native closure remain.

## 6. Rounds

| round | builds | done when |
|---|---|---|
| R1 (done) | `Spine`; congruence closure over the goal's equations and hints at their instances; proof by explanation; the graph as the failure | the hand `trans`/`cong` steps of a library proof close by `grind_with` with its lemmas as hints, and a failure names the missing equation's classes |
| R2 (done, §9) | e-matching ([grind-e-matching](../../issues/grind-e-matching.md)): equations under binders, from the locals and a hint list, instantiated by matching their patterns against the graph's terms modulo the classes; the used hints reported on success | `grind_using(["List::append_assoc", "List::append_nil"], [])` closes an append tower with no instance written, and `grind_report` says which it used |
| R2½ (done, §11) | premises ([grind-lemma-premises](../../issues/grind-lemma-premises.md)): a binder no side binds and nothing depends on is proved at the instance, by the graph, a local or hint, or `Synth` | an order premise by a local and an equation premise by the graph close, and the report names an unproved premise |
| R2¾ (done, §13) | definitional equalities ([grind-definitional-equalities](../../issues/grind-definitional-equalities.md)): a pattern's argument matched up to `Defeq`, its free binder drawn from the graph; both sides of a lemma as patterns | `Int::neg_add`'s `Succ` step closes by `grind_using` with the four lemmas its `calc` cites |
| R3 (done, §14) | constructor facts and disequalities ([grind-constructor-facts](../../issues/grind-constructor-facts.md)): injectivity, disjointness, `≠` hypotheses, `False` goals | `Cons(a, as) = Cons(b, bs)` gives `a = b`, and `Nil = Cons(x, xs)` closes any goal |
| R4 | case splits and theories ([grind-splits-and-theories](../../issues/grind-splits-and-theories.md)): split on a `match` scrutinee in the graph (`split_all`'s `Cases`), and exchange equalities with `omega`/`ring` | a goal needing a `Bool` case split and a linear fact closes, and the failure is the decision tree |

The graph's pure half is now a generic library (§8).

R2 added one host request, `Say`: a tactic could only report on failure,
and the used-subset report ([lemma-selection-and-search](../../issues/lemma-selection-and-search.md)
piece 3) is a note on success (§9.4).

## 7. Rejected alternatives

- **Search in Rust with a Heather certificate**, as `omega` does. The search
  is small and the milestone puts it in Heather; the certificate would be the
  same explanation proof. Kept as the scaling path (§5).
- **Congruence by `cong` over a λ** (derive.hthr's way: `cong(λ z => C(…,
  z, …), p)` per position, `Assume` for `z`). It needs the application rebuilt
  with every argument, a local per step, and fails at dependent positions the
  same way; curried `congr` needs neither.
- **Holes for `congr_fun`'s functions.** `congr_fun(_, _, _, _, _, pf)` with
  the functions left as holes fails to unify when `pf` is an equation between
  partial applications (the hole's type is a function type the unifier
  η-expands, `f(a, ?9) = f(b, ?9)` against `?2 = ?3`); the proof passes the
  functions and arguments explicitly. Not filed: explicit arguments are what a
  proof should carry anyway.

## 8. The e-graph library (2026-11-02)

Minus asked for the e-graph to be generic, for other parts of the system
that identify terms up to equations, and so that its correctness is proved
once ([egraph-library](../../issues/egraph-library.md)). It is
`lib/std/data/egraph.hthr`, and grind runs on it.

- **`EGraph<Op, J>`**: nodes `ENode<Op> { op, kids }` numbered as added,
  each node's class representative, and the merge edges. `add` hash-conses
  (same operator by the caller's `eq_op`, same children by number), `fresh`
  does not; `union(u, v, j)` merges with a justification of any type;
  `close(eq_op, fuel)` closes under congruence. A congruence merge is
  checked against the graph it is made in (`congruent`), so signatures only
  propose candidates and the soundness proof never reasons about them.
- **Explanations** fold the unique path through a `PathAlg<J, P>`
  (`refl`, `given(j, forward)`, `cong(from, to, kid evidence)`, `trans`).
  grind's `proof_alg` builds proof terms; the probes fold a printable trace.
- **Soundness**, over a denotation `den: Nat → A` and an interpretation
  `interp: Op → List<A> → A`: `Agrees` is "every node's value is its
  operator applied to its children's" and "every node's value is its
  representative's". `empty_agrees`, `fresh_agrees`, `add_agrees` (given the
  new node's value), `union_agrees` (given the two values are equal) and
  `close_agrees` (given `eq_op` is sound) preserve it, and
  `same_class_sound` reads an equation off one class. The probe
  `by_classes` (`lib/_tests/std/data/egraph_tests.hthr`) proves
  `f(a, c) = f(b, c)` from `a = b` with no explanation built: the class is
  the proof. Only soundness is proved; no client needs completeness.
- **grind's instance**: operators `GAtomOp(n)` (atoms are told apart by
  grind, by key and `Defeq`), `GAppOp` with children `[f, a]`, and
  `GDepOp(arg)` with child `[f]`, so a dependent argument is part of the
  operator and congruence reads only the function.

- **E-matching** (round 2, §9.2): `Pattern<Q>` (items numbered like nodes,
  since a type nested in its own `List` is not lowered yet), a client
  `test: Q → Op → Subst → Option<Subst>` that may bind variables an
  operator carries, `ematch(test, table, p)` over every root, and
  `subst_same` to tell a new instance from a seen one by classes.

What the library does not have yet: a soundness theorem for e-matching
([egraph-ematch-soundness](../../issues/egraph-ematch-soundness.md)), a `≈` path algebra with `Proper`
congruences ([egraph-setoid-path-algebra](../../issues/egraph-setoid-path-algebra.md)),
a theorem that a hash-consed `add` returns a node of the requested value
([egraph-add-value-theorem](../../issues/egraph-add-value-theorem.md); clients
that need it use `fresh`), and union by rank
([egraph-scaling-structures](../../issues/egraph-scaling-structures.md), §5).
Its arrays, signature index and incremental closure are §15.2's.

## 9. Lemmas by e-matching (round 2, 2026-11-02)

Issue: [grind-e-matching](../../issues/grind-e-matching.md).

### 9.1 The surface

| call | facts |
|---|---|
| `grind()` | the goal's locals |
| `grind_with(hints)` | the locals, and the facts the terms `hints` prove |
| `grind_using(names, hints)` | the above, and the lemmas `names` names, resolved where the `by` is (`"List::append_assoc"`) |
| `grind_report(names, hints)` | `grind_using`, and on success a `tactic-report` warning naming the hints and lemmas the proof cites, the ones it does not cite but whose terms the search needed (§9.6), and the ones it does not use |

Any fact whose statement is an equation under binders, a local
(`k: (n: Nat) → f(n) = n`), a hint or a named lemma, is a **lemma**. Before
round 2 such a fact was reported as "not read"; now it is instantiated:

```
theorem tower<A>(a, b, c, d: List<A>): ((a ++ b) ++ c) ++ d = a ++ (b ++ (c ++ d)) {
    by grind_using(["List::append_assoc"], [])
}
theorem lens<A>(a, b, c: List<A>): ((a ++ b) ++ c).len() = a.len() + (b.len() + c.len()) {
    by grind_using(["List::len_append", "Nat::add_assoc"], [])
}
```

Names rather than terms because a lemma written as an `Expr` hint is
elaborated at the `by`, where its implicit parameters become holes the
hint's type then mentions; a name resolves to the global with its whole
telescope, so every binder is a pattern variable.

### 9.2 Patterns and matching

A lemma's type is opened binder by binder (`Open`), and one side of its
equation is read as a **pattern** the way a term is read into the graph
(§2): a binder is a variable, a global, local, literal or constructor is an
atom of its key (`QKey`), an application is `QApp`, and an application to a
dependent argument is `QDep(v)`, whose argument (part of the graph's
operator) binds variable `v`. A term only `Defeq` could compare (a λ, a
type built from a binder) is a **wildcard**, a variable no binder is. A
constructor atom matches at any instance of its type's parameters, so the
pattern `Nil` meets `Nil<Nat>`; the parameters are bound elsewhere (the
`QDep` of `append`) or the instance's type refuses it. Nullary constructors
are now atoms of their constructor's key in the graph too, which is what
lets a pattern find them.

The side is the left one unless it is a bare binder (it would match every
node) or misses a binder; then the right one. (Since §13, both sides that
qualify are patterns.) A lemma neither of whose sides
binds every binder has a premise (`n = 0 → f(n) = n`); round 2 set it
aside, and §11 proves it at the instance.

Matching is the library's (`EGraph::ematch`, §8): every node is tried as the
root, matched as it is, and every item below the root is matched against
any member of the class of the node it meets, so `f(b, x)` matches
`f(a, c)` once `a = b`. A variable meets again only nodes of its first
node's class. All of it is evaluation; the host is asked nothing until an
instance is added.

### 9.3 Rounds

`saturate` closes the graph and checks the goal. If the sides are apart, each
lemma's matches are listed, and the ones whose binders meet classes no
earlier instance of that lemma met are added: the lemma applied to the
matched nodes' terms, `infer`red, its sides read into the graph and joined
by a `Fact` named after the lemma. An instance the kernel's type of does
not make an equation of (an ill-typed match through a wildcard) is dropped.
Then the graph is closed again, up to **8 rounds**, at most **64 new
instances a round**.

It stops for three reasons, each a line of the failure:

- the sides meet: the proof is the explanation, as in round 1;
- a round finds no new instance ("no new instance after k rounds", or "no
  instance in the graph"): matching ran dry, so more rounds cannot help;
- the round budget is spent ("stopped after 8 rounds"): a lemma that makes
  new terms every round (`f(n) = f(g(n))`) would go on forever.

Each lemma's line says how many matches it had and how many instances were
added, or that its patterns never matched a term of the graph; that is the
report's answer to "which hint was useless" on failure.

No heuristics yet: every lemma is matched against every node every round,
with no trigger selection, no relevance filter, and no orientation (a
lemma's equation is added both ways, as any equation is). The dedup is by
classes, so an instance whose arguments only met new members of old classes
is not added twice. This is the first cost to watch (§5): a round is a
match of every pattern against every node, each item scanning a class.

### 9.4 Saying what was used: `Say`

`Say(msg, notes)` (tag 26, answered with `True`) records a message and
notes rendered as `Fail` renders them, and the host reports them as one
`tactic-report` warning at the `by`, **only if the run's result is the
goal's proof**. A run that says something and then fails reports only its
failure (`crates/elab/tests/tactic_host.rs`,
`say_reports_only_a_run_that_succeeds`). The lint is a warning, not an
error, so a library may keep a `grind_report` in place; its job is the
narrowing a reader (or a model at the hint interface) does next:

```
warning: `by grind_report(…)`: grind: the proof uses List::append_assoc; not used: List::append_nil
```

The used names come from the same explanation the proof does, folded
through a second path algebra (`cited_alg`, the names of the given facts
along the path), so the report is exactly what the proof term cites. Locals
the proof cites are named separately ("and the locals k, h"). A hint the
proof does not cite can still be one the search needed (§9.6).

### 9.5 Found on the way

A `let` above a recursive `match`, bound from a parameter the self-call
changes, keeps the top call's value: `saturate`'s first draft bound the
closed graph above `match rounds` and found the same instances every round.
The elaborator accepts the shape and computes the wrong function
([recursion-let-reads-changing-parameter](../../issues/recursion-let-reads-changing-parameter.md));
`saturate` now matches on `rounds` first.

### 9.6 Hints the search needed: lurking facts (2026-11-06)

Issue: [grind-report-lurking-hints](../../issues/grind-report-lurking-hints.md).
What the proof cites (§9.4) is not all a narrowed call needs. A near match
draws its free binder from the graph's terms, or finds a hole's solution
among its nodes (§13.1, §13.4). That term may be in the graph only because
some hint put it there, and the proof cites the matched lemma, not the hint
that supplied the term. Probe `lurk_reported`: `lurk_one: 1 + 0 = 1` is the
only source of the node `1`, which `lurk_sc(?b) ≡ lurk_two()` needs as `?b`.
The proof cites only the local `k`, and without `lurk_one` the goal fails
(`lurk_narrowed`).

This is the *lurking axiom* of Gopinathan et al., "Accelerating Automated
Program Verifiers by Automatic Proof Localization" (CAV 2025): an SMT axiom
outside the UNSAT core whose instances made the ground terms that triggered
a core axiom. They find them by walking Z3's instantiation graph back from
each core axiom. grind keeps the same walk as it goes:

- **Per node, what brought it** (`GInfo.by`). The goal's terms: nothing. A
  fact's terms, as read: the fact's name. An instance's new terms: the
  lemma, the names its premises cite, and what brought the nodes it stands
  on (the nodes it was matched at, the node a near match met, the older
  nodes its sides are made of, its premises' paths). So `by` is already
  closed: nothing walks back later. A side's reduct inherits its side's.
- **Per edge, what it stands on** (`Fact.found`): for an instance, the
  above plus its sides' `by`; for a reduct's or injectivity's edge, its
  endpoints' and the path that justified it.
- **Per proof**, `found_alg`: a second path algebra beside `cited_alg`,
  collecting each edge's `found` and the `by` of the nodes every congruence
  and reflexivity step is at.

The report then splits the hints three ways:

```
warning: `by grind_report(…)`: grind: the proof uses none of the hints, and the locals k; not cited, but needed to find it: lurk_one; not used: List::append_nil
```

"Needed to find it" over-approximates in one direction only: a hint whose
terms the search stood on is named even if another term would have done.
A hint named "not used" can be dropped. Read facts are the exception that
needs no tracking: a fact's terms are interned by its own reading, so a fact
read earlier never makes a later one work. Only search does.

Cost: one name list per node and per edge, built as instances are added,
and one more explanation of the proof's path, by `found_alg`, which only the
report reads.

**Mutation controls.** The paper also measures whether a localized proof
survives renamings and reorderings, as a stand-in for a project evolving.
grind is deterministic, but it visits nodes in order under per-round
budgets, so the same question applies: `grind_mutation_tests` re-proves
goals of `grind_tests` with their lemmas reversed or beside lemmas they do
not need. All close. The last to, `neg_add_succ` with `Int::add_comm`
added, failed with "ran out of fuel or nesting depth" until 2026-11-06. It
was depth, and not grind's: the extra lemma takes the run past about 2,000
host requests, and any run that long under a `bind` died reading its result
(docs/kernel/native-depth-budget-design.md §9,
[grind-unrelated-lemma-fuel](../../issues/grind-unrelated-lemma-fuel.md)).
A grind call's request count is still a cost worth watching (each round's
matching and closing is split into one evaluation per `settled` piece), but
no longer a cliff.

## 10. The library sweep (2026-11-02)

Issue: [grind-library-sweep](../../issues/grind-library-sweep.md). Of the
library's theorems, 143 build four or more `trans`/`cong` steps by hand
(most in `lib/native`, then `std/num`, `std/arch`, `std/os`). A sample
across the areas, each equational step restated as a probe and given to
`grind_report` with the lemmas its hand proof cites:

| proof | step | result | blocker |
|---|---|---|---|
| `Memory::set_set_comm` | each `get` after two `set`s | closes from the three instances (`grind_with`), not from the names | **premises**: `get_set_hit`/`get_set_other` need `space.same(y, x) = True/False`, which the branch has as a local |
| `Int::neg_add` | the `Succ` step of its `calc` | the pattern never matches as written; with the step made syntactic, stops one equation short | **definitional equalities**: `OfNat(Succ(k))` is `OfNat(k).isucc()` and `-OfNat(k)` is `Int::negOfNat(k)` only by computation |
| (`Int`) | `(a + b) + c = b + (c + a)` | closes from `add_assoc` and `add_comm` | none |
| `Float::same_of_squeeze` | `n = m` from `n = k`, `k = False`, `m = False` | closes | none |
| `Float::same_of_squeeze` | `m = False`, `m = True` ⊢ anything | the report shows `True` and `False` in one class, and stops | **constructor facts** (R3) |
| `Env::compose_same` | `trans(ka.left, trans(k0.left, sym(kb.left)))` | nothing read | **conjunctions**: the equations are fields of `∧`/record locals (§12) |
| `commit_chain` | each branch | premises proved by derived terms (`Succ(a).le_trans(b, c, first, bc)`) | **premises**, some needing a search (`Synth`) |
| `BitVec::sub_bits_cons_leaf` | each of eight branches | per branch, after a `Bool` split and computation | **case splits** (R4) and definitional steps |

What it says, in order of how much it would unlock:

1. **Premises** ([grind-lemma-premises](../../issues/grind-lemma-premises.md)):
   the most common reason a named lemma cannot be used. Most are a `Bool`
   test or an order fact the branch already has as a local.
2. **Definitional equalities**
   ([grind-definitional-equalities](../../issues/grind-definitional-equalities.md)):
   the number and integer lemmas are stated on the constructors' functions
   (`isucc`, `negOfNat`), while goals hold the computed forms. The hand
   proofs cross these silently, because the kernel compares up to
   conversion.
3. **Conjunctions** ([grind-read-conjunctions](../../issues/grind-read-conjunctions.md))
   and **constructor facts** ([grind-constructor-facts](../../issues/grind-constructor-facts.md)):
   small readers, each needed by a whole family of native proofs.
4. **Case splits** ([grind-splits-and-theories](../../issues/grind-splits-and-theories.md)):
   the bit-vector and float proofs split before they chain.

Two defects the sweep found in grind itself are fixed here:

- **Evaluation fuel.** The host gives the evaluation between two requests a
  fixed fuel, and one round (closing the graph, matching four lemmas,
  rendering the report) outgrew it on a 29-node graph. Each lemma's
  matching, and the closed graph, are now their own evaluations (`settled`
  asks the host about a number that depends on each piece). The report's
  class listing read every class's members off the class list, cubic in
  the nodes; it now reads the class table once.
- The report spells terms as the kernel's calls (`neg(add(a, …))`), the
  general diagnostic gap of
  [diagnostic-operator-resugaring](../../issues/diagnostic-operator-resugaring.md),
  which grind's report is now a customer of.

No library proof was replaced. The proofs grind closes today are the ones
whose instances are written out, and a `grind_with` naming those instances
is no shorter than the hand `trans` chain. The replacements come with
premises (§11.4).

## 11. Premises (round 2½, 2026-11-02)

Issue: [grind-lemma-premises](../../issues/grind-lemma-premises.md). The
sweep (§10) found premises the commonest reason a named lemma could not be
used: `Memory::get_set_hit` needs `m.space.same(a, x) = True`, which the
branch proving the goal already has.

### 11.1 Which binders are premises

`Open` says of each binder whether the rest of the statement depends on it.
A side is a pattern when it binds every binder something depends on (and is
not a bare binder); a binder it leaves unbound and nothing depends on is a
**premise**. A binder no side binds that a later premise or the conclusion
mentions (`(n, m: Nat) → n < m → f(n) = n`'s `m`, an `∃` in disguise) is
depended on, so neither side is a pattern and the lemma is set aside as in
round 2. A side that binds a proof argument (`xs.get(i, h)`) matches it like
any other binder.

### 11.2 Proving one at an instance

The instance is built left to right: a matched binder is its node's term,
and at a premise the partial application is `infer`red, its type's domain
read (`View`, or the head normal form), and that statement proved, in this
order:

1. **by the graph**, when it is an equation: its sides are read in, the
   graph is closed, and if they meet, the explanation is the proof (as the
   goal's is). A premise `p(a) = True` holds from `p(b) = True` and `a = b`
   this way, where no local is it.
2. **by a local or a hint**, up to `Defeq`: every local of the goal, then
   every hint that is no equation. `Defeq` is what lets
   `m.set(z, e).space.same(y, x) = True` be the branch's
   `m.space.same(y, x) = True`: the two are one only by computing `set`'s
   `space`. A hint that is no equation was "not read" before this round; it
   is now kept for the premises, which is how a derived fact reaches one
   (`Succ(a).le_trans(b, c, first, bc)`).
3. **by `Synth`**, the `:= infer` search: instances, computation, and the
   evidence rules of [facts-on-demand](../native/facts-on-demand-design.md). A closed
   `0 < 3` is proved here.

Nothing about a premise's proof is trusted: the finished instance is
`infer`red before its equation is read, and the kernel checks the whole
proof at the `by`. The names a premise's proof cites (the graph's facts, the
local or the hint) travel with the instance's edge (`Fact::uses`), so
`grind_report` names them as used.

### 11.3 Waiting instances

A premise not proved now may be later: an equation premise whose sides a
later instance merges. An instance with an unproved premise is recorded as
seen (matching does not find it again) and kept **pending**, with a note of
the premise it lacks. After each round that adds instances, the pending ones
are tried again after the new ones, against the grown graph. A round that
finds no new instance stops as before, since the graph is then the one the
pending instances were last tried against.

The failure lists the pending instances, the first four by their premise:

```text
  tried k: a lemma, instantiated by matching, its premise proved at each instance
  tried k: 2 matches, 0 instances added
  tried premises: 1 instance not added: a premise was not proved
  at `a = 0`
    tried k, premise 1: not proved: its sides are not in one class, no local or hint is it, and the instance search finds none
```

### 11.4 What the sweep's blocked proofs became

| proof | before | now |
|---|---|---|
| `commit_chain` (parser diagnostics) | three branches of three instances, each premise a derived term | replaced: each branch is a `grind_using` of the three `commit_*` lemmas with the one derived fact as a hint |
| `Memory::set_set_comm` | three branches of two or three `trans`/`get_set_*` instances each | closes, each branch as `by grind_using(["Memory::get_set_hit", "Memory::get_set_other"], [])` (the probe `set_set_hit_other`); the premises are the branch's locals, over another memory by `Defeq`. **Not replaced** |

`set_set_comm` keeps its hand proof: `memory.hthr` is the byte memory model
under the whole native stack, and importing grind there puts the tactic
library (`tactic`, `derive`, `egraph`, `grind`) into the closure of every
module and Rust test that loads the model, for one theorem. Its `absurd`
branch (`True = False` from the two locals) would stay by hand anyway: it
needs constructor facts (R3). `parser_diagnostics` already imported
`omega`; it now imports `grind`, and the two Rust tests that list the parser
library's closure by hand list grind's.

### 11.5 Not done

- **A premise tactic.** A `grind_by(names, hints, t)` running a caller's
  tactic at an unproved premise was tried and left out: with
  `apply(Nat::le_trans, assumption())` on `commit_chain`'s first branch it
  changed which other instances were added in a way not yet understood,
  while the hint route above closes the same proofs. Filed as
  [grind-premise-tactic](../../issues/grind-premise-tactic.md).
- **Premises by a decider.** An order premise that needs arithmetic
  (`p < k + i` from `i <= p`) is `omega`'s; that is the theory exchange of R4.
- **Cost.** Each premise asks one `Defeq` per local and hint, and an
  equation premise closes the graph once more. No client is near the round
  caps; if one is, a cheap key on the premise's head before `Defeq` is the
  first thing to add.


## 12. Conjunctions and records (2026-11-02)

Issue: [grind-read-conjunctions](../../issues/grind-read-conjunctions.md). The
sweep (§10) found `Env::compose_same`'s chains citing `ka.left`,
`h1.right.right`: equations that are fields of `∧` and record locals, which
the reader listed as "not equations, not read".

A fact that reads as neither an equation nor a lemma is now taken apart by
a new host request, `Fields` (host design §24): a term of a non-indexed
inductive with one constructor comes back as its fields, each a handle to
its projection, the term `k.left` elaborates to. Each field is a fact of its
own, named `k.left`, proved by its projection (`Hd` of the handle), and read
the way any fact is: an equation into the graph, an equation under binders
as a lemma (`Env::Same`'s `(i: Nat) → a.number(i) = b.number(i)`), a field
of fields taken apart again, up to the reader's depth of 64 and 4096 facts
under one local. A field that is none of these is kept for the premises
(§11.2) with no line of its own, so `h: (a < n) ∧ True` proves a lemma's
`a < n`. A fact none of whose fields reads as anything is reported as
before (a local in the "not equations" line), so a data local (`env: Env`)
costs one `Fields` per record layer and says nothing new.

Two kinds stay whole, as the issue asks:

- **`∃`** and any record with a field a later field's type mentions:
  `Fields` refuses it. `k.proof: P(k.witness)` is a fact about the
  value, and reading it would put the projection `k.witness` in the
  graph as an opaque atom; the issue leaves that to a design of its own.
- **`↔`**: its directions are implications between propositions, not
  equations between terms; `Fields` answers the type's reference, and grind
  compares it with `Lookup("Iff")`. (A direction concluding an equation
  would otherwise be read as a lemma with a premise.)

The reader is no longer one recursive function: a function can only call
the ones declared above it, so `read_fact` reads a fact alone
(`read_one`), takes it apart (`expand`), flattens fields of fields with a
work list (`leaves`), and reads the leaves (`read_leaves`).

`Env::compose_same`'s `args_same` and its two field chains are `by grind()`
now (`lib/native/native_structured_meaning.hthr` imports `grind`; `tactic`
was in the native closure already). Its `numbers` branch stays by hand: it
chooses between frame lemmas by a dependent `match` on `absent(i, …)`,
which is case splits (R4) territory.

Probes: `conj`, `conj_nested`, `conj_defined` (through a definition whose
value is a `∧`), `conj_lemma`, `conj_hint`, `conj_record` (a value-parameter
record), `conj_open`, `conj_premise`, `conj_checking`, and the refusals
`conj_no_equation`, `dependent_unread`, `exists_unread`, `iff_unread`, in
`lib/_tests/std/tactic/grind_tests.hthr`. `exists_unread` and `iff_unread`
would close if read, so they discriminate.

## 13. Definitional equalities (round 2¾, 2026-11-02)

Issue: [grind-definitional-equalities](../../issues/grind-definitional-equalities.md).
The sweep (§10) found `Int::neg_add`'s `Succ` step stopped by two
equalities the kernel accepts by computation and the graph did not see:
the goal holds `OfNat(Succ(k))` where `Int::add_isucc` speaks of
`b.isucc()`, and the induction hypothesis holds `-OfNat(k)` where
`Int::ipred_negOfNat` speaks of `Int::negOfNat(n)`. Both are true only by
unfolding a definition at a constructor (`isucc(OfNat(n))` is
`OfNat(Succ(n))`; `neg(OfNat(n))` is `negOfNat(n)`), and neither side is a
term the graph holds before the instance that needs it, so comparing the
graph's existing nodes pairwise (the issue's option 2) would not find them,
and grind has no reducible transparency to normalise by (option 3).

### 13.1 Near matches

The issue's option 1, made to work when the item's binder is not yet
bound. The library gains `ematch_loose` (`lib/std/data/egraph.hthr`): an
item the client allows that meets a class none of whose members it matches
is **left**, with the node it met, and the match goes on past it; at most
one item per match, never the root. grind allows the applications in
argument positions that are whole subterms of the side (`isucc(b)` in
`a + isucc(b)`). A near match binds everything but the binders only the
left item mentions.

grind resolves a near match by `Defeq`: the item's subterm, abstracted over
the lemma's binders (`Lam` over the opened telescope, each binder applied
to the node it met, a premise to a hole), against the node. With no free
binder that is one question. With one, the binder is drawn from the
graph's whole terms, in node order, as e-matching draws every binder from
the graph: `isucc(b) ≡ OfNat(Succ(k))` at `b := OfNat(k)`, a term the
induction hypothesis put there; `negOfNat(n) ≡ -OfNat(k)` at `n := k`.
More free binders than one are asked about with holes (§13.4), which is
also tried first for one.
`Mark`/`Restore` around each question keep a hole a premise left from
being solved by it.

A resolved near match is an instance like any other (premises proved at
it, read from its `infer`red type), with one more edge: from the item's
instance, found under the instance's side by the path from the pattern's
root to the item, to the node it was compared with, justified by
`grind::defn(x, y, refl)`, which the kernel checks by computation. The
edge carries the lemma's name, so `grind_report` names the lemma.
Congruence does the rest: `a + isucc(OfNat(k))` and `a + OfNat(Succ(k))`
meet once `isucc(OfNat(k))` and `OfNat(Succ(k))` do.

Cost: a candidate costs one `Defeq` (plus `Mark` and `Restore`), so a
round asks at most `grind_defeq_budget()` (256) of them, and a near match
is tried once per candidate: `Defeq` reads terms, not classes, so a
candidate that failed fails again (`NearTried` keeps how far each near
match's candidates went). Matching keeps its shape; a near match is a
branch where a strict one would have ended.

### 13.2 Both sides

`Int::add_ipred`'s left side, `a + b.ipred()`, has no instance in the
`neg_add` graph: the term that needs it is the right side,
`(-a + -OfNat(k)).ipred()`, which `neg_isucc` and the hypothesis produce.
A lemma now matches by every side that qualifies as a pattern (§9.2),
whichever the graph holds; an instance found from either is one instance
(`known` compares the lemma and its binders' classes). This doubles the
matching and is what equations already were: added both ways. Each root
is matched in an evaluation of its own (`settled`), and congruence closing
is one pass per evaluation: a graph of four dozen terms outgrew one
evaluation's fuel closing in one piece.

### 13.3 What it closes

`Int::neg_add`'s `Succ` step, stated as `int.hthr`'s `calc` states it,
closes by `grind_using` with `Int::add_isucc`, `Int::neg_isucc`,
`Int::add_ipred` and `Int::ipred_negOfNat` (probe `neg_add_succ`; the
report shows two of `add_isucc`'s instances and one of `add_ipred`'s found
up to a definitional step). `int.hthr` keeps its hand proof for the reason
`memory.hthr` does (§11.4): the integers sit below most of the library, and
importing grind there puts the tactic library in every client's closure.
Probes at an open element type (`[a] ++ xs` against `Cons(a, ys)`; `[] ++ ys`
against `xs`, found from the right side's pattern), a checking position,
and a negative control (`[b] ++ xs`, which no term makes `Cons(a, ys)`) are
in `lib/_tests/std/tactic/grind_tests.hthr`; the library's own probes of
`ematch_loose` in `lib/_tests/std/data/egraph_tests.hthr`.

Not done: the issue's option 2 (pairs of nodes compared by `Defeq` after a
dry round) is not needed by any probe yet, and a near match's candidates
are every whole term of the graph in order, with no key on the item's head
or the candidate's type to skip the hopeless ones; both are where to look
if a client spends the budget.

### 13.4 Several free binders (2026-11-02)

Issue: [grind-near-match-binders](../../issues/grind-near-match-binders.md).
Drawing every free binder from the graph is a power of its size, so a near
match whose item leaves several binders free (`f(Cons(x, ys))` against
`f([a] ++ xs)`, or a free type binder, `List::len<?A>(?xs)`) asks the host
instead, the issue's first option. `Holes` at the lemma's proof makes one
hole per binder, each at its binder's type over the arguments before it;
the item, at the nodes the match bound and the holes elsewhere, is compared
with the node by `Defeq`, which solves what the comparison determines
(`?x := a`, `?ys := [] ++ xs`, and `?A := Bool` from the types alone).
Each solution is then looked up among the graph's nodes, whole terms in
order and then the atoms that are not whole (a type argument, read as part
of an operator), by `Defeq` again (`[] ++ xs` is `xs`). The holes are
forgotten (`Mark`/`Restore`), and the instance at the nodes found is asked
once more with no hole: that is the question its `defn` edge stands for,
so an instance the kernel would refuse is never added, whatever a partial
solution's lookup let through.

A hole the comparison leaves unsolved (`len([] ++ ?xs)` against
`near_len(bs)`: the unifier stops at two stuck matches; `isucc(?b)` against
`OfNat(Succ(k))`) or a solution no node is ends the question. With one
free binder, the binder is then drawn from the graph's terms as before
(§13.1), so nothing the earlier rounds closed is lost; with more it is
left. The hole question is asked once per near match (`NearTried.asked`):
its answer reads terms, not classes.

Cost: one `Defeq` for the question, at most one per node for each
solution's lookup, and one to confirm, all from the round's budget; a round
whose budget runs out mid-question asks it again next round.

Not done: a solution that is no node of the graph (the instance would bring
a new term) is not interned, and a question answered before the node it
needs was added is not asked again
([grind-near-match-new-terms](../../issues/grind-near-match-new-terms.md)).
Probes: `near_two`, `near_two_checking`, `near_two_closed`, `near_type`,
`near_drawn` and the negative control `near_two_refused` in
`lib/_tests/std/tactic/grind_tests.hthr`.

## 14. Constructors and disequalities (round 3, 2026-11-05)

Issue: [grind-constructor-facts](../../issues/grind-constructor-facts.md). The
sweep (§10) counted about 35 `Option::some_inj(…, trans(sym(a), b))` sites
and about 35 `absurd(trans(…))` sites outside `lib/native`: an equation
chain ending in injectivity or in disjointness, which congruence alone
cannot finish.

### 14.1 What the graph adds

After each closing (`ctor_closed`), every class holding two or more
constructor values is looked at pairwise, its first value against each
other one, each pair once (`CState.done`):

- **One constructor** (`Cons(a, as)`, `Cons(b, bs)`): each field pair not
  already in one class gets an edge whose proof is `Inj(pf, k)`, `pf` the
  explanation of the two values' equation. The edge cites what `pf` cites,
  so `grind_report` still names the hint the field came from. The graph is
  closed again while that adds edges (at most 16 times per round).
- **Two constructors** of one type, two different literals, or a literal
  and a successor: `Absurd(pf, goal)`, a proof of the goal itself. The host
  decides; the graph only proposes (`3` and `Succ(n)` are no
  contradiction, and the host says so).
- **A disequality** read from a fact (`h: a ≠ b`, `h: a = b → False`, also
  once in head normal form, so `Not(a = b)`) is kept with its sides' nodes;
  when they meet, `h(pf)` proves `False`, which `exfalso` (an equation goal)
  or `elim_false` (any other) takes to the goal.

A constructor value is what `View` calls `HCtor`: its constructor function
(from `Ctors`) applied to its fields, so congruence and injectivity read the
same nodes. `Nat` is the kernel's, not a declared inductive, so its
successor is the graph's first atom, `grind::succ_fn`, keyed `KSucc` by the
reference `Lookup("Succ")` answers; `Succ(n)` is that atom applied to `n`,
lemma patterns read it the same way, and `Succ(x) = Succ(y)` gives `x = y`
by `grind::succ_inj` (not `Inj`, which takes declared inductives apart).

The laws a proof cites are grind's own (`grind::exfalso`,
`grind::elim_false`, `grind::succ_inj`): a law is resolved where the `by`
is, and a module using grind need not import `nat` or `logic`'s names.

### 14.2 Goals

The goal no longer has to be an equation. Its binders are opened first
(`open_goal`), but only where it is written as a function type or as
`Not(P)` (so `a ≠ b` is `a = b → False` under one binder, and `(m: Nat) →
f(f(m)) = m` under one): a definition whose value is a function type (an
order's `Le`) is the goal as written, because a `λ` over its unfolded
binders is not checked against it. The proof is the λ over the opened
binders. A goal that is then no equation (`False`, `P`, `a <= b`) is proved
only from a contradiction, and its failure says so: "the goal is not an
equation, and the facts hold no contradiction", with the classes and a "to
close it" line naming the two shapes a contradiction takes.

The host side builds `inj` and `absurd` exactly as the surface forms do
(`Inj`, `Absurd`, host design §25), so a refusal is the surface's (a field a
later field's type mentions, sides that are no constructors' values): such
a pair is left alone, and the graph stays as it was.

### 14.3 Reading terms through definitions

Two things the first conversions needed (`x86_64_fetch`,
`x86_64_data_read`, `x86_64_stack`):

- `Spine` reads a head β-redex as its contractum, as `View` shows it: a
  `cong_fn` or a lemma's function argument leaves `(λ s => f(w, s))(x)` in
  a type, which is the call `f(w, x)`.
- A leaf that would be an atom compared only by `Defeq` (`KOther`) is put
  in head normal form first and read again (`ISpine(h, reduce)`), so a
  definition whose value is a constructor's is read as that value.

### 14.4 A side's head normal form

`linux_world_co`'s `Io::pass_tau`/`Io::pass_ret` close their `absurd` and
`inj` steps through computation: `after(none, 0, X)` is `obs(none, X)`, and
`obs(none, pass_reading_obs(ORet(x), io))` is `ORet(…)`. Read as written,
neither side shows a constructor, and the two spellings of one stuck
observation never meet.

So each side of a fact read is remembered (`CState.unreduced`), and **once
the graph as written proves nothing** (no lemmas, or no new instance) its
head normal form is asked for (`Whnf`), and the round is run again:

- a **constructor's value** (or a literal, or `Succ(n)`) is read as a node
  joined to the side by `grind::defn` (`refl`: one by computation);
- a **stuck form** (a `match` on a neutral scrutinee, or a form `View`
  names no further, as a codata observation's) is never a node: it is
  compared by `Defeq` with the stuck forms read before, and a side whose
  form is one of theirs is joined to that side by `grind::defn` between the
  two sides as written.

Why lazily: reading every side's head normal form up front put
`x86_64_data_read`'s record-heavy states over the evaluation's fuel, and a
proof that closes as written should cost what it did. Why stuck forms are
not nodes: their spelling (a case on an `M` value, pairs built through the
checked spelling) is no term the kernel infers, and a proof whose
explanation passed through one was refused (`NotInferable`). For the same
reason injectivity and disjointness are asked about the **sides as
written** (`source_of`), never a reduct: the host computes them anyway.

The host gained two small things for this (host design §25): `Whnf` reads
off projections of pairs in its answer (`contract_projections`, as `inj`
and `absurd` do), so a constructor value built through the checked spelling
is a `View`'s `HCtor`; and `View` calls a `match` applied to arguments (a
codata observation's motive is a function type) `HMatch` of its scrutinee.

Not done
([grind-reduct-fields](../../issues/grind-reduct-fields.md)): a field of a
reduct is the reduct's spelling of it, not the term the goal writes
(`obs(E, CTau(t))`'s field is not `t` as an atom, and
`Io::pass_tau`'s `OTau`/`OVis` arms want `x2 = pass_reading(s, io)`), so
those stay by hand.

### 14.5 Conversions, and what importing grind costs

By `grind()`/`grind_with`: `round_real`'s `Float::same_of_squeeze` and
`Float::le_trans` disjointness arms (`absurd(trans(sym(a), b))` over `Bool`
locals), and `linux_world_co`'s six `pass_reading_at` steps in
`Io::pass_tau`/`Io::pass_ret` (§14.4).

Minus decided (2026-11-05) that any std module grind's own imports allow
may import it, `int` and `memory` included (`nat` and `list` are below
grind). The round converted more (`x86_64_fetch`, `x86_64_data_read`,
`x86_64_stack`, `x86_64_byte_memory`, `linux_x86_64_io`,
`linux_x86_64_determinism`, `round`, `x86_64`, `int`) and took those back,
for a cost the decision did not price in: `compile-x86`'s bundled proof
library (`crates/cli/src/native/support.rs`) and the Rust tests' module
lists (`tests/support/read_loop.rs`, the x86 prefix, `lib_std_float.rs`,
some forty lists holding `int`) are closures written by hand, so each list
holding an importer must hold grind's closure too (`char`, `string`,
`tactic`, `derive`, `egraph`, `grind`). Cold, that closure's elaboration
(dominated by `grind` itself, then `tactic`) is a large share of a test's
CPU rail, and it put `native::tests::the_bundled_library_checks` over its
CPU rail (killed, signal 9) on the first run after a compiler change. Until
the lists stop being hand-written or grind's own elaboration gets cheaper
([grind-closure-cost](../../issues/grind-closure-cost.md)), modules on those
lists keep their hand proofs; the conversions are one-line edits to
replay.

Also left by hand, for reasons of their own: `memory`'s `set_set_comm`
clash (the hint's `m.space.same(y, z)` and the local's are atoms `Defeq`
keeps apart, through the laws' dictionary), `x86_64_asm_table`'s name
clashes (importing `tactic` there shadows the table's `At` with `Note`'s),
`x86_64`'s `canonical_bytes_unique` (a field read through a projection of a
computed record), `linux_x86_64_determinism`'s `c_strings_alike` (a
hypothesis read through a match the branch only partly refines),
`Io::pass_tau`'s `OTau`/`OVis` arms (§14.4), and `fn` decision procedures
(`BitVec::unsigned_lt_dec`), whose bodies conversion unfolds.

Probes: the constructor block and its negative controls in
`lib/_tests/std/tactic/grind_tests.hthr`.

### 14.6 Cheaper to import (2026-11-06)

Both, in [grind-closure-cost](../../issues/grind-closure-cost.md)'s round.

**Where the closure's time went.** Cold, at width one, `grind` and `tactic`
were nearly all of the closure, and half of each was the kernel gate. The
gate's cost was `Tac` values written as constructors: `Tac` is lowered on
`W` (docs/inductives/inductive-tier2-w-lowering.md), and `Pure(a)` or `Ask(r, k)` in an
expression spells the encoding's annotations into the term, which the gate
checks at every occurrence (a probe's `Pure(1)` was about 20k kernel steps;
the same body through a one-line function about 2.7k). A wildcard arm of a
`match` is one copy per constructor it covers, so a `Tac` value under `_` on
`Head` (12 constructors) or `Req` (29) was paid that many times: `sides_of`,
`pi_domain` and `attempt_from` were a third of the gate between them.

**The rule.** Tactics build values through calls declared once in
`tactic.hthr`: `pure(a)`, `ask(r)` (the request helpers are `ask(View(h))`
and so on) and `ask_then(r, k)`; the constructors stay free in patterns. A
view is read by a plain function (`eq_sides`, `pi_dom`, `failure_of`) and the
tactic matches the `Option`, not the view. `pure(match …)` is a `match` in
inference position, so those few stay `Pure(match …)`. Every module that
imports `tactic` was rewritten to the rule; modules that also import
`rt_io` (whose `ETm` has a `Pure` of its own) were left alone.
[tier2-constructor-value-cost](../../issues/tier2-constructor-value-cost.md)
is the elaborator fix that would make the rule unnecessary.

The cold elaboration of grind's closure (release, width one) fell from about
two and a half minutes to just over one: `grind` by about three fifths,
`tactic` by half, `derive` by two fifths.

**The lists.** A Rust module list marked `// lib-closure: <roots>… [minus
<roots>…]` is written by `scripts/lib-closures --fix` from the imports, in
the loader's order, and `crates/cli/tests/lib_closures.rs` holds every marked
list to the CLI's loader. The bundled proof library
(`crates/cli/src/native/support.rs`), the x86 prefix, the read loop and
`lib_std_float`'s list are marked, so an import added to a module on them is
one command, not an edit per list.

**Conversions, measured and left out.** With the closure halved, the round
replayed the conversions on the bundled path (`x86_64_fetch`'s
`readable_head_same`, `x86_64_data_read`'s four load-sameness steps,
`x86_64_stack`'s two word reads) and timed
`native::tests::the_bundled_library_checks` cold, through `scripts/test` at
width one with no seeded stores: it passed, but at about 216 s of its 300 s
rail against master's 36 s. Its own `--timings` rows say where: grind's
closure about 105 s (`grind` 65, `tactic` 33, `derive` 6), then about 33 s
of `image_recheck` at each of `x86_64_fetch` and `x86_64_data_read`, the
modules where grind's chain meets the x86 chain (the session has no verdict
store there, so the relocated images are kernel-checked again); the grind
calls themselves are a few seconds. That is a sixfold cold cost on the path
every native test's first `compile-x86` builds, for seven one-line proofs, so
the conversions stay out (`round` and `linux_x86_64_determinism`'s
conversions, which also check, likewise: their test lists would pay the same
closure). What would let them in: a cheaper closure still
([tier2-constructor-value-cost](../../issues/tier2-constructor-value-cost.md)),
and a recheck that a merge of two chains does not repeat
([lib-closure-markers](../../issues/lib-closure-markers.md) records both).

**Where the sixfold went (later the same day).** Most of it was not grind.
The bundled check's session had no verdict store, so each world where two
import chains meet kernel-rechecked the moved chain; with an in-memory store
(every declaration still faces the kernel once) that went, but the store's
one Merkle prefix then re-hashed everything past the common part at every
switch between the process's world and a module's canonical world. The
store now keeps the prefixes of the last few worlds, image relocation
memoizes shared nodes, and the Merkle walk hashes a large node as a digest
walked once (`docs/infrastructure/cache-v1-design.md` §12.5). With the conversions
replayed the cold check went from about 216 s to about 120 s; master's own
stayed at about 35 s. What is left of the difference is the closure's own
elaboration (`grind` about 42 s, `tactic` about 23 s), which is
[tier2-constructor-value-cost](../../issues/tier2-constructor-value-cost.md).

## 15. Native chains: next spellings and an incremental graph (2026-11-08)

The tactics survey (PR #488) found that grind does not reach `lib/native`'s
hand `trans` chains for two reasons
([grind-unfold-defined-heads](../../issues/grind-unfold-defined-heads.md),
[grind-matching-fuel-on-native-terms](../../issues/grind-matching-fuel-on-native-terms.md)):
the chains cross steps only conversion sees, and matching three lemmas over a
native-sized graph ran out of fuel. The probe both name, `rt_loop`'s
`Fun::post_left`, now closes by
`grind_using(["Valuation::set_here", "Valuation::set_other", "branch_false"], [])`
(`lib/_tests/std/tactic/grind_native_tests.hthr`), under the suite's
address-space rail.

### 15.1 Next spellings

`Spell(e)` (tactic tag 32) answers `e` spelled one definition further on:
its head definition unfolded and the head reduced on (the elaborator's
reduct walk, `Unfold::Spelling`) until a global's call or a local is at the
head again, or as far as it reduces. A term stuck in a `match` on a literal
decision (`Nat::equation(64, w)`) is followed through it, and a closed value
(`word_value(s0)(64)`) to its value. The walk goes through the interface
boundary as conversion does: another module's `interface fn` at an open
argument is not unfolded, so a spelling is never one the gate would refuse
(`interface_head_folded`, the negative control).

When the sides stay apart, grind reads the next spelling of each stuck term
under them (`spell_from`): the spelling is read into the graph and joined to
the term as written by a `defn` edge, whose `refl` the kernel checks. That
is the hand chain's step, taken one δ at a time: `loop_finish(Fun::post(…),
…)(…)` → `Fun::post(…).eval(…)(…)` → `branch(x, …).eval(…)(…)`, which
`branch_false`'s pattern meets. A pass spells at most `grind_spell_cap()`
terms, a term already tried is not tried again, and at most
`grind_spell_passes()` passes run, each followed by the ordinary rounds.

A premise no equation meets can still be one the graph decides with a
**stand-in**: `branch_false` needs `values(1, x).head_bit() = False`, where
`values` is `Valuation::set(bound, x, bit_value(False))`; the term is
built from the instance's nodes (`app_node`), the graph closes, and the
premise is proved by its class. A disequality premise (`o0 ≠ x`) is proved
from a disequality read whose sides are its sides' classes, either way
round (`by_diseq`: `λ e => apart(…)` over the explanation).

**Dependent congruence.** Spelling joins valuations (`Valuation()` is
`(w: Nat) → Nat → BitVec(w)`), so a congruence step can be one through a
dependent application `q(64)`. `congr_dep` carries a motive `B: A → Type`
no unifier finds (`?B(w) ≟ Nat → BitVec(w)` is outside the pattern fragment
the elaborator solves); `dep_motives` reads it off the function's type,
opened, as `Lam(w, body)`, before anything infers the proof. A type handle
where a term is expected now stands for its code (`reify`), which is what
lets a motive's body be a type.

### 15.2 What the cost was, and the incremental graph

The probe's first runs held the value arena past 8 GiB: the arena is not
freed during a tactic run, so what bounds a run is its **total** fuel across
evaluations, not one evaluation's. Profiled by evaluation, the cost was the
graph, not the spelling:

- **Linear structures.** The nodes and classes were lists, so every `find`
  and node lookup walked the graph. They are now `Array`s over `NatMap`
  (`lib/std/data/nat_map.hthr`), a binary trie keyed by `Nat`: a lookup is a
  step per bit of the key. Node ids must stay numerals (`+ 1`, not `Succ`),
  or `half` walks a unary chain.
- **`let` is inlined.** A `let` read three times is computed three times; a
  value a recursion reads after a `settled` is computed again in the next
  evaluation. `shared(a, λ x => …)` (in `nat_map`) binds it once.
- **Whole-graph passes.** Congruence closure compared every node's
  signature every pass, and e-matching rebuilt the class table every round.
  The graph now keeps its class table (`class_rows`), each class's parents,
  and a signature index (`sigs`, by the key of the first two children's
  classes), and closes **incrementally** as egg's rebuilding does: a node is
  read again only when it is new or a child's class was merged
  (`relabelled` puts the absorbed class's parents on `dirty`). A node read
  is merged with the first node filed under its key that is congruent to it
  in another class; leaves are never read. grind closes a batch of
  `grind_settle_batch()` dirty nodes per evaluation.
- **Congruent copies.** A node merged with its congruent twin leaves its
  class's row (`unlisted`): it has the same operator over the same classes,
  so matching through the twin finds everything it would. Without that, a
  pattern item meeting a class visited every congruent copy, and a match
  through nested copies was found once per combination; on the probe that
  was about half the remaining total fuel.

None of this touches the soundness proofs' reasoning: `Agrees` reads only
the nodes and the representatives, every new field is carried through by
conversion, and every merge is still checked at the graph it is made in
(`settle_one_agrees`, `settle_all_agrees`, `close_agrees`). Hash-consing
looks only in its key's bucket (`node_among`), and `add_at` with a found
node leaves the graph unchanged, so a bucket that misses only costs a
duplicate node.

Costs, as shapes: a lookup is logarithmic in the graph; a close reads each
dirty node against its bucket; a merge relabels the representatives array
(linear, lazily, which is what union by rank would fix) and moves the
absorbed class's rows. On the probe the remaining total is spread over atom
search, the uses index, stamping, explanation and matching, none above a
fifth.

### 15.3 Not done

- Union by rank and the representatives kept as a forest
  ([egraph-scaling-structures](../../issues/egraph-scaling-structures.md)).
- The arena: a tactic run's values are never freed, so total fuel is the
  bound. A host that reclaimed what no live value reaches between requests
  would turn it back into a per-evaluation bound.
- Which heads to spell: today every stuck head under the sides, up to the
  caps; a lemma-directed choice (spell toward a head some pattern names)
  would spell less.
