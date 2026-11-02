# grind: congruence closure whose failure is the graph

Issue: [grind-port](../issues/grind-port.md) (milestone `tac-general`).
Round 1 built `lib/std/tactic/grind.hthr`, the `Spine` host request, and the
probes in `lib/_tests/std/tactic/grind_tests.hthr`. Round 2 added lemmas
instantiated by e-matching, the `Say` host request and `grind_report` (§9).
Round 2½ proves lemmas' premises at their instances (§11), and the
reader takes conjunctions and records of equations apart (§12).

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
(`docs/host-elaboration-interface-design.md`), like `mono` and `norm_num`.
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
selection language ([lemma-selection-and-search](../issues/lemma-selection-and-search.md))
and a machine-readable diagnostics stream
([ai-facing-tooling](../issues/ai-facing-tooling.md)).

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
[ai-facing-tooling](../issues/ai-facing-tooling.md)'s, and when it lands the
report needs no change. The 2026-08-06 cross-reference in the issue asks that
the handed-back e-graph be (a serialization of) the goal-keyed decision tree
of [parallel-checking-and-caching](../issues/parallel-checking-and-caching.md);
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

## 6. Rounds

| round | builds | done when |
|---|---|---|
| R1 (done) | `Spine`; congruence closure over the goal's equations and hints at their instances; proof by explanation; the graph as the failure | the hand `trans`/`cong` steps of a library proof close by `grind_with` with its lemmas as hints, and a failure names the missing equation's classes |
| R2 (done, §9) | e-matching ([grind-e-matching](../issues/grind-e-matching.md)): equations under binders, from the locals and a hint list, instantiated by matching their patterns against the graph's terms modulo the classes; the used hints reported on success | `grind_using(["List::append_assoc", "List::append_nil"], [])` closes an append tower with no instance written, and `grind_report` says which it used |
| R2½ (done, §11) | premises ([grind-lemma-premises](../issues/grind-lemma-premises.md)): a binder no side binds and nothing depends on is proved at the instance, by the graph, a local or hint, or `Synth` | an order premise by a local and an equation premise by the graph close, and the report names an unproved premise |
| R3 | constructor facts and disequalities ([grind-constructor-facts](../issues/grind-constructor-facts.md)): injectivity, disjointness, `≠` hypotheses, `False` goals | `Cons(a, as) = Cons(b, bs)` gives `a = b`, and `Nil = Cons(x, xs)` closes any goal |
| R4 | case splits and theories ([grind-splits-and-theories](../issues/grind-splits-and-theories.md)): split on a `match` scrutinee in the graph (`split_all`'s `Cases`), and exchange equalities with `omega`/`ring` | a goal needing a `Bool` case split and a linear fact closes, and the failure is the decision tree |

The graph's pure half is now a generic library (§8).

R2 added one host request, `Say`: a tactic could only report on failure,
and the used-subset report ([lemma-selection-and-search](../issues/lemma-selection-and-search.md)
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
once ([egraph-library](../issues/egraph-library.md)). It is
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
([egraph-ematch-soundness](../issues/egraph-ematch-soundness.md)), a `≈` path algebra with `Proper`
congruences ([egraph-setoid-path-algebra](../issues/egraph-setoid-path-algebra.md)),
a theorem that a hash-consed `add` returns a node of the requested value
([egraph-add-value-theorem](../issues/egraph-add-value-theorem.md); clients
that need it use `fresh`), and union by rank or a signature table
([egraph-scaling-structures](../issues/egraph-scaling-structures.md), §5).

## 9. Lemmas by e-matching (round 2, 2026-11-02)

Issue: [grind-e-matching](../issues/grind-e-matching.md).

### 9.1 The surface

| call | facts |
|---|---|
| `grind()` | the goal's locals |
| `grind_with(hints)` | the locals, and the facts the terms `hints` prove |
| `grind_using(names, hints)` | the above, and the lemmas `names` names, resolved where the `by` is (`"List::append_assoc"`) |
| `grind_report(names, hints)` | `grind_using`, and on success a `tactic-report` warning naming the hints and lemmas the proof cites and the ones it does not |

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
node) or misses a binder; then the right one. A lemma neither of whose sides
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
added, or that its pattern never matched a term of the graph; that is the
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
the proof cites are named separately ("and the locals k, h").

### 9.5 Found on the way

A `let` above a recursive `match`, bound from a parameter the self-call
changes, keeps the top call's value: `saturate`'s first draft bound the
closed graph above `match rounds` and found the same instances every round.
The elaborator accepts the shape and computes the wrong function
([recursion-let-reads-changing-parameter](../issues/recursion-let-reads-changing-parameter.md));
`saturate` now matches on `rounds` first.

## 10. The library sweep (2026-11-02)

Issue: [grind-library-sweep](../issues/grind-library-sweep.md). Of the
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

1. **Premises** ([grind-lemma-premises](../issues/grind-lemma-premises.md)):
   the most common reason a named lemma cannot be used. Most are a `Bool`
   test or an order fact the branch already has as a local.
2. **Definitional equalities**
   ([grind-definitional-equalities](../issues/grind-definitional-equalities.md)):
   the number and integer lemmas are stated on the constructors' functions
   (`isucc`, `negOfNat`), while goals hold the computed forms. The hand
   proofs cross these silently, because the kernel compares up to
   conversion.
3. **Conjunctions** ([grind-read-conjunctions](../issues/grind-read-conjunctions.md))
   and **constructor facts** ([grind-constructor-facts](../issues/grind-constructor-facts.md)):
   small readers, each needed by a whole family of native proofs.
4. **Case splits** ([grind-splits-and-theories](../issues/grind-splits-and-theories.md)):
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
  [diagnostic-operator-resugaring](../issues/diagnostic-operator-resugaring.md),
  which grind's report is now a customer of.

No library proof was replaced. The proofs grind closes today are the ones
whose instances are written out, and a `grind_with` naming those instances
is no shorter than the hand `trans` chain. The replacements come with
premises (§11.4).

## 11. Premises (round 2½, 2026-11-02)

Issue: [grind-lemma-premises](../issues/grind-lemma-premises.md). The
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
   evidence rules of [facts-on-demand](facts-on-demand-design.md). A closed
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
  [grind-premise-tactic](../issues/grind-premise-tactic.md).
- **Premises by a decider.** An order premise that needs arithmetic
  (`p < k + i` from `i <= p`) is `omega`'s; that is the theory exchange of R4.
- **Cost.** Each premise asks one `Defeq` per local and hint, and an
  equation premise closes the graph once more. No client is near the round
  caps; if one is, a cheap key on the premise's head before `Defeq` is the
  first thing to add.


## 12. Conjunctions and records (2026-11-02)

Issue: [grind-read-conjunctions](../issues/grind-read-conjunctions.md). The
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
