# grind: congruence closure whose failure is the graph

Issue: [grind-port](../issues/grind-port.md) (milestone `tac-general`).
Round 1 built `lib/std/tactic/grind.hthr`, the `Spine` host request, and the
probes in `lib/_tests/std/tactic/grind_tests.hthr`.

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
| R1 (this) | `Spine`; congruence closure over the goal's equations and hints at their instances; proof by explanation; the graph as the failure | the hand `trans`/`cong` steps of a library proof close by `grind_with` with its lemmas as hints, and a failure names the missing equation's classes |
| R2 | e-matching ([grind-e-matching](../issues/grind-e-matching.md)): equations under binders, from the locals and a hint list, instantiated by matching their patterns against the graph's terms modulo the classes; the used hints reported on success | `grind_with([List::append_assoc, List::append_nil])` closes an append tower with no instance written, and reports which hints it used |
| R3 | constructor facts and disequalities ([grind-constructor-facts](../issues/grind-constructor-facts.md)): injectivity, disjointness, `≠` hypotheses, `False` goals | `Cons(a, as) = Cons(b, bs)` gives `a = b`, and `Nil = Cons(x, xs)` closes any goal |
| R4 | case splits and theories ([grind-splits-and-theories](../issues/grind-splits-and-theories.md)): split on a `match` scrutinee in the graph (`split_all`'s `Cases`), and exchange equalities with `omega`/`ring` | a goal needing a `Bool` case split and a linear fact closes, and the failure is the decision tree |

The graph's pure half is now a generic library (§8).

R2 needs one host addition: a tactic can only report on failure today. The
used-subset report ([lemma-selection-and-search](../issues/lemma-selection-and-search.md)
piece 3) wants a note on success, a request that records notes without ending
the run; R2 designs it.

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

What the library does not have yet: a `≈` path algebra with `Proper`
congruences ([egraph-setoid-path-algebra](../issues/egraph-setoid-path-algebra.md)),
a theorem that a hash-consed `add` returns a node of the requested value
([egraph-add-value-theorem](../issues/egraph-add-value-theorem.md); clients
that need it use `fresh`), and union by rank or a signature table
([egraph-scaling-structures](../issues/egraph-scaling-structures.md), §5).

