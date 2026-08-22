---
title: "Lightweight goal-directed application: auto-refl and apply"
status: closed
labels: [frontend,elaboration,syntax,proofs,ergonomics]
created: 2026-07-24
updated: 2026-08-22
---

Two ergonomic surface features (user-requested 2026-07-24; not scheduled).
Both use expected types and Heather's existing metavariable/goal machinery,
but neither introduces a kernel construct. Auto-refl is proof-specific;
`apply` is deliberately not. It is an alternate, goal-oriented layout for an
ordinary application and should be usable in ordinary programs as readily as
in proofs.

## 1. Auto-refl (trivial-closer for empty/residual goals)

Goal: `theorem two_two(): 2 + 2 == 4 {}` auto-passes — an empty proof block discharges by reflexivity/computation.

- **Mechanism**: in *checking* position, an empty block (later: any residual `?_`) gets ONE speculative `refl` attempt — construct `Refl`, run the existing checking path, keep it iff the kernel accepts; else the goal stays open (-> the goal-listing error from [[goal-holes]]). It is the simplest hardwired instance of that issue's future solver slot (`on _: _ := solver(goal)`).
- **'ignored for values' falls out**: refl only shapes an `Id` goal, and checking-only means a `fn` result type (not generally an equality) offers nothing to close — no default fires in value position.
- **DECIDED — conservative**: speculation is tied to the empty block ('I didn't write a proof' is the trigger). `refl` never becomes a tolerant no-op: a load-bearing `refl` silently doing nothing would hide mistakes.
- **MVP is independent**: empty-block -> refl-attempt needs only a parser tweak (allow `{}`) + a checking-position elaborator hook; no [[goal-holes]] engine required. Could land opportunistically.

## 2. `apply`: ordinary application in goal order

The design target is **not** a special tactic language. `apply` presents the
arguments of an ordinary application as restricted checking scopes, in the
same telescope order the call already owns. It performs no lemma search and
has no proof/value distinction.

The unary form wraps the remaining expression:

```heather
apply outer;
apply middle;
value
```

and elaborates to the ordinary term:

```heather
outer(middle(value))
```

Constructors and program values are first-class customers:

```heather
apply Inr;
compute_value(input)
```

is `Inr(compute_value(input))`. The whole application is elaborated in its
original checking position; the wrapper is not inferred in isolation, so
constructor result indices and implicit arguments retain the information from
the expected return type and supplied bodies.

### 2.1 Multiple goals are multiple argument bodies

For a callee with several remaining explicit parameters, each parameter is a
goal: an expression checked at that parameter's domain. The landed spelling
uses contextual `give` for every non-final argument, with the final goal
completed by the ordinary trailing expression:

```heather
apply trans;
give first;
second
```

The parser lowers this to:

```heather
trans(first, second)
```

`give` makes non-final completion visible without borrowing proof-specific
language such as `exact`; it reads just as naturally for program inputs.
Braces remain available around a
non-final body containing its own statements:

```heather
apply trans;
give {
    let x = prepare(input);
    produce_left(x)
};
produce_right(input)
```

Requiring `give` for every non-final goal avoids a
future ambiguity with effectful expression sequencing: bare `first; second`
must not silently alternate between "two arguments" and "discard `first`, then
return `second`". It also makes nested multi-goal applications locally scoped.

Parsing lowers the bodies to one ordinary n-ary `App`, with a `goal_oriented`
provenance bit retained for the promotion policy and its diagnostics below.
The kernel sees only the resulting application.

### 2.2 Normal implicit inference runs across every goal

`apply` does not turn implicit parameters into immediate goals. They remain
Heather's ordinary flexible per-call metavariables and consume information
from the expected result and every explicit argument body.

For example:

```heather
theorem trans({a, b, c: Int}): a <= b → b <= c → a <= c
```

applied at an expected `x <= z` begins conceptually as:

```text
a := x
b := ?b
c := z
first  : x <= ?b
second : ?b <= z
```

The expected result solves `a` and `c`. If `first` infers a type `x <= y`,
ordinary unification solves `b := y`; the second body is then checked at
`y <= z`. A later inferable body may solve an earlier unknown as well: the
existing deferred-argument retry-to-fixpoint is the right mechanism, not a
new tactic-state solver.

Named arguments are the direct, local escape when the writer already knows
the intermediate:

```heather
apply trans(b := midpoint);
give prove_left(midpoint);
prove_right(midpoint)
```

This is often preferable to deferring `b`, and keeps the choice at the source
site that created the application.

### 2.3 Promote only genuinely unsolved implicits

If ordinary expected-type solving, argument inference, and deferred retries
reach a fixpoint with `b` still unknown, `apply` may **promote** that flexible
implicit meta into a declaration-scoped named goal:

```text
?b : Int
```

Promotion is late and one-way. Promoting immediately would make `b` rigid and
prevent later argument bodies from inferring it. The intended order is:

1. create ordinary flexible implicit metas;
2. use the expected result and every inferable body;
3. retry checking-only/deferred bodies to a fixpoint;
4. promote remaining implicit metas to named goals;
5. substitute those goal globals into blocked argument domains and retry them;
6. elaborate explicit holes there as ordinary dependent goals.

That permits a fully deferred application such as:

```heather
{
    apply trans;
    give ?left;
    ?right

    on ?b := midpoint;
    on ?left := prove_left(midpoint);
    on ?right := prove_right(midpoint);
}
```

The existing `?name`/`on` mechanism remains the only persistent goal store.
Flexible scratch metas do not escape their application call: they are either
solved there or converted to ordinary goal globals before the call returns.
Ordinary call syntax continues to report an inference failure; automatic
promotion is opt-in through the goal-oriented `apply` spelling.

### 2.4 A promoted goal must say where it came from

The parameter name is API, but the name alone is insufficient. Every promoted
implicit records structured provenance:

- the source span of the `apply` head that failed to infer it;
- the resolved callee and its declaration, when nameable;
- the callee parameter name and position;
- the expected result which supplied the information that was available; and
- which later argument goals remain blocked on it, when known cheaply.

An unfilled-goal diagnostic should read approximately:

```text
?b : Int
promoted from implicit parameter `b` of `trans`
at path/file.hthr:line:column (`apply trans`)
```

and the primary or secondary caret must point back to that `apply`, not merely
to the end-of-block goal listing. A future infoview should expose the same
origin as navigable metadata, so selecting `?b` answers both "what is this?"
and "which application asked for it?" without reconstructing the call from
its type.

The provenance is data, not preformatted prose: terminal rendering, editor
navigation, and a future code-action that inserts `b := ...` on the apply line
must consume the same record. Goal-name collisions retain the existing
ordinal suffix convention (`b`, `b.1`, ...), while origin metadata preserves
which is which.

### 2.5 Boundary from a tactic language

`apply` may expose several checking goals and promote failed inference, but it
still:

- performs no declaration or lemma search;
- uses no proof-only classification (`Prop` is not required);
- never guesses which explicit parameter is a premise;
- follows the callee's explicit/implicit binder API;
- compiles to the same n-ary application the writer could spell directly;
- uses explicit `?name`/`on` for obligations that survive the application;
- reports ordinary call/type errors when a supplied goal body is wrong.

This is the useful part of tactic-style information flow without making
ordinary term code the disfavored language. Programs may deliberately use
multiple goal bodies to construct several inputs before returning the final
application.

## Sequencing

`apply` is implemented: the `apply`/`give` grammar, n-ary lowering, ordinary
cross-argument inference, automatic late meta-to-goal promotion, structured
source provenance, named inline goals, and dependent-goal retries all share
the existing application and goal machinery. Future infoview and code-action
consumers may expose the provenance more richly; no elaboration slice remains
for the construct itself. It interacts with [[match-recursion]] because
self-call proofs share the block surface. Tracked in [[frontend-roadmap]].

## Log

- 2026-07-24: Unblocked by [[goal-holes]] landing: blocks now have a statement grammar (`Block` + `let x (: T)? = e;` + trailing `on`), which was the stated dependency for even the cheap `apply` slice, and the goal engine (holes as decl-scoped Ψ-metas, `on` discharge, unfilled-goal listing) is the substrate the multi-premise `apply trans` slice wanted. Note for whoever picks this up: a hole is currently refused inside an `on` right-hand side, so `apply`'s desugaring must place its holes in the block body, not in a discharge.
- 2026-08-02: A future consumer, recorded off the certifying-generator v2 round (2026-08-02, docs/ir-simulate-design.md section 13 note 9): quantitative fuel/cost reasoning. The design settled on 'modality in statements, numbers hidden' — Converges is a computes-in-finite-time possibility modality and specific bounds are compositional debt — but consumers that DO want the number (complexity certificates, cost-model refinements) are exactly a goal-solver workload: a fuel bound is a witness a tactic should synthesize (run the mini-evaluator / compose per-instruction costs) and a human should never spell. When the solver slot lands (goal-holes' on _: _ := solver(goal)), bound synthesis and le-discharge are natural early tactics alongside auto-refl.
- 2026-08-05: MVP slice scheduled as [[auto-refl-empty-block]] (2026-08-05 ergonomics round); apply and the solver slot stay here.
- 2026-08-05: auto-refl MVP landed ([[auto-refl-empty-block]], 2026-08-05); the solver slot and apply remain here.
- 2026-08-19: The post-I-prime proof-style review split introduction into
  [[sequent-binder-expression]]. It is goal-directed but not automation:
  `intro x; rest` is simply the checking-position face of `λ x => rest`.
  `cases` is already [[split-on-arms]], including a default arm; do not grow
  this issue into an umbrella tactic language.
- 2026-08-22: Apply direction substantially sharpened. It is an ordinary
  n-ary application presented as argument goals, useful for programs and
  proofs. Non-final goals need explicit scope (then considering `exact` or
  bounded blocks; the landed spelling is `give`), the
  final expression is the lightweight implicit completion, and ordinary
  implicits remain flexible across all bodies. Only an implicit still unsolved
  at fixpoint is promoted to a named `on`-dischargeable goal. Promotion carries
  structured provenance back to the originating apply/callee/parameter so a
  diagnostic or infoview can navigate there, while a named argument such as
  `b := midpoint` remains the immediate inline escape.
- 2026-08-22: Landed the first implementation slice. Contextual
  `apply f; give a; b` lowers to one ordinary n-ary application, the final
  body nests naturally for unary chains, `apply(x)` remains an ordinary call
  to a function named `apply`, and `apply f(p := value)` carries named values
  onto the generated call. The AST retains `goal_oriented` provenance.
  Programming, proof, dependent implicit-inference, inline named-goal, and
  compatibility tests landed. Automatic promotion remains open because the
  current declaration goal world must reserve every global slot before
  elaboration; an inferred meta is not present in the syntactic hole count.
- 2026-08-22: Automatic promotion landed without a syntactic approximation or
  fixed limit. A speculative declaration elaboration records the exact extra
  goal-prefix capacity demanded by unsolved apply implicits and restarts the
  uncommitted declaration with that stable Ψ prefix. Promotion happens only
  after expected-type solving, argument inference, and deferred retries reach
  a fixpoint; blocked solver and explicit-argument obligations are retried
  afterward. Multiple telescope-dependent implicits promote in order. Each
  goal carries structured callee, parameter, parameter-index, and apply-span
  provenance, while ordinary calls retain their inference failures.
