# Traits and instances: design discussion record

Status: **design discussion, pre-doc-round** (2026-08-07). This file is the
full record of the traits/typeclass design conversation, kept so nothing is
re-derived; the implementing rounds will each carve their specification out
of it (and should tighten, not restate, what they take). Tracking issue:
`issues/traits.md`.

Adjacent decisions live where they are owned: the `Compile` certificate shape
in `docs/archive/compile-typeclass-design.md` (v1 landed; its §5 "class layer" is
superseded by this design — see §10 here), records in
`docs/language/surface-records.md`, the meta-layer facts in
`docs/metaprogramming/in-language-map-design.md`, resolution's eventual in-language home in
`issues/generators-in-the-language.md`.

The design principle, inherited from the Compile sketch and applied to the
whole feature: **resolution is policy; the kernel checks everything that
crosses into a term.** A resolver — even a user-programmable one — only ever
*proposes* a value; the worst failure mode is slow or failed elaboration,
never a wrong proof. Every ambitious choice below is safe for exactly this
reason.

---

## 1. The three layers

Designed together, built in order. Nothing in an earlier layer may assume a
later one is primitive — in particular, nothing may assume resolution is
built into the elaborator forever.

1. **Semantics** (§2–§5): class = parameterized record declaration; instance
   = namespace of ordinary declarations plus an assembled record value;
   `extends` = flattening plus a canonical-value discipline. All sugar over
   landed features (records, polymorphism, modules, type-owned namespaces).
   Useful on its own: Mathlib-style algebra becomes writable.
2. **Default resolution** (§6–§8): a deterministic, terminating,
   mode-directed backchainer with a canonical-derivation table, implemented
   natively (Rust) against a pinned interface — the same migration pattern
   as the generators: Rust prototypes the in-language function's exact
   contract.
3. **Programmable resolution** (§10): the layer-2 interface re-implemented
   as a heather meta-function once context computation lands; user-supplied
   solvers slot in beside the default. Blocked on the enumerated missing
   meta-layer features (the 2026-08-02 ch. 07 expressiveness verdict), not
   on an unexplored question.

## 2. Classes are parameterized records

A class is a record parameterized by its carrier(s):
`class Monoid<A> { unit: A, op: A -> A -> A, unit_op: ..., ... }`. A class
declaration and a `record` declaration produce the same kernel artifact; the
`class` keyword adds registration for resolution (§6) and the `extends`
discipline (§5). Trait-vs-typeclass is resolution policy, not semantics
(sketch-round decision, unchanged).

**Carrier as parameter, not as field.** Resolution keys on the parameter,
and it matches Lean's own choice for classes. Bundled records
(`record Mon { carrier: Type, ... }`) are *available* — they landed with the
Type Session, 2026-07-27 (`crates/elab/tests/universe.rs:131`; the Compile
sketch's §6 "blocked on the level-1 record round" was stale on this point) —
and remain the right form for quantifying over structures themselves
(`Grp` as objects). The two forms coexist; classes use the parameterized
one.

**No special target indexing.** `Compile[Cpu]`-style class indexing
dissolves under this semantics: a class needing a target is a class with one
more ordinary parameter, coherence keyed on all parameters. No indexing
machinery exists. (Separately, `Compile` itself should not carry a target at
all — §10.)

## 3. Instance declarations

Syntax: `instance Monoid<Rat> { ... }` — angle brackets, no `for`. The
`for T` spelling privileges one type parameter and breaks at
multi-parameter classes (`Coe<A, B>`); since the semantics is "record
parameterized by types," the bracket form is simply the truth.

Two forms, because an instance is just a value:

- **Block form** — the centerpiece. An `instance` block is a **namespace of
  ordinary declarations plus a generated record value**. Each `fn`/`theorem`
  written inside elaborates, in order, to a real top-level global under the
  instance's namespace (`Rat.Monoid.op`, `Rat.AddCommGroup.zero_add`); the
  instance value is the record literal assembled from those globals,
  generated at the end of the block.
- **Literal form** — `instance Monoid<Rat> { op := Rat.op, ... }` assembles
  from previously declared globals, for the "the simple theorems are needed
  much earlier in the file" workflow.

The block form **dissolves Lean's name duplication** rather than managing
it: Lean has `Rat.zero_add` *and* an opaque instance field because the
instance is one anonymous term and fields are not names. Here the block
members *are* the globals and the record merely references them — one
definition per fact, reachable both as `Rat.AddCommGroup.zero_add` and as a
projection of the instance.

**Within-block references and the circularity boundary.** Later members use
earlier members by name as ordinary globals (sequence handles everything —
the "in Lean this is rough" case is free here). The one genuinely
unreachable thing: a member that wants the class's *generic* theorems
applied to the carrier before the instance exists. The answer is the
telescope discipline of §5 — declare the parent instance first, use its
generic consequences, then extend.

## 4. Inheritance: `extends`, flattening, and the canonical-value invariant

`class AddCommGroup<G> extends AddGroup<G>, AddCommMonoid<G>` makes two
separable claims, both accepted:

- **Representation: flattened.** The child record contains the parent's
  fields directly (field-list concatenation with dedup at declaration
  time). Flattening is what makes shared-ancestor diamonds definitionally
  trivial *when the fields are the same fields* — both projection paths to
  `AddMonoid` hit literally the same components.
- **Derivation: parent instances by projection.** A child instance yields
  parent instances, and the resolver chases these (§6).

Flattening alone is Lean-post-structure-eta and is not enough: Lean's
residual diamond problem is *data fields with defaults* derived differently
along different paths — the reason every Mathlib `AddCommGroup ℚ` instance
hand-writes `nsmul := (· * ·)`/`zsmul := ...` is that the default (iterated
addition) would otherwise produce an `AddMonoid ℚ` on one path that is not
definitionally the one on another path ("forgetful inheritance," a
library-wide manual discipline enforced by linters). The structural fix:

**One canonical value per (class, carrier).** Direction-symmetric:

- Parent instance already declared → the child's inherited fields **fill
  from it by reference**; the block writes only what is new. A derived
  parent projection is then the declared parent, not a copy.
- Parent not declared → the child declaration **synthesizes and registers**
  the parent instances as its own projections; those become canonical.
  (This is what keeps deep hierarchies writable in one declaration —
  strict parents-first would mean five bottom-up declarations to say
  `AddCommGroup<Rat>`.)

Either way exactly one `AddMonoid<Rat>` value exists and every path reaches
it; diamonds collapse structurally rather than by discipline. Defaults are
computed once, where the canonical value is minted, never once per path.

**Overrides owe agreement proofs.** Overriding a field that a canonical
value already holds (the `nsmul`-for-efficiency case) creates a genuine
second value, so the declaration owes agreement: kernel-checked
convertibility with the inherited value at declaration time, or a
propositional-equality field where conversion won't reach. Incoherence
becomes a *checked declaration error*. Lean cannot cheaply demand this; we
have the kernel sitting at elaboration time. This is the house principle
one level down — override is safe *because* it carries a certificate — and
it is also the escape that keeps §6's overlap rule livable.

Why Lean doesn't do this, recorded so the comparison isn't re-litigated:
path-dependence (structure eta arrived after the idiom set; one bundled
declaration per type, parents projected downward) and the verbosity of
strict parents-first on a deep hierarchy — which the synthesis direction
above answers. Hierarchy *depth* as a modeling style remains a library
discipline question, not a language commitment.

## 5. Resolution: ascending scopes, automatic

Implicit instance arguments resolve automatically — the whole point of
typeclasses; this is a deliberate exception to the house "force explicit"
habit. Search is by ascending scope:

1. local variables of instance type (including a scoped
   `let instance C<T> = v;` override — which shadows locally and never
   touches the canonical table),
2. function parameters (instance-implicit `requires` binders, §6),
3. instances in enclosing scope / the current module,
4. the wider registry (the class's module, the carrier type's module,
   imports).

An explicit value in scope always wins. The registry entry point is the
`instance` declaration itself (declaring *is* registering); whether
ordinary globals can additionally be marked as instances after the fact
(attribute-style) is an open question (§12).

## 6. Generic instances, and the four disciplines of the resolver

A conditional instance is a dictionary-valued function:

```heather
instance<A, B> Monoid<Pair<A, B>>
    requires ma: Monoid<A>, mb: Monoid<B>
{
    fn op(x: Pair<A, B>, y: Pair<A, B>) -> Pair<A, B> {
        Pair(ma.op(x.fst, y.fst), mb.op(x.snd, y.snd))
    }
    ...
}
```

elaborating to an ordinary global
`Pair#Monoid<A, B>(ma: Monoid<A>, mb: Monoid<B>) -> Monoid<Pair<A, B>>`.
Statable today (records + polymorphism); `requires` is the
instance-implicit case of §8's mechanism. Expressiveness for mathematics
lives in this layer and is deliberately unconstrained: quantifying over
structures is Π over record types, multiple structures on one carrier are
named values plus scoped overrides.

Instances are Horn clauses; resolution is logic programming. Lean runs an
undisciplined logic program (backtracking, priorities, declaration-order
sensitivity, defeq unfolding mid-search, heuristic loop detection,
anonymous result blobs). Each pathology gets a discipline; the rules are
few and *statable* — learnable by reference rather than by folklore, which
matters for AI-assisted development too:

1. **Canonical named derived globals — memoization is canonicalization.**
   The first resolution of `Monoid<Pair<Nat, Rat>>` mints a global
   (`Pair#Monoid` applied to the canonical `Monoid<Nat>`, `Monoid<Rat>`),
   registers it as *the* value for that (class, carrier-syntax) key, and
   every later resolution returns it by reference. The performance cache
   and the coherence invariant are the same object; §4's invariant extends
   to derived instances; "which multiplication is this term using" is
   answered by unfolding a name. Locals and scoped overrides (§5) shadow
   the canonical table locally, never mutate it.
2. **Modes on the class, overlap checked at declaration.** Class parameters
   are declared search *inputs* or *outputs* (Lean's `outParam` / Haskell
   fundeps, made explicit and first-class). Resolution keys on input
   positions only. Two instances whose input heads unify is a
   declaration-time error — unless the overlap carries a §4 agreement
   proof. This replaces priorities and declaration-order sensitivity
   entirely: the resolver never faces a choice, so its result is a function
   of the goal, not of the database's history. (Rust's coherence rules are
   the precedent that this is livable; the agreement-proof escape keeps it
   livable for mathematics.)
3. **Termination by structural decrease, checked at declaration**
   (default). Each `requires` subgoal must be structurally smaller than
   the instance head on input positions (Paterson-style):
   `Monoid<A> → Monoid<Pair<A, B>>` passes; self-feeding loops are refused
   when declared, not detected when they hang. Escape: a named instance
   value applied explicitly. **Held as the default, not yet as doctrine** —
   the open question (§12) is where legitimate mathematics wants
   non-structural instances and whether the named-value escape is enough
   there.
4. **Metavariables by the scheduler, not by search.** Resolution fires only
   when the goal's input positions are meta-free — a withheld obligation
   (the unifier round's Sol::Withheld machinery, 2026-08-06), retried to
   fixpoint as solving progresses, reported at the argument span if it
   stays blocked. Output positions may be metas; resolution solves them.
   This is `outParam`/`semiOutParam`'s purpose obtained as a corollary of
   landed machinery.

## 7. Diagnostics: the search state comes back as data

With resolution deterministic, a failed search has a well-defined trace:
which clause matched, which subgoal failed, what the canonical table and
scope contained. That trace is the diagnostic — and, per
`issues/ai-facing-tooling.md` (and the `grind-port` e-graph doctrine), it
comes back as *data*, not prose. Lean's "failed to synthesize" black box is
a diagnostics decision, not a necessity.

## 8. Auto-params: one mechanism under instance search

Instance implicits are the well-known default of a general feature: **a
default argument may be a solver run in the caller's elaboration context.**

```heather
theorem blah(x: Nat, hx: x > 0 := infer) : ... { ... }
```

`infer` scans the caller's scope for a value of the goal type (which is
exactly what instance search does, so instance implicits are `:= infer`
with registry search); other solvers (`:= omega`-style, eventually
user-written — §10) take work off callers. This unifies instance
resolution, auto-params, and the filed goal-solver directions
(`congruence-by-anti-unification`, `lemma-selection-and-search`) as one
feature with a good default.

Lean's auto-params are weak for a diagnosable reason, recorded so we don't
inherit it: the tactic fires at whatever moment elaboration reaches the
argument — goal metas unsolved, no deferral, no retry, opaque failure. The
fix is the same scheduling discipline as §6.4: a solver-default argument is
a withheld obligation, run when its goal type is meta-free, retried to
fixpoint, honest about being blocked. The scheduling machinery is already
paid for.

## 9. Performance and determinism

- **Memoization is structural** (§6.1) and keyed intensionally —
  (class, carrier-syntax, scope-fingerprint for the non-canonical part).
  Lean's synthesis cache is bolted on; ours is the coherence invariant.
- **Determinism is non-negotiable**: `elaboration-determinism` is the trust
  spine for parallel checking and the certified cache, so the resolver —
  including user-written layer-3 solvers — must be a deterministic function
  of (goal, scope), with search order specified, not emergent.
- **The interpreted-resolver worry is bounded**: layer 2 is native; by the
  time layer-3 heather solvers exist, hot ones can be compiled via the
  machinery they serve — `Compile` certifying the resolver is the intended
  endgame, not a joke.

## 10. Layer 3: programmable resolution, and what the calculus says

The ambition: `class`/`instance` as declaration sugar is layer 1; *finding*
an instance is, eventually, a **heather-level function the elaborator
invokes** — "run a program in the caller's context" — with typeclass search
as the shipped default and user solvers beside it. This is not a hack
around the theory; it is the theory's target (DeLaM's layer-m programs over
open code and contexts).

Grounding, from the landed record:

- The ch. 07 expressiveness reading (2026-08-02, on
  `generators-in-the-language`) enumerated the missing features: opaque
  globals, no oracle, no code equality, **no context computation**. "Scan
  the caller's context" is the fourth item. Blocked on a known finite
  list, not an open question.
- **The resolver's currency is syntax.** A layer-p type can never appear
  inside layer-c code (binding invariant `i' ≤ i`;
  `docs/metaprogramming/in-language-map-design.md` §3), so an in-language resolver receives
  the goal *as quoted syntax* (`CodeTy`), consumed by the analysis story's
  code recursors. This agrees with, rather than fights, the intensional
  keying decision: resolution was already a function over syntax. The
  layer-2 contract is therefore written over quoted goals from day one:
  **resolver: (quoted goal type, scope) → term**, implemented natively now,
  swapped later.
- **Types travel into code as their codes.** The better notion for
  generic-over-a-type templates is not cross-stage persistence (rejected on
  principle: a persisted semantic value has no syntax, so recursors could
  never analyze past it — and the certifying-generator thesis depends on
  intensional analysis). It is type *splices* — `code { fun (x: $A) => … }`
  with `A : Code(Γ ⊢ Ty)`, the local/surface form of the pattern
  `family-types-as-code-defs` already runs at the global level
  (`El(D#fam^δ)`). Kernel formers for this exist ("complete and
  unreachable"); whether the surface slice is elaborator-only is a
  ch. 04–06 reading for that round.

**`Compile` as a client, target indexing struck.** The compiler is simply a
consumer that walks the call graph from `main` asking the same resolver at
each site — one mechanism, many clients; the traits rounds do not drag the
compiler in. And `Compile` itself certifies function → IR simulation; the
IR is architecture-agnostic by construction, so arch belongs to the later
IR→native stage (`datarepr-separation`), under whatever class that stage
wants — with one more ordinary parameter, per §2. The Compile sketch's §5
bullets (resolution-from-main, `[Cpu]` indexing, `let instance`, `.code`
keying) are all subsumed by this design.

## 11. Deliberately rejected

- **`instance C for T` syntax** — privileges one parameter; breaks at
  multi-parameter classes (§3).
- **Class-level target indexing as machinery** — dissolves into ordinary
  parameters (§2).
- **Instance priorities / declaration-order tie-breaking** — replaced by
  declaration-time overlap checking with agreement-proof escapes (§6.2).
- **Cross-stage persistence** for types-in-code — breaks intensional
  analysis (§10).
- **Nested (non-flattened) parent representation** — reintroduces
  projection-path defeq obligations that flattening discharges for free
  (§4).
- **Resolution as a primitive the language semantics depends on** — it is
  policy over first-class record values, forever (§1, the layering rule).

## 12. Open questions

- **Where structural-decrease termination bites** legitimate mathematics,
  and whether the named-instance escape suffices there (§6.3 — held as
  default, not doctrine).
- **Post-hoc registration**: can an ordinary global be marked as an
  instance (attribute-style), or is the `instance` declaration the only
  registrar? (§5.)
- **Mode-annotation surface syntax** for input/output class parameters
  (§6.2).
- **Canonical-table scope**: per-module vs global; interaction with
  separate checking and the certified cache (`parallel-checking-and-caching`).
- **Agreement-proof form** for overrides conversion can't reach:
  where does the propositional-equality obligation live in the record?
  (§4.)
- **Both instance forms** (block and literal) are kept — two spellings of
  one thing has cost; revisit if one atrophies.
- `CallCtx` descriptor shape stays owned by
  `docs/archive/compile-typeclass-design.md` §8.

Added at the closing pass (2026-08-07), scope items more than questions:

- **Method dispatch through instances.** `x.op(y)` at a *concrete* carrier
  nearly falls out — block members are real globals under `Rat.Monoid.op`,
  reachable by the existing receiver machinery through the type-owned
  namespace. The case that matters is generic: inside
  `fn f<A>(m: Monoid<A>, x: A)`, `x.op(y)` finding `m.op` means receiver
  sugar consults in-scope *dictionaries*, not only namespaces. Most of the
  ergonomic payoff lives here; explicitly in layer 1/2 scope.
- **Operators migrate onto classes.** `+`/`==` are currently
  surface-operators machinery bound to fixed functions — the "elaborator
  machinery wearing a syntax" pattern. `Add<A>`/`Eq<A>` are their natural
  home: operator overloading for free, one resolution story. Recorded as
  direction so the two mechanisms don't drift; migration is its own round.
- **Content-addressed minting.** The canonical derived global's *name* is
  derived from the (class, carrier-syntax) key, so minting is idempotent
  and elaboration-order-independent — whoever mints first produces the
  identical definition. This largely dissolves the canonical-table
  interaction with parallel checking above.
- **Agreement-proof cost.** Declaration-time convertibility is a kernel
  workload in the memory-superlinear regime; the propositional-equality
  fallback is the cost escape as well as the expressiveness one.

## 13. Staging

Not one round. The natural sequence, each with its own design-doc slice
checked against this record: (a) layer 1 — `class`/`instance` declaration
forms over records, block namespaces, `extends` with the canonical-value
discipline; (b) layer 2 — the resolver with its four disciplines and the
`:= infer` mechanism, native, against the quoted-goal contract;
(c) trace-as-data diagnostics riding (b); (d) layer 3 with the meta-layer
roadmap, when context computation lands. Bundled records need no
scheduling — already landed.

Layer 1 landed 2026-08-07; its specification slice is
`docs/language/classes/traits-layer1-design.md`, whose §7 records what implementing corrected
(the canonical name is keyed on the carrier *head* rather than the whole
carrier syntax, and `extends` at a non-parameter argument is refused) and
whose §8 lists what it hands to layer 2.

Layer 1's acceptance corpus, named now: the prelude types
(Option/Result/List) for ordinary classes; a small
`AddMonoid → AddCommGroup` hierarchy as the `extends`/canonical-value/
override-agreement test; and `lib/certgen/ir_v1.hthr`'s `Compile` instances as the
pre-existing client that must not break. The operator migration (§12) gets
its own round after layer 2 exists to resolve for it.
