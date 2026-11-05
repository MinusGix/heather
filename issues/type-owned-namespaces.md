---
title: "Type-owned namespaces: names attach to subjects, reachability through evidence"
status: open
labels: [frontend, syntax, elaboration, design, modules]
area: language
created: 2026-08-05
updated: 2026-10-26
---

Direction issue, not scheduled — filed from the 2026-08-05 namespace
discussion (the round after [[modules]] v1 landed), so the design is
written down rather than re-derived. The prompt: `cong_nat` should be
`nat::cong` — a name wearing its namespace as a suffix — and a prover
needs mass accessibility that Rust-style selective import does not give,
while typeclasses "capture a good chunk but not wholly."

The standard library now supplies a concrete readability test. Its branching
algebra probe exposes `TreeAlg`, `TreeElim`, `tree_fold`, and
`TreePassLaws`; the intended organized surface is `Tree::Alg`, `Tree::Elim`,
`Tree::fold`, and `Tree::PassLaws`. This is not merely shorter spelling: it
lets a user discover the theory from `Tree` while keeping the ambient module
namespace from becoming a catalogue of prefixed names. [[tree-library-public-shape]]
owns which declarations form that public theory; this issue owns how those
attachments are declared and resolved.

## The claim

The natural namespace is the **subject** — a type (`Nat`, `Le`,
`Option`) or a structure (`Monoid`) — not the file. Files are storage;
subjects are what names organize around. Proposal, in two coupled halves:

1. **Type-owned namespaces, checked.** A declaration form attaches
   theorems/fns to a type: `Le::refl`, `Nat::cong`, `Option::map`. The
   `Type::member` grammar exists since [[modules]] (constructors qualify
   by type); this opens membership beyond constructors and fields, and
   the attachment is a checked declaration, not a Lean-style naming
   convention.
2. **Reachability through evidence.** A member of `T`'s namespace is in
   scope wherever a `T` is in evidence, by the one-resolution-judgment
   direction (docs/modules-design.md §8):
   - *Elimination-shaped* members reach through a **receiver** —
     `p.trans(q)` with `p : a = b`; the method fallback is already
     receiver-directed, so this is Lean dot-notation landing on built
     machinery.
   - *Introduction-shaped* members reach through the **expected type** —
     bare `refl` at goal `Le(n, n)` resolves to `Le::refl`. This
     subsumes [[ctor-resolution-by-expected-type]] (constructors are the
     special case).
   The duality is bidirectionality itself: synthesis position, the
   arguments are the evidence; checking position, the goal is.

   Extension for function-subject lemmas (`add_comm` is "about" `add`):
   the goal's **head symbol may pick the namespace** (coarse, stable);
   full unification picking the *lemma* stays banned, per the growth
   invariant.

Consequence for the collision problem: the ambient bare namespace
shrinks to genuinely ambient names; subject-owned lemmas are reached
through evidence at zero import cost and zero pollution, which is the
accessibility profile proof text actually needs.

## Where typeclasses sit

A structure is a record type, so its theory is its own type-owned
namespace (`Monoid::assoc`). Instance resolution adds a second
**evidence relation**: nominal membership is "this value *is* a `T`";
class membership is "this type *has* a `T`-instance." Same judgment, two
relations — one definitional, one semantic. Typeclasses are the semantic
half, capturing exactly the lemmas stable under transport along
instances; Nat-specific facts (computation lemmas, inversions, induction
schemes) are the nominal half's. Neither subsumes the other, and the
"these assumptions only" boundary role is the little-theories reading:
structure = theory, instance = interpretation, reachability-through-
instance = transport.

## The Better-than-Lean line (why not just copy)

Lean has the same ingredients (namespaces, dot-notation, `open`,
classes) and loses where our invariants hold:

- Lean disambiguates overloads **by elaboration success** — try every
  interpretation, keep what typechecks. That is what the growth
  invariant forbids: growth elsewhere can reinterpret existing text.
  Here, evidence may *shrink* the candidate set, never race candidates;
  residual ambiguity errors with origins named.
- `open` is precedence-ordered pollution; the base layer here stays
  [[modules]]' ambiguity-at-use, and evidence-reachability removes most
  of the need for mass-open.
- Namespaces are checked attachments, so `Le::refl` cannot drift from
  `Le`.

## Honest gaps

- **Forward reasoning** (`let h = sub_zero(n);`) has no evidence in
  hand; those sites keep the v1 regime (bare-if-unambiguous, qualify
  otherwise). The design is strictly additive over [[modules]].
- Rewrite-direction / normal-form tension between `Nat::add` facts and a
  future `Monoid::op` statement of "the same" fact is a tactic-layer
  problem no naming scheme solves.
- `nat::cong` is spellable today by renaming `cong_nat` → `cong` inside
  the module; deliberately not done — if this issue lands, its name is
  `Nat::cong`, and one rename beats two.

## What it assumes from elsewhere

- **[[modules]]** (closed) owns the base regime and the two invariants.
  Assumed here: ambiguity-at-use stays the floor; `Type::member`
  qualification stays.
- **[[ctor-resolution-by-expected-type]]** owned the constructor special
  case and **landed first** (closed 2026-08-16), so the absorption runs the
  other way: `Elaborator::ctor_here_expected` is the shape to generalize,
  and the two guards it had to grow are the ones the general case inherits
  — the route is a *fallback* after the ordinary reading, and it stands
  down entirely when any visible declaration of the name is not a member of
  the expected type's namespace. The second is the load-bearing one: a
  bare name that a plain `fn` also declares is not settled by the goal,
  because a function of the right result type is equally admissible there.
- **[[compile-typeclass-design]]** owns instances. Assumed here: only
  that instance resolution exists someday; the second evidence relation
  waits for it.

## When

A scheme round wants: the attachment syntax (impl-block vs qualified
declaration head), the evidence judgment written against the elaborator's
actual checking/synthesis split, and the method-fallback unification.
Triggered by the first library round that hurts without it — plausibly
the prelude layer-2 round or the first file that wants two order kits.

## Log

- 2026-08-20: Added `Tree::Alg` / `Tree::Elim` / `Tree::fold` as the first
  whole-module acceptance pressure. The Tree cleanup itself is separately
  owned; flat `TreeAlg` names should not become the permanent workaround for a
  missing subject namespace.

- 2026-08-05: Receiver half scheduled as [[type-owned-members-receiver-slice]] (2026-08-05 ergonomics round); expected-type resolution and head-symbol picking stay here.
- 2026-08-05: Receiver slice landed ([[type-owned-members-receiver-slice]], 2026-08-05). Three findings for this issue's next slice: (1) Le::refl is not spellable — a fn … -> Type predicate owns no namespace, so every decided predicate is outside the design as landed; (2) the member-ambiguity diagnostic suggests import a::{List::nth}; which does not parse — what a member's standing disambiguation looks like is this issue's call; (3) the exercise file's still-hurts list ranks expected-type (introduction-shaped) resolution as its #4 tax: four lemmas with no ambient home.
- 2026-08-17: First real customer of the prediction [[list-algorithms-exercise]] made on 2026-08-05 ("map is declared bare in both list and option, so it is already ambiguous at use for any file importing both"). Wave L2' hit it (2026-08-17, [[std-list-l2-prime-laws]]): in a module importing list AND option, map(zip(xs, ys), λ q => swap(q)) resolves to NEITHER declaration — it reaches the prelude's vector map and reports `map's receiver has to be a vector`, which names a third thing the author never mentioned. list::map is the workaround now in crates/elab/tests/lib_std_list.rs. Two facts for the fix's design: the failure is silent-then-confusing rather than an ambiguity error, and it happened in a TEST probe rather than in lib/, because lib/std/data/list.hthr does not import option.
- 2026-09-18: A second concrete readability test, beside the `Tree` probe this issue already
  cites: `docs/showcase/calc_text.hthr` ([[sequence-parser-source]]) was read as a
  language-quality target on 2026-09-18 and the first complaint was freestanding
  `tier(d)`, `meaning(d)`, `spell(d, tail)`, `WellFormed(d)` — a derivation's
  whole theory spelled as ambient functions. Nobody calls `tier` by itself; the
  intended surface is `Derivation::tier`, `Derivation::meaning`,
  `Derivation::spell`, `Derivation::WellFormed`.

  What the probe settled (`probes/str/p11.hthr`): the **receiver half of this
  issue already works** for a user-declared inductive. `fn Derivation::tier(self
  d: Derivation) → Nat` declares, and `Sum(…).tier() = 0` holds by `refl`. So the
  gap the showcase actually hit is not the mechanism but the habit — the standard
  library and the showcases keep writing ambient names because that is what the
  pre-`modules` code did, and new code copies it.

  Two consequences worth recording:

  - Elimination-shaped members are available *today*, so the readability half of
    this issue can be paid down incrementally in existing files rather than
    waiting on the introduction-shaped half (bare `refl` at goal `Le(n, n)`).
    Non-receiver members of a type's namespace — `Derivation::WellFormed(d)`,
    where `d` is an argument and not a subject — are the part still missing.
  - The pattern that forces ambient names is sometimes not habit but
    [[member-shadows-receiver-member]]: `string.hthr` writes `string_len` beside
    `String::len` precisely because the member being declared would make the bare
    name ambiguous. Any cleanup pass over the library will meet that first.
- 2026-09-18: The missing non-receiver reach now has a diagnostic and a cost. A type-owned
  member cannot be named at all except through a receiver: inside
  `fn Tree::flat_d(self t: Tree, …)`, the qualified self-call `Tree::flat_d(l, …)`
  is refused with "`Tree::flat_d` is qualified by `Tree`, which is neither an
  imported module nor a type in scope here" (`probes/str/p13.hthr`).

  So the two halves of this issue are not independent after all. Because there is
  no qualified spelling, every use of a member goes through the receiver path, and
  any analysis that does not understand receivers becomes a hard block rather than
  a style tax — which is exactly what [[receiver-member-ih-generalization]] is: a
  structurally recursive member that varies a non-decreasing parameter has no
  spelling that checks.

  Concretely, in `docs/showcase/calc_text.hthr` the derivation's theory converts
  to members except `spell`, the difference-list spelling, which must stay
  freestanding among members that are not. Worth weighing when this issue is
  scheduled: a qualified form (`Type::member(args)`) may be the cheaper half to
  land first, since it gives every existing analysis a spelling it already
  understands.
- 2026-09-22: The 2026-09-22 std namespacing refactor moved `nat`'s `add` to `Nat::add`; certgen still identifies functions by surface name, filed as [[certgen-namespaced-function-identity]].
- 2026-09-23: 2026-09-23: the refactor's fallout on master is fixed and the full suite is green (2904 passed). The fixes were fmt drift, lib_algebra and operators_onto_classes test respellings, and certgen now keys functions on global identity (certgen-namespaced-function-identity, closed).
- 2026-09-24: 2026-09-24: Namespace round (#1a) chartered from the refactor's residue. Probe of the 80 remaining lib `@` sites (all BitVec) found [[receiver-with-unsolved-implicit-unbound]]: member lookup refuses any receiver whose type carries a meta (`R::mk().get()`, `Nil.len()`), with a false "declared below" hint. It joins the facade re-export of members, `x.f()` vs a bare `f` in scope, [[type-member-missing-self-diagnostic]] and [[receiver-member-ih-generalization]].
- 2026-09-24: 2026-09-24: #1a design: docs/receiver-member-resolution-design.md. It covers owner-by-head for uninferable receivers, dropping ambient readings that cannot take the receiver (a non-function local like `let len = …`, or a disjoint subject carrier), the declared-below and missing-self diagnostics, and the lib `@` sweep. The facade re-export of members already works (`Cursor::start` through `import parser`).
- 2026-09-24: 2026-09-24: #1a landed (docs/receiver-member-resolution-design.md §7): an uninferable receiver names its owner by its head; ambient readings that cannot take the receiver no longer block the member; the declared-below and missing-self diagnostics are fixed; lib `@` lines went 90 → 42; calc_text's `spell` is a member. Residue: [[nested-uninferable-argument-under-checking]] (chains headed by an uninferable call) and [[method-chain-receiver-reinference]] (2^depth).
- 2026-10-26: The non-receiver reach inside an owner is filed as [[owner-sibling-names]] (docs/sections-design.md §6): inside a member of `T`, `T`'s members are bare-name candidates at ambiguity rank, no precedence. The library writes `Owner::x` inside `Owner`'s own members 3,409 times. Owner blocks were weighed and not recommended (doc §5.4): owners stay on heads for grep.
- 2026-10-26: 2026-10-26: inside a member of T, T's other members are now reachable bare at ambiguity rank (issues/owner-sibling-names.md, docs/sections-design.md §6) — the elimination half of this issue in non-receiver positions.
- 2026-11-05: gardener: cites a file it shares with [[requires-placement-syntax]] (`docs/sections-design.md`).
