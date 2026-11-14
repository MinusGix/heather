# Delayed theorems: a theorem made when a proof first names it

Status: proposal, 2026-11-14. Nothing here is built. Tracking issue:
[definition-branch-equations](../issues/definition-branch-equations.md)
(its "Open" list). Minus asked for this after #643: "delayed theorem
creation is a potentially valuable tool but needs thought".

## 1. Why

Since #631 and #643 every `fn` whose body is a test or a `match` on a
parameter gets its branch equations (`f::True`, `f::Succ::True`, …)
elaborated and gated right after it. On the library that is about 1400
functions and 4300 theorems, and a whole-library sweep is a few percent
slower. Almost none of those theorems are cited: the SHA-256 stream proof
names five. The cost is paid for every function so that the few a proof
names are there.

The same shape recurs. A `decreases` function's `f_unfold`, `f::ext` and
`f::irrel` are eager (`docs/decreases-unfolding-design.md` §7), as are an
interface definition's equations. Each is a theorem that is *derivable* from
something already checked, cheap to state, and rarely cited. A theorem made
on first citation removes the cost and keeps the names.

## 2. What a delayed theorem is

A **pending theorem** is a name with a recipe, recorded where the theorem
would have been elaborated:

- the **designed name** (`f::Succ`) and the minted one (`f#Succ`);
- the **recipe**: the surface `Decl` the generator built (statement and
  proof). It is pure syntax, so it costs a walk of `f`'s body and nothing
  else;
- the **scope** it was generated in. The recipe's names mean what they
  meant in `f`'s module, as an inductive's stored field types do
  (`Inductive::scope`), and it is elaborated under
  `Elaborator::with_module_scope`;
- the **readings** still open. A `Bool` condition is tried as a
  proposition first and as a `Bool` second (`branch_equations::Reading`).
  That choice is made by elaborating, so it moves to materialization too.

A pending theorem has no kernel term, is never in Ψ, and is never gated
until it is **materialized**: elaborated, gated and committed like any
generated declaration, at the first reference.

## 3. Materializing at the first reference

Name resolution is where a reference meets a pending name: `resolve_name`
already consults `unfold_refusals` for a generated name that is missing
(`crates/elab/src/lib.rs`), and a pending name is one more case there. The
question is *when* to elaborate it, since the reference is in the middle
of another declaration's attempt (goal arena, metas, a rollback
checkpoint).

Three routes, from simplest to most general:

1. **Pre-scan.** Before a declaration is elaborated, walk its surface for
   `Var` names that are pending, and materialize them first, at the item
   boundary. A direct citation (`Sha256::push::True(…)`, `simp_only(f::Succ)`)
   is a written name, so this covers every reference in the library today,
   with no change to the attempt machinery. The walk is cheap next to
   elaboration.
2. **Restart.** A name that only appears during elaboration (a tactic's
   generated source, `name_of`, a `simp` set registered elsewhere) records
   a request and fails the attempt, and the item loop materializes it and
   elaborates the declaration again. `elab_decl_one` already restarts a
   declaration from its source when the goal arena asks for a bigger base,
   so this follows a pattern the code already has.
3. **Inline, then mint.** Elaborate the recipe as a closed term in place
   (`{ let e: Π… = λ… => proof; e }`) and queue the mint for after the
   declaration, as `Resolution::mint_pending` does for derived instances
   ("the first use site of a derivation inlines it and every later one
   references the mint"). This is the most general route, but it pays the
   elaboration twice and copies the term into the first citer.

Proposal: build 1 now and 2 behind it, so a missed name costs one restart
and never a wrong answer. Route 3 would only be worth it if restarts turn
out to be common.

## 4. Who owns a materialized theorem

This is the hard part. `f` is in module A, the citation is in module B,
and A's image is sealed: it was written before B was elaborated, and other
modules replay it unchanged.

- **In A, retroactively.** Rewriting A's image breaks the build DAG and
  early cutoff (`docs/module-interface-cutoff-design.md`). Rejected.
- **In B, under A's name.** B's image carries the theorem `A::f#Succ`. If
  modules B and C both cite it, a module D importing both meets two
  declarations with one name. They are the same theorem by construction:
  the same recipe from the same image, elaborated by the same compiler.
  Import can treat them as one if a pending theorem's identity is a key,
  (A's interface hash, designed name). The second import then aliases the
  first instead of declaring again. That needs the importer to merge, which
  it does not do for any declaration today.
- **In B, under B's own minted name.** No merge is needed, but `f::Succ`
  in D resolves to two names and the alias must pick one. Both are the same
  statement, so picking either is sound, but two names for one theorem
  spread through images and displays.

Proposal: the second option, with the key. A materialized theorem is an
*instance* of the pending one, and the import-time rule is "one instance
per key", the coherence a derived instance's canonical table already
gives. Within one module the first materialization is the only one.

## 5. What the image and the cutoff see

- A's image gains one event per pending theorem: the recipe, its scope
  module and its readings. Surface `Expr`, `Ty` and `Stmt` already have an
  image encoding (`put_expr`, `put_stmt`, used for inductive defaults and
  value parameters), so this is a new event kind and a format bump.
- A's **interface** includes its pending names. A client can cite them, so
  a change to `f`'s body changes A's interface, as it already does through
  `f`'s own term.
- B's image records each materialized theorem as an ordinary declaration,
  plus its key. Replaying B replays it without the recipe.
- **The gate** sees a materialized theorem when it is made, in B, like any
  generated declaration. A pending theorem is never trusted: until it is
  cited it is not a theorem at all, only a name that may become one.
- **A refusal** is found at materialization, in B, and reported at the
  citation. The message is the same as now ("no branch equation `f::Succ`
  …: the generated … was refused (…)"), but the error is shown in B.

## 6. What changes for a writer

Nothing a proof says changes: `f::Succ(…)` is cited as today. What changes
is when a broken recipe is noticed. Today an equation the checker refuses
is recorded quietly when `f` is elaborated. With delayed theorems it is
noticed when a proof first cites it. A `heather check --materialize-all`
(or a test lane that cites every pending name) would keep the generators
honest, the way the library gate does now by building them all.

## 7. Beyond generated equations

A pending theorem is a producer that runs on demand, as a fact's producers
do in `docs/facts-on-demand-design.md`. That is the shape of Minus's
"request a proof from a function" for the optimizer, with a name as the
request. Candidates after the branch equations:

- `f_unfold`, `f::ext`, `f::irrel`, `f::step`, `f::done` for `decreases`
  functions (eager today; they have the same rarely-cited shape);
- an interface definition's equations;
- record η and projection lemmas, if [record-eta] lands as lemmas.

A **user-written** delayed theorem (`delayed theorem t … { proof }`, checked
when cited) is a different thing: it changes what "this module checks"
means, since an uncited theorem's proof would never be checked. It is not
proposed here. If it is wanted, it is a language and trust-base decision
for Minus.

## 8. Rejected: the equation computed from the kernel term

The equations could also be made at the citation from `f`'s **kernel**
definition, unfolding it and reading the eliminator at its head, with
nothing stored. That needs a reading of every match encoding (sums, `Wf`,
`IWf`, the tiers) back into "which arm, under which condition". It
duplicates the pattern compiler in reverse, and the condition as the
source wrote it (`fill = 63`, not a bit) is lost. The surface recipe keeps
both for free.

## 9. Plan

1. Pending theorems in one module: the record, pre-scan and
   materialization, the restart fallback, and the branch equations moved
   onto it. No image change, because a pending theorem that crosses a
   module boundary is still materialized eagerly at the end of A's pass.
   This is enough to measure the in-module saving and to test the
   restart.
2. Across modules: the image event, the key, and import-time merging. This
   is a format bump, so it goes to Minus.
3. Move the `decreases` companions onto it, and add a materialize-all lane.

Open questions for Minus:

- **Ownership.** Is "B owns an instance of A's theorem, merged by key on
  import" acceptable, or should materialized theorems live in a shared
  side store keyed by A's image, outside the module DAG?
- **Checking.** Is a recipe that is never cited and never checked
  acceptable for generated equations, given that a materialize-all lane
  checks them?
- **Scope.** Should user-written delayed theorems be considered at all?
