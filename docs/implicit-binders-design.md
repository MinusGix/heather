# Implicit binders in function types and lambdas: the skeleton design

Design for the round picking up `issues/implicit-binders-in-function-types.md`.
Round pattern as usual: this document first, the implementing round against
§10's acceptance list. House model: `docs/unifier-completeness-design.md`.

**The framing decision is already made and is binding** (the issue's
2026-08-06 log entry): implicitness is a property of the *surface* type,
erased at the kernel boundary. The elaborator carries a positional
**implicitness skeleton** beside the kernel type — the issue's option 1 —
with the full mirrored type language (option 2) as the named fallback if the
skeleton keeps getting lost. **No kernel change of any kind**: `Type::Pi`
keeps `dom_level`/`cod_level`/`dom`/`cod` and no flag, conversion and the
52-branch walkers are untouched, and nothing here taxes the Coq
formalization. The accepted degradation, stated up front and pinned by test
(§9): a function type that arrives by **computation** — out of an eliminator,
through a decoded code, off a `whnf` — carries no skeleton and offers no
implicit insertion. It degrades to today's explicit spelling, never to
wrongness.

Everything below is `crates/syntax` (grammar) and `crates/elab/src/lib.rs`
(one new data type, a handful of threaded parameters). The round builds
directly on the unifier-completeness machinery that landed 2026-08-06
(`apply_implicit`'s `param_offset`/`bare_ref` honesty, the `Sol` model,
per-argument deferral, `is_checking_only`, `bare_implicit_prefix`,
`solve_from_expected`) — §5 says exactly which pieces transfer unchanged and
which need a named generalization.

---

## 1. Empirical pre-work

Probes live in the session scratchpad (`probe_poly.hthr` … `probe7.hthr`),
each run capped per the house rule
(`ulimit -v 8388608 -t 120; target/release/heather check …`). One incident
worth recording: the first probe pass ran against a **stale binary** (built
10:10, before the unifier round's 11:09 commit) and reported inverted results
for two probes; everything below is from a fresh build.

### 1.1 Expressibility: `{A: Type} -> …` is writable this round

The issue's sequencing note ("not urgent while the surface has no universe")
is **obsolete**, exactly as the decision log suspected. `docs/surface-universe.md`
landed 2026-07-27: `TyKind::Univ` exists (`crates/syntax/src/ast.rs:275`),
and — the part that had to be verified — `elab_ty`'s `Fn` arm **registers a
universe-typed binder as a tyvar for its codomain**
(`crates/elab/src/lib.rs:1604`), so a function type can genuinely quantify
over a type. Confirmed live:

- `fn appnat(f: (A: Type<0>) -> A -> A, n: Nat) -> Nat { f(Nat, n) }`
  elaborates and kernel-checks, applied to both a polymorphic `fn` value and
  a written `fun (A: Type<0>) (x: A) => x` (probes 1–2).
- The spelling is pervasive in the suite already
  (`crates/elab/tests/template_registration.rs`, `in_language_map.rs`, …).

**So the high-value case is in scope: `{A: Type<0>} -> A -> A` is this
round's headline, not a smuggled dependent-function-type extension.** Value
implicits (`{n: Nat} -> …`) ride the same machinery. No scope question
remains here for the coordinator.

### 1.2 Where function-typed values enter with elaborator-built types

The inventory the skeleton has to cover — each site elaborates a *surface*
type itself and can decorate at the source:

| Entry point | Where the type is built | Where a skeleton can live |
|---|---|---|
| declaration parameters | telescope loop, `elab_decl_inner` (lib.rs:989) → `cx.push` | a `Cx` entry, parallel to `names`/`gamma` |
| binders inside a written type | `elab_ty`'s `Fn` arm pushes its own binder for the codomain (lib.rs:1594) | the same `Cx` slot, set by the `Fn` arm itself |
| `let` aliases | `elab_stmts` (lib.rs:1507): annotation via `elab_ty`, or inferred from the RHS | a new field on `Alias` |
| record/inductive fields | stored as **surface** `Ty` (`inductive.rs:147`), re-lowered per use; projection reads the kernel Σ (`project_field`, `inductive.rs:1714`) | derived on demand from the stored surface `Ty`, positionally — no new storage |
| lambda binders | `elab_lam_check` reads the expected Π; `elab_lam_infer` reads annotations (lib.rs:4311, 4375) | from the expected skeleton / from the written marks |
| meta-layer signatures | `elab_meta_decl`, `Code(g \|- T)` | **out of scope** — marks refused (§8) |

Function-typed record fields work today (probes 3–4, including
`f: (A: Type<0>) -> A -> A`), and so does a Π field on a plain inductive
(probe 7) — the motivating `Compile`-instance shape is live.

### 1.3 A regression found in passing: flag for the coordinator

Probe 5 — a bare polymorphic global passed where the expected type is the
**full explicit polymorphic Π**:

```heather
fn myid<A>(x: A) -> A { x }
fn appnat(f: (A: Type<0>) -> A -> A, n: Nat) -> Nat { f(Nat, n) }
theorem t(): appnat(myid, 3) = 3 { refl }   -- kernel LevelMismatch today
```

This **passed before the unifier round and fails after it** (verified against
the pre-round binary): the new §5.3 bare-reference route unconditionally
mints `?A` in checking position, the harvest mis-teaches against the
expected `Π (A : Ty 0). …` (the right answer was *no insertion at all* — the
parameter wants the polymorphic value verbatim), and the junk instantiation
dies in the kernel. No test pinned the shape, so it went unnoticed.

This design fixes the shape **where the expected type carries a skeleton**
(§5.3's suppression rule) — which after this round is every written
parameter.

**Resolved before implementation (2026-08-06):** the regression — including
the residual explicit-spelled case — was hotfixed the same day (commit
`414531f`): the bare-reference route now suppresses insertion whenever the
whnf'd expected type is a Π with a *universe* domain, pinned by
`polymorphism.rs::a_bare_reference_at_a_polymorphic_expected_type_is_not_instantiated`.
The record is the 2026-08-06 log entry in
`issues/elab-unifier-completeness.md`; no separate issue exists or is
needed. The two rules compose (§5.3): where an expected skeleton exists it
is consulted first, and the erased-type universe check remains as the
fallback for skeleton-less expected types — it already covers TYPE-implicit
heads in both spellings (they erase identically); the skeleton rule is what
adds coverage for VALUE-implicit heads (`{n: Nat} -> …`, whose erased
domain is not a universe).

---

## 2. The skeleton representation

### 2.1 Decision: a nested, sparse `Skel`

```rust
/// The implicitness skeleton of a surface-written function type
/// (issues/implicit-binders-in-function-types.md, option 1). Positional:
/// entry `i` speaks for the `i`-th Π along the type's spine. Contains no
/// terms, no de Bruijn indices, and no name that resolves — binder names
/// are carried only as goal-name hints and diagnostic labels.
struct Skel {
    params: Vec<SkelBinder>,
}

struct SkelBinder {
    /// The written binder name, for goal-name hints and the §7 messages.
    name: Option<String>,
    implicit: bool,
    /// The surface domain was `Type<n>` — selects the "type argument"
    /// message flavor, exactly as `ParamMeta.is_type` does for globals.
    is_type: bool,
    /// The domain's own skeleton, when the domain is itself a function
    /// type carrying implicits — a lemma-shaped callback's implicits.
    dom: Option<Rc<Skel>>,
}
```

Derivation is one purely syntactic function, `skel_of_ty(&Ty) -> Option<Skel>`,
walking `TyKind::Fn` chains. Sparse by rule: it returns `None` unless an
implicit mark occurs somewhere in the type (including nested `dom`s).

*Amended 2026-08-20*: named arguments made a written binder name operational
surface data, so a skeleton is also retained whenever a binder has a name.
An anonymous `T -> U` remains skeleton-less and positional. The cost of the
wider allocation rule is measured by `scripts/bench --check`; the kernel type
and every implicit-insertion rule remain unchanged.

**What nests and what deliberately flattens.** The codomain chain flattens:
`Nat -> {A: Type<0>} -> A -> A` is one spine, `params = [explicit, implicit,
explicit]` — Π is right-nested and positional along the spine, so partial
application is an offset, not a re-association. The **domain** nests: a
higher-order parameter `f: {A: Type<0>} -> A -> A` needs its own skeleton
both to check an implicit lambda against (§6) and to govern insertion at
`f`'s uses once bound — that is `SkelBinder::dom`. The final result type
past the last written arrow carries nothing: a skeleton describes Π
structure only.

**Prefix authority.** A skeleton speaks for the first `params.len()` Πs of
its type and no more. `whnf` can expose *further* Πs past the written spine
(an `OfExpr` codomain decoding to a function type); those are explicit, by
the degradation rule. A skeleton can never be longer than the real spine,
because each entry corresponds 1:1 to a surface `Fn` node that `elab_ty`
lowered to exactly one `Pi`.

### 2.2 Rejected alternatives

- **Flat `Vec<bool>` per spine.** The issue's minimal sketch. It cannot
  type a callback: checking `λ {A: Type<0>} (x: A) => x` against
  `twice(f: {A: Type<0>} -> A -> A, …)`'s domain needs the *domain's*
  skeleton at the lambda, and a per-spine mask has nowhere to put it. The
  motivating uses (a `Compile` instance taking a lemma-shaped callback) are
  exactly this shape, so the flat form fails the round's own acceptance
  list, not a hypothetical.
- **The full mirrored type language** (issue option 2). A second `Type` to
  keep in sync through substitution, whnf, and every constructor — the cost
  the codebase has avoided everywhere. It stays what the decision log made
  it: the *named fallback* if masks keep getting lost. §3.3 argues they do
  not get lost at any site this round touches.
- **Kernel `Pi` flag / Lean-style binderInfo in the term.** Rejected in the
  binding decision, recorded here for completeness: either forks the
  function space or threads inert data through conversion — a shared-notion
  edit taxing every Pi-touching lemma, the 52-branch walkers, and the
  in-progress Coq formalization, for data with no semantic content.

---

## 3. Where skeletons live and travel

### 3.1 The carriers

1. **Context entries.** `Cx` gains a vector parallel to `names` and
   `gamma.entries` — `skels: Vec<Option<Rc<Skel>>>` — maintained by `push`
   (defaulting `None`) with a variant for the sites that have one. Set by:
   - the declaration telescope loop (lib.rs:989): `skel_of_ty(&p.ty)`;
   - **`elab_ty`'s own `Fn` arm** (lib.rs:1594): the binder it pushes for
     the codomain gets the *domain's* skeleton. This one line is what makes
     insertion work inside any written dependent type — a theorem statement
     `(f: {A: Type<0>} -> A -> A) -> f(0) = 0` has `f`'s uses in the
     codomain inferring with no further plumbing;
   - `elab_lam_check` (lib.rs:4346): the pushed binder gets
     `SkelBinder::dom` from the expected skeleton (§6);
   - `elab_lam_infer` (lib.rs:4396): from the annotation's `skel_of_ty`.
2. **Aliases.** `Alias` (lib.rs:5433) gains `skel: Option<Rc<Skel>>`. Set
   from the `let` annotation when present; from the RHS lambda's written
   marks when the RHS is an implicit lambda (§6.4); from the stored surface
   field type when the alias is a record projection (`LetRecord`,
   lib.rs:1496) or a `match`-arm field binder (`elab_arm`'s alias pushes,
   `inductive.rs:1693`).
3. **Record/inductive fields.** No storage change: the declaration already
   keeps every field type in **surface** form (`Ctor::fields`,
   `inductive.rs:147`), and the braces are right there in it. The
   projection path derives the skeleton on demand — `DotResolution::Project`
   (lib.rs:558) gains a skeleton slot filled by `skel_of_ty` on
   `ind.ctors[0].fields[idx].1`, keyed positionally by the same `idx` the
   kernel Σ-walk uses.
4. **Declarations.** A declaration's own top-level implicits stay
   name-directed `ParamMeta.implicit`, exactly as today. *Amended at
   implementation (2026-08-06):* `ParamMeta` gains one field after all —
   `skel: Option<Rc<Skel>>`, the parameter's own **domain** skeleton,
   derived from the same surface `Ty` its kernel domain was lowered from
   (so the §3.3 pairing guard holds). Without it, §6.1's first caller class
   has nothing to supply for a *global* callee: checking
   `use(λ {A: Type<0>} (x: A) => x, 3)` needs the expected skeleton at the
   argument, and `use`'s parameter table is the only place it can live —
   the original "untouched" claim contradicted §6.1/§10-positive-2.
   `None` for every markless parameter, so existing declarations store
   nothing new. A skeleton in a declaration's **result type** still has no
   consumer this round and is refused rather than dropped (§3.4).

### 3.2 The substitution story (stated explicitly, per the decision entry)

A skeleton contains booleans and hint strings — no terms, no de Bruijn
indices, nothing that a `LocalSubst`, `GlobalSubst`, shift, or discharge
acts on. Those operations act on the kernel `Type` beside it, and they are
structure-preserving on `Pi` nodes: substitution cannot change the arity or
order of a type's outer Π spine. So the positional correspondence fixed when
the entry was bound cannot drift, and skeletons travel with the entry with
**no update operation at all** — there is deliberately nothing to keep in
sync. The one reduction that changes spine arity — `whnf` decoding a
codomain into further Πs — only *appends* past the skeleton's end, which the
prefix-authority rule (§2.1) already covers.

### 3.3 Why this dodges the stored-syntax staleness class — and where it would not

`issues/module-scope-of-stored-syntax.md`'s hazard is **name resolution at
the wrong scope**: stored surface syntax re-lowered at a use site resolves
against the importer's scope. A skeleton resolves nothing — deriving one
from a stored field type reads only the brace structure, which is fixed at
parse time and identical in every scope. The caching round can serialize a
skeleton without serializing an open name.

Where the hazard *would* re-enter, named so the implementing round can keep
it out: pairing a stored kernel `Type` with a skeleton derived from a
*different* surface node, or letting any future pass rewrite stored surface
syntax (a cache normalizer, a formatter) independently of a stored skeleton.
The design's guard is structural — a `(Type, Skel)` pair is never stored;
skeletons are either derived fresh from the same surface node the `Type`
came from, or travel on the same entry the `Type` travels on. Any future
change that breaks that sentence is the moment option 2 gets its hearing.

### 3.4 Positions that refuse the marks

An implicit mark whose skeleton has no consumer must not be silently erased
— accepted-and-ignored is this feature's version of stale metadata (the
writer believes call sites will infer; they will not). Refused with one
shared diagnostic ("implicit binders take effect in parameter types, `let`
annotations, field types, and lambdas; this position cannot use one — see
issues/implicit-binders-in-function-types.md"):

- a declaration's **result type** (`fn mk() -> {A: Type<0>} -> A -> A` —
  callers of `mk()` get a computed head with no skeleton; result-position
  skeletons on `GlobalInfo` are a coherent future extension, filed per §9);
- `D<…>` type arguments, `[T; n]` element types, valparam types, index
  types (the lowered instantiations store kernel types or re-lower in
  contexts with no skeleton slot);
- meta-layer signatures (`Code(g |- T)` — the slice is pure quotation).

Marks in a *domain* nested under any accepted position are consumed
automatically by `elab_ty`'s `Fn` arm (§3.1.1) and need no listing.
Mechanically this is one syntactic walker (`has_implicit_mark(&Ty)`) called
at the enumerated `elab_ty` entry points, mirroring how `count_holes`
already walks `Ty`.

---

## 4. Application of a skeletal value

### 4.1 Which heads carry a skeleton

At `ExprKind::App` dispatch (lib.rs:2206, 2217), a head offers a mask
exactly when it is:

- a `Var` naming a local with a `Cx` skeleton entry, or an alias with one
  (locals shadow globals in `resolve` order; the skeleton lookup follows the
  same precedence, so a local `f` never borrows a global `f`'s `ParamMeta`);
- a `Dot` projection whose `DotResolution::Project` carried one (§3.1.3).

Anything else — an application result, a `match`, a parenthesized compound —
has a computed type, no skeleton, and stays on today's `apply_explicit`
path. Note the corollary: **every skeletal head has a name** (a binder, an
alias, or a field), so diagnostics never need an anonymous form.

### 4.2 Generalizing `apply_implicit`: decision

`apply_implicit` (lib.rs:4688) is name-keyed in exactly two ways: `name` in
its message strings, and `self.params_of(name)` for goal-name hints and
per-slot diagnostics (lib.rs:4738, 4774, 4870, 4908, 4947). Decision: keep
`name: &str` as a **display string** (the local's or field's name — §4.1
guarantees one exists), and pass the parameter table in:

```rust
fn apply_implicit(&self, cx, name: &str, params: Rc<Vec<ParamMeta>>, …)
```

Global call sites pass `self.params_of(name)` as today; value call sites
synthesize the table from the skeleton — `SkelBinder{name, implicit,
is_type}` maps onto `ParamMeta{name: name.unwrap_or("#i"), implicit,
is_type, is_self: false}` — so goal-name hints, the deferral hint at retry,
and the per-slot discharge messages all work verbatim from skeleton binder
names. This is the same honesty move the unifier round made with
`param_offset`: stop *recovering* per-callee data inside the function, pass
it from the one caller that knows.

*Implementation note (2026-08-06):* `apply_explicit` got the same
treatment, for the same reason — it recovered `params_of(name)` internally,
which would let a skeleton-less local `f` borrow a same-named global's
hint table (the §10 shadowing pin). Both functions now take
`params: Rc<Vec<ParamMeta>>`; `apply_implicit` additionally takes
`value_head: bool` to select the §7.3 value message flavor.

**Rejected alternative: an `enum ParamSource { Global(name),
Skel(&Skel) }` consulted lazily inside.** Two lookup paths through the body
instead of one table at the boundary; every one of the five consultation
sites would branch. The synthesized table is small, built once per call, and
makes the body head-agnostic.

**Rejected alternative: `Option<&str>` for the name** (the `apply_explicit`
precedent). Dead generality — §4.1's corollary means the `None` case is
unreachable, and threading it would weaken every message for nothing.

### 4.3 What transfers from the unifier round unchanged

The scratch-world machinery never consults the callee's identity: the `n`
metas, `Sol`/`Withheld`, per-argument deferral and its fixpoint retry,
`solve_from_expected` (both the LGG trigger and the general harvest), the
flex-head guard, and the spill all operate on the head as a shifted `Term`
and the mask as positions. A skeletal value call gets D1-style deferred
holes (`f(?p)` with the hole's goal named from the skeleton) and D2-style
expected-type harvest for free.

Two places it does **not** transfer, each with a decided story:

- **`f<T, …>` on a value has no spelling** — `elab_ty_app` is global-keyed,
  and this round does not extend it (§9). Consequence for diagnostics: the
  §7-style messages for a value must offer only the escapes that exist,
  `@f(…)` and an annotated eta-expansion — never `f<…>`. New message
  variants, §7 below.
- **`bare_ref` naming**: the zero-argument route's messages (lib.rs:4912)
  read naturally with a value's name substituted; only the `write
  `{name}<…>`` escape line is swapped per the previous point.

`is_checking_only` (lib.rs:4642) gains the value analog of its bare-global
member: a bare `Var` whose local/alias skeleton has a leading implicit
prefix is checking-only, for the same reason the 2026-08-06 amendment
recorded — it *can* infer, but only at its uninstantiated Π, which against a
meta-bearing domain mis-teaches.

---

## 5. Insertion timing

### 5.1 Applied values: insert at application

`f(x)` with `f` skeletal and the mask non-trivial routes to
`apply_implicit` exactly as a named global does at lib.rs:2368 — same
saturation rule (no partial application mixed with insertion), same spill,
same expected-type gating. `param_offset` is `0` (a value has no consumed
type-argument prefix).

### 5.2 Bare values in checking position: the `bare_implicit_prefix` analog

A bare `f` with skeleton `{A: Type<0>} -> A -> A` met where `Nat -> Nat` is
expected takes the §5.3 route with an empty argument list: a twin of
`bare_implicit_prefix` (lib.rs:5071) reads the *leading implicit prefix* off
the local/alias skeleton, and the `Var` arm (lib.rs:2093) calls
`apply_implicit` with `args = []`, the prefix mask, `param_offset = 0`,
`bare_ref = true`. Inference position is unchanged: bare `f` with no
expected type resolves verbatim, today's behavior.

### 5.3 The suppression rule (the probe-5 lesson)

> Bare-reference insertion — for values *and* for globals — is **suppressed**
> when the expected type carries a skeleton whose own leading position is
> implicit. The value is passed verbatim: the parameter asked for the
> implicit function itself.

Without this, `twice(f: {A: Type<0>} -> A -> A, n: Nat)` fed a bare skeletal
`g` would mint `?A` against an expected type that wants the *uninstantiated*
function, mis-teach, and die in the kernel — the §1.3 regression replayed
one level up, in the feature's own core use case. With it, implicit-headed
expectations compose: passing a polymorphic value to a polymorphic-expecting
parameter is the identity it should be.

Mechanically: the expected skeleton must reach the `Var` arm. `elab_check_hinted`
grows an optional expected-skeleton parameter threaded exactly where a
caller has one (§6.1 lists the three sites); the `Var` arm consults it
before the prefix route. Skeleton-less expected types keep today's behavior
— including the §1.3 residual gap, which stays filed rather than half-fixed
here.

**Rejected alternative: attempt-first conversion** (try the verbatim value
against the expected type; insert only if conversion fails). It closes the
residual gap too, but it is elaboration-by-backtracking: outcome depends on
a kernel conversion check run speculatively mid-elaboration, a control-flow
pattern the codebase has deliberately avoided (the no-backtracking doctrine
the OTT strip design leans on), and it charges a conversion on every bare
polymorphic reference to buy a case the skeleton rule already covers
wherever this round's syntax is used.

---

## 6. Lambda checking and inference

### 6.1 Threading the expected skeleton

`elab_lam_check` (lib.rs:4311) gains `skel: Option<&Skel>`, supplied by the
three caller classes that have one, mirroring how the `hint` pair already
travels: argument checking inside `apply_explicit`/`apply_implicit` (the
callee parameter's `SkelBinder::dom`), an annotated `let` (the annotation's
`skel_of_ty`), and record-literal field checking (the stored field type's).
Everything else passes `None`.

### 6.2 The coherence rule: decision

Skeleton mismatch is **not** a kernel mismatch — the kernel types are
identical — so the rule is about honoring written intent:

- **An implicit-marked binder requires the expected position to be
  implicit.** Marked binder at an explicit or absent skeleton position is a
  diagnostic (§7), not an acceptance: silently accepting means the writer
  believes uses of the function will infer, and they will not — stale
  intent, the §3.4 hazard at the term level. The message names the
  degradation when the expected type is computed.
- **An explicit binder is accepted at any position, including implicit
  ones.** Insertion at *uses* is governed by the type's skeleton, not by the
  argument's spelling, so `λ (A: Type<0>) (x: A) => x` checked against
  `{A: Type<0>} -> A -> A` is harmless and useful — every pre-existing
  explicit lambda and function value can inhabit an implicit-skeletal
  position unchanged (probe 2's shape stays green).
- The binder pushed by `elab_lam_check` carries the expected position's
  `dom` sub-skeleton (§3.1), so a callback bound by the lambda inserts at
  its own uses.

**Rejected alternative: automatic implicit-lambda insertion / η-expansion**
(the Lean behavior — checking `λ x => e` against an implicit-headed Π
inserts an invisible binder). It manufactures binders the user did not
write, breaking the emitted-term ↔ source correspondence the goal listing
and the `on`-discharge world depend on, and nothing motivates it: the
explicit-binder-accepted rule above already lets every existing lambda check.

**Rejected alternative: ignore the marks in checked lambdas** (treat them as
documentation). Cheapest, but it makes the marks *sometimes* meaningful
(types) and sometimes not (lambdas) — the mixed regime is harder to state
than the rule above and silently absorbs the mismatch case that most
indicates a user misunderstanding.

### 6.3 Inference position

`elab_lam_infer` **refuses** implicit marks ("an implicit lambda binder
needs a checking position, or a `let` — its implicitness has nowhere to go
from here"), with one carve-out: the `let`-RHS caller (`elab_stmts`,
lib.rs:1513) uses a harvesting variant, so

```heather
let f = λ {A: Type<0>} (x: A) => x;
```

infers (all binders annotated, as inference already requires) and the alias
records the skeleton read off the written marks. Any other inference
position would infer the type and *drop* the skeleton — the silent-erasure
case §3.4 forbids. Same shape as the existing rule that unannotated binders
are checking-only: forms whose surface data the position cannot consume are
refused there by name.

---

## 7. Erasure, `@`, and diagnostics

### 7.1 `@` on a value clears the whole mask

Today `@` on a named global narrows the mask to type parameters
(lib.rs:2357) — value implicits become positional, `<…>` remains the knob
for type arguments. For a **value that knob does not exist** (§4.3), so
narrowing would leave *no* complete escape. Decision: `@f(…)` on a skeletal
head clears the mask entirely — every parameter positional, which the erased
kernel type supports directly (probe 2: `f(Nat, n)` type-checks). The
asymmetry with globals is argued from the missing spelling, and disappears
if a value `<…>` form ever lands (§9).

Plumbing is already there: `@f(…)` on a local parses today and reaches the
`App` arm with `explicit: true` (the grammar's `@`-demands-a-name rule and
the non-name-head rejection at lib.rs:2207 are untouched); the arm's mask
computation adds the skeleton case beside the `ParamMeta` case. A
projection escape is one alias away (`let g = w.f; @g(…)`) and `@w.f(…)`
stays out of the grammar this round.

### 7.2 Erasure

Nothing changes at the kernel boundary because nothing crosses it: the
emitted `Term::Lam`/`Type::Pi` are byte-identical to the explicit spelling's,
and the kernel re-checks the saturated term either way. There is no erasure
*pass* — the skeleton simply is not part of what gets emitted.

### 7.3 Messages (verbatim, elaborator-level)

1. Unsolvable implicit on a value (the discharge message, value flavor —
   type-argument variant shown):

   > cannot infer the type argument `A` of `f` here — no argument's type
   > mentions it; write the call fully explicitly (`@f(…)`) or eta-expand
   > with the argument written (`λ … => f(T, …)`)

2. Implicit binder against a skeleton-less expected type:

   > this binder is marked implicit, but the function type expected here
   > carries no implicitness — it was computed, not written, and a computed
   > type offers no implicit insertion
   > (issues/implicit-binders-in-function-types.md)

3. Implicit binder where the expected skeleton says explicit:

   > this binder is marked implicit, but the expected function type spells
   > this parameter explicit — the two must agree position by position

4. Implicit lambda in a non-`let` inference position, and the §3.4 shared
   refusal — texts in §3.4/§6.3.

---

## 8. Parser

### 8.1 Grammar

```
ty      ::= '{' ident ':' ty '}' '->' ty        -- NEW: implicit binder
          | '(' ident ':' ty ')' '->' ty
          | ty_atom '->' ty
          | ty_atom

binder  ::= ident | '(' ident ':' ty ')'
          | '{' ident (':' ty)? '}'             -- NEW: implicit lambda binder
```

One binder per brace group, mirroring the paren rule. Inside `{…}` the type
parses exactly as inside `(…: …)` (same comparison-rung treatment;
an equality domain is written `{p: (a = b)}`, the let-annotation precedent).
An *unannotated* `{x}` lambda binder is allowed — checking position supplies
the domain from the expected Π, as for `x` today. `TyKind::Fn` gains
`implicit: bool`; `LamBinder` gains `implicit: bool`; both are surface-only
`Debug`-derivable structs, no kernel formatting concern.

### 8.2 Ambiguity: verified claims, each a test

The two diagnostics this grammar replaces sit at `parser.rs:1052` ("implicit
binders are not supported in function types yet", 3-token lookahead
`{ Ident :`) and `parser.rs:1674` (the lambda-binder brace refusal) — both
confirmed present and firing today.

- **Type position has no other brace form**: record literals (`{ f: e }`)
  are expression syntax, blocks are expression syntax; `TyKind` has no brace
  production. The `{ Ident : ` lookahead the diagnostic already uses is
  taken over unchanged by the parse.
- **Positions where a brace follows a finished type** (fn/theorem body,
  match arms): a body's first token pair is never `Ident Colon` (statements
  open with `let`/keywords/expressions; no colon operator exists), an arm's
  is `Pat =>` or `Pat(`. So `fn f(g: Nat -> Nat) -> {A: Type<0>} -> A -> A`
  wants the §3.4 *elaborator* refusal (result position), but it **parses**
  unambiguously — and `docs/surface-function-types.md` §3.1's "known
  restriction" (a type may not begin with `{`) is lifted by the lookahead
  rather than worked around with parentheses. The residual case named
  there, `match t as x -> {p: Nat} -> T { … }`, parses greedily and
  correctly: the motive takes the implicit binder, the arms brace cannot
  match `{ Ident :`.
- **Lambda binder position**: between `λ`/`fun` and `=>` no other brace form
  exists; the current refusal arm becomes the parse.

Record-pattern `let { f: x } = e;` — statement syntax, never reached by
`ty()` — is unaffected; a pin keeps it so.

---

## 9. What this round does NOT do

Each with its pointer, per the house rule:

- **No kernel change.** `Type::Pi` unflagged, conversion untouched, no
  metatheory obligation, nothing for the Coq formalization to mirror. The
  binding decision's two rejected kernel routes are recorded in the issue
  log and §2.2.
- **No insertion for computed types** — the accepted degradation, pinned as
  documented behavior by §10's negative controls, permanent under option 1.
  Option 2 (the mirrored type language) remains the named fallback in
  `issues/implicit-binders-in-function-types.md` if a future round finds
  skeletons getting lost at sites this design claims they cannot.
- **No result-position skeletons** (`fn mk() -> {A: Type<0>} -> …` refused,
  §3.4): carrying one on `GlobalInfo` so `mk()(x)` inserts is coherent
  future work — file as a follow-on in the tracking issue when refusal
  first annoys someone.
- **No `f<T>` written instantiation for values** (§4.3): the escape is `@`
  and eta-expansion; a value-head `<…>` spelling would also dissolve §7.1's
  `@`-asymmetry. Same follow-on home.
- **No skeleton on goal statements**: an `on`-discharge lambda against a
  skeletal goal type degrades to explicit binders (a `Goal` stores a kernel
  `Type` only). Note in the tracking issue; the fix is one field on `Goal`
  if wanted.
- **The §1.3 residual gap is RESOLVED** (2026-08-06, ahead of this round):
  hotfixed by commit `414531f`'s universe-domain suppression in the
  bare-reference route — see §1.3 and the 2026-08-06 log entry in
  `issues/elab-unifier-completeness.md`. No separate issue was filed.
- **Meta layer**: marks refused in `meta fn` signatures and `Code` payloads
  (§3.4); the quotation slice keeps zero implicit machinery
  (docs/in-language-map-design.md §5).

---

## 10. Test plan

Per `docs/testing-generated-terms.md`'s axes — literal *and* neutral
callee, an open element type, checking *and* computation position, negative
controls. New suite `crates/elab/tests/implicit_fn_binders.rs`; touches to
`function_types.rs` (retire the two §8 refusal pins, replacing not deleting)
and `parser` tests (the two diagnostics become parses). Every positive test
elaborates and is re-checked by the real kernel.

**Positives:**

1. *Neutral head, value implicit and type implicit*:
   `fn use(f: {A: Type<0>} -> A -> A, n: Nat) -> Nat { f(n) }` — insertion
   solves `A := Nat` off the argument; and the `{n: Nat}`-valued analog.
2. *Literal head, computation position*:
   `use(λ {A: Type<0>} (x: A) => x, 3) = 3` by `refl` — the inserted
   instantiation actually reduces; and via a `let`-alias literal
   (`let g = λ {A: Type<0>} (x: A) => x; g(3) = 3`).
3. *Open element type*: inside `fn h<B>(y: B, f: {A: Type<0>} -> A -> A) ->
   B { f(y) }` — `A` solved to the open `B`.
4. *Checking position, bare value*: skeletal `f` passed bare where
   `Nat -> Nat` is expected (the §5.2 prefix route); and the **suppression**
   positive — bare polymorphic value passed to a `{A: Type<0>} -> A -> A`
   parameter arrives verbatim (§5.3; the fixed probe-5 shape).
5. *Statement codomain*: `theorem …(f: {A: Type<0>} -> A -> A): f(0) = 0`
   style — insertion inside a written type's codomain (§3.1's `elab_ty` line).
6. *Record field*: `record Endo { f: {A: Type<0>} -> A -> A }` — `w.f(3)`
   inserts; `w.f` bare in checking position; a record literal whose field is
   an implicit lambda checks (§6.1's third site); `let { f } = w;` carries
   the skeleton onto the alias.
7. *Deferral and hints*: `f(?p)` on a skeletal value raises a goal named
   from the skeleton binder; the deferred-argument retry works on a value
   callee (D1's machinery, value head).
8. *`@`*: `@f(Nat, 3)` fully positional on a skeletal local (§7.1).

**Negative controls (each message asserted):**

1. Skeleton mismatch: implicit binder where the expected skeleton says
   explicit (§7.3-3); implicit binder against a plain expected type
   (§7.3-2).
2. **The degradation, pinned as behavior**: a function type that genuinely
   arrives by computation — e.g. projected through a `Val -> Type` value
   (`docs/record-type-values.md` §4's shape) or read back off a decoded
   code — offers no insertion: bare `f(x)` fails with the ordinary explicit
   error (not a junk instantiation, not a kernel LevelMismatch), and the
   explicit spelling `f(Nat, x)` succeeds. This is the design's contract,
   not an accident, and this test is where it is written down.
3. Unsolvable implicit on a value: §7.3-1 verbatim (no `f<…>` escape
   offered).
4. Implicit lambda in a non-`let` inference position refused; the `let`
   harvest positive beside it.
5. Shadowing: a local skeletal `f` over a global `f` with different
   `ParamMeta` uses the skeleton's names in hints (pins §4.2's
   params-passed-not-recovered refactor).
6. Parser: `{` still refused (elaborator now, §3.4) in result position;
   `@` on a non-name head still grammar-rejected; `let { f: x } = e;`
   record patterns unaffected; `match t as x -> {p: Nat} -> T { … }` parses
   with the binder in the motive.

**Suites that must stay green unchanged**: `implicit_args.rs`,
`goal_holes.rs`, `polymorphism.rs`, `congruence_lgg.rs`, `determinism.rs`
(the new insertion is ordered and structural), and the two whole-library
acceptance tests. Inner loop on `scripts/test --fast`; the round's final
verification is the plain full `scripts/test` — grammar and elaborator
changes touch everything, the rule is the rule.
