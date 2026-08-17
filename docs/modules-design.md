# Modules: imports, per-file namespaces, and the library as Heather files

Design doc for `issues/modules.md` (2026-08-05). The claim being designed:
one `.hthr` file can use another's declarations, so `Nat`'s order kit,
`Option`, and `List` can live once, as Heather source, and every library
file stops re-declaring them (`issues/prelude-option-and-friends.md` is the
record of the tax).

Scope guard, from the issue: v1 is module **organization** — imports,
namespaces, resolution. Separate compilation, serialization of checked
kernel state, and per-module caching are non-goals, but §8 records the
routes so nothing here forecloses them.

## 1. Ground truth (what the design leans on, verified 2026-08-05)

- **The kernel is nameless.** `GlobalVar` is a de Bruijn index into one flat
  Ψ telescope (`crates/kernel/src/term.rs:27`); no kernel object carries a
  surface name. A module system therefore lives entirely in the
  syntax/elab crates: **no kernel change, no ch. 07 obligation.**
- **The elaborator is one monotone accumulator.** `Elaborator` holds Ψ plus
  the name tables — `globals: HashMap<String, GlobalInfo>`, `inductives`,
  `ctors`, `record_fields`, `meta_defs`/`meta_slots`
  (`crates/elab/src/lib.rs:376`). Declaration order is Ψ order; a failed
  declaration registers nothing (`check_source` recovery, `lib.rs:559`).
- **The prelude is already a module in all but name.** `with_prelude`
  elaborates `crates/elab/src/prelude.hthr` into a fresh accumulator
  (`lib.rs:541`). "Import" as a mechanism exists; what's missing is files,
  names for them, and a resolution story.
- **Generator keys are nominal, not named.** `GenDefs` keys on the
  inductive's `tag: u32` (`gendefs.rs:48` — "Keys are **nominal**"), so
  qualification cannot disturb μ_D / SkelCode / IdxCode recognition. The
  §10.6 alias-hostility of `issues/indexed-families.md` is about an index
  type surviving *as a declaration*, which imports preserve trivially.
- **Constructor names are globally unique today** only because "there is no
  path syntax yet" (`lib.rs:387`). That comment is a to-do addressed here,
  not an invariant to preserve.
- **The CLI checks each file against a fresh prelude'd elaborator**
  (`crates/cli/src/main.rs:37`), with the comment "there is no import
  system for one file to see another through" — the other half of the same
  to-do.

## 2. The unit: a module is a file

One module = one `.hthr` file; the module's name is the file stem, which
must be an identifier. No module header inside the file — the file system
already says the name, and a header is a second copy that drifts. No inline
`mod { … }` nesting in v1; nothing below forecloses it, but nothing needs
it either (the repo's whole library is two files).

Directories are namespaces-of-modules only for *lookup* (§3); there is no
`std::nat` compound path in v1. Single-segment names, search-path lookup.
If the library grows past one directory, compound paths are a parser-only
extension.

## 3. Imports

### 3.1 Syntax

New item, allowed only before the first declaration (readability; also
makes the import DAG readable without parsing declarations):

```heather
import nat;                 // qualified access: nat::le_add
import option::{Option, some_ne_none};   // these names, unqualified
```

`import m::{…}` also brings `m` itself into scope for qualified access —
the list is a convenience, not a different mode. No glob form `import m::*;`
in v1: §4's resolution regime makes plain `import m;` already behave like
the useful part of a glob (see below), so a glob adds nothing but a second
spelling.

### 3.2 Resolution and semantics

`import nat` resolves `nat.hthr` against, in order: the importing file's
directory, then each `-L <dir>` given to the CLI (the standard library is
`-L lib/std`, defaulted by the CLI when the directory exists). First hit
wins; a name found in two search dirs is an error, not a precedence.

Semantics: the import DAG is walked depth-first from the root file,
**each module elaborated exactly once** (dedup by canonical path), in
topological order, into the single shared Ψ — exactly what `with_prelude`
does today, iterated. Diamonds are free (dedup), cycles are an error with
the cycle printed. The kernel sees one telescope and never knows.

Errors in an imported module are reported against that module's own source
(the CLI already renders per-file snippets); the importing file then checks
against whatever did land, per the existing recovery discipline.

The prelude stays an implicit import of every module, unchanged. It does
not grow: new library content goes in `lib/std/*.hthr` as ordinary
modules (§7).

### 3.3 What one run means now

`heather check lib/ir_v1.hthr` checks the transitive closure. A fresh
elaborator per CLI *root* argument stays (two roots re-elaborate a shared
import; caching is §8's problem, and at current sizes an import costs what
the prelude costs — milliseconds for prelude-sized modules).

## 4. Names: unambiguous-or-qualified, never silently shadowed

The regime, and the one deliberate departure from Rust/ML convention:
**a name is a reference, not a slot.** Heather has no overloading, no
first-match scoping between modules, and instance identity is intensional
— so the name layer can be honest in a way `open`-style systems aren't:

- `import nat;` puts all of `nat`'s declarations in scope **unqualified**.
- A name that resolves uniquely across the file's own declarations and all
  its imports just works, unqualified.
- A name declared in two visible places is not shadowed by import order —
  it is **ambiguous at use**, an error naming both origins, fixed by
  writing `nat::sub` (or an `import …::{…}` list, which is a standing
  disambiguation: a listed name binds unqualified and beats collision — an
  explicit list is the user saying which one they mean).
- A file's own declaration colliding with an *unlisted* imported name is
  fine (locals win is the one precedence: the file you are reading beats
  the file you aren't) — but colliding with a **listed** import is an
  error, since the user asked for both by name.

Why ambiguity-at-use instead of Rust's explicit-list-only: the library is
proof text. `theorem` files want `le_add`, `add_succ_left`, `sub_zero` in
scope by the dozen, and an import list that restates a module's whole
export surface is the drift-prone copy this repo's issue tracker already
banned for issues. Why not `open`-with-shadowing: silent capture in proof
text is a soundness-adjacent footgun — a theorem that still checks but
about the wrong `sub` is exactly the failure a prover surface must not
make quiet. Ambiguity-at-use is the honest middle, and it is cheap here
*because* there is no overloading to make ambiguity common.

Qualification is `::` (Rust-flavored surface; `.` is projection/method).
Parser: `ident :: ident` as an atom, composing with existing call/type
syntax — `nat::le_add(p, q)`, `option::Option<Nat>`.

Constructors and record fields ride the same rule: a constructor name is
ambiguous only if two visible inductives declare it, and then either
qualification (`Option::None` — constructor names qualify by *type* name,
which is how they are already keyed per-inductive) or checking position
can settle it. v1 implements qualification only; **type-directed
resolution** (in checking position the expected type names the inductive,
so a bare `None` is unambiguous — the bidirectional elaborator already has
the type in hand) is filed as the follow-up ergonomic, not built. It is
the feature that finally deletes the "globally unique" constraint rather
than merely scoping it.

**Built 2026-08-16** (`issues/ctor-resolution-by-expected-type.md`), and
§8's two invariants sized it. `Elaborator::ctor_here_expected` is the
judgment: after the ordinary reading fails, the expected type's
declaration is asked for the name, through the very `arm_ctor_index` a
`match` arm uses — so the two type-directed constructor routes are one
function, and the `Option::None` spelling costs nothing extra in either.
Three things it is *not*, each a control in `crates/elab/tests/modules.rs`:

- it is not consulted first — a name that resolves today keeps its
  declaration, so the type only settles what the name layer left
  unsettled;
- it does not fire when a visible **non-constructor** declares the name.
  A `fn None() -> Option<Nat>` is as admissible at an expected
  `Option<Nat>` as the constructor is, so the type is not evidence
  between them and the name stays ambiguous. Without this guard the route
  breaks the second invariant outright: a file meaning the *function*
  would start meaning the constructor the moment a second `None` became
  visible;
- it does not beat a binder. The shadowing check is repeated inside the
  route rather than inherited, because a local `None` wins at *every*
  expected type.

Synthesis position is unchanged and still needs uniqueness or
qualification — that is invariant 1, not an omission. One consequence of
that worth knowing before writing a file: whether an **argument** is
checking position depends on the parameter, not on the call. `mono(None)`
at `fn mono(o: Option<Nat>)` is settled; `unwrap_or(None, 9)` at
`fn unwrap_or<A>(o: Option<A>, …)` is not, because that argument is where
`A` comes from — an argument that is the *source* of an instantiation
cannot also be checked against it. Both are pinned in
`crates/elab/tests/modules.rs`.

`meta_slots` stays global: one template per slot across the program, a
second claim is an error at the join (same rule as today, now possibly
triggered by an import — the error names both modules). `record_fields`
is a negative test; union is correct as-is.

## 5. What the tables become

Mechanically: every name table keys `(module, name)`; the resolver takes
the importing file's visibility (own module + imports + listed names) and
returns either the unique hit, or the ambiguity error with origins. The
`GlobalInfo.abs` machinery, goal padding, and everything Ψ-facing is
untouched — Ψ never knew about names. `Inductive.name` gains a module
field for diagnostics and qualified constructor display. The tag counter
is per-run and topo-order-stable; nothing new.

## 6. Visibility: deferred, deliberately

Everything is public in v1. Privacy in this language is namespace hygiene,
not soundness — proofs are checked before Ψ registration and importers
consume statements, so a "private" helper lemma leaks convenience, never
trust. Under §4's regime, pollution only bites on actual collision, which
is an error message away from fixed. When a real library wants `priv`
(or `pub` flipped default), it is one flag on the name tables. Recorded as
a seam, not built.

## 7. The standard library, and the acceptance migration

`lib/std/` is born with:

- `nat.hthr` — the order kit currently local to `ir_v1.hthr`: `leb`, `Le`,
  `sub`, `le_add`, `add_left_zero`, `add_succ_left`, `sub_zero`, and the
  add/mul lemmas the prelude discussion listed.
- `option.hthr` — generic `Option<A>` with `map`, `and_then`, `unwrap_or`.
- `list.hthr` — `List<A>` with `append`, `nth`, `map`. (`nth` became
  `List::nth`, the first member of a type's namespace, in the 2026-08-05
  ergonomics round — §8's receiver-direction bullet, landed:
  `issues/type-owned-members-receiver-slice.md`.)

That is the **birth** inventory and is kept as such; it is not a current
listing. `lib/std/` has since grown by deliberate waves — `logic`, `bool`,
`algebra`, `pair`, and an order/arithmetic kit and list API many times the
size of the three bullets above (`issues/std-api-waves.md` sequences them,
and each wave's own issue holds its content). Read the directory for what is
there now.

Acceptance is the migration: `lib/ir_v1.hthr` imports `nat` (and `option`
where `OptVal` permits — `OptVal`'s monomorphic uses migrate only where
the swap is mechanical; forcing it is not the round's job) and deletes its
local copies. The prelude (`prelude.hthr`) does not move in this round:
`sym`/`trans`/`cong_succ` are load-bearing in every file and implicit
import is their correct home either way.

## 8. The horizon this must not foreclose (recorded, not built)

- **Caching / separate checking.** The natural unit is a module's
  (Ψ-segment, name table) pair keyed by content hash of the module and its
  import closure. Two order-sensitivities to keep out of *persistent*
  artifacts when that round comes: `GlobalVar` indices (Ψ-position depends
  on import order) and nominal tags (allocation order). Both are
  per-run-stable today and nothing in v1 writes either to disk — keep it
  that way. This is also `ir_v1`'s 59-second answer: the deep acceptance
  theorems become their own module, checked when touched.
- **Parameterized modules are generators, not functors.** The kernel
  already binds Ψ-extensions (`Λ(g : Ctx)`, `Λ(U : Typ)`,
  `term.rs:581–615`), and the 2026-08-02 expressiveness reading
  (`issues/generators-in-the-language.md`) established the working shape:
  a layer-m function returning code, instantiated per argument, is how
  level- and type-generic libraries were already going to work. A "module
  parameterized by a type" is that same object wearing an import — so
  ML-style functors need **no new mechanism**, only the
  generators-in-the-language rounds this project already intends. Design
  consequence for v1: nothing — except that module names must not become
  load-bearing inside elaborated terms (they don't; Ψ is nameless), so a
  generated module instantiation can share the namespace machinery.
- **One resolution judgment.** The elaborator already resolves
  type-directedly in two places: `.` fields/methods are settled by the
  receiver's type (`docs/surface-records.md` §4.2), and §4's follow-up
  gives constructors the same treatment from the expected type. Operator
  notation over typeclasses (`a - b` → the `Sub`-class's `sub` at `a`'s
  type) is the third instance of the same shape, and the Compile
  resolver the fourth. The direction worth holding: these are all one
  judgment — `resolve(name, candidates-in-scope, type evidence) → unique
  or error` — where §4's name regime is the degenerate case (no type
  evidence). Two invariants make the family honest, and any future
  resolver should be checked against both:
  - **Synthesis position needs uniqueness; checking position may use the
    expected type to shrink the candidate set.** Bidirectionality is the
    oracle, and it is already deterministic.

    *Amended 2026-08-16* (`issues/false-collides-with-bools-constructor.md`):
    the **syntactic position** may shrink it too, on the same licence — a
    *type* position never considers a constructor a candidate
    (`names::resolve_kinds`, with `lookup_inductive` passing `[Inductive]`),
    because a constructor is not a type and that reading could never have
    elaborated. The dual now holds inside the expected-type route as well: an
    inductive expected type does not consider a *type name* a candidate, since
    a type name's own type is a universe. A `fn` of the same name still stands
    the route down and must — it may genuinely return the expected type, and
    choosing there would be a decision rather than a shrink. The rule to carry
    forward: **shrink only where the dropped reading could not have checked**,
    never where it merely looks less likely.
  - **Library growth may introduce errors, never reinterpretations.** A
    new declaration in an imported module can make a bare name ambiguous
    (a loud, local fix: qualify) — it must never silently change which
    declaration a checked file meant. Import-order shadowing violates
    this; ambiguity-at-use, receiver-direction, and
    expected-type-direction all satisfy it.

  Two free wins inside the regime, cheap enough to schedule early:
  **match patterns** never need visibility at all (the scrutinee's type
  names the inductive, so arm constructors resolve through it — worth
  doing in v1's arm walk if it falls out), and bare constructors in
  checking position (`None` at expected `Option<A>`). Both are now
  built — the arm walk with v1, checking position 2026-08-16 (§4) —
  and the second one found the first's *third* site, which is not free
  and is not done: a bare name in a **deep pattern's column** is
  classified with no type evidence at all, so an ambiguous one becomes a
  binder silently (`issues/deep-pattern-ctor-needs-column-type.md`). It
  is the one member of this family that currently violates the second
  invariant below. Deliberately *out*:
  expected-type-directed **lemma** resolution (picking between two
  ambiguous `le_add`s by which statement unifies) — proof text choosing
  premises by unification is a reinterpretation hazard as libraries grow,
  which the second invariant exists to forbid.
- **`use` as the policy keyword.** Reserved by decision 2. If scoped
  instance selection (`let instance` in compile-typeclass round-2's
  sketch), notation packs, or per-file meta-template choice (`meta_slots`
  conflicts dissolving into "the template you `use`d") want a surface
  form, `use` is it: `import` moves *names* into scope, `use` moves
  *policies* into the resolution set. Nothing parses yet; the reservation
  is the design content.
- **Module-scoped instances.** `compile-typeclass-design`'s resolver round
  wants scoped instance visibility (`let instance` was round-2's sketch);
  a module boundary is the natural scope. Nothing to do now; the resolver
  round should read §4 when it happens. One live seam recorded there
  today: instance keying "on elaborated syntax" must not mean raw
  `GlobalVar` indices, which §8's first bullet makes order-sensitive —
  key on the definition's identity (module, name, or content hash), not
  its Ψ-position.

## 9. What this amends elsewhere

- `issues/prelude-option-and-friends.md` layer 1 is satisfied by §7
  instead of `with_prelude` seeding; layers 2–3 (`?`-chaining, syntax)
  stay open there, unblocked and unchanged.
- `lib.rs:387`'s "globally unique, no path syntax yet" comment and
  `docs/inductive-tier0-lowering.md`'s statement of it: scoped per §4.
- `crates/cli/src/main.rs:37`'s "no import system" comment: retired.
- `docs/frontend-benchmarking.md` corpus: `ir_v1.hthr` becomes
  multi-file; the corpus timer needs to time the closure (parse/elab/kernel
  splits already sum per-declaration, so this is plumbing, not method).

## 10. Phasing

1. **Parser + AST**: `Item::Import`, `::`-qualified atoms in expression
   and type position. Pure syntax, testable alone.
2. **Resolver**: name tables keyed by module, visibility computation,
   ambiguity errors. `Elaborator::elab_module_source(module, src)`;
   `with_prelude` becomes the degenerate call.
3. **CLI + loader**: DAG walk, dedup, cycle error, `-L`, default
   `lib/std`. Multi-file diagnostics.
4. **Library + migration**: §7's three modules, `ir_v1.hthr` imports
   `nat`, deletes the local kit. Full suite + bench `--check` green;
   re-save the corpus baselines that legitimately change shape.

Tests, by the four-axes discipline where it applies plus negatives per
positive: cycle detection, both ambiguity errors (unlisted collision at
use; listed collision at import), locals-beat-imports, cross-module
inductive + match + generated artifacts (μ_D et al. resolved through an
import), cross-module `meta fn` template dispatch, a qualified constructor
in checking and synthesis position, and the corpus check that `ir_v1`
post-migration proves exactly what it proved before.

### 10.1 Stored declarations retain their resolution environment (2026-08-09)

An inductive keeps field types, value-parameter types, and route-2b result
indices as surface syntax because they must be re-lowered at each
instantiation. That syntax now carries the declaration's `Scope`; every
re-lowering temporarily installs it in the resolver, nesting when one stored
declaration refers to another and restoring the use-site scope afterward.
Consequently, adding a same-named declaration to a later imported module may
make the later module's own bare use ambiguous, but cannot reinterpret or
invalidate syntax already checked in an earlier declaration. The module
acceptance suite crosses ordinary fields, recursive fields and matches, value
parameters, and a forded result-index expression with same-name collisions.

## Decisions (2026-08-05, with MinusGix)

1. §4's regime signed off: ambiguity-at-use, locals-beat-imports, no
   silent shadowing between modules.
2. Keyword is **`import`** — the operation brings in a chunk, not a part.
   `use` is deliberately **reserved**, unspent: the standing candidate
   meaning is §8's policy-scope bullet (bringing *instances, notation,
   meta templates* into the resolution set, as distinct from bringing
   names into scope). No `use` form parses in v1.
3. Migration scope is minimal (§7). Splitting `ir_v1.hthr` itself waits
   for the round after — likely the caching round that makes it pay.
4. `lib/std/` layout confirmed.
