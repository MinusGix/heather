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
  committed `Names`, `Types`, `Traits`, `Representations`, and `MetaPrograms`
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

That reading is `heather_syntax::leading_imports`: the import items a source
opens with, lexed and parsed up to the first token that begins anything else.
The loader orders a build by it and the session derives a module's image key
from it, so neither parses a body; the elaborator reads the same imports
from the whole parse, and `crates/cli/tests/lib_closures.rs` holds the two
readings equal over every source in the tree. A source that does not parse
still has the imports it opens with, and the elaborator reports what is
wrong with it once its imports are built
(`issues/import-lines-read-by-whole-parses.md`).

`import m::{…}` also brings `m` itself into scope for qualified access —
the list is a convenience, not a different mode. No glob form `import m::*;`
in v1: §4's resolution regime makes plain `import m;` already behave like
the useful part of a glob (see below), so a glob adds nothing but a second
spelling.

### 3.2 Resolution and semantics

`import nat` resolves `nat.hthr` against, in order: the importing file's
directory, then each `-L <dir>` given to the CLI (the CLI defaults to
`-L lib/std -L lib` when no `-L` is given, each folder that exists), then the
directories below those `-L` dirs. First hit wins; a name found in two
search dirs of one tier is an error, not a precedence.

The lower tier (2026-09-29) is how the library keeps modules in
subdirectories — `lib/std/parser/`, `lib/std/arch/x86_64/`,
`lib/std/bitvec/` — without every client naming them. Names stay flat, so a
nested module carries its family in its stem (`parser_core`, `x86_64_fetch`,
`bitvec_omega`): the stem is the name every build uses, the CLI's and the
native builder's bundle alike. The tier is only consulted on a miss above
it, so a module below cannot shadow or conflict with a public one of the
same name. Since 2026-10-23 the whole library lives in such folders
(`docs/library/lib-layout-design.md`): a folder groups modules by subject and is
never part of a name. It leaves out dot-directories (`.git`, caches, worktree
checkouts that hold a second copy of the library), and it is why the editor
server searches `lib/std` and `lib` but not the workspace root: below a root
lie build trees and scratch copies, each a second hit for a library name.

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

`heather check lib/certgen/ir_v1.hthr` checks the transitive closure. A fresh
elaborator per CLI *path* argument stays (two file paths re-elaborate a shared
import; caching is §8's problem, and at current sizes an import costs what
the prelude costs — milliseconds for prelude-sized modules).

A directory path denotes one flat module set: every module the directory
can name (below), sorted by path; the CLI loads their union as one deduplicated closure, and prints one
result for the directory. Thus the whole standard library, including its
source lints, is one command with no repeated import diagnostics:

```sh
heather check lib/std
```

The target directory joins the search directories, so its descendants are
the lower tier of §3.2 for their import closure. Its roots are its own
`.hthr` files and every nested file (dot-directories aside) whose stem no
search directory answers itself: exactly the files `import <stem>` from the
directory reaches. A private nested module shadowed by a public one of the
same name (`shadow/base.hthr` under `base.hthr`) is no root, so it still
cannot conflict; and a module nothing imports is still checked. Until
2026-10-23 only the immediate files were roots, which left the folders
nobody at the top imported (`float/`, `arch/x86_64/`) out of
`heather check lib/std`; with the library in folders
(`docs/library/lib-layout-design.md`) it is the whole-library command again.

### 3.4 Reexports: a facade names the same declaration (2026-09-15)

`export m::{a, b, T::method};` is the one reexport form. It is an import
item with a public list: it must precede the first declaration, the list is
mandatory and nonempty (no `export m;`, no glob), and `export` stays a
contextual keyword, so `fn export()` still parses. A listed name may be
qualified by its owning type (`Box::get`) exactly as a declaration may.

Semantics are aliasing in the *visibility index only*. The facade gains
entries for the selected names that point at the declaration's **origin**
module; global coordinates, nominal tags, instance keys, signatures and
proof provenance never move, and a facade adds zero Ψ bindings. Resolving
`facade::x`, a listed `import facade::{x}`, a bare `x` visible through the
facade, a receiver call, or `T::ctor` all yield the origin, so a client that
imports both the component and its facade interchanges values and
certificates with no conversion, and an axiom audit reports the origin path.

Rules that follow from "same declaration, new spelling":

- **Ordinary imports stay private.** A facade's `import m;` or
  `import m::{h};` publishes no bare name; only the `export` list is visible
  bare to the facade's clients (`m::x` reaches them qualified, §3.6). Reexports chain: a facade may export a name it only
  sees through another facade, and the origin is still the declaring module.
- **Selecting a type selects its constructors.** Methods, instances and
  other type-owned members remain explicit selections (`Box::get`) — except
  that since 2026-11-03 a client that sees a type only through a facade also
  reaches the members the type's own module declares on it (`xs.map` through
  `export list::{List}`). They are read at the client's lookup, not copied
  into the facade, so a member added later needs no new facade image
  (§3.5).
- **Ambiguity is by origin.** A diamond reaching one declaration through
  two facades is a single hit; two different declarations sharing a name are
  ambiguous at use exactly as in §4, with no import-order precedence. A
  facade exporting the same name from two origins, or exporting a name it
  also declares with a different origin, is an error at the `export` item;
  a listed import naming a facade and its component agree and are not a
  double listing.
- **Generated names are refused** at the export list by the same access
  regime that refuses them at use (`docs/native/repr-access-spellings-design.md`).
- **The loader treats an export edge as an import edge**: same discovery,
  ordering, duplicate and cycle diagnostics. A semantic image records each
  import's exported names; replay re-validates every alias against the
  already accepted dependency world before the facade is admitted, and a
  changed origin invalidates the unchanged facade and its clients through
  the ordinary dependency identity.

Not built, by decision: whole-module reexport, renaming on export, and
hierarchical module paths. Each would obscure either the identity rule or
§3.2's flat search, and the parser umbrella needed none of them.

The acceptance client is `lib/std/parser/parser.hthr`, a pure facade over the
components in `lib/std/parser/` (the former core now lives in
`parser_core.hthr` so that no component imports the facade that exports
it); the mechanism is pinned in `crates/elab/tests/modules.rs` and the
loader/replay path in `crates/cli/tests/semantic.rs`.

### 3.5 The common prelude (2026-11-03)

`lib/std/core/common.hthr` is a facade over the core modules (`logic`, `bool`,
`option`, `list`, `pair`, `algebra`) that every module **later than it in a
run's order** imports implicitly (`heather_elab::COMMON_MODULE`,
`issues/std-prelude-facade.md`). The loader reads the prelude's closure
first and gives every module outside it the prelude as a first import; the
image keys (`semantic::module_imports`) and the elaborator (an import added
when the prelude is already in the module's world) apply the same rule, so
the modules the prelude exports from never see it and nothing cycles. A run
without the library on its search path has no prelude, and nothing changes.

What an importer gets:

- **Bare names**: exactly the prelude's export lists — the core types and
  their constructors, the `algebra` classes, `decide`/`decide_bit` for `if` —
  and, through §3.4's member rule, each exported type's own members. Not
  the core's theorems: `nat`'s and `int`'s `le_trans` stay out of every
  module's bare namespace.
- **Qualified names**: every module in the prelude's closure, qualified
  only (`nat::Nat::add_comm`, `logic::not_not_intro`). This is the
  "qualified-only" visibility `issues/feature-implicit-module-dependencies.md`
  asked for, and it is what the elaborator's own spellings need: an
  instance's global (`list::List::CollectionLiteral`) and a designated
  operation (`bool::Bool::and`) are qualified names resolved at the use
  site.
- **The ordered-field tower, qualified only** (2026-11-10): the prelude
  also has a plain `import ordered_field;`, which exports nothing bare but
  puts `ordered_field`, `semiring`, `order`, `int`, `omega`, `morphism` and
  `mono_laws` in its closure. The arithmetic tactics ask for their carrier
  classes by those qualified names (`ordered_field::OrderedField`,
  `semiring::CommRingOfInt`), so `import rat; import linarith;` is enough
  for `linarith` and `ring` at `Rat`
  (`issues/linarith-rat-without-ordered-field-import.md`). Those seven
  modules are now inside the prelude's closure and so no longer see it;
  each imports what it uses directly.

Why a curated facade and not "all of std sees all of std": measured on the
cloud box, the prelude's closure is already in almost every module's, so
the prelude costs almost nothing to build or replay, while an umbrella over
the whole library costs about a minute to replay warm for a one-line client,
and inside std the same idea is an import cycle that the single Ψ telescope
collapses into one unit (`issues/std-prelude-facade.md` has the numbers).

### 3.6 Every module's closure is visible qualified (2026-11-19)

§3.5's second bullet, generalized (decided with Minus, 2026-11-19): a
qualified name `m::x` resolves wherever `m` is in the **importing module's
own** closure, not only the prelude's (`names::closure_reaches`). Bare
names are unchanged: they still come only from direct imports, export
lists and §3.4's member rule.

The reason is the same as the prelude's, at every module. Registries are
closure-wide (`docs/infrastructure/module-dag-design.md` §2), so a
designation reached through the closure (`/` at words, declared in
`bitvec_div`) is found, and the elaborator then spells its operation
qualified (`bitvec_div::BitVec::udiv`); a tactic spells its lemmas the same
way (`bv_omega`'s `bitvec_omega::add_form`), and a generator looks up its
own names. Before this, each of those failed unless the client imported the
module itself, so `import sint;` made `x / 3` at a word fail, and a `runtime
fn` file carried a list of modules it never named
(`issues/runtime-generator-imports.md`).

Consequences:

- A module that wants a feature's machinery reachable by its importers
  imports it, and that is enough: `runtime` imports `bitvec_omega`,
  `bitvec_shift_nat`, `bitvec_div` and `bytes`, so `import bitvec; import
  runtime;` gives a `runtime fn` a measure over words, its reading of
  `x >> k`, and `/` and `%`.
- §3.4's "ordinary imports stay private" now holds for **bare** names
  only: a facade's `import m;` publishes no bare name, but `m::x` resolves
  in the facade's clients.
- A qualifier that is no loaded module's name (`List` in `List::map`) is
  answered without walking the closure; otherwise the walk is made once per
  scope and noted for the early cutoff exactly as the prelude's is.

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

A member of a namespace is the third qualified reading: `List::nth` (a
type's, 2026-08-05) and `ten_pow::pos` (a function's, 2026-10-11,
`issues/function-owned-members.md`) declare the whole string, which the
§4 regime then resolves like any name. It is tried after the module path
and the constructor, and it races neither: a function shares a module's
lower-case spelling, so where a visible module `f` declares `pos` and a
visible member `f::pos` exists too, `f::pos` is **ambiguous** and
`m::f::pos` names the member. A function named like a module its own file
sees is refused as an owner at the declaration. A `record` may be a type's
member too (`record Target::Held(self t: Target, …)`, 2026-11-18,
`issues/record-in-type-namespace.md`, `docs/language/surface-records.md`
§1.3): its type former and its constructor are both the whole string, so
`Target::Held` resolves as any member does and `t.Held(…)` reaches it
through the receiver.

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

The `MetaPrograms` slot index stays global: one template per slot across the
program, and a second claim is an error at the join (same rule as today, now possibly
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

Acceptance is the migration: `lib/certgen/ir_v1.hthr` imports `nat` (and `option`
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
  receiver's type (`docs/language/surface-records.md` §4.2), and §4's follow-up
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
  sketch), notation packs, or per-file meta-template choice (`MetaPrograms`
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
  `docs/inductives/inductive-tier0-lowering.md`'s statement of it: scoped per §4.
- `crates/cli/src/main.rs:37`'s "no import system" comment: retired.
- `docs/infrastructure/frontend-benchmarking.md` corpus: `ir_v1.hthr` becomes
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

### 10.2 Host generators choose a checked module scope (2026-09-28)

`Elaborator::with_module_scope(module, callback)` runs reflection and
source generators with the named module's saved name-resolution environment.
The module must already have been checked. Bare names follow its own
declarations, imports and listed-name choices; qualified names still need
visibility in that scope. Nested calls restore the enclosing scope, including
on an error or panic, and the callback receives an immutable elaborator.
Generators can therefore choose the context their certificate will import
without depending on which module the session checked last. The native loop
producer names its checked context module; its formatter reads in
`decimal_line`'s declaration scope. This selects name resolution only, not
instance or notation policy.

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
