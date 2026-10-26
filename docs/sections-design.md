# Sections: writing a declaration's context once

Status: assessment and proposal (2026-10-26). Nothing here is built. Tracking
issues: `issues/section-spliced-heads.md` (the proposal),
`issues/owner-sibling-names.md` (the separate resolution change in §6).

The question: should Heather have sections, or some other way to organise
code, so that a group of declarations stops repeating its context? It is
answered against what `lib/` repeats today, measured by
`scripts/signature-census`, rather than against what other provers have.

**Answer, in short.** The repetition is real but concentrated. Across the
library, everything any mechanism could remove is a few percent of the text;
in a dozen files (classes with operator parameters, the x86 stack and site
theorems, the float `Format` theory, the Linux I/O specs, the FunctionIR
indexing lemmas) the repeated context is most of each declaration head. That
is worth one small mechanism, not a module system:

1. **Build a section whose head is spliced into every declaration in it**
   (§5): `section<A: StrictOrder(≈, <, <=)> { … }` means exactly what writing
   `<A: StrictOrder(≈, <, <=)>` at the front of each head inside would mean.
   It is a parser desugaring. There is no inclusion rule, and there is no
   difference between how a declaration is called inside and outside the
   block. A generic or implicit binder that some member's head does not
   determine is refused at that member, so a member never gets a binder that
   no call could fill.
2. **Keep the owner on each head** (`theorem StrictOrder::le_refl`), with no
   owner blocks. The owner prefix is the smallest repetition, and `grep 'fn
   List::append'` finding the declaration is worth more than the characters.
3. **Separately, let a member name its owner's other members bare** (§6),
   with the same ambiguity rank as every other name and no precedence.
4. **Do not build** Lean-style `variable` inclusion, Coq-style discharge,
   Idris/Agda parameter blocks, functor modules, named telescopes or `open`
   (§7). Each has a recorded condition under which to look at it again.

## 1. What the library repeats

`scripts/signature-census` reads every top-level `fn` and `theorem` head in
`lib/` (`lib/_tests` skipped) and counts text that four mechanisms would
remove. Its numbers on master at `9a80b41`:

| | chars | of `lib/` |
|---|---:|---:|
| the library | 2,893,132 | |
| all `fn`/`theorem` heads (name, `<…>`, `(…)`) | 473,423 | 16.4% |
| owner prefix, over runs of ≥3 same-owner heads | 13,195 | 0.5% |
| common leading binders, over runs of ≥3 heads (spliced sections) | 29,574 | 1.0% |
| any identical binder in ≥3 consecutive heads (upper bound for `variable`) | 75,943 | 2.6% |
| `Owner::x` written inside one of `Owner`'s own members | 23,761 | 0.8% |

There are 5,196 heads, and 3,099 of them sit in a run of three or more that
shares a leading binder. So most declarations have a neighbour with the same
context, but most of that shared context is short: `self a: Int`, `<A>`,
`self F: Format`. The long prefixes are where the cost is felt:

| heads | file | prefix every head repeats |
|---:|---|---|
| 32 | `std/algebra/ordered_field.hthr` | `<A: OrderedAddGroup(≈, <, <=, +)>` |
| 18 | `std/algebra/ordered_field.hthr` | `<A: StrictOrder(≈, <, <=)>` |
| 14 | `std/algebra/ordered_field.hthr` | `<A: OrderedField(≈, <, <=, +, *)>(x: A, …` |
| 17 | `native/function_ir/function_ir.hthr` | `({directory: PortDirectory}, {index: Nat}, {width: Nat}, {output: Nat}, …` |
| 23 | `std/arch/x86_64/x86_64_stack_runs.hthr` | `<M>(self site: Site<M>, …` |
| 6 | `std/arch/x86_64/x86_64_stack.hthr` | `<M>({fetch: FetchAccess<M>}, {data: ByteReadAccess<M>}, self stack: Stack<M>(fetch, data), …` |
| 22, 19 | `std/os/linux/linux_x86_64_{sim,io}.hthr` | `<M>(io: LinuxIo<M>, …` |
| 24, 28, 19 | `std/num/float/{round,error}.hthr` | `(self F: Format, …` |
| 5 | `std/num/float/round.hthr` | `(self F: Format, x: Rat, h: Nat, st: Bool, a: F.Approx(x, h, st), …` |
| 7 | `native/stream_filter_spec.hthr` | `<C>(input: BitVec(64), output: BitVec(64), step: C → BitVec(8) → Filtered<C>, …` |

`scripts/signature-census --runs` prints the full ranking. Three observations
shape the proposal:

- **Most measured repetition is a leading prefix.** The heads already put the
  shared context first. Splicing a prefix keeps every argument where it is,
  so no call site changes. The larger "any position" figure is only
  reachable by moving shared binders to the front, which reorders explicit
  arguments and changes every caller (§4.1).
- **Runs end at other items.** A `record`, `designation` or `instance` between
  two heads ends the run in the census, and most runs are already grouped by
  subject. Nothing suggests a block should hold anything but `fn` and
  `theorem`.
- **Little repetition crosses files.** The most repeated three-binder window
  across files, `{fetch: FetchAccess<M>}, {data: ByteReadAccess<M>}, self
  stack: Stack<M>(fetch, data)`, is in 18 heads in 3 files. The library
  already bundles a cross-file context when it is a concept: `Site<M>` carries
  `program`, `fetch` and `data`. A named-telescope feature has no customer
  (§7).

## 2. What Heather already has

Several mechanisms already cut what a head has to say. A section adds to
these and does not replace any of them.

- **Owned names.** `fn List::append`, `theorem ten_pow::pos`. An owner is a
  type, a class, or a function (`issues/function-owned-members.md`), and the
  §4 regime of `docs/modules-design.md` resolves the whole string.
- **Receivers.** `self xs: List<A>` makes `xs.append(ys)` the call, so a
  member's subject is never passed by name.
- **Inline constraints and type-level projection.** `<A: Monoid>` desugars in
  the parser to an anonymous solver parameter, and `A.unit` projects from the
  constraint (`issues/requires-placement-syntax.md`, R2 decisions,
  2026-08-07/08). A section's generic list is this same grammar.
- **Binder sugar** (`n: Pos<Nat>`, `h := omega`) and records that bundle a
  context which is a concept (`Site<M>`, `Format`).
- **Modules and folders.** A file is a module, folders are only for lookup,
  and facades re-export names (`docs/modules-design.md`,
  `docs/lib-layout-design.md`).

The parser refuses `section`, `given` and `context` by name and points to the
open item in `issues/requires-placement-syntax.md`
(`crates/syntax/src/parser.rs`, the item loop). That issue's round 2
recommended `section { given A: Monoid; … }` with a syntactic inclusion rule.
§4 explains why this document recommends splicing instead.

Two facts (and a third in §5.2) were checked by probe on 2026-10-26 (release
build of `9a80b41`):

- `section<A> { fn id(x: A) → A { x } }` is refused with that message.
- Inside `fn Box::twice(self b: Box)`, the bare name `get` for a sibling
  `Box::get` is "unbound name `get`". `Box::get(b)` and `b.get()` both
  elaborate. A member's own name is bound in its body (recursion), but its
  siblings' names are not.

## 3. How others do it

| mechanism | written once | the declaration outside | inside the block | which binders a declaration gets |
|---|---|---|---|---|
| Coq `Section` + `Variable`/`Context` | binders, hypotheses | generalised at `End` | section variables are fixed constants, so calls omit them | those used in the type *or body*; `Proof using` overrides |
| Lean 4 `variable` (in `section`/`namespace`) | binders, instances | real parameters | real parameters, so calls pass explicit ones | mentioned in the header, plus instance binders about those, plus `include`; since 2024 a theorem's body no longer counts, while a `def`'s still does |
| Lean `namespace X` | the `X.` prefix | `X.f` | `f` is reachable bare | n/a |
| Agda parameterised module `module M (A : Set) where` | parameters | every definition takes *all* parameters | fixed, calls omit them | all |
| Agda generalisable `variable` | binders | implicit parameters | same | those used in the signature, ordered by dependency |
| Idris 2 `parameters (x : T)` | parameters | every function takes all of them | fixed, calls omit them | all |
| Isabelle `context`/`locale` (`fixes`, `assumes`) | fixed terms and assumptions | generalised on export; locales are instantiated by `interpretation` | fixed | those used |
| ML functors | a module signature | instantiated module `F(X)` | n/a | all |
| Rust `impl<T> Foo<T> { … }` | generics, `Self`, the `Foo::` owner | `Foo::f` | `Self::f` or the receiver | all generics, with unused ones refused |

These systems differ on two questions, which §4 settles for Heather:

1. **Inclusion.** Does every declaration get every binder (Agda modules, Idris,
   Rust), only those its signature mentions (Lean theorems, Agda `variable`), or
   those its body uses too (Coq, Lean `def`s, Isabelle)?
2. **Call shape inside the block.** Are block binders fixed constants that
   sibling calls omit (Coq, Agda modules, Idris, Isabelle), or real parameters
   that callers pass everywhere (Lean, Rust)?

## 4. The two questions, for Heather

### 4.1 Inclusion: splice everything, and refuse what cannot be filled

**A body cannot be allowed to decide a signature.** That was settled in round
2 of `issues/requires-placement-syntax.md`, and the project's interface
doctrine depends on it: module images, early cutoff
(`docs/module-interface-cutoff-design.md`) and every client read a
declaration's elaborated head, and a proof edit must not move it. So the Coq,
Isabelle and Lean-`def` rules are out.

That leaves "mentioned in the signature" (Lean theorems) and "all of them"
(splicing). Round 2 recommended the first. Measured against the library, the
second wins on every point that matters here:

- **What it costs to read.** With splicing, a declaration's full head is the
  section head followed by its own head, in that order, with no rule to
  apply. Under the mention rule the reader has to work out which binders were
  included and in what order. That needs the dependency closure (`stack:
  Stack<M>(fetch, data)` pulls in `fetch`, `data`, `M`), the riding of
  instance binders, and an `include`/`using` escape for hypotheses only a
  proof uses. `laid: site.program.laid_out().IsTrue()` in
  `function_ir_lower_calls.hthr` is that case: no `call_*` statement mentions
  it, and every proof uses it. Lean changed this rule as recently as 2024,
  and it is the part of `variable` that users have to learn by experience.
- **What it delivers.** The mention rule's extra reach (2.6% against 1.0% in
  §1) comes from binders that are not in leading position. Making them
  leading means reordering explicit arguments, and that changes every call.
  Without that reordering the two rules remove about the same text from the
  library as it stands.
- **What it costs to build.** Splicing is a parser desugaring, as the inline
  `<A: Monoid>` form already is. Every pass after the parser (elaborator,
  module images, `--only`, export, certgen identity) sees ordinary
  declarations it already handles. The mention rule needs a free-name analysis
  of surface heads, which has to be correct before the elaborator has resolved
  anything.

What the mention rule protects against is a member that does not use a
section binder. For an explicit binder this is harmless: the member has an
unused parameter, as it could today, and the author moves it out of the
section. For a generic or implicit binder it is a trap, because nothing at a
call site determines it. **So splicing comes with one check**: after the
splice, a generic or implicit section binder that the member's own head does
not determine is refused at that member, naming the binder and suggesting
it move out of the section. This is the mention rule turned into an error. It
never quietly drops or adds a binder.

### 4.2 Call shape: real parameters everywhere

Coq, Agda modules, Idris and Isabelle fix the block's binders inside it, so a
sibling call omits them. In Heather the gain from that is small and the cost
is a second meaning for every name:

- Generic and implicit binders are already inferred at every call, so for the
  library's largest runs (`<A: OrderedAddGroup(…)>`, `{F: Format}`) the
  inside and outside call sites are already the same.
- For a receiver binder (`self F: Format`, `self site: Site<M>`), calls are
  already `F.grid(m)` and `site.Moves(…)`.
- What is left is explicit non-receiver binders (`site, laid, stack` in the
  `call_*` theorems, `io` in the Linux specs). Fixing those inside a block
  would make `call_spills(d, s0, …)` mean one thing above `}` and another
  below it. It would also need the elaborator to know which block a call site
  is in, so a member checked alone by `--only` would elaborate differently
  from the same member in its file.

So section binders are real parameters inside the block and outside it, as in
Lean and Rust. If the explicit-binder call noise turns out to matter in
practice, that is a separate, measurable proposal (§7).

## 5. The proposal: spliced section heads

### 5.1 Surface

```heather
section<A: StrictOrder(≈, <, <=)> {

theorem StrictOrder::lt_asymm(x, y: A, h: x < y): ¬(y < x) {
    λ back => A.lt_irrefl(x, A.lt_trans(x, y, x, h, back))
}

theorem StrictOrder::le_refl(x: A): x <= x {
    A.le_of_not_lt(x, x, A.lt_irrefl(x))
}

}
```

```heather
section<M>({fetch: FetchAccess<M>}, {data: ByteReadAccess<M>}, self stack: Stack<M>(fetch, data)) {

fn Stack::at(i: Nat) → BitVec(64) { … }
fn Stack::Unchanged(from: Nat, before, after: M) → Type { … }
theorem Stack::unchanged_refl(from: Nat, memory: M): stack.Unchanged(from, memory, memory) { … }

}
```

```heather
section(self F: Format, x: Rat, h: Nat, st: Bool, a: F.Approx(x, h, st)) {

theorem Format::le_cut(m: Int, le: F.grid(m) <= x): m <= h.int() { … }
theorem Format::cut_le(m: Int, le: m <= h.int()): F.grid(m) <= x { … }

}
```

The grammar is `section` followed by an optional `<…>` list and an optional
`(…)` list. Both are exactly a declaration's (constraints, `+` stacking,
implicit braces, `self`, solver defaults, `requires`), so a reader who knows
how to read a head already knows how to read a section. A section with
neither list is refused, since an owner-only block is not proposed (§5.4).

### 5.2 Meaning

For every `fn` or `theorem` inside, prepend the section's `<…>` entries to
the member's `<…>` list and the section's `(…)` entries to the member's
`(…)` list. That is the whole meaning. A nested section concatenates its lists
onto the enclosing one. The desugared declaration is what a reader could have
written by hand, and a hand-written copy is the same term: the acceptance
tests pin this by `refl` between a spliced declaration and its hand-written
twin, at a concrete and an open carrier.

Rules that follow from it, each an error and none a precedence:

- A member's own binder with the same name as a section binder is refused.
  For type parameters this is the existing "duplicate type parameter" error.
  For value parameters it is a **new** check: today a head may repeat a value
  parameter's name, and the later binder shadows the earlier one (`fn f(x:
  Nat, x: Nat) → Nat { x }` checks and returns the second argument, probe
  2026-10-26). Spliced into a section, that would let a member silently shadow
  the section's binder, so the splice refuses it.
- Two `self` binders (one in the section, one in the member) are the
  existing two-receivers error.
- The undetermined-binder check of §4.1.
- Only `fn` and `theorem` (including `evidence theorem`) may appear inside.
  `meta fn` has its own binder kinds, and the other items have no head to
  splice into. Each is refused by name.

### 5.3 What does not change

The desugaring runs in the parser, so everything after it sees ordinary
`Item::Decl`s:

- **Module images and early cutoff** carry declarations, not blocks, so the
  image format does not change. Editing a section head changes every member's
  interface, and the existing cutoff invalidates exactly those members.
- **`--only Owner::name`** finds the member by its head name, as today.
- **Mutual groups** are found by adjacency over `Item::Decl`s
  (`docs/mutual-recursion-design.md` §1). A flattened section keeps its
  members adjacent, so a section boundary neither forms a group nor breaks
  one.
- **Export, certgen and generators** consume elaborated declarations or emit
  full heads, so they are unaffected. Generators do not need to emit
  sections.
- **`heather fmt`** never moves a line break or changes indentation, so it
  needs nothing. The style rule this document proposes is that a section's
  members are **not indented**, as in a C++ namespace or a Lean section. Moving
  an existing run into a section is then a diff of its heads alone, and `git
  diff -w` shows nothing else.

What has to change beyond the parser, so the round is not surprised:

- **Spans.** A spliced binder keeps its span in the section head. A type error
  in a section binder then shows up in every member, so the CLI reports
  identical (span, message) pairs once, with a count of members.
- **Display.** Any diagnostic that prints a member's signature prints the
  spliced one, because that is what the elaborator holds.
- **Tooling.** `tree-sitter-heather/grammar.js` and the Zed extension need
  the block, and the LSP's document outline should list members under it.
  `book/` gets a short section.
- **The refusal.** `section` stops being refused. `given` and `context` stay
  refused by name, since those decisions belong to
  `issues/requires-placement-syntax.md`.

### 5.4 Why the owner stays on each head

An owner block (`section List<A> { fn append … }` declaring `List::append`)
would remove the 0.5% of §1 and look like Rust's `impl`. That is the smallest
of the four repetitions, and the most expensive to lose: the codebase is
navigated by grep, by people and by Claude, and `fn List::append` and
`theorem Format::le_cut` are how a declaration is found. Inside a 1,700-line
`nat.hthr`, a head that says only `theorem le_add` would no longer say which
namespace it is in without scrolling to a block opener. `impl` is also
already taken (`impl op for Repr`, `docs/datarepr-design.md`). If owner blocks
are wanted later, the head grammar has room: `section List<A>` with a name
after the keyword parses unambiguously.

### 5.5 Migration

There is no sweep. A section is worth writing where a run is long and its
prefix is heavy. The census ranks the candidates, and in order the first ones
are `ordered_field.hthr` (three classes, 64 heads), `float/round.hthr` and
`float/error.hthr` (`self F: Format`, and the `Approx` hypothesis run),
`x86_64_stack.hthr` and `x86_64_stack_runs.hthr`, `linux_x86_64_{io,sim}.hthr`,
and `function_ir.hthr`'s `node_indexed_*` family. Each migration is checked
the way any refactor is: `scripts/timings --diff` over the file must show
identical count columns, which proves the terms did not change.

## 6. Owner-scoped sibling names (separate change)

The census's fourth row is 3,409 references, written as `Owner::x` inside a
member of `Owner`. Examples are `List::cong_cons(h, ih)` inside
`List::append_assoc`, and `Rat::…` throughout `rat.hthr`. These exist because
a member can name only itself bare (§2). Lean's namespaces make them bare.

This is a change to name resolution, not syntax, and it is independent of
sections. It is keyed on the declaration's owner, not on any block. The
proposed rule: inside the body of a member of `T`, `T`'s members are
candidates for a bare name, with the **same rank as every other visible
name**. That means no precedence, not even the "locals win" of
`docs/modules-design.md` §4, so a collision is an ambiguity error that names
both readings. The reason is §8's second invariant there: a file's own
`Rat::add` beating an imported ambient `add` would silently reinterpret
existing text that means the ambient one today. At ambiguity rank, landing the
rule can only produce loud errors in the library, and the round fixes those
by qualifying, as it would for any new collision.

It is a separate issue because its risk is resolution-wide, unlike the
parser-local section. It is the elimination half of
`issues/type-owned-namespaces.md` reaching non-receiver positions.

## 7. Not recommended now, and when to look again

- **Lean-style `variable` with a mention rule.** §4.1. Look again if, after
  the migrations in §5.5, the census's inclusion figure stays well above the
  prefix figure *in files that have already moved to sections*. That would
  mean the remaining repetition is not in leading position.
- **Coq/Idris/Agda fixed parameters (sibling calls omit block binders).**
  §4.2. Look again if a migrated file shows explicit section binders passed
  unchanged in most sibling calls. That count is a census a later round can
  add.
- **Parameterised modules and functors.** `docs/modules-design.md` §8 already
  decided that a parameterised module is a generator's output, and that the
  instantiation ceremony is what typeclasses exist to remove (round 2,
  candidate 14).
- **Named telescopes / bundles** (`params StackAt<M> = (…)`, or round 2's
  `context Sortable<A> = …`). Cross-file repetition is small (§1), and a
  context that recurs across files has so far been a concept that deserved a
  record. Look again when one telescope appears in more than a handful of
  files without being a concept.
- **`open` of a namespace or dictionary.** Ambiguity-at-use already makes
  names reachable without a precedence-ordered `open`, and §6 covers the
  in-namespace case. Round 2's judgement stands: if it is ever wanted, only as
  a body-side convenience that reports when it shadows.
- **Auto-bound implicits** (an unbound name in a head binds itself). A typo
  becomes a binder. This was rejected in round 2 (candidate 17) and nothing
  measured here argues otherwise.
- **Isabelle locales.** Classes and instances already are the theory and
  interpretation pair (`issues/type-owned-namespaces.md`, "Where typeclasses
  sit").

## 8. Decisions for Minus

1. **Splice (§4.1) rather than the mention rule round 2 recommended.**
   Recommended: splice, because it needs no rule to read and it is a parser
   desugaring.
2. **Keyword and form:** `section<…>(…) { … }`. The alternative is round 2's
   `section { given …; }`, which separates the binder grammar from the head
   grammar. Recommended: the head form, which reuses the declaration head
   grammar.
3. **Owner on each head, no owner blocks (§5.4).** Recommended: keep owners on
   heads.
4. **Owner-scoped sibling names (§6) at ambiguity rank.** Recommended: build
   it, separately from sections.
5. **Unindented section bodies** as the house style (§5.3).
