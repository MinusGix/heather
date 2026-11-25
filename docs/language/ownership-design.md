# Ownership, borrows and shared mutation: the brief and the direction

Status: **a brief (§0 to §9) and the direction a design discussion with
Minus reached the same day (§10 on), 2026-11-24.** §10 says which decisions
of §4 it changes. §11 is what the tree has, §12 the work packages and their
order, §13 what is still open. Nothing of §10 is built; the packages of §12
carry their own issues.

Read with it: `docs/compilation-vision.md` (§1's settled principles,
especially 7 and 13, and §2.5 on memory a function is lent),
`docs/native/rung2-spans-design.md` (spans, the arena, the vector header),
`docs/language/effects-capabilities-design.md` §5 (today's linearity clause
for capabilities), `docs/language/sequencing-surface-design.md` §8.2
(`mut self`), `docs/native/facts-on-demand-design.md` §7 (the `Unique` fact),
and the issues `ownership-discipline-over-code`, `separation-algebra-ownership`,
`unique-fact`, `effects-uniqueness-surface` (milestone `nh-ownership` in
`docs/roadmap.md`).

## 0. The question, in Minus's words

Heather compiles ordinary functions (`runtime fn`) to verified native code.
To allocate vectors, build hash maps and update data in place, the compiler
has to know what is uniquely owned and what is shared, and when a reference
stops being valid.

- "We care about *knowing this information and optimizing based on it*
  rather than hoping the compiler will magically be good enough."
- Mutable value semantics alone "leaves obvious ways of writing things to
  indicate uniqueness on the table, opaquely."
- Rust's style is troublesome, but "less troublesome than it sounds: we have
  proofs and can make a much more drastic inference algorithm than anything
  Rust has trusted itself to implement."
- Translating Rust directly is "neat" but not the goal.
- "We definitely need borrows inside data structures." "Stored references
  are simply too important not to have. Similarly shared mutable structures
  needs support." They are "closely entangled with each other on everything",
  so they are designed together even if built in stages.
- The aim throughout this project: the most elegant method, easiest to work
  with, least special-cased; "less magic types, more powerful language
  features".

## 1. What Heather has today

- **Two worlds** (vision principle 1). An ordinary `fn` is mathematics and
  never runs. A `runtime fn` is compiled, and its compiled code is proved to
  compute the function it is written as: a certificate, checked by the
  kernel, per function, with no per-program hand proofs.
- **The meaning is pure.** A `mut self` method's meaning is a function
  `T → Mutated<T, R>` (the new receiver and the answer); `let mut` is
  rebinding; `t.f := v` is a record with a field replaced. Proofs about
  programs never mention aliasing (`lib/native/runtime/word_map_laws.hthr`,
  a hash table proved to be a finite map, is all values).
- **Call-scoped borrows exist already, unnamed.** A caller lends a span (a
  buffer) to a callee for the call; a function lends windows of its spans to
  its callees (`FTm::Lend`); a laid record is a typed view of a span; a
  function writes one span and reads others. These are borrows whose region
  is "this call", checked structurally, with no lifetime written.
- **Linearity for capabilities is a clause of the default setup's
  judgment**, over reflected code: each version of an `Io` is used once and
  never stored (effects-capabilities §5). The elaborator checks nothing about
  linearity.
- **In-place update is planned as a fact.** `Unique(p, k)`: the buffer an
  update consumes is not read again, found by an ownership judgment or a
  liveness check, used by the lowering to update in place instead of copying
  (facts-on-demand §7, `unique-fact`). Not built.
- **An arena exists** (`lib/native/runtime/arena.hthr`, rung2 §5): a bump
  allocator inside the span a function writes, windows `(base, count)`, a
  vector as a three-word header stored in the arena and referenced by its
  index `h`, growth by allocate-and-copy, `reset` to a mark. Its laws
  (`alloc_below`, `alloc_fresh`, `store_apart`, `grow_abs`) are proved. Its
  negative control is exactly the bug a lifetime prevents: a window kept past
  a `reset` meets the window handed out next (`stale_windows_meet`). Today
  that is a proof that fails, not a type error.
- **Principles that bind the design.** Principle 7: disciplines are
  libraries, decidable judgments over reflected code with one soundness
  theorem; the kernel never learns their words. Principle 13 (Minus,
  2026-11-24): a runtime check is a proof checked at another time; the
  proof takes primacy. A primitive states an obligation, a runtime check is
  a helper that discharges it, and a case the obligation rules out is absurd
  and emits no code.

## 2. Where lifetimes come from

Lifetimes are relevant data exactly where a reference is first-class: stored
in a structure, returned, kept past the call that made it. If references only
exist for the duration of a call, every lifetime is "this call" and needs no
name. That is the trade mutable value semantics makes (Hylo, Swift's law of
exclusivity, Koka's and Lean 4's reuse in place): give up stored references,
and lifetimes vanish from ordinary code. Minus has ruled the trade out
(stored references are required), so lifetimes, or regions, are data the
design must carry. The design's task is to make them cheap to write and
impossible to get wrong, not to avoid them.

## 3. Options weighed

- **A. Rust-style ownership in the language**: first-class references,
  lifetimes, a borrow checker. Full expressiveness, Rust translates directly.
  Lifetimes reach every signature, and in a dependently typed language a
  borrow interacts with types and proofs that mention the borrowed data.
- **B. Mutable value semantics as the default**: no first-class references;
  `mut self` and lent spans are borrows for one call, checked by a local
  exclusivity rule; in-place update from uniqueness the compiler infers.
  Fits what is built. **Rejected as the whole answer**: uniqueness is the
  compiler's private conclusion, which cannot be stated or relied on, so an
  edit that breaks it silently copies; and it has no stored references.
  **Kept from it**: the meaning stays pure.
- **C. Opt-in first-class references as a second `runtime fn` setup**: the
  roadmap's original `nh-ownership` plan. Superseded by §4: ownership is the
  default discipline, not an alternative.
- **D. Validity as a proof about a handle**: "handle `h` is valid in arena
  state `a`", carried across operations by laws. This is how the arena
  works today. It becomes the soundness argument of the checker in §4
  rather than lemmas each program cites.

## 4. The direction (decided 2026-11-24)

1. **Ownership is stated and known, and it is a guarantee.** A value the
   program owns uniquely, or holds by exclusive borrow, compiles to an
   in-place update, always. If the checker cannot establish what the program
   states, the program is refused with the reason, never silently copied.
   Copies are explicit (`clone`).

2. **Borrows are values: a type former is the primitive.** A shared borrow
   `Ref<r, T>` and an exclusive borrow `Mut<r, T>` (spellings illustrative),
   with `r` a region. Values of these types can be stored in records,
   returned and abstracted over; records take region parameters. A mode on a
   parameter (`&mut x: T`, the present `mut self`) is notation for a
   parameter of the borrow type with its region an implicit argument: one
   concept, two spellings. Dereferences and reborrows are deterministic
   coercions the elaborator inserts and can show, not guesses. "Magic"
   elaboration that decides on its own which positions are borrows is ruled
   out, as it hides the information the programmer wants stated.

   The distinction weighed: a *mode* is a property of a binding, not a
   value, so it cannot be stored, put in a list, returned as data or
   abstracted over generically; types stay the mathematical types and
   checking stays local. A *type former* makes the borrow a value, at the
   cost of distinguishing "a `T`" from "a borrow of a `T`" and of needing a
   meaning for a borrow as a value. Stored references force the type
   former; modes survive as its notation.

3. **The meaning stays pure; borrows are functional.** Lean: **backward
   functions** (Aeneas: Ho and Protzenko, "Aeneas: Rust verification by
   functional translation", ICFP 2022). An exclusive borrow means its
   current value, and its lender receives a pure function that rebuilds the
   whole from the borrow's final value when the borrow's region ends.
   `Mutated<T, R>` for `mut self` is the simplest case already. Fully
   functional, nothing new in the kernel (principle 7), and Aeneas handles
   borrows stored in structures. Alternative to weigh: **prophecies**
   (RustHorn, Creusot): `&mut T` means a pair of the current and the final
   value, the final one resolved when the borrow ends. Simpler statements,
   natural for stored borrows, but it needs a prophecy principle in the
   logic.

4. **The checker is a search for proofs, so it can be bolder than Rust's.**
   Its hard questions are proof obligations (principle 13):
   - *disjointness*: two exclusive borrows into one array at indices `bv_omega`
     proves distinct are fine, so `split_at_mut` is a theorem, not an unsafe
     primitive;
   - *outlives*: region constraints solved flow-sensitively (Polonius-style
     loans and origins), with no lexical scopes required;
   - where the search fails, the programmer supplies the proof, or chooses a
     runtime helper (§5) that discharges the same obligation dynamically.
     No `unsafe`.

5. **The checker is a library judgment; the surface is in the language.** The
   judgment runs over reflected code with one soundness theorem against the
   byte memory model (`lib/std/machine/memory.hthr`); the kernel never learns
   the words (principle 7). The syntax and the types are part of the
   language, so ownership is written, read and checked where code is
   written.

6. **Default Heather mostly does not care.** Ordinary functions are
   mathematics and never see regions or modes. In `runtime fn`s, inference
   fills what is not written; signatures show modes where the programmer
   wants intent stated. Most code writes nothing beyond what it writes today
   (`mut self`, `let mut`).

7. **Inference: inside a function first; across a module later.** Function-
   local inference, with signatures following elision rules, comes first.
   Whole-module inference is to be considered: inferred regions become part
   of a module's interface and are stored in its module image, and the
   cache's interface cutoff (`docs/infrastructure/module-interface-cutoff-design.md`)
   already handles "a dependency changed in a way an importer observed".

8. **Ownership becomes the default `runtime fn` discipline.** The roadmap's
   `nh-ownership` (a *second* setup beside the default) is reframed: the old
   default, which copies wherever it would update, is the degenerate case
   where everything is shared.

9. **Stored references and shared mutation are both in scope** and are
   designed together, even if built in stages.

## 5. Shared mutable structures

Every mutable access needs evidence that nothing else accesses the same
memory at the same time. A shared structure (a graph, a cache, an arena of
nodes referring to each other) obtains it in one of two ways, both
discharging the same obligation:

- **Statically, by permission tokens**: values with no runtime presence,
  consumed and returned by accesses ("I hold write permission to node 5"),
  composed by a separation algebra (`separation-algebra-ownership`). Prior
  art: Verus's `PointsTo` ghost permissions; Pony's reference capabilities
  (`iso`, `trn`, `ref`, `val`, `box`, `tag`) as a fixed lattice of them;
  separation logic generally.
- **At run time, by helpers**: reference counts (and reuse when the count is
  one, as Lean 4 and Koka do), borrow flags (`RefCell`), generational
  handles for arena slots (Vale), each a helper in principle 13's sense.

The arena's handles are the first customer: a window or vector header is a
borrow whose region ends at the `reset` that frees it, so a window used after
a reset becomes a type error instead of a failed proof.

## 6. Worked examples the design should handle

1. A vector pushed in place, owned by a local, and the same vector borrowed
   exclusively by a callee that pushes to it.
2. `split_at_mut`: two exclusive borrows of one array, disjoint by a proof.
3. A hash map's `get_mut` returning an exclusive borrow of a value, used,
   then the map used again.
4. A zero-copy tokenizer: tokens stored in a vector, each holding a shared
   borrow of a slice of the input, the vector outliving the loop that built
   it but not the input.
5. Arena handles: a vector header in the arena borrowed with the arena's
   region; `reset` ending that region; the stale window refused.
6. A graph with shared nodes and mutation, once by permission tokens and once
   by a runtime helper.
7. Today's code unchanged: `mut self` methods, lent spans, laid records,
   `Mutated`, and the word map's proofs, all reading as the new design's
   notation without edits beyond what the checker asks for.

## 7. Questions still open

1. **Backward functions or prophecies** for the meaning of an exclusive
   borrow (§4.3), including what a proof about a function that returns a
   stored borrow looks like in each.
2. **The region language.** Regions as ordinary implicit arguments of what
   type? Outlives as propositions? How region parameters on records interact
   with the record's fields, with `laid record` layouts and with dependent
   types that mention borrowed data.
3. **Elision and inference limits**: the function-local rules, what is
   inferred and what must be written, and what whole-module inference adds.
4. **The permission algebra** for shared mutation: which separation algebra,
   how tokens are passed without runtime cost, how they meet the runtime
   helpers.
5. **Two-phase borrows, reborrowing and moves out of borrows**: which of
   Rust's refinements are needed and which a proof-backed checker makes
   unnecessary.
6. **Interaction with the existing native layers**: spans lent per call,
   windows, laid records, the arena, `Unique`, and the effects capability
   (`Io`) linearity clause, which this design subsumes.
7. **Soundness**: the statement proved once against the byte memory model,
   and how it composes with each compiled function's certificate.

## 8. Prior art to read

Rust and RustBelt (Jung et al.); Polonius (loans and origins); Aeneas
(functional translation, backward functions); RustHorn and Creusot
(prophecies); Verus (ghost permissions); Hylo, formerly Val (mutable value
semantics); Swift's law of exclusivity; Koka and Lean 4 (Perceus, reuse when
unique); Pony (reference capabilities); Vale (generational references);
Cyclone (regions); Mezzo; Linear Haskell, Idris 2 (quantities) and Granule
(graded modalities), as the modes-on-binders family; Clean (uniqueness
types); Austral (linear types).

## 9. What the design session produces

The rest of this file, as a design note: the types and syntax; the meaning
(a translation to pure functions); the checker's judgment and the proof
obligations it raises; the soundness statement; the runtime helpers; the
inference; each worked example of §6 written out; the stages in which it is
built and what each stage's done-when is; and the decisions it needs from
Minus, each with a recommendation.

## 10. The direction (Minus and a design session, 2026-11-24)

Spellings are illustrative throughout. This section is the frame the work
packages of §12 build in; the worked examples of §6 written out in full, and
the soundness statement, are deliverables of those packages.

**What it changes of §4.** §4.1 (stated, guaranteed, a refusal and never a
silent copy), §4.4 to §4.9 stand. §4.2 changes: a region is named by what
is borrowed, not by a duration (§10.5). §4.3 changes: an exclusive borrow
means a path into its owner, of which a backward function is the case where
the path is static (§10.4); prophecies are not used. New: aliasing of
exclusive borrows is a fact that licenses optimisations, and the obligation
that carries soundness is validity (§10.3, §10.6).

### 10.1 Ownership is a licence

A `runtime fn` means a pure function, defined whether or not two of its
arguments share storage. Ownership never protects the meaning. It decides
which implementation of that meaning the compiler may choose: an update in
place and not a copy, a pointer and not a copied value, a read with no
check. So every construct has a default implementation that needs no fact
(copy, checked index, count), and a fact buys the cheap one (principle 13).

The guarantee of §4.1 is then one rule. Where the source states a
representation (a borrow, a move, an update of an owned value), a fact the
compiler cannot find is a refusal that prints the obligation. Where the
source states nothing, the compiler may still look for the fact as an
optimisation. One fact system (`docs/native/facts-on-demand-design.md`)
serves both; what differs is who asked.

A consequence: strictness is a policy on a function, not a second language.
A function that allows inserted copies and a function that refuses them have
the same meaning and the same certificate.

### 10.2 What the propositions are about

A pure value has no identity, so "these two do not alias" is not a
proposition about two values. Identity comes from three places:

- **Names.** Two locals are distinct storage by construction. This is the
  judgment over reflected code, as `Program::owned` is today
  (`lib/lang/facts/unique.hthr`).
- **Paths inside one owner.** `buf[0..k]` and `buf[k..n]` are apart because
  the ranges are: an ordinary proposition about indices, found by `omega` or
  `bv_omega`.
- **Keys into a store.** A handle is valid if the store has it: an ordinary
  proposition about the store's value and the key.

So once two things have a common owner, every obligation of this design is
an ordinary Heather proposition, and the fact machinery, a found proof
(`:= bv_omega`) and a user's theorem all discharge it.

### 10.3 Three kinds of access

| Access | Spelling | Means | Obligation that carries soundness |
|---|---|---|---|
| Owned | `x: T` | the value | the storage is reached through `x` only (`Unique`) |
| Frozen view | `&T` | the value | no store overlaps its footprint while it is live |
| Live path | `&mut T` | a path into its owner (§10.4) | the path is valid in the owner at each use (§10.6) |

A frozen view's meaning has cached the value, so a write under it must be
shown apart from it; the showing is a proposition, so writing element 5
while element 3 is frozen is accepted with a found proof. A live path is
read through its owner at each use, so two live paths that overlap are well
defined (the last store wins) and a pointer implementation agrees.

One qualification. Two `&mut` parameters of a function whose meaning is
stated the static way (each parameter a value of its own, §10.4) ask their
arguments to be apart, because that meaning gives each its own copy. Passing
overlapping places needs the callee to take paths under one owner.

### 10.4 The meaning: a borrow is a path

- A **frozen view** means the value, as in Aeneas. A token holding a slice
  of the input means a token holding bytes; a proof about the tokenizer
  never sees a region.
- A **live path** means a path: data that names a part of an owner, with a
  partial read and a partial write (a lens held as data, over
  `lib/std/machine/location.hthr` where it is total). Reading is
  `owner.get(p)`, writing is `owner := owner.set(p, v)`.
- A **region** is the lent owner. A region parameter of a function is an
  implicit, erased, linearly threaded argument whose meaning is the lent
  value; the function's meaning takes it and returns it. This is the
  mechanism `Io` already uses (`effects-capabilities-design.md` §5).

`Mutated<T, R>` and `mut self` are the case where the path is static and the
owner is the caller's place: the callee is handed the part and the caller
puts it back. Nothing built changes. A record of live paths means a bundle
of names for things passed alongside:

```heather
record Emitter(out: region) { sink: &mut{out} Vec<u8>, depth: Nat }
// Emitter::byte means (self, b, out) → out
```

This is also the program written with indices into a vector or a slot map
when lifetimes get hard elsewhere. Here that program is the meaning, and
facts recover the pointer.

**Built** (`ownership-paths`, `lib/std/machine/path.hthr`). A path is
`Path<S, V> { get: S → Option<V>, set: S → V → S }` with `PathLaws`, the
optional-lens laws: a write through a valid path is read back, writing back
what was read changes nothing, the second of two writes stays, and a write
through an invalid path changes nothing. So the partial write is total and
every law holds at every owner; validity is about the read alone. A
location is a path that always answers and a path that always answers is a
location, each with its laws carried across; paths compose (`then`), and
lawful locations compose to a lawful location. Two choices the note left
open, taken there:

- **A slice's value has its length in its type.** A window of a list is a
  `Path<List<A>, [A; n]>` (`list_path.hthr`): a write cannot change the
  shape, as a store through `&mut [T]` cannot, and the laws need no
  side condition on the value. A window must fit to be valid, the empty
  one too: `xs[5..5]` of four elements is not valid, as in Rust.
- **Apart is a fact about the meaning; spans decide it.** `Apart(p, q)` is
  the partial `Disjoint` (each write leaves what the other reads, the writes
  commute). The decider is over footprints: `PathIn(p, span)` says a path of
  a list reads and writes only at a `Span`'s indexes, every path composed
  after it lies there too, and `Span::apart` on two footprints gives
  `Apart` (sound; complete on spans, not on paths). Two fields of one
  element share a span and are apart by their own `Disjoint`
  (`Apart::under`), not by the decider.

The worked examples are theorems: `split_at_mut` (`split_apart`,
`split_rebuilds`, `split_reads`), holding element `i` while storing `j ≠ i`
(`hold_while_store`), and the word map's slot for a key
(`word_map_paths.hthr`), lawful at every table and, under `WordMapInv`,
the read of `get` and the write of `insert` of a stored key.

**Joined** (second wave, `ownership-library-join`). Paths, keys and the
separation algebra are one vocabulary:

- *A key is a path step* (`lib/std/data/store_path.hthr`):
  `Store::key_path(k) : Path<Store<V>, V>`, the store's partial read and its
  `put`, lawful at every store, valid exactly where `Store::Valid` holds.
  Two different keys are apart, of different slots or of one slot at two
  generations (`keys_apart`), decided by `Key::apart`, sound and complete.
  A key then a path into its value (`key_then`) is valid where the key is
  and the inner path is valid in what it reads; under two keys any paths
  are apart (`inside_apart`, from `Apart::then_both`: parts of parts
  apart). Keys are the second kind of footprint (`KeyIn`), decided by key
  inequality as spans decide positions.
- *A vector's entry is the list's element read in a vector*
  (`lib/std/machine/vector_path.hthr`): a list path that keeps the length
  is a vector path through its entries (`Path::in_vector`), so the step
  `[A; n] → A` is `elem(i)` again (`Path::entry`). A path in `s` under the
  window of `n` from `lo` lies in `Span(lo + s.base, s.len)`
  (`PathIn::under_window`): an element of a window at its own span, a window
  of a window where the one window from `lo + lo2` lies.
- *A field of a laid record is a path with a byte span*
  (`lib/std/machine/part_path.hthr`): a window of the codec's size, then
  the codec read off its bytes (`Stored::codec_path`). Lawful where the
  codec is exact (one with padding writes its padding back as its own, not
  as it was); its footprint needs no exactness, so two fields are decided
  apart from the layout (`Part::paths_apart`), at an open base with the
  verdict still evaluated (`paths_apart_at`), at open codecs from the
  layout's own facts (`pair_apart`). §13.7 is this.
- *An element of a vector held by handle is one composed path*
  (`lib/native/runtime/arena_handle_paths.hthr`): `Heap::window_path(w)`,
  the window's words behind the check that its key still names it, then
  `Path::entry`. One validity statement (`elem_valid`, `elem_valid_parts`:
  the handle valid and the index below its count), a footprint
  (`Span(base + i, 1)` behind the key, `elem_same`), and two elements of
  valid windows of different keys apart at every heap
  (`valid_elems_apart`). The handle's own `read` and `store` are the path's
  read and write (`read_is_elem`, `store_is_elem`), and a vector's element
  reads its item and what `Arena::elem_path` reads (`vec_elem_items`,
  `vec_elem_agrees`): the two name one word, the handle's path carrying
  the key and `elem_path` the window the header points at.

Two choices taken there. *A path behind a check* (`Path::guard`) is how a
handle's validity enters a path: the check reads only erased state (the
claims), which no write of words changes, so the guard keeps the laws and
`Apart`. *Spellings are a relation, not an equation* (`PathSame`): a
composition regrouped, or a step written through a guard, is the same
path read and written alike at every owner, and laws, validity, `Apart`
and footprints carry across it, since paths are records of functions and
the kernel has no function extensionality.

### 10.5 Regions are named by what is borrowed

`&{self} V` says the result borrows from `self`; a set of places is a region
(`&{a, b} T`), which is Polonius's origin. Elision keeps the common cases
unwritten. A record's field may borrow from an earlier field, which a
dependent record states directly:

```heather
record Lexed { input: Bytes, tokens: Vec<Token(input)> }
```

A closure's type carries its capture set the same way (§10.9).

### 10.6 Validity is the obligation; aliasing is a fact

What is unsound is using a path whose storage moved or changed shape: a push
that reallocates, an enum that changes variant, an arena reset. So:

- `Valid(owner, path)` is the obligation at each use of a path.
- Every operation on an owner publishes which paths it keeps (a store keeps
  all; a push with spare capacity keeps all; a growing push keeps none).
- `Apart(p, q)` is a fact: it lets the compiler keep a read across a store,
  hand two callees their parts at once, and run iterations in parallel. For
  a frozen view it is the obligation of §10.3.

Capacity is therefore a fact about a home, not a field of the value.

**What the vector showed** (`ownership-paths`, `arena_paths.hthr`). A
push keeps every path into the vector's *value*: element `i` of the list is
element `i` after any push, growing or not. What a growing push breaks is a
path that names the home, which is what a pointer is. So a live path into
an owner whose storage can move names where it was taken: the arena
vector's element is `elem_path(h, b, i)`, the header at `h`, the window at
`b`, element `i`, valid while the header still points at `b`. Validity is
stated over the home (the arena), and the vector's meaning is unchanged by
both pushes (`push_in_abs`, `grow_abs`): a push with room keeps the path
(`push_in_keeps`), growing does not (`grow_loses`, `grow_not_keeps`).
"What an operation keeps" is a relation between two owners,
`p.Keeps(before, after)`, so an operation with a precondition (room in the
window) states it under that precondition.

**Producers of `Valid`**, cheapest first, in the order facts already take:
a region discipline over the reflected code (decidable, the common case); a
proof the programmer supplies or a tactic finds; a runtime helper (a
generation check, a count) that decides the same proposition; and a copy,
which makes any view valid by making it owned.

### 10.7 Stores and keys: shared mutation

A shared structure is a store and keys: the pure meaning of a graph is a
finite map and its handles. Keys copy freely; access needs the store, held
`mut`. Fresh identity needs a supply to come from, so allocation threads the
store; that is forced by purity, and the implicit region token of §10.4 is
what keeps it out of the source.

Validity of a key is a proposition about the store and the key. The arena
is the first customer: a window used after the reset that freed it has no
proof of validity, so `stale_windows_meet` becomes a refused obligation. A
generation kept as erased state is the static form, and the same generation
kept at run time and compared is the helper; a reference count is the other
helper. Permission tokens of §5 are the store itself, split where paths are
apart (`separation-algebra-ownership`, built with fractions in mind).

**Built (2026-11-24, `ownership-stores-and-keys`).** What the build
settled or changed against the text above:

- *The store* (`lib/std/data/store.hthr`) is a list of slots, each
  `Live(gen, value)` or `Free(gen)`; a key is a slot and a generation.
  `Valid(s, k)` is `s.get(k).is_some()` being `True`: the partial read
  answers, the form `ownership-paths` states a path's validity in. `read`
  and `write` take it (found by `known`); `alloc` takes the first free slot
  or a new one, `free` moves the slot's generation past the key's, and a
  key behind its slot's generation is `Stale`, which no operation undoes
  (`stale_after_reuse`). `check`, the generation compare, is proved to
  decide `Valid` (`check_decides`), and `checked` is the access that tests
  it, a `When` whose `Present` carries the proof the static access takes.
  `retain` frees every value a test refuses: an arena's reset read as keys.
- *The generation is the slot's, not the store's.* One counter for the whole
  store would not do for the arena: a reset frees only the windows above
  its mark, and those below keep their keys across it. A generation per
  slot is exact for both.
- *The arena* (`lib/native/runtime/arena_handles.hthr`): a `Heap` is the
  laid `Arena` and, beside it, erased claims (a `Store<Claim>`) with the
  invariant tying them to it. A window is its two words and a key, valid
  where the key's read answers the window it says. Two valid windows of
  different keys are apart, so `store_apart` over handles takes no `Apart`
  premise: aliasing became a fact read off validity, as §10.6 says. A
  vector is a header window and a data window; `grow` claims the new data
  window and releases the old. The arena's own functions and laws are
  untouched, and the handle laws are read through them (`Arena::store_apart`,
  `grow_abs`).
- *The stale window* is a `¬` theorem (`stale_window_invalid`) and a read
  or store through it is refused naming `Heap::Valid`
  (`lib/_tests/native/runtime/arena_handles_tests.hthr`); `stale_windows_meet`
  stands beside it, the same two windows meeting as words.
- *§6 example 6* is `lib/std/data/store_graph.hthr`: the shared write proved
  at an open store, and the checked write proved equal to it wherever the
  key is valid and a no-op where it is not.
- *The arena's checked route is not O(1).* The claims are history, so
  keeping them at run time is a table, not a word compare. A run-time
  generation for the arena wants a word per window in the heap (Vale's
  layout), which changes `arena.hthr`'s layout: left to
  `arena-runtime-generation`.

**Joined with the separation algebra** (second wave,
`ownership-library-join`): a permission token is a holding, finitely many
footprints at shares (`Held`, `lib/std/data/set/held.hthr`), whose
validity is decided by evaluation. A path's holder holds its footprint
whole, a frozen view at a share; an owned path's holding composing with
any positive holding of another makes the two paths `Apart`
(`Held::apart_of_valid`), and a key's footprint is its slot
(`Held::keys_apart_of_valid`). The frame theorems with a holding as the
frame are `lib/std/machine/access_frame.hthr`: at a path
(`Held::path_keeps`, a frozen view's predicate kept by every write of a
holder it composes with, `Held::view_kept`) and against memory
(`Access::store_keeps`). Composition is sound for `Apart`, not complete:
footprints over-approximate, and two views compose while overlapping.

A home is a root and a path. A local's home is not observable until it is
borrowed, and two owned values never share one. Pointer equality is
equality of paths. An address as a number is machine-level code against the
explicit memory model, with its provenance questions, and is deferred.

### 10.8 Copy, Clone, drop, and erased uses

- **A use in an erased position is a use of the value, not the storage.**
  The judgment runs over reflected code, and reflection drops proofs, types
  and specifications, so a proof may mention a buffer after it moved or
  while it is lent, and never needs a clone. A binding used only in erased
  positions has no storage.
- **`Clone`** is an operation with no law. **An extension** carries
  `clone(x) = x`. Its consumers ask for it as a fact: a proof that rewrites
  a clone away, the compiler inserting one where the policy allows, the
  optimizer deleting one when the original is dead. It is derived for a type
  described by its layout. A type whose meaning has representation slack
  keeps plain `Clone`, or states its law up to its own equivalence.
- **`Copy`** is a fact about a representation: words, records of copyable
  parts, frozen views and keys are copyable; owned buffers, live paths and
  stores are not.
- **Drop** means nothing, so values are affine by default and a leak is
  never unsound. A capability that must not be dropped says so in its type.

**Built (2026-11-25, `ownership-copy-clone`).** What the build settled:

- *The classes* (`lib/std/core/clone.hthr`) are the relation-indexed chain
  of `algebra_rel`: `Clone<A>` is the operation alone, `CloneRel<A>(same)`
  adds `clone(x) ≈ x` at the type's own equivalence, and `ExactClone<A>` is
  `CloneRel` at `RelId`, so its law is `clone(x) = x` by unfolding
  (`ExactClone::clone_eq`, which `simp_only` reads at an open carrier and
  a concrete one). The note's "exact clone" is kept as the name: `Exact` is
  already the library's word for "loses nothing" (`Stored::Exact`), and an
  adjective on the parent is how a chain member is spelled (`CommMonoid`).
  Drop has no class, said where the classes are declared.
- *`Copy` is indexed by a representation*, `Copy<A>(rep)`
  (`lib/lang/facts/copy.hthr`): an `rt` code at a table (`Rep::Code`), a
  `Stored` codec (`Rep::Bytes`), or nothing (`Rep::Absent`, erased data).
  Over codes the statement is `Ty::Copy` and the judgment's question
  `Ty::copies`, proved to reflect it; an instance at a code is the
  decider's verdict and gives it back (`Copy::of_code`,
  `Copy::code_copies`), so the two askers have one answer. The decider
  agrees with `Ty::holds_bytes` at every code that names no table entry,
  never contradicts its "may hold" at a record, and at an enum agrees where
  the payload's slots copy (an enum with a buffer slot is where
  `holds_bytes` is the wrong one: `holds-bytes-enum-payload`).
- *Every codec copies* (`Stored::copies`: a copy of a value's bytes reads
  the value), and the negative control is that **no codec holds an
  unbounded type** (`Stored::unbounded`, by pigeonhole over the codec's
  bytes): not a byte list, not a store (`Store::no_codec`,
  `lib/std/data/store_copy.hthr`). A key copies at its code, a record of two
  counts. A `Count` copies though `Nat` is unbounded, because its code
  holds only what fits a word: the code's meaning, not the codec's.
- *Copy derives the exact clone*: a representation read back is the value
  (`Rep::copy_eq`), so `Copy::exact_clone` builds `ExactClone` from a
  copyable representation, compiled as the copy of its words. Words, `Bool`,
  counts, keys and `Erased<A>` whatever `A` are derived so; a laid record
  by `generate laid_copy("T")` beside it and two `instance` lines, because a
  generator cannot yet register an instance at a named carrier
  (`generated-instance-at-named-carrier`; the join into `laid` is
  `laid-publishes-copy`). An exact clone does not need `Copy`: a list's
  and a store's clones are exact though neither copies.
- *Slack*: the word map registers `CloneRel<WordMap>(WordMap::SameRows)`, a
  clone that copies only the live rows and zeroes the rest, equal under
  `WordMap::abs` and provably not exact
  (`lib/native/runtime/word_map_clone.hthr`).

### 10.9 Closures, and what concurrency asks now

A closure is a record of its captures and code, so it is the stored-borrow
case, and its type carries its capture set. One that captures a live path of
`out` means `(a, out) → (b, out)`. The three receiver modes that exist
replace three function traits. The capture set of live paths is the
closure's footprint, the same thing `effects-locality-design.md` calls a
footprint fact.

Concurrency has no model yet. Deterministic parallelism needs none: the
meaning of a parallel map is the sequential one, licensed by the iterations'
footprints being apart. What that asks of the design today is only that
footprints are values and tokens can be split.

### 10.10 Inference, and the policy on copies

Inference is untrusted search (principle 3): it writes the annotated program
(regions, where each loan ends, where a copy goes), and a small checker of
annotations carries the soundness theorem. Written annotations are demands
checked against it. Inferred ones belong to a module's interface, so a
change shows as an interface change.

A `runtime fn` refuses an implied copy and names `clone`. A relaxed marker
on a function lets the compiler insert the copy and report it.

## 11. What the tree has, against this design

Read off the code on 2026-11-24.

| Piece | State |
|---|---|
| Updates in place | Only the one written span of an `FTm` computation, a laid record's fields and `Bytes(n)`, justified structurally: the span is never a value (`rt_file.hthr`). |
| Buffers as values | `Op::Get`, `Op::Set` are refused by the default judgment and not lowered. |
| `Unique`, `Owned`, `WritePlan` | Built over `rt` (`lib/lang/facts/`); no lowering consumes them (`unique-fact`). |
| Borrows for a call | `FTm::Lend` and `FView`; FunctionIR `View`; machine `Loan`, `Viewed`. Views of one buffer, any of them written (`split_at_mut`), are lowered where the path knows them apart, by value or a comparison on the path; `ViewsApart` is the fact that licenses the call (`views-of-one-buffer-apart`). In a `runtime fn`, a window to read of the written span beside the written window, apart by the same check (`rt-window-of-the-written-span`, 2026-11-25). |
| Several written spans | In FunctionIR and the machine, built (several written views, of one buffer or several); in `rt`'s meaning, not built (`rung2-spans-design.md` §6): a callee that writes two spans has no `FTm` meaning, so a `runtime fn` cannot lend two written windows (`rt-several-written-spans`). |
| Linearity | The reflector's refusals for the world and the span (`rt_reflect.hthr`). No judgment over `FTm`, `ETm` or held code: only pure `Fun` goes through `Setup`. |
| Typed references | None in compiled code. A window is two words, a vector handle a `u64`, laid records nest by value. In the meaning, a window and a vector are handles with keys into erased claims (`arena_handles.hthr`, §10.7 "Built"). |
| Lenses | `Location`, `LocationLaws`, `Disjoint` (`lib/std/machine/location.hthr`), total only; `Part` and `Stored` for laid records. |
| Footprints | `Span`, `SpanSet` with deciders (`span_set.hthr`); the separation algebra over them, fractions, an access map and the store frame theorem (`docs/library/separation-algebra-design.md`, built 2026-11-24 in the first wave). |
| `mut` in the surface | A parser desugaring; the AST's `Param` has no mode, and a `mut self` method is known by its `Mutated` result type alone. `&` is an infix token only. **Since built** (`ownership-parameter-modes`, `sequencing-surface-design.md` §24): `Param::mode`, `x: &T` and `x: &mut T` on any parameter, `&mut place` at a call, the modes readable by a generator (`tactic::modes`). |
| Erased parameters | A parameter whose type is a proposition (`∥P∥`) or `Erased<A>` is no word of the code wherever it stands, in a function of a laid record and one of a `Bytes(n)`; a call's erased arguments are dropped at any position. The arena's `read` and `store` are `runtime fn`s keeping their found proofs (`runtime-erased-parameters`, §13 item 8). A plain function of words, a span writer, and a compiled caller of a function that takes one were refused by name; **since built** (`runtime-erased-pure-shadow`, §13 item 8), but for a laid record's function calling one of the record that takes one. |
| `Copy`, `Clone` | No class. **Since built** (`ownership-copy-clone`, §10.8): `Clone`, `CloneRel`, `ExactClone`; `Copy<A>(rep)` over codes, codecs and erased data, with the decider on `Ty`. |

In flux, and to be worked around rather than through: the loop combinator's
rounds (`loops-on-one-combinator`), and one control language for `FTm` and
`ETm` (`docs/native/dogfooding-plan.md` §5.3b).

## 12. Work packages

Each is an issue; its done-when is in the issue. The first wave has no
package waiting on another.

**First wave.**

| Package | Issue | Where |
|---|---|---|
| Paths and validity: the meaning layer of §10.4 and §10.6, with `split_at_mut` and the word map's slot as theorems | `ownership-paths` | library, pure |
| Stores, keys and generations, with the arena's windows as typed handles and the stale window refused | `ownership-stores-and-keys` | library, pure |
| The separation algebra, with fractions | `separation-algebra-ownership` | library, pure |
| Modes in the surface: a mode on a parameter the AST keeps, `&T` and `&mut T` on any parameter, several per function | `ownership-parameter-modes` | parser, elaborator |
| Views of one buffer known apart, then two written views: `split_at_mut` through the machine | `views-of-one-buffer-apart` | FunctionIR, x86 views |
| Proof and erased parameters of a laid-record `runtime fn`, so an access carries its obligation into compiled code | `runtime-erased-parameters` | reflector, generator |

**The first wave is built** (2026-11-24, merged on one branch and its suite
green). What it showed missing between it and the discipline working end to
end: a compiled function cannot call one that takes a proof
(`runtime-erased-pure-shadow`); a `runtime fn` cannot say `split_at_mut`,
since the reflector refuses a window of the span a call writes though the
lowering takes it (`rt-window-of-the-written-span`); and nothing reads the
modes the surface records.

**Second wave.** No package waits on another.

| Package | Issue | Where |
|---|---|---|
| A plain function and a span writer taking an erased parameter, compiled from the reflection written out, so a compiled caller passes a found proof | `runtime-erased-pure-shadow` | generator, reflector |
| A window to read, and a second to write, of the span a call writes: `split_at_mut` said in a `runtime fn` | `rt-window-of-the-written-span` | reflector, `FTm` |
| `Copy`, `Clone` and the exact-clone extension, derived from a layout | `ownership-copy-clone` | library |
| The first wave's libraries joined: a key as a path step, footprints for fields, the algebra at paths | `ownership-library-join` | library, pure |

*`ownership-library-join` is built* (2026-11-25): §10.4 "Joined", §10.7
"Joined with the separation algebra", `docs/library/separation-algebra-design.md`
§7. What the soundness round can now state: "this path's holder owns it"
as `Held::own` of its footprint with `Held::own_excludes`, "this view is
frozen" as `Held::at` with `Held::view_kept`, each with its frame theorem.

**Third wave**, designed against what the second produces:

- **The judgment**: access kinds, moves and regions over reflected code,
  reading the modes (`tactic::modes`), raising `Valid` and `Apart` as fact
  requests, as a checker of annotations with inference beside it. It
  replaces the reflector's linearity refusals and `Program::owned`.
- **Homes for owned values and the in-place lowering**: what `unique-fact`
  leaves, with a vector owned by a local living in the arena.
- **Stored borrows**: place-named regions on records, frozen views in a
  vector (the tokenizer), and a view's layout as an address and a count,
  which needs a reference-typed field in `laid` and `datarepr`.
- **Soundness**: the invariant that every live name and path reads its
  value, stated once against the memory model through the separation
  algebra, composed with a function's certificate.

**Later.** Closures and capture sets; the parallel licence; reference counts
as a helper; addresses as numbers.

## 13. Still open

1. The spelling of regions and modes (§10.5), and elision's rules.
   *Informed by `ownership-parameter-modes` (2026-11-24):* `x: &T` and
   `x: &mut T` on a parameter and `&mut place` at a call are built
   (`sequencing-surface-design.md` §24), with `self x: &mut T` a second
   spelling of `mut self x: T`. A parameter's mode is written in front of
   its type, which leaves `&{self} V` free for a region in the type
   position later. Several `&mut` parameters return their values after as
   `Mutated<A, Mutated<B, R>>` in parameter order, so one is exactly `mut
   self`'s shape. Alternatives met and not taken: a mode before the name
   (`&mut x: T`, the spelling §4.2 floated), which reads as a pattern and
   collides with `mut x` at the head of a binder; and a record of the
   values after per signature, which a generator would have to name. At a
   call, nothing marks a frozen view (`f(&a)`): it means the value.
   *Extended by `parameter-modes-residue` (2026-11-25,
   `sequencing-surface-design.md` §24.4–§24.6):* a `mut self` receiver
   beside other `&mut` parameters is written first among them, so the one
   rule (parameter order, answer innermost) puts it outermost, where a
   method call rebinds it from; and whether a dot call rebinds its receiver
   is the receiver's written mode, not a `Mutated` result (a plain `self`
   answering `Mutated` answers that record). A call lending places may
   stand wherever its statement surely runs it, which runs it first; a
   place so lent is read nowhere else in the expression. `f(&a)` stays
   unbuilt: as notation it should be held to a `&` parameter on every
   route an argument meets its parameter, and it carries nothing until a
   view's region is named.
2. Whether `Ref` and `Mut` are transparent to the kernel (a frozen view
   unfolds to its type, the region a phantom the judgment reads) or opaque
   with coercions. Lean: transparent, so ordinary functions take a view with
   no coercion. *As built (2026-11-24):* a parameter's mode is fully
   transparent, recorded beside the type and not in it, so the judgment
   reads it from the declaration (`tactic::modes`), never from a type.
3. How a frozen view carries its path when pointer equality on it is asked.
4. Erased state that a `mut self` method changes (an arena's generation):
   an erased field of the receiver, or a parameter of its type that the
   method's result may change. **Settled for the arena (2026-11-24): an
   erased field beside the laid record** (`Heap { arena, claims, ok }`,
   `arena_handles.hthr`). A `mut self` method answers `Mutated<Self, R>`,
   whose `after` has the receiver's own type, so a parameter the method
   changes cannot be said without a Σ in every result; and the claims are
   history (which allocation a window came from), which no function of the
   arena's words recovers, so they cannot be a parameter computed from it.
   The laid record stays as compiled; the erased fields are what proofs
   read. *Built (2026-11-25, `runtime-record-erased-fields`):* a field is
   erased by the recognition a parameter has, so data is wrapped (`claims:
   Erased<Store<Claim>>`, a window's `key: Erased<Key>`) and a proposition
   is not (`ok: HeapInv(…)`; the test reads propositions by their form as
   well as by irrelevance, so an equation and a record of facts count). A
   `runtime fn` of such a record is compiled as its laid field's function,
   a record parameter of words and erased fields as its words, and its
   `runs_held` takes the records whole and holds at every value of their
   erased fields (`docs/native/runtime-fn-setups-design.md` §16.24).
   `Heap::read`, `store` and `reset` compile; an answer carrying an erased
   field (`alloc`'s window) and a compiled caller of them do not yet
   (`runtime-erased-field-answers`, `runtime-erased-field-callers`).
5. The shape of the checker's annotations, and which of them a module's
   interface keeps.
6. The milestone's done-when (`docs/roadmap.md`, `nh-ownership`), to restate
   once the first wave has shown what holds.
7. Footprints beyond a list's indexes: a laid record's `Part` already
   carries a byte offset and size with read and frame laws
   (`lib/std/machine/part.hthr`) that are `PathIn`'s over bytes, so a
   field's path could be decided apart by its byte span. Not joined yet
   (`ownership-paths-footprints`).
   **Joined (2026-11-25, `ownership-library-join`):** `Part::path`, a
   window then the codec, in `Span(offset + at, size)`
   (`lib/std/machine/part_path.hthr`); elements of windows at their own
   span (`PathIn::under_window`); keys as a footprint (`KeyIn`).
8. **Decided (2026-11-24, `runtime-erased-parameters`): erased data is a
   type, `Erased<A>`** (`lib/std/core/erased.hthr`, a record of one field),
   not a mark on the binder. A type needs no parser (which
   `ownership-parameter-modes` is changing), reaches every shape of
   `runtime fn` through the one place the reflector reads a parameter's
   type, and travels with the value into callers, records and theorems,
   where `g.value` is an ordinary field. A proof needs no wrapper: a
   parameter is a proof when its type is definitionally irrelevant (two
   locals of it convert, the kernel's own test), which is what makes its
   pin hold at every proof. What is erased reaches compiled code as this:
   the reflector binds the parameter to no variable (a use of it as data is
   refused by name), and every theorem the generator publishes takes it
   where the function does and holds at every value of it. *Built for every
   shape but loops (2026-11-25, `runtime-erased-pure-shadow`):* a plain
   function of words and a span writer that take one are compiled from
   their reflection written out, a closed function of the code's words
   (`f::words`, or `f::bytes` over a span), and a caller's table lists
   that, so a compiled caller passes a found proof and its code has no
   trace of it. What is stated of `f` (`f::reflects`, `f::agrees`,
   `f::runs_over`) takes a local for each erased parameter where `f` does.
   The shadow tried first (the reflection's *meaning* as the compiled
   function) compared two meanings at two worlds, in its pin and in
   linking; a written-out term has no world in it, so neither comparison
   arises (`docs/native/runtime-fn-setups-design.md` §16.22). A function
   of a laid record calling one of the record that takes an erased
   parameter compiles too (2026-11-25, `runtime-record-calls-erased`): the
   callee is written out over its record (`T::n::words`), which the
   caller's mark names, so the arena's window `read` and `store` have
   compiled callers (§16.23). When the
   binder mode of
   `ownership-parameter-modes` lands, an erased mode can lower to this type,
   so the generator keeps one route. Item 4 (an arena's generation changed
   by a `mut self` method) is then an `Erased` field of the receiver or a
   parameter of its type; neither is built yet.

## 14. Decisions of 2026-11-25, and the design in progress

Minus, in discussion after the second wave. These bind the judgment's design,
which is being worked out before anything more of it is built.

1. **Proofs are passed down and used; they are not compiled.** Today the
   function compiler learns that two views are apart by re-reading the code
   (`File.known`: constants, comparisons, the test of the arm taken;
   `views_apart`), and a theorem proved once turns that answer into a
   proposition. A found proof in the source reaches nothing below
   reflection: every span read and store compiles with a comparison of the
   index against the length even where the source proves the index inside.
   The direction: a path's known facts are a context of hypotheses; `if a <=
   b` adds one in its arm; a site that needs a fact carries "under this
   path's hypotheses, P of the values"; today's lookup is one prover of it,
   `omega` and a cited theorem are others, and a runtime check is an `if`
   that adds the hypothesis. Reflection keeps an erased proof argument,
   closed over the locals and hypotheses in scope, beside the code as the
   site's fact, and each lowering carries site facts across by its agreement
   theorem. A check the compiler makes of the code produces such a proof or
   uses one in context.
2. **One language, not four.** `Tm`, `FTm` (one written span), `ETm` (the
   world) and `PTm`, with the held and `Bytes(n)` meanings, are one thing,
   so the language's redesign and the ownership design are one project. No
   more iterative extension of the four (`rt-several-written-spans` is
   answered by the redesign, not by a patch). The first reading here, "a
   computation that threads a row of resources", is superseded by item 12:
   there is no row and no second kind of variable.
3. **A resource is abstract**: anything with a threaded value. Bytes with a
   typed view are one representation; the world and an erased token are
   others.
4. **Every obligation is a site fact** (lean: yes): bounds, validity,
   apartness, dead after this use. Refusal or an inserted check is policy.
5. **Regions are written in signatures and record declarations and inferred
   as annotations in bodies** (lean, not committed; custom syntax is open if
   it reads better).
6. **The compiler inserts a copy where policy allows, and a check only where
   it cannot change the meaning.** A check whose failure the meaning does
   not define is never inserted: an access takes its proof, and a method
   that can fail (`get` answering an option) has the check in its
   definition. Checks are expected to be rare and written.
7. **The world is a resource like any other** (representation: the system),
   beside an arena (bytes) and a region's token (nothing). One row; the
   separate effects language goes.
8. **A local borrow is not a construct of its own**, unless a benefit of
   making it one turns up. The proposal on the table: a function's frame is
   a resource, and a local borrow is a path into it, so it is the stored
   borrow's case with the frame as owner. How a path or a `&mut` parameter
   is held (an address, or the value passed in and handed back, as
   `Mutated` does today for a word) is a choice of representation.
9. **The old pipeline is not touched.** The one language is built beside
   the four with site facts native to it, the customers (the arena, the word
   map, the linked lexer and hash) are ported, and the four are deleted. No
   new package extends the old generator, reflector or term languages.
10. **The back half is kept**: FunctionIR and the x86 lowering, extended so
    a load or a store is accepted under a fact and not only under a
    comparison on the path.
11. **A region is the name of what a path was taken from** (lean: yes);
    validity is an obligation with the region discipline as its fast
    prover, not a typing rule.
12. **No split between values and resources in the reflected language**
    (Minus: "the same thing with different behaviour"). The reflected form
    is the function's own body in A-normal form, pure, one kind of
    variable. What differs is a property of a type's representation: how a
    value is held (words, bytes at a home, nothing, the system), whether it
    can be duplicated (freely, by an operation, never), and which of its
    operations may build their result in an argument's home. Where a home is
    reused is a plan beside the code, an annotation an untrusted planner
    writes; its licence is that the planned run agrees with the meaning,
    proved by the liveness check, by a "keeps" proof, or refused. Homes and
    stores as a second kind of thing appear only in the back half, which
    already has them (FunctionIR's values and buffers).
13. **Sharing and placement are two levels, and ownership speaks only of the
    first** (Minus: why would high-level code think of the registers it is
    put into?). Item 12's "plan" mixed them. *Sharing* is which values are
    one object: an operation's result is its argument updated, a value is a
    view of part of another, a call lends, moves or copies. It has no
    registers, addresses or frame slots in it; it is what modes state, what
    a copy costs, and what a module's interface records. *Placement* is
    where an object or a word physically lives and how it crosses a call on
    this machine; it is the back half's, planned and checked there as
    register placement already is. Between them stands a program over
    objects that have identity and no location, which is what FunctionIR's
    numbered buffers are. A type's sharing class (plain data, an object with
    a clone, an object that cannot be duplicated) belongs to the first
    level; its layout to the second. In a strict function sharing is
    determined by the source: share everywhere, copy only at a written
    `clone`, refuse where sharing has no licence.
14. **`&mut T` is exclusive: it means the value, taken from its place and
    written back to it (eagerly, §15.2), with an erased slot that says where
    it goes back and travels with the borrow.** This revises §10.3 and §10.4:
    an exclusive borrow is not a path read through its owner, and two
    overlapping `&mut`s are not accepted. `swap(&mut v[i], &mut v[j])` asks
    `i ≠ j` (Minus: expected; you do have to know that). Mutation that
    tolerates aliasing is keys into a store, with access an operation on the
    store; §10.3's "live path" row describes those.
15. **The obligation is that a name still reads its value at each use.**
    It is proved by a checker over place states (§15.3), not by share
    accounting: the separation algebra is not in the judgment, and its home
    is the theorem that live objects get disjoint memory (§15.4). A
    read-only view holds nothing and is licensed by its region being frozen
    (§15.3 has the rule and its precision).
16. **An unannotated parameter's access is determined by its uses**,
    recorded in the module's interface; a written mode is a demand checked
    against it. "Least" is not the rule: the accesses that check are not
    closed downward (§15.3 has the rule that is unique).
17. **Old code is not a constraint.** The levels and the decisions above
    stay; FunctionIR's upper part, the library's `Held`, `Path` and `Keeps`,
    and the stores may be reshaped or replaced where the design wants it
    (Minus: we own this repo and can write something truly beautiful). Item
    10's "kept" means the lower back half's proved work is not thrown away
    without cause.


18. **Ownership of the feature** (Minus, 2026-11-25): the coordinating
    session owns this feature's design and its building, and brings back
    results and real forks. The charge: make it elegant, and do not slide
    into the feature by iterative extension, "because that way lies bugs
    and poor design"; big dramatic moves are feasible. A thing stated in
    many places is a sign it wants consolidating (the call contract over
    buffers, stated in about ninety places, is the first such: §16).

## 15. The design as it stands (2026-11-25)

One place to read the design after §14's decisions and two rounds of
adversarial review. Where this section and §10 differ, this section holds:
§10.3's "live path" row and §10.4's "a borrow is a path" describe keys into
a store and level 2's references, not `&mut`; §10.7's permission tokens are
not part of the judgment. Nothing here is built. §15.6 is the experiment
that tests it first.

### 15.1 Three levels

| Level | What it has | Whose decisions |
|---|---|---|
| 1. Pure code | The function's own body in A-normal form; one kind of variable; no identity | the source |
| 2. Objects | Blocks with identity and no location; references into them; `new` and `dead` | sharing: derived from the source in a strict function |
| 3. Bytes and below | Layout, where a block lives, registers, addresses (FunctionIR, then x86) | placement: planned and checked |

A type has a sharing class for level 2 (plain data, an object, an object
that may not be dropped or duplicated) and a layout for level 3.

### 15.2 What the source's ownership words mean (level 1)

- `&{ρ} T` means `T`. The region `ρ` is a finite set of places (a root and
  steps over atoms), phantom: a `region` parameter, never a value index.
- `x: &mut T` as a parameter means `T` in and `Mutated` out.
- A `&mut{o} T` stored in data means the value and an erased slot, the path
  it returns to. Where its owner is not in scope (a callee that consumes a
  collection of them) the function takes an erased in-out owner `o`.
- **Write-back is eager**: after each statement that may change a write
  view `x` of place `π`, the meaning has `π := x`. No point of death enters
  the meaning, so the elaborator computes no liveness. That every later
  placement of the write-back gives the same meaning is three facts the
  library has (`PathLaws.set_set`, `Apart.writes_commute`,
  `Apart.right_after_left`).
- Mutation that tolerates aliasing is a key into a store; access is an
  operation on the store and owes `Valid`.

### 15.3 The checker

An annotation (untrusted, inferred): each object binder is `own` or a view
of a place, to read or to write; each site lists the bindings that die
there; each signature has modes, regions, and whether a result is fresh, is
one of its parameters, or is a view of places of its parameters (§15.8).

The checker is one forward pass over the body with a state per place:
`whole`, `frozen(viewers)`, `out(viewer)` or `gone`.

- A read needs no overlapping place `out` or `gone`.
- A write or a take needs every overlapping place `whole`; a take leaves
  `gone`.
- A view to read adds a viewer; a view to write turns `whole` to `out`.
  The viewer of an `out` place may read and write it.
- A death removes the viewer, or restores `whole`. The death of an owner
  is a take, so it needs the place `whole`: a view cannot outlive what it
  views.
- A join is the meet, with regions coarsened: a view live on both arms in
  one mode stays, its region the union of the arms' (a region is a window,
  the whole object, or a union of regions, so the coarsening loses nothing
  but which arm was taken); any other view is dead after the join. An arm's
  residuals are owed under its test, as closed data with the test as their
  hypothesis. A type that may not be dropped may not be `gone` by
  weakening.
- Overlap is decided on the places' steps where they are closed; otherwise
  it is a residual obligation. A key access emits `Valid`; an index its
  bound; a call the callee's precondition.

The first experiment (§15.6) keeps the state per object, not per name: a
table of which name holds each object now, and the views, each naming its
object and window. A name is `gone` when it no longer holds its object, an
object some view reads is `frozen` with those viewers, one none reads is
`whole`. `let y = x.set(i, v)` passes the object from `x` to `y`, so a
frozen window follows the object through its versions with nothing per
version. Stated per name, as above, the invariant needs two more clauses
(live names hold distinct objects; every live name on a view's object lists
its window), which are this table rederived.

What `out(viewer)` stands for is exclusivity: a live write view is apart
from every other live view. With eager write-back (§15.2) the holder's value
inside an out window is the viewer's, so the invariant does not weaken while
a loan lives: the object holds the holder's value everywhere, and each live
write view holds its own value at the window its slot names, which are the
same values there. A read of an `out` place by its owner would therefore be
sound (the fourth experiment proves it, `Sim::owner_reads`); it is refused
as policy (§15.7, item 4), and a write by the owner there is refused because
the next write-back would put back what was lent over it.

A place is frozen while a live binding's type mentions it in a read region.
A write under a frozen place is licensed where it is apart from it, so a
view of `xs[0..8]` permits `xs[9] := s`. A collection states one region for
all its elements; a finer one is a dependent record, never required.

**What is inferred is determined, by a rule and not by "least".** An
unannotated object binder `let x = π` is a take if `x` is consumed (moved,
updated in place, stored into an owned field, returned as owned) or if `π`
or a place containing it is replaced while `x` is live, and a read view
otherwise. The counterexample to "least": `let x = r.a; r.a := Buf::new(8);
sum(x) + len(r.a)` checks with `x` a take and is refused with `x` a read
view. The rule is one backward pass, since whether `let y = x` consumes `x`
depends only on later code. That its answer checks whenever any does is
argued, not proved. A write view is always written, never inferred; a death
is the last use; a join is the union of the place sets.

### 15.4 The theorems

- **`check_sound`** (once): a closed verdict `check(f, ann) = Some(rs)`, by
  evaluation and linear in `f`, and a proof of each residual under its
  site's hypotheses, give `Safe(f, plan)`. The residuals' proofs come from
  the proofs the source carries (§14.1) or a tactic. No separation algebra
  is used.
- **`Safe`** is, at each use of a place, that the place still reads its
  value: "usable implies current".
- **`sharing_sound`** (once): `Safe` gives that the level-2 run of the plan
  agrees with the meaning and stores only inside what it took or was lent
  to write.
- **`placement_sound`** (once): layout and placement take level 2 to the
  bytes level with typed cells (§15.5), live blocks in disjoint windows. The separation algebra
  of the first two waves (`Held`, exclusive footprints, the arena's
  `alloc_fresh`) is this theorem's mathematics, and the parallel licence's.
- Then the lowering as built, accepting a load or a store under a fact.

A compiled function's own `check_sound` is what a caller cites for it; only
level 2's primitives owe a hand proof that they keep what they do not need.

### 15.5 Level 2, and where memory comes from

```
value ::= word | Ref(block, steps)
steps ::= Field(i) | Elem(a) | Window(a, n) | Key(k) | Variant(c)
ops   ::= new(shape) | load | store | narrow | dead
```

A block's cells are typed (words, bytes, references), with no layout and no
address; the meaning is unchanged by renaming blocks. `dead` is emitted at
a death, one for the whole value; it has no code at level 2, and placement
gives it code or none (§15.10). A stored view, a view
chosen by a test, and a view returned into a caller's record are all a
`Ref` held as a value.

**Steps, as built (package 2, 2026-11-25; `issues/ownership-steps.md`).**
Steps are untyped data over atoms, `lib/lang/ownership/steps.hthr`:
`SField(i)` with a literal index, `SElem(a)`, `SWindow(lo, n)`,
`SKey(index, gen)` with the key as two atoms, `SVariant(c)`. Their meaning is
a model in one value type in which a step that does not fit the value reads
nothing (`StepModel`, denoted by `Path::then`); typed steps indexed by their
source and target were rejected as a universe above what the kernel
evaluates cheaply. Level 2's value universe is the model built
(`value_steps.hthr`: word, sequence, record, variant, store). Overlap of two
places is `Steps::apart`: the first difference after the common prefix,
answering no, yes, or yes owing obligations over the atoms
(`atom.hthr`'s `Obligation`, of which the checker's residual is the span
case). It is sound in any model with the laws and complete on closed steps;
an open index followed by more steps owes more than it needs
(`issues/steps-decider-completeness.md`). A window's value is a sequence of
its length, lawful only where what is written is one, which is the one
place the untyped universe costs a law (`PathLawsOn`).

**Why untyped, measured** (2026-11-25,
`issues/reflected-languages-typed-by-construction.md`; pins in
`lib/_tests/lang/ownership/typed_steps_tests.hthr`). The kernel's speed is
neither the cost nor the blocker. Steps indexed by types elaborate (through a
declared index type holding two types), denote, and decide by evaluation, but
no proof comparing two steps out of one source can be written: inverting the
second needs type formers injective and disjoint, which the theory does not
give. Steps indexed by codes (a mutual universe of shapes decoded by large
elimination) work, need only UIP at the codes beyond what the library has,
and remove the fit machinery; they cost a constant factor per code node,
because a code is data checked node by node, and a chain of either kind
carries its intermediate types, so checking a place is quadratic in its
depth where untyped steps are linear, a constant factor at the depths places
have. Proof work comes out about even, so all three languages stay untyped;
a code-typed universe is one more `StepModel` and can follow without rework.

This level stands above FunctionIR, which is bytes with static buffer
numbers. One new pass joins them: steps become byte spans (`Part`,
`Stored`) and each live block gets its memory.

**What a `Ref` becomes below** (the third; settled, §15.7). Three
candidates were worked through. One buffer with every supply a window of it
and a reference an offset: cheapest in proved code, but a span lent by a
Rust caller stays a second buffer, so a stored reference into either is
refused by a level-3 notion. Several buffers with a tag word in a stored
reference: a global supply table read on every access. **Typed cells down
to the machine**, a reference cell holding a reference until it becomes an
address, crossing by an injection of blocks: nothing is restricted, the
code is a pointer, and placelessness becomes a property of the language
(no operation observes a block's address) in place of a check per function.
Its cost is a new memory model in the middle of FunctionIR (buffers as
lists of bytes become blocks of cells, touching every module stated over
buffers by number; the word-only lowering is untouched), typed loads, and
`Loan` extended across an allocation. (The third experiment, §16, narrowed
all three: the memory relation is additive, the loads are typed in the
meaning only and lower to the same instructions, and `Loan` needs no
extension, only to be threaded per state.) The first is an instance of the third
with one supply, so level 2 and `placement_sound` are written against the
general interface.

`new` names no supply in the source or the meaning for an owned object:
identity first appears at level 2.

**The allocation policy is not a design commitment.** For memory obtained
at run time the checked thing is an allocator, and `placement_sound` is one
theorem over any allocator satisfying laws: a block it answers is disjoint
from every live one and large enough; a freed block leaves the live set;
with enough room it never fails. These are the arena's `alloc_fresh` and
`alloc_below` with a `free`, stated in `Held`. A frame plan decided at
compile time is the case discharged by a plan checker. So the first build
may be the simplest allocator.

**What is a commitment** (settled as leaned, §15.7):

- *When memory runs out.* The meaning is total, so an owned `new` cannot
  fail in it. Lean: the machine theorem says the code computes the meaning
  or stops at a defined out-of-memory exit, and computes the meaning
  whenever the room is at least a bound the level-2 run defines (as stack
  room is a premise today); a program that must handle exhaustion uses the
  library's fallible store, whose state is named and threaded.
- *What the default promises.* Level 2 defines the live size at every step,
  so the peak of live sizes is a function of the run that a theorem can
  bound. Only "a block's storage is reusable from its `dead`" has that peak
  as its cost; a stack or inferred regions can hold dead memory without
  bound (a state replaced per pass of a loop; a queue). Under that promise
  the death of a container has code, a traversal freeing its elements,
  though in the meaning a drop is still nothing.

**What the source may state**, each a demand: `new … in a` for an arena
value `a` (the block is part of `a`); `region r { … }` (every `new` inside
is in `r`, freed in bulk with no traversal, refused if anything typed in
`r` escapes); a frame slot (refused if the size is unbounded or the life is
not nested); `no_alloc` on a function.

A statically sized block with no live reference may be moved by placement;
that is never a copy.

### 15.6 The first experiment

One module: straight-line code over lists of numbers with in-place set,
get, a read view of a window, and clone; `eval1` over values; `run2` over
one buffer per object; `check` answering residuals; `check_sound`. Three
programs: a linear one accepted with no residual; a view and a write
accepted by one residual from a source hypothesis, with a `¬` theorem that
the runs differ where the residual fails; a read of a name after its update
refused, with a `¬` theorem that the refusal is not spurious.

It refutes the design if the invariant needs more than the place states,
if residuals cannot be closed data with a cheap meaning, if following a
name through its in-place updates makes frozen tracking awkward, or if the
kernel cannot evaluate the checker at tolerable cost. It does not test
write views, calls, stored references or placement.

**Result (2026-11-25).** Built as `lib/lang/ownership/place_check.hthr`, with
its programs and controls in `lib/_tests/lang/ownership/place_check_tests.hthr`
(`ownership-checker-spike` has the log). `check_sound` is proved by a
simulation whose invariant is the place states' meaning and nothing else:
a held object's buffer holds its holder's value, and each view reads its
window, its object held. No separation algebra, history or ghost state. The
write under a frozen window is framed by `PathIn::agree_apart` over
`Path::elem_in`. Residuals are closed data (`Span(lo, n)` apart from
`Span(i, 1)` over atoms), read in the words the meaning ends with, and the
second program's is one `omega` from `k <= j`. None of the four refuting
conditions was met. Two choices the design did not state: a run's view
carries its length (a read past it is zero, as the window's value is), so
no bound residual arises in this fragment; and the checker checks the plan
(a set's result on its source's buffer, a clone's on a free one, the
parameters' distinct). The checker's closed verdict grows quadratically
with program length, from unary name lookups rather than from the checker
(`place-check-name-lookup-cost`). What the next experiment needs of
these definitions is `ownership-checker-call-and-write-view`.

**The second experiment** adds functions and two operations: a call that
lends a window to write (in the meaning: window, call, `put_window`, the
eager write-back; at level 2 the callee runs on a reference with no copy),
and a call answering a read view of its argument, which the caller rebases.
Each function has a safety statement (its answer and its window agree with
the meaning, the file is unchanged outside the window, a returned view lies
inside the reference), and the caller's proof cites only its callees'
statements and signatures. Three programs: a written window beside a held
view, by one residual; a returned view, frozen while it lives; a callee
that breaks its signature, whose own check fails. It refutes the design if
a caller's proof needs more of a callee than its signature and safety
statement, if the simulation through `put_window` after `window` is costly
enough that eager write-back is the wrong meaning, or if the checker's cost
grows with the call depth.

**Result (2026-11-25).** Built as `lib/lang/ownership/call_check.hthr`, with
its programs and controls in `lib/_tests/lang/ownership/call_check_tests.hthr`
(`ownership-checker-call-and-write-view` has the log). A body's meaning and
run are stated over a world of its callees' meanings and runs, so no body is
reachable from a caller's proof: `check_sound` gives a function's `FnSafe`
from a closed verdict, its residuals under its precondition, and `FnSafe` of
what it calls, in any world; `prog_sound` gives every function of a checked
program `FnSafe` at every depth of calls. None of the refuting conditions
was met. The write-back is one lemma (`written_back`): the caller's "outside
my reference nothing changed" and the callee's "outside my window nothing
changed" compose pointwise, given that the callee's value has its window's
length; it is a once-proof cost, nothing per program. Rebasing uses only the
caller's own reference and the callee's "inside the reference". A verdict
reads signatures only, and its cost does not grow with depth. Because a loan
lasts one statement here, no window is `out` between statements and the
invariant did not need weakening; inside the call's step the weakened
invariant is two holds, the caller's outside the window and the callee's in
it. What was added to the place states: a live view lies inside the span it
freezes, and a read parameter comes back unchanged (what a callee that
breaks its signature violates). Choices: the run cuts a window to its
reference as the meaning's window is cut to its list, so no bound residual
arises (Rust panics instead); a residual is a sum of "apart" and a callee's
precondition, which is the proof parameter of §15.8; a view a callee answers
freezes the whole parameter. The promise has no postcondition, so a residual
over a callee's answer cannot yet be discharged
(`ownership-fnsafe-postconditions`). The checker is linear in program length
where the first experiment's was quadratic, from its representation
(`place-check-name-lookup-cost`). What the checker needs next (a loan held
across statements, a join, stored references) is
`ownership-checker-loans-and-joins`.

**The fourth experiment** (`ownership-checker-loans-and-joins`) restructures
`call_check.hthr` so one checker covers both earlier experiments' calls and
what they left untested, each item landed and verified before the next.

*A loan held across statements* (2026-11-25). The write parameter is now a
place (`x[i] := v` means `x := x.set(i, v)`), not a chain of named versions:
with one object per function the versions only counted writes, and a join
could not have met two arms that wrote different numbers of times. A view is
`View(t, md, lo, n)`, to read or to write; `Put(t, i, v)` writes through a
write view; `CallMut(g, t, args, z)` lends a live write view to a callee, so
the second experiment's one-statement loan is `View`, `CallMut`, `Die`. In
the meaning a write view is its value and an erased slot (§15.2), and `Put`
and `CallMut` write it back at once (`Sem::back`). The invariant did not
weaken: the file holds the holder's value everywhere, each live write view
holds its own value at the window its slot names (`Lent`), and a live write
view is apart from every other live view (`Sim.excl`, what `out` means).
`written_back` serves both a store through a view and a call lent one, so
the write-back after a statement costs one write's proof whatever the
loan's length. The owner's read of a lent part is refused and proved sound
(`Sim::owner_reads`; `loan_unchecked_agrees` runs a program whose residual
fails and whose runs agree); the owner's write inside the window is refused
with `clobber_control` (the run reads 9, the meaning 6).

*A branch with a join* (2026-11-25). A body is a tree, `If(test, a, b,
rest)`, the arms binding as many words and views as each other (an arm's
words are the join's values, as a phi's). The checker joins the arms'
places by the meet above; a residual of an arm is `Under(test, arm, owed)`,
which holds wherever the test gives the other answer or the owed holds, so
the residual is closed data whose hypothesis is the test. The proof needed
nothing per arm that survives the join: the arm taken has the invariant at
its own places (by the same induction), and `Sim::weaken` gives it at the
meet's, since the meet only drops views and a union region covers each
arm's (`Covers`, `Coarser`); no flag records which arm ran. Coarsening to
the whole object was tried first and refused writes apart from both arms'
windows; the union is exact and simpler to prove, a region's licence being
pointwise (`Region::Clear`). Controls: a view read after a join where one
arm ended it (`after_join_control`, 9 against 5); the same write without the
branch, whose residual fails (`unguarded_control`); the write in the other
arm, whose residual is owed under the other answer and fails there
(`swapped_control`); a write into either arm's window while the joined view
lives (`coarse_held_control`, 7 against 6).

*A finer returned region* (2026-11-25). A signature's result is `KView(region)`,
the region stated in the callee's parameter words (`Ret::kind`: the
answered window where it reads only parameter words, else the whole
parameter); a caller reads it at its arguments (`Region::subst`) and freezes
only that, so it may write beside the view. `FnSafe`'s `view_in` became "the
answered view lies in the signature's region, at the call's words", and it
is load-bearing: the caller's frame for its later write is the view's
`ViewOk.within`, which comes from it and nothing else. `stray_not_safe` is a
callee that answers the right value at the wrong place, keeping every other
part of the promise; with it, an accepted caller's runs differ
(`stray_breaks`).

*Postconditions* (2026-11-25, `ownership-fnsafe-postconditions`). `FnSafe`
gains a postcondition, a proposition of the call's words and its answer,
which the callee's own proof establishes and its callers assume. The
checker's data did not change: a residual over a word a call bound is
ordinary closed data, and its proof is the caller's, under the hypothesis
`Posted` that the world's callees answer what their postconditions say
(derived from their `FnSafe` at a file holding only the argument). A
callee's postcondition is one more proof parameter beside its precondition
(§15.8). One limit: the depth-zero world of `prog_sound` answers zero, so a
postcondition zero does not meet is composed depth by depth from
`check_sound` (`after_sound`); a recursive program with such a postcondition
needs the termination the meaning assumes, which this toy's world by depth
does not state.

*Stored references and the erased owner* (2026-11-25). A mode `Lends(n)`
is a function lent `n` write references stored in a collection, whose owner
is erased: in its meaning it takes the owner's value in and out with each
reference's slot (`Sem::start`), and in its run it is given the references
and no reference to the owner (`Mode::owner`). It cannot name its owner
(the owner statements need `Mode::owns`). A caller hands it live write views
(`CallAll`), which the call consumes. `FnSafe` is stated at a reference
standing for the owner's place, which the run never sees, over the slots it
was lent (`Lendable`: as many as the mode says, pairwise apart); its frame
is `kept_out`, nothing changed outside the lent references' spans, so it
names no object reachable through them, only the owner's place once per
owner. The caller's proof cites only that promise, at its own reference;
the collection's exclusivity comes from its own place states (`Sim.excl`)
and the consumed views die. Inside the callee the invariant gains `kept`
(a lending function opens no view and changes nothing outside what it was
lent), which follows from its having no owner to touch. Controls: one view
lent twice (`twice_control`: the second write-back puts back a stale copy,
1 against 6), a consumed view read after the call (`reuse_control`), a
lending function that reads its owner or answers a view of it (refused).
Untested: a collection held in data across statements rather than formed
at the call, references into several owners, and places with steps.

**Cost and shape (2026-11-25).** The closed verdict stays linear with
loans, joins and union regions: at 2 to 64 units of ten statements (a loan
held across a write and a read beside a long-lived view, then a branch
whose arms open views on different windows), the full verdict `check_fn(…)
= Some(rs)` costs 9.2k to 290k kernel steps, each doubling 1.96 to 2.03
times the last. One object per function throughout, so the holder table the
first experiment's quadratic came from does not arise.

### 15.7 Settled by Minus, 2026-11-25, and what is still open

- **When memory runs out**: room is a premise of the machine theorem, the
  stop is a defined one, and the room a function needs is something a
  theorem can bound (the peak of live sizes of its level-2 run), so a caller
  or an export can discharge the premise. How bounds are stated and found
  is to be designed; it should be done elegantly, not bolted on.
- **The death of a container may have code**, and the default promises
  reuse from `dead`. The aim is to do it better than Rust: no drop flags
  (a death is static, inserted on the arm that did not move), no user code
  run at a drop, no walk where the elements are plain or the container is
  in a stated region, a traversal that cannot overflow the stack, and a
  thing that must be closed (a file) is a type that may not be dropped, so
  its closing and its error are written.
- **References stay references down to the machine**: typed cells, an
  injection of blocks at the last step, placelessness a property of the
  language.

- **The first reclaiming allocator frees at the death**, so the bound is
  the peak a reader can see; a lazy one stays possible as a policy under
  the same laws.
- **`defer` is for a release that cannot fail**; a close that can fail is
  written as the bracket, so its error is combined.

Still open:

3. That the inference rule's answer checks whenever any annotation does
   (§15.3): argued, to be proved with the judgment.
4. Whether an owner may read a part it has lent to write, which eager
   write-back would make sound. Kept refused at first. (The fourth
   experiment proves it sound, `Sim::owner_reads`: with eager write-back
   the owner's buffer holds the viewer's value inside the out window.)
5. The order in which the levels are built and the customers ported.

### 15.8 What a signature records

Per function, in the module's interface: its region parameters (and for
each whether an erased owner goes in and out); per parameter its class,
its mode (take, read, write), the parts it may write, and what places its
type's regions stand for; for the result its class and whether it is fresh,
is a parameter, or is a view of places of parameters; and its cost (none, a
bound with its theorem, or unstated: §15.9). Residual preconditions are not extra data: they are the proof
parameters in the kernel type, and so is a postcondition about the answer,
which the function's proof establishes and its callers assume (the fourth
experiment's `FnSafe`). A caller's checker reads the modes to step
its place states across the call, the result's origin to know what is
frozen or out while the result lives, the parts to emit `Apart` against
views it holds, and the name of the callee's safety theorem to cite. It
reads no summary of what the callee keeps.

The inferred fields (take or read, fresh or a parameter, a cost of none) are in
the interface, so a body that flips one changes the interface and its
importers are checked again: a caller that used `v` after `f(v)` is refused
when `f` starts consuming it. A callee's plan, deaths and internal
residuals are not in it.

### 15.9 Memory bounds

A cost is a pair: the high-water mark of live size above the entry, and the
change in live size at the exit (an integer: a function that consumes an
argument has a negative one). Costs compose in sequence as `(max(a.peak,
a.net + b.peak), a.net + b.net)`, a monoid. A `new` of size `n` is `(n, n)`;
a death is `(0, -size)`; a call is the callee's cost at its arguments, which
is the callee's peak on top of the caller's live size; a loop is the fold
over its passes. `Cost2(f, args)` is this read off the level-2 run, with
sizes from the layout. The total allocated, which a bump allocator consumes,
is the same recursion in the naturals under addition, and a step bound
later is that monoid over steps: one judgment, parameterised by a monoid.

- **Published**: nothing for `Cost2`, which every function has. A bound is
  a theorem beside the function, `f::room: Cost2(f, args) <= bound(args)`
  with `bound` a level-1 term, and the interface's cost field names it.
  Importers depend on the stated bound, so a body that keeps it provable
  does not change the interface. `no_alloc` is the demand for a cost of
  none.
- **Found** by a second judgment of the checker's shape: `cost(f, plan)`
  answers a bound term and residuals, and `cost_sound` gives the bound from
  them. Automatic where there is no `new`, where sizes are literals or
  terms in the arguments with no loop of positive net, and for a loop whose
  pass has net at most zero. A loop whose live size grows asks the user for
  a potential, and the residuals are each pass's net against its
  difference. A growable container's size is level-2 state, so its type
  publishes a law bounding it by its level-1 length.
- **Used** at an export: with a bound, the wrapper evaluates it and compares
  it with the room given, a failure being an answer in the export's written
  result type; or it sizes a region by it. With none, the machine theorem
  is "computes the meaning or stops at the defined exit". An internal call
  composes its callee's bound.

A tokenizer over a doubling vector has both buffers live at a growth, so its
bound is about three tokens' sizes per input byte, from the vector's law and
the invariant "tokens so far at most bytes consumed"; with the vector made
at the input's length it is one `new`, automatic, and the same invariant
proves each push has room. A loop that replaces its state each pass has a
pass of net zero, so its bound is two states and does not grow with the
count; under a bump allocator the same pass computes the total, which does.

This is the metered model `memory-bound-certificates` asks for and
`hih-alloc-metering`'s done-when, and the capacity `datarepr-design.md` §2.3
says an out-of-memory outcome is erased relative to.

### 15.10 Deaths

A death at level 2 is one `dead(x)` for the whole value: every block
reached through owning cells. A view and a key own nothing.

| Value | Code at placement |
|---|---|
| Plain data; an object in a frame slot, a stated region or a bump supply | none |
| A vector of plain data, in a reclaiming allocator | one free |
| A vector of owned buffers | a loop freeing each, then one free |
| A tree | a traversal, linear in its blocks, in constant stack |
| A store | a walk of its live slots if their values own blocks; a key's death is nothing |
| A record holding a view | nothing for the view |
| A value that may not be dropped | none exists: it is consumed |

A type's death is nothing exactly when it owns no block in a reclaiming
allocator, decided on the type's description beside the copy decider. The
traversal is one function over shape descriptions, proved once and
specialised per type: it terminates because ownership is a tree, which
exclusivity gives, and it runs in constant stack by threading its worklist
through the dead blocks.

Partial deaths need no flags, since place states are static at every point:
a record with a field moved out frees the rest; a conditional move puts the
death on the edge of the arm that did not move; an element moved out at an
index is skipped. A pop while a view of another element lives owes that
they are apart.

A value that may not be dropped and is live at an early exit is refused.
What is written is a bracket, an ordinary higher-order function whose
finaliser takes the resource and the block's result, so a close's error is
combined and not lost; `defer` is its sugar over the rest of a scope.

Against Rust: no drop flags, no user code at a death (so no drop order and
nothing that can fail there), no unwinding paths since the language is
total, a death at the last use and not the scope's end, a traversal that
cannot overflow the stack, bulk death by a stated region, and the cost of a
death as a term in §15.9's bounds. Merely different: a container of owned
things still costs a walk; a guard or a counted pointer is a type that may
not be dropped, with a written release; an early exit holding a resource
costs a bracket.

## 16. The order of building

**§17 supersedes this section's plan for the back half** (package 5 and
"the typed-cells change is made additively"), and gives the stages. The
other packages stand as the content of §17.5's stages 4 to 7.

From the design partner's reading of the back half (sizes measured; how
local the typed-cells change is in the two largest lowering modules is not
yet known).

**Three interfaces first**, definitions and law records with no proofs, so
that work on either side is against a record: level 1 (the reflected form,
the annotation, residuals, the signature record of §15.8 with its cost
field); level 2 (its syntax, heap and run, the `new` and `dead` events,
steps); and the bytes level's contract (memory with references, the
allocator's laws, the statement of the injection).

| # | Package | Needs | Done when |
|---|---|---|---|
| 1 | The three interfaces | the experiments | the modules check; a probe states each theorem's type |
| 2 | Paths as data: steps, their denotation, the apartness decider | nothing | sound against `Apart`, complete on steps; `split_at_mut` and two fields by evaluation |
| 3 | The checker with calls, write views, regions, joins and loops, and `check_sound` | 1, 2 | the experiments' programs through it; the inference rule's completeness proved or refuted |
| 4 | Level 2 and `sharing_sound` | 1 | a planned program's level-2 run equals its meaning |
| 5 | Typed cells and the injection to x86 | 1 | a reference stored, loaded and read through, compiled; existing certificates unchanged |
| 6 | Layout, the allocator's laws, a bump allocator, `placement_sound` | 1 | live blocks disjoint; the arena's laws an instance |
| 7 | `cost` and `cost_sound` | 1 | §15.9's two examples with their bounds |
| 8 | Deaths: the traversal, a reclaiming allocator | 6 | a tree freed in constant stack; a replace loop's cost independent of its count |
| 9 | The surface: region parameters, stored borrows, eager write-back, the inference rule, interface fields | 1 | probes; the image carries the signature record |
| 10 | One reflector to level 1 with site facts | 1, 9 | a function with a found proof compiles with no bounds comparison |
| 11 | Port the arena, the word map, the linked lexer and hashes; delete the four languages | all | `scripts/linked --check`; the suite |

After package 1: 2 then 3; 4; 5; 6; 7; 9 run beside each other. 4, 6 and 7
meet only through level 2's interface, 5 and 6 only through the bytes
level's.

**The typed-cells change is made additively.** `Buffers()` stays bytes; a
shadow beside it says which slots of which block hold a reference and to
what; a reference value kind and its nodes are added; the injection says
the machine's bytes are the buffer's off the shadow and the target's address
on it. Every buffer that exists has an empty shadow, so every existing
theorem is the special case and keeps its statement. About half of
`lib/native/function_ir` by size is heavy on buffers; the operations, loops,
certificates and word rules are untouched, and little of
`lib/std/arch/x86_64` is.

**The riskiest package is 5**, the only one that changes proved code: the
lowering's central invariant, "a register holds the valuation's word",
becomes for a reference "holds the address of the valuation's reference",
and whether that splits cleanly by kind is unknown. Its earliest test is a
third experiment: a toy bytes-level language with word and reference values
and one shadowed block; a store of a reference, a load of it, a byte load
through it; lowered to x86 and proved by the injection. The second risk is
the kernel's cost of evaluating the checker on real functions; if it is
bad, the checker runs on the untrusted evaluator, as reads do.

**What the third experiment found** (2026-11-25,
[[ownership-reference-cells-spike]], `lib/native/reference_cells/`, deleted
with `issues/bytes-level-on-the-contract.md`). The
toy is proved through to x86's instruction steps: a reference stored, loaded
back and read through, under any `Loan` of its blocks (`Loan::program_runs`),
the meaning unchanged by renaming blocks (`run_renames`), and both controls
theorems. It corrects the two claims above.

- *Additive*: true of the memory relation, and proved both ways: the
  injection at an empty shadow is `Stack::InMemory` (`in_memory_injected`,
  `injected_in_memory`), and the toy's store theorem there is
  `in_memory_span`'s (`in_memory_word_stored`). Not true of the call
  contracts: `Effects()` relates `Buffers()` before and after a call in
  about ninety places across ten modules, and a reference kept in a block a
  callee is lent needs that file to carry the shadow. So the change is
  additive inside a function and a choice at calls: generalize the contract
  with today's as its empty-shadow instances, or keep references out of
  lent blocks at first ([[reference-cells-call-contracts]]).
- *The riskiest package*: the register invariant does not split by kind,
  and need not. A register holds the valuation's word where the valuation
  is the one lowered through the injection, a reference lowering to its
  target's address; that is `Held::Rep` at kind `Word` unchanged
  (`registers_represent`), and the buffer homes (`Lent::Holds`) already are
  this case. The risk moves to what replaces `placeless`: FunctionIR's ids
  typed word or reference, and a per-node check that no word node reads a
  reference, without which a node's equation does not transfer to the
  lowered valuation ([[reference-cells-id-kinds]]). The word and reference
  loads and stores are the same instructions; the types are in the meaning.
- *`Loan` across an allocation*: no new law. Pieces carved from lent spans
  are a `Loan` (`Loan::carve`) and their stores are their parents'
  (`Stack::wrote_in_parents`); what changes is that a body's invariant
  carries the current pieces instead of one lending fixed for the program
  ([[reference-cells-lending-per-state]]).
- *New*: a store that cuts a reference has no meaning (the bytes left under
  it are part of an address), so a copy of a record holding references is
  a typed copy where the layout is known, with no fragments; a copy of
  unknown layout is open ([[reference-cells-range-copy]]).
- *Cost*: the machine module checks in about a second; stated over x86_64's
  step records at neutral parameters, in stage theorems, the proof was not
  where the cost is.

Package 5 is reordered by this: the id kinds and the per-node check first
(the change that replaces a proved check), the new nodes over the injection
second, then the per-state lending with package 6, and the call contracts
last, when a customer passes a structure holding references to a callee.

## 17. The back half's target, and the staging (2026-11-25, revised)

This replaces §16's "the typed-cells change is made additively" and its
package 5. It was written after Minus's charge (§14 item 18) and a reading
of where the call contract is stated. §16's packages 1 to 4 and 6 to 11
stand as the content of stages 4 to 7 below.

### 17.1 Why the contract is stated ninety times

Two causes. **Buffers are numbered per scope**: a callee's buffer `k` is its
caller's view `k`, so every call that lends a window renumbers memory, and
that alone is why `Lending`, `Site::CallsLent`, `Views`, `Viewed`,
`Lendable`, the `Lend` node and experiment three's `Carved` exist (`Carved`
and `Viewed` are one record, `Loan::carve` and `Loan::view` one proof: the
experiment re-derived the views lemma under a new name). And **the meaning
is stated several ways**: `Callees`, `Answers`, `Defines`, `Effects`,
`Writers`, `Readers`, a relation or a function crossed with the file fixed
or threaded, with definedness beside, and bridges proving one is another.
At the machine the contract grew in tiers (`Unchanged`, `Wrote`, `WroteIn`
over one lending, any lending, parts of spans), each derived from the next.

### 17.2 The one statement

At the bytes level, one partial function, a missing answer covering both
"not defined" and "no meaning":

```heather
record Answer { words: List<Value>, heap: Heap }
fn Calls() → Type { Nat → List<Value> → Heap → Option<Answer> }
fn run(p: Program, f: Nat, args: List<Value>, heap: Heap) → Option<Answer>
```

A pass proves one thing, that every answer of its input is an answer of its
output. At the machine, one contract over one lending for the whole run
(`Site::Meets`): before the call the arguments are passed and the heap is
injected into memory; after it the answer is in place, the kept registers
are kept, the stores were inside the lending, and the answer's heap is
injected. Since the injection after the call pins every byte of every
block, "the callee left alone what it was not lent" is not a machine
statement: it is a fact about the answer's heap, proved above.

The lemma interface is one module: `Loan` and its laws; `WroteIn` with its
order and frame rule; `Injected` with one lemma per memory operation; and
`Sub` (a part of a span) used once, where an export's borrows are parts of
its caller's spans. A reference in a lent block is then a change to
`Injected` and its operation lemmas and to nothing else.

**As built (stage 1, 2026-11-25; `issues/x86-memory-contract.md`).** The
module is `lib/std/arch/x86_64/x86_64_memory_contract.hthr`, the older
names its instances in `x86_64_memory_tiers.hthr`
(`docs/native/native-one-compiler-design.md` §2.7). Choices made there:

- `WroteIn`'s order is one lemma over the offset and the spans
  (`Stack::wrote_in_widen`, `Spans::Within`), and `WroteIn::up` is
  `Stack::wrote_in_up`, `WroteIn` being a method of `Stack`.
- `Sub`'s place equation holds where a piece has a byte, since the
  callee's buffers over views place an empty buffer anywhere; so
  `Loan::sub` takes the pieces' canonical bound, which a piece with a byte
  has (`Loan::canonical_at`).
- A store is one lemma at any width (the shadow's overlap and cut are
  stated for `n` bytes), a load one lemma with the machine's widths as its
  cases. Eight bytes stored over exactly a pointer replace it, as in the
  experiment.
- The heap is canonical by construction: a pointer store zeroes its eight
  bytes, so it is a word store and a pointer, and its injection lemma is
  derived from the word store's; `Heap::Canonical` and its preservation are
  stated beside `Injected`, not inside it, so no operation lemma carries
  it.
- A byte is plain, part of a reference, or undefined: `Heap.undefined`
  is a per-byte set beside the shadow (a store clears its window, so no
  range is ever split), `Injected` constrains only defined bytes, and is
  stable under any change of memory at undefined, uncovered bytes
  (`Injected::undefined_change`), which is what a failed `read` leaving
  junk needs. Canonical includes zero under undefined bytes.
- The heap's blocks are lists by block number (each block's bytes and its
  undefined flags), updated as lists by a store, and read only through
  `Heap::bytes` and `Heap::undefined`: a closure layered per store made
  evaluating a run quadratic (measured: a run of k load-then-store steps
  doubled to 2.2, 2.5, 2.8 times its steps at each doubling of k; as
  lists, 1.9, 1.9, 2.0).
- `Site::Meets` is stated against a meaning on words
  (`Nat → List<BitVec(64)> → Heap → Option<Returned>`): the bytes level's
  `Calls()` over values meets it through lowering each value to its word.
  The System V definitions it needs (`argument_registers`, `ArgsIn`,
  `Stack::Passed`, `callee_kept`, `answer_registers`) moved into the
  module from FunctionIR's lowering. It was provisional; its final form,
  over the bytes level's meaning with the world, is §17.6's second part
  (`x86_64_call_contract`).

### 17.3 The bytes level as the design wants it

- **Values** are words and references (a block and a byte offset); a length
  is a word beside a reference. Every id has a kind, checked by validity as
  widths are. That check replaces the per-function `placeless`, and
  placelessness is one theorem of the language (a run commutes with a
  renaming of blocks).
- **Memory is bytes with a shadow**, which is the right definition here and
  not the cheap one: layout has happened, and memory is bytes some eight of
  which are a reference. (Level 2 has typed cells and no sizes.) The bytes
  under an entry are zero by invariant, so a heap is canonical.
- **Blocks are few and fixed for a run**: the spans lent from outside and
  the supply. Nothing creates a block here; a level-2 block is a window of
  the supply, and `new` and `dead` are calls into the allocator, which is a
  function of this language over the supply under its laws.
- **Nodes**: the word operations as built; through a reference, a load and
  a store at a width, a load and a store of a reference, an offset, a typed
  range copy. No node names a buffer by number. A load or a store is
  accepted under a site fact (in bounds, not cutting a reference, inside
  what may be written), of which a comparison on the path is one prover.
- **A call** is an ordinary call on values, under `Site::Meets`. A window is
  two parameters. A system call is one more kind of callee, answered by the
  world's model, in the contract from the first day.

### 17.4 Against what is built, and the choice

Of `lib/native/function_ir`: the word operations, the optimizer's rules,
loops, certificates, register placement and the structured lowering are
already the target; evaluation, the passes, linking, the compile theorem
and exports are the target with a different memory; and `placeless`, views,
lends, the buffer homes, the several meanings and the contract's tiers and
bridges exist only because of how memory and calls were stated.

**Chosen: a new memory and call layer beside the old, then one switch.**
The new node type wraps the existing word nodes, whose lowering already
proves the buffer-free case and is cited unedited; the memory nodes, calls
under `Site::Meets`, loops, linking, the compile theorem, exports and the
passes are new modules against one meaning. The additive shadow was
rejected: it keeps every meaning and tier and adds one more, with buffer
numbers and references both naming memory. The end state has the program
compiler (`native_compile*`, `native_source*`, `native_build*`) folded in:
with the world in `Calls`, the tools become functions over `Io` and that
second compiler goes, which is where `native-one-compiler` was heading.

Not yet known: whether the structured-control lowering and the frame proofs
are generic in the body's invariant, so cited, or must be redone. Reading
those two proofs opens stage 2. (Read: §17.6.)

### 17.5 Stages

The rule: **a layer exists once, and a customer is on exactly one
pipeline.** Two pipelines may stand beside each other; one statement may
not have two spellings in use.

| Stage | Replaces or adds | Verified by |
|---|---|---|
| 1 | Replaces the x86 memory tiers and `x86_64_views` with the contract module; the old names survive only as abbreviations the old lowering cites | the suite; every existing certificate unchanged |
| 2 | Adds the bytes level and its lowering beside FunctionIR's memory half, with a translation from the old programs (buffer `k` becomes a reference parameter) | its probes; every row of `crates/linked`'s exports compiled both ways gives the same assembly, or a reviewed difference |
| 3 | Replaces: `compile-x86` goes through the new layer; the old memory and call modules, the buffer nodes and stage 1's abbreviations are deleted in the same change | `scripts/linked --check`; the native gates; the plain suite |
| 4 | Adds level 1 (the checker), level 2 and `sharing_sound`, placement, cost, deaths: a library stack with no customer, landed package by package against fixed interfaces | the library gate; the experiments' programs through the real modules |
| 5 | Adds the surface and the one reflector, not yet selected | probes; each existing customer's new declarations published beside the old in a scratch build, counting which library theorems fail to restate |
| 6 | Replaces: `runtime fn` selects the new generator; every `runtime fn` moves at once; the four reflected languages, their meanings, the generator and the old facts are deleted in the same change | the plain suite; `scripts/linked` |
| 7 | Replaces the library's old path vocabulary (`Footprint`, `KeyIn`, `PathSame`, the three `*_paths` modules), and the tools and the program compiler | the suite; the tools' tests |

Stage 3 is the largest safe single move: no customer has a hand proof at
the back half, every certificate is regenerated by the compile, and stage 2
has shown the output is the same. Migrating the memory modules one at a
time would put two heap types in one proof. Stage 6 is the riskier one,
since customers cite generated names and the arena and the word map lean on
the held meaning; stage 5's scratch build is its test.

The experiments' modules (`place_check`, `call_check`, `reference_cells`)
are deleted when the real modules exist (`reference_cells` on 2026-11-25,
its probes re-expressed in the bytes level's and the contract's).

### 17.6 Stage 2's language as built (2026-11-25)

`lib/native/bytes_level/` (`issues/bytes-level-language.md` has the log,
`lib/_tests/native/bytes_level/` the probes).

**The reading.** The structured lowering (`function_ir_lower_structured`)
is about words and control only: its invariant is registers alone. The
call, loop and frame proofs of `function_ir_lower_calls` reach memory
through one clause, `Stack::Trail` in `EmitsOver`, and use it only for
its stability under the frame's own stores. So they can be cited by a new
memory layer once that clause is a parameter with that one law, which
is now so (below).
`StructuredRegion` itself is not reused: its leaves have buffer nodes and
its meaning is relational. The new language states its own regions with
the same shapes so that the lowering can reuse the emission and the
word-and-control theorems.

**The generalisation, made** (stage 2, `issues/lowering-generic-in-memory.md`;
`docs/native/native-one-compiler-design.md` §2.8). The memory clause is a
parameter `Mem: S → M → Type` over a state type, the trail is
`WroteIn ∧ Mem`, and its one law is stability under the frame's own
stores (`Stack::ClauseStable`). The emission lemmas, the conditional, the
call sequence (with the callee's contract any `Pre`, `Post` and two
hypotheses relating it to the caller's clause), the function's three
stages and the loop's passes are proved once over it. FunctionIR's
statements are the instance at `Buffers()` and the file in memory, each a
one-line derivation, so no certificate changed; the bytes level's is
`Injected` at the contract's heap, whose law is `Loan::stable_injected`.
Every theorem the reading listed used the clause only through that law,
except the CALL, which also relates the callee's clause to the caller's:
that is a hypothesis, as it was for a call over views. The loop's passes
became one induction on any measure, the run's fuel for a plain loop and
the passes left for the bounded one; the bounded loop's head is the plain
one with the counter as one more register.

**The language** (`bytes_level`, as revised the same day by the
coordinator's round on the world and non-terminating loops). Values are
words and references (`x86_64_call_contract`'s `Value`).
A run is at a configuration: a routine's ids (its words in a FunctionIR
valuation, so a wrapped node (`Compute`) runs as FunctionIR's evaluator runs
it, unedited, and references beside them), memory (the machine contract's
`Heap`), and the world (`linux_world`'s `Io`). Nodes: `Compute`, a
load and a store of 1, 2, 4 or 8 bytes, a reference's load and store,
`Offset` and a typed `Copy`. Regions: a leaf, a sequence, a branch, a call,
a plain loop, a system call (`Sys`: read and write so far) and `Exit`. The
one meaning is a family over fuel, `run(p, blocks, n, f, args, heap, io) →
Ran<Answer>`, where `Ran` is one of `Done`, `Exited`, `Going` with the world
so far, or `Stuck` with the world it got stuck in (no meaning). It is monotone in fuel (`run_monotone`,
`run_settled`, `bytes_level_fuel`). Calls and loop passes spend fuel, so
routines are tied by fuel and not by levels. Validity checks every id's
kind (`Program::valid`, a system call's descriptor and count among them),
and that check is what replaces `placeless`. Placelessness is `run_renames`
and `run_words_alike` (`bytes_level_renames`), proved once for the
language, fuel by fuel; a renaming is the identity on the world, because a
command carries only words and bytes.

**Choices this made**, each the default taken where §17.2–17.3 left it
open:

- *What is fixed for a run is beside the program, not in what it answers*:
  `Blocks` says which blocks may be written, and the heap holds contents.
  With references, which block a store hits is dynamic, so a store into a
  block the run may not write is `Stuck`. One writability per block per
  run is the grain; read-only-ness per call is proved above, by the
  checker. Lengths stay the heap's (its bytes are lists): a second copy
  would need an invariant tying the two.
- *A byte is plain, part of a reference, or undefined.* A load of an
  undefined byte is `Stuck`; a store defines; a failed read leaves its
  window undefined; a typed copy carries undefinedness.
- *Every memory operation is a take or a put of a piece* (bytes, the
  references wholly among them at offsets of their own, and which bytes
  are undefined). A word's load is a take holding no reference and nothing
  undefined. A reference's load is a take of eight bytes holding one at its
  start. A store is a put of bytes, a reference's store a put of eight zero
  bytes holding it, and a typed copy a take and a put. So there are two
  site facts and two renaming lemmas, and each lowering lemma will be one
  `Injected` lemma per primitive. Since the second part these are the
  contract's own operations, defined once (below).
- *Canonical by construction*: a reference's bytes and an undefined byte
  are zero (`Heap::Canonical`, kept by every put and so by every run:
  `run_canonical`, `bytes_level_canonical`). That entries are apart from
  each other is kept by construction too but not yet stated; the passes'
  congruence needs it (`issues/bytes-level-passes.md`).
- *`Refines`* (the coordinator's three clauses, and a fourth from the
  second part): answers and exits of `p` are `q`'s; a history `p` reaches
  while going is a prefix of one `q` reaches; a history `q` reaches with a
  meaning is a prefix of one `p` reaches unless `p` gets stuck after a
  prefix of it; and where `q` gets stuck, `p` got stuck after a prefix of
  where. Heaps are compared as they read (`Heap::Same`); there is no
  function extensionality. `refines_refl` and `refines_trans` are proved
  (below).
- *Widths stay FunctionIR's*: validity checks kinds, not the widths of word
  nodes, which the leaf's lowering tracks as it does today.
- *`Offset` adds a word as a number*: a reference below its block's start
  is not expressible yet. A window is carved forward from a base.

**Cost** (shapes, `--timings` per declaration). Each module's own
declarations check in about a second or less in all; the costliest are
the canonical lemmas' `omega` steps. The renaming and fuel proofs are
linear in the language's constructors. `run` on the probes is a few
thousand kernel steps per run. On the experiment's heap (blocks as a
closure per store) a read of one block through stores into another is
quadratic in the stores; blocks as a list by number is the linear form.

**The second part: the language on the contract** (2026-11-25,
`issues/bytes-level-on-the-contract.md`). One memory, a transitive
refinement, and `Site::Meets` in its final form.

- *One heap, one definition of each operation.* The language's memory is
  the contract's `Heap` (blocks as lists by number, a shadow of pointers,
  per-byte undefined flags), read through `Heap::bytes` and
  `Heap::undefined`. Every operation is defined once, in the contract, as a
  read or a write of a piece: `Heap::piece` and `Heap::placed` (the only
  way a heap changes), with one site fact, `Heap::fits` (in its block,
  cutting no reference: a range may hold references whole), and the
  partial forms `take` and `put` (which also asks that the block may be
  written, given as a function so that both the language's `Blocks` and a
  lending's `Spans` are one). `read_bytes`, `load_ref` and `copy` are
  takes and puts; the machine's `store` and `store_ref` are `placed` of a
  plain and a reference piece. The direction chosen was the contract's
  stores from `placed`, not the reverse: a put of a piece with several
  references and its flags (a typed copy, a failed read's undefined window)
  is not a composition of word and pointer stores, while each machine store
  is one put. `placed` on an empty shadow and empty flags reduces to the
  lists FunctionIR's `Heap::of` facts expect, so `function_ir_lower_calls`
  checks unchanged. The contract's loads are stated from `read_bytes`
  (`Injected::reads` and its widths) and `load_ref` (`ref_read`), so the
  old `Heap::plain`, `byte`, `dword`, `word` and `found` are gone. One
  `Heap::Canonical` (the language's form: zero under a pointer and under an
  undefined byte), kept by every canonical piece placed
  (`Heap::placed_canonical`) and carried by every piece
  (`Heap::piece_canonical`). `Blocks` stays the language's;
  `Heap::put_lent` is the one fact a lowering needs of it, that under
  `Blocks::Lent(spans)` a put the run makes is a store the lending allows.
  Renaming (`HeapRenamed`, `Heap::take_renames`, `put_renames`) and the
  canonical run (`run_canonical`) are re-proved over the lists with their
  statements unchanged.
- *`Stuck` carries the world it was stuck in*, and `Refines` gains its
  fourth clause. With the third clause alone transitivity fails twice:
  where `q` is stuck, `(p, q)` says nothing of `p`, so a `p` that diverges
  silently refines a `q` that gets stuck, which refines an `s` that writes
  anything; and where `p` is stuck at a history extending one `s` reaches,
  "stuck after a prefix" is false although `p` did reach it. So the third
  clause counts a history `p` reaches stuck or not, and the fourth makes a
  stuck output owe a stuck input at or before it. Two prefixes of one
  history are comparable (`extends_comparable`), which is the step that
  composes (`covers_at`); `refines_trans` follows.
- *`Site::Meets` in its final form* lives in `x86_64_call_contract`, with
  the meaning's `Value`, `Answer`, `Ran` and `Calls()`: FunctionIR's
  lowering imports the memory contract and spells its own `Word` and
  `Answer` bare, so those names cannot be declared there. The machine's
  state carries the world (`Running`), a step is a machine step or a
  system call the Linux model reads (`LinuxRequests`, `linux_answered`,
  the world's answer one `LinuxCmd::Answers` allows), and the claim form
  quantifies over every resumption as `LinuxResumes` does. Three clauses
  at every fuel: done (`Site::MeetsDone`), exited (`MeetsExited`), going
  (`MeetsGoing`, every world reached before the return a prefix of a
  history the meaning reaches). The record `Returned` is gone. The probe
  that `Site::CallsLent` gives the done clause at an empty shadow is
  `calls_lent_meets_done`.
- *Evaluation is linear on the lists in both shapes the first part
  measured.* `run` with k one-byte stores into a block then a load of it:
  5,061, 7,765, 13,173, 23,989 and 45,621 kernel steps for k = 8 to 128
  (the closure heap: 5.4k to 49k). k rounds of a store into one block and a
  load of another: 6,713, 11,633, 21,473, 41,153 and 80,513 (the closure
  heap: 7.4k, 12.8k, 25k, 57k, 149k, quadratic).

**The third part: the lowering, its first half** (2026-11-25,
`issues/bytes-level-lowering.md`, `lib/native/bytes_level/bytes_level_lower.hthr`).
Nodes, leaves, sequences and branches are lowered and proved; calls, loops,
the routine's frame, the done clause and the world are filed (below).

- *The clause and the instance.* A node's code is proved as
  `function_ir_lower_calls`' `EmitsBy` at state type `Heap` and the clause
  `heap_in` (the heap injected under the one lending), whose law is
  `Loan::stable_injected`. Sequences are `may_emit_by_seq` and branches
  `branch_emits_by` at that instance, cited as stated: the generalisation
  missed nothing these needed.
- *One valuation per scope.* `EmitsBy` states the register file against one
  FunctionIR valuation for a whole body, as FunctionIR's single-assignment
  functions have it. The bytes level's locals change as it runs, so the
  lowering's theorem is over a valuation that agrees with the locals at every
  node (`Locals::Agrees` at validity's kinds; `RunAgrees` along a leaf): a
  word id is its word at every width, a reference id its target's address.
  The kind never reaches the register file. Such a valuation exists for a run
  exactly where no id is bound twice in a scope (a routine's body, a loop's
  pass), which the lowering is to check, as FunctionIR's programs already
  are; that existence lemma is the first thing the routine theorem needs.
- *The bridge.* Each node's step, where the valuation agrees before and
  after, is its facts at the valuation (`Instr::holds_of`): validity's kinds
  make a word node's operands the valuation's and a reference's word its
  address. So a word node on a reference, a store cutting a reference and a
  load of an undefined byte have no facts and no theorem applies, not merely
  no meaning.
- *A load and a store are the machine's.* Chosen here: a word load reads
  its bytes as a word, zero above them (`word_of_bytes`), and a store writes
  a word's low bytes (`low_bytes`), as `MOVZX`, `MOV r32` and `MOV` read and
  as the byte, doubleword and word stores write. The language had read a
  store's value at `8 * bytes` bits of the valuation and a load as a number:
  a value's narrow widths are not its word's low bits in general (a right
  shift at 8 bits is not the low byte of one at 64), so the old store could
  not be lowered from the register holding the word. Probes are unchanged.
- *Each node one instruction*: `MOVZX`, `MOV r32`, `MOV r64` loads through
  the register holding the reference (`Injected::byte_read`, `dword_read`,
  `word_read`), the same `MOV` for a reference (`ref_read`), a byte,
  doubleword and word store (`Loan::store_injected`) and a reference's
  store as a word's (`store_ref_injected`). An offset is a word node, the
  `ADD` of the address and the amount (`offset_adds`), lowered by
  `lower_nodes`. Two-byte accesses (no `MOVZX r, word` in the model) and the
  typed copy are refused.

**What follows.** The rest of the lowering under `Site::Meets`
(`issues/bytes-level-lowering-routines.md`, `bytes-level-lowering-loops.md`,
`bytes-level-lowering-world.md`), the translation of FunctionIR programs
and the comparison over `crates/linked`'s exports
(`issues/bytes-level-translation.md`), and the passes
(`issues/bytes-level-passes.md`).

## 18. The world, termination, and level 2 fixed (2026-11-25)

Round six of the design review. Where this section and §15.4, §15.5 or §17
differ, this section holds.

### 18.1 One meaning, clocked

A run is a family over fuel with four outcomes, and the world is in its
state beside the heap:

```heather
record Answer { words: List<Value>, heap: Heap, io: Io }
inductive Ran { Done(a: Answer), Exited(status: BitVec(64), io: Io), Going(io: Io), Stuck }
fn run(p, n: Nat /* fuel */, f: Nat, args: List<Value>, heap: Heap, io: Io) → Ran
```

`Going` is "not finished at this fuel, and here is the world so far";
`Stuck` is "no meaning". The run is monotone in fuel. "No answer" for a run
that does not end would conflate divergence with undefinedness and lose
what a diverging run wrote; a coinductive run would make every pass a
proof up to silent steps. This does not change the surface's meaning (an
unmeasured loop over the world is `Io → Partial<…>`, Minus 2026-11-03): the
reflected levels are that meaning observed at a count, and one pin theorem
per function connects them.

- **A pass's theorem has three clauses**: every finished run of its input is
  one of its output at some fuel; every history the input reaches while
  going is a prefix of one the output reaches; and the converse unless the
  input is stuck.
- **Every loop is a plain loop**: no bound operand, counter or exhausted
  output at the bytes level. The fuel gives the meaning's totality; that a
  program ends is a separate fact, from its measure. The two loop meanings
  (bounded in FunctionIR, iterated in `Source`) become one.
- **Calls spend fuel**, so a program is tied by fuel and not by levels.
- **Fuel is the step meter**: a time bound is "done at a fuel below a
  bound", the judgment of §15.9 over steps.

### 18.2 The world

- **Level 1**: `Io` as built, a type that may not be duplicated or dropped.
  A system call is an operation whose meaning is `Io::call`. `write` and a
  path take a read view. `read_into` takes its window by value and answers
  the filled window and a count, or a failure: **a failed read takes the
  window**, so the place must be written before it is read again. The
  meaning never sees what a failed read left behind, so the copy through a
  scratch range that every read pays today goes, and the Linux model does
  not change. A descriptor is plain data; a file that must be closed is a
  library type that may not be dropped, around the word.
- **Below**: the world has no block and no bytes. A system call is a node
  whose meaning builds the command from words and the heap's bytes at a
  window, asks the world, records the exchange and decodes the answer. A
  renaming of blocks is the identity on the world, since a command carries
  bytes and words and never a reference (the kind check enforces it).
- **A byte is plain, part of a reference, or undefined.** The injection
  constrains only the defined; a store defines; a load of an undefined byte
  has no meaning and owes "defined", which the place state supplies. A
  fresh block, a dead one and a window after a failed read are undefined.
- **The machine**: one step lemma for the system-call node, whose
  conclusion holds for every answer and resumption the Linux model allows.
  The whole-program theorem: at every fuel, the trace the code has
  performed is the history the meaning has reached, and an exit ends it.
- **Deleted with the tools' move**: the program compiler and its scratch
  range, `Source` and its denotations, the builder, the effect terms.
  **Kept**: `Io`, the world's model, the machine's Linux model and its
  determinism, the image and start-up, the contract record, and `Partial`
  with `Io::against` as the surface's meaning and the bridge to a spec
  written as a tree.

### 18.3 Level 2, fixed

- **No intermediate `Safe`.** Both experiments proved one theorem: a
  verdict and its residuals give agreement of the run and the meaning,
  stated as a function's safety (`FnSafe`). So §15.4's `check_sound` and
  `sharing_sound` are one theorem, stated at level 2.
- **The heap** is a list of blocks, each live with an object or dead; a
  fresh block is the next index. An object is the universal value of
  `value_steps.hthr` with three more leaves: an owning reference to a
  block, a view (a block and selectors), and a taken cell.
- **Operations**: make a block; load and store at a selector; narrow a
  view; a death (the block and every block it owns); calls, primitives and
  system calls. Anything not defined is stuck.
- **There is no plan beyond the annotation.** An in-place operation's result
  is its operand's name with a store; a fresh result makes a block; a view
  narrows; a write-back is nothing; a listed death of an owner is a death.
  The experiments' buffer plan existed because their file was allocated in
  advance.
- **A level-2 value reads a level-1 value** by resolving owning references
  and views through the heap, with the block count as fuel since ownership
  is a tree.
- **A function's safety**: its answer reads the meaning's; each written
  parameter reads the meaning's value after (the eager write-back); the
  heap is unchanged outside what was lent, which for a window is one lens
  equation; a returned view's selectors extend its parameter's; its events
  are well formed. A postcondition is one more field.

### 18.4 Three things not yet tested, and their tests

1. **Discharging a residual from the source's own proof.** Every experiment
   used a hand-written term. For a real function, a hypothesis about the
   function's variables must become the obligation at the reflected
   environment, through the pin, at a cost the kernel accepts, by a term a
   generator could write. Test: one function with a found proof, its body
   written by hand in the checker's language, its residual discharged from
   its own hypothesis.

   **Result (2026-11-25, `lib/lang/ownership/site_facts.hthr`, probes in
   `lib/_tests/lang/ownership/site_facts_tests.hthr`, log in
   `issues/ownership-residuals-from-source-proofs.md`): it works, and the
   discharge is the source's proof itself.** A read under a parameter proof,
   an index read into a `let`, a write apart from a held view under an `if`,
   and calls passing the caller's proof on (directly, and over a read) each
   have a pin by `refl`, a discharge, and their safety from the checker's
   once-theorem with nothing else. Per site the term is the proof the source
   has there (a parameter, `decide_true(e)` of the enclosing `if`'s convoy
   equation, a `squash` of either), placed at the residual's statement, and
   the kernel sees the statement at the reflected words as the hypothesis's
   at the source's locals by running the meaning. A `let` costs nothing: the
   elaborated `let` is its value, and the reflected word evaluates to the
   same term. That needed four things the checker's module does not have,
   added beside it: residuals stated as the proposition the source writes
   (a bound as a squashed `<`, a callee's precondition as written) over the
   meaning's final state, not over its words alone; a precondition that
   reads the parameter as well as the words (the arena's `read` cannot be
   stated otherwise); open words spelled from their length, one lemma for
   every function; and a branch whose meaning is the same convoy the
   source's `if h:` elaborates to. Two things are not conversions.
   Apartness is a Boolean verdict over a disjunction, spelled with the
   view's offset (`0 + k <= j` against the source's `k <= j`), so its term
   is a typed `let` and `omega` over the hypotheses in scope, which reflection
   must therefore keep per site, not only the argument at the site. And
   cost: one residual costs a linear pass over the body, but a tuple of
   residuals, each converted on its own, runs the meaning once per residual,
   which is quadratic for a residual per statement (ten million steps at 256
   statements). The design's own fix measures linear: restate the residuals
   over the source's terms and move the whole conjunction by one ascription
   (one conversion, which shares the meaning's evaluation). So a generator
   emits, per function, the restated conjunction and its proof tuple, and
   per site only the proof term and, for apartness, the hypotheses in scope.
   What the experiment could not do in this fragment: a callee whose
   precondition reads its lent window (`Pre` is over the call's words), a
   reader answering a word (no such call), and an `if` whose test reads a
   word the body bound (that is the checker's own branch, which the joins
   work brings).
2. **Loops.** A place state stable at the loop's head in one pass;
   residuals that hold at every pass and not "at the words the meaning ends
   with"; soundness by induction on fuel. Test: one loop added to the
   checker's fragment, writing an element while a view of a later window is
   held, its residual from the loop's guard.
3. **Where a growable container lives: settled by Minus, it is what
   `datarepr` is for.** Source code is written over the mathematical type
   and its interface (`List<T>` and its operations), and a representation
   (a vector, a small vector, a linked list) is chosen for it; a function
   "just uses the List API" whatever the representation. So there are three
   tiers of type, not two: the specification type, in which programs are
   written and theorems stated; a representation (`docs/native/datarepr-design.md`:
   a carrier, an abstraction function, an invariant, an implementation of
   each operation with its refinement theorem), which is ordinary code over
   records and is what the checker and level 2 see; and a layout. Capacity
   is a field of a representation and is not in the specification, which
   is what §10.6's "a fact about a home" was reaching for. Only the author
   of a representation writes code over the record. A representation may
   fail where the specification does not (a full fixed-capacity vector;
   memory): that is its operation's precondition, a residual or the room
   premise. To be designed: how a representation is chosen and recorded in
   an interface; a function general in its representation; how a place in
   the specification (an element, a window) becomes a place in a
   representation; and where the transfer sits relative to the checker.

## 19. The representation tier (2026-11-25)

Round seven of the design review, after Minus's answer in §18.4 item 3.
What `docs/native/datarepr-design.md` becomes in this design. Nothing here
is built; the library's only `datarepr` declarations are `I8` to `I64` for
`SInt(n)`, and today's containers (the arena's vector, the word map) are
hand-written representations: an abstraction function, an invariant record
and one theorem per operation.

### 19.1 Where the transfer sits

Before the checker. There is one reflected language, read over two tables
of operations, the specification's and a representation's. The transfer
rewrites each object binder's type from the specification type to the
carrier, and each interface call to that representation's implementation.
The checker, level 2 and everything below see only the result, so level 2
stays structural, a representation's operations are checked code, and
whether an operation is in place and what it costs are facts about an
implementation.

The transfer's theorem is proved once over the reflected language, by
induction on the term with "the representation environment abstracts to
the specification environment" as its invariant, from a table saying each
implementation refines its operation and keeps the invariant. (The
existing generator emits that induction as text per function, because it
works on unreflected source.) A level-2 value stands for a specification
value when it reads a carrier value that satisfies the invariant and
abstracts to it; the end theorem is a function's safety (§18.3) with that
in place of reading, about the function the user wrote. The invariant
enters as a precondition and a postcondition.

How what is stated at the specification crosses: a mode is the same mode
at the carrier's type; a region `xs[a..b]` is the representation's place
for that selector, or the whole object where it has none; a found proof
`i < xs.len()` becomes the residual at the carrier by one rewrite with the
length's refinement; an apartness is decided on the translated steps; and
"in place" is the implementation's result origin, so a representation
whose `set` copies makes a demand for in place a refusal that names it.

### 19.2 Places

A representation declares, for each kind of selector it supports, a
translation into its own steps and two equations through the abstraction
function (the place's read and its write agree with the specification's):
for a vector, an element is the items field then the element. This is the
refinement of the selector's read and write, stated on `Steps`, and not a
new kind of fact. The checker works on the translated steps, so fine
apartness is structural.

A place with no constant-time form (an element of a linked list) is an
accessor: a checked function answering a view, with the same two
equations. The checker does not see through it, so its region is the whole
object and its cost is its body's. A place the representation has neither
for is refused, naming it and the written copy.

A window of a vector is itself a representation of the list, a slice with
no `push`; so two representations of one specification type in one
function is the ordinary case. Beyond refinements and these, a
representation owes a bound on its size by the specification's length
(§15.9).

### 19.3 Choosing one, and functions general in it

A representation belongs to an object and is fixed where the object is
made: by the constructing operation, by `as Vec` on a binder, parameter or
field, or by a default per specification type. A function with no `as` is
general and is specialised per representation at each use, the instance
keyed by the function and each object parameter's representation; no
dispatch at run time and no inserted conversion.

For that to leave an interface stable, **the specification's interface is
declared, with modes**: each operation with its meaning and its modes
(`set` takes its list; `get` reads). A representation implements at those
modes; one that copies does not use the licence it was given. The sharing
signature of §15.8 splits into a general part (modes, regions at
specification places), which is all a caller's checker reads, and a part
per instance (result origin, cost, the code).

### 19.4 Failure

Three sources, none an outcome type. A failure the input determines within
a representation is a precondition of its implementation, so a residual at
the call: a fixed-capacity `push` owes that there is room, discharged by a
found proof, the user's, or a test the user writes, which is definable at
the specification level because a fixed capacity is a static parameter.
Memory is the room premise: a growable `push` is total and its growth is a
`new`, entering the cost. A program that must handle exhaustion uses a
specification type that has the outcome. The existing design's inserted
check that bubbles an error goes, since the specification does not define
its failure (§14 item 6).

### 19.5 What changes in `datarepr`

Kept: a carrier, a total abstraction function, an invariant; the open
registry of implementations keyed by representation and operation with
their refinement and invariant theorems; keying on the declaration; no
inserted conversion; nothing trusted. Surplus: the outcome path;
constructor images as required fields (a vector's `Cons` is a prepend
nobody wants; an image is one more operation, implemented where a program
constructs that way); the fold anchor as an obligation (kept as a derived
lemma for transferring a structurally recursive library function); and
with those, the per-inductive record generation, since the record is the
same three fields for every specification type; and the per-function
transfer text, replaced by the once-theorem. Missing: places; the declared
interface with modes; a representation parameterised by its elements'
(a vector of buffers); the sharing class and copy fact of a carrier; a
death (structural by default, or declared where a representation owns
things that are not owning cells, which is the one place checked code runs
at a death); a cost and the size law; and clone as an implementation of
the identity, `abs(clone(r)) = abs(r)`, of which an exact clone is the
case of an injective abstraction.

### 19.6 The experiments, and the test

The four checker experiments are the slice representation (the
abstraction function the identity) with the transfer left out; nothing in
them is invalidated. Not yet exercised: an object that is a record, an
operation that changes length, growth, an invariant as a precondition and
postcondition. A clone's meaning at this tier is its implementation's, so
"a clone is equal" must not harden in the checker.

The test: `fn bump(xs: List<Nat>, x: Nat) → List<Nat> { let ys = xs.push(x);
ys.set(0, ys.get(0) + ys.len()) }` by hand through the checker's fragment
at two representations, a fixed-capacity array with a length and a growable
one over a block. It should show the transfer's theorem stated once and
instantiated twice; at the fixed one, only capacity and bound residuals,
each from a specification-level hypothesis by one rewrite; at the growable
one, no residual and the growth in the cost; and a caller holding `&xs[0]`
across the `push` accepted at the fixed one (apart from what `push` writes)
and refused at the growable one. It refutes the tier if the transfer needs
an induction per function, if a specification-level proof cannot reach a
representation-level residual mechanically, if the two instances need
different modes at the specification level, or if the abstraction through
the universal value costs the kernel too much per step.

### 19.7 Minus on this tier, and what it settles (2026-11-25)

Minus: common interfaces will just use `List<T>`, while code may name a
concrete type, `Vector<T>` or `LinkedList<T>`; for inferring a
representation he leans typeclass-like; he is unsure about a declared
"List interface", which would be a `ListLike` class by another name; and
`datarepr` may be altered where that is the better design.

Settled from that, as the owner's reading:

- **`Vector<T>` and `LinkedList<T>` are ordinary library types** with their
  own checked methods. Code that cares names them, and then nothing is
  inferred: ownership is fully determined by what is written.
- **A representation is an instance, and so is an implementation.** A
  class instance says a carrier represents a specification type (the
  abstraction function and the invariant); an instance keyed on an
  operation and a carrier says how that operation is implemented, with its
  refinement. This is the pattern `Compile(f)` already uses, an instance
  keyed on a function, and it is found by the resolution the language has.
  There is no declaration form of its own, no required constructor images
  and no fold anchor (§19.5's surplus goes; the images and the fold are
  ordinary instances and lemmas where wanted).
- **A representation for a `List<T>` is chosen as an instance is**: stated
  (`as Vector`), forced by what the value is passed to or made by, or the
  specification type's default instance. Code over `List<T>` is the casual
  tier: it runs at the default with nothing written.
- **There is no declared List interface.** "The List API" for a
  representation is whichever functions on lists have an implementation
  instance for it; a function with none is transferred through its own
  body. A function general in its representation is checked, and its
  sharing signature recorded, per instance. This replaces §19.3's "the
  specification's interface is declared, with modes".

What that last choice costs, so it can be revisited with evidence: an
ownership refusal in a general function can appear only at one
representation, as an error in a template does, where declared modes
would check it once. If that bites, modes written on the list functions
themselves are an annotation that adds the once-check without changing
what code is written against.

The difference from a `ListLike` class is what a signature says. A class
abstracts over the type in the signature: `fn f<C: ListLike<T>>(xs: C)`,
with theorems about `C` through its laws. A representation leaves the
signature alone: `fn f(xs: List<T>)` is a function on lists, usable in
mathematics and proved about as one, with the instance found behind it.
The machinery (instances and laws) is the same, and a `ListLike` class is
an ordinary thing a library may also define.
