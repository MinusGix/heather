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
- A death removes the viewer, or restores `whole`.
- A join is the meet, with regions coarsened. A type that may not be
  dropped may not be `gone` by weakening.
- Overlap is decided on the places' steps where they are closed; otherwise
  it is a residual obligation. A key access emits `Valid`; an index its
  bound; a call the callee's precondition.

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
- **`placement_sound`** (once): layout and placement take level 2 to
  FunctionIR with live blocks in disjoint windows. The separation algebra
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
address; the meaning is unchanged by renaming blocks. `dead` is a fact with
no code, emitted at a death and read by placement. A stored view, a view
chosen by a test, and a view returned into a caller's record are all a
`Ref` held as a value.

This level stands above FunctionIR, which is bytes with static buffer
numbers. One new pass joins them: steps become byte spans (`Part`,
`Stored`) and each live block gets its memory.

**What a `Ref` becomes below** (lean: the third; Minus to decide). Three
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
`Loan` extended across an allocation. The first is an instance of the third
with one supply, so level 2 and `placement_sound` are written against the
general interface.

`new` names no supply in the source or the meaning for an owned object:
identity first appears at level 2. (Lean; Minus has not settled it.)

**The allocation policy is not a design commitment.** For memory obtained
at run time the checked thing is an allocator, and `placement_sound` is one
theorem over any allocator satisfying laws: a block it answers is disjoint
from every live one and large enough; a freed block leaves the live set;
with enough room it never fails. These are the arena's `alloc_fresh` and
`alloc_below` with a `free`, stated in `Held`. A frame plan decided at
compile time is the case discharged by a plan checker. So the first build
may be the simplest allocator.

**What is a commitment** (Minus to decide):

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

Still open:

1. How memory bounds are stated, found and discharged at an export.
2. The design of deaths: what code a type's death is, where it may be
   elided, and the bulk forms.
3. That the inference rule's answer checks whenever any annotation does
   (§15.3): argued, to be proved with the judgment.
4. Whether an owner may read a part it has lent to write, which eager
   write-back would make sound. Kept refused at first.
5. The order in which the levels are built and the customers ported.

### 15.8 What a signature records

Per function, in the module's interface: its region parameters (and for
each whether an erased owner goes in and out); per parameter its class,
its mode (take, read, write), the parts it may write, and what places its
type's regions stand for; for the result its class and whether it is fresh,
is a parameter, or is a view of places of parameters; and whether it
allocates. Residual preconditions are not extra data: they are the proof
parameters in the kernel type. A caller's checker reads the modes to step
its place states across the call, the result's origin to know what is
frozen or out while the result lives, the parts to emit `Apart` against
views it holds, and the name of the callee's safety theorem to cite. It
reads no summary of what the callee keeps.

The inferred fields (take or read, fresh or a parameter, allocates) are in
the interface, so a body that flips one changes the interface and its
importers are checked again: a caller that used `v` after `f(v)` is refused
when `f` starts consuming it. A callee's plan, deaths and internal
residuals are not in it.
