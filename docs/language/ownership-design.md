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
  residuals are owed on its side of the test, and what follows the join
  is owed in each arm (the verdict is a tree in the body's shape, below).
  A type that may not be dropped may not be `gone` by weakening.
- Overlap is decided on the places' steps where they are closed; otherwise
  it is a residual obligation. A key access emits `Valid`; an element read
  its bound; a call the callee's precondition.
- A residual is the proposition the source writes at that site, read in
  the state the site reads (§14 item 1): a bound is a squashed `<` on the
  length of what the read reads (one per element read, through a view
  too); a callee's precondition is stated at the value the call lends (the
  object, a loan's window, or the owner with the slots of a collection of
  references) and the call's words; two windows apart is the disjunction of
  its two sides, the first ending before the second or the second before
  the first, each spelled as a source spells it (`k <= j` for the window
  `0..k` before `j`, `j < lo` for the element after), so the source's
  hypothesis is the discharge by conversion and its proof names the side.
  Where the checker cannot know the side, it owes the disjunction; a
  source's proof is on one side. The verdict is a tree of residuals in the
  body's shape, and what a function owes is one proposition along its
  meaning: each statement's residuals at the state it reads, a branch's
  under its test (the shape of the source's `if h:` proof). Writes owe no
  bound in this fragment: the source's `update` is total; the bytes level's
  store does need one, which is still to be stated.

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

*Site facts in the checker* (2026-11-25,
`issues/ownership-site-facts-into-the-checker.md`). The fifth experiment's
additions (§18.4 item 1) are statements of the one checker, re-expressed
rather than added beside it, and its probes run against it
(`site_facts_tests.hthr`). What changed, each once:

- *The words.* The meaning's and the run's words are an `Env`: the
  parameters read by position and the words the body bound newest first,
  with their count, so a parameter and a recent word are read in constant
  time. The pin, which read through a snoc list by position, was quadratic
  in the body; it is linear now.
- *Residuals.* A residual is the proposition the source writes at its site
  (§15.3): a bound per element read (`Inside`, through a view too), a
  callee's precondition at the value the call lends (`Pre`), two windows
  apart as the disjunction of its two sides spelled as a source spells
  them (`Apart`). It is read in the state its site reads, along the
  meaning, not in the final state: with the parameter a place there are no
  versions for a final state to hold, and arms bind different numbers of
  sites. The verdict is a tree in the body's shape (`Owes`), and a function
  owes one proposition (`Owes::Due`): residuals at their sites, an arm's on
  its side of the test, what follows a join in each arm. `Under` went with
  the final-state reading.
- *Branches.* The meaning carries what follows a branch into each arm, the
  convoy a source's `if h:` elaborates to, so a function whose `if` ends it
  pins by conversion, and its arms' residuals are discharged by
  `Bool::cases` of the `if`'s evidence. One `If`, no `Branch`.
- *Contracts.* A pre- and a postcondition are of the parameter's value (its
  object and the slots it is lent) and the words; a postcondition is of the
  whole answer. Owing every read's bound made both necessary: a read
  through a view a callee answered is bounded by the callee's promise about
  its view, a read through a lent reference by a precondition over what was
  lent, and a read after a call by the callee's promise about the object it
  hands back. `CallGet` calls a reader answering a word.
- *Proofs.* The theorems whose statements changed are re-proved, as stage
  lemmas; nothing is stated twice. The module's fresh elaboration and its
  dearest declarations (the window lemmas) are as before.

Costs, as shapes, at doubling bodies with a residual at every statement:
the verdict, the pin (through parameters or a chain of lets) and the
discharge as one ascription of the restated conjunction are linear in the
body; the discharge as a tuple converted component by component is still
quadratic, so a generator emits the restated form, as a statement and proof
built by recursion (a literal conjunction is linear in the kernel but
superlinear to elaborate). Owing every bound has a price for programs: each
read needs its bound from the caller, and a program whose callee answers a
view composes its depths from two (depth zero answers an empty view).

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

**The fourth part: routines, calls and the done clause** (2026-11-25,
`issues/bytes-level-lowering-routines.md`; `bytes_level_scope`,
`bytes_level_routines`).

- *One valuation per scope, by a check.* The lowering refuses a routine
  whose scope binds an id twice along any path (`Body::fresh`: both arms of
  a branch may bind one id, nothing after the branch may bind it again).
  A checked run then changes only the ids it binds (`Frames`), and its
  final locals lowered (`Locals::lower`: a reference its address) are a
  valuation agreeing with the locals at every node (`Locals::Shows`,
  `agrees_of`); `Body::holds_of` turns the run into the facts
  `Body::emit_emits` takes. The invariant carried is that a word id holds
  no reference and a reference id one (`Scoped`).
- *A call* is FunctionIR's call code (`File::emit_call`, no buffers lent),
  proved by `File::emit_call_steps_by` and `call_step_by` at the heap's
  clause, cited as stated: the callee's contract is its routine's return
  (`RoutinePre`, `RoutinePost`), the answer at the fuel the run gave the
  call (`run_answers`). Its facts are `CallLands`: the arguments lowered
  are the valuation's words, the answer's words land at the results.
- *A routine with no results answers zero in RAX* (a `Const` into an id
  its scope never binds, `ids_past`), because FunctionIR's call and
  function theorems have a word in RAX: the contract's `Site::Returned`
  says nothing of RAX then, so this is a choice of the lowering's own
  callee contract, not of the language's meaning.
- *A routine* is `function_runs_by` at the heap's clause around
  `Body::emit_emits` (`routine_runs`), FunctionIR's frame arithmetic and
  `Site::returns_by` around that (`routine_body`, `routine_returns`).
- *The done clause* (`lower_program_meets_done`): `Site::MeetsDone` for
  every routine of every program `Program::lower` returns, at every fuel,
  by one induction on the fuel (`program_returns`): at `n + 1` a routine's
  calls are answered at `n`, so the callees' code meets them by the
  hypothesis. A run done without a system call leaves the world alone
  (`program_quiet`), so the code performs the answer at no system call.
- *Recursion is refused.* The meaning ties routines by fuel, so a routine
  may call itself; but `Site::Entering` fixes the room below the return
  address (`rooms(f)`) for every fuel, and a routine that calls itself
  needs room growing with the depth the fuel allows. So a routine calls
  only those below it, as FunctionIR's functions without levels do, and
  the room table (`routine_rooms`) is each routine's largest frame over its
  callees' rooms.
- *The plain loop* (`issues/bytes-level-lowering-loops.md`): its facts are
  its passes at some fuel (`PassesHold`), each at a valuation of its own,
  since a pass is a scope of its own from its parameters. Its code is the
  inputs moved into the state's registers, a head H, the pass, the exit
  bit's test (to C where clear), the next words moved in and a jump to J,
  at C the same moves and a jump to H, then J (`plain_done`). The passes
  are `Site::loop_iterates` on the run's fuel with `Stack::LoopAt` at the
  head, a pass `loop_body_runs_by` and the turn `loop_turns`, cited as
  stated; leaving is the loop's own (`plain_leaves`, the bounded loop's
  `loop_leaves` without its flag). The ids a pass binds are counted bound
  in the scope around the loop, so the routine's spare id is none of a
  pass's and nothing after the loop rebinds one.
- *The exited clause* holds of every program the lowering returns, and
  vacuously: it lowers no exit and no system call, so its meaning never
  exits (`program_no_exit`, `lower_program_meets_exited`). What remains of
  the world (`issues/bytes-level-lowering-world.md`): the system call, which
  needs the frame, call, loop and function theorems in the claim form
  `Site::Performs` (all are over `Site::Moves`), and the going clause, a
  statement about every state the code reaches, which none of the
  existential theorems gives.

**What follows.** The rest of the lowering under `Site::Meets`
(`issues/bytes-level-lowering-routines.md`, `bytes-level-lowering-loops.md`,
`bytes-level-lowering-world.md`), the translation of FunctionIR programs
and the comparison over `crates/linked`'s exports
(`issues/bytes-level-translation.md`), and the passes
(`issues/bytes-level-passes.md`).

### 17.7 The contract tracked on fuel (2026-11-26)

§17.6 left three things wrong with `Site::Meets`. Its going clause
quantified over every state the code reaches, which no region theorem
proves. The region theorems were over `Site::Moves`, so a region with a
system call could not cite them. And the room below a return address was
one number for every fuel, so recursion could not be stated. Round
`issues/call-contract-tracks.md` fixes all three. Its pieces, in the order
they landed:

**Fuel where the machine steps.** The fuel is spent where the code takes a
step it can count. A loop's first pass runs at the loop's own fuel, and
each turn back costs one (`loop_run` = `loop_pass` at the fuel, then
`loop_later`, whose `Succ` case is the turn). A call costs one, as before.
These are the two places where a fuel step is a machine step: a turn's JMP
back to the head, and a call's CALL.

**The claim, with a lower bound.** `Site::Performs` (in
`x86_64_stack_runs`) is generic over a world type `W` and a `Kernel<M, W>`,
which says what a system call resumes to (`resumes`, monotone). Beside the
count of system calls it carries `least`, a lower bound on the machine
steps taken. Under bind, the counts and the bounds add (`performs_bind`).
Linux is one kernel (`Site::linux_kernel`), and `Site::LinuxPerforms` is
the claim at it. The quiet kernel `Kernel::none` resumes nothing.
*Differs from the design:* `Performs` lives with the stack runs, not the
contract. The generic theorems' modules cannot import the Linux world
(hand-listed module sets in `crates/elab/tests`), nor the contract (its
`Answer` and `Value` collide with FunctionIR's).

**The generic theorems in claim form.** Each is stated once over
`Site::Claims`: a kernel, a world clause `World: S → W → Type`, at most
`calls` system calls, at least `least` steps. Those are `EmitsClaim`,
`may_emit_claim_seq`, `branch_emits_claim`, `call_step_claim`,
`File::emit_call_steps_claim`, `function_runs_claim`,
`Site::loop_iterates_claim` and `ReturnsClaim`. Their former statements
(`EmitsBy`, `may_emit_by_seq`, `branch_emits_by`, `call_step_by`,
`File::emit_call_steps_by`, `function_runs_by`, `Site::loop_iterates`,
`Site::returns_by`) are one-line instances at the quiet kernel, the world
`True`, no system call and bound zero, so every certificate is unchanged.
Only two lemmas add a counted step: `claims_jump_item` (a JMP) and
`claims_call` (a CALL). The two kernel-write facts the claims need come
from the Loan, in the contract module (`Site::window_keeps_code`,
`Site::resumes_resident`). No `ClauseStable` law for kernel writes was
added, since one instance needs it.

**One clause.** `Site::Tracks` says that at every fuel `n`, from the entry,
the code performs the state read off the meaning there (`Site::Reached`):

- *Done* is returned (`Site::Returned`), at least 0 steps.
- *Exited* is at the exit call with its status, in the exit's world, at
  least 0 steps.
- *Going(o)* is any state in world `o`, at least `n - 1` steps
  (`going_least`).
- *Stuck* is nothing.

The clause asks `io.Answerable()`, and it is the only clause that uses it.
`Site::MeetsDone` and `Site::MeetsExited` are its readings
(`Site::tracks_done`, `Site::tracks_exited`).
*Differs from the design:* the going bound is `n - 1`, not `n`. The first
CALL of the chain is the caller's instruction, executed before
`Site::Entering`'s state.

**Entering.** `Site::Entering` takes the Loan and the meaning's own law of
what it may write (`lent: Type`; the bytes level's is
`blocks.Lent(spans)`) as hypotheses of the clause, for one lending over the
whole run. Its room premise is `room(f, peak(n, f, args, heap, io)) <= i`,
a table by routine and call depth.

**Room by call depth.** `Body::peak` is the deepest chain of calls a run
enters, defined by the run's own recursion beside it in `bytes_level.hthr`
(`program_peaks`, `run_peak`; `run` is unchanged). A call node entered
counts one plus its callee's chain at the fuel the call gives it.
Sequences, branches and passes take the deepest of what they run, each
part from where `run` leaves the one before.

The lowering no longer checks room. Its theorem holds under every table
satisfying `RoomLaw`: at every depth `p`, each routine's largest frame fits,
a call's 24 bytes fit below it, and its callees' rooms at `p - 1`
(`rooms_below`) fit in what is left. `depth_rooms` is lawful for every
program (`depth_rooms_lawful`). A call may go to any of the program's
routines, itself included (emission's `bound` is the routine count).
*Differs from the design:* the old `routine_rooms` is deleted, not kept as
an instance. For an acyclic program the depth table is constant past the
program's height, but I have not proved it equal to `routine_rooms` there.
Probes: `down` (`bytes_level_routines_tests`), a routine that calls itself,
is done at fuel 3 from 2 with `run_peak` 2 and is tracked. The control
`down_no_constant_room` shows that no table constant in the depth is
lawful for it. The run-time out-of-room outcome (the old compiler's exit
139) has no meaning here: `issues/bytes-level-lowering-recursion.md`.

**The lowering, re-proved to `Tracks`** (`lower_program_tracks`), by two
inductions on fuel:

- *Done* is `program_returns`, as before. Its callees are answered at the
  caller's depth less one (`peak_answers`), so their room is the table's
  there.
- *Going* is `program_goes`. A routine still going at fuel `n + 1` makes at
  least `n` steps from its entry: the entry's loads and frame
  (`function_enters_claim`), then its body's code going
  (`Body::emit_goes`). The latter is by induction on the region: the
  CALL's step and the callee's run going on (`call_heap_goes`, with a
  hand-off kernel `into_callee` that turns the call sequence's claim into
  one of reaching the CALL); the arm the bit picks (`branch_heap_goes`); a
  loop's passes, each turn's JMP counted (`plain_passes_goes`). The going
  facts are read off a run going at a valuation of the locals where it went
  on (`Body::goes_of`). A run still going leaves the world alone
  (`program_going_quiet`), so the world is the entry's.
- *Exited* is vacuous, since nothing is lowered that exits.
- *Stuck* is trivial.

**The going clause from `Tracks`, once.** `Site::MeetsGoing` is restated
with the stuck alternative. Every world the code reaches in `j` steps
before it returns, where its room is there at fuel `j + 1`, is a prefix of
a history the meaning reaches at some fuel, or the meaning gets stuck at
some fuel. `Site::tracks_meets` proves `Tracks → Meets`. A path of the code
and `Tracks`' claim at fuel `j + 1` lie on one branch of resumptions, which
gives three cases:

- *Going there:* the claim's steps number at least `j`, so the path ends
  at or before the claim's goal and its world is a prefix of the goal's.
- *Done:* the returned state is not before the return.
- *Exited:* no step leaves an exit.

Determinism is needed only up to the state's defined components:
`step_respects_defined` and `syscall_excludes_step` between system calls,
`asks_meet` at one, `linux_answered_respects` for each resumption. These
are facts of the Linux instance, used in two lemmas (`performs_reaches`,
`performs_meet`). The lowering's `Site::Meets` is one line
(`lower_program_meets`); the recursive probe has it (`down_meets`). Why
this is stronger than `Sim`, and how it gives `RunsAs`:
`issues/linux-sim-divergence.md`, `issues/call-contract-whole-program.md`.

**Cost.** Stated as shapes: the claim lemmas are linear in their proof
terms. The region theorems' claim forms cost what their `Moves` forms did,
plus the counted step. The going induction mirrors the done induction
region by region.

**The exit lowered (round `issues/bytes-level-lowering-world.md`, item 1).**
`Exit(status)` is emitted as the status moved from the register the file
says holds it into RDI, sixty into RAX, and `SYSCALL` (`emit_exit`); the
code after it is never reached. `Body::fresh` accepts it (it binds
nothing). Its claim is not a third induction beside the done and the
going ones: the going development is generalised over how a run stops
short (`Stop`: `StopGoing(o)` or `StopExited(status, o)`, read off a run by
`Ran::stopped`), and going and exited are its two instances.

- The facts (`Body::Stops`, was `Body::Goes`) carry the stop: a loop out
  of fuel is `x.Zero()` (going: true; exited: false), an exit node with the
  word at its status is `x.Exits(w)` (going: false; exited: `w` is the
  status). Read off the run by `Body::stops_of` (was `goes_of`), whose
  only new case is the exit node.
- The code theorems (`StopsHeap`, `Body::emit_stops`, the loop, branch and
  call lemmas) claim the stop's state (`Stop::Reached`: going, any; exited,
  `LinuxSyscallAt` and `LinuxExits` with the status) with at least
  `x.least(fuel)` steps (going, the fuel; exited, none). The counting is
  three lemmas on `Stop::least` (`least_le`, `least_succ`, `least_mono`,
  and `least_pred` at the routine). The exit node's claim is `exit_stops`:
  the block, then the `SYSCALL` item fetched (`Site::item_fetched`).
- The routine and program inductions are `routine_stops`/`program_stops`
  at a stop `x`; `program_tracks` reads `Tracks` at `StopGoing(o)` for
  going and at `StopExited(status, o)` for exited. The world is the
  entry's (`program_stop_quiet`, generalising `program_going_quiet`), as
  no system call is lowered yet. `program_no_exit` and its lemmas are
  deleted.

The exited reading is no longer vacuous: the language's `exits` and an exit
inside a callee are compiled and tracked (`bytes_level_routines_tests`:
`exits_tracks`, `exits_meets_exited`, `exits_nested_tracks`, with their runs
exiting at every fuel that enters them); the control is an exit whose status
no id holds, refused.

**The world beside the heap (same round, item 2).** A region's code is
proved at the state `Now`: the heap, injected into memory as before
(`now_in`), and the world, which the machine's must equal (`NowWorld`).
Every region claim is at Linux (`Site::linux_kernel`), and so are the
callee contracts (`CalleesReturn` is a `ReturnsClaim` at Linux). A claim
counts the system calls it makes as the exchanges its world gained
(`calls_between(before, after)`), so the counts are read off the worlds and
never carried by hand:

- `Site::linux_performs_exact` (call contract): a Linux claim whose goal
  pins the world makes exactly as many calls as that world has exchanges
  past the start, since each resumption records one. `Site::claims_exact`,
  `emits_now_exact` and `claims_stop_exact` apply it. It is needed because
  a sequence's two counts are fixed across its middle state, but a loop's
  count (`loop_iterates_claim`) is existential.
- A sequence's facts say its middle history lies between the two ends
  (`Between`), and `emits_now_up` raises a part's count to the whole's.
  `holds_of` proves `Between` from `HistoryGrows`: a run's history only
  grows (`Body::run_grows`; a program's, `program_grows`).
- The done side (`Body::emit_emits`, `routine_body`, `routine_runs`,
  `program_returns`) is `EmitsClaim` at `Site::linux_kernel`. The quiet
  lemmas (`program_quiet`, `program_stop_quiet`) are deleted: the
  inductions carry the world in their facts, and `program_tracks` reads the
  done side by `performs_weaken` of the routine's `ReturnsClaim`.

**System calls lowered (same round, item 3).** `Sys(call)` is emitted as a
call's arguments are, then Linux's call: its three words move into RDI, RSI
and RDX (`File::call_moves`, judged by `outputs_check`), the call's number
goes into RAX, and `SYSCALL` follows (`emit_sys`). The file after holds the
result in RAX and forgets RCX and R11 (`sys_after`), which Linux may
clobber. `Body::fresh` accepts it, binding its result word.

- The facts (`SysCall::Lands`) are the reference's location, the window
  open (read) or the bytes read (write), the world's answer landed
  (`ReadLands`: the bytes put, or the window undefined; `WriteLands`), and
  the exchange recorded. `holds_of` reads them off the run
  (`SysCall::ran`, `lands_of`).
- The step is one claim through the kernel (`Site::claims_resumes`, a new
  generic lemma in `x86_64_stack_runs`). It holds for every answer the world
  gives and every resumption `LinuxResumes` allows (`sys_write_resumes`,
  `sys_read_resumes`). The language's words are Linux's (`count_word_linux`,
  `errno_word_linux`).
- The read's memory clause is re-established from the loan's window laws.
  - Inside a written span the code stays resident (`Site::resumes_resident`).
  - The bytes a read returns are the heap's put (`read_bytes_kept`, by
    `Loan::store_injected`).
  - For a failed read (`read_failed_kept`), the window is first stored
    zero, the heap's own bytes, then called undefined
    (`injected_undefining`). Whatever junk Linux left is then read instead
    by `Injected::undefined_change`. No law was added to `ClauseStable`.
- A read of no bytes at its block's end is allowed by the language, but no
  loan law reaches that address (every one asks `k < size`). It was a named
  hypothesis for a while. Now the stack's writes' own law covers it
  (`stack.empty`, `ByteWrites::EmptyRange`: a store of no bytes changes
  nothing and needs no room, `issues/byte-writes-empty-range.md`), and
  `injected_placed_nothing` keeps the clause there. The probe is
  `empty_read_meets`.
- `io.Answerable()` travels in the world relation: `NowWorld` is now the
  machine's world being the state's, every answer one Linux may give. The
  same holds for the routine's pre and post (`RoutinePreNow`,
  `RoutinePostNow`). Every region keeps the world's function, so each claim
  re-establishes it for free. `Tracks` supplies it at the entry. No fact,
  `holds_of` or loop-pass lemma carries it.

**Tracks with the world, and `RunsAs` (same round, items 4 and 5).**
`lower_program_tracks` and `lower_program_meets` cover every program the
lowering returns, system calls included, with no premise.

The probes found one completeness gap in the emission: the call's
`MOV RAX, n` and Linux's clobbers lost a value the file still held in RAX,
RCX or R11, so `echo`'s read count, which is live across its write, made it
unlowerable. Such values now move to a free R8 to R10 first (`sys_kept`),
judged by the same `outputs_check`.
The limit: there are three spares, and a spare counts as free only if
the file holds nothing in it. When fewer are free than there are values to
keep, the keep and argument moves no longer pair with their registers.
`outputs_check` then fails, `emit_sys` answers `None`, and the program is
refused (`Program::lower` returns nothing; there is no refusal message for
it yet). A value of a narrow or low kind is not kept either. Any later use
of it then fails to find a register, and the program is refused the same
way. Soundness never depends on the keep: only the moves the checks pass
are emitted.

The language's `echo`, `read_then_load` and `exits`, and a pass that writes
forever, are compiled and meet the whole contract. Each is read where it
applies: done, stuck, and going with the history as long as the fuel
(`bytes_level_routines_tests`).

`bytes_level_whole` reads `Tracks` as the Linux model reads a process.
- A Linux claim whose goal pins the world is `RunsAs` of the trace of the
  world's new exchanges (`Site::linux_runs_as`). Silent steps are the
  claim's machine runs, and each resumption is a `LinuxAnswered` call.
- So `Tracks` gives `RunsAs` of the meaning's outcome at every fuel
  (`Site::tracks_runs_as`).

What stands between this and `Sim` for a whole image is in
`issues/call-contract-whole-program.md`: the image's `_start`, the meaning
as an itree, and `LinuxValid`.

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
  are well formed. A pre- and a postcondition are propositions of the
  parameter's value as it went in (its object and the slots it is lent,
  whose values are the object's windows there) and of the words; the
  postcondition is also of the whole answer (its value, word and view).
  The callee's precondition is owed at the value the call lends (§15.3).

### 18.4 Three things not yet tested, and their tests

1. **Discharging a residual from the source's own proof.** Every experiment
   used a hand-written term. For a real function, a hypothesis about the
   function's variables must become the obligation at the reflected
   environment, through the pin, at a cost the kernel accepts, by a term a
   generator could write. Test: one function with a found proof, its body
   written by hand in the checker's language, its residual discharged from
   its own hypothesis.

   **Result (2026-11-25, built as `lib/lang/ownership/site_facts.hthr`
   beside the checker, now folded into it: probes in
   `lib/_tests/lang/ownership/site_facts_tests.hthr`, logs in
   `issues/ownership-residuals-from-source-proofs.md` and
   `issues/ownership-site-facts-into-the-checker.md`): it works, and the
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

   **Folded into the one checker (2026-11-25,
   `issues/ownership-site-facts-into-the-checker.md`).** The four additions
   are statements of the checker now, not a module beside it, and the three
   gaps are closed: a reader whose precondition reads its list is called on
   the caller's list (`CallGet`) and on a loan's window (`CallMut`), its
   precondition owed at the value lent; and a test over a word the body
   bound is the checker's `If` (`hop_le`). Two things changed from the
   experiment's form. A residual is read in the state its *site* reads,
   along the meaning, not in the final state: with the parameter a place,
   the final state no longer holds the value an earlier read read, and arms
   bind different numbers of sites, so no static index into a log would
   do. And apartness names its side: the residual is the disjunction of the
   two sides, each spelled as a source spells it, so `poke`'s `k <= j` and
   `after_read`'s `1 + xs[0] <= j` are their discharges by conversion
   (`Inl(h)`), with no `omega` and no hypotheses kept beyond the site's
   proof. The restated conjunction stays the shape a generator emits for
   many residuals (the tuple, converted component by component, is still
   quadratic); built by a recursive statement and proof it is linear and
   pays no elaborator cost.
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
4. **How a typed function meets the checker's meaning.** Result
   (2026-11-25, `lib/lang/ownership/coded.hthr`, probes in
   `lib/_tests/lang/ownership/coded_tests.hthr`, log in
   `issues/ownership-coded-values.md`).

   **The universal value as a native value tagged with its code keeps both
   headline results.** A code (`Shape`: word, sequence, named type) and its
   decoding by large elimination (`El`), a structure per named type (a
   record's field paths, or opaque), and `Dyn` (a code with a value of its
   decoding). The decision on codes and the cast are `fn`s that reduce to
   `refl` and the identity at closed codes, and `dec(c, c) = Inl(refl)` is
   proved by induction on the code, with no unique identity proofs.

   Over a list of user records and at an open type parameter, every pin
   tried is by `refl`:
   - a field of an element;
   - its functional update;
   - a generic element copy;
   - an `if h:` guarding a read;
   - a function that continues after its `if`;
   - calls passing a record and a window.

   Every residual (a bound, a callee's precondition at the value passed) is
   the source's proof by conversion. The cost is linear, 1.5 to 2.3 times
   the uncoded meaning's steps. The same read over `Val` is an induction per
   operation.

   What carries the result, and what it changes:
   - **The meaning reads totally and writes by modifying.** An absent part
     reads as its code's inhabitant, and a part is modified by a function.
     A read through a path's `Option` stops at a stuck `nth`, since the
     kernel does not do case-of-case. This is how today's `runtime fn`
     sources already read: `Vec::at` and `Bytes::at` carry the bound as an
     erased parameter and their bodies are total, 0 past the end. A read
     that consumes its proof costs one library lemma per site. For an open
     `T` the inhabitant can stay in the pin's statement, quantified: a
     write then pins by `refl`, and a read needs that lemma.
   - **A branch names its output.** Each output after the join is the
     convoy of the arms' values, and what follows runs once. A function
     that continues after its `if` then pins by `refl`, at linear cost.
   - **A step's fit is relative to the value it replaces.**
     `StepModelLaws` as stated cannot hold at `Dyn`
     (`Dyn::elem_not_lawful`), since a fit over the written value alone
     cannot say "the read part's code". With `fits(read, written)`:
     - any model lawful as stated stays lawful (`Val`'s included);
     - the decider's soundness holds by the same proof;
     - `Dyn`'s model is lawful from the structures' laws alone, with no
       unique identity proofs;
     - a single-sorted step lemma (a store through a view keeps every view
       the decider finds apart) follows from these laws without looking
       inside a code.

   **The level-1 interface should therefore be:**
   - values are `Dyn` over a type environment and its structures, which a
     derived instance per type supplies (field paths, their laws, an
     inhabitant);
   - the meaning's reads and writes are total and code-directed;
   - a branch names its outputs;
   - `steps.hthr`'s laws take the relative fit, changed once in place.

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

## 20. Where the experiments stop (2026-11-25)

Written by the coordinating session after the checker's rebuild
(`issues/ownership-site-facts-into-the-checker.md`) was read against §15 to
§18. Five experiments and one rebuild have been spent on
`lib/lang/ownership/call_check.hthr`. It answered what it was built to
answer, and it is not the checker: one object per function, a list of
numbers, windows as the only places, its own run over a file of lists, its
own world built by depth. Each round reshaped most of its statements. Two
more rounds were queued on it (several objects, loops), and three of the
issues the rebuild filed are requests to change its meaning again. That is
the feature being slid into. **The experiment module is not extended
again.** What is still untested is tested in the modules that stay, against
interfaces fixed first (§16's package 1), and `call_check.hthr` and
`place_check.hthr` are deleted when their programs pass through those, as
`lib/native/reference_cells/` was when the bytes level took its programs
(§17.6).

Four things about those interfaces are decided here, each from a defect the
experiments showed. A fifth is under test.

### 20.1 One text, two readings

Every experiment proved one theorem about one body read twice: `eval1` and
`run2` of the same statement, and §18.3's "there is no plan beyond the
annotation". So level 1 and level 2 do not have a syntax each. There is one
annotated body. Its *meaning* is the pure reading (values, no identity);
its *run* is the level-2 reading (blocks, references, deaths). The checker
is a function of the body, and `check_sound` is the agreement of the two
readings. §16's "three interfaces" are therefore: the body with its
annotation and signature record; the two readings, sharing one outcome type;
the verdict. The bytes level's contract is the fourth and exists (stages 1
and 2).

### 20.2 One control skeleton, at every level

The bytes level's body (§17.6) is a leaf of instructions, a sequence, a
branch, a call, a loop that names its inputs, parameters, next values and
outputs, a system call and an exit. FunctionIR's regions have that shape
already. The body of §20.1 has the same skeleton, so the step from level 2
to the bytes level is statement by statement, and a theorem about control
(a branch's two cases, a loop by induction on fuel) is stated the same way
at each level.

### 20.3 A join binds its outputs

*Amended by §21.2:* the join is the surface's, one convoy over the packed
outputs with each output a projection, and a join point where an arm
returns; "each output is the convoy of the two arms' values" below is the
one-output case.

The rebuilt checker's meaning carries what follows a branch into each arm:
`If(cd, a, b, rest)` means `convoy(test, a then rest, b then rest)`, and
what the function owes after the join is owed once per arm. Three things
are wrong with that, and they are one defect.

- *Cost.* What follows `k` branches in sequence is read `2^k` times: the
  meaning's normal form and the proposition a function owes both double at
  each open test. Every measurement so far was of straight-line bodies and
  of one branch.
- *The pin.* A source that continues after an `if` elaborates to the rest
  over a convoy of values, which is not the convoy of two rests
  (`issues/ownership-pin-after-join.md`). Only a function whose `if` is its
  tail pins by `refl`.
- *The discharge.* After its `if`, the source's proof at a later site is in
  a context without the test, about the joined values. Owed once per arm,
  the same residual is asked twice, each time about one arm's values.

The join that matches the source is the one a compiler's intermediate form
has: a branch names its outputs, and after it each output is the convoy of
the two arms' values for it, `convoy(test, a's, b's)`, the term the source's
own `let x = if h: … ` elaborates to. An arm's own bindings end with the
arm. A view live after the join on both arms is an output like any other
(its value the convoy, its region the union, §15.3). Residuals inside an arm
are owed under its side of the test; residuals after the join are owed once,
at the joined state, under no test. A function ending in an `if` is the
case whose outputs are its results. In the once-theorem a branch is one
case split on its test, where each output's convoy reduces. This replaces
`mean_then` and the `OIf(a, b, rest)` reading of `Owes::Holds`; the verdict's
tree keeps its shape.

### 20.4 The world is clocked

*Amended by §21.3 and §21.4:* a measured function's meaning takes no fuel
and is a value; only its run is clocked, and a postcondition is the
source's theorem, not a clause under `Done`.

`prog_sound` builds a program's callees by depth, and at depth zero a call
answers a made-up value (its argument, the word 0, an empty view), which
every postcondition then has to allow
(`issues/ownership-world-depth-zero-postconditions.md`): a callee that
promises a nonempty view cannot be composed, and a recursive one not at
all. This is §18.1 not yet applied to the checker. Both readings of a body
take fuel and answer the bytes level's outcome (`Done`, `Exited`, `Going`,
`Stuck`); out of fuel is `Going`, not a value. A function's safety speaks
of the fuel at which its meaning is `Done`: there the run is `Done` with an
answer that reads the meaning's, and a postcondition is a proposition of a
`Done` answer only. So nothing is promised of the depth-zero world, and a
loop (§18.4, item 2) and recursion are the same induction on fuel.

A total source function's pin is then stated at enough fuel: for a
straight-line body any fuel beyond its statement count, by evaluation; for a
loop, by the one lemma that relates the source's recursion to the loop's
iterations (§18.4, item 2's test).

### 20.5 Under test: values typed by code

Every experiment's object was a `List<Nat>`, so the meaning computed on the
source's own values, the pin was `refl` and a residual was the source's
proposition by conversion. With the universal value of
`value_steps.hthr` (`Val`) neither survives for a real function: a read of
an encoded list against the encoding of a read is a lemma per operation and
per residual, and a generator would be writing proofs again.

The sixth experiment (`issues/ownership-coded-values.md`, branch
`claude/ownership-coded-values`) tests the alternative: the single sort of
the step model is a native value tagged with its code. Codes are closed
first-order data (a word, a sequence, a named type by index); a type
environment decodes a named type to the source's own type, so a record and
a type parameter are both names; a second environment gives a named record
its fields as the library's paths with their laws, which is what a derived
instance would supply and is the same mechanism as §19's representations.
The reflected syntax stays untyped. If it holds, pins and discharges are
conversions for records, lists of records and generic functions, and the
once-theorem never looks inside a code. If it does not, the pin is a
generated proof through an encoding and §18.4 item 1's result is restated.

### 20.6 What follows

1. The sixth experiment's result fixes the value sort.
2. The interfaces of §20.1 are written as modules of definitions, with the
   theorems' types stated and unproved, and reviewed against the five
   experiments' programs before anything is proved over them.
3. The checker, the two readings and `check_sound` are built once over
   them, with several objects, places with steps, joins as §20.3 and loops
   from the start: the cases the experiments left
   (`issues/ownership-checker-several-objects.md`, §18.4 item 2) are this
   build's first probes, not further rounds on the experiment.
4. The issues that ask for changes to the experiment's meaning
   (`ownership-pin-after-join`, `ownership-world-depth-zero-postconditions`,
   `ownership-branch-on-object-length`, `ownership-write-bounds`) are
   requirements on that build and are closed by it.

## 21. The interfaces (2026-11-25)

**§22 is this section as built, and holds where the two differ** (a
reference holds selections, not closed steps; a pin is stated through the
continuation that reads the answer back; written parameters are results;
the environment's form).

§20.6's step 2, written after the sixth experiment
(`issues/ownership-coded-values.md`, §18.4 item 4) held, and revised
against an adversarial review of its first draft (thirteen defects, each
with a program; what each changed is §21.6). Each part says whether an
experiment proved it (**shown**) or it is this section's proposal and one
of the build's first probes (**proposed**). The modules of definitions are
written from this section; a definition that cannot be written as stated
comes back to this section, it is not adjusted in the module.

**The rule that fixes the body: it has the forms the surface already lowers
to.** `docs/language/sequencing-surface-design.md` §5, §14, §19 and §22 are
built: straight-line code as aliases, a statement `if` as one convoy over
the packed locals its arms assign, a branch that ends a block, a
`while` as the library's loop combinator run on a named step
(`docs/language/loop-combinator-design.md`), a `for` as a fold of a named
step. (Its join point for a continuation needed in more than one place is
designed and not built: §21.2.) The reflector reflects that
lowered form one construct for one, so a pin is a conversion by
construction and not by the luck of two designs agreeing. Where this
section and that document differ about a form, that document holds and this
section is corrected.

### 21.1 Values

- **Codes** (shown for a `Nat` word, `List` and names). `Shape` is closed
  first-order data with decidable equality: a word of a width, or a named
  type by index. A type environment `tys: Nat → Type` and `El(tys, c)` by
  large elimination: a name is `tys(k)` itself. A user record, a type
  parameter and a sequence type are all names.
- **Structure.** A second environment gives each name its `Struct`: its
  sharing class (§15.1), and one of
  - *opaque*: nothing (a type parameter, a type the function does not look
    into);
  - *a record*: its fields, each a shape and a total read and update of the
    field, with their laws and the apartness of distinct fields;
  - *a sequence* (proposed): its element shape, a total read and update at
    an index, a window, its length, and **the proposition its accessor
    asks**, with the laws (a read after an update inside; distinct indices
    and disjoint windows apart; an update keeps the length). `List<A>`,
    `[A; n]` and `Bytes(n)` are three instances, each spelling its bound as
    its own accessor does (`i < xs.len()`, `i < n`, an order on `u64`), so
    the sources' three spellings are each a conversion. The experiment's
    built-in `SSeq` is the `List` instance.

  A `Struct` is what a derived instance supplies, found the way §19's
  representations are found. Variants and stores are added the same way,
  each with its probe; neither is in the first build's fragment.
- **The pad** (amended the same day, from the build's first report). A
  sequence's total read is its type's own total accessor, and what it
  answers past the end is that accessor's: `[u64; n]` and `Bytes(n)` need
  nothing. No total read of a `List<A>` exists at every `A`
  (`read(False, Nil, 0)`), so `List<A>` and `[A; n]` are sequences at an
  element structure that has a pad: zero for a word, a record's derived
  default where every field has one, and for a type parameter a field of
  its opaque structure, quantified in the pin's statement, so the function
  takes no `T`. A source reading through that accessor pins by `refl`; one
  reading through a proof-consuming accessor pins by one library lemma per
  site, which is confined to generic library code. The meaning does not
  take proofs as input: its type would depend on the states it computes.
- **Words** (proposed beyond `Nat`). A word shape decodes to the source's
  word type at that width. A selection's index is the word itself, a
  number or a word at a width, and an instance reads it at its own
  accessor's type (`Bytes::at` takes the `u64`; a number round-tripped
  through `toNat` does not spell it); the decider and the obligations read
  an index through `toNat`, which is how the sources state their bounds
  (`∥i.toNat() < count.toNat()∥`).
- **The single sort** is `Dyn(tys)`, a code and a value of its decoding.
  A word is a `Dyn`, so the body has one kind of variable (§15.1) and one
  environment. A newest-first list makes any long-lived variable dearer
  with every binding after it (the build measured it on three axes:
  parameters under locals, an object under words, a local under either).
  Two indexed environments were measured against it, the library's trie
  and a skew-binary list: both linear on every axis and two to three and a
  half times dearer on the common ones, a level of numeral arithmetic
  costing about sixty kernel steps where a list cell costs a few. So the
  environment is arguments by position and locals newest first, a
  variable `Arg(i)` or `Loc(j)`; its blind spot is a local that outlives
  hundreds of bindings in straight-line code, since a loop's state is its
  parameters (`issues/ownership-long-lived-local.md`). Theorems reach it
  only through `push`, `get` and their two laws, so the representation can
  change without a statement changing. A variable's code is
  static, a function of the body alone and never of a value, so no later
  dispatch waits on one.
- **Steps are total, and stated once** (proposed). The step model is a
  total read `at: Sel → S → S`, a total modification
  `over: Sel → (S → S) → S → S` and a Boolean "this step fits this owner";
  the laws hold where the step fits and are relative to what was read
  there (the sixth experiment's relative fit: the same code, for a window
  the same length; a fourth component of the model, "what is written is
  like what was read"). A step that does not fit modifies nothing, and
  reads a value that does not depend on its owner: the word zero for an
  absent field, its accessor's pad for a sequence. That is what lets the
  decider's verdict hold at every value, fitting or not (reading the owner
  back, as the first text here had it, is unsound for the decider, an
  absent field against a write of a present one, and would make the read's
  code the bound's decision, stuck at an open index). This replaces `steps.hthr`'s `StepModelLaws`, `PathLawsOn` and `KeepsFit`
  in place, and `Steps::apart_sound` is re-proved over it: the experiment
  showed the relative laws at the `Option`-valued paths and pinned through
  the total forms, and the agreement of the two was not built. One
  spelling removes the need for it. `value_steps.hthr`'s `Val` has no
  customer after this and goes, its probes restated at `Dyn`.

### 21.2 The body

One text (§20.1), in continuation form, so each reading is one structural
recursion. Statements are shown; the control forms are the surface's and
are proposed as stated here.

```
Place = a variable and steps
Stmt  = a word primitive | a read of a place | a write of a place
      | a view of a place, to read or to write | a take of a place
      | fresh(shape, n, v) | a call | a death of a place
Body  = Ret(results)                       // the function's result
      | Yield(outputs)                     // to the enclosing join
      | Do(stmt, rest)
      | Join(test, yes, no, rest)          // rest sees the arms' yielded outputs as new variables
      | Jump(args)                         // the function's own call, last (a loop's back edge)
Func  = signature (§15.8), body
```

- **A join binds once.** Its arms are bodies whose leaves are `Yield` or
  the function's own terminators (`Ret`, `Jump`). Where every leaf of both
  arms is a `Yield`, the join's meaning is the surface's:
  `j = convoy(test, pack(yes), pack(no))`, `pack` the nested `Mutated` of
  the outputs' native values in first-assignment order (one output: the
  value itself), and output `k` is the `Dyn` of its code and the `k`th
  projection of `j`. Every variable an arm writes is an output.
  Where an arm has a leaf that is not a `Yield` (an early return on an
  inner path), `rest` is bound once as a function of the outputs and each
  `Yield` calls it. The surface's own join point is designed and not built
  (it copies what follows into each arm that falls through), and the bound
  form converts to the copied one, so the pin holds and the meaning stays
  linear in the body; the doubling is the source's own term's. A join's
  codes are its yes arm's yielded ones, the no arm's values cast to them
  with the yes arm's as the fallback; an ill-coded call binds the word
  zero. So an ill-coded body has a junk meaning and never a missing one:
  nothing in the meaning is optional and no pin has a `Some`. The check
  refuses a join whose arms' codes differ and a call whose arguments'
  codes are not its signature's, from the codes alone. A branch
  that ends the body is the join none of whose leaves is a `Yield`; it is
  not a second node. In every case what follows a join is read once.
- **A view as an output.** A read view chosen by a join is an output like
  any other, its region the union (§15.3). A view to write survives a join
  only where both arms hold it at one parent and one place; otherwise it is
  written back before the join. (An earlier text here allowed one root with
  the slot a convoy of the arms' steps; a write-back's place is static, so
  there is nothing to write back to. §23.)
- **A loop is a function**, which is what the surface makes it: `while`
  is the library's loop combinator run on a named step over the state
  (`docs/language/loop-combinator-design.md`; an earlier text here described
  the generated sibling that design replaced), the step's round ending in
  the loop's own call; `for` is the fold of its step, pinned by the library's fold
  lemma once. There is no loop node and no loop flag: a loop is a function
  whose body has a `Jump`. Its parameters are **the places live at its
  head, each with its state**: a word by value; a place by its mode; the
  owner of a write view held across the loop as an erased in-out parameter
  (§15.2); a variable partly `gone` as its available places. So the place
  state at the head is the signature, a residual at every pass is the
  loop's precondition, owed at entry and at the `Jump`, and the checker has
  no rule for loops. What it does need beyond a function call's rule is
  the passing of partly available variables, which is the build's probe.
- **The step to the bytes level is a pass with its own theorem**, not
  statement by statement (this departs from §20.2, which holds for
  sequences, joins and calls only): a loop function is inlined at its use
  and its `Jump` becomes that level's `Loop`. That node binds its outputs
  to the final state, so a loop whose results are not its state is
  widened by the pass, or the node is given results apart from its state;
  which, is decided when the pass is built
  (`issues/bytes-level-lowering-loops.md` is told).
- **A fresh object takes its first value as an operand**: `fresh(shape, n,
  v)` means `n` copies of `v`. An uninitialised fresh object, whose
  elements start `gone` and become available as they are written (§18.2:
  a load owes "defined", which the place state supplies), is a later
  statement with its own probe.
- **A death is of a place**, since a write to an owned place kills what was
  there and no binder holds it. The annotation (§15.3) is otherwise in the
  statements: a binder is own or a view with its mode.
- **The world is a value** (§14 item 7, §18.2). `Io` is a variable of the
  class that may be neither dropped nor duplicated, and a system call is a
  call on it; `read_into` is a join on its outcome, the window an output
  of the filled arm only. There is no `Sys` node and no `Exit` node: a
  program is its entry function and an exit with its result, and the
  exited clause is the program theorem's.

### 21.3 The two readings

- **The meaning.** Given `tys`, the structures and a world, the body's pure
  reading. The world gives each callee's meaning as the source's own
  function over `Dyn`s; a recursive function's world holds the function
  itself. For a measured function the meaning takes no fuel and is a
  value. A function with an unmeasured loop over `Io` has the source's own
  type, `Partial`, observed at a count. (This supersedes §20.4's "both
  readings take fuel" for measured functions.)
- **The pin** of a function that does not call itself is `refl` (shown).
  A function with `decreases` does not unfold at open arguments, so its
  pin is its unfolding equation and then `refl`: one stated lemma per
  recursive function, which a loop is. Composing a program needs each pin
  pointwise, `W(g)(args) = mean(body_g, W)(args)`, as a premise.
- **The run** (proposed: level 2 as §18.3 fixed it, over `Dyn`). A heap is
  a list of blocks, each dead or live with an object. A variable holds a
  plain value or a reference, a block and steps. An object is a `Dyn` and
  its **holes**: selections (what was selected, an index being the
  variable's own value; steps with their atoms are the body's syntax) at
  which the value is not here
  but *owned* (in a block it owns), *viewed* (a block and steps it does not
  own: a stored view, §15.2) or *taken*. A nested part whose sharing class
  is "object" is always an owned hole. **A reference is canonical**: it is
  resolved through every hole before its last step, so two references are
  compared in one block's steps or are in different blocks. Reading an
  object as a value fills owned and viewed holes; it is defined except at
  taken places, and its fuel is the number of owned holes plus the views'
  depth, since only ownership is a tree. This keeps one decoding and one
  sort; it is untested beyond one write through a view of an object with
  no holes. The run takes fuel and answers the bytes level's outcome; a
  call spends one, so recursion and loops are one induction.

### 21.4 The verdict and the theorem

- `check(sigs, f)` is one forward pass (§15.3) answering what the function
  owes: a tree in the body's shape, each statement's residuals at the state
  it reads, a join's arms under their sides of the test, what follows a
  join once.
- **Residual kinds are three.** `Apart` (a disjunction naming its sides).
  `Pre`: a callee's precondition at the values passed, and **an accessor's
  precondition at a step**: an element read, an element write, a take and
  the opening of a view each owe what the sequence's accessor asks, so
  there is no separate bound kind and writes owe theirs
  (`issues/ownership-write-bounds.md`). `Fits`: a write of a whole place
  owes that what is written fits what was there (a sequence of the same
  length). Each is stated over the native values inside the `Dyn`s, so the
  source's proof is its discharge by conversion; many are discharged as
  one restated conjunction (§18.4 item 1). A call of a measured function
  also owes `need_g(args') < need_f(args)` where the two are in one
  recursion, discharged by the source's own `decreases` proof.
- **`check_sound`, once.** A verdict and its residuals give the function's
  safety, relative to its callees' at less fuel:
  - at no fuel is the run `Stuck`;
  - a measured function's run is `Done` at every fuel from its `need`
    (the fuel half of §15.9's cost, one statement with it): termination is
    proved in the same induction, since it needs what only that induction
    has, that each call's arguments in the run read the meaning's;
  - where the run is `Done`, its answer reads the meaning's except at
    taken places; each written parameter reads the meaning's value after,
    and fits its value before; the heap is unchanged outside what was
    lent; a returned view is its parameter's reference narrowed by the
    steps the signature names, at the call's words, by the run's own
    narrowing;
  - where an unmeasured run is `Going`, the world's history so far is a
    prefix of one the meaning reaches (§18.1's second clause).
- **A postcondition is not in safety.** With a meaning that is a value, a
  postcondition is a theorem about the source function, and a caller cites
  it as a hypothesis of its own residuals before any run exists.
- A program's safety is each function's, composed on fuel, with the exit
  clause at the entry (§20.4: no depth, no made-up answer).

### 21.5 The build's first probes

In this order, since each tests something proposed above before more is
built on it.

1. The total step model: `Steps::apart_sound` over it, and the three
   sequence instances with a read under each one's own bound.
2. One environment against two (cost), with word types other than `Nat`.
3. A join assigning two variables, one an object an arm writes, then a use
   of both; a join one of whose arms returns on an inner path; three such
   in sequence (linear).
4. A loop as a function: writing an element while a view of a later window
   is held, its residual from its guard (§18.4 item 2's test); then one
   whose parameter is partly `gone`, and one holding a write view of
   another parameter.
5. Two objects, a view of one beside a write of the other; a write of a
   whole place owing `Fits`.
6. Holes: a record holding a buffer and a list of lists, read and written
   through a view; a view returned from behind a hole; a swap of two
   fields' buffers.
7. A recursive function composed on fuel, `Done` from its `need`.

### 21.6 What the review changed

The first draft was not committed. An adversarial review of it returned
thirteen defects, each with a program; they are summarised here by what
moved.

- The join was per output and of `Dyn`s (a projection of a stuck convoy is
  not a convoy of projections; a convoy of `Dyn`s has a stuck code); it is
  now the surface's packed convoy with recorded codes.
- Straight arms and a tail branch as two nodes brought the exponential
  back for an arm with one returning path; a join now binds what follows
  once, by the surface's join point. (A chain of joins each reading the
  last one's output is still quadratic, as the source's own `let` chain
  is: `issues/ownership-join-chain-cost.md`.)
- Sequences were one built-in shape decoding to `List`; the cited sources
  read `[u64; 16]` and `Bytes(n)`. A sequence is now a name with a
  structure, and a bound is its accessor's precondition.
- Reads through a default asked an inhabitant of every type; the pad is
  now the accessor's own, asked only of a sequence's element where its
  accessor has none, and a fresh object takes its value.
- The step was spelled twice (total in the meaning, `Option`-valued in the
  laws); it is stated once, total.
- The meaning was total for every function and safety silent at `Going`,
  against §18.1 and §18.2 for a program that never ends; unmeasured loops
  keep the source's `Partial` and the prefix clause.
- Termination was left to the cost theorem, which would repeat the
  simulation; it is in the one induction, from `need`.
- The postcondition was a clause of safety under `Done`; it is the
  source's theorem.
- Writes owed nothing and safety had lost the fit of a written parameter.
- Holes were owned or taken only, references not canonical, and "extends"
  a list prefix: stored views had no representation and a view returned
  from behind a hole did not extend its parameter.
- "A loop needs no new rule" overlooked parameters partly `gone` and a
  write view held across the loop; the loop flag was a second spelling;
  the step to the bytes level's `Loop` is a pass.
- `Sys` and `Exit` as nodes were a second effects language beside §14 item
  7's world as a value, and one continuation after a read could not give
  the window back only where it was filled.
- A death named a binding; a write view chosen by a join had no slot.

## 22. The interfaces as built (2026-11-25)

`issues/ownership-interfaces.md` built §21 as modules. This section says
what each module holds, where a definition differs from §21 and why, and
what was measured. Where it says "agreed", the coordinating session
decided it; "pending" is reported and not yet decided.

### 22.1 What each module holds

| Module | Holds |
|---|---|
| `lib/lang/ownership/steps.hthr` | Steps, `Ix`, selections, the decider; the total step model (`StepModel { at, over, fits, like }`, `StepModelLaws`, `ApartAt`) and `Steps::apart_sound` over it |
| `lib/lang/ownership/shape.hthr` | `Shape { SWord(Width), SNamed(k) }`, `El`, `Dyn`, `Struct { sharing, pad, kind }` (opaque, record, sequence with windows), the kinds' laws, `Dyn`'s model and `Dyn::model_laws` from the structures' laws alone |
| `lib/lang/ownership/sequences.hthr` | `List<A>` (with windows), `[A; n]` and `Bytes(n)` as sequences; unique identity proofs at `Nat` for `Bytes`'s length proof |
| `lib/lang/ownership/body.hthr` | `Var { Arg(i), Loc(j) }`, the environment `Env` and its laws, `Place`, `Stmt`, `Body`, a signature record, `Func`, the total meaning in continuation form, the pin's form `Func::then` and the one lemma relating it to the answer (`Body::mean_then`, `Func::then_denote`), the `Ret` convention (`Sig::written`), and the stage lemmas (`convoy_map`, `dconvoy_map`, `List::foldl_same`) |
| `lib/lang/ownership/level2.hthr` | Heap, blocks, objects with holes at selections, values and references holding selections (`Sel::same`, `Sel::read_at`, `Ref::narrow`), a canonical reference, an object read as a value, the run's outcome and signature (definitions only) |
| `lib/lang/ownership/verdict.hthr` | The residual kinds, the verdict's tree and what it owes along the meaning, a program, `SafeAt`/`Safety`; the code check `Func::coded` (a `Bool`, computed); `Checker`, `CheckRefusesIllCoded` and `CheckSound` (`Type`-valued definitions only) |

Probes: `lib/_tests/lang/ownership/{shape,sequences,body,interfaces}_tests.hthr`.
Retired: `value_steps.hthr`, `coded.hthr` and their probes, and
`PathLawsOn`/`KeepsFit` from `lib/std/machine/path.hthr`.

### 22.2 Where the built form differs from §21

- **The step model has four parts** (agreed). §21.1's "relative to what
  was read there" is a fourth component, `like(sel, read, written)`: for a
  `Dyn` its code, through a window also its length.
- **An unfit step does not read its owner back** (agreed, withdrawn from
  §21.1). Soundness never reads an unfit step. Reading the owner back
  would make a read's code the bound's decision, stuck at an open index.
- **An unfit read answers a value independent of the owner** (agreed,
  decision D): the word 0 for a step with no part at the owner's code, and
  for a sequence the accessor's pad. An owner-back read is unsound beside a
  write. `[SField(2)]` and `[SField(0)]` on a record of two fields are found
  apart, yet a write through field 0 would change what field 2 read back.
  The probes are `absent_field` (shape) and its sequence twin
  `past_end_apart`/`past_end_kept` (an element past the end against a
  write of one inside).
- **The index is the variable's own value** (agreed, decision B). A
  selection's index is an `Ix`, a number or a word at a width. An instance
  reads it at its accessor's own type, and the decider reads it through
  `toNat`. `Bytes::at` reads at the `u64` itself, so an index carried as
  its number cannot spell it.
- **A sequence's read is its type's own total accessor, with that
  accessor's pad** (agreed, decision A; §21.1's "no inhabitant is asked" is
  withdrawn).
  - `[u64; n]` and `Bytes(n)` need nothing.
  - `List<A>` and `[A; n]` take their pad as an instance parameter, at an
    element structure that has one.
  - A read through a proof-consuming accessor pins by one library lemma
    per site (`copy_below_pin`).
  - No real type was excluded for want of a pad in this package.
- **The meaning is total; nothing is optional and nothing is recorded**
  (agreed; the optional meaning first built here is taken out).
  - Every pin is the meaning read back through a native continuation
    equal to the source's term (below, "The pin's form").
  - A join's codes come from its yes arm. The no arm's values are cast to
    them, with the yes value as the fallback.
  - A callee in the world is `List<Dyn> → List<Dyn>`. An ill-coded call
    answers no results, and a binder with no result binds the word-zero
    `Dyn`.
  - A word primitive or test at a non-word reads the word 0 there.
  - Ill-coded bodies therefore have a meaning, and it is junk. The probes
    `join_ill_coded_junk`, `call_ill_junk` and `ill_word_junk` pin it.
- **The code check refuses, from codes alone, what the casts would cover**
  (agreed). `Func::coded` walks the body with each variable's code and
  refuses:
  - a join whose arms yield different codes;
  - a call whose argument codes are not its signature's parameters;
  - a word primitive or test at a non-word;
  - a `Ret` whose codes are not the signature's results followed by its
    written parameters' (the `Ret` convention, below).

  Each refusal has a `= False` probe beside an accepted twin
  (`interfaces_tests`). `CheckRefusesIllCoded` states that a checker's
  verdict implies `coded`.
- **A variable's code is static** because every arm of every join yields
  closed codes, read off the yes arm, and no statement's code depends on a
  value. Two statements record a code not computed from their operands:
  `Fresh(c, …)` names its object's code, and a call's results take their
  signature's result codes.
- **A join binds what follows once** (agreed, decision C). A packed join
  is one convoy over the packed outputs; a join with an inner return binds
  what follows as a function of the outputs, which each `Yield` calls.
- **The pin's form** (agreed). A pin states `f.then(R, …, args, k) =
  source(args)`: the meaning in continuation form at the source's own
  result type `R`, the continuation `k` reading the results back natively
  (`Dyn::index`, `Dyn::back`). A tail join is then the source's
  `convoy(test, …)` itself, so every pin is `refl`, a function ending in a
  branch or returning on an inner path (`early_pin`) included, and no pin
  cites a convoy lemma.
  - One lemma relates the form to the answer: `Body::mean_then`, by
    induction on the body, says the meaning at continuations that are
    pointwise `f` of others is `f` of the meaning at those (pointwise,
    because there is no funext). `Func::then_denote` is its instance,
    `f.then(…, k) = k(f.denote(…))`; it is what `check_sound` and a
    program's composition use.
  - Inside it a statement hands its continuation the next environment
    (`Stmt::eval_is`, by cases), a packed join needs nothing, and the
    join-point join commutes its convoy once (`convoy_map`). The earlier
    per-function use of `convoy_map` is gone.
- **The `Ret` convention** (agreed). A function's `Ret` lists its results,
  then its written (`ByWrite`) parameters' values at its end, in signature
  order (`Sig::written`). A call binds all of them and the caller writes
  each back to the place it lent (§15.2's eager write-back). There is one
  meaning, and "the meaning's value after" of a written parameter is its
  position in it. Against the source's `Mutated` nesting
  (`sequencing-surface-design.md` §24.2: one `Mutated` per `&mut`
  parameter in parameter order, the answer innermost): with written
  parameters `p₁ … p_W` and one result, list position 0 is
  `.value` taken W times, and position `k` (1 ≤ k ≤ W) is `.value` taken
  `k − 1` times then `.after`. So `fn f(a: &mut A, b: &mut B) → R` ends
  `Ret([r, a, b])` and is read back as `Mutated(rs[1], Mutated(rs[2],
  rs[0]))` (probes `copy_elem_pin`, `bump_means`).
- **The surface has no join point** (agreed). A statement `if` with a
  return on an inner path copies what follows into each arm that falls
  through (`sequencing-surface-design.md` §22 items 5 and 8). The meaning
  binds it once, the same term after β.
- **A `while` is the loop combinator** (pending: §21.2 says a generated
  sibling function).
  - The surface now lowers a `while` to `Loop(measure, f::step).run(state)`
    (`docs/language/loop-combinator-design.md`), whose one equation is
    `Loop::run_unfold`.
  - The loop's body is still a function whose round ends in a `Jump`. The
    world holds the loop as the source's function.
  - The pin is the equation, then the step's split on its test
    (`dconvoy_map`), each arm `refl`.
  - `dconvoy_map` is one library lemma for every loop. What each loop
    adds is its unfolding (`Loop::run_unfold` at its state) and one stated
    equation of its step as the convoy of its test (`drain_step_is`, by
    `refl`): the "one stated lemma per loop" §21.3 allows.
- **A `for` is the fold of its step.** The step is a function pinned by
  `refl`. The loop is the fold of the step's meaning, related to the
  source's fold by `List::foldl_same`.
- **Variables are `Arg(i)` or `Loc(j)`** (agreed, conditionally). An
  environment holds the arguments by position and the locals newest-first.
  Every theorem reaches it only through `Env::push`, `Env::get` and the
  laws (`get_push_here`, `get_push_below`, `get_push_arg`). An index atom
  `Var(w)` reads argument `w` below the argument count and local `w − A`
  above it (`Env::ixs`). A local that lives long, such as a taken object,
  still sinks one deeper with each binding: the issue
  `ownership-long-lived-local` holds its measured shape.
  - One indexed environment, variables named by level, was built twice
    (the library's `NatMap` `Array`, and a skew-binary random-access list)
    and measured against this split (§22.3). Both are linear up to the
    logarithm and cure the long-lived local, but cost 1.3 to 3.7 times the
    split on the other rows, past the agreed margin of a third, so the
    split stays (agreed).
  - The split's blind spot is only a long straight-line body. A loop's
    state is its parameters (§21.2), and the reflector passes anything
    long-lived into a loop as a parameter, which `Arg` reaches by position
    at every round; only a local that outlives many bindings in one
    straight run sinks. The issue says what would reopen the choice.
  - Under an indexed environment a place's atoms name levels while the
    decider reads indices from a `List<Ix>`, so each read renumbered its
    own atoms and took only their words; that cost a further share on the
    list-read row. The split needs none of it: an atom reads the
    arguments' words, then the locals' newest first.
- **Level 2 and the verdict are definitions.**
  - `SafeAt` states, at each fuel:
    - the run is not stuck;
    - a measured run is done from its `need`;
    - where it is done: its results read the meaning's results; each
      written parameter's argument, read in the heap after, is the
      meaning's value after, which fits its value before
      (`Value::Written`); the heap outside what the arguments lend is
      unchanged; and each returned view is its parameter's reference
      narrowed by the steps its signature names at the call's words
      (`Value::Views`, `Ref::narrow`);
    - where an unmeasured run is going, its history is one the meaning
      reaches.
  - **References and holes hold selections** (agreed; §21.3's "steps,
    closed in the run" is now "selections"). A reference is `Ref { b,
    sels: List<Sel> }` and a hole sits at selections. A run-time value
    holds what was selected, each index an `Ix` (the variable's own
    value), not the body's steps with atoms. Closed steps could not say a
    byte at a `u64` index: a literal atom reads a number, and `Bytes(n)`
    reads a word only. A read folds the model's `at` over the selections
    (`Sel::read_at`), narrowing appends a place's selections at the
    call's words (`Ref::narrow`), and `Canonical` compares selections by
    `Sel::same`. Probes: `view_clause` (a view narrowed at `IWord(64, i)`)
    and `view_of_plain` (a view of a by-value parameter owes `False`).
  - `CheckSound` quantifies over a checker, since the checker is not built.

### 22.3 What was measured

Kernel steps, width one, a fresh cache per run, read with `scripts/timings`.

- **The option** cost a factor of 1.01 to 1.09 before it was taken out.
  That was an optioned meaning against a copy with fallbacks and no
  failure, on the same bodies.
- **One newest-first list of variables is quadratic.**
  - A variable that lives long, such as a parameter or an object, sinks one
    deeper with every binding.
  - N word additions reading one parameter: 11.5k, 29.7k, 87k, 289k steps at
    N = 32 to 256.
  - N reads of a list at the last read's index: 20k, 47k, 122k, 357k.
  - With arguments addressed by position and locals newest-first, both are
    exactly linear: 8.4k to 64k, and 17k to 129k. On the built `Arg`/`Loc`
    environment: 8.0k, 15.5k, 30.8k, 61.6k, and 18.7k, 36.8k, 73.4k, 146k.
  - A long-lived local is not: the same chain over a list first taken into
    a local costs 23k, 52k, 133k, 379k. Each binding pushes it one deeper.
- **One environment against two** (§21.5 probe 2), with a `[u64; 16]`
  object and `u64` words. N rounds of a read at the last word's `toNat`
  plus one:

  | N | one | two |
  |---|---|---|
  | 32 | 121k | 109k |
  | 64 | 263k | 218k |
  | 128 | 613k | 436k |
  | 256 | 2.62M | 873k |

  Two (objects apart from words) is exactly linear. One is superlinear and
  needs more than the default budget at 256.

  Rerun on the built `Arg`/`Loc` environment, with the object taken from
  an argument into a local:

  | N | one | two |
  |---|---|---|
  | 32 | 128k | 117k |
  | 64 | 280k | 236k |
  | 128 | 660k | 485k |
  | 256 | 2.76M (out of fuel) | 1.02M |

  The result is unchanged. Splitting arguments from locals does not help
  here, because the object is a local and sinks with each word bound. This
  is the long-lived local's shape again.
- **Joins in sequence.**
  - Independent packed joins: 10.6k, 22.9k, 53.9k, 141k at K = 4 to 32. That
    is mildly superlinear, from the same variable depth; the source alone
    is linear.
  - Joins with an inner return: 2.1k, 5.4k, 12.3k, 26.4k, 55.6k, 116k at K =
    1 to 6. That is exponential, the surface's copied rest; the meaning's
    text is linear (recorded on `bind-in-non-tail-match-arms`, the surface's
    unbuilt join point).
  - On the built `Arg`/`Loc` environment, independent packed joins: 11.8k,
    25.4k, 58.5k, 149k at K = 4 to 32.
- **An indexed environment against the split.** One environment, variables
  named by level, the same sources and pins; "split" is `Arg`/`Loc`, or for
  item 4's rounds the two environments:

  | Row | N | `NatMap` `Array` | skew-binary list | split |
  |---|---|---|---|---|
  | add | 32 … 256 | 20.0k … 230k | 21.6k … 216k | 8.0k … 61.6k |
  | chain | 32 … 256 | 31.4k … 320k | 33.0k … 306k | 18.7k … 146k |
  | long-lived local | 32 … 256 | 33.5k … 319k | 32.4k … 298k | 23.0k … 379k |
  | item 4 | 32 … 128 | 167k … 738k | 145k … 599k | 117k … 485k |
  | packed joins | K = 4 … 32 | 22.5k … 281k | 20.9k … 200k | 11.8k … 149k |

  Both indexed forms are linear up to the logarithm (item 4 runs out of the
  default budget at 256 in both). Their constant is the lookup: each level
  of a trie or tree is a comparison, a halving and a subtraction on
  numerals, constant-time but tens of kernel steps each, where a list cell
  is a few. The full rows are on `ownership-long-lived-local`.

## 23. The checker as built (2026-11-25, in progress)

`issues/ownership-checker.md` builds the run, the checker and `check_sound`
over §22's interfaces, for objects whose nested parts are plain (no holes).
This section grows with that issue: items 1 and 2 (definitions and
evaluation) are here; the proofs (items 3 and 4) follow. Where it says
"proposed", the coordinating session has not yet decided.

### 23.1 What each module holds

| Module | Holds |
|---|---|
| `lib/lang/ownership/run.hthr` | The run: a variable as a `Cell` (a `Value` and whether its frame owns the block it refers to), the run's environment with the meaning's shape (`REnv`), reads and writes at selections that fit (`Sel::get`, `Sel::put`), statements, bodies in continuation form, `Func::run`, `Run::calls` (a callee at one less fuel, a primitive natively), `Run::of` |
| `lib/lang/ownership/checker.hthr` | The checker: a role per variable, the table of live views, the licence, the statements, calls, leaves, the join's meet, `check: Checker(tys)` |

Probes: `lib/_tests/lang/ownership/{run,checker}_tests.hthr`.

### 23.2 The run

- **A body read over a heap.** An object is in a block; a variable holds a
  plain value or a reference (`Value`), and its frame owns the block where
  it took or made it (`Cell.own`). A read, a word primitive, a literal and
  a take out of a part bind a plain copy. A view of a referring variable
  binds its reference narrowed (`Ref::narrow`), of a plain one a copy. A take
  of a whole variable passes its cell on. `fresh` makes the next block. A
  write stores where the place is: in the block the root refers to, or in a
  plain root's own value. A death of an owner kills its block; any other is
  nothing. So the eager write-back the reflector places after each change
  of a view stores, in the run, what the block already holds.
- **Calls** run the callee's body at one less fuel (`Run::calls`): a taken
  argument the caller owns is passed on, unless it is a word; a word and one
  it does not own are copied; a read or written argument is passed as it
  is. A **primitive** (a callee the program gives no body, such as a list's
  length, which `body_tests.hthr` reaches as a callee) reads its arguments
  through the heap and answers the world's results, plain. A `Jump` is a
  call of the function itself. Out of fuel a call is `Going`.
- **A join** runs the arm its test picks; a `Yield` continues after the join
  with the outputs pushed on the environment from before it, as the
  meaning's does. The run needs no convoy and no join point: both join forms
  run alike.
- **Stuck** is a read of a dead or dangling block, and any selection that
  does not fit what it selects in (an element past the end, a field the
  record lacks). The meaning's reads are total; the run's are not, which is
  where the accessors' preconditions (`RAccess`) are needed at this level.

The probes: each pinned function of `body_tests.hthr` at closed arguments,
its objects in blocks, answers what its meaning answers (both by
evaluation); a write is a store in the block; the loop is done from fuel
four (the outer call and three jumps) and going below; a read past the end,
a dangling and a dead block, a write through a view whose owner died, and a
field the record lacks are stuck.

### 23.3 The checker

One forward pass, reading the signatures only, after the code check
(`Func::coded`, folded in: `check` refuses what it refuses).

- **The state mirrors the meaning's environment**: an entry per variable,
  the arguments by position and the locals newest first, so a variable is
  reached at the meaning's cost. A variable is plain (the run holds a
  plain copy), holds an object with an access (an argument as its mode
  lends it, a fresh object, a taken one), is a view, or is gone.
- **A table of live views**, each naming its variable's level, its object,
  its region there (steps with atoms at levels, so a stored region keeps its
  meaning as locals are pushed), its mode, its parent (the variable it was
  opened on) and its place in the parent, and for a view to write whether it
  has been written back since it last changed.
- **The licence** (§15.3): an access of a variable at a place lands at the
  variable's region followed by the place's steps. A holder's access meets
  every live view of its object; a view's meets only the views opened
  through it, since every other live view was found apart from it when the
  later of the two was opened (a live view to write is apart from every
  other live view). A read meets only views to write. Apart is
  `Steps::apart`: closed, decided; open, `RApart` naming its two sides, its
  atoms read back at the site.
- **The write-back** `Write(Place(p, at), w)` of a view to write onto its own
  parent and place is licensed as it is (the run stores what is there),
  marks `w` written back and changes `p`. A view to write dies only written
  back; a view dies only after the views opened through it; an owner dies
  or is taken only with no view of its object live. A word that a live
  region reads is not written.
- **Residuals**: an accessor's precondition at every element or window
  prefix of a place read, written, taken or viewed (`RAccess`); `RFits` at a
  write whose place is a sequence; `RPre` and `RMeasure` at every call and
  `Jump`; `RApart` from the licence.
- **Calls** read what they lend to read, write what they lend to write, and
  move an owned non-word object they take (anything else taken is a copy).
  Arguments lent where one may change are apart where one is a view of the
  other or holds the object. Results: a fresh object; a taken object back;
  a read view of a parameter at the steps the signature names. Then each
  written parameter's value after, bound as a view to write of the argument
  lent (its whole, not written back): the caller writes it back to that
  argument, and the argument back to its own place.
- **Leaves.** A `Ret` reads its variables owing nothing (a `Ret` owes
  nothing in the verdict's tree), answers each result as its origin says,
  and gives back each written parameter's object, held and written back. A
  `Jump` passes each written or returned parameter back in its own place.
- **The join** is the meet (§15.3). What each arm yields becomes the
  outputs. A variable from before the join that an arm wrote or yielded is
  gone after it (the meaning returns to its value before the join, the heap
  does not); one the arms leave alike stays; any other is gone. A read view
  chosen by the join keeps every arm's entries (its region the union); a
  view to write survives only where both arms hold it on one parent at one
  place. Every view an arm holds that the join does not keep is dropped, and
  a dropped view to write must be written back.

### 23.4 What changed in the interfaces

Each agreed by the coordinating session after items 1 and 2.

- **A call binds its results, then its written parameters.**
  `Stmt::code_step` bound the results only, so after a call lending a view
  to write its value after could not be bound or written back. It now
  binds `ret_codes()`, §22.2's `Ret` convention read at the call.
- **Primitives are §15.4's "level 2's primitives", and there is no other
  kind.** A primitive is a world entry the program gives no body
  (`Prog.prim`): every parameter read or taken plain, every result fresh and
  plain (`Sig::reads_only`). Its run is, by definition, the world's function
  at its arguments read through the heap (`Run::prim`), so it has no run of
  its own to prove sound. The checker licenses a call of one as a read of
  each argument and refuses a primitive, or a call of one, that is not
  read-only. A list's length is the first (`body_tests.hthr` reaches it as
  a callee).
- **Passed by value is copied for plain data**, by the sharing class
  (`Shape::plain`: a word, or a name whose class is `Plain`), in the run
  (`Cell::pass`) and the checker (a taken plain parameter is a plain
  variable; a taken non-plain owned one moves).
- **The program's run is the defined one** (`Prog::run` is `Run::of`); the
  field is gone.
- **`SafeAt`** compares the run with the world `p.w`, and `CheckSound` takes
  each function's pin pointwise as a premise (`Prog::Pinned`, §21.3). Both
  hold under the function's own precondition. Its inputs are lendable
  (`Lendable`, named once, the design's "a function requires only that what
  it may change is not aliased"): each referring argument's block is live
  and has no holes and its selections fit; an argument taken at a plain code
  is plain; an argument the callee may change is apart from every other.
  The caller's side of `Lendable` is to be a lemma the licence gives at
  each call (item 3), not a premise re-proved per call.
  `Heap::Frame` covers the blocks that existed before. `ReadAll` reads the
  whole answer, results then written values. `Value::Written` reads a
  referring written argument's block after; a plain one is in the written
  slots. `Value::ViewIs`: a fresh result is plain or a block the call made
  (none below the heap's length before it, so no argument reaches it; the
  checker answers `OFresh` only with an object made in the call, never a
  taken argument, which is `OParam`); an `OParam(i)` result is the argument
  itself.
- **A returned view's place reads the call's words, the arguments' and then
  the results'** (§15.2: a view travels with its slot). In an `OView`'s
  steps an atom past the parameters' count reads a result; the callee's
  check requires that result to be a plain word, and the caller binds it
  among the call's results, so its write-back place is static in its own
  words. `call_check_tests`' `found` is accepted that way (`found_checked`,
  `beside_found_checked`); no region coarser than the view is added.
- **The sequences' laws**: `SeqLaws` and `WinLaws` have `pre_inside` (what
  the accessor asks gives the run's fit) and `inside_len` (the fit reads
  only the length, so a write that keeps lengths keeps every fit). A list's
  `Pre` at a word index is `False`, as decision B makes an index of another
  kind unfit (a source indexing by `i.toNat()` binds the number with a word
  primitive). `[A; n]` reads any word through `toNat` in both, and `Bytes(n)`
  a `u64` in both.
- **`RMeasure` at every call.** Fuel is depth, so `Done` from `need` composes
  through every call, and a signature does not name its recursion. Within
  a recursion the source's `decreases` proof discharges it. Outside one a
  generator writes the caller's `need` as one more than the largest of its
  call sites' callee needs at the values passed, and the residual holds by
  that definition (`both_due`: two calls of `pick`, need 1, from `both`,
  need 2).
- **A view to write survives a join only where both arms hold it at one
  parent and one place**; otherwise it is written back before the join. A
  write-back's place is static steps, so no place spells "the convoy of the
  arms' steps" (`two_windows_refused`; §21.2's allowance is withdrawn).

### 23.5 The experiments' programs

Restated in `checker_tests.hthr`, each accepted one with its verdict by
`refl`, each refusal refused and shown to pass the code check
(`refusals_coded`). In the real body the experiments' versions
(`let x1 = x.set(i, v)`) are writes in place, a take needing its place
whole; a lending call is followed by the two write-backs; every arm that
writes a variable yields it. Not restated: `call_check_tests` §9 (a
collection of stored write references and the erased owner, next round's
with stored views), and the first experiment's plan probes (two parameters
on one buffer, a clone into its source's buffer), which have no
counterpart: there is no plan, and arguments a callee may change are apart
by `SafeAt`'s inputs.

### 23.6 What was measured

Kernel steps, a fresh copy of a library-only cache per run, read with
`scripts/timings`. Each row is a generated body of `N` rounds over two
objects, its verdict checked to its residual count (which forces every
residual):

| N | straight loans (11 statements a round) | joins in sequence | calls lending a view to write |
|---|---|---|---|
| 8 | 131k | 44.5k | 104k |
| 16 | 264k | 86.7k | 206k |
| 32 | 542k | 173k | 414k |
| 48 | 836k | 262k | 627k |

All three are linear. Past about a million steps a single declaration
meets the kernel's budget, and the count it reports is no longer the
term's (a plain list sum shows the same at the same count), so a verdict
larger than about five hundred statements is checked in parts: the pass
over a body's prefix is a function of the state it starts in
(`Body::verdict` takes `CSt`), so a generator states, as one declaration,
the state a prefix ends in, and as the next, the verdict of the rest from
that state. Not a defect.

The dearest definition to elaborate is `CSt::out_role` (half a million
steps): a match on the two arms' roles, four by four, each arm an
`Option` built by `then` over a nested match on view entries, whose
motive the elaborator spells per arm. Not optimised. Of the
probes the dearest is `long_checked` (six rounds, 21 apartness residuals,
102k steps).

### 23.7 `check_sound`, in progress

**Three tightenings of the checker**, each so the invariant needs no case
the probes do not use:

- **The write-back is eager, as §15.2 says**: after a statement that
  changes a view to write, the only statements until it is written back are
  write-backs and deaths of views already written back; a join, a `Yield`,
  a `Ret` and a `Jump` are refused while one is pending (`CSt::pending`,
  `CSt::writes_back`; probes `between_refused`, `between_after_checked`).
  This is §15.2's rule made a refusal, `between_refused` its probe. So
  between statements at most the chain of a just-changed view is stale, and
  the invariant's patch is only along that chain.
- **Atoms read plain variables only** (`CSt::atoms_ok`): an index cannot move
  under a region, the variable being written refused while a region reads
  it and a plain variable's run value being its meaning's.
- **A fresh result of a plain code is a plain value**, on both sides
  (`Value::ViewIs`, the caller's role): a word a call answers is a plain
  variable, which an atom may read.

**The invariant** (`sound.hthr`'s `Inv`, stated once, with `Sim` as its
first field): between the checker's state, the meaning's environment and
the run's machine, for a function entered on heap `h0` and lent the blocks
`lent`:

- `sim`: each live variable's cell agrees with its meaning as its role says
  (a plain variable holds the value; a holder or a view reads it through
  the heap, its block live, its selections fitting; a gone one owes
  nothing), with the environments' lengths and each variable's code;
  against the meaning *with the pending chain written up*
  (`CSt::patched`, `CSt::up`): while a view to write has changed and is not
  yet written back, the heap already holds its value in each ancestor,
  which the meaning holds only after each write-back. Nothing pending, it
  is `Sim` itself (`Inv::sim_now`).
- `root`, `refs`: each object has one run reference, and a live variable's
  reference is its object's (a holder) or its object's narrowed by one of
  its entries' region at the words (a view; `CSt::RefOk`). This is what
  turns the licence's apartness of regions of one object into apartness of
  the run's references.
- `apart`: references to different objects, one of which something live
  may change through, are apart (`Lendable`'s clause at entry; a fresh
  block after).
- `owned`, `frame`, `grows`: every live reference is to a block lent or
  made here, so the blocks not lent are as they were (`Heap::Frame`).

**Entry** (`Inv::start`): the invariant at a function's start from
`SafeAt`'s premises: `ReadAll` and `Lendable` give each argument's cell its
role's agreement and reference, `Lendable.apart` the cross-object clause,
and `Dyn::Coded` the codes.

**`Dyn::Coded`** (added 2026-11-26): the meaning's arguments have the
parameters' codes, a premise of `SafeAt` and of `CheckSound`'s `Due`. Without
it `CheckSound` is false: `get_x(p: Point, read) { p.x }` (a field step owes
nothing) is checked owing nothing, and at the word `5` for `p` every other
premise holds (it reads as itself, there is no precondition, a plain value
is lendable) while the run is stuck reading a field of a word, at fuel 0,
where `Safety` assumes nothing of callees. A junk meaning for an ill-coded
input is sound only if inputs are coded, and codes come from outside only
here. The call stage discharges it from the code check (`Stmt::code_step`'s
`Call` case). Probes: `pick_args_coded`, `words_not_coded`.

**Built** (`sound.hthr`, probes `sound_tests.hthr`): reads, writes and fits
along appended selection paths; a place's steps as selections at the words;
levels and variables, and a push keeping every earlier level; `Sim::push`,
the one lemma every binding statement uses; `Value::get_more`; and
`Place::fit_from`: a place whose codes have parts and whose accessors'
residuals hold fits in the run, from `pre_inside`. A read's verdict split
once into its parts (`ReadInv`); the stage lemmas for `Lit` and `Op`
(`Stepped`: the run continues, the invariant holds after); and the words:
an atom the checker reads at plain levels reads one index in the run and in
the meaning (`Sim::atom_ix`), so a place's steps make one list of
selections in both (`Sim::steps_same`).

**Added to the interfaces** (decided 2026-11-26): writing back what was
read changes nothing, `put_back`, a law of the model rather than of this
proof: `FieldLaws` (`f.set(v, f.get(v)) = v`), `SeqLaws` and `WinLaws` (at
every index, inside or out: outside it is `still`), `PartLaws`, and
`StepModelLaws` (`over(a, λ _ => at(a, s), s) = s`, with no fit hypothesis),
derived for `Dyn::model` by `Dyn::in_put_back` and proved for the list,
`[A; n]`, `Bytes(n)` and list-window instances. The write-back stage needs
it: the run stores, at the view's place, what the block holds there.
`Lendable` carries the arity (`arity`: as many arguments as parameters),
since the checker's levels assume it.

**What remains for straight-line bodies and calls** (the invariant and
its entry are proved; `Lit`, `Op` and `Read` are proved against `Sim`): the
stage lemmas restated against `Inv` (the three above lift through
`Inv::sim_now`, nothing being pending when they run), then `Take`, `View`,
`Fresh`, `Write` (through a holder,
through a view, a write-back), `Death`, `Call` (each argument's lending,
`Lendable` at the callee from the licence, the callee's `SafeAt` at less
fuel, results and written slots) and `Ret` (`ReadAll`, `Written`, `Frame`,
`Views`); then `SafeAt` for a body with no join and no `Jump`.

### 23.8 `check_sound` continued: the interfaces tightened (2026-11-26)

Decided by the coordinating session after the first half of item 3, and
found while designing the invariant for every stage.

- **A block lent only to read is unchanged by the call.** `Heap::Frame` in
  `SafeAt` exempts only the blocks lent to a parameter that may change them
  (`Value::lends` takes the parameters). The caller's invariant after a call
  of a reader needs it: its other variables' reads of a read-lent block stand
  on the frame, not on the callee's word.
- **An object taken is a whole block no other argument refers to**
  (`Lendable.whole`). The callee owns it and its death frees the block, so a
  taken argument sharing a block with another one made `CheckSound` false:
  `f(a: Buf take, b: Buf read) { Death(a); Read(b) }` is checked, and at two
  apart fields of one block the run kills the block and the read is stuck.
  The caller's side is its own invariant (`own`, below).
- **The code conditions are in the checker's pass.** `Func::coded`, its
  `CEnv` walk and `CheckRefusesIllCoded` are gone from `verdict.hthr`; each
  statement, test, leaf and join is refused first if its codes are wrong
  (`Stmt::code_ok`, `Test::code_ok`, the leaves' and arms' code lists), from
  the codes the checker's state records, so a stage reads its codes off the
  verdict's inversion. A refusal says whether it was the codes or ownership
  (`Why`, `Func::refusal`): the code-refusal probes answer `Some(WCodes)`
  (`interfaces_tests`), and the experiments' refused programs `Some(WOwn)`
  (`refusals_owned`, which replaces `refusals_coded`).
- **A plain variable a live region reads does not die** (a checker
  refusal): the invariant needs every word a region reads to stay a plain
  variable.

**The invariant's shape** (`Inv`; the reasons are beside its definition):
`root: Nat → Option<Ref>` (an object held by value has no root); the
cross-object clauses are per object over roots, so a binding touches none of
them: roots of objects one of which may change are apart (`apart`), every root
is in the heap (`inheap`, so a fresh block is past it), an object something
may change through has its root in a block lent to change or made here
(`owned`, which with `frame` gives the tightened `Frame` at `Ret`); a cell its
frame owns is its object's whole block, which no other object's root is in
(`own`); an object has one holder (`one`); every level a live region reads is
plain (`words`). A view's reference is one of its entries' object's root
narrowed (`RefOk`), since after a join a read view's entries may be of several
objects. `Inv::start` proves every clause at entry.

Found for the call stage (item 4), reported and not yet built: a written
parameter's slot in the answer must be the argument where it refers, and two
fresh results of one call must be distinct blocks; and three checker defects,
each a refusal to add (a join over a read-lent holder binding an owned
output; an arm yielding one holder twice; a returned view's region reading a
non-plain level in the caller).
