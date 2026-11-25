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
| Borrows for a call | `FTm::Lend` and `FView`; FunctionIR `View`; machine `Loan`, `Viewed`. Views of one buffer, any of them written (`split_at_mut`), are lowered where the path knows them apart, by value or a comparison on the path; `ViewsApart` is the fact that licenses the call (`views-of-one-buffer-apart`). |
| Several written spans | In FunctionIR and the machine, built (several written views, of one buffer or several); in `rt`'s meaning, not built (`rung2-spans-design.md` §6). |
| Linearity | The reflector's refusals for the world and the span (`rt_reflect.hthr`). No judgment over `FTm`, `ETm` or held code: only pure `Fun` goes through `Setup`. |
| Typed references | None in compiled code. A window is two words, a vector handle a `u64`, laid records nest by value. In the meaning, a window and a vector are handles with keys into erased claims (`arena_handles.hthr`, §10.7 "Built"). |
| Lenses | `Location`, `LocationLaws`, `Disjoint` (`lib/std/machine/location.hthr`), total only; `Part` and `Stored` for laid records. |
| Footprints | `Span`, `SpanSet` with deciders (`span_set.hthr`); the separation algebra over them, fractions, an access map and the store frame theorem (`docs/library/separation-algebra-design.md`, built 2026-11-24 in the first wave). |
| `mut` in the surface | A parser desugaring; the AST's `Param` has no mode, and a `mut self` method is known by its `Mutated` result type alone. `&` is an infix token only. **Since built** (`ownership-parameter-modes`, `sequencing-surface-design.md` §24): `Param::mode`, `x: &T` and `x: &mut T` on any parameter, `&mut place` at a call, the modes readable by a generator (`tactic::modes`). |
| Erased parameters | A parameter whose type is a proposition (`∥P∥`) or `Erased<A>` is no word of the code wherever it stands, in a function of a laid record and one of a `Bytes(n)`; a call's erased arguments are dropped at any position. The arena's `read` and `store` are `runtime fn`s keeping their found proofs (`runtime-erased-parameters`, §13 item 8). A plain function of words, a span writer, and a compiled caller of a function that takes one are refused by name (`runtime-erased-pure-shadow`). |
| `Copy`, `Clone` | No class. |

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
   read. Open still: how the reflector drops them (`runtime-erased-parameters`
   drops erased parameters; erased fields are the same question one level
   in).
5. The shape of the checker's annotations, and which of them a module's
   interface keeps.
6. The milestone's done-when (`docs/roadmap.md`, `nh-ownership`), to restate
   once the first wave has shown what holds.
7. Footprints beyond a list's indexes: a laid record's `Part` already
   carries a byte offset and size with read and frame laws
   (`lib/std/machine/part.hthr`) that are `PathIn`'s over bytes, so a
   field's path could be decided apart by its byte span. Not joined yet
   (`ownership-paths-footprints`).
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
   where the function does and holds at every value of it. A plain function
   of words that takes one is not compiled yet: the shadow `f::erased` (its
   reflection's meaning, listed in its callers' tables) was tried and taken
   out, and `runtime-erased-pure-shadow` has where it stopped and the route
   proposed instead. When the binder mode of
   `ownership-parameter-modes` lands, an erased mode can lower to this type,
   so the generator keeps one route. Item 4 (an arena's generation changed
   by a `mut self` method) is then an `Erased` field of the receiver or a
   parameter of its type; neither is built yet.
