# Ownership, borrows and shared mutation: the brief

Status: **a brief, 2026-11-24**: the direction Minus chose in discussion and
the questions still open, written so that a separate design session can
start from it. It is not the design. The design session's deliverable is the
rest of this file (§9), and it extends rather than replaces the decisions in
§4.

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
