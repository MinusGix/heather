# Compiling the specification's own shapes — design

Status: **design note, 2026-11-14, for Minus's agreement before any slice is
built.** Extends `docs/datarepr-design.md` (§3's transfer generator, §5.2's
"bytes" stage) and `docs/compilation-vision.md` (§2.4's representations, Q9's
specialisation, Q10's representations as a separate axis). Brief: section 6 of
`/mnt/project-files/design/language-feature-threads-2026-11-14.md`. Issue:
`issues/compile-specification-shapes.md`. Hand-run:
`lib/_tests/native/spec/extend_handrun_tests.hthr`.

Minus (2026-11-14): *"we should avoid distorting design by missing important
language features as we want the language features!"*

---

## 0. The problem in one paragraph

There are two SHA-256s in Heather. `lib/std/crypto/sha2.hthr` is the
specification: lists of words, `Nat` recursion, a record of eight words, a
family record `Sha2` that the functions take as their first argument, and it
"is written to be read against the standard, a section at a time, and nothing
here is shaped for a machine". `lib/native/crypto/` is the compiled one:
arrays in a laid record (`Sha256 { hash, working, schedule, count }`), word
loops under `decreases` with an `if h:` test, `put`/`at` at word indexes. The
second exists only because `runtime fn` cannot take the first, and the proof
that the two agree is the hand work that `issues/sha2-compress-native.md` says
waits on Minus. This note says how the first is compiled as written: the
compiled copy is still there, but a generator writes it and proves it, and
nobody reads either.

---

## 1. What `sha2.hthr` asks of a compiler

Every function of the specification, by the shapes it uses. "Exists" means
the `rt` language or the record-function generator already takes the shape.

| function | shapes | exists | missing |
|---|---|---|---|
| `ch`, `maj`, `Sha2Counts::big/small` | words; rotate and shift by a count | words, rotations (§16.12 of `runtime-fn-setups-design`) | the counts are fields of a closed argument (§3.1) |
| `t1`, `t2`, `turn`, `round`, `plus` | a record of eight words as a value | records as their fields (§16.7 there) | eight words across a call (`function-call-past-six-words`) or in the span (§3.5) |
| `word`, `start` | `nth` of a closed `List<Nat>` at a closed or word index | — | a closed list read at an index is a constant table (§3.1) |
| `window_word`, `next_word`, `push` | `nth(i).unwrap_or(0)` and `Cons` on a list of words | — | a bounded list held as an array (§3.3) |
| `extend` | structural recursion on a `Nat`, its step after the recursive call | `Count` and tail recursion on it (§16.10 there) | a step-after recursion as a loop (§3.4) |
| `schedule` | `rev` of a list; `rounds() - 16` | — | `rev` as a change of representation that moves nothing (§3.3) |
| `run`, `compress` | step-after recursion carrying a record of words; `from + n` | — | §3.4 with a record in the loop's state; a `Nat` sum held as a word (§3.2) |
| `be_bytes`, `spell_word` | recursion whose other argument changes (`value / 256`) | — | declined in the first cut (§3.4) |
| `pieces`, `words`, `blocks`, `pad`, `hash` | a message of any length; lists of sublists | bytes in a span, a length word | a list that is a stretch of another's storage (§7) |
| `be_value`, `foldl`, `foldr`, `map` | folds over a list | — | a fold over a held list is a loop over its indexes (§3.4) |

Nothing in the specification needs a new kernel feature or a new code level.
What it needs is representations for four spec shapes and one more loop
shape, plus a way to ask for a function at a closed argument.

---

## 2. The route: transfer, then compile

### 2.1 What is settled that the route rests on

`docs/datarepr-design.md` §3 already decided the architecture, for a
smaller fragment: a spec function over a repr'd type is **transferred** to an
ordinary Heather function over the carrier, with a kernel-checked `refines`
theorem (`abs(f_r(x)) = f(abs(x))` under `inv`), and "a reprgen output is an
ordinary Heather `fn` plus theorems, which certgen can then take to IR — the
two certificates composing by transitivity at the Compile layer, no shared
trust". `reprgen` (`crates/elab/src/reprgen.rs`) does this today for
structural functions over byte-free reprs.

The vision's principle 4 says how such a producer matures: it starts
certifying (a checked proof per output) and moves into one theorem proved
once as it stabilises. Principle 11 says specialisation at a closed argument
is certified partial evaluation. §6 (Q10) says representations are a separate
axis each language reads.

### 2.2 The pipeline

```
Sha2::extend(Sha2::sha256(), count, window)      the specification, unchanged
        │  transfer (generated, checked): specialise at the closed argument,
        │  hold each spec type by its representation, a recursion as a loop
        ▼
runtime fn Sha2Window::extend…(mut self s, len, count: u64) → u64
        │  + refines: abs(result) = Sha2::sha256().extend(count.toNat(), abs(s, len))
        │  the record-function generator, as it is (rt_held_reflect, runtime.hthr)
        ▼
code + runs_held: where the span holds s, the code leaves what the function leaves
        │  composed (one generated theorem, by transitivity)
        ▼
where the span holds a window w, the code leaves bytes whose window is
Sha2::extend(Sha2::sha256(), n, w)
```

The middle function is what `lib/native/crypto/sha256_schedule.hthr`'s
`Sha256::expand` is today. The difference is who writes it, and that its
agreement with the specification comes with it.

### 2.3 The alternative, and why not first

The other route is to teach `rt` itself the spec types: a `Ty::List(elem,
cap)` beside `Ty::Bytes(cap)`, the reflector reading spec bodies directly,
the lowering's `Holds` relating an array in memory to the list, and every
law proved once inside the lowering. It is where shapes should end up
(principle 4), and it is a single certificate rather than two. It is not the
first step, for three reasons found in the code:

- `rt`'s agreement theorems are unconditional (`program_eval(…) = f(…)`),
  and a list held in a fixed array is only a list while it fits: a push is a
  constructor's image guarded by room (`datarepr-design` §1.3, FINDING 1).
  The guard has no place in `rt`'s statements; it has one in a `refines`.
- `rt`'s pure layer does not hold memory (`Ty::Holds` at `Bytes` is `True`,
  at `Lines` it is `False`); memory is the span layer's (`FTm`,
  `rt_held`). A list in an array is a span-layer value, which is what the
  record-function generator already compiles.
- A step-after recursion is not a pass of `rt`'s fuel loop, which is tail
  recursion (§16.10 there); the reflector would need the loop transform
  anyway, and the transform's proof is the same theorem either way (§3.4).

So the transfer is the certifying producer, the record-function generator is
the code level, and the shapes that stabilise move into `rt` later with the
proofs the transfer already uses.

---

## 3. The four shapes and the loop

### 3.1 A closed record argument: specialisation is conversion

A request names the function at its closed arguments:
`Sha2::extend(Sha2::sha256())`. The transfer works on that partial
application. Every projection of the closed argument it meets
(`p.width`, `p.small1`, `p.k`) it asks the host to reduce (`Unfold`, the
numeral request), so `BitVec(p.width)` is `BitVec(32)` and
`p.small1.small(x)` is `Sha2Counts(17, 19, 10).small(x)`, rotations by
literal counts. Nothing is proved for this: the statement is about the
partial application, and the generated body converts with it (δ on
`Sha2::sha256`, ι on the record). The hand-run's `extend_next` is written with
the literal counts and its law is checked against `Sha2::sha256().next_word`.

Two things follow:

- **A closed list read at an index is a table.** `p.word(p.k, from + n)`
  is `nth` of a closed sixty-four-element list at a word: a constant table
  in the program (today `sha256_k` is a tree of comparisons; a table is
  `rt-fixed-arrays-and-tables`). Its law is one evaluation per entry, or
  the table's own `refl`.
- **Unread fields cost nothing.** `Sha2::extend` never reads `p.k`, so the
  sixty-four constants are never unfolded in its certificate.

This is the vision's Q9 at its simplest point: the context is "these
arguments are these closed values", and the instance is the transfer at them.

### 3.2 A `Nat` with a bound, held as a word

`rt` already holds a `Nat` in a word (`Ty::Count`, `values(64, p).toNat() =
n`, §16.10 there), so every `Nat` below `2^64` has a word. The rule from
`datarepr-design` §1.3 carries over exactly:

- **Consumption is total.** A `match` on a count is a test against zero and
  a decrement, with no precondition; `count` in `Sha2::extend` is consumed
  only.
- **Production is guarded.** `from + n` in `Sha2::run` is a word add only
  where the sum stays below `2^64`. The transfer states that as a
  precondition of the function it writes and discharges it from what bounds
  the loop (`from + n <= rounds() = 64`); where it cannot, it declines with
  the reason. A fact search (`omega`, vision §2.3) is the general discharger,
  and the first cut asks it only for sums of a loop's counter and a bound.

### 3.3 A bounded list, held as an array

A `List<A>` whose length stays below `n` is held as `v: [A; n]` and a length
`len`, its entries `0 … len - 1`. Two readings of the same storage:

- **queue order**: `v.queue_abs(len) = [v[0], …, v[len - 1]]`, oldest first;
  `Cons` is not cheap, appending at the end is.
- **stack order**: `v.stack_abs(len) = [v[len - 1], …, v[0]]`, newest first;
  `Cons` is a store at `len` (`push`), `nth(back)` is a read at
  `len - 1 - back`.

The specification's window is newest first and grows by `Cons`, so it is held
in stack order, and then its reads are FIPS's own indexes: `window_word(w, 1)`
is `v[t - 2]`, `window_word(w, 15)` is `v[t - 16]`. That is `Sha256::expand`'s
body, derived rather than written.

`rev` between the two orders moves nothing: `v.stack_abs(len) =
v.queue_abs(len).rev()`. So `Sha2::schedule(block) = p.extend(48,
block.rev()).rev()` holds its block in queue order, the inner `rev` is the
same array read in stack order, and the outer `rev` reads the result back in
queue order. The two `rev`s compile to nothing. This is `datarepr-design`
§5.3's "inter-repr conversions are ordinary certified `Impl`s, never
compiler-inserted": the conversion is the spec's own `rev`, written in the
specification, and its `Impl` between the two orders is the identity on the
carrier.

The representation's laws, proved once (hand-run, `Vec::stack_read_abs`,
`Vec::stack_push_abs`):

- **A read needs no invariant.** `v.stack_abs(len, pad).nth(back).unwrap_or(pad)
  = v.stack_read(len, back, pad)`, where `stack_read` reads `v` at
  `len - Succ(back)` when `back < len` and answers `pad` otherwise. With the
  carrier's own reads padding past the array's end, the law holds for every
  `len`; the specification's `unwrap_or(BitVec::zero())` is the same pad.
- **A push needs room.** `vector_update(v, len, x).stack_abs(Succ(len)) =
  Cons(x, v.stack_abs(len))` under `len < n`: `Cons`'s image, guarded
  (`issues/datarepr-guarded-images.md` is the `datarepr` form for exactly
  this). A transferred function that pushes inherits the guard as a
  precondition, accumulated over its loop (§3.4).

Where the array lives is the layout library's business: a field of a laid
record over the span the function is lent (`Sha256::schedule` today). The
length is a word beside the span, the way a span's length word is beside its
bytes; holding it in the record instead costs a load and a store per pass and
is the operational choice of a later round.

### 3.4 Structural recursion, compiled as a loop

Two shapes of structural recursion on a count, both one loop:

- **Tail**: `f(Succ(k), x) = f(k, g(x))`. `rt`'s fuel loop already compiles
  it (`Fun::lower_fuel`), from two equations the generator proves by `refl`.
- **Step after**: `f(Succ(k), x) = step(f(k, x))`, the argument fixed (
  `Sha2::extend`, `Sha2::run`). It is the tail loop that applies `step`
  `count` times from `x`, and that it is so is one theorem, proved once and
  for every representation (`Nat::loop_refines` in the hand-run): given a
  carrier `R`, an abstraction `abs(r, len)`, a pass on the carrier and a
  room bound `cap`, if one pass refines one step where there is room, then
  `count` passes refine `f(count, ·)` wherever `len + count <= cap`.

  ```heather
  theorem Nat::loop_refines<R, X>(abs: R → Nat → X, pass: R → Nat → R, step: X → X, cap: Nat,
      pass_abs: (r: R) → (len: Nat) → len < cap → abs(pass(r, len), Succ(len)) = step(abs(r, len)),
      F: Nat → X → X, F_zero: …, F_succ: (k, x) → F(Succ(k), x) = step(F(k, x)),
      L: Nat → R → Nat → R, L_zero: …, L_succ: (k, r, len) → L(Succ(k), r, len) = L(k, pass(r, len), Succ(len))):
      (count, r, len) → len + count <= cap → abs(L(count, r, len), len + count) = F(count, abs(r, len))
  ```

  What a function supplies is `pass_abs` (§4) and four equations that are
  `refl` for a function and its generated loop.

A step that reads the counter (`Succ(k) => step(k, f(k, x))`, as `run` reads
`from + n`) is the same theorem with the counter carried as a word of the
loop's state; it is the next slice's addition. A recursion whose other
argument changes (`be_bytes(value / 256, k)`) is declined in the first cut:
going up needs the argument's sequence computed forwards, which is a
different theorem per argument function. Folds over a held list (`foldl`,
`map`) are a loop over the list's indexes, the tail shape again, with the
list's reads as the pass's.

### 3.5 A record of words, as a value

`Sha2State(32)` is eight `BitVec(32)` fields. Inside one function, `rt`
already holds a record as its fields (§16.7 there: scalar replacement,
`Field` free, `Make` a move per field), so `turn` and `round` are eight
words in and out of a region with no new theory. At a boundary there are two
holdings, both a representation of the same record:

- **in the span**: the record as `[u32; 8]` in a laid record's field, read
  through `Sha2State::words()` (its `abs` is the record built from the eight
  entries);
- **in registers**: eight words passed and returned, which is
  `issues/function-call-past-six-words.md` (another thread's).

The transfer picks the span holding for a record that is a loop's state
(`run` carries one across sixty-four passes) and leaves the register holding
to the calling convention when it lands.

---

## 4. What is generated and what is proved once

| piece | written | proved |
|---|---|---|
| a representation's carrier and laws (`stack_abs`, `stack_read_abs`, `stack_push_abs`; queue order; a word for a count) | once, in a library | once, by hand |
| a loop shape (`Nat::loop_refines`; the tail shape is `rt`'s) | once | once |
| the conversion between two orders (`rev`) | once | once (not in the hand-run yet) |
| a function's specialisation at a closed argument | per request, by the transfer | conversion |
| the repr-side function: a pass and its loop, a `runtime fn` of a laid record | per function, by the transfer | — (it is a definition) |
| the pass's law (`extend_pass_abs`) | per function, by the transfer | a chain of the representation's laws and `cong`, one per read and one per push |
| the function's `refines` | per function, by the transfer | one application of the loop theorem |
| code and `runs_held` | per function, by the record-function generator | the generator's own, unchanged |
| the end statement over bytes | per function, by the transfer | transitivity of the two |

Nothing is proved by hand per function. The per-function proofs are the
certifying producer's outputs; the day the pass law is itself a theorem over
the transfer's input (a transcription datatype whose soundness is proved once,
`datarepr-design` §3.1 phase 4's "small expression datatype"), the producer
becomes verified and stops emitting them.

---

## 5. The hand-run

`lib/_tests/native/spec/extend_handrun_tests.hthr` writes out by hand, at
`Nat` lengths, what the transfer would write for `Sha2::extend` at
SHA-256, and checks it:

- the representation: `Vec::stack_abs`, `stack_read`, and their two laws;
- the loop shape: `Nat::iterate_shift` and `Nat::loop_refines`;
- the function: `extend_next` (the pass's word, at literal counts),
  `extend_pass`, `extend_loop`, and `extend_loop_refines`:

  ```heather
  theorem extend_loop_refines(count: Nat, v: [BitVec(32); 64], len: Nat, room: len + count <= 64):
      extend_abs(extend_loop(count, v, len), len + count) = Sha2::sha256().extend(count, extend_abs(v, len))
  ```

  whose proof is one application of `Nat::loop_refines`, with `refl` for the
  four equations;
- a negative control: a pass that reads seven back where the specification
  reads six is refused by the pass law's `rewrite`.

What it showed:

- **The per-function certificate is small and schematic**, as the table in
  §4 says: `extend_next_abs` is one `rewrite` by four instances of the read
  law, `extend_pass_abs` one push law and one `cong`, and the function's
  theorem one application. The whole module checks in seconds.
- **Specialisation costs nothing to prove.** `Sha2Counts(17, 19, 10).small`
  against `Sha2::sha256().small1.small`, and `List<BitVec(32)>` against
  `List<BitVec(Sha2::sha256().width)>`, are conversions the kernel does
  without help.
- **The read law needs no invariant** once the carrier's reads pad, which is
  why the only precondition is the push's room. A first sketch with
  `len <= n` as the representation's invariant was unnecessary.
- **A step-after recursion is a tail loop by one generic theorem**, not by
  an induction per function: `iterate_shift` (the step commutes with the
  recursion) is the only lemma it needs.

What it did not check: the word level. The hand-run's lengths and counts
are `Nat`; the function the record-function generator compiles has `u64`
ones and `at`/`put` with found proofs. The bridge is `rt`'s `Count` holding
(`toNat`) and one lemma, `(len + 1).toNat() = Succ(len.toNat())` below the
room, which the loop theorem's word form takes as its `Succ`. The first slice
(§6) is where that is checked.

---

## 6. The request, and the first slice

### 6.1 How a function is asked for

The specification is never edited: it is mathematics and stays so. A request
lives where the compiled code is wanted, as a generator call, the way `laid`
is asked for a record declared elsewhere:

```heather
// lib/native/crypto/…, or a probe
generate compiled(Sha2::extend, at := [Sha2::sha256()],
    hold := [window := Stack(Sha256, schedule)], into := "Sha256::schedule_words");
```

Spellings are illustrative. What a request names: the function; its closed
arguments; for each list or record parameter, its representation and where
the representation's storage is (a laid record and a field); the name of the
generated function. A count is held as a word without being asked. The
request publishes the generated `runtime fn`, its `refines`, and the end
statement over bytes.

Where a request's choices come from later: the representation by the
registry's default for the type (`datarepr-design` §5.2's auto-pick), the
storage by a layout the program's root chooses (vision §6, Q10's
"invisibly generic … from `main`"), the room from a fact search over the
calls. None of that is needed for a function to compile once a person names
them.

### 6.2 The first slice: `Sha2::extend` at SHA-256

- A library module (`lib/native/spec/` or beside the layout library) with
  the stack and queue representations of `[A; n]`, their laws, the `rev`
  conversion, `Nat::loop_refines` and its word form.
- The transfer as a Heather generator (the direction of
  `generators-in-the-language`; `reprgen` is Rust and stays as it is),
  taking the shapes of §3.1 to §3.4 and declining anything else with the
  reason, the way `reprgen` and the reflector decline.
- One request: `Sha2::extend` at `Sha2::sha256()`, its window in a laid
  record's `[u32; 64]` field.

**Done when** `Sha2::extend` at SHA-256 is compiled from `sha2.hthr` as
written, with the end statement over bytes published by the generator and
checked; a negative control (a perturbed pass law) is refused; and the
linked code computes the schedule of a NIST block's words. No `Sha256::expand`
is written for it. Whether `sha256_schedule.hthr` then uses the generated
function is the native lexer and crypto thread's choice.

What it needs from other threads: nothing it cannot work around. The
record-function generator takes the shape the transfer writes today
(`decreases`, `if h:`, `at`/`put` with found proofs, as `Sha256::expand`
reads); when the `for` and `v[i]` thread lands, the transfer writes that
spelling instead, and the generated text reads like the hand one.

### 6.3 The slices after it

In order, each a function of `sha2.hthr` more:

1. `Sha2::schedule`: the block in queue order, `rev` as the conversion,
   `rounds() - 16` folded by specialisation.
2. `Sha2::run` and `compress`: a step that reads its counter, a record of
   words in the span as the loop's state, the constants as a table.
3. `Sha2::hash` over a message of any length: §7.
4. `Sha2::digest`: `spell_word`'s varying argument, the last decline lifted.

At the end of 2 the compiled compression function is the specification's,
which is `issues/sha2-compress-native.md`'s "`compress = spec` as one
theorem", by generation.

---

## 7. What this note does not settle

- **Lists of sublists** (`pieces`, `blocks`): a block is a stretch of the
  message's storage, so a `List<List<A>>` whose elements are windows of one
  span is a representation by views (an offset and a length per element),
  which is the arena's (`Lines`) generalised. Its laws are `take`/`drop` of
  the parent's (`list_window.hthr` has most of them). Designed when slice 3
  starts.
- **A message of any length**: the span is the message, its length a word,
  and `pad` writes past the message's end into room the caller lends. The
  room is the request's; the precondition is the caller's.
- **Inlining and calls**: the transfer writes one function per loop, with
  every non-recursive callee inlined into its pass, because the
  record-function reflector refuses a call of an unmarked function. The
  pass law keeps one lemma per callee, so a callee's law is reused across
  requests even when its code is not.

---

## 8. For Minus

1. **The route** (§2): transfer to a generated `runtime fn` of a laid
   record, with a generated `refines`, then the record-function generator as
   it is. Lean: yes; `rt` learns spec types later, with these laws.
2. **The request** (§6.1): a generator call beside the compiled code, the
   specification untouched; the representation and its storage named in the
   request for now. Lean: yes.
3. **A push's room** (§3.3): a precondition of the generated function and of
   the end statement, with the compiled code keeping the comparison the push
   needs for its found proof (the vision's §2.5 default), and a fact
   removing it later. The other rung, an outcome the function returns when
   full, changes what the caller sees and is not needed by any function of
   `sha2.hthr`. Lean: precondition.
4. **The length word beside the span** (§3.3), not a field of the record.
   Lean: beside.

---

## 9. Rejected

- **A `runtime` marker on the specification** (`runtime fn Sha2::extend`):
  the specification would be shaped for the machine, and the marker cannot
  say at which closed argument or in which representation.
- **One `rt` term for the whole family** (`p` as a run-time record): the
  width is a type index, so there is no single code for both widths without
  a run-time width, and SHA-256 at a run-time width is slower for nothing.
  Specialisation is per member, which is what `Sha2::sha256()` names.
- **Proving the hand copy against the specification** (the route
  `sha2-compress-native` waits on): it is the per-program hand proof the
  vision's principle 5 rules out, and every function written that way is
  written twice.
