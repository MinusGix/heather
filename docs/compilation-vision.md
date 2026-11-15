# Compilation in Heather: the vision, what is settled, and the open questions

Status: **a vision document, 2026-10-31**, written at Minus's request so that
design rounds on compilation start from what has already been thought out
instead of rediscovering it. It does not decide a round's details. Rounds
that touch compilation (native, `runtime fn`, `Compile`, `datarepr`, passes,
disciplines) read this first, then their own design note.

Minus (2026-10-31): *"We want compilation to be abstract after a fashion: common
cases run through `rt`, but you can do more specific 'separate languages' that
you tell it how to compile. DSLs, or internal language logic that is then
turned into much more efficient assembly, like an annotation that restricts the
code that could be written and then generates a more efficient version for the
platform. As well as making composition better: the compiler wanting a proof of
'is this value aliased'. A Rust-like borrow-checker annotation would generate a
`Compile` instance like `rt` does, and a bunch of separate side-proofs
automatically for the compiler to find. The compiler might try to search or
infer in some cases, like LLVM does, but intelligently, and thus producing a
proof of correctness. We are being ambitious."*

---

## 1. The principles that are already settled

None of these is new. Each was decided in an earlier round, and each is cited
so a round can read the argument instead of re-making it.

1. **Kerneltime and runtime are different worlds.** An ordinary `fn` is
   mathematics; it never runs. Spec types (`Nat`, `List`) are never run
   either: their runtime representations are chosen separately
   (`issues/datarepr-separation.md`, `docs/datarepr-design.md` §0).
2. **The certificate is logical; everything else is operational.** A
   compiled artifact carries a proof that it agrees with the function. Which
   artifact runs, how it was found, how it was searched for, how artifacts
   are cached: all policy, none of it able to threaten soundness
   (`docs/archive/compile-typeclass-design.md`, the principle stated once at the top).
3. **Untrusted search over checked witnesses.** Producers (reflectors,
   compilers, optimizers, analyses) may be heuristic, incomplete and
   aggressive, because each output is kernel-checked. A producer that cannot
   handle something declines; it never miscompiles
   (`docs/certifying-generator-design.md@4acf2fe`; `in-language-certificate-emission`,
   "compilation to good code is search, and untrusted search over checked
   witnesses is what lets the search be aggressive").
4. **Prove the generator, not the copies.** Where a producer is stable, its
   correctness is one theorem quantified over its inputs, and each output is
   an instance of it (`docs/archive/surface-v3.md` §1: "`equiv` quantifies
   over `ctx`, so every specialized emission is certified by the one
   theorem"). Experimental producers start certifying (a checked proof per
   output) and move into the verified theorem as they stabilise: a
   lifecycle, not a fork (`in-language-certificate-emission`, 2026-08-11).
5. **No per-program hand proofs.** The native compiler is proved once
   (`docs/native-program-logic-design.md`). A generated, kernel-checked
   certificate per program is fine; a human writing one is not.
6. **Small, inspectable statements per stage.** Per-pass certificates with
   small statements, never one leap with a page-long statement
   (`in-language-certificate-emission`, 2026-08-11; `datarepr`'s refinement
   ladder is this applied).
7. **Disciplines are libraries.** Ownership, linearity, constant time are
   decidable judgments over reflected code plus one soundness theorem. The
   kernel never learns the words (`issues/ownership-discipline-over-code.md`).
8. **Code is boxed and intensional.** Instances and analyses are keyed on
   syntax: refactoring a function re-runs what was derived from it
   (`docs/archive/compile-typeclass-design.md` §1).
9. **Opt-in.** A function runs only if someone asked: a `Compile` instance,
   written by hand or by a marker such as `runtime fn`
   (`issues/runtime-compile-opt-in.md`, Minus 2026-10-31).
10. **Smart instances, dumb resolution.** Context-specific compilation is an
    instance that consumes a context descriptor, never a resolver that picks
    different instances by context. Context facts can be proofs, so
    "optimization guards become propositions" (`docs/archive/surface-v3.md`
    §1).
11. **The total object language makes specialization tractable.** Partial
    evaluation by structural recursion over code terminates, and stuckness is
    syntactic; context-specific compilation is certified partial evaluation at
    instance level (`docs/archive/surface-v3.md` §3).
12. **The Right Way first.** Design is argued on semantics and principle,
    then cost (Minus, 2026-10-22).

---

## 2. The picture

```
            meaning: ordinary Heather functions and spec types (never run)
                               ▲ agrees (a proof)
   ┌───────────────────────────┴──────────────────────────────────────────┐
   │ Compile(f): code for f, and the proof it agrees with f              │  the one interface
   └───────────────────────────▲──────────────────────────────────────────┘
        produced by any of:    │
   ┌──────────────┬────────────┴──────┬────────────────┬──────────────────┐
   │ rt setups    │ DSL compilers     │ restricted     │ hand-written     │  languages
   │ (reflect any │ (a data language  │ dialects       │ instances        │
   │  runtime fn) │  with its own     │ (simd fn, ct fn│ (tuned IR and    │
   │              │  compiler)        │  …)            │  its proof)      │
   └──────┬───────┴─────────┬─────────┴───────┬────────┴─────────┬────────┘
          │      facts: side-proofs the compiler can ask for       │
          │  (NoAlias, Unique, InBounds, ConstantTime, Pure, …)    │  published, or inferred
          ▼                                                        ▼
   ┌──────────────────────────────────────────────────────────────────────┐
   │ code levels: Source (effects) ▸ FunctionIR (pure) ▸ machine (x86)    │  a producer may
   │ certified passes between them, each proved once, consuming facts     │  target any level
   └──────────────────────────────────────────────────────────────────────┘
          representations: datarepr (spec type ⇄ runtime layout, refinement)
```

### 2.1 `Compile(f)` is the one interface

Everything that runs is reached through `Compile(f)`: code for `f`, plus the
proof that the code agrees with `f`. It is an operation-indexed class keyed on
the function (`docs/runtime-fn-setups-design.md` §9.3). Callers find their
callees' code by instance search. Who produced an instance is invisible to
the caller, which is what lets every kind of producer below compose with
every other.

### 2.2 Languages: `rt` is the common one, not the only one

A **language** is a data type of terms, a meaning for them, a judgment of
which terms it compiles, a compiler, and one soundness theorem. That is the
`Setup` record of the setups note, read more generally:

```heather
record Language {
    Term: Type,
    meaning: Term → Meaning,       // what a term denotes, as ordinary Heather
    judge: Term → Verdict,         // which terms it compiles, with reasons
    compile: Term → Option<Code>,  // at whatever code level it targets (§2.4)
    sound: (t) → judge(t) = Ok → compile(t) = Some(c) → c.Agrees(meaning(t)),
}
```

The kinds differ in *where the term comes from*:

- **`rt`, the general language.** Its terms are reflected from ordinary
  function bodies by a generator, and tied to the function by a pin
  (`docs/runtime-fn-setups-design.md`). This is the common path: write
  Heather, mark it `runtime fn`, get code. Its setups (default, ownership,
  constant time) are judgments and lowerings over the same terms.
- **DSLs.** The user writes terms of the language as data (a regex, a
  parser grammar, a tensor expression, a state machine, a SQL-ish query, a
  packet format), usually through a notation or generator. The function is
  defined *as the meaning of a term*: `fn is_email(s) = EMAIL.matches(s)`.
  The DSL's compiler is free to do what no general compiler can (regex to
  DFA; a grammar to a table-driven parser; a tensor expression fused and
  tiled), and its soundness is proved once, for every term. Then
  `instance Compile(λ s => r.matches(s))` holds for any closed `r` by that one
  theorem. No reflection is needed: the term already is data.
- **Restricted dialects.** An annotation that *restricts* what may be
  written, in exchange for better code: `simd fn` (straight-line lanes, no
  data-dependent control), `ct fn` (no secret-dependent branch or address),
  `bounded fn` (no allocation, statically bounded loops, for interrupt
  handlers), `kernel fn` (a GPU-shaped map). Each is an `rt` setup whose
  judgment is stricter and whose lowering exploits the restriction. This is
  Minus's "annotation that restricted the code that could be written and then
  generated a more efficient version for the platform".
- **Hand-written instances.** Tuned code and its agreement proof, written by
  a person, for the hot inner loop nobody's compiler does well yet.

A language may also compile *into* another language rather than straight to
code: a DSL that lowers to `rt` terms reuses `rt`'s compiler and composes the
two soundness theorems. A tower of languages is a chain of small,
inspectable steps (principle 6).

### 2.3 Facts: side-proofs the compiler can find

Optimizations need facts: this pointer is not aliased, this index is in
bounds, this loop terminates within `n` passes, this call has no effects,
this branch does not depend on a secret. In LLVM those are analysis results
the optimizer trusts. Here **a fact is a proposition with a proof**, and an
optimization that uses it is proved once under it as a hypothesis.

- **Facts are class instances** the compiler searches for, so producing
  and consuming them are decoupled: a borrow-checked function publishes
  `NoAlias` and `Unique` instances about its code beside its `Compile`
  instance, and an unrelated pass that wants `NoAlias` finds them. That is
  Minus's "a bunch of separate side-proofs automatically for the compiler to
  find".
- **Facts come from four places**, cheapest first:
  1. a *verified analysis*: a decidable function whose soundness is proved
     once (a borrow check, an interval analysis), so a fact costs one
     evaluation by `refl`;
  2. a *setup's judgment*: the same thing, run when the function is
     compiled;
  3. *user lemmas*: a theorem the programmer proved about their function
     (`xs.len() ≤ 4096`), registered as a fact;
  4. *proof search*: the compiler asks a tactic to prove a fact it would
     like (`by omega`, `by bv_decide`, a custom solver). Search is untrusted;
     a found proof is checked; a failed search means the optimization is
     skipped, never a wrong program. This is "like LLVM, but intelligently,
     and producing a proof of correctness".
- **Facts cross function boundaries as contracts.** A fact about how `f`
  treats its arguments (does not retain them, writes only this buffer,
  returns within these bounds) is part of `f`'s interface, which callers'
  facts can be derived from. This is `issues/proof-carrying-function-analysis.md`'s
  "requirements and guarantees with evidence tied to the generated function",
  and it is what keeps whole-program optimization modular.
- **Facts are also context.** A call site's facts (`2 < xs.len()` in scope)
  ride the call's context descriptor, so a smart instance may specialize to
  them (principle 10): a bounds check elided *because a theorem says so*.

### 2.4 Code levels, passes, and representations

- **Levels.** `Source` (effects, as interaction trees), FunctionIR (total
  pure regions), and machine code (x86 `Prog` under `Sim`). Each has its own
  meaning and the levels are tied by theorems proved once
  (`native_compile_correct`, `compiled_returns`). A producer may target any
  level: most target FunctionIR or `Source`; a DSL that wants specific
  instructions (vector units, `popcnt`, `crc32`) can emit machine code
  directly, provided it meets the calling contract (N2's procedure contract
  and register convention) that lets other code call it.
- **Passes.** Optimizations between and within levels are certified passes:
  a structural algebra plus local laws, with one generic induction proving the
  pass sound (`docs/certified-pass-algebra-probe.md`;
  `function-ir-pass-in-heather` is the first real one). A pass that needs a
  fact takes it as a hypothesis of its local law.
- **One compiler serves the levels** (Minus, 2026-11-11: "unify first and
  then export"; `docs/native-one-compiler-design.md`). `write-elf` and
  `compile-x86` share FunctionIR and the region lowering and grew apart
  above it. The direction is one compiler of functions: a frame, System V
  registers, buffers lent, a body that may have effects. A pure function,
  a program's `main` and an export are its cases. The first joint is
  built: a program's call of a `runtime fn` is a CALL of the function
  compiler's code in the same file, proved from that function's contract.
  The second is built for reads: a function reads a buffer it is lent
  through a home (two of its values, address and length), under a
  comparison the path knows, and its contract says what it was lent
  (§2.5); a program's call passes its buffer's home, and a tool runs that
  reads its input and calls a compiled loop over it. `Compile(f)` says so
  for a function over memory: it is stated at every file, the function
  taking a span and its length word where its code takes the home, and
  one code serving every file, and a `runtime fn` whose leading
  parameters are a byte list and its length word is such a function, a
  loop over the span included. Such functions link into a program that
  is proved at every file, call one another over the same span, and a
  tool's call of one is proved to answer as the Heather function at the
  tool's buffer: `wc -l` counts with a `runtime fn`. What is left of it
  is writes. They are designed (`docs/native-one-compiler-design.md`
  §2.6): the file is state the meaning threads, and a caller lends a
  span by laws that say what a store into it leaves, which are what
  Rust's `&` and `&mut` give. The memory half is built
  (`x86_64_lending.hthr`), the function compiler's contract is stated
  under those laws with the file threaded (`Site::CallsOver`), and it
  compiles a store under the bound a load asks, into a span the lending
  lets be written; what such a function returns and leaves is stated by
  evaluation (`program_run`), the same at every address of the spans it
  is lent (`program_run_placeless`), and a program's meaning threads the
  file through its calls (`program_writers`). The program compiler
  proves such a call: it lends its buffers to write, and the statement
  after the call holds over the file the callee left
  (`Target::based_left`), so a program whose functions store links:
  `tr` runs with its loop a called function that rewrites the buffer
  (`raise_span`, a `runtime fn`). `rt` writes as
  a computation over the span, a layer over its pure terms as the layer
  over Linux is (`FTm`, `rt_file.hthr`): the meaning threads the bytes
  of the one span written, and the lowering's code runs to it
  (`FTm::lower_sound`, `rt_file_lower.hthr`). A computation that calls
  itself last under a measure is one loop with the span carried from
  pass to pass, proved once against any function that satisfies the
  body's equation (`FFun::measured_sound`, `rt_file_loop.hthr`); the
  measure may read the span. Such a function is ordinary Heather of
  type span to `Mutated`, a `mut self` method or a function returning
  the record, and its reflection is read from its elaborated body by
  the chain of stores and calls that makes each end's span
  (`rt_file_reflect.hthr`). Its class states the run
  (`CompileSpan<F>(f)`, `runtime_file.hthr`), and a program is linked
  from instances of both classes over the files with a span first, a
  function at a time (`program_spanned`, `function_ir_link.hthr`). The
  generator is `runtime fn`'s own, told by the type: a function whose
  type ends in `Mutated` gets a `CompileSpan` instance, a linked
  program and its run stated at every file (`f::runs_over`), with
  nothing proved for the function in particular. The third joint is
  built but for its last step
  (`docs/native-procedures-are-functions-design.md`, steps 5a to 5c): a
  statement's words are in a frame of its activation, the callee saves
  what it keeps and counts its own depth, one function emits every
  call, and one contract says a callee runs as its tree
  (`Target::Callable`), proved once at the call site
  (`Target::goes_calls`). A procedure meets it with its body's tree and
  a function with the tree that is a value, its proved return read as
  the answer. Still to come is one lowering of byte nodes. Calls keep
  two levels in the meaning, because a region is a total function and a
  statement is a tree: what a region calls answers with a value, what a
  statement calls may ask, run out of depth or exit, and recursion
  lives there.
- **Representations.** `datarepr` gives a spec type a runtime layout by
  certified refinement (`repr::BigNat` for `Nat`, `repr::Vec` for `List`,
  `docs/showcase/idealized.hthr`). Which representation a program uses is an
  operational choice with a certificate, like which `Compile` instance.

### 2.5 Memory a function is lent

Proposed 2026-11-10 (`docs/native-library-exports-design.md`); Minus's
answer (2026-11-11) was to join the two compilers first, so it lands in
the order of `docs/native-one-compiler-design.md`. Principle 1 applied to
memory:

- **A buffer is a value in every level's meaning.** A list of bytes in
  `rt`, a numbered entry of `Buffers()` in FunctionIR. No meaning mentions
  an address. Where a buffer lives (a caller's span, a static slot, an
  arena line, the frame) is a *home* the lowering is told, operational
  like a placement.
- **Addresses appear only in the theorem that ties a level to the
  machine**, and there a call's effect on memory is stated as the stores
  it may make (`Wrote`). What a caller wants kept, its frame, the code, the
  spans it lent, follows from that one relation, so exports, calls between
  compiled functions and `Proved` items share one footprint.
- **What a caller promises is a premise, stated semantically** (first
  `Lends`: no store the call may make changes what the span reads; with
  writes, the laws of a `Loan`, which say what each store leaves).
  Geometry, two
  spans sharing no address, proves the premise where addresses are
  numbers and is decided there, never inside the compiler's proof.
- **An access the machine may refuse is guarded by a comparison the path
  knows**, the default that always compiles; a fact (`InBounds`) removes
  the guard as an optimization (§2.3).

Built for reads in the function compiler (2026-11-11,
`function_ir_lower_reads`): the home is two values of the scope, carried
by loops and handed on by calls; the guard is the conditional the source
already has, known in the arm it selects, so the lowering emits no check
of its own. One thing the list above leaves open is settled in
`docs/native-one-compiler-design.md` §2.3: the lowered code is handed an
address as a word, so "no meaning mentions an address" needs the
evaluation not to depend on that word. An export gets this from its
agreement equation over an open word; a program's tree needs it as a
theorem about placeless functions. That theorem is built
(`program_eval_placeless`), and a program's compile cites it: the tree
states a call over the buffers the program holds with no address
(`program_readers`), the code passes the address the layout gives, and the
two answers are the same for every function `Prog::links` accepts.

---

## 3. Sketches

Spellings are illustrative. Each sketch says which parts exist.

### 3.1 The common case

```heather
runtime fn checksum(buf: Bytes(4096), n: BitVec(64)) → BitVec(32) {
    let mut acc = 0;
    for i in 0..n.toNat() { acc := acc.rotl(5).bxor(buf[i].zext()) }
    acc
}
// publishes instance Compile(checksum) via rt's default setup
```

Exists in part: the back half and `compile-x86`'s Rust reflector. Designed:
`docs/runtime-fn-setups-design.md`, `docs/sequencing-surface-design.md`.

### 3.2 A borrow-checked function and its side-proofs

```heather
owned fn reverse_in_place(mut xs: Bytes(4096), n: Nat) → Bytes(4096) {
    let mut i = 0; let mut j = n - 1;
    while i < j decreases j - i { xs.swap(i, j); i := i + 1; j := j - 1 }
    xs
}
// publishes:
//   instance Compile(reverse_in_place)          code that swaps in place, no copy
//   instance Unique(reverse_in_place, xs)       the input buffer is consumed, never shared
//   instance Writes(reverse_in_place, [xs])     the only buffer it writes
// a caller holding `xs` uniquely compiles its own call as a move, not a copy,
// because it finds `Unique`; a pass reordering two calls finds `Writes`.
```

Designed in outline only: `issues/ownership-discipline-over-code.md`, the
setups note §11.

### 3.3 A DSL with its own compiler

```heather
// lib/std/regex: a language, its meaning, and a compiler proved once.
inductive Regex { Chr(c: BitVec(8)), Seq(a, b: Regex), Alt(a, b: Regex), Star(r: Regex), … }
fn Regex::matches(self r: Regex, s: List<BitVec(8)>) → Bool { … }          // the meaning
fn Regex::dfa(self r: Regex) → Dfa { … }                                    // the compiler
theorem Regex::dfa_sound(r: Regex, s): r.dfa().run(s) = r.matches(s) { … }  // once

// The user writes a declaration under the language's generator (Minus, 2026-11-01):
regex def is_hex = "[0-9a-f]+";
// `regex` is a declaration-prefix generator like `runtime`, but it may ALTER the
// value: it parses the string into a Regex term and publishes
//   def is_hex::term: Regex = Plus(Range('0', '9') | Range('a', 'f'))
//   fn  is_hex(s: List<BitVec(8)>) → Bool = is_hex::term().matches(s)       // the meaning, by definition
//   instance Compile(is_hex) := is_hex::term().dfa().compile_with(Regex::dfa_sound(is_hex::term()))
// a runtime fn calling is_hex finds Compile(is_hex): a table-driven DFA, not a
// reflected backtracking matcher. No pin is needed, because is_hex IS the
// meaning of its term.
```

The frontend half exists (2026-11-01, `docs/value-definitions-design.md` §4):
`def`, prefix generators that rewrite the `def` they prefix, and
`lib/std/text/regex/regex.hthr`, whose `regex def is_hex = "[0-9a-f]+";` publishes
`is_hex` as `Regex::accepts` of the parsed term (a Brzozowski-derivative
meaning) and `is_hex::term`, tied by definition. Still missing: the `Compile`
class (§9.3 of the setups note), and a DFA compiler with its soundness and a
runner with its own `Compile` instance (an `rt` function, compiled once),
issue `regex-dfa-compiler`.

### 3.4 A restricted dialect

```heather
simd(lanes := 16) fn add_saturating(a, b: [BitVec(8); 16]) → [BitVec(8); 16] {
    a.zip_with(b, λ x y => x.add_sat(y))
}
// the simd setup's judgment: lane-wise, no data-dependent control or indexing;
// its lowering: one vector instruction (machine level, §2.4), proved once for
// every lane-wise term.
```

Nothing exists. It needs a machine-level target with vector instructions in
the ISA model.

### 3.5 The compiler asks for a fact

```heather
fn sum_prefix(xs: Bytes(4096), k: Nat) → BitVec(64) { … xs[i] … }   // i < k inside
// the bounds-check-elision pass wants InBounds(sum_prefix, xs[i]); it finds none
// published, so it asks: by omega over the loop invariant (i < k) and the
// caller's fact k ≤ 4096 (carried in the call's context). Found → the check is
// gone, proved; not found → the check stays.
```

A prototype exists over a small language of checked reads
(`docs/facts-on-demand-design.md`): a generator asks for `InBounds` per
read, the producers (a verified range analysis, user lemmas) answer first,
the compiler's own budgeted exhaustive check after them, and a read with no
proof keeps its check. Over `rt` code it waits on `runtime fn` reflection.

---

## 4. Open questions

The questions a design round would otherwise stall on. Each has a lean; Minus
decides.

1. **Is a `Language` the unit, with `rt` setups as one kind?** Lean: yes.
   The setups note's `Setup` record is a `Language` whose terms are
   reflected; a DSL is a `Language` whose terms are written. One record,
   one soundness shape, and composition by compiling one language into
   another.
2. **What is a fact's subject: the source function or the code?**
   `NoAlias` as a statement about `f`'s meaning is what callers and users
   reason with; a pass needs it as a statement about the code's semantics.
   Lean: both, with the producer that knows the correspondence (the setup)
   publishing the code-level fact derived from the source-level one, and
   contracts (question 4) at the source level.
3. **Which facts are standard?** A small vocabulary the compiler knows
   (`Unique`, `NoAlias`, `Writes`, `InBounds`, `Bounded`, `Pure`,
   `ConstantTime`, `Terminates(n)`), or open-ended classes any pass may
   define? Lean: open-ended classes, with a small standard library that the
   built-in passes use, like LLVM's attributes but each a proposition.
4. **How do contracts compose across calls?** A function's guarantees and
   requirements (`proof-carrying-function-analysis`) must be checked where
   it is defined and assumed where it is called. Lean: the contract is part
   of the `Compile` instance's interface (a stronger class, `CompileWith(f,
   contract)`), and N2's procedure contract is the first instance.
5. **What is the calling contract between producers at different levels?**
   A DSL emitting machine code must be callable from FunctionIR code. Lean:
   N2's register convention and frame contract are the one boundary every
   level meets, stated once.
6. **How abstract is the target?** Today there is one machine, x86-64 under
   Linux. A target as a *description record* (word size, endianness,
   features), not a tag, was the 2026-08-13 lean
   (`compile-typeclass-design` log). Lean: keep it, and let instances be
   generic over facts about the target (`any 64-bit LE target with
   AVX2`), so cross-compilation holds instances for several targets.
7. **Can a compiler run tactics?** Proof search for facts (§2.3, source 4)
   means a pass, written in Heather, sends goals to tactics. That is the host
   interface's request tree from inside a generator. Lean: yes, it is the
   same `Tac` loop; cost is budgeted per fact, and a failed search is a
   skipped optimization.
8. **Who searches: the compiler or the user?** An LLVM-style pipeline runs
   analyses everywhere; a proof-producing one costs a proof per success.
   Lean: verified analyses (cheap, one evaluation) by default, tactic search
   only where a pass asks and a budget allows, and an annotation to request
   more (`optimize(aggressive)`).
9. **Specialization: instances that consume context.** The `CallCtx`
   descriptor's shape is the old open question (principle 10). Lean: a
   coarse lattice of facts (known constants, ranges, uniqueness), so
   specialized copies are shared, and certified partial evaluation as the
   mechanism (principle 11).
10. **Representations and languages.** Is choosing `repr::Vec` for `List`
    a language choice (the `rt` term's types) or a separate axis? Lean: a
    separate axis, as `datarepr` designed it, read by every language's
    compiler through the type's registered representation.
11. **Where does a DSL's notation come from?** `regex!("…")` needs a
    generator that parses a string at elaboration time. Lean: the
    declaration and term generators of `scoped-declaration-generators`, with
    the parser library; no per-DSL syntax in the elaborator.
12. **How much of the compiler is itself a language?** If passes are
    certified algebras and producers are languages, the compiler is a
    library of them plus a driver. Lean: yes, and that is also the road to
    `hih-self`: the compiler compiles itself as a set of `rt` functions.

---

## 5. Where each part stands

| part | state | owner |
|---|---|---|
| back half (`Source`, FunctionIR, x86, ELF) | built, proved once | `docs/native-program-logic-design.md`, `docs/native-effect-source-design.md` |
| `rt` and setups | built: the reflected language, the default setup and the `runtime fn` generator (words, loops, buffers, `i64` by its representation); issues still open for what the default setup does not take | `docs/runtime-fn-setups-design.md`, milestone `nh-front` |
| `Compile(f)` class | built (`lib/native/runtime/runtime.hthr`); instances are linked into `f::program` | `issues/compile-typeclass-design.md` |
| libraries and exports | word functions built and linked (`crates/linked`); memory the caller lends designed (§2.5) and built for reads and writes inside one file (a program lends its buffers to a function it calls, which may store into them); a function that reads a span its Rust caller owns is exported, its declaration generated from the certificate's signature; the scanner's loop is one such function, proved to be the specification's scan of a token and called once a token from Rust; a function that stores into a span its Rust caller lends is exported too, the spans it may write read off its program and its wrapper taking `&mut [u8]` | `docs/native-one-compiler-design.md`, `docs/native-library-exports-design.md`, milestone `nh-library` |
| facts as classes, fact search | prototype landed: search rules, `Synth`, `request`, `InBounds` over checked reads, `Unique` over `rt` writes (ownership judgment, per-site check, write plan) | `docs/facts-on-demand-design.md` §7, `issues/facts-on-demand.md`; the in-place lowering's theorem is `issues/unique-fact.md` |
| DSL languages | frontends built: `def` and prefix generators that rewrite a `def`; `regex def` parses to its term and meaning, no compiler yet | `docs/value-definitions-design.md`, `issues/regex-dfa-compiler.md` |
| restricted dialects | constant time surveyed | `docs/constant-time-survey.md` |
| ownership | direction issue | `issues/ownership-discipline-over-code.md`, milestone `nh-ownership` |
| certified passes | probe passed | `docs/certified-pass-algebra-probe.md`, `function-ir-pass-in-heather` |
| representations | v1 built | `docs/datarepr-design.md` |
| specialization (`CallCtx`) | sketched | `docs/archive/surface-v3.md` §1, §3 |
| contracts across calls | direction issue | `issues/proof-carrying-function-analysis.md` |
| foreign code as an instance | surveyed, not scheduled | `docs/foreign-binaries-survey.md`, `issues/foreign-binary-contracts.md` |

---

## 6. Minus's answers (2026-11-01), and where they leave the questions

- **DSL declarations** (§3.3): a language's generator prefixes a declaration
  and may alter its value: `regex def is_hex = "[0-9a-f]+";`, parsed by the
  `regex` generator into a term, published as the term's meaning plus its
  `Compile` instance. Needs a proper `def` (`value-definitions`).
- **The `simd` sketch** (§3.4) is the right shape.
- **Q1, `Language` as the unit**: "plausibly", with the reasoning asked for.
  It is §6.1 below.
- **Q2, the subject of a fact**: both, and they interrelate. Sometimes a
  mathematical fact about the function is wanted, sometimes a fact on the
  code; one may be derived from the other.
- **Q3, which facts**: open classes. Standard *dispatch methods* do not
  materialise until requested: not every function needs every fact, so a
  fact is produced on demand. A borrow-checked function produces "is this
  aliased" cheaply; for any other function the request goes to a function or
  tactic that may fail. To the compiler it is an opaque, usually cheap proof
  (§6.2).
- **Q4, contracts across calls**: unsure; stays open.
- **Q5, tactics in the compiler**: yes, in Heather. General correctness
  proofs (proved once, never executed per program) sit beside proof search.
  There is no strong boundary between a check ("is there an alias") and a
  search for a proof of it: an LLVM-style check is a search with a tight
  budget. Both are tuned and fuel-bounded (§6.2).
- **Q10, representations**: a separate axis; each language decides how it
  uses a `datarepr`. For runtime code the lean is *invisibly generic*:
  `runtime fn`s are generic over the representations of the spec types they
  use, and the choice flows down from `main` (or the program's root), which
  carries a set of defaults. Unsettled.

### 6.1 Is `Language` the unit? (Q1, the reasoning)

Yes, with one split that the `regex def` form makes visible: **a language and
a frontend are different things.**

- A **language** is what has a compiler proved once: a term type, a meaning,
  a judgment, a compiler at some code level, and its soundness theorem.
  `Regex` with `dfa_sound` is one; `rt` with a setup's `sound` is one.
- A **frontend** is how a declaration becomes a term of a language, and how
  the declared name is tied to the term's meaning. There are three ways, and
  they differ exactly in what has to be checked per declaration:
  1. *Definitional* (`regex def`): the generator defines the name as the
     term's meaning, so the tie is a definition and costs nothing.
  2. *Reflective* (`runtime fn`): the user wrote an ordinary body, the
     generator reflects it into a term, and the tie is the pin
     `term.meaning = f` by conversion (setups note §4.3).
  3. *By hand*: the user writes the term, or the code and its proof
     directly (a hand `Compile` instance).
- A **setup** is then a language over `rt`'s terms with its own judgment and
  compiler: the default setup, `owned`, `simd`, `ct`. A dialect is a setup
  whose judgment is stricter.

What the split buys:

- **One soundness shape for everything that compiles**, so the compiler and
  the facts machinery treat a DSL, a setup and a dialect alike.
- **Languages compile into languages.** A DSL may lower its terms to `rt`
  terms (a parser grammar to an `rt` loop) and reuse `rt`'s compiler; the
  two soundness theorems compose. A tower is a chain of small statements
  (principle 6).
- **Frontends are where syntax lives.** The prefix generator owns parsing
  (`regex`'s string, `simd`'s lane annotation) and naming, so a language
  never needs elaborator support of its own.
- **Facts attach to languages.** A language whose judgment proves
  non-aliasing offers the `NoAlias` dispatch method for every function it
  compiled (§6.2).

What it costs, honestly: `Language` must be generic over its code level
(FunctionIR, `Source`, machine) and over the facts it offers, so the record
is larger than the setups note's `Setup`, and the one soundness shape is
really a family indexed by the code level. The setups note's `Setup` is the
FunctionIR-level member of that family. That is the only real cost, and it
is the price of a DSL being able to emit vector instructions directly.

### 6.2 Facts on demand: dispatch methods, and checks as searches

From Q3 and Q5 together:

```heather
// A fact is an open class over a function (or a code position, Q2).
class NoAlias<F>(f: F, arg: Nat) { proof: … }        // a proposition, its proof

// Producers register a dispatch method, not a proof: nothing is built
// until a pass asks.
instance(f) NoAlias(f, i) given Owned(f) := owned_noalias(f, i)   // cheap: read off the borrow check
instance(f) NoAlias(f, i) := by search(budget := small) { alias_tactic }   // anything else: may fail
```

- **Lazy.** A fact is resolved when a pass asks for it, so a program pays
  only for the facts its optimizations want. Instance search is the
  dispatch: the most specific producer (the language that compiled `f`)
  first, the generic search last.
- **A check is a search with a budget.** An LLVM-style alias check and a
  tactic that searches for a proof of non-aliasing are the same request at
  different fuel. A *verified* check (a decision procedure proved sound
  once) answers by evaluation, so its proof is one `refl`; an unverified
  search answers with a proof the kernel checks. A failed or exhausted
  search means the optimization is skipped.
- **Opaque to the compiler.** A pass sees a proof of the proposition it
  needs, never how it was found, so producers can improve without touching
  passes.
- **Cost.** A fact that is cheap for its producer (the borrow check already
  ran) stays cheap; a searched fact is budgeted per request, and the budget
  is a knob (`optimize(aggressive)`, Q8).

The first prototype of this section is `docs/facts-on-demand-design.md`: a
fact is a proposition whose producers are evidence rules (no coherence is
needed, since no one observes which proof was found), a producer that
searches is an evidence rule whose premise runs a tactic, and a generator
asks with the `Synth` host request, hearing `None` when nothing is found.

### 6.3 Questions still open

Q4 (contracts across calls), Q6 (how abstract the target is), Q8 (who pays
for search by default), Q9 (`CallCtx`), Q10's details (how representation
defaults flow from `main`, and what "invisibly generic" costs in
specialization), Q11 (notation: now answered for DSLs by prefix generators
that parse a string or a block), Q12.
