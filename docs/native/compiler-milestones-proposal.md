# Compiler milestones, reconsidered: ordinary Heather compiles

Status: **adopted, 2026-10-31 (Minus's decisions are recorded in §8).** Nothing here is built,
and its milestones are in `docs/roadmap.md`, with one issue per round. Written
on master `cb5331c`, after `hih-tools` reached nine of its fourteen tools.

Minus's ask (2026-10-31): Minus is not sure that building out the remaining tools
is the right target. It may be better to look at:

1. making the fundamental language better: less painful composing, and more
   imperative-style coding;
2. generalizing features rather than whatever the next program needs;
3. real work toward Heather in Heather, and its compilation.

This note turns those three into one direction, a set of milestones, and
ten ordered rounds. Each round can be handed to a thread as written.

---

## 0. Recommendation

**Make ordinary Heather compile.** Today a native program is not a Heather
function. It is a value of an untyped word DSL (the builder), written in
continuation-passing style and compiled through `Source`. The three
directions all come back to the same gap, so the plan closes it:

- The language gets **one sequencing surface**: a binding statement for
  any carrier with a `bind`, plus `let mut`, `:=`, `for`, `while` and early
  exit in pure functions. This removes the `bind` towers in tactics and the
  `local(…, λ x => …)` towers in tools with one feature, and gives
  imperative style in pure code (§3, milestone `lang-sequencing`).
- An ordinary Heather function compiles when it is marked **`runtime fn`
  under a setup**. A setup is a Heather library generator that boxes the
  function, checks a judgment over its code, and hands the compiler a
  lowering plus the proofs that judgment earned. The default setup takes
  words of any width, `Bool`, records and enums, `match`, recursion, calls
  that are not inlined, `uniq` capabilities for I/O, and heap data through
  `datarepr`. A second setup, Rust-style ownership, gives the compiler
  non-aliasing facts it can use. Each step is a general feature, not a
  tool (§4, milestone `hih-native-heather`).
- Heather in Heather gets **two concrete first components** on that
  compiler: Heather's own lexer, compiled natively and tested against the
  Rust lexer on the whole library; then the native compiler itself
  (`Source::compile`, already a Heather function), compiled natively and run
  where `write-elf` now evaluates it in the kernel. The kernel still checks
  its output, so this changes no trust, and it speeds up the step that the
  current cost profile says is the slowest (§5, milestone `hih-self`
  re-scoped).
- Proofs **compose against interfaces, not code**: a definition can be
  used through its equations and lemmas without being unfolded, automation
  finds a type's lemmas in registries instead of hard-coded tables, loops
  and procedures come with invariant and contract rules, and large proofs
  keep their sharing so they need no hand staging. Minus added this
  direction on 2026-10-31 ("it should be easy to prove your specific
  properties without needing to think about lots of code, and even the
  automation should try to be modular") (§6, milestone
  `lang-proof-modularity`).

**`hih-tools` stops being a target and becomes a regression corpus.** It
would close at the nine tools that are built. Every later round's "done
when" rewrites some of them in the new surface, and they must still pass
their GNU tests. `grep -F` and `sort` come back as the first customers of
procedures and of the heap, not as tools for their own sake (§7).

The order of the rounds is in §7. The first rounds (the sequencing design,
the proof-modularity design, and the native front end's design) can start
now in parallel.

---

## 1. What the tools taught

Rounds 1–9 of `docs/native/native-real-programs-plan.md` were worth doing. They
built byte state, argv, `open`/`close`, a GiB data segment, decimals,
memory-resident regions, checked register homes, and a certificate that
grows linearly, all proved once. But writing nine tools also showed the
limits of the shape they are written in.

**There are two program languages, and neither one is Heather.**

- `compile-x86` reflects a pure Heather function into FunctionIR. It only
  takes functions of at most six `BitVec(64)` parameters returning one,
  with loops written as fuel recursion
  (`crates/elab/src/function_ir_source/program.rs`). It has no records, no
  bytes, no other widths and no effects. Its certificate pattern is good: a
  generated `_agrees` theorem says the region evaluates to the source
  function at neutral arguments, and the kernel checks it.
- `write-elf` compiles a `Source`. Tools write that through the builder
  (`lib/native/native_build.hthr`). Every value there is an untyped word
  `Val`, a local is a HOAS binder (`local(num(0), λ n => …)`), a read is
  `.get()`, a character is its code (`num(45)` for `-`), and control is
  `branch`/`when`/`loop_while` combinators joined by `++`.
  `lib/native/native_tools.hthr` has 82 such binders, and its larger tools
  end in a run of a dozen or more closing parentheses.

**A tool's meaning is a `Source` tree, not a function.** The library's
lists, records, tactics and lemmas cannot be used to state or prove what a
tool does, because the tool is code that generates code. `cat_implements`
had to reason about the tree directly. A program written as a Heather
function (as the burned `wc.hthr` was, `docs/archive/native-programs-read-like-programs-design.md`)
could be proved with `split_all` and `bv_omega`, one line per fact.

**Composition hurts in the same way across areas.** `lib/std/tactic` has
518 `.bind(` / `and_then(` calls. Tactics are written in CPS with no
do-notation (`docs/metaprogramming/host-elaboration-interface-design.md`: "sugar is its own
surface round"), so `mono.hthr` reads `a.bind(λ x => b.bind(λ y => …))` six
levels deep. The builder's towers are the same problem. `?` (result
propagation) solved it for `Result` only, and deliberately deferred "a
generic propagation protocol" (`docs/language/result-propagation-design.md`).

**Every new tool is a new program, not a new capability.** Once byte state,
argv and decimals landed, the remaining tools add nothing general. The two
that do, `grep -F` and `sort`, need features that are general (procedures,
so a helper is not inlined at every site, and a heap). The next-areas
evaluation already found the same thing: "decide whether they need
procedures" before building them.

**The compiler is already Heather in Heather, but it runs in the kernel.**
`Source::compile`, the allocator check, the layout and the encoder are
Heather functions (`lib/native/native_compile*.hthr`,
`native_alloc.hthr`). `write-elf` evaluates them by kernel evaluation on an
untrusted fork (`evaluate_numbers`, `crates/cli/src/native/elf.rs`), and the
kernel then checks the result. That fork evaluation is the largest cost
block left in a tool's build (`perf/bench/targets.md` T3). A native compiler
compiled from its own Heather source would replace exactly that step.

---

## 2. The thesis

> A program is an ordinary Heather function, opted into running by
> `runtime fn` under a setup: a library generator that boxes the function,
> analyses its code, and hands the compiler a lowering and the proofs its
> analysis earned. The language makes that function pleasant to write in an
> imperative style, and the builder and `Source` become the compiler's back
> half.

This joins Minus's three directions:

| direction | what it becomes here |
|---|---|
| a better language | one sequencing surface (§3), used by tactics, parsers, `Result`/`Option`, trees, and native programs |
| generalizing features | the compiler grows by language feature (records, calls, capabilities, heap) and by setup (ownership, constant time), not by tool (§4) |
| Heather in Heather | the lexer, then the compiler itself, compiled from Heather (§5) |

It also keeps the decisions already made. The effects decision
(`issues/effects-direction.md`, 2026-10-21) is a uniqueness-threaded surface
that denotes interaction trees, which is §4's step N3. The source's shape
(control layer over total FunctionIR, loops split by totality,
`docs/native/native-effect-source-design.md` §12) is the back half, unchanged. The
principle "compiler proved once, no per-program proofs" holds. The one
generated per-program artefact, the agreement of a reflected function with
its region, is a checked certificate in the `compile-x86` pattern and not a
hand proof. "Users never write monadic types or prove against a CPS
elaboration target" also holds: the sequencing surface hides the CPS, and
proofs about a pure imperative function see its fold (§3.3).

---

## 3. The language: one sequencing surface (`lang-sequencing`)

### 3.1 What it is

Three forms, in two layers.

**Layer 1: binding over a carrier.** In a block, `let x <- e;` binds the
result of `e` for the statements after it, and a bare `e;` sequences an `e`
whose result is discarded. The carrier is any type constructor with a
`bind` (and a `pure` for a final value), found by the class instance the
block's expected type gives: `Tac`, `Result`, `Option`, `Parser`, `ITree`,
and the builder's `Act` for as long as the builder exists. It lowers to the
`bind` chain that is written by hand today, so it adds no trusted rule.
`?` stays as it is for `Result`, and gets `Option` as well.

The spelling is the design round's decision (R1). `<-` is the candidate
because `=` is equality and `:=` is held for assignment
(`docs/language/let-and-blocks-design.md` §3.1). Interleaved statements in a block
(`let a = …; f(x); g(a)`), which were deferred to the effects work
(`docs/language/let-and-blocks-design.md` §4.5), mean something here: `f(x);` is a
sequenced computation.

**Layer 2: local state and loops.** Inside a function body (spellings
illustrative):

```heather
fn count_words(bytes: List<BitVec(8)>) → Nat {
    let mut words = 0;
    let mut inside = False;
    for b in bytes {
        if b.is_space() { inside := False }
        else if !inside { inside := True; words := words + 1 }
    }
    words
}
```

`let mut x = e` declares a local that `x := e` reassigns. `for x in xs`
iterates a `List` or a range `a..b`. `while c decreases m { … }` loops
under a measure, and `while c fuel n { … }` loops under fuel with an
`Exhausted` result where no measure is available. `break`, `continue` and
`return` exit early. As in Lean 4's `do`, the body lowers to pure code. The
mutable locals become a state tuple threaded through a fold or a structural
recursion, and early exits become a sum in that state. In a block over a
carrier (layer 1), the same forms thread the state through `bind`.

### 3.2 Why it is a generalizing feature

It is one elaborator feature, and it has at least five customers already in
the library:

- **Tactics**: the 518 `bind`s in `lib/std/tactic`, and every tactic still
  to be written in Heather (`tac-general`).
- **Parsers and `Result`/`Option` chains**: `prelude-option-and-friends`
  layer 2 (the `gather` shape) and the parser library.
- **Native programs**: the builder's towers now, and the surface that
  replaces it (R6).
- **Pure algorithms written the way they are usually described**: decimal
  formatting, the `wc` step, list algorithms in `lib/lang`, numeric code in
  `lib/std/num` (interval evaluation, `Nat::isqrt`), and later ML's loops.
- **Compiler passes and Heather-in-Heather code** (§5), which are
  mostly loops over arrays and lists with local state.

### 3.3 What proofs see

This is the round's real design question, and the reason it starts with a
design round. Proofs must not have to unfold a desugaring by hand. The
plan:

- A `for` over a list lowers to `List::foldl` (or a structural recursion
  the library already has lemmas for), so a property is proved by the fold's
  induction lemma, or by the existing `induction`/`split_all` path.
- Each lowered loop gets **unfolding equations** generated beside it, as
  `decreases` functions already get them (`unfolding-computed-scrutinee`),
  so `rewrite` steps see the loop's one-step behaviour.
- A `for` body that only updates locals is a step function on the state
  tuple, and is exposed as one (`count_words::step`). That is exactly the
  shape `docs/archive/native-programs-read-like-programs-design.md` §1.1 proved
  with one line per fact.

Negative controls: a `:=` to a non-`mut` local, a `break` outside a loop, a
`while` with no measure and no fuel, a `let x <- e` where the block has no
carrier. Each is a refusal that names its reason
(`docs/test-value-audit.md` §5).

---

## 4. The compiler: `runtime fn` setups (`hih-native-heather`)

### 4.1 What a `runtime fn` is

Heather is not Lean: not every function is compiled. An ordinary `fn` is
kerneltime mathematics, and it never runs on hardware
(`issues/datarepr-separation.md`, "Execution model"). A function crosses to
the machine only when it opts in, and the opt-in is not a compiler keyword.
It is a **declaration generator** written in Heather
(`issues/runtime-compile-opt-in.md`, `issues/scoped-declaration-generators.md`).
The generator boxes the function, so it can analyse the function's code
*intensionally*. It then produces whatever that setup's compiler needs, as
checked declarations (Minus, 2026-10-31).

So "ordinary Heather compiles" means this: an ordinary Heather function,
marked `runtime fn` under some **setup**, compiles with no per-program proof.
A setup is a library value with four parts:

1. **A fragment and a reflection.** The fragment is the code the setup
   accepts. The generator reads the function's boxed body through the pull
   API (`Elaborator::fn_body_code` today, `docs/metaprogramming/fn-signature-reflection-design.md`;
   the host interface's `View` for tactics) into an ElabCode-style AST,
   which is ordinary data (`issues/elabcode-abstraction-layer.md`).
2. **A judgment.** This is a decidable check over that AST, written as an
   ordinary `Bool` function. The default setup's judgment is "is in the
   fragment". A stricter setup checks more.
3. **One soundness theorem, proved once per setup.** It says what a
   function that passes the judgment guarantees at run time. For the
   default setup that is agreement: the `Source` it lowers to denotes the
   function. A stricter setup's theorem also hands the compiler facts it
   may use, such as "this buffer is not aliased" or "no branch depends on
   a secret".
4. **A lowering** from the AST to `Source` and FunctionIR, the back half
   that exists today. Its output is kernel-checked as `write-elf`'s is.

The compiler consumes a setup's evidence as it consumes any certificate.
That is the claim of `issues/ownership-discipline-over-code.md`: a
discipline is a decidable syntactic judgment over reflected code plus one
soundness theorem, and the kernel never learns the word. Instance keying
stays on syntax (`issues/compile-typeclass-design.md`): a setup's verdict is
about this code, and refactoring the function re-runs the generator.

R4's design of all four parts, and of how the compiler consumes the
evidence, is `docs/native/runtime-fn-setups-design.md`.

### 4.2 The default setup, and its four steps

The **default setup** is "abstract programming that can talk to the
system". It covers words of any width, `Bool`, records and enums, `match`,
§3's loops, calls, and I/O through capabilities. Representations come from
`datarepr`. Its judgment is membership in the fragment, and its theorem is
agreement. It grows in four steps (the submilestones):

**N1 `nh-front`: the generator and the pure fragment.** The `runtime fn`
generator, written in Heather on the host interface, and the default
setup's pure fragment:

- `BitVec(w)` at any width the ISA model has, `Bool`, and `Nat` narrowed
  to a word, with overflow as a refusal (the `datarepr` narrowing,
  `docs/native/datarepr-design.md` §2.4);
- flat records and enums laid out in words, so a `WcState` record or an
  `enum Flag { L, W, C }` is a value and not a set of word ids;
- `match`, `if`, and §3's loops, lowering to FunctionIR's bounded loop
  where a measure exists (L3) and to the layer's `Repeat` otherwise;
- fixed-size byte arrays as buffers, with `a[i]` and `a[i] := v` as the
  state edges that round 1 built;
- calls inlined, as today.

Its agreement certificate states that the lowered region evaluates to the
function at neutral arguments, in `compile-x86`'s `_agrees` form. Today
`compile-x86`'s reflector is Rust (`crates/elab/src/function_ir_source/`).
N1 moves that logic into Heather as the setup's lowering, which the
roadmap's "logic in Heather, not Rust" principle asks for anyway. N1 also
absorbs `native-build-loop-regions` and `native-build-reflected-helpers`.

**N2 `nh-procedures`: calls that are not inlined.** A call to a compiled
procedure, with its frame on the process stack (`io-image-process-stack`),
its contract derived from its body rather than proved per procedure
(`native-procedure-contracts`), and a register convention
(`native-register-moves-and-convention`). Recursion that is not a tail loop
compiles. Code grows once per helper, not once per call site, which is the
wall the next-areas evaluation predicted for `grep -F`.

**N3 `nh-effects`: talking to the system.** This is
`effects-uniqueness-surface`. A `runtime fn` takes `uniq` capabilities and
is written with §3's surface. The spellings below are illustrative; R1 and
R6 fix them.

```heather
runtime fn wc(io: uniq Io, args: Args) → Exit {
    let mut lines = 0;
    let mut buf: [BitVec(8); 4096] = zeros();
    loop {
        let n <- io.read(stdin, buf);
        if n == 0 { break }
        for b in buf[..n] { if b == '\n' { lines := lines + 1 } }
    }
    io.print_decimal(stdout, lines);
    Exit(0)
}
```

It lowers into `Source`: a run of pure statements becomes a leaf (through
N1), `io.read` becomes an `Invoke`, and `loop` becomes a `Repeat`. The pure
reading, world threading, agrees with `denote` construct by construct,
proved once (the statement of `ITree::run_state_bind`). Character and string
literals are bytes here (`'\n'`, `"cat: "`). A program file stops importing
the compiler's modules by hand (`feature-implicit-module-dependencies`).

**N4 `nh-heap`: recursive data at run time.** This is `hih-first-alloc`,
re-scoped. It starts with a bump arena in the data segment, then moves to
`mmap` as a Linux event. Exhausting the arena is a defined exit, which fits
partial correctness. `datarepr` instances give `List` and small trees arena
cells. `datarepr` v1 is implemented (`crates/elab/src/datarepr.rs`). A
metered bound on the arena is `hih-alloc-metering`'s follow-up, not a
prerequisite.

### 4.3 An alternative setup: `nh-ownership`

The milestone is not done when one setup works. It is done when a
**second** setup exists beside the default one and gives the compiler
something the default cannot, because that is what makes setups a feature
and not a second name for the compiler. The candidate Minus named is
Rust-style ownership (`issues/ownership-discipline-over-code.md`):

- the judgment is a borrow check over the reflected AST (moves, shared and
  unique borrows, scopes);
- the soundness theorem is proved once, against the byte memory model
  (`lib/std/machine/memory.hthr`, PR #120): code that passes neither aliases a unique
  buffer nor reads one after it is freed;
- what the compiler gets is in-place update of buffers and arena cells
  where the default setup must copy or keep everything, frees with no
  per-program proof, and values kept in registers across calls that cannot
  touch them.

The cheaper second setup is **constant time** (`docs/surveys/constant-time-survey.md`).
Its judgment is "no branch or address depends on a secret", its theorem is
the survey's leakage contract, and it needs no heap. If a setup is wanted
before N4 lands, it can go first.

### 4.4 What stays as it is

The back half: `Source` statements, FunctionIR regions, checked homes,
`native_compile_correct`, and `write-elf`'s ELF theorem. The builder stays
as a library a setup's lowering may emit into, and it stops being how
people write programs.

---

## 5. Heather in Heather (`hih-self`, re-scoped)

Today `hih-self` is one open issue (`self-hosting-first-component`) that
waits on everything. The proposal gives it two concrete submilestones, each
with a test that cannot be argued with.

**S1 `self-lexer`: Heather's lexer, in Heather, compiled natively.** A pure
function from bytes to tokens, written with §3's surface. Its spec is the
token grammar. It is a `runtime fn` under the default setup, compiled by N1 and N3 into a `heather-lex` executable
that streams tokens to stdout, so it needs no heap. Done when its output
matches `crates/syntax/src/lexer.rs` on every file under `lib/`. This is a
customer for the whole front end on a real workload, and the first piece of
Heather that runs natively.

**S2 `self-compiler`: the native compiler, compiled natively.** Compile
`Source::compile`, the allocator check and the encoder (all Heather today)
with N1–N4, and have `write-elf` run that binary where it now evaluates the
compile on its fork. The kernel still checks the emission, so a bug in the
compiled compiler is a refusal, not a wrong certificate. Done when
`write-elf` builds the corpus through it and `scripts/perf ab` shows the
fork's read-back counters gone. This is the bootstrap step the roadmap's
first area names ("move the compiler's logic out of Rust into Heather"),
with a measurable payoff.

**Alongside: `hih-passes`' first pass.** A FunctionIR rewrite (constant
folding and dead-node removal over a region) written in Heather, proved
once to preserve `eval`, and run inside `Source::compile`. It needs none of
the above, sits in the native lane, and makes every compiled program
smaller. It is the first optimisation pass that is a Heather function with
its proof, which is what `hih-passes` asks for.

## 6. Proofs: compose against interfaces (`lang-proof-modularity`)

Minus's second ask (2026-10-31): proving a specific property should not
mean thinking about lots of code, and automation should be modular too,
for reasoning and for cost. Today both fail for the same reason: **every
`fn` is transparent everywhere**, so the elaborator, the kernel and every
tactic see a definition's whole body, and nothing marks the facts a client
is meant to use instead.

### 6.1 What it costs today

`docs/proof-patterns.md` is, read one way, a list of the places where
proofs are not modular, each with the workaround the rounds found:

- "Split a long proof into stage theorems with written statements": one
  composed theorem took 80 s, the same stages took 0.2 s each. The
  elaborator loses the sharing a composed proof has
  (`frontend-large-proof-composition-cost`: 68.9 s of frontend against
  7.5 s of kernel on one certificate).
- "Never compare two separately computed values by `refl`" and "prove at a
  neutral parameter, instantiate at the literal": conversion unfolds
  definitions in lockstep because nothing says it should not.
- A proof whose state λ holds many lets makes every later let dearer, and
  nothing says which let (`let-fanout-diagnostic`).
- The `wc` proof of 2026-10 needed `split_all; all_goals { bv_omega }` per
  field and a hand copy of the step (`docs/archive/native-programs-read-like-programs-design.md`
  §1); `cat_implements` reasons about the `Source` tree statement by
  statement.

Automation is monolithic in the same way. `mono` reads a hard-coded carrier
table (`mono_carriers` in `lib/std/tactic/mono.hthr`), so a new ordered
type gets `mono` by editing the tactic. `ring`, `linarith` and `norm_num`
each have their own way of being told about a carrier. A tactic that
proves a goal about `f` does it by unfolding `f`, so its cost grows with
`f`'s code rather than with the fact asked for.

### 6.2 What it proposes

- **Definitions with an interface.** A `fn` can be declared so that
  clients use it through generated equations (its unfolding equations, as
  `decreases` functions already get, `docs/language/recursion/decreases-unfolding-design.md`)
  and the lemmas proved about it, while conversion outside its module does
  not unfold it unless a proof says `unfold f`. Evaluation still runs it
  (closed verdicts by `refl` keep working), so this is about what a proof
  sees, not about what computes. Theorems are already opaque
  (`docs/language/have-design.md`); this extends the boundary to definitions.
- **Lemma registries that automation reads.** One declaration-side
  mechanism (an attribute or a registry entry beside the lemma) says "this
  is a monotonicity law", "this is a step equation", "this is a ring
  morphism". `mono`, `norm_num`, `ring`'s atoms, `rewrite` sets and the
  later `tac-general` tactics read it through the host interface. A new
  type gets automation by registering its lemmas, and a tactic proving a
  fact about `f` uses `f`'s registered lemmas instead of its body.
- **Rules for loops and procedures.** Every loop of §3 comes with an
  invariant rule: `inv(init)` and `inv(s) → inv(step(s, x))` give
  `inv(result)`. A procedure of N2 comes with its contract, proved once and
  cited at every call. Then the spec of `count_words` is an invariant and a
  step lemma, and a property of a native tool is proved about its Heather
  function, not about its `Source`.
- **Sharing kept, staging automatic.** The elaborator keeps the sharing of
  a large composed proof (`frontend-large-proof-composition-cost`), reports
  the `let` that multiplies a slow proof (`let-fanout-diagnostic`), and
  where it must stage, it stages by itself. The proof-patterns rule "split
  into stage theorems" then retires.
- **Modular automation is also cheaper automation.** A tactic that proves
  a generic lemma once at neutral parameters and instantiates it (the rule
  of `docs/proof-patterns.md` §1) should do that by itself, and memoise
  results per goal within a declaration.

Each round's "done when" names the `docs/proof-patterns.md` rules it
retires, so the guide shrinks as the milestone lands.

### 6.3 Interface definitions, in detail

Minus asked for this one to be spelled out (2026-10-31). Today a `fn` has
one visibility for proofs: its whole body, everywhere. Theorems already
have the other one (opaque, `docs/language/have-design.md`). An **interface
definition** sits between the two.

```heather
interface fn List::sorted_insert(self xs: List<Nat>, x: Nat) → List<Nat> {
    match xs { … }
}
// generated beside it, as decreases functions already get them:
//   List::sorted_insert::nil:  Nil.sorted_insert(x) = [x]
//   List::sorted_insert::cons: Cons(y, ys).sorted_insert(x) = if x <= y { … } else { … }

theorem List::sorted_insert_sorted(…): … { … }   // proved inside, by the equations or by unfolding
```

What changes, and what does not:

- **Proofs outside the defining module do not unfold it.** The elaborator's
  conversion and every tactic treat `sorted_insert(…)` at an open argument
  as an atom. A proof reaches the body through the equations, the lemmas
  proved about it, or an explicit `unfold sorted_insert` that says "I am
  thinking about the code here". Inside its own module the body is visible
  as it is today, so the lemmas that make the interface can be proved.
- **Closed values still compute.** `[3, 1].sorted_insert(2) = [1, 2, 3]` by
  `refl` still works, because evaluation at closed arguments is how the
  library states verdicts (`docs/proof-patterns.md` §1). The boundary is on
  *reasoning* about open terms, not on running.
- **The kernel is unchanged.** It is an elaborator and tactic policy. A
  proof term that crosses the boundary cites an equation lemma, so the
  kernel checks it without unfolding. No proof is accepted that would be
  refused today.
- **Boxing is unaffected.** A `runtime fn` setup reads the boxed body
  through the pull API (§4.1). That is intensional analysis of code, a
  different act from conversion in a proof, so an interface definition can
  still be compiled and still be checked by a discipline.

What it buys:

- **Specific properties without lots of code.** Goals stay in the vocabulary
  of the interface. A tactic that meets `sorted_insert` uses its registered
  lemmas (§6.2) instead of expanding a `match` that spells the whole
  implementation into the goal.
- **Cost.** The lockstep unfoldings that `docs/proof-patterns.md` §1 warns
  against stop at the boundary, and so do the large goal spellings that
  make later steps dearer.
- **Robustness and rebuilds.** Changing an implementation does not break
  client proofs that never looked inside it. That is also the shape early
  cutoff wants (`docs/infrastructure/module-interface-cutoff-design.md`): a client that did
  not unfold a definition did not observe its body. Whether module images
  can then skip re-elaborating on a body edit is a question for P2 to
  measure, not a promise.

**Opt-in or default.** The library today leans on conversion through
definitions everywhere: `refl` on computed sides, `trivial`, matches that
reduce through helpers. So:

- *Opt-in per definition* (`interface fn`) breaks nothing. Modules migrate
  one at a time, starting where proofs are slowest or most fragile. The
  cost is that the boundary is only where someone thought to put it.
- *Default for exported definitions, opt-out with `transparent fn`* gives
  modular reasoning everywhere, and is the direction Lean's module system
  has taken for build cost. But it would break a large part of the library
  in one step, and the migration would be the round.

The recommendation is opt-in now, with P2 measuring one migrated module. If
it pays, the default can flip later, module by module. The precedent is the
`--review` lints, which arrived as warnings before they were required.


---

## 7. The rounds, in order

Each round is one thread. "Beside" names rounds whose footprints are
disjoint enough to run at the same time (`docs/roadmap.md`, Parallel
lanes).

| # | milestone | round | scope | done when | needs | beside |
|---|---|---|---|---|---|---|
| R1 | `lang-sequencing` | **sequencing design** | design note: the carrier protocol (class, instance lookup from the expected type), the binding spelling, interleaved statements, `let mut`/`:=`/`for`/`while`/`break`/`return` lowering, what proofs see (§3.3), and the effects case (N3) so one surface serves both | the note is decided by Minus, and R2/R3 are filed | — | R4 |
| R2 | `lang-sequencing` | **binding statements** | `let x <- e;` and `e;` in blocks over any carrier, `Option` `?`; port `mono.hthr` and one parser chain | `mono.hthr` has no `bind` tower, and `lib/std/tactic`'s `.bind(` count falls by most of `mono`'s share; refusals named | R1 | R4, R10 |
| R3 | `lang-sequencing` | **pure imperative** | `let mut`, `:=`, `for` over lists and ranges, `while … decreases`/`fuel`, early exit; lowering to folds with unfolding equations and exposed step functions | the decimal formatter and `wc`'s step are written imperatively, and their theorems are proved by the existing tactics with no hand unfolding; negative controls refuse by reason | R2 | R5 |
| R4 | `hih-native-heather` | **setups design** | design note: the setup record (§4.1: fragment, judgment, soundness theorem, lowering) and how the compiler consumes its evidence; the `runtime fn` generator on `scoped-declaration-generators` and the host interface; reflecting a body beyond `fn_body_code`'s Nat fragment; the default setup's fragment, record and enum layouts, `Nat` narrowing; how the `_agrees` certificate scales; what is left of `compile-typeclass-design` | decided by Minus; N1's issues filed, `native-build-loop-regions` and `native-build-reflected-helpers` folded in | — | R1, P1 |
| R5 | `hih-native-heather` | **N1: the generator and the pure fragment** | the `runtime fn` generator in Heather, the default setup's pure fragment and lowering, `compile-x86`'s Rust reflector retired onto it | a `wc` step over a `WcState` record and the decimal formatter, marked `runtime fn`, compile into a tool and pass its GNU test; `compile-x86`'s examples still pass through the Heather generator | R4 (R3 for the imperative spellings) | R2, R3 |
| R6 | `hih-native-heather` | **N3: I/O as capabilities** | `effects-uniqueness-surface` over §3's surface; byte and string literals; implicit compiler imports | `cat FILE…`, `wc` and `head -n` are rewritten in it and pass the same GNU tests; the builder versions are deleted | R3, R5 | R7 |
| R7 | `hih-self` | **S1: the lexer** | Heather's lexer in Heather, streaming tokens, compiled natively | `heather-lex` matches the Rust lexer on every file under `lib/` | R6 | R8, R10 |
| R8 | `hih-native-heather` | **N2: procedures** | compiled calls with frames on the process stack, derived contracts, a register convention; `io-image-process-stack` finished | one helper called from several sites is compiled once; a non-tail recursive function compiles; `grep -F` is built with a shared line-buffer helper | R5 | R7 |
| R9 | `hih-native-heather` | **N4: the heap** | a short design section first, then the bump arena, `datarepr` cells for `List` and trees, arena exhaustion as a defined exit | `sort` (lines into a list) and `tac` are written as ordinary Heather and pass GNU tests | R8 | R10 |
| R12 | `hih-native-heather` | **a second setup: ownership** | `nh-ownership` (§4.3): the borrow-check judgment over reflected code, its soundness theorem against the byte memory model, and what the compiler does with it (in-place updates, frees) | a program that updates an arena structure in place compiles under the ownership setup with no per-program proof, the same program under the default setup copies, and a program that aliases a unique buffer is refused by the judgment with its reason | R9 (constant time first, if a setup is wanted earlier: R5 is enough) | R11 |
| R10 | `hih-passes` | **first pass in Heather** | constant folding and dead-node removal over FunctionIR regions, proved once to preserve `eval`, run inside `Source::compile` | the regression tools build with smaller code and unchanged GNU results; the proof is one theorem, not per program | — | any |
| P1 | `lang-proof-modularity` | **proof-modularity design** | design note: interface definitions (what conversion may unfold, where, and the `unfold` escape), the registry mechanism and which tactics read it first, invariant and contract rules, and which `proof-patterns` rules each piece retires | decided by Minus; P2–P5 filed | — | R1, R4 |
| P2 | `lang-proof-modularity` | **interface definitions** | generated equations, no unfolding outside the module unless asked, tactics and `rewrite` use the equations | one library module (the interval or layout lemmas) re-proved through equations with fewer conversion steps in `--timings`; one proof-patterns rule retired | P1 | R2, R5 |
| P3 | `lang-proof-modularity` | **lemma registries** | one registration mechanism; `mono` and `norm_num` read it in place of their tables | a new carrier gets `mono` and `norm_num` by registering lemmas, with no edit to the tactics; `mono_carriers` is gone | P1 (the host interface it reads exists) | R5, R8 |
| P4 | `lang-proof-modularity` | **loop and procedure rules** | invariant rules generated beside §3's loops; contracts of N2's procedures cited at calls | `count_words`'s spec is an invariant and a step lemma in a few lines; a property of a rewritten tool (R6) is proved about its Heather function | R3 (R8 for procedures) | R7 |
| P5 | `lang-proof-modularity` | **sharing and staging** | `frontend-large-proof-composition-cost`'s acceptance, `let-fanout-diagnostic`, staging done by the elaborator where it must stage | the nested 100-node certificate checks near the staged spelling's cost; "split into stage theorems" retires from proof-patterns | P1 | any |
| R11 | `hih-self` | **S2: the compiler compiles itself** | `Source::compile` and its checks compiled by N1–N4; `write-elf` runs the binary in place of the fork's evaluation | `write-elf` builds the corpus through it; `scripts/perf ab` shows the fork's read-back counters gone, with the kernel check unchanged | R9 | — |

Each round's issue: R1 `sequencing-surface-design`, R2
`binding-statements`, R3 `pure-imperative-statements`, R4
`runtime-fn-setups-design`, R5 `runtime-fn-default-setup`, R6
`effects-uniqueness-surface`, R7 `self-hosted-lexer`, R8
`native-compiled-procedures`, R9 `native-heap-arena`, R10
`function-ir-pass-in-heather`, R11 `self-hosted-compiler`, R12
`ownership-discipline-over-code`, P1 `proof-modularity-design`, P2
`interface-definitions`, P3 `automation-lemma-registries`, P4
`loop-invariant-rules`, P5 `frontend-large-proof-composition-cost` with
`let-fanout-diagnostic`.

R1, P1 and R4 can start today, as can R10 in the native lane. After the
designs, three lanes run side by side: the language lane (R2, R3), the
proof lane (P2, P3, P5, which touch the elaborator core and the tactics, so
P2 and R2 should not run at the same moment), and the native lane (R5, R8,
R9). They meet at R6 and P4.

**Kept running beside them, pulled by these rounds.** The certificate cost
that grows with the program (next-areas item 1,
`native-tool-test-cold-certificate-rail`) stays an enabling round. R6 pulls
it, because the rewritten tools must check under the suite's rail. N2 also
cuts code size, which lowers that cost. Lemma search, the monoid
normaliser, ML and export are in other lanes and are not affected by this
proposal.

### 7.1 What happens to the open native issues

| issue | under this proposal |
|---|---|
| `native-tools-suite` | closed as re-scoped: nine tools stand as the corpus; `grep -F`, `sort`, `tac` move to R8/R9's "done when"; `basename`, `dirname`, `rev`, `cmp` are left for anyone who wants them |
| `native-build-loop-regions`, `native-build-reflected-helpers` | folded into R4/R5 |
| `effects-uniqueness-surface` | R6 |
| `self-hosting-first-component` | split into R7 and R11 |
| `datarepr-separation`, `memory-bound-certificates` | R9 (metering after it) |
| `native-procedure-contracts`, `io-image-process-stack`, `native-register-moves-and-convention` | R8 |
| `prelude-option-and-friends` (layer 2), `pipeline-operator`, `function-composition-operator` | R1 decides whether they are still needed after binding statements |
| `tactic-composition-ergonomics` | stays separate: it is about proof scripts (`split_all; all_goals {…}`), not about binding results; P1 says whether registries change it |
| `frontend-large-proof-composition-cost`, `let-fanout-diagnostic` | P5 |
| `mono-class-laws`, `monotonicity-tactic` | P3 decides what remains |
| `runtime-compile-opt-in`, `scoped-declaration-generators`, `compile-typeclass-design` | R4 and R5: the marker is the setup's generator; R4 says what is left of the class layer |
| `elabcode-abstraction-layer`, `code-variable-analysis-api` | R4 and R5: the reflected AST the setups read |
| `ownership-discipline-over-code` | R12 |
| `native-decimal-io-proved`, `native-compile-stat` | unchanged, not scheduled |

---

## 8. Decisions

1. **Adopt the thesis** (§2): native programs become ordinary Heather
   functions, and the builder becomes the compiler's back half. *Adopted
   (Minus, 2026-10-31), with proof composition added as §6.*
2. **`hih-tools`**: close it at the nine built tools as a regression
   corpus. *Decided (Minus, 2026-10-31): yes.*
3. **Binding over a carrier** (§3.1): any carrier with a `bind`, or only
   named ones. *Decided (Minus, 2026-10-31): any.*
4. **The lexer before the heap** (R7 before R9). *Decided, tentatively
   (Minus, 2026-10-31: "I guess").* Swapping is cheap: the token-list lexer
   follows from the streaming one once N4 lands.
5. **Interface definitions** (§6.3): opt-in per definition, or the
   default for exported definitions. *Decided (Minus, 2026-10-31): opt-in.*
6. **Roadmap shape**: add `lang-sequencing` and `lang-proof-modularity`
   (area `language`, pulled by `heather-in-heather` and `tactics`) and `hih-native-heather` with
   `nh-front`, `nh-procedures`, `nh-effects`, `nh-heap` as submilestones;
   re-scope `hih-first-alloc` into `nh-heap`; add `nh-ownership`; give `hih-self` the
   submilestones `self-lexer` and `self-compiler`. *Done on this PR: the
   rows, the log line and one issue per round are in `docs/roadmap.md` and
   `issues/`.*
7. **Setups** (§4, added after Minus's note of 2026-10-31 on `runtime fn`):
   is ownership the right second setup? *Leaning yes, final choice later
   (Minus, 2026-10-31): Rust-like talk about ownership would make
   translating Rust code easier (`rust-in-heather`), and the lower-level
   control is powerful. So `nh-ownership` is filed as the second setup, and
   its round confirms the choice before it starts.*

## 9. Risks, and what would change the order

- **Elaborator cost of lowered loops.** A `for` lowered to a fold inside a
  large function may hit the elaborator whnf cost that computed-from-code
  types have hit before. R3 tests with a large body and
  states its cost as a shape. If it is superlinear, R3 adds named step
  functions by default.
- **Agreement certificates scale with the program.** `_agrees` is per
  function and per loop. If R5 finds it growing faster than the code, the
  fallback is the one `in-language-certificate-emission` named as route 2:
  the reflector's agreement proved once by induction over the reflected
  fragment. That is a larger round, and R4 should price it.
- **The heap's design is the least settled part.** R9 opens with a design
  section. If arena allocation turns out to need the separation-logic
  footprints (`wp-view-separating-product`) before anything runs, R7 and R10
  still deliver, and R11 waits.
- **Interface definitions can break proofs that rely on conversion.** Many
  library proofs close by `refl` or `trivial` through a definition. Opt-in
  per definition keeps them working; P2 migrates one module and measures
  before anything becomes a default.
