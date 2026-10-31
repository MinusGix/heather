# Compiler milestones, reconsidered: ordinary Heather compiles

Status: **proposal, 2026-10-31, for Minus's decision.** Nothing here is built,
and `docs/roadmap.md` is unchanged until the decisions in §7 are made. Written
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
- The native compiler takes **ordinary first-order Heather**: words of any
  width, `Bool`, records and enums, `match`, structural and measure
  recursion, calls that are not inlined, then `uniq` capabilities for I/O,
  then heap data through `datarepr`. Each of these is a general feature, and
  each one makes many programs possible at once (§4, milestone
  `hih-native-heather`).
- Heather in Heather gets **two concrete first components** on that
  compiler: Heather's own lexer, compiled natively and tested against the
  Rust lexer on the whole library; then the native compiler itself
  (`Source::compile`, already a Heather function), compiled natively and run
  where `write-elf` now evaluates it in the kernel. The kernel still checks
  its output, so this changes no trust, and it speeds up the step that the
  current cost profile says is the slowest (§5, milestone `hih-self`
  re-scoped).

**`hih-tools` stops being a target and becomes a regression corpus.** It
would close at the nine tools that are built. Every later round's "done
when" rewrites some of them in the new surface, and they must still pass
their GNU tests. `grep -F` and `sort` come back as the first customers of
procedures and of the heap, not as tools for their own sake (§6).

The order of the rounds is in §6. The first two rounds (the sequencing
design, and the native front end's design) can start now in parallel.

---

## 1. What the tools taught

Rounds 1–9 of `docs/native-real-programs-plan.md` were worth doing. They
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
function (as the burned `wc.hthr` was, `docs/native-programs-read-like-programs-design.md`)
could be proved with `split_all` and `bv_omega`, one line per fact.

**Composition hurts in the same way across areas.** `lib/std/tactic` has
518 `.bind(` / `and_then(` calls. Tactics are written in CPS with no
do-notation (`docs/host-elaboration-interface-design.md`: "sugar is its own
surface round"), so `mono.hthr` reads `a.bind(λ x => b.bind(λ y => …))` six
levels deep. The builder's towers are the same problem. `?` (result
propagation) solved it for `Result` only, and deliberately deferred "a
generic propagation protocol" (`docs/result-propagation-design.md`).

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

> A program is an ordinary Heather function. The language makes that
> function pleasant to write in an imperative style. The native compiler
> takes it, and the builder and `Source` become the compiler's back half.

This joins Minus's three directions:

| direction | what it becomes here |
|---|---|
| a better language | one sequencing surface (§3), used by tactics, parsers, `Result`/`Option`, trees, and native programs |
| generalizing features | the compiler grows by language feature (records, calls, capabilities, heap), not by tool (§4) |
| Heather in Heather | the lexer, then the compiler itself, compiled from Heather (§5) |

It also keeps the decisions already made. The effects decision
(`issues/effects-direction.md`, 2026-10-21) is a uniqueness-threaded surface
that denotes interaction trees, which is §4's round N4. The source's shape
(control layer over total FunctionIR, loops split by totality,
`docs/native-effect-source-design.md` §12) is the back half, unchanged. The
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
(`docs/let-and-blocks-design.md` §3.1). Interleaved statements in a block
(`let a = …; f(x); g(a)`), which were deferred to the effects work
(`docs/let-and-blocks-design.md` §4.5), mean something here: `f(x);` is a
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
  shape `docs/native-programs-read-like-programs-design.md` §1.1 proved
  with one line per fact.

Negative controls: a `:=` to a non-`mut` local, a `break` outside a loop, a
`while` with no measure and no fuel, a `let x <- e` where the block has no
carrier. Each is a refusal that names its reason
(`docs/test-value-audit.md` §5).

---

## 4. The compiler: ordinary Heather compiles (`hih-native-heather`)

The compiler's back half stays as it is: `Source` statements, FunctionIR
regions, checked homes, `native_compile_correct`, `write-elf`'s ELF theorem.
The new work is a front end that takes ordinary Heather and produces a
`Source` with a certificate that it agrees with the Heather function, then
the language features that front end needs. Four submilestones, in order.

**N1 `nh-front`: first-order pure functions.** One reflector, from an
elaborated Heather function to FunctionIR regions and `Source` leaves. It
generalizes `compile-x86`'s word reflector and replaces the builder for pure
code. It takes:

- `BitVec(w)` at any width the ISA model has, `Bool`, `Nat` narrowed to a
  word with overflow as a refusal (the `datarepr` narrowing,
  `docs/datarepr-design.md` §2.4);
- flat records and enums (no recursive fields) laid out in words, so a
  `WcState` record or an `enum Flag { L, W, C }` is a value, not a set of
  word ids;
- `match`, `if`, and the layer-2 loops of §3, which lower to FunctionIR's
  bounded loop where a measure exists (L3) and to the layer's `Repeat`
  otherwise;
- fixed-size byte arrays as buffers, with `a[i]` and `a[i] := v` as the
  state edges round 1 built;
- calls inlined as today.

Its certificate states that the region evaluates to the function, at
neutral arguments, in the `compile-x86` `_agrees` form. This absorbs
`native-build-loop-regions` and `native-build-reflected-helpers`, and
`compile-x86` becomes a client of the same reflector.

**N2 `nh-procedures`: calls that are not inlined.** A `Stmt` (or region)
call to a compiled procedure, with its frame on the process stack
(`io-image-process-stack`), its contract derived from its body, not proved
per procedure (`native-procedure-contracts`), and a register convention
(`native-register-moves-and-convention`). Recursion that is not a tail
loop compiles. Code size grows once per helper rather than once per call
site, which is the wall the next-areas evaluation predicted for `grep -F`.

**N3 `nh-effects`: I/O as uniqueness-threaded capabilities.** This is
`effects-uniqueness-surface`: a program is a function over `uniq`
capabilities, written with §3's surface.

The spellings below are illustrative; R1 and R6 fix them.

```heather
fn wc(io: uniq Io, args: Args) → Exit {
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

It elaborates into `Source`: a run of pure statements becomes a leaf
(through N1), `io.read` an `Invoke`, `loop` a `Repeat`. Its world-threading
reading agrees with `denote` construct by construct, proved once (the
statement of `ITree::run_state_bind`). Character and string literals are
bytes here (`'\n'`, `"cat: "`), and a program file stops importing the
compiler's modules by hand (`feature-implicit-module-dependencies`).

**N4 `nh-heap`: recursive data at run time.** This is `hih-first-alloc`,
re-scoped. A bump arena (in the data segment first, then `mmap` as a Linux
event), with exhaustion as a defined exit, which fits partial correctness.
`datarepr` instances (already implemented for v1, `crates/elab/src/datarepr.rs`)
give `List` and small trees arena cells, and the reflector compiles
functions over them. A metered bound on the arena is `hih-alloc-metering`'s
follow-up, not a prerequisite.

---

## 5. Heather in Heather (`hih-self`, re-scoped)

Today `hih-self` is one open issue (`self-hosting-first-component`) that
waits on everything. The proposal gives it two concrete submilestones, each
with a test that cannot be argued with.

**S1 `self-lexer`: Heather's lexer, in Heather, compiled natively.** A pure
function from bytes to tokens, written with §3's surface. Its spec is the
token grammar. It is compiled by N1 and N3 into a `heather-lex` executable
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

---

## 6. The rounds, in order

Each round is one thread. "Beside" names rounds whose footprints are
disjoint enough to run at the same time (`docs/roadmap.md`, Parallel
lanes).

| # | milestone | round | scope | done when | needs | beside |
|---|---|---|---|---|---|---|
| R1 | `lang-sequencing` | **sequencing design** | design note: the carrier protocol (class, instance lookup from the expected type), the binding spelling, interleaved statements, `let mut`/`:=`/`for`/`while`/`break`/`return` lowering, what proofs see (§3.3), and the effects case (N3) so one surface serves both | the note is decided by Minus, and R2/R3 are filed | — | R4 |
| R2 | `lang-sequencing` | **binding statements** | `let x <- e;` and `e;` in blocks over any carrier, `Option` `?`; port `mono.hthr` and one parser chain | `mono.hthr` has no `bind` tower, and `lib/std/tactic`'s `.bind(` count falls by most of `mono`'s share; refusals named | R1 | R4, R10 |
| R3 | `lang-sequencing` | **pure imperative** | `let mut`, `:=`, `for` over lists and ranges, `while … decreases`/`fuel`, early exit; lowering to folds with unfolding equations and exposed step functions | the decimal formatter and `wc`'s step are written imperatively, and their theorems are proved by the existing tactics with no hand unfolding; negative controls refuse by reason | R2 | R5 |
| R4 | `hih-native-heather` | **N1 design** | design note: the reflector's fragment, layouts of records and enums in words, `Nat` narrowing, how the `_agrees` certificate scales (stated per loop and per function), and how the builder is retired | decided by Minus; N1's issues filed, `native-build-loop-regions` and `native-build-reflected-helpers` folded in | — | R1 |
| R5 | `hih-native-heather` | **N1: pure functions compile** | the reflector of §4 N1, with `compile-x86` moved onto it | a `wc` step over a `WcState` record and the decimal formatter, written as ordinary Heather, compile into a tool and pass its GNU test; `compile-x86`'s examples still pass | R4 (R3 for the imperative spellings) | R2, R3 |
| R6 | `hih-native-heather` | **N3: I/O as capabilities** | `effects-uniqueness-surface` over §3's surface; byte and string literals; implicit compiler imports | `cat FILE…`, `wc` and `head -n` are rewritten in it and pass the same GNU tests; the builder versions are deleted | R3, R5 | R7 |
| R7 | `hih-self` | **S1: the lexer** | Heather's lexer in Heather, streaming tokens, compiled natively | `heather-lex` matches the Rust lexer on every file under `lib/` | R6 | R8, R10 |
| R8 | `hih-native-heather` | **N2: procedures** | compiled calls with frames on the process stack, derived contracts, a register convention; `io-image-process-stack` finished | one helper called from several sites is compiled once; a non-tail recursive function compiles; `grep -F` is built with a shared line-buffer helper | R5 | R7 |
| R9 | `hih-native-heather` | **N4: the heap** | a short design section first, then the bump arena, `datarepr` cells for `List` and trees, arena exhaustion as a defined exit | `sort` (lines into a list) and `tac` are written as ordinary Heather and pass GNU tests | R8 | R10 |
| R10 | `hih-passes` | **first pass in Heather** | constant folding and dead-node removal over FunctionIR regions, proved once to preserve `eval`, run inside `Source::compile` | the regression tools build with smaller code and unchanged GNU results; the proof is one theorem, not per program | — | any |
| R11 | `hih-self` | **S2: the compiler compiles itself** | `Source::compile` and its checks compiled by N1–N4; `write-elf` runs the binary in place of the fork's evaluation | `write-elf` builds the corpus through it; `scripts/perf ab` shows the fork's read-back counters gone, with the kernel check unchanged | R9 | — |

R1 and R4 can start today. R10 can start today in the native lane. After
R1, the language lane (R2, R3) and the native lane (R5, R8, R9) run side by
side and meet at R6.

**Kept running beside them, pulled by these rounds.** The certificate cost
that grows with the program (next-areas item 1,
`native-tool-test-cold-certificate-rail`) stays an enabling round. R6 pulls
it, because the rewritten tools must check under the suite's rail. N2 also
cuts code size, which lowers that cost. Lemma search, the monoid
normaliser, ML and export are in other lanes and are not affected by this
proposal.

### 6.1 What happens to the open native issues

| issue | under this proposal |
|---|---|
| `native-tools-suite` | closed as re-scoped: nine tools stand as the corpus; `grep -F`, `sort`, `tac` move to R8/R9's "done when"; `basename`, `dirname`, `rev`, `cmp` are left for anyone who wants them |
| `native-build-loop-regions`, `native-build-reflected-helpers` | folded into R4/R5 |
| `effects-uniqueness-surface` | R6 |
| `self-hosting-first-component` | split into R7 and R11 |
| `datarepr-separation`, `memory-bound-certificates` | R9 (metering after it) |
| `native-procedure-contracts`, `io-image-process-stack`, `native-register-moves-and-convention` | R8 |
| `prelude-option-and-friends` (layer 2), `pipeline-operator`, `function-composition-operator` | R1 decides whether they are still needed after binding statements |
| `tactic-composition-ergonomics` | stays separate: it is about proof scripts (`split_all; all_goals {…}`), not about binding results |
| `native-decimal-io-proved`, `native-compile-stat` | unchanged, not scheduled |

---

## 7. Decisions for Minus

1. **Adopt the thesis** (§2): native programs become ordinary Heather
   functions, and the builder becomes the compiler's back half.
2. **`hih-tools`**: close it at the nine built tools as a regression corpus
   (recommended), or keep its "done when" and finish the remaining five
   alongside.
3. **Binding over a carrier** (§3.1): `Tac` and the builder already have
   monadic types, and the sugar hides the CPS without adding any. Is that
   inside the effects decision's "users never write monadic types", or do
   you want binding limited to named carriers (`Tac`, `Result`, `Option`)?
4. **The lexer before the heap** (R7 before R9): the first Heather-in-Heather
   program would stream tokens with no allocation. The alternative is to
   wait for the heap and have the lexer return a token list.
5. **Roadmap shape**: add `lang-sequencing` (area `language`, pulled by
   `heather-in-heather` and `tactics`) and `hih-native-heather` with
   `nh-front`, `nh-procedures`, `nh-effects`, `nh-heap` as submilestones;
   re-scope `hih-first-alloc` into `nh-heap`; give `hih-self` the
   submilestones `self-lexer` and `self-compiler`. Once you decide, the
   roadmap rows, the log line and the issues go on this PR before it
   merges.

## 8. Risks, and what would change the order

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
- **"Composing" may mean proofs too.** This proposal reads Minus's "less
  painful composing" as composing computations. If it also means composing
  large proofs (stage theorems instead of one big one, for cost reasons:
  `frontend-large-proof-composition-cost`), that is an elaborator-cost
  round that fits in the language lane beside R2.
