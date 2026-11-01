# `runtime fn` setups: what a setup is, what it checks, how it is proved once, how it lowers

Status: **proposed, 2026-10-31, for Minus to decide (§14).** Round R4 of
`docs/compiler-milestones-proposal.md` (issue `runtime-fn-setups-design`,
milestone `nh-front`). Nothing here is built. Written on master `f9a1a59`.

The proposal (§4) fixed the frame: an ordinary `fn` is kerneltime
mathematics and never runs; a function crosses to the machine only when it is
marked `runtime fn` under a **setup**, a library value that boxes the function,
checks a judgment over its code, is proved sound once, and lowers to the back
half that exists today (`Source`, FunctionIR, `Source::compile`). Minus's note
(2026-10-31): there is a default setup, "abstract programming that can talk to
the system", and users can build others, such as a borrow-checked one that
hands the compiler extra proofs.

Read `docs/compilation-vision.md` first: it collects the settled principles
and the larger picture this note is one part of. There, a setup is one kind
of **language** (terms, meaning, judgment, compiler, one soundness theorem)
whose terms are reflected from ordinary function bodies; DSLs, restricted
dialects and hand-written instances are the other producers of `Compile(f)`,
and setups also publish **facts** (side-proofs such as `Unique` or `Writes`)
for the compiler's passes to find.

This note says what each of those words is, concretely enough that R5
(`runtime-fn-default-setup`) can be handed to a thread, and names what R5 must
verify before it builds (§12).

---

## 0. The proposal in one page

```heather
// Ordinary Heather, kerneltime maths. Spellings are illustrative throughout.
record WcState { lines: BitVec(64), words: BitVec(64), inside: Bool }

runtime fn wc_step(s: WcState, b: BitVec(8)) → WcState {
    let space = b.is_space();
    WcState(lines := s.lines.add(b.is_newline().word()),
            words := s.words.add((!space && !s.inside).word()),
            inside := space.not())
}
// `runtime` is a library generator, not a keyword (§9). After `wc_step` is
// elaborated as an ordinary fn, the generator publishes beside it:
//   wc_step::rt        : rt::Program       the body, reflected as data       (§3, §4)
//   wc_step::judged    : default().judge(wc_step::rt()) = Ok        by refl  (§5)
//   wc_step::reflects  : wc_step::rt().meaning(…) = wc_step         by refl  (§4.3)
//   instance Compile(wc_step)          the code and its agreement theorem (§6, §9.3)
```

1. **A setup is a record value** with a judgment, a lowering and one soundness
   theorem (§2). Every setup reads the same reflected language, `rt`, and
   setups differ in what they accept, what they prove and how they lower.
2. **Reflection is a Heather generator over the host interface** (§3). It
   reads the elaborated body through new host requests (a definition's body,
   λ and `match` arms in a view, shared subterms by identity), never through
   Rust and never through layer-m `match code`. It is untrusted.
3. **The reflection is tied to the function by one equation, checked by
   conversion**: the reflected program's meaning is the function (§4.3). That
   is the only per-function certificate. It is structural (an interpreter
   unfolding against a body it mirrors node for node), not an evaluation of
   FunctionIR, so it needs no case analysis and no loop induction.
4. **The lowering is proved correct once, over the fragment** (§6). This is
   route 2 of `in-language-certificate-emission`, and it replaces
   `compile-x86`'s per-function `_agrees` theorems, whose decided cases split
   over every comparison of a pass. The proof's cases already exist as
   `compile-x86`'s certificate templates and the general FunctionIR loop
   lemmas (§6.3 prices it).
5. **The compiler consumes a setup's evidence inside the setup's own lowering
   and theorem** (§6.2). The back half keeps one contract for every setup. A
   stricter setup is one whose lowering may do more (update in place, skip a
   copy) because its judgment proved it may.
6. **The default setup's first fragment (N1)** is first-order code over words
   of the ISA's widths, `Bool`, flat records and enums laid out as words, byte
   buffers, `match`, R3's loops and calls between runtime fns (§7, §8).
7. **`runtime fn` is a declaration prefix that names a generator**: `g fn f`
   runs the library generator `g` over the elaborated `f`;
   `runtime(owned) fn f` picks a setup (§9). A runtime fn may call only its
   setup's primitives and other runtime fns.
8. **The `Compile` class stays, and a setup is one way to produce its
   instances** (§9.3). `Compile(f)` is an operation-indexed class keyed on the
   function (`Monoid<A>(op)`'s mechanism): code plus its agreement with `f`.
   The `runtime` generator publishes `instance Compile(f)`; a hand-written
   instance (tuned FunctionIR and its proof) is accepted with no setup; a call
   finds its callee's code by instance search. `runtime-compile-opt-in` closes
   as superseded; `compile-typeclass-design` narrows to this.

---

## 1. What this builds on

**`compile-x86` today** (`crates/elab/src/function_ir_source/program.rs`,
`crates/cli/src/native/verified.rs`). An untrusted Rust reflector reads the
elaborated body of a `BitVec(64)` function with at most six parameters and
builds a FunctionIR program: literal constants, `add`/`sub`/`band`/`bor`/`bxor`,
calls to functions of the same fragment as `Call` regions, tail `match` on a
test, recursion on a fuel, and `decreases` recursion on a word's `toNat`, each
a `Loop`. The certificate is `program_eval(program, f, args) = f(args)`:

- by `refl` against the total evaluator when every `match` is on a comparison;
- through an *expansion* (the same decision tree in source operations) and
  `split_all; all_goals { refl }` when a test goes through `&&`, `||`, `!` or a
  Bool helper ("decided"), which is a case split over every comparison;
- by `loop_eval_agrees` / `loop_eval_agrees_measured` plus a per-loop pass
  proof (`_pass_cased`, `_pass_tree`, `_unfolds`, `_runs`) for loops.

Calls are proved against the callees' sources (`program_eval_sources`), so no
proof unfolds a callee. `compiled_returns` then carries the result through
`lower_program` to x86, proved once. This note keeps that shape and moves two
things: the reflector into Heather, and the per-function agreement into one
theorem.

**The host interface** (`docs/host-elaboration-interface-design.md`). A
generator is a `Tac<List<Decl>>`, run by `generate g(args);` (§19), whose
declarations are checked and published together or not at all. A term reaches
Heather as a lazy, surface-level view with host-issued handles (§4). There is
no request yet for a definition's body, and `View` shows a `match` only as
`HMatch(scrut)` (no arms) and has no λ form (§3 below).

**The sequencing surface** (`docs/sequencing-surface-design.md`, decided, PR
#313). Layer 2 lowers in the elaborator, so a runtime fn's elaborated body
contains no mutation: `let mut` is SSA aliases, a statement `if` joins per
variable, a `for` is `O::foldl` (or `O::for_in` with an early exit) of a named
sibling step `f::step` over a state record `f::State`, and `while … decreases`
is a generated `decreases` function `f::run` (§5). Effects are layer 2 as well:
a capability is a `let mut` local and a `mut self` method returns the pair
(§8.2). §8.3 there assigns uniqueness to the setups, and §9 says the lowered
shapes are the setups' input.

**The back half.** `Source` (`lib/native/native_source.hthr`): statements over
words and buffers whose pure leaves are `StructuredRegion`s (FunctionIR:
`Dataflow`, `Sequence`, `Compose`, `Conditional`, `Call`, `Loop`), with a
function table for `Call`. `Source::compile` and its theorem
(`native_compile_correct.hthr`), `write-elf`'s ELF theorem, and
`lower_program`/`compiled_returns` for a pure program exported under the C ABI.
None of it changes here.

**`datarepr`** (`docs/datarepr-design.md`, v1 in `crates/elab/src/datarepr.rs`)
owns runtime representations of recursive spec inductives, and its §2.4 owns
the `Nat` narrowing. N1 needs neither: its data is flat (§7.2).

---

## 2. What a setup is

### 2.1 The record

```heather
// lib/native/runtime/runtime.hthr (spellings illustrative)
inductive Verdict { Ok, Refused(why: String, at: rt::Path) }

record Setup {
    name: String,
    // The judgment: decidable, an ordinary function over reflected code.
    judge: rt::Program → Verdict,
    // The lowering: into the back half. `None` only where `judge` said `Ok`
    // and a resource ran out (a width, a port count), never silently.
    lower: rt::Program → Option<rt::Code>,
    // Proved once. Where the judgment accepts and the lowering produces code,
    // the code means what the reflected program means.
    sound: (p: rt::Program) → judge(p) = Ok → (c: rt::Code) → lower(p) = Some(c) → c.Agrees(p),
}
```

- **`judge`** returns reasons, not a `Bool`: every refusal names what it
  refuses and where (`docs/test-value-audit.md` §5), and `at` is a path into
  the reflected program that the generator maps back to a source span (§5.2).
  The soundness hypothesis is `= Ok`, which the kernel checks by evaluation.
- **`rt::Code`** is what the back half takes: a FunctionIR program (a
  `List<Function>` and an entry) for pure code, and a `Source` once N3 adds
  effects. `Agrees` is stated per kind (§6.1).
- **One reflected language for every setup** (decision 3, §14). The judgment
  and the lowering are where setups differ. A setup that wants more structure
  (lifetimes, say) adds annotations the generator reads *from the same body*,
  or a judgment that infers them; it does not get its own AST. This is what
  lets setups compose (§11) and keeps one reflector.

### 2.2 What `runtime fn f` publishes

For `runtime fn f` under setup `s` (the default unless named), after `f` is
elaborated as an ordinary `fn`, the generator publishes one group (all or
none, as `generate` does today):

| declaration | statement | proof |
|---|---|---|
| `f::rt()` | `rt::Program`: `f`, and the runtime fns it calls by reference (§9.2) | definition (data) |
| `f::judged` | `s.judge(f::rt()) = Ok` | `refl` (kernel evaluation) |
| `f::reflects` | `(xs…) → f::rt().meaning(callees…)(xs…) = f(xs…)` | `refl` (conversion, §4.3) |
| `f::code()` | `rt::Code` | `s.lower(f::rt())` unfolded, or evaluated by the generator and pinned by `refl` |
| `instance Compile(f)` | `f::code()` and `agrees : (xs…) → f::code().run(encode(xs…)) = encode(f(xs…))`, callees answered by their own `Compile` instances | `s.sound(…)` rewritten by `f::reflects` |

`Compile(f)` is the one thing every consumer reads: a runtime fn calling `f`,
the builder's helper form while it exists, `compile-x86`, and N3's program
entry. Its agreement theorem mentions `f` itself, so no consumer ever sees
`rt`.

---

## 3. Reflection: from an elaborated body to `rt`

### 3.1 Where it runs

The reflector is a Heather function `rt::reflect(g: GlobalRef) →
Tac<rt::Program>`, run inside the `runtime` generator. It is untrusted: a
wrong reflection fails `f::reflects` (the kernel refuses the conversion), and
the generator then reports "reflection disagrees with `f`", a bug in the
reflector, never a wrong program.

The two alternatives, rejected:

- **Extend the Rust reflector.** Cheapest now, and it keeps the fragment's
  definition in Rust, which the roadmap's "logic in Heather, not Rust" and
  `function-ir-source-denotation-after-b2`'s option 2 both argue against.
  It stays as `compile-x86`'s producer until R5 retires it (§10).
- **Layer-m `match code` over the boxed body** (certgen's route, deleted in
  B2). Variables are opaque at layer v (`code-variable-analysis-api`), so
  every variable needs a marker pass in Rust, and the fragment's walkers cost a
  52-branch recursor each. The host view already solves both: locals are
  host-issued refs, and a view is one layer at a time.

### 3.2 What the host must add

`View` was built for tactics, which read goals and never a definition's code.
A reflector needs (issue `runtime-body-reflection-requests`):

1. **`Body(g: GlobalRef) → Checked<Handle>`**: the elaborated value of a
   definition. Refused for a theorem, an axiom, a constructor or anything
   with no body. An `interface fn` (§6.3 of the proposal) is *not* refused:
   boxing is intensional analysis, not conversion in a proof.
2. **λ in a view**: `HLam(dom: Handle)`, opened by `Open` as a function
   type's binder is today, so a body's parameters become host refs.
3. **`match` with its arms**: `HCases(scrut, motive, arms)` where each arm is
   the constructor, its fields opened as locals, and the arm's body, the way
   `Cases` already presents a split goal. Equation binders (`match h: c`)
   appear as a local whose type is a proposition, which the reflector erases
   (§3.3).
4. **Sharing by identity.** A block's `let` is an alias, not a binder
   (`docs/let-and-blocks-design.md` §4.4): the kernel term has no `let`, only
   a shared subterm. A reflector that walks a tree re-reads every shared node
   at every use, which is exponential over an SSA chain. So the host must
   answer the *same handle* for the same shared subterm within a run (or a
   `Same(a, b)` request), and the reflector memoises on handles, building a
   DAG whose shared nodes become `rt` lets. The Rust reflector does this
   today (`examples/x86-native/sharing.hthr`).
5. **One request per node is the cost.** Evaluating the generator between
   requests dominates a tactic's cost (§8 of the host design), and a 2,000-node
   lexer body would be 2,000 round trips. If R5 measures that as the
   bottleneck, a bulk `Reflect(h)` answers a whole tree of heads at once with
   shared nodes numbered. The protocol does not change, only the batching.

### 3.3 What reflection keeps and drops

- **Types.** Every reflected node carries its `rt::Ty` (§4.1), read from the
  host's `Infer` and classified by viewing the type. A type with no `rt` code
  is a refusal naming the type ("`List<Nat>` has no runtime layout under the
  default setup").
- **Proofs and types are erased.** A subterm whose type is a proposition (an
  equation binder, a `decreases` obligation, a `Fin` bound) or a universe is
  not runtime data. The reflector drops it, and the meaning (§4) does not need
  it, because the pin is proved against `f` by conversion and propositions
  are irrelevant to what `f` returns. Where `f`'s result depends on a proof
  computationally (a `match` on an equality), the reflector refuses.
- **Names.** Globals the setup knows are primitives (§7.1) become `Prim`
  nodes. Runtime fns become `Call`s (§9.2). Any other global is a refusal
  ("`Nat::max` is an ordinary fn: mark it `runtime fn`, or the default setup
  has no primitive for it").

---

## 4. The reflected language `rt` and its meaning

### 4.1 The data

```heather
// lib/native/runtime/rt.hthr (illustrative)
inductive Ty {
    Word(width: Nat),             // BitVec(w), w a width the ISA model has
    Bit,                          // Bool
    Rec(fields: List<Ty>),        // a flat record: its kernel lowering (§12 V2)
    Enum(ctors: List<List<Ty>>),  // a flat enum: constructors' fields
    Bytes(capacity: Nat),         // List<BitVec(8)> of length ≤ capacity, held in a buffer
}
inductive Tm {
    Var(i: Nat),                                   // a parameter or a `Let`
    Lit(t: Ty, n: Nat),
    Prim(op: Op, args: List<Tm>),                  // a setup primitive (§7.1)
    Let(t: Ty, e: Tm, body: Tm),                   // a shared subterm (§3.2 item 4)
    If(c: Tm, yes: Tm, no: Tm),
    Case(t: Ty, scrut: Tm, arms: List<Tm>),        // an arm binds its constructor's fields
    Make(t: Ty, args: List<Tm>), Field(t: Ty, i: Nat, of: Tm),
    Call(fn: Nat, args: List<Tm>),                 // a runtime fn, by index into the program
    Fold(over: Tm, init: Tm, step: Nat),           // `foldl` of a named step (R3)
    ForIn(over: Tm, init: Tm, step: Nat),          // `for_in`: early exit (R3)
    Measured(fn: Nat, args: List<Tm>),            // a `decreases` fn's recursion (R3b, compile-x86 today)
}
record Fun { params: List<Ty>, result: Ty, body: Tm }
record Program { funs: List<Fun>, entry: Nat }
```

The constructors mirror the elaborated forms node for node, including the
recursion shapes R3 emits. Nothing in `rt` is a FunctionIR concept (ports,
valuations, bounds): those belong to the lowering. That is what makes the
reflection checkable by conversion and the lowering provable once.

### 4.2 The meaning

`Ty::sem : Ty → Type` is a large elimination (`Word(w) ↦ BitVec(w)`,
`Bit ↦ Bool`, `Rec(fs) ↦` the product the record type lowers to,
`Bytes(c) ↦ List<BitVec(8)>`). `Program::meaning` gives each function the
Heather function of its signature, with calls answered by a table of meanings
(as `program_eval_sources` answers calls by the callees' sources). The
interpreter is **type-directed**: it is defined by recursion on the node with
the expected `Ty` in hand, and every place where two types must agree (a
variable's type, a call's result) is decided on *closed* type codes. Over a
concrete program every such decision computes to `refl` and every cast
vanishes, so only the arguments are neutral. That is the property §4.3 needs
and the first thing §12 verifies.

The alternative, an untyped value domain with a `decode` at the end, fails
exactly at branches: `decode(match c { True => W(x), False => W(y) })` is not
`match c { True => x, False => y }` without a commuting conversion. An
intrinsically typed family `Tm(Γ, τ)` would avoid casts, but its indices are
computed (`Var(i) : Tm(Γ, Γ[i])`), which route-1 indexed families refuse
(`docs/inductive-indexed-lowering.md` §8).

### 4.3 The pin: `f::reflects` by conversion

`f::rt().meaning(callees)(xs…) = f(xs…)` at neutral `xs`. The left side
unfolds the interpreter once per `rt` node and lands, node for node, on the
term the elaborator built for `f`: `Prim(add)` on `BitVec::add`, `If` on the
`Bool` eliminator, `Fold(over, init, k)` on `over.foldl(f::step, init)` where
`k`'s meaning is `f::step` (answered from the table, so `f::step` is not
unfolded), `Measured` on `f::rec` at its bound (as `loop_eval_agrees_measured`
states it today). It is the round-trip pin that
`issues/elabcode-abstraction-layer.md` described ("reify(reflect(c)) = c at
any concrete instance is refl, free, today"), stated against the function
instead of against code.

Two things this pin does not do that `_agrees` does today. It never evaluates
FunctionIR, so it carries no valuations. And it never case-splits, because
`a && b` reflects as `Prim(and, [a, b])` whose meaning is `Bool::and`, the very
function the elaborator applied. The tree of `Conditional`s that `&&` lowers
to is the lowering's business, proved once.

The cost is linear in `f`'s DAG: the kernel's conversion shares as the terms
do. It is not free (the interpreter's unfolding is a constant factor per
node), and R5 records its shape against `_agrees` on the same examples.

---

## 5. The judgment

### 5.1 The default setup's judgment

"Is in the fragment", decided over `rt::Program`, in Heather:

- every `Ty` is one the setup lays out (§7.2), at a width the target has;
- every `Prim` is in the setup's primitive table at its types;
- every `Call` names a function of the program, with matching arity and types
  (the reflector built them, but the judgment does not trust it);
- loops are the shapes §7.4 lowers;
- the program's call graph is acyclic except through `Measured` (a recursive
  call that is not a loop is N2's, `native-compiled-procedures`);
- in N3, capability linearity (§8.3 of the sequencing design): each version
  of a capability is used exactly once and never stored in a record, a
  closure or a buffer.

Most of these the reflector already refused with a better message. The
judgment repeats them because `sound` may assume only what `judge` checked.

### 5.2 Where refusals point

The generator runs the judgment twice: once in the elaborator, to report a
refusal at the source span of the offending node (it keeps a side table from
`rt` paths to the handles it reflected, and handles keep their provenance,
host design §4.3), and once in the kernel, as `f::judged`'s `refl`. A refusal
reads "`wc_step` cannot be a runtime fn under the default setup: `Nat::max` is
an ordinary fn …" at the call, with the setup named.

---

## 6. Soundness once, and the evidence

### 6.1 What `Agrees` states

For pure code (N1): `c.Agrees(p)` is, for every entry argument tuple, that
the FunctionIR program `c` evaluates on the arguments' encoding to the
encoding of `p.meaning(…)` on them, with callees answered by their own
`Compile` instances. `encode_τ : τ.sem → List<BitVec(w)>` is the layout of §7.2.
Composed with `f::reflects`, it is the statement `Compile(f)`'s `agrees` field holds:
`f::code().run(encode(xs)) = encode(f(xs))`. Downstream, `compiled_returns`
carries that to x86 for an export, and a `Compute` leaf's region meaning
carries it into a `Source`.

For effectful code (N3) it becomes a tree statement:
`Implements(c.denote(args), p.tree(args))`, where `p.tree` reads capability
operations as events. That statement belongs to R6
(`effects-uniqueness-surface`), which owns the denotation agreement
(`ITree::run_state_bind`); this note fixes only that the setup's `sound` is
where it is proved, once.

### 6.2 How the compiler consumes a setup's evidence

Inside the setup. A setup's judgment establishes facts about the reflected
program; its lowering is written to *use* them (an in-place buffer update
where the judgment proved the old version dead, no copy of a record the
judgment proved unshared); and its `sound` is proved under the hypothesis
`judge(p) = Ok`, so the facts are discharged once, in the setup's proof, and
never per program. The back half sees ordinary FunctionIR and `Source` with
one contract (`Source::compile`'s theorem) for every setup.

The alternative, passing facts into the back half (a `Source` annotated "this
buffer is unaliased"), is deferred to the round that needs it: register
allocation across N2 calls is the likely first customer, and then the back
half checks the annotation or the setup proves it, case by case. Nothing in
N1 needs it.

### 6.3 What the once-proof costs (route 2, priced)

`default().sound` is an induction over `Tm` under a lowering invariant: an
environment from `rt` variables to FunctionIR ports, fresh ids above every
written port, and the valuation agreeing with the encoded meaning on every
port in the environment. Its pieces, and where each already exists:

| case | lowers to | the lemma it needs | exists today as |
|---|---|---|---|
| `Lit`, `Prim` on words and bits | `Dataflow` nodes | each `Node`'s evaluation is its `BitVec` operation | FunctionIR's node equations (`function_ir_eval.hthr`) |
| `Let`, sequencing | `Sequence`/`Compose` | evaluation composes; a region writes only fresh ports | `region_extends`-style frame lemmas (back half), and `compile-x86`'s per-function templates |
| `If`, `Case` on a bit or enum tag | `Conditional` | `Conditional` evaluates the chosen branch | used by every decided `_agrees` |
| `&&`, `\|\|`, `!`, Bool helpers | trees of `Conditional` | the tree decides the connective | today a per-function `split_all`, here one lemma per connective |
| `Make`, `Field` | ports per field (§7.2) | layout lemmas: `encode` of a record is its fields' encodings | new, small |
| `Call` | `Call` region | callee's `Compile` agreement | `program_eval_sources` |
| `Fold`, `ForIn` over `Bytes` or a range | `Loop` with `BufferLoad` | `loop_eval_agrees` instantiated at the step's meaning | `function_ir_compile::loop_eval_agrees` |
| `Measured` | `Loop` of at most the measure | `loop_eval_agrees_measured` | the same file |

So the once-proof is new in its invariant and its record layout lemmas, and
old in every per-construct case: those are `compile-x86`'s templates with the
closed instance replaced by a quantifier. The shape is one case per construct
plus one frame lemma family, and adding a construct adds one case. Per
program, the kernel does no proof at all, only `f::judged` (evaluation, linear
in the program), `f::reflects` (conversion, linear) and, at `write-elf`, the
compile it already evaluates.

What that buys over today: the decided route's `split_all` is a case split
over the comparisons of a pass, exponential in their number, and each loop
regenerates its pass proof. Both disappear. This is the scaling risk
proposal §9 named.

**The lifecycle, if a construct is not proved yet.** A setup may accept a
construct its `sound` does not cover yet by publishing, for that function,
today's certifying certificate (`_agrees` against the lowered code) instead of
citing `sound`. That keeps the trust boundary where it is (every output is
kernel-checked) and only moves cost: experimental constructs live certifying,
stabilized ones join the induction (`in-language-certificate-emission`'s
"lifecycle, not a fork"). Decision 1 (§14) is whether N1 starts verified or
certifying.

---

## 7. The default setup's lowering (N1)

### 7.1 Primitives

A table from globals to `rt::Op`, each with its FunctionIR node and its case of
`sound`: `BitVec::add`/`sub`/`band`/`bor`/`bxor`, shifts, `eq_bit`,
`unsigned_lt_bit`, `signed_lt_bit` (FunctionIR's nodes today), `Bool::and`,
`or`, `not`, `Bool::word`, `zero_extend`/`truncate` between widths, and the
byte reads and writes of a `Bytes` value at a word index. Multiplication,
division and remainder have no FunctionIR node yet; the decimal formatter
needs them or a loop, so `function-ir-alu-core` gains them as N1's first
back-half addition. The table is a library value, so a later setup (or P3's
lemma registries) adds a primitive by registering an op with its lemma, not by
editing the reflector.

### 7.2 Layout: flat data as words

| `rt::Ty` | encoding | |
|---|---|---|
| `Word(w)` | one port of width `w` | widths the ISA model has |
| `Bit` | one port of width 1 | |
| `Rec(fs)` | the fields' encodings, concatenated | scalar replacement: a record is never in memory in N1 |
| `Enum(cs)` | a tag port, then the widest constructor's fields | payload-free enums are the tag alone |
| `Bytes(c)` | a `Source` buffer of capacity `c` and a length word | the buffer's bytes are the list (`Env::buffer`) |

Records and enums are *values*, so a `WcState` is three ports and not a set of
word ids the program names. This is the setup's own layout, not `datarepr`:
flat data needs no abstraction function, its encoding is a bijection on its
image, and the layout lemmas are refl-shaped. `datarepr` enters with N4, for
recursive data.

`Nat` is not in N1's table (decision 6, §14). It is accepted only where a
bound is structural: a literal, a `Bytes` length or index (bounded by the
capacity), and a loop's count. Checked `Nat` arithmetic with overflow as a
trap exit needs an exit, which arrives with N3's `Source` statements; it is
filed as `runtime-nat-checked-arithmetic`.

### 7.3 Calls

A `Call` lowers to FunctionIR's `Call` region against the program's function
table, as `compile-x86` lowers calls today, so a callee's code is emitted once
per program, not once per call site. FunctionIR's `Call` takes and returns
64-bit words, one result: a record argument or result needs several, so
`function-ir-multi-word-calls` widens it (or, until then, the lowering inlines
a callee whose signature is not all single words, which `sound` covers by a
substitution lemma). Frames on the process stack and a register convention are
N2's (`native-compiled-procedures`), and they change the back half, not this.

### 7.4 Loops

R3's shapes, which are the ones the native compiler already verifies
(sequencing design §9):

- `over.foldl(f::step, init)` over `Bytes` or a range `List::range_from(a, n)`:
  a `Loop` of at most the length's passes, the state the step's encoded state,
  the element a `BufferLoad` (or the counter). `f::step` is itself a runtime fn
  of the program, reflected and proved like any other.
- `over.for_in(f::step, init)`: the same, with `ForStep`'s tag as the exit bit.
- `f::run` from `while … decreases` and any `decreases` fn on a word's
  `toNat`: `Measured`, a `Loop` bounded by the measure, as `compile-x86` does
  (`loop_eval_agrees_measured`).
- Fuel recursion (`while … fuel`): a `Loop` bounded by the fuel.

A recursion of any other shape is refused under N1 with "a recursive call
that is not a loop needs procedures (N2)".

---

## 8. The default setup beyond N1

Recorded so N1's shapes do not paint N2–N4 into a corner, not designed here.

- **N2 (procedures).** A recursive call that is not a loop becomes a call of a
  compiled procedure with a frame. `rt` already has `Call`; what changes is
  that the judgment admits cycles in the call graph and `sound` gains the
  procedure-contract case, proved once (`native-procedure-contracts`).
- **N3 (effects).** A capability is a `let mut` local and its methods `mut
  self` (sequencing design §8.2), so `rt` gains capability types and an
  `Invoke(op, cap, args)` node whose meaning is the world-threading function.
  `rt::Code` becomes a `Source`: runs of pure statements become `Compute`
  leaves through N1's lowering, `Invoke`s become `Invoke` statements, and
  loops containing `Invoke`s become `Repeat`. The judgment adds capability
  linearity. Entry: `runtime fn main(io: Io, args: Args) → Exit` publishes a
  `Source`, and `write-elf` compiles it as it compiles a builder tool today.
- **N4 (heap).** `Ty` gains a datarepr-backed constructor (`Repr(spec, repr)`),
  laid out as an arena cell index, its meaning the spec type through `abs`.
  Arena exhaustion is a defined exit, like the `Nat` trap.

---

## 9. The marker

### 9.1 `runtime fn f` is a generator prefix

`runtime` is not a keyword. The parser reads an item of the form
`IDENT fn …` or `IDENT(args) fn …` as a **generator-prefixed declaration**:
the `fn` is elaborated and published as written, then the generator that
`IDENT` resolves to (an ordinary library function returning
`Tac<List<Decl>>`) runs with the new function's `GlobalRef` and `args`, and its
group is published beside it, or the whole item is refused with the
generator's error. `runtime fn f` is the default setup; `runtime(owned) fn f`
passes a `Setup` value. An identifier before `fn` is not otherwise a valid
item, and the existing modifier keywords (`meta fn`) are matched first, so an
unknown prefix is "`runtme` is not a generator in scope".

Built 2026-11-01 (`docs/value-definitions-design.md` §3), with one change:
the generator receives the declaration's **name**, a `String`, in front of the
written arguments (`runtime("f", setup)`), and calls `lookup` for its
`GlobalRef`, since a `GlobalRef` is issued by a run and none exists before
it starts.

This is the first syntax-carrying form of `scoped-declaration-generators`:
the generator receives an already elaborated declaration, the case that issue
distinguishes from lowering syntax first. Alternatives: `generate
runtime(f);` after the fn (works with no parser change today, but separates
the marker from the function it marks), and an attribute form (`@[runtime]`),
which Heather has no other use for yet. Issue `declaration-prefix-generators`.

### 9.2 Callees

A runtime fn calls only its setup's primitives and other runtime fns
(decision 5, §14). Ordinary helpers are refused with the reason, and the fix
is to mark them. That is Minus's model taken literally ("not every function
is compiled"): a helper crossing to the machine is a decision someone wrote
down, and nothing is compiled because something else happened to call it.
The alternative, reflecting an ordinary helper through and inlining it,
silently compiles mathematics and makes a library edit change what runs.

A `Call` in `f::rt()` names its callee, and the generator finds the
callee's code by instance search for `Compile(g)`, so a callee is compiled
once, in its own declaration (or by hand, §9.3), and `f`'s certificate cites
its agreement. Changing how `g` is compiled (another setup, a hand instance)
changes no caller. The agreement statement is the same for every instance,
whoever produced it, which is what lets a caller's `sound` cite a callee
compiled under another setup; a setup that needs more from its callees
(ownership's non-aliasing) asks for a stronger class, a question for R12.

### 9.3 The `Compile` class: what stays, what changes

The first draft of this note made `Compiled(f)` a plain record and closed
`compile-typeclass-design`. Minus asked about the class (2026-10-31), and
keeping it is better: a record has the class's content (code plus its
agreement with `f`) but loses two things only a class gives.

```heather
// an operation-indexed class, keyed on a function value (docs/operation-indexed-classes-design.md)
class Compile<F>(f: F) { code: rt::Code, agrees: code.Agrees(f) }

runtime fn step(…) → … { … }
// the generator publishes:  instance Compile(step) := default().compiled(step::rt(), step::judged, step::reflects)

instance Compile(fast_hash) := Compile(code := tuned_ir(), agrees := tuned_ir_agrees)   // by hand, no setup
```

- **Hand-written instances.** `runtime-compile-opt-in` decided that a valid
  hand-written instance is accepted without the marker. A setup is then one
  way to produce instances, not the only one: hand-tuned FunctionIR for a hot
  function, with its proof, is used by every caller.
- **Resolution.** A call finds its callee's code by instance search (§9.2),
  instead of a callee list fixed at reflection.

| the old issue's item | here |
|---|---|
| a function runs only with a checked instance or an explicit marker (`runtime-compile-opt-in`, 2026-09-07) | kept: the marker is §9.1, which publishes the instance |
| instances keyed on syntax, so refactoring invalidates them | kept: the generator re-runs whenever `f`'s module re-elaborates, `f::reflects` is checked against the current `f`, and a hand instance whose proof no longer checks is refused |
| coherence | one instance per function; the setup is the instance's content, not its key. Two setups for one `f` need a named or scoped instance, which operation-indexed classes already allow |
| resolution-from-main over the call graph | instance search at each `Call` |
| target indexing (`Compile[Cpu]`) | struck already (2026-08-07): the target is the back half's |
| `CallCtx`-parametric specialization, generic code (`where Compile(A::add)`) | stays open on `compile-typeclass-design`; not needed for N1 |
| `derive_runtime_fn` | the `runtime` prefix |

So `runtime-compile-opt-in` closes as superseded, its open acceptance items
(unmarked rejection, hand-instance success, `examples/x86-native/mix.hthr`
opting in) moving to `runtime-fn-default-setup`, and
`compile-typeclass-design` narrows to the class above plus its open items.

---

## 10. The builder and `compile-x86` on the way

- **Landed (2026-10-31).** `native-build-reflected-helpers` and
  `native-build-loop-regions` closed: the builder has `Calc` regions, and
  `heather reflect <file> <fn>` writes a word function's FunctionIR program
  with `<fn>_native_agrees` as a checked module, which a tool calls through a
  FunctionIR `Call` (compiling once `native-compiled-procedures` lands). In
  R5, `heather reflect` is what the Heather generator replaces: the tool-side
  form (`program(…)`, `call(k, args, r)`) stays, and the program it names
  comes from a `Compile(f)` instance instead of the Rust reflector. The
  `Calc` forms become unnecessary for code a runtime fn can express.
- **R5 (N1).** The Heather generator replaces the Rust reflector.
  `compile-x86 file f` requires a `Compile(f)` instance (from `runtime fn f` or by hand), and runs
  the existing `lower_program`/`compiled_returns` chain with that instance's
  agreement where `_agrees` was. The `examples/x86-native` files gain the
  prefix. `crates/elab/src/function_ir_source/` is deleted once every example
  passes through the generator.
- **R6 (N3).** Tools become `runtime fn main(…)`, and the builder versions are
  deleted (R6's "done when"). The lowering emits `Source` directly, never
  through the builder: the builder's HOAS continuation style is a writing
  surface, and a lowering that is proved once wants a first-order target.

---

## 11. Does the record fit a second setup?

Checked against the two candidates so that the record is not shaped by the
default setup alone.

**Ownership (R12).** After R3, a runtime fn's body has no mutation: `xs[i] :=
v` on a `let mut` buffer is `let xs2 = xs1.set(i, v)`. So Rust-style
ownership over `rt` is a *uniqueness* judgment over SSA versions: `xs1` is not
used after the `set` that consumes it, no version is both stored and used,
borrows are uses that do not consume. The lowering then writes the buffer in
place where the default lowering copies, and `sound` uses uniqueness to show
the old version unobservable. All of it fits the record: same `rt`, a stricter
`judge`, a different `lower`, its own `sound`. Its judgment can be written as
`default().judge(p) = Ok ∧ owned(p) = Ok`, and its `sound` can reuse the
default's cases for everything it lowers the same way, which is the
composition `scoped-declaration-generators` asks for ("a generator may return
evidence consumed by another") in its simplest form.

**Constant time.** Judgment: no `If`, `Case`, loop bound or buffer index
depends on a parameter marked secret (a marked parameter is a generator
argument, `runtime(constant_time(secret := [k])) fn`). Lowering: the default
one. `sound`: the default agreement plus the leakage contract of
`docs/constant-time-survey.md`, stated over the lowered program's trace. Same
record; `Agrees` grows a second conjunct. Nothing in N1 blocks it.

---

## 12. Verification first (R5 opens with these; stop and report if one refutes the plan)

- **V1. The pin by conversion, straight-line and branching.**
  `examples/x86-native/branches.hthr`, `calls.hthr` and `sharing.hthr`, reflected
  by hand into `rt` and pinned by `refl`; including a `&&` test, to confirm
  the type-directed interpreter's casts compute away at closed type codes and
  that `Prim(and)` lands on `Bool::and` with no split.
- **V2. Records.** A `WcState`-shaped record through `Make`/`Field`: does
  `Rec(fs).sem` convert to the record type's kernel lowering, so the pin is
  `refl`, or does it need an `encode`/`decode` round trip (record η)?
- **V3. Loops.** A `foldl` of a named step and a `decreases` word recursion:
  the pin by `refl` with the step answered from the meaning table, and
  `Measured` against `f::rec` at its bound.
- **V4. Erasure.** A `match h:` convoy and a `Fin`-bounded index: the erased
  `rt` still pins.
- **V5. Host reflection.** `Body`, λ and arm views, and handle identity on a
  shared subterm, prototyped far enough to reflect V1–V4's examples from the
  real elaborated terms.
- **V6. One `sound` case end to end.** The `Prim(add)` and `If` cases of
  `default().sound`, to fix the lowering invariant before the rest is
  written.

If V1–V3 show the pin cannot be conversion for some construct, that construct
starts certifying (§6.3's lifecycle) and the note is corrected.

---

## 13. Rounds and issues

R5 (`runtime-fn-default-setup`) is too large for one thread. Its slices, each
an issue:

| slice | issue | scope | done when |
|---|---|---|---|
| R5a | `runtime-body-reflection-requests` | §3.2's host requests | V5; the reflector reads `examples/x86-native`'s bodies |
| R5a | `runtime-fn-reflected-language` | `rt`, `Ty::sem`, `Program::meaning`, V1–V4 | the pins of V1–V4 by `refl` |
| R5b | `runtime-default-setup-soundness` | `Setup`, the default judgment and lowering, `sound` | `default().sound` proved for §7's N1 constructs |
| R5c | `declaration-prefix-generators` | §9.1's syntax | `runtime fn f` publishes `instance Compile(f)`; unknown prefixes refused by name |
| R5d | `runtime-fn-default-setup` (narrowed) | the generator, `compile-x86` on it, the Rust reflector deleted, a tool using runtime fn helpers | its existing "done when" |
| back half | `function-ir-alu-core` (log), `function-ir-multi-word-calls` | `Mul`/`UDiv`/`URem` nodes; multi-word call arguments and results | each issue's own |
| N3 | `runtime-nat-checked-arithmetic` | §7.2's `Nat` trap | when decision 6 is taken |

R5a's two issues run in parallel; R5b needs R5a's `rt`; R5c is independent of
both. R1's R3 (`pure-imperative-statements`) is not a prerequisite for R5a–c:
until it lands the examples are written with `match` and recursion, and its
named steps are what R5d's tool round then consumes.

---

## 14. Decisions for Minus

1. **Certificate route.** The lowering proved once, plus one reflection pin
   per function by conversion (§4.3, §6.3). Alternative: keep today's
   per-function `_agrees` against the lowered FunctionIR (certifying), and
   prove the lowering later. *Recommended: verified from the start for N1's
   constructs, since their proof cases exist as `compile-x86`'s templates;
   the certifying route stays available per construct (the lifecycle).*
2. **Where reflection runs.** A Heather generator over new host requests
   (§3). Alternatives: extend the Rust reflector; layer-m `match code`.
   *Recommended: the host requests.*
3. **One reflected language for every setup** (§2.1), setups differing in
   judgment, lowering and theorem. Alternative: each setup brings its own AST
   and reflector. *Recommended: one `rt`.*
4. **The marker's spelling** (§9.1): `runtime fn f` as a generator prefix that
   resolves `runtime` in scope, `runtime(s) fn f` for a setup. Alternatives:
   `generate runtime(f);` after the fn, or `@[runtime] fn f`.
   *Recommended: the prefix.*
5. **Callees** (§9.2): only primitives and other runtime fns, ordinary helpers
   refused with "mark it `runtime fn`". Alternative: reflect ordinary helpers
   through and inline them. *Recommended: explicit.*
6. **`Nat` at run time** (§7.2): N1 accepts `Nat` only where it is
   structurally bounded (literals, lengths, indices, counts), and checked
   arithmetic with overflow as a trap exit comes with N3's exits.
   Alternatives: no `Nat` at all (words only); or checked arithmetic now, with
   a "trapped" bit in every pure result. *Recommended: bounded now, trap with
   N3.*

Made without asking (say if wrong): flat records and enums are the setup's own
scalar layout, not `datarepr` (§7.2); a setup's evidence is consumed in its
own lowering and theorem, the back half keeping one contract (§6.2); the
lowering emits `Source` directly, never through the builder (§10);
`runtime-compile-opt-in` closes as superseded (§9.3).

---

## 15. Risks

- **The type-directed interpreter may not reduce cleanly** (V1–V2). If casts
  at closed type codes do not compute to nothing under the kernel's `J`, the
  pin needs a generated proof per cast. Fallback: a per-signature interpreter
  generated beside each runtime fn (no casts, one more generated declaration),
  which keeps the pin by `refl`.
- **Reflection cost on large bodies.** One host round trip per node (§3.2
  item 5). The lexer (R7) is the first large body; R5 records the shape, and
  bulk reflection is the fallback.
- **The once-proof's invariant.** Fresh ports, environment and valuation
  agreement is the bulk of `sound`, as the frame lemmas were the bulk of
  `Source::compile`'s theorem. V6 fixes it on two cases before the rest is
  written.
- **R3's shapes may move.** The `rt` loop nodes mirror the sequencing
  design's §5 lowering. If R3 changes a shape, `rt` follows; the pin catches
  any mismatch as a refused conversion, not as a wrong program.
