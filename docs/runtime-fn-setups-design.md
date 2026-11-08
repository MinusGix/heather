# `runtime fn` setups: what a setup is, what it checks, how it is proved once, how it lowers

Status: **decided 2026-10-31 (§14, as recommended); R5a built 2026-11-01; R5b's V6 2026-11-01; R5d's generator 2026-11-04 (§16.8).**
Round R4 of `docs/compiler-milestones-proposal.md` (issue
`runtime-fn-setups-design`, milestone `nh-front`). Written on master
`f9a1a59`. R5a (§13) built `rt`, its meaning, the host requests and the
reflector, and ran V1–V5; §16 records what that changed in §3.2 and §4.1.
Read §16 before the sections it amends.

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

*As built (§16): operands are variables (A-normal form), records are
`Named(i)` codes read from a table, `match h:` is its own node `IfEq`, and
there is no `Measured` node. The file is `lib/native/runtime/rt.hthr`.*

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
byte reads and writes of a `Bytes` value at a word index (`rt`'s `Get` and
`Set`, meaning `List::byte_at` and `List::with_byte`, landed with the
`Unique` fact; a write is in place where `lib/lang/facts/write_facts.hthr`'s
plan carries `Unique`, `docs/facts-on-demand-design.md` §7). Multiplication,
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

The judgment's first form is built: `Program::owned` in
`lib/lang/facts/unique.hthr` is the uniqueness check over `rt` writes, with
parameters owned and calls as moves, and `Unique::of_owned` reads each
write's fact off its verdict (`docs/facts-on-demand-design.md` §7). What
remains for R12 is the surface (borrows a user writes) and the lowering's
`sound`.

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

*Results (R5a, 2026-11-01; `lib/_tests/native/runtime/rt_tests.hthr`):* V1,
V2, V4 and V5 hold, every pin by `refl`; V3 holds for `foldl` and, for
`decreases`, up to the generated unfolding equation (§16.3). V6 moves to R5b,
where the lowering it fixes the invariant of is designed.

*Results (R5b, 2026-11-01; `lib/_tests/native/runtime/rt_lower_tests.hthr`):*
V6 holds. The `Add` and `If` cases (with variables and `Let`, which every
program has) are proved once by induction over `Tm` (`Tm::lower_sound`,
§16.5). V3's measured pin now reaches the function, because `count_down_unfold`
exists (§16.3).

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

---

## 16. What R5a found (2026-11-01)

R5a built `lib/native/runtime/rt.hthr` (the language and its meaning),
`lib/native/runtime/rt_reflect.hthr` (the reflector) and the host requests
(`crates/elab/src/host.rs`, `lib/std/tactic/tactic.hthr`). Four things
differ from §3.2 and §4.1, each forced by something the kernel or the
elaborator does.

### 16.1 The meaning is typed by synthesis, and the casts vanish

`Tm::ty(w, Γ)` computes a node's code; `Tm::sem(w)(Γ, env)` lives at that
code's semantics. Variables need no cast (their code is the context's);
casts sit only where two codes must agree (an operand at a primitive's
parameter, the second branch at the first's, an argument at a callee's
parameter) and go along `Ty::equation`, data that evaluates to `refl` at two
closed codes. So §15's first risk did not materialise: no per-signature
interpreter is needed. The pin is `refl` for straight-line code, calls,
connectives, records, `foldl` and convoys, and a wrong reflection is refused
(`leaf_misreflects`).

### 16.2 A-normal form, and records by name

- **Operands are variables.** `Prim`, `Call`, `Make`, `Field`, `Fold` and
  `If`'s scrutinee name de Bruijn indices; every intermediate value is a
  `Let`. `Tm` then has no `List<Tm>` field, which the kernel route does not
  lower yet (`nested-inductives-container-fields`), and a value read twice is
  one `Let`, which is what the lowering wants anyway (a port).
- **Records are `Named(i)`.** A record type lowers to a Σ spine behind a
  nominal `sEq` tag that no surface term spells
  (`docs/inductive-tier0-lowering.md` §3.3), so a structural `Rec(fs)` code
  cannot mean the record type. The meaning instead takes a table of
  `RecInfo { T, fields, mk, get }`, as it takes a table of callee meanings,
  and `Make`/`Field` go through `mk`/`get`; at a concrete table both reduce
  to the constructor and the projections, so V2's pin is `refl` with no
  `encode`/`decode`. A record's fields are flat (words, bits, bytes): the
  table cannot refer to itself.

### 16.3 Convoys and measured recursion

- `match h: c` elaborates to the match at a convoyed motive applied to
  `refl` (`matching::plan_convoy`), which does not convert with a plain
  match. `rt` has `IfEq`, whose meaning is that convoy (`Tm::convoy`); the
  arms' equation is erased. A plain `If` is refused against a convoy
  (`safe_pred_plain_if`).
- **There is no `Measured` node.** A `decreases` function's recursive call
  is `f#rec`'s ih applied to the new arguments *and a proof* of the measure's
  decrease, which the kernel does not treat as irrelevant and the reflection
  does not carry. So a self-call reflects as `Call` of the function itself,
  answered from the table by `f`, and the body pins by `refl` against the
  body as written (`count_down_body_reflects`). The step from `body[f]` to
  `f` is the generated `f_unfold`
  (`docs/decreases-unfolding-design.md`): the measured pin is
  `refl` composed with that theorem, still generated, never hand-written.
  For a body whose test is a `match h:`, which is every native loop,
  `f_unfold` was refused at first. R5b fixed it
  (`issues/decreases-unfold-convoy-scrutinee.md`), and
  `count_down_reflects` is that composition.
  The lowering of a measured function consumes `f_unfold` and the
  obligations (`f#obl_N`) as its evidence, in R5b.

### 16.4 The host requests, and sharing

- `Body(g)`, `HLam(dom)` with `Open` on a `λ`, and `HCtor(ty, i, name,
  fields)` (constructor values, by the display's own recogniser) are as
  §3.2 proposed.
- The `match` is a request, `Arms(h)`, rather than an `HCases` head: `View`
  keeps `HMatch` for the tactics that read it. An arm is a handle to a `λ`
  over the constructor's payload, which `Open` reaches; a `match h:` lists
  its `refl` argument and its arms take the equation as a second `λ`. Only
  two-constructor matches are presented so far.
- One handle per shared subterm per scope (`Run::issue_shared`). But the
  elaborated bodies do not share let-bound values: each use is its own copy
  (`issues/elaborated-let-sharing-lost.md`). The reflector therefore numbers
  values (a node over already-bound operands is bound once), as the Rust
  reflector does, and its output is DAG-shaped either way; what remains
  exponential in an SSA chain is the number of requests it makes, until
  that issue is fixed.
- `Bytes(cap)`'s capacity is not in the type: the reflector writes
  `Bytes(0)` and the capacity becomes a setup choice (a generator argument).

### 16.5 V6: the lowering's invariant (R5b, 2026-11-01)

`lib/native/runtime/rt_lower.hthr` lowers a term, in a context of one port
per variable and from a fresh id `next`, to a structured region, the port that
holds its value, and the next fresh id. `Tm::lower_sound` states what every
case owes. Its premises: the environment holds (each port holds its
variable's encoding, a word at its width and a bit as `ofBool`) and every port
is below `next`. Its conclusion: after `StructuredRegion::eval`, `next` has
grown, every id below the old `next` is kept, and the result port holds the
encoded `Tm::sem`. The theorem is stated over the total evaluator, so
FunctionIR's `program_eval_computes` carries it to the relational semantics
the back half consumes. What V6 settled:

- **The lowering decides what the meaning casts.** Wherever the meaning reads
  a value at another code, the lowering asks `Ty::check` for the equation and
  refuses without it, and the proof carries the encoding along that equation
  (`Ty::cast_holds`). So `sound` has no `judge(p) = Ok` hypothesis. An accepted
  lowering is typed, and `judge` (§5) only reports reasons. The record in §2.1
  keeps its shape, with the hypothesis unused.
- **`Keeps` makes it compose.** A `Let` body reads its context after the bound
  term's region ran, and the two arms of a branch start from the same
  valuation. The first arm's fresh ids sit below the second's, and both move
  their result to one port above both.
- **The chain is one `Option::and_then` per check**, each continuation a named
  function where it is not recursive. The proof walks the same chain with
  `Option::and_then_elim`, which hands each step its equation (`port_at(…) =
  Some(p)`, `Ty::at(g, a) = Word(w)`). The match compiler never has to see
  inside `Tm::lower`.
- **Per program nothing is proved.** `pick_agrees` and `twice_agrees`
  instantiate the theorem at an evaluated lowering, and the meaning lands on
  the Heather function by conversion. A wrong claim and an `Add` lowered to a
  `Sub` node are both refused.

The cases to come are the remaining primitives, `Lit`, `IfEq`, records, calls
and `Fold` (§6.3's table). After them comes the `Fun` wrapper, which binds
parameters with `Valuation::bind` and reads the result with `Function::eval`.
That wrapper is §6.1's `Agrees`.

### 16.6 Round 2: primitives, convoys, calls and functions (R5b, 2026-11-02)

The second round added the cases that need no new data layout:

- **Literals and the primitive table.** A literal is a `Const` node (a bit as
  the one-bit 0 or 1). The binary primitives FunctionIR has a node for share
  one leaf lemma each per shape: a word operation at its width, a comparison
  as its bit (`bit_value_bit`), and `&&`/`||` as the bitwise node on one-bit
  words with a four-case law (`Tm::band_ofBool`). `!` is two nodes, a
  constant one and an exclusive or. `zero_extend` has no node (a `Move`
  reads the source at the wider width, which says nothing of its value), so
  it waits on `function-ir-alu-core`; the byte primitives wait on buffers.
- **`IfEq` is `If`.** It lowers to the same chain, and its meaning is the
  plain match by `Tm::convoy_match` (a case split on the bit, both arms
  `refl`). The `If` case moved into `Tm::if_sound`, which takes the two arms'
  theorems as arguments, so both nodes share one proof.
- **Calls are a hypothesis of the theorem, not of the region.** FunctionIR
  answers a `Call` from the program (`Answers`), so `Tm::LowerHolds` now
  takes `Tm::CallsAgree(w, call)`: every function whose signature is all
  64-bit words (`Sig::Words`) is answered by `call` with its meaning, read
  through `Ty::Answers` (on every word list, the curried meaning applied to
  the words cast to the parameters, cast to a word). The lowering accepts a
  call only at such a signature and with word arguments, one per parameter,
  so the case is the hypothesis at that index plus `Ty::cast_trans`. Wider
  signatures wait on `function-ir-multi-word-calls`.
- **The function wrapper is the same relation.** `Fun::lower` binds the
  parameters at ids `0, 1, …` (the context's ports are them reversed, the
  last parameter being variable 0) and lowers the body above them;
  `Fun::lower_sound` proves `Ty::Answers` of the function's curried meaning
  against `Function::eval`. So the conclusion for function `i` is the
  hypothesis a caller of `i` needs: a program discharges `CallsAgree` by
  induction over its functions, each answered by the ones before it as
  `program_eval` orders them. The proof goes through `Ty::curry_answers`
  (currying against an uncurried word function) and `Fun::bind_bound` (what
  `Valuation::bind` leaves at distinct ids).

Per program still nothing is proved: `lib/_tests/native/runtime/rt_lower_tests.hthr`
instantiates `Fun::lower_sound` at the reflector's `leaf`, `caller` and
`safe_pred` and lands on the Heather functions by conversion. A `!` lowered
against a zero constant fails the `Neg` case's proof.

What is left of N1, and what each waits on:

- **The program wrapper.** Discharging `CallsAgree` for `program_eval` needs
  the call's bound: function `i` is answered only by functions below `i`, so
  the hypothesis becomes `CallsAgree` below a bound and the lowering refuses a
  call at or above it. A self-call is not a call under N1 but a loop
  (`Measured`), and recursion through calls is N2's.
- **Records.** Done in round 3 (§16.7).
- **`Fold` and the byte primitives.** `StructuredRegion::eval` reads every
  buffer as empty (a `BufferLoad` is zero there); buffers live in
  `function_ir_state`'s run. So `Fold` needs the theorem stated over that
  semantics, with `Bytes` encoded as a buffer and a length word.

### 16.7 Round 3: records as their fields (R5b, 2026-11-02)

A record is scalar-replaced (§7.2): a variable of `Named(i)` still has one
port in the context, the port of its first field, and its fields sit at the
consecutive ports from there (`Ty::FieldsHold`). What changed to make that
sound:

- **Spans, not ports.** `Below` is typed by the context's codes: a record's
  span is below `next` when each field's port is (`Ty::Below`,
  `Ty::FieldsBelow`), and a lowering promises its result's span below its
  next fresh id, not just its first port. What a valuation keeps of a value
  is likewise its span (`Ty::Same`), so `Keeps` carries every variable,
  records included, past a region.
- **`Field` is free.** It lowers to no code: field `k`'s value is already at
  `Ty::field_port(k, p)`. `Make` moves each field variable to the fresh
  ports, and a branch with a record result moves it a field at a time
  (`Ty::moves`, proved once by `Ty::moves_sound`).
- **The record law is on the table.** `Make`'s case needs the projection of
  what it built to be its fields, so `RecInfo` gains `round: get(mk(t)) = t`.
  For a record's own constructor and fields it is `refl`: the kernel's η for
  pairs and `True` (crates/kernel/DESIGN.md) closes it, so a table entry
  costs nothing per record.
- **Fields are flat.** A record of a record is refused (`Ty::check_ones`), as
  is a field past the end (`Ty::has_field`): the meaning reads a default
  there that no port holds.

`wc_step` (rt_tests' V2, a `WcState` updated through fields, two branches,
`!`, `&&` and `Make`) lowers and agrees with the Heather function through the
theorem, and a record-valued branch does too. The probe reads the theorem off
at an abstract lowering (`wc_step_lowered` takes `r: Option<Lowered>`):
projected at the computed lowering itself, the elaborator spells the whole
lowered region inside the conclusion's type and the check does not finish
(docs/proof-patterns.md §1).


### 16.8 R5d round 1: the generator (2026-11-04)

`runtime fn f` works end to end for N1's word fragment:
`lib/native/runtime/runtime.hthr` holds the default setup, the `Compile`
class and the generator, and `lib/_tests/native/runtime/runtime_tests.hthr`
marks `calls.hthr`'s, `branches.hthr`'s and `sharing.hthr`'s functions and a
convoy, with no proof written for any of them. What the round fixed:

- **The group.** `f::rt` (the reflection), `f::world` (no records; the
  table's entry 0 is `f`, its callees after, their meanings the Heather
  functions), `f::judged` (`Fun::judge(f::rt, f::world) = Ok`, by
  evaluation), `f::reflects` (the pin, by conversion), `f::code`
  (`Setup::code`, the default lowering), `f::agrees` (`f::code` answers `f`
  wherever the table's functions are answered with their meanings, which is
  `Fun::lower_sound` read at the reflection) and `f::compile`, the
  `Compile(f)` instance. Members cannot cite each other
  (`generate-group-internal-references`), so each spells the reflection
  again; it is data.
- **The class** (§9.3's sketch, made precise):
  `class Compile<F>(f: F) { reflected, world, typed, code, agrees }`. The
  agreement is §6.1's, about `f` itself: `typed` is the equation between `F`
  and the reflection's curried type, `refl` at every instance, and `agrees`
  states `Ty::Answers` of `f` read along it. `agrees` still assumes the
  table's calls are answered (`Tm::CallsAgree`): the code answers its calls
  by table index, and the program wrapper that discharges this from the
  callees' own instances is next. `Setup::compile` builds an instance from a
  reflection, carrying `Setup::code_answers` to `f` along the pin, which the
  generator passes as `refl` and the kernel checks by conversion. The
  equation is stated as `Itself(F) = Itself(…)`: a class field naming its
  carrier as a bare term is refused at generic uses of the class
  (`class-carrier-as-term`).
- **The record of §2.1** is `Setup { name, judge, lower, sound }` over
  `Fun` and `World`; `sound` is `Fun::lower_sound`, with no judgment
  hypothesis (§16.5). `Fun::judge` reports reasons for what the lowering
  refuses (a parameter or result that is not a 64-bit word, a call of a
  function that is not, recursion, `Fold`, the byte and line primitives,
  `zero_extend`), reading the function as entry 0 of its table.
- **Callees are found by the walk.** The reflector's state carries the
  program's functions; in the generator's mode a call of a global `g` with a
  published `g::rt` appends `g` to the table. So a callee is compiled in its
  own declaration and cited by table index. A hand-written `Compile(g)`
  instance is not found this way yet: callee resolution by instance search
  (§9.2) needs `Synth` of a class at a function, which the generator cannot
  spell (a type former is not a term in an `Expr`).
- **Host changes.** `DeclForm` gains `AsInstance(class, args, index)`: a
  value also registered as `class<args…>(index…) { f := value.f, … }`,
  elaborated as that instance written in source; a function-type argument is
  spelled as an arrow so the instance is keyed as an arrow (`#Fn`). The
  host's numeral reader reads a run of successors whole, so a 64-bit literal
  a reflection quotes back is read in one step.
- **Spelling types and proofs from a generator.** An `Expr` cannot apply a
  type former, and a type read below a function type's first binder lives
  under it, so the generator reads `Ty`, `List<Ty>`, … off the types of
  witness values (`runtime_w_*`). `refl` is passed as `tactic::rfl` at an
  explicit term with its type left to a hole: the unifier does not unfold a
  reflection's meaning, while the kernel's conversion does.

Left for R5d: the program wrapper (one FunctionIR program from the callees'
instances, discharging `CallsAgree`), `compile-x86` reading `Compile(f)`,
retiring the Rust reflector (which also covers loops, which the lowering
does not yet), `heather reflect` from instances, and callees by instance
search. A module using `runtime` imports what the generator looks up
(`tactic`, `char`, `string`, `rt`, `rt_lower`, `function_ir`,
`function_ir_eval`, `runtime`).

### 16.9 R5d round 2: linking, and `compile-x86` on runtime fns (2026-11-04)

`f::agrees` no longer assumes anything: it is
`program_eval(f::program, root, [xs…]) = f(xs…)`, where `f::program` is
one FunctionIR program built from the `Compile` instances of `f` and of
every runtime fn it reaches. What the round fixed:

- **Linking is renaming.** An instance's code answers its calls by index
  into its own table (entry 0 itself, its callees after). A program numbers
  functions its own way, callees first, so each function goes in with its
  calls renamed (`Function::relabel`, `function_ir_eval.hthr`), and
  `Function::relabel_eval` proves once that a renamed code evaluates as the
  code with each call answered at its new name. Nothing else about the code
  changes; no proof unfolds it.
- **Calls are answered by meanings, not by code.** The program's calls are
  answered by a list of word functions, each function's meaning uncurried
  (`Ty::uncurry`, `Compile::uncurried`). Every world is answered by its own
  uncurried meanings (`World::calls_agree_own`, from
  `Ty::answers_uncurry`), so an instance's agreement can be read at its own
  table's meanings, with no circularity: an entry for the function itself
  is answered by its meaning too. `Compile::part` is the per-function step,
  stated over the class, so it holds for any instance, hand-written or
  generated: where the program's word functions read through the renaming
  are the table's meanings (`linked`, one equation between lists of word
  functions, checked by conversion), the code's calls fit its table and it
  takes its function's parameters (both by evaluation), the renamed code
  returns its meaning. The parts are `program_sourced`'s conjuncts, and
  `program_fit_sources` (`function_ir_eval`) turns them into the program's
  agreement. That "function `i` is answered only by functions below `i`,
  at their arity" is `program_calls_fit`, checked by evaluation; the
  lowering needs no bound. Answering calls alike (`eval_answers`) needs
  only that the calls fit, not `evaluable`'s disjointness, which is
  quadratic in a function's size: checking it for every callee made a
  caller of a dozen-arm callee run out of fuel
  (issues/runtime-fn-caller-agreement-fuel.md). `program_evaluable`
  remains what the x86 certificate needs (`eval_computes` needs the
  disjointness); it checks it through `program_scan`, one pass over each
  function, a function per declaration, and `program_scan_evaluable`
  (issues/function-ir-evaluable-quadratic.md).
- **The program.** The generator walks the tables depth first (each
  callee's table read by reflecting it again, as its own generator did) and
  places each function once, callees first, the function itself last. A
  callee's instance is its published `g::compile`, found by name (the
  name read off a view of the global); the function's own is spelled
  inline, since a group's members cannot cite each other.
- **A call's result is moved.** The x86 lowering answers a call in RAX and
  the next call does not keep RAX (it spills the other caller-saved
  registers), so two calls in a row lost the first result. `Tm::lower_call`
  now emits the `Call` and then a `Move` of its result to the next fresh
  port, as the Rust reflector's programs do; `Tm::lower_call_sound` covers
  the move.
- **A conditional names its outputs.** `branch` now takes the ports both
  arms move their result into (`moved_ports`), as a `Conditional`'s
  `outputs`. With none, the x86 planner placed each arm's result on its
  own and a nested `if` left them in different registers, which the join
  refuses; with the outputs named it picks one register for both arms.
- **`compile-x86`.** A function marked `runtime fn` compiles through its
  published program: the certificate defines its program as `f::program`
  and its `_agrees` as `f::agrees`, and the rest (placement, lowering,
  bytes, `compiled_returns`) is unchanged. An unmarked function is refused
  ("`f` is not a runtime fn: mark it `runtime fn f`…"), except where the
  Rust reflector's program has a loop or a test through a `Bool` helper,
  which the default setup does not compile yet: those stay on the Rust
  reflector until the loop round. The loop-free examples are marked
  (`branches.hthr` but its three `unequal` callers); `mix.hthr` and
  `program.hthr` became `word_mix.hthr` and `levels.hthr`, because a
  runtime fn named like its module cannot publish members
  (`runtime-fn-named-like-its-module`).

Left: `Fold` and measured recursion in the lowering, then the Rust
reflector's deletion; `Bool`-returning helpers (a call of a non-word
signature); `heather reflect` from instances; callees by instance search
rather than by `g::compile`'s name; and the imports a module using
`runtime` must write (`runtime-generator-imports`).

### 16.10 R5d round 3: loops, proved once (2026-11-05)

`lib/native/runtime/rt_loop.hthr` lowers §7.4's two recursions to one
FunctionIR `Loop` each and proves each lowering once. Nothing about a loop
is proved per program; what a program supplies is two or three equations
the generator states and proves by conversion or from the function's own
companions. `lib/_tests/native/runtime/rt_loop_tests.hthr` instantiates
both theorems at `loop_triangle.hthr`'s `sum_down` and `loop_measure.hthr`'s
`count_down`, and a step whose `+` is read as `-` is refused. What the
round settled:

- **`rt` gains a `Nat`, held in a word.** `Ty::Count` means `Nat` and holds
  as `values(64, port).toNat() = n`, so a count is always below `2^64` and a
  callee that reads its fuel as `b.toNat()` reads what the caller held.
  `Op::ToNat` makes one from a word at no cost (the word's port is the
  count's). `Tm::Case(c, zero, succ)` is a `match` on a count, its
  predecessor variable 0 in `succ`; the plain lowering refuses it, and a
  fuel recursion's body is one at the top. `Lit` at `Count` is refused (the
  encoding would need the literal below `2^64`).
- **A pass is the body in tail mode** (`Tm::lower_tail`). Every leaf either
  goes round (the flag word 0, a self-call's arguments moved to the loop's
  `next` ports) or leaves (the value moved to the first of them, the flag
  1); a branch names the flag and `next` as its outputs, so the x86 planner
  joins them in one register each. `Tm::tail_sound` states what a pass
  leaves for the loop for *any* continuation: `Tm::tail_sem`, the body with
  each self-call (entry 0, past its first `skip` arguments) answered by the
  continuation and every other result read as a word. Leaves are lowered by
  `Tm::lower` and proved by `Tm::lower_sound`, so a pass's primitives,
  calls, records and branches are the plain lowering's.
- **Fuel** (`Fun::lower_fuel`, `Fun::fuel_sound`): the loop's bound is the
  fuel's word, its state the words, and each pass first takes the
  predecessor as a word (`count - 1`), so the `Succ` arm's context (the
  predecessor, the words, the fuel at the count) holds as the plain
  lowering's invariant needs; the fuel arguments of the self-call are the
  loop's own count. The proof is `loop_eval_agrees` with each pass told its
  count is below the bound (`Fun::loop_agrees_below`): a count held as a
  word must be below `2^64`. What the function supplies is `Fun::FuelZero`
  and `Fun::FuelStep`, the two equations of its structural recursion,
  `λ x… => refl` each (§16.3's conversion, with #428's lowering at the
  top: `h(Succ(r), x…)` unfolds to the arm with `h(r, …)` at its calls).
- **Measured** (`Fun::lower_measured`, `Fun::measured_sound`): the loop is
  given `2^64 - 1` passes, a constant, and its state is the words; no
  measure is computed at run time. The passes cannot run out first, which
  the proof gets from `Fun::Guarded`: the body as written, its recursion
  answered by anything that agrees with the function where the measure is
  smaller, is the function. That is `loop_eval_agrees_measured` with the
  continuation in for "anything", and the exhausted branch (the body once
  more, its recursion answered by a junk word) is `Guarded` with nothing to
  agree on, since the measure is below one there. `Fun::Bounded` (the
  measure below `2^64`) is `BitVec::toNat_lt_pow`.
- **`Guarded` is the function's `ext` and `irrel`.** The body's tail meaning
  converts with `f::body` at an ih that drops its proof (`count_down_step`,
  `refl`), so `Guarded` is `f::ext` (the step's congruence in its ih, which
  the elaborator already generates for `f_unfold`) with the agreement it
  asks for from `f::irrel` and the hypothesis: three applications, no split,
  no tactic. The two companions now have designed spellings, `f::ext` and
  `f::irrel`, beside `f::rec` and `f::body`.

Left for the next round, in order: the `Setup` and `Compile` plumbing
(`Fun::lower` dispatching to the loops, with `Fun::LowerHolds` taking the
function's equations as a hypothesis the generator discharges); a
signature's `Count` parameters in calls (`Ty::Answers` reading a word as
`toNat` there, so a caller passes `w.toNat()`); the reflector reading a
fuel recursion's top `match` (the host's `Arms` on a `Nat` eliminator) and
a measured function's body as written (`f_unfold`'s right-hand side, with
`decreases w.toNat()` read for its measure); then `compile-x86` on the loop
examples and `crates/elab/src/function_ir_source/` deleted. `Bool` helpers
are separate: a call whose result is a `Bit` needs a word on the call's
edge (a branch on the bit to `0`/`1`, read back by a comparison).

### 16.11 R5d round 4: loops through `Setup` and `Compile` (2026-11-06)

`runtime fn` now takes the two loop shapes §16.10 proved, and `compile-x86`
compiles the loop examples through their instances; the Rust reflector no
longer compiles loops (it refuses one, naming the marker) and keeps only
tests through `Bool` helpers and `heather reflect`. What the round settled:

- **The lowering dispatches on a shape** (`RtShape`, `Fun::shape` in
  `rt_loop.hthr`). A function whose first parameter is a `Count` and whose
  body is a `Case` on it is `Fuel`; one whose body calls itself (entry 0)
  is `Measured`; anything else is `Plain`. `Fun::lower_any` lowers by the
  shape, and `Fun::Holds` is what each shape's code promises given what the
  function supplies: nothing for `Plain` (`Fun::LowerHolds`), `FuelZero`
  and `FuelStep` for a fuel, a measure with `Bounded` and `Guarded` for a
  measured loop. `Fun::lower_any_sound` is the three soundness theorems
  under one statement, and `Setup.sound` is now `f.Holds(w, lower(f, w))`,
  so a setup's soundness is over the shapes.
- **An instance per shape** (`Setup::compile`, `Setup::compile_fuel`,
  `Setup::compile_measured` in `runtime.hthr`). A plain function's instance
  rests on the pin, as before. A loop's cannot: its meaning is one step,
  which is the function only at a constructor fuel or below a bound, so its
  instance takes the shape's equations instead and builds the `rt` term from
  its pieces, which keeps the statements reducing. The generator proves the
  equations: `FuelZero` and `FuelStep` are `λ x… => refl` (with `λ r` for the
  step), and `Guarded` is three applications of the function's own
  `f::ext`, `f::irrel` and the hypothesis (`runtime_measured_instance`, for
  any arity; `rt_loop_tests`'s `count_down_guarded` was the template). A
  measured function must `decreases` a word's `toNat`: `Bounded` is
  `BitVec::toNat_lt_pow` at that word, read off `f::rec`'s bound proof.
- **A count crosses a call held in a word.** A signature's `Count`
  parameter is a word on the call's edge, read by `toNat`
  (`Ty::cast(Word(64) → Count)` is now `toNat`, `Ty::held_reads`), so
  `triangle` passes `n.toNat()` to `sum_down` and the callee's fuel is the
  word's count. A runtime fn's `f::agrees` reads its count parameters the
  same way (`sum_down::agrees(r, n, acc)` is about `sum_down(r.toNat(), …)`).
- **The reflector reads both bodies.** A fuel recursion's body is the
  kernel's `ElimNat` applied to the varied words, which `View` shows as no
  head; the host's `Arms` now opens it (the `Zero` arm the base, the `Succ`
  arm under `k` and `ih`), and `rt_reflect` reads `ih` applied to the varied
  words as `Call(0, …)` with the fuel's predecessor first. A measured
  function is reflected from `f::body` (found by `lookup`), its ih applied
  to the words and a proof read as `Call(0, words)`. `sum_down` reflects to
  §16.10's hand-written step exactly (`runtime_loop_tests`'s `sum_down_rt_is`).
- **A leaving pass writes every `next` word.** §16.10's pass moved a
  leaving value to the first `next` port only; the evaluator does not care,
  but the x86 emission meets a branch's two register files and keeps only
  what both arms hold, so the other words were lost and the loop's exit
  refused. A leaf now copies the value to the rest too (`Tm::leave_region`),
  which nothing reads. Both arms also write the flag *last*
  (`Tm::again_region` moves the arguments first): the planner gives each arm
  the join's registers (`pick_targets`) only where they are free, and with
  the flag first an arm going round could find its register still holding
  a source, put the flag elsewhere and the next word in the flag's place,
  which the meet dropped (`loop_climb`).
- **A caller's pin meets its callee before unfolding it.** The pin is
  `meaning(rt, world)(x⃗) = f(x⃗)` by conversion, and `world` holds the
  callees themselves. The kernel's δ-lazy loop unfolded the newer head
  first, so it unfolded `f`'s callee on the right before the left reached
  it through `world`, and a callee given a closed count (`loop_multiply`'s
  65, `loop_anywhere`'s 100) then unrolled on both sides into a tree with
  two recursive arms per pass. Conversion now remembers the spines it
  stepped past and meets the other side there
  (`issues/conversion-meet-past-newer-head.md`, `crates/kernel/DESIGN.md`).
- **Generated instances are held as solved holes.** A loop's instance
  abstracts locals the generator opened, and a host `Lam` reifies only at
  the scope its local was opened in, so the instance cannot be repeated
  inside `f::agrees`'s statement under its parameters. The generator solves
  a hole with it (`defeq`) and uses the hole's handle, which stands
  anywhere.
- **What the generator cites is named in `runtime`** (`Setup::Guarded`,
  `Setup::lt_succ`, `Setup::below_pow`, `Setup::eq_sym`, `Setup::eq_trans`),
  so a module marking a loop needs only `runtime-generator-imports`' list.
  `Setup::lt_succ` is a transparent `fn` returning `Nat::lt_succ_self`,
  because a `decreases` function's body passes exactly that proof to its
  recursor and the instance meets it by conversion.

Left: `Bool`-returning helpers (`branches.hthr`'s `unequal` callers still
use the Rust reflector), `heather reflect` from instances, `Fold` in the
lowering, and a `decreases` measure that is not a word's `toNat` (a count
parameter matched below the top is refused by the reflector today). The generator's cost grows with the functions a
program links ([[runtime-generator-link-cost]]): `loop_anywhere` was cut to
five functions to stay well inside the native gate's rail.

### 16.12 R5b round 4: widths and shifts (2026-11-07)

The word half of §7.1's primitive table is now in `Tm::lower_sound`:
`zero_extend`, `truncate` and the three shifts by a literal count. The byte
half (`Get`, `Set`, `Fold`) is left for the buffer round below. What the
round settled:

- **One node resizes both ways.** FunctionIR gains `Resize(from, to,
  output, source)`, whose value at every width is
  `BitVec::ofNat(values(from, source).toNat())`. At the output's width that
  is the zero extension when `to` is wider and the low bits when it is
  narrower (`BitVec::ofNat_toNat_zero_extend` and `_truncate`, by
  `ofNat_toNat`'s recursion on the width), so one equation covers both, and
  no case of the theorem compares two widths. A `Move` at the wider width
  could not do it: it reads the source *at* that width, which is unrelated
  to the source's value at its own (the negative control in
  `rt_lower_tests`, `wrong_zext_node_sound`, is exactly that lowering, and
  the kernel refuses its proof).
- **`rt` gains `Trunc(n, extra)` and `Shl`/`Lshr`/`Ashr(w, k)`.** A shift's
  count is part of the op, as FunctionIR's shift count is an immediate. The
  three shifts lower to FunctionIR's existing shift nodes and are proved by
  one lemma (`Tm::word1_node_sound`); `Zext` and `Trunc` lower to a `Resize`
  and are proved by `Tm::resize_node_sound`, whose only premise per op is
  that op's `ofNat ∘ toNat` law.
- **The reflector reads them, `<<` included**, and a width written as a sum
  (`zero_extend`'s `BitVec(extra + n)` as the type of a later operand) is
  read as its numeral by peeling successors off its head normal forms
  (`rt_number`). Before, `x.truncate(8, 56).zero_extend(56).add(x)` failed
  with "expected a numeral" on the `add`'s operand type.
- **No back end emits `Resize` or a shift yet.** S4 refuses both (it keeps
  only 64- and 1-bit values in registers, and shifts wait on
  `function-ir-x86-shift-legalization`), and the memory-resident leaf
  compiler treats `Resize` as never wide, so a program using them gets a
  refusal from `compile-x86`, not wrong code. The theorem is about the
  lowering, so this does not hold the case back.

Left for N1: the byte primitives and `Fold`. `StructuredRegion::eval` reads
every buffer as empty, so their cases need the theorem restated over
`function_ir_state`'s `run`: a `Bytes` variable held as a buffer of the
file, the plain cases carried over by `run_pure` (a region without byte
nodes runs as it evaluates), and an in-place `Set` justified by the old
buffer's variable being dead after it (`Unique`). A fold's step takes a
`Word(8)` element across a call, which wants a 64-bit word on the edge: a
`Resize(8, 64)` there now that the node exists.

### 16.13 Types held by their `datarepr`: `i64` (2026-11-08)

`i64` is `SInt(64)`, a one-field record over `BitVec(64)`
(docs/fixed-width-integers-design.md §3). Minus chose to lower it through a
`datarepr` rather than have the reflector see through one-field records
(issues/sint-native-lowering.md): the repr is the place a type says how it
is held, and the generator asks for it instead of guessing from the shape.
What landed:

- **A repr per width, from the registry.** `sint.hthr` states `datarepr
  I64 for SInt(64) { R := BitVec(64), abs := BitVec::as_signed, mk SInt :=
  λ b => b }` (and `I8`…`I32`). The datarepr elaborator now accepts a spec
  that is an inductive applied to closed value arguments
  (`valparam_spec_view`), monomorphised there and keyed by the spelled
  arguments; one repr over the telescope is
  issues/datarepr-value-parameter-telescope.md. Two host requests serve
  the generator: `Repr(ty)` answers the repr's global for a type (refused
  when it has none), and `Unfold(h)` is a global application's one-step δ
  with its arguments substituted and β-reduced at the head.
- **A repr'd type is a `Named` record whose table entry is the repr.** The
  generator reads the function's signature, asks `Repr` of each type, and
  numbers the repr'd ones; the reflector's `Known::ty` gives such a type
  `Named(recs.len() + i)`. The published world's table is `RecInfo::cons`es
  of `RecInfo::word_repr(abs, emb, round)`: type `S`, one `Word(64)` field,
  `mk` the repr's `abs`, `get` its `emb`, and `round` the repr's round trip,
  `refl` per word. The meaning therefore stays at the spec type, so the pin
  `f::rt.meaning(f::world)(xs) = f(xs)` is still a conversion node for
  node, and a reflection that misreads the repr fails it. The generator's
  own judgment and lowering read the table's shape only
  (`RecInfo::shape([Word(64)])`).
- **Operations are read through their definitions.** A global the
  reflector does not know whose result or an argument has a repr'd type
  (and which is not a field of one) is unfolded once and walked again:
  `SInt::add(a, b)` is `SInt(a.bits.add(b.bits))`, reflected as `Field`,
  `Add(64)`, `Make`. `lt_bit` arrives at `BitVec::signed_lt_bit` (`Slt`,
  `JL`) and `shift_right` at `arithmetic_shift_right` (`Ashr`, `SAR`). An
  ordinary helper over `i64` is inlined the same way; that is a
  convenience, not a promise, since the pin is what checks it.
- **The boundary passes the record in one word.** A function's parameters
  and result were `Word(64)` (`Ty::Words`); they are now `Ty::OneWord`: a
  64-bit word, or a record whose fields are `[Word(64)]`. `Ty::convert`
  reads a word at such a record as `mk` of it and the record back as its
  field, so `Ty::cast(Word(64) → Named(i))` is the repr's `abs` and the
  reverse its `emb`, by conversion at a closed table. `Fun::lower_sound`
  carries the change (`Ty::one_word_holds`, `one_word_reads`); the loop
  theorems keep `Ty::Words` and bridge (`Ty::words_one_words`). So
  `f::agrees` reads `program_eval(f::program, 0, [x, y]) =
  I64::emb(f(I64::abs()(x), I64::abs()(y)))`, which for `i64_add` converts
  to `x.add(y)`: the same words a `u64` add takes and returns.

Refused, each with its reason and issue: a call of a runtime fn with a
repr'd signature (`Sig::is_words`, issues/runtime-repr-calls.md), a loop
over repr'd words (issues/runtime-repr-loops.md), a repr'd type the
signature does not name (issues/runtime-repr-inner-types.md), a repr whose
carrier is not one 64-bit word (issues/runtime-repr-narrow-words.md). Sign
extension and signed division have no `rt` op
(issues/runtime-signed-extend-divide.md). Probes:
`lib/_tests/native/runtime/runtime_sint_tests.hthr`.
