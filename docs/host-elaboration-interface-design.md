# Host elaboration interface: Heather tactics as request trees

Design proposal for the `tac-host-interface` milestone
(`docs/roadmap.md`: "Heather code can read a goal, build a checked term, and
report failure with its search state, through one scoped host interface").
It answers `issues/host-elaboration-interface.md`, retargets
`issues/heather-checked-construction-api.md` (whose customer was burned in
B1) and places `issues/elabcode-abstraction-layer.md`. Round pattern as
usual: this document first, the implementing rounds against §10.

Status: **§0 decided by Minus on 2026-10-21** (the request-tree model, with
native tactics and certificate oracles as §8a describes). **Rounds 1, 2, 2½,
2¾, 3 and 4 landed**: §12–§16 and §19 record what building them changed.

---

## 0. The decisions

Each has a recommendation; the rest of the document argues for it.

1. **Execution model** (§2–§3). A Heather tactic is an *ordinary Heather
   value* of type `Tac<A>`: a tree of requests to the host, whose leaves are
   results. The elaborator runs the tree (evaluates to the next request,
   answers it, applies the continuation) exactly the way it already runs
   in-language analyzers (`docs/analyzer-evaluation-design.md`). The rejected
   alternative is a layer-m `meta fn` producing `Code(g ⊢ T)`; §2 says why
   that model is right for typed code generators and wrong for tactics.
2. **What a tactic sees** (§4). Terms reach Heather as a small *surface-level
   view* with host-issued handles (`Expr`), one layer at a time, never as the
   kernel's lowered forms and never as strings. Unrecognised structure stays an
   opaque handle the tactic can pass back.
3. **Shape of the request type** (§3.2). An interaction tree over a
   container, `Ask(r: Req, k: Resp(r) -> Tac<A>)`, declared locally in
   `lib/std/tactic/tactic.hthr` now, so that when `it-core` lands `Tac<A>` becomes
   that library's tree over a `Host` event container with no client change.
   Not blocked on the parallel interaction-tree thread.
4. **Invocation surface** (§7). A tactic is an ordinary `fn … → Tac<Proof>`
   and runs where a proof is expected as `by t` (or `by t(args)`). `by` is a
   new contextual keyword. The alternative is the bare-name convention of
   `omega`/`ring`, which needs per-name recognition in the elaborator and is
   what the `tactic-composition-ergonomics` issue wants to get away from.

Smaller choices made here without asking (say so if any is wrong):
continuation-passing style with a `bind` function and no do-notation in the
first round (sugar is its own surface round); handles are run-scoped
numbers the host validates; publishing new declarations is round 4, not
round 1.

---

## 1. What exists today

Four mechanisms, each the nearest prior art for one part of the interface.

- **Rust tactics write source text.** `bv_omega` writes a Heather proof as a
  string, parses it (`omega_cert::parse_generated_expr`) and checks it at the
  goal (`lib.rs`, the `bv_omega` arm); `omega` reconstruction does the same.
  `heather_emit` (`docs/generated-heather-emission-api.md`) made the *writing*
  structured, but the boundary is still render → parse → resolve names again.
  The issues' "no resolved-name string round trips" is about this.
- **Tactics are recognised by name.** `ring`, `omega`, `positivity`,
  `bv_omega`, `rel_derive` are `ExprKind::Var` arms in `elab_check`, each
  guarded by `!shadowed` and `ctor_here_expected`. There is no way for a
  library to add one.
- **Search state already has a shape.** `positivity`'s trace
  (`resolve.rs`, `TraceLine` at a depth: "omega: not imported, so not
  tried") and `SearchMark` rollback are a failure report with structure, and
  the backtracking primitive a tactic needs.
- **The elaborator can run Heather programs.** In-language analyzers
  (`lib/certgen/certgen_code.hthr`) are evaluated in the kernel's value domain by
  `Eval::force`, and `certgen.rs`'s `Reader` decodes the lowered constructor
  values back into Rust data under a fuel and a read budget. Tier-2 inductives
  (PR #88) made function-typed recursive fields writable, so a value can now
  *carry a continuation*.

And one mechanism this design deliberately does not build on for tactics:
**layer-m `meta fn`s over `Code`**, with slots
(`docs/meta-def-registration-design.md`), `match code` analysis over
`TyCode`, and the pull reflection API (`docs/fn-signature-reflection-design.md`).

---

## 2. Why tactics are not layer-m code generators

The modal layer is the project's thesis and stays the home of *typed*
generators: a `vec.map` template has a type every instance shares, so
`Code(g ⊢ (A: Type<0>) -> … -> [B; k])` is a real specification, and the
kernel's layer discipline is what makes it one. A tactic is the opposite case.
Its input is an arbitrary goal and its output is a proof *of that goal*, so the
type it would want is `(T: TyCode(g)) -> Option(Code(g ⊢ El T))`, and four of
the meta layer's documented limits land on exactly that:

1. **The result type mentions the input.** A code type is indexed only by
   globals, never by a Π-bound local (`docs/in-language-map-design.md` §3),
   and there is no dependent motive over code. A goal-generic `Code(g ⊢ goal)`
   is not a type we can write.
2. **No generation-time oracle** (blocker (2) of
   `issues/generators-in-the-language.md`): no whnf, no conversion, no
   unification at layer m. Every useful tactic asks "is this hypothesis the
   goal up to definitional equality?".
3. **No code equality** (blocker (3)).
4. **The kernel view is the lowered one.** `match code` sees `Wf`/`W`
   encodings and treats globals as opaque neutrals (the opaque-globals round
   lifts this per name, at the boundary, for one fragment). A tactic reading
   `xs.len() = n` needs `List::len` and `Eq`, not their encodings.

What tactics need instead is a *conversation* with the elaborator: ask a
question, get an answer, decide. Every answer is checked later anyway: the
proof a tactic returns is elaborated against the goal and re-checked by the
kernel gate. So the tactic's own typing can be plain data typing, and the
guarantee comes from checking the output, which is the same split the
analyzers already use (they return `Ir` data; Rust checks what is emitted).

The ElabCode issue said the same thing from the other side: most
metaprograms should not touch raw `Code`; they should manipulate a friendly
reflected AST as ordinary data, with a translation to the real thing that is
what gets checked. `Expr` (§4) is that AST for tactics, and the host's
elaboration of a returned `Expr` against the goal is the translation.

---

## 3. The model: a tactic is a tree of host requests

### 3.1 Running a tactic

```
tactic value  ──eval──▶  Pure(proof)                 → host elaborates proof at the goal
                   └──▶  Ask(r, k) ──host answers a──▶ eval k(a) ──▶ …
                   └──▶  Ask(Fail(msg, notes), _)    → the invocation fails with the notes
```

The host loop is small and lives in a new `crates/elab/src/host.rs`:
evaluate the tree to weak head (value domain, `Eval::force`, one fuel
budget for the whole run), decode `Pure`/`Ask` and the request's fields with
the analyzer reader's decoding, perform the request against the current
`Cx`, build the answer as a closed constructor term, apply `k` to it as a
pending `Elim::App` (the `global_app1` shape, so nothing is read back into
syntax and re-evaluated), repeat. A request budget bounds the conversation
independently of fuel.

### 3.2 The request type is a container

```heather
// lib/std/tactic/tactic.hthr (round 1 subset)
inductive Req {
    Goal,                         // the goal and its local context
    View(e: Expr),                // one layer of a term (§4)
    Defeq(a: Expr, b: Expr),      // definitional equality at the goal's context
    Fail(msg: String, notes: List<Note>),
}
fn Resp(r: Req) → Type {
    match r { Goal => GoalInfo, View(e) => Head, Defeq(a, b) => Bool, Fail(m, n) => Empty }
}
inductive Tac<A> { Pure(a: A), Ask(r: Req, k: Resp(r) → Tac<A>) }
```

The answer type depends on the request, which is what makes this an
interaction tree over a container (`Req`, `Resp`), and is exactly the shape
the `it-function-fields` milestone made writable
(`crates/elab/tests/inductive_tier2.rs`'s `Vis(c: Cmd, k: Resp(c) -> Tree)`).
`Fail` answers in `Empty`, so a failure has no continuation by type.

Why a local type and not the interaction-tree library's: `it-core` is being
written in parallel, and the host only needs the tree's two constructors.
The local declaration is shaped so that the switch is a rename: `Req`/`Resp`
become a `Host` event container, `Tac<A>` becomes `ITree<Host, A>`, and
`bind`/`iter` come from the library. Tactics written against `bind` and the
request helpers (`goal()`, `defeq(a, b)`, `fail(msg, notes)`) do not change.

### 3.3 What this buys the host-interface issue

- **Capability, not ambient access.** A tactic touches the elaborator only
  by asking; between requests it is a pure function. "Access to the current
  environment is an explicit host context/capability" is true by
  construction: the tree *is* the capability's uses, in order.
- **Imported definitions vs the active host.** Importing `lib/std/tactic`
  imports the *protocol* (types and helpers), never an implementation. The
  implementation that answers is the elaborator running the build, pinned for
  it. A later Heather implementation is a *handler*: a Heather function from
  `Tac<A>` and a model of the environment to a result. Handlers over a
  recorded transcript or a mock goal are the first such (§9's probe already
  runs one by `refl`), and they are also how a tactic gets a correctness
  theorem one day.
- **Identity and correctness are separate.** Which implementation answered
  is the build's identity; whether the proof is right is the kernel's
  answer to the returned term. The design never asks the first to vouch for
  the second.

---

## 4. Terms as Heather sees them

### 4.1 Handles and views

A tactic never holds a kernel term. It holds an `Expr`, which is either a
host **handle** to a term the host has (`Hd(h)`) or structure the tactic built
itself:

```heather
record Handle { id: Nat }         // run-scoped; the host validates every id
record GlobalRef { id: Nat }      // a resolved global, typed by the host
record LocalRef { id: Nat }       // a local of the goal's context (or one the tactic introduced)
inductive Expr {
    Hd(h: Handle),
    Global(g: GlobalRef),
    Local(x: LocalRef),
    App(f: Expr, a: Expr),
    NatLit(n: Nat),
    Hole,                          // left for the host to infer, `_` in source
}
```

`View(e)` returns one layer as a `Head`, whose children are handles again:

```heather
inductive Head {
    HGlobal(g: GlobalRef, name: String, args: List<Handle>),   // `List::len(xs)`, `Eq(A, a, b)`
    HLocal(x: LocalRef, name: String, args: List<Handle>),
    HPi(name: String, dom: Handle, body: Handle),
    HLit(n: Nat),
    HOther,                                                     // a form the view does not present
}
```

Three properties:

- **Lazy.** A goal is not reflected; its head is. A tactic that only compares
  the goal with each hypothesis never asks for a view at all (§5's
  `assumption`). This is what keeps a large goal from becoming a large Heather
  value.
- **Surface level.** The view is computed by the same recognition the
  speller uses for diagnostics (`display.rs`'s decode + `spell_type`), made to
  return structure instead of text: a lowered `Eq` is `HGlobal(Eq, …)`, a
  record type is its name. Factoring the speller's recogniser so both the
  string speller and the view consume it is part of round 1 (§10).
- **Never a string round trip.** `GlobalRef`s come from views and from
  `Resolve` (round 2); the host maps them back to the global it already
  resolved. `name` fields are for messages and for tactics that key on a
  name; nothing re-parses them.

### 4.2 Binders and hygiene

Building under a binder is the meta layer's hard case (ElabCode's "the hard
case is BINDERS"). Here it is a host request: `Intro(name)` (round 2) asks the
host to introduce the goal's binder, answers a fresh `LocalRef` and moves the
goal; the eventual `Expr` mentions that ref, and the host abstracts it when
it reifies the proof. Refs are host-issued and never reused within a run, so
capture cannot happen, and the tactic never computes a de Bruijn index.

Names the *tactic's own source* mentions (`Eq::refl`, a lemma) resolve in
the tactic's module, at its definition, the ordinary way; names the
*caller* means come through the goal, its context, or an explicit
`Resolve(name)` against the invocation site's scope. The two scopes are
different requests, so the hygiene rule is visible in the protocol.

### 4.3 Provenance

Every handle the host hands out remembers where its term came from (the goal,
a hypothesis, an elaboration of tactic output at a span). Diagnostics about a
term the tactic built point at the `by t` site and name the tactic; a term the
user wrote keeps its own span.

---

## 5. Producing a proof

The tactic's result is an `Expr`. The host elaborates it **against the goal**
through the ordinary checker (`elab_check` on a syntax tree whose leaves are
pre-resolved: a new `ExprKind` leaf carrying a host term, so handles and refs
skip name resolution), then the enclosing declaration reaches the kernel gate
as usual. So:

- implicit arguments, numerals and coercions in a built term are the
  elaborator's ordinary inference (`Hole` asks for it explicitly);
- a wrong proof is an elaboration error at the `by` site, prefixed with the
  tactic's name, never a kernel surprise;
- **typing is not semantics.** A checked proof establishes the goal; it
  does not establish that the tactic implements any particular strategy, and
  moving a tactic into Heather does not prove it correct. A correctness
  theorem for a tactic is a separate artifact over a Heather handler (§3.3),
  stated against the protocol, and is not part of this milestone.

The first customer, as a sketch of what writing one looks like:

```heather
fn assumption() → Tac<Expr> {
    goal().bind(λ g => try_each(g.target, g.locals, Nil))
}
fn try_each(target: Handle, ls: List<LocalInfo>, tried: List<Note>) → Tac<Expr> {
    match ls {
        Nil => fail("no hypothesis matches the goal", tried),
        Cons(l, rest) => defeq(Hd(l.ty), Hd(target)).bind(λ same => match same {
            True => Pure(Local(l.ref)),
            False => try_each(target, rest, Cons(Tried(l.name, "not the goal"), tried)),
        }),
    }
}
```

---

## 6. Failure with its search state

`Fail(msg, notes)` ends the run. `Note` is structured, not prose:

```heather
inductive Note {
    Tried(what: String, verdict: String),     // the positivity trace's line
    At(e: Expr, note: Note),                  // about a term; the host spells it
    Nested(label: String, notes: List<Note>), // a sub-search, indented
}
```

The host renders notes the way `positivity` renders its trace (one line per
attempt, nested by depth, terms spelled by the speller), so the report a
Heather tactic gives reads like the ones Rust tactics give today.

Recoverable failure is separate from ending the run: round 2's
`Check(e, ty)` and `Attempt` answer a `Result`, rolling the elaborator back
with `SearchMark` on the failure side, so a tactic can try one thing, look
at why it failed, and try another. That is the "alternation leaf (try refl,
else bv_omega)" the composition issue's 2026-10-01 customer wanted, written
as a Heather function instead of syntax.

---

## 7. Invocation

```heather
import tactic;
import my_tactics;

theorem t(p: P, q: Q): Q { by assumption }
theorem u(…): … { by rewrite_with(h) }
```

`by e` in a proof position elaborates `e` at type `Tac<Proof>` for some
`Proof` (round 1: `Tac<Expr>`), runs it (§3.1), and checks the result at the
expected type. `by` is a contextual keyword, so no library needs to be
recognised by name and a local cannot shadow the mechanism. Existing
name-recognised tactics are unaffected; giving them `by` spellings is the
composition issue's job once some of them live in Heather.

---

## 8. Cost and budgets

- **Evaluation** is the analyzer path (value domain, environments not copies,
  annotations never traversed), so a tactic pays per request and per force,
  not per term size. A run has one fuel budget, one request budget and one
  decode budget, each declining loudly (CLAUDE.md's runaway discipline: the
  value is produced by library code and may be arbitrarily wrong).
- **Requests** cost what the Rust tactics already pay: `Defeq` is
  `Tc::conv_ty` at the goal's context, `View` is one decode plus one
  recognition step.
- `Whnf` (round 2) answers a **handle**, and `View` presents one layer of it.
  Nothing in the protocol spells a reduct as text, and the host's rendering
  of `Note`s spells only terms a tactic chose to show, never a whnf on an
  error path (the rule `issues/wp-obligation-tactic.md` repeats: computed
  native obligations are the case where spelling one costs gigabytes).
- Nothing here adds an inference route to a hot path: `by` is only entered
  when written.

---

## 8a. Execution tiers, oracles and outside integration

The request tree fixes a **protocol**: what a tactic may ask and what comes
back. It does not fix *who runs the tactic's own code*, and soundness never
depends on that, because every result is elaborated against the goal and
re-checked by the kernel. So a tactic is untrusted however it runs, and three
ways of running one share the protocol:

1. **Interpreted Heather** (R1). The tree is evaluated as §3.1 says. Each step
   costs an evaluator force, so this suits strategy, composition and glue,
   not hot loops. It is the tier you can prove theorems about directly.
2. **Native protocol speakers.** A Rust tactic implements the same protocol
   as a coroutine: it yields a `Req` and resumes with the `Resp`. The host
   loop drives both kinds alike. Two consequences follow. Existing Rust
   tactics (`omega`, `ring`, `split_all`) can be wrapped as protocol speakers,
   so a Heather `first_of` composes them with Heather tactics. And an
   **outside process** speaks it over a serialised `Req`/`Resp` stream: the
   data types are first-order apart from the continuation, which stays on the
   speaker's side. R1 ships the Rust trait beside the interpreter, so a
   native tactic works from the start.
3. **Compiled Heather.** Later, the native compiler compiles a Heather
   tactic to machine code. You keep the source as the thing to reason
   about and gain native speed, and no tactic changes.

**Certificates: native search, checked in Heather.** For expensive search,
the split is an untrusted **oracle** plus a checker. A request
`Oracle(name, input)` calls a registered native procedure (in-process, or an
outside tool such as a SAT/SMT solver or a CAS) and answers with certificate
*data*; the Heather side then checks it in one of two ways:

- **by reflection**: a Heather checker `check(input, cert) = true` proved
  sound once, its run discharged by evaluation (`decide`-style). The proof
  term stays small, and the cost is kernel evaluation of the check. SAT with
  DRAT-style traces, linear-arithmetic witnesses and ring certificates fit;
- **by reconstruction**: the tactic builds a proof term from the
  certificate and the host elaborates it, which is what `omega` does today
  in Rust.

An oracle is never trusted, only the check is. That is the same stance as
the rest of the design, and it is what makes outside integration safe to
add. The oracle registry (which names exist, how outside tools are launched
and pinned for a build) is part of the build's identity (§3.3), never of
correctness.

**Where the work should live.** Search and normalisation go in native code,
as oracles or as native protocol speakers. Strategy and the last step of a
proof go in Heather. Compiling Heather tactics later removes most of the
interpretation cost without moving that line.

---

## 9. Probe (in this round)

`crates/elab/tests/tactic_request_tree.rs` checks that the protocol is
writable and computes in today's surface, without any host: the `Req`/`Resp`
container, the generic `Tac<A>` with its `bind`, a two-request tactic, and a
**Heather handler** that answers from a mock goal, with closed runs proved by
`refl`, an open-continuation run, and a negative control. This is the
"Heather implementation of the host" in miniature, and it is the check that
§0.3's choice does not wait on anything.

One thing the probe taught, which shapes how handlers are written: a `match`
on the request *inside* the handler does not refine the continuation's domain
(`k: Resp(r) -> Tac<A>` stays at `Resp(r)` in the `Goal` arm), so the arm
cannot apply `k` to a `GoalInfo`. The dependent answer is instead computed by
a function whose result type is the request's own,
`reply(r: Req) -> Reply<Resp(r)>` with `Reply<R> = Stop(code) | Give(a: R)`,
and the handler matches on `reply(r)`. The Rust host does not care (it builds
the answer term directly); a Heather handler, including the one a tactic's
correctness theorem would be stated over, uses this pattern until match gains
the generalisation.

---

## 10. Rounds

| round | builds | done when |
|---|---|---|
| R1 (landed) | `lib/std/tactic/tactic.hthr` (protocol, `bind`, helpers), `host.rs` loop, `by`, requests `Goal`/`Defeq`/`Fail`, the Rust protocol-speaker trait (§8a) | `by assumption` closes goals at open types and neutral hypotheses, and its failure lists every hypothesis tried |
| R2 (landed) | `Open` (the design's `Intro`), `Infer`, `Resolve`, `Lam` in `Expr`, binder scopes in the host; quoting the goal's terms into `Expr` arguments; `focus`, `attempt`, `first_of`, `exact`, `intro`, `apply` in Heather (§13) | a Heather `apply` closes an implication chain; a failed `first_of` reports each branch |
| R2½ (landed) | `View` on the speller's recognisers (moved from R1 and R2), `Whnf`, `Match`; `apply` solves what its conclusion determines (§14) | a Heather tactic dispatches on the goal's head; `apply(sym, assumption())` closes `b = a` |
| R2¾ (landed) | `Hole` with `Mark`/`Restore`, `GlobalRef` (`Lookup`, `Global`, `HGlobal`'s reference), `At` notes rendered by the host (§15) | `apply(trans, assumption())` closes `a = c`; a failed alternative's solutions are forgotten |
| R3 (landed) | `tac-first-port`: `split_all` in Heather on the split requests `Cases`/`Constructor`/`Close` and `View`'s `HMatch`, with `reflexivity` as its leaf (§16) | it closes the same goals as the Rust one on the existing tests |
| R3½ | `Oracle(name, input)` with one registered native procedure and a reflection-checked certificate (§8a) | a goal closes by native search plus a Heather check whose proof term is small |
| R4 (landed) | publication (`heather-checked-construction-api`, retargeted): a `generate g(args);` item running a `Tac<List<Decl>>`, requests `Assume`/`Ctors`/`AsType`/`Publish`, `Expr`'s `Blank`/`Pi`/`Equation`; the group is checked and published only if every member passes (§19) | a Heather generator publishes a lemma group in the caller's scope; a failing member publishes nothing |

R1 tests follow `docs/testing-generated-terms.md`'s axes: a closed and a
neutral hypothesis, an open element type, a checking position (the goal comes
from an expected type, not only a statement), and negative controls (no
match; a tactic that returns a wrong proof is refused at the `by` site; a
forged handle is refused).

---

## 11. Rejected alternatives

- **Layer-m `meta fn` tactics over `Code`** (§2). Kept for typed generators.
- **Full reflection of kernel terms into a Heather `Term` type.** It would
  expose `Wf`/`W` encodings, copy whole goals into values, and need a
  Heather mirror of every kernel former. The lazy surface view gives tactics
  what they use.
- **Strings across the boundary** (render, parse, resolve again). This is
  what the issues ask to remove, and it loses typed references and
  provenance.
- **A Rust tactic trait first, Heather later.** Cheaper for one round, but
  the milestone is about Heather code, and the Rust-side shape would be
  fixed by Rust's needs. (Native tactics are not rejected: §8a makes them
  speakers of the same protocol.)
- **An effect-system or monad-transformer `TacticM`.** Heather has no
  effects; a request tree is the pure encoding of one, and it is the same
  object the interaction-tree area is building.
- **Waiting for `it-core`.** The host needs two constructors; §3.2's local
  type keeps the protocol identical to the library's tree.

---

## 12. What round 1 changed

Recorded after building it, as the inductive-tier designs do.

- **`View` moved to R2.** `assumption` needs only `Goal` and `Defeq`, and the
  speller's recogniser is a refactor of its own. Round 1's `Expr` has no
  `Global` constructor yet for the same reason: a tactic builds terms from
  locals, literals and applications.
- **The host never decodes `Tac`'s encoding by hand** (§3.1 said it would
  reuse the analyzer reader's decoding). Every question is an application of
  one of the library's `host_*` functions, read back as a numeral, an `Expr`
  or a `String`, and every answer is built by the library's builders
  (`host_goal`, `host_goal_local`, `host_bool`, `str_push`). The tier-2 tree's
  lowering stays the elaborator's business, and the protocol's definition is
  all Heather. `host_resume` uses §9's `reply` pattern (`fit`).
- **Answers are built in the value domain, not elaborated from text**: a
  string literal elaborated in the caller's scope would need the caller to
  import `char`, which is exactly the scope leak §4.2 forbids.
- **Round 1 runs closed trees.** `by t(h)` with an argument naming a local is
  refused with a message; the tactic reaches locals through `Goal`. Lifting
  this (evaluating under the goal's context) is R2's.
- **The returned `Expr` is reified straight to a kernel term** (locals and
  literals are terms, an application is formed against its head's Π after a
  conversion check), not elaborated through a pre-resolved syntax leaf as §5
  proposed. Nothing is resolved by name. `Hole` waits for the elaboration
  route, with `View` in R2.
- **Cost, found and fixed in the kernel.** The first runs used tens of MB per
  request: every `elim_W` step rebuilt its recursive eliminator by shifting
  the whole step (a `match`'s every arm), and a tier-2 tree pays one per
  `match`. `ValueArena` now memoizes that syntax by the identity of the
  eliminator's bodies (`fire_elim_w`, `WIhSyntax`); a request costs tens of
  microseconds and a few hundred requests run in well under a second.
  The memo only shared a copy between recursions at the same depth, and a
  handler such as `focus` or `bind` recurses one level deeper per request,
  so every request still paid one copy per handler layer: tens of
  milliseconds a request in round 3's `split_all`. Since 2026-10-23 the
  evaluator holds the ih as a value (`Val::WIh`) and builds no syntax for it
  at all (`issues/tactic-strategy-step-cost.md`).
- **A run was limited to about a thousand requests** (fixed 2026-10-21).
  A `match` on a tier-2 tree rebuilds the continuation over the scrutinee's
  proof, so each resumed tree's proof was the previous one's applied, and the
  final `Pure` leaf's `J` forced the whole chain at once, one evaluator level
  per earlier request, into `NATIVE_DEPTH_LIMIT`. The host now forces both
  components of each resumed tree and holds them as values
  (`Interpreted::pin`), so the chain stays one link long and the request
  budget is the only bound (`issues/tactic-run-continuation-chain.md`).
  What remains is a cost of the tactic's own shape: binds nested to the
  left are exponential in their depth (`issues/tier2-left-nested-bind-cost.md`),
  so a loop should recurse in the continuation, `step.bind(λ _ => loop(j))`.

---

## 13. What round 2 changed

- **`Open` instead of a goal-moving `Intro`.** `Open(h, name)` introduces the
  binder of *any* function-type handle and answers the new local and the
  body; it does not change "the goal". The goal a sub-tactic sees is set by
  a library handler, `focus(g, t)`, which answers `t`'s `Goal` requests with
  `g` and passes everything else on. `intro(t)` is `Open` on the target,
  `focus` on the body, and `Lam(x, e)` around the result; `apply` uses
  `Open` to reach a premise's type. So the host has no goal stack, and
  subgoals are ordinary values.
- **Scopes, not a goal stack, in the host.** Every handle and local belongs
  to a scope (the goal's context, or a binder `Open` introduced under its
  parent's scope). An `Expr` is elaborated at the deepest scope it mentions;
  handles from enclosing scopes are weakened into it, and two scopes neither
  of which encloses the other are refused (a local used outside its
  binder). `Lam(x, b)` must sit exactly at `x`'s parent scope. These are
  protocol errors and end the run, like a forged handle.
- **Recoverable failure is a library handler, not host rollback.** §6
  planned `Check`/`Attempt` with `SearchMark` rollback. Every request is
  free of side effects on the elaborator (conversion is the kernel's, and
  answers create only handles and scopes the run owns), so `attempt(t)` is a
  Heather function that turns `t`'s `Fail` into a value, and `first_of`
  is built on it. `Resolve` is the one request that elaborates, and it rolls
  itself back when it fails. `Infer` and `Open` answer `Checked<…>`
  (`Accepted`/`Refused(why)`), so a tactic can act on why an `Expr` was
  ill-typed.
- **Tactic arguments mention locals by quotation.** While the tactic
  expression is elaborated, a position that expects an `Expr` and is given a
  term of another type takes a handle to that term (`by exact(h)`,
  `by apply(h2, apply(h1, assumption()))`). Checking alone cannot tell the
  two apart, because it defers a mismatch to the kernel, so the term's type
  is inferred on a clone first. The quoted term becomes a closed
  `host_quote(n)`, so the tactic value is still closed and evaluated as in
  round 1; any other mention of a local is refused. A term of the tactic
  expression's own binders cannot be quoted.
- **`Note` is flat.** Nested inductives are not supported
  (`nested-inductives-container-fields`), so §6's `Nested(label, notes)` is
  `Under(n: Note)`: a sub-search's notes are each wrapped once per level.
  `first_of` reports each alternative as `tried an alternative: <its
  failure>` with that alternative's notes beneath it. `At(e, note)` waits
  for `View`'s speller.
- **`apply` proves premises eagerly.** It compares the function's type with
  the goal, and otherwise opens the next premise, proves it with the premise
  tactic at the premise's type, and continues with the applied function's
  inferred type. A later premise may depend on an earlier proof. There is
  no unification: a premise is never left for the conclusion to determine,
  which waits for `Hole`.
- **Still not here:** `View`, `Whnf` and `Hole` (R2½ above); they share the
  speller refactor and are only needed by tactics that dispatch on a goal's
  shape.

---

## 14. What round 2½ changed

- **`View` shares the speller's recognisers, not its string building.** The
  call recogniser (`Speller::call_parts`: an application spine as a named
  global, a local or a record field, and how each argument is shown) is
  now one function that the string speller's `call` and the host's `View`
  both consume; an inductive instance is recognised by the same
  `display_tag_of`/`display_targs` the speller uses, and a registered
  lowering is unspelled first, as there. The rest of the speller (budgets,
  fallbacks, source spelling) is presentation and stays where it is.
  `Head` is `HPi(dom)`, `HEq(lhs, rhs)`, `HGlobal(name, args)`,
  `HLocal(x, args)`, `HLit(n)` or `HOther`; arguments are the ones a
  diagnostic writes, implicit ones left out. `Succ(p)` is a `HGlobal`,
  because it is what `Whnf` leaves of a numeral sum. No `GlobalRef` yet:
  a tactic keys on the name and uses `Resolve` for the term.
- **`Match` instead of `Hole`.** What `apply` needed from unification is
  "which of `f`'s parameters does matching its conclusion against the goal
  determine". `Match(ty, target)` answers exactly that: for the fewest
  leading parameters that work, it makes them metavariables of a scratch
  world (the same representation implicit application uses), runs the
  elaborator's unifier (`unify_root`), and accepts when the conclusion
  with the solutions substituted mentions no unsolved parameter and
  converts to the target. Each parameter comes back as a handle to its
  value or as open. `apply` fills the solved ones and proves the open ones
  with its premise tactic, left to right; the host checks the application
  as it checks every `Expr`, so a wrong solution is a refusal, not a
  soundness question. A parameter only a later premise determines
  (`trans`'s middle point) is still proved before that premise is seen:
  metavariables shared across premises are what `Hole` would add, and no
  tactic needs it yet.
- **Globals are quoted as themselves.** `by apply(sym, …)` hands the
  tactic `sym` with its whole type, implicit parameters still binders, so
  `Match` can solve them. Inferring a bare reference would insert them.
  `Resolve` does the same for a name that is not a local.
- **Still not here:** `Hole` (above), `At(e, note)` (a note about a term,
  spelled by the host), and `GlobalRef`.

---

## 15. What round 2¾ changed

- **Holes are metavariables of the run, in the unifier's own form.**
  `Hole(ty)` answers a handle to a new metavariable at `ty`'s scope. A run
  with `m` holes lives in Ψ extended by `m` bindings, newest innermost:
  exactly the scratch world implicit application uses
  (`unification.rs`), so the elaborator's unifier works on the run's terms
  unchanged. Each handle records how many holes existed when it was issued
  and is shifted on use, and a hole's occurrence is a `GlobalTm` with its
  home scope's identity substitution, weakened like any term. Solutions are
  committed-world terms scoped in the home's context.
- **The kernel never sees a hole.** Every request zonks first. A committed
  term goes through the existing code; one that still mentions an unsolved
  hole gets only what its structure answers: `View` gives `HHole` for an
  unsolved hole itself and `HPi`/`HEq` from a syntactic former; `Open`
  needs a syntactic Π (and its body's scope then has a hole in its context,
  so kernel requests there wait until it is solved); `Whnf` and `Match`
  refuse. A run's result must zonk completely, or it is refused with the
  holes spelled `?1`, `?2`, ….
- **The comparing requests solve holes.** `Defeq`, and the domain check of
  every application an `Expr` builds, compare a side that mentions unsolved
  holes with a committed one by the unifier, and keep the solutions only if
  the solved side then converts; a failed comparison solves nothing. Two
  sides that both mention unsolved holes are not equal for now.
- **A hole made under fewer binders is unified at its home.** The unifier
  solves a metavariable whose occurrence is the identity of its context,
  while a hole used under a binder `Open` introduced occurs weakened. So a
  comparison unifies one home scope at a time, at that scope, with the
  deeper scope's locals as binders already crossed (`unify_under`): a
  solution mentioning one of them does not strengthen to the home and is
  not learned. Other homes' holes are withheld meanwhile.
- **Requests now have one side effect, and `attempt` undoes it.** §13's
  "requests are side-effect free" held until solutions existed. Rather than
  roll back inside the host, `Mark` answers the current position of the
  run's solution trail and `Restore(m)` forgets every solution after it, so
  `attempt` stays a Heather handler: it marks before running its tactic and
  restores when the tactic fails. `first_of` inherits it.
- **`apply` postpones what a premise determines.** `Opened` now says
  whether the body mentions the new local. An open slot that is depended on
  becomes a hole and the premises after it are proved with the hole in
  their types, so proving `trans`'s first premise solves the middle point;
  a hole still open after the premises is proved last at its type and the
  proof compared with it. `assumption` commits to the first local that
  fits, so a wrong first fit is not revisited (Lean's `apply` behaves the
  same way); a searching premise tactic is the client's choice.
- **`GlobalRef` is an identity.** References are interned per run, by Ψ
  index, inductive tag, or builtin former (`Nat`, `Succ`, `True`), so
  `HGlobal(g, name, args)` from `View` and `Lookup(name)` agree and a tactic
  compares heads by number. `Global(g)` in an `Expr` is that global as a
  term with its whole type, as quoting gives it; a type or a former is
  refused there.
- **The host renders notes.** `At(e, note)` needs the diagnostics' speller,
  so a failure's notes are read structurally (one `host_note` at a time)
  and rendered in Rust, in the same layout the library's renderer used.
  An `At` term with unsolved holes is spelled with the `?n` names.
- **Still not here:** comparing two sides that both mention unsolved holes
  (no tactic needs it yet), `Hole` under `Match` (a target with holes is
  refused), and backtracking `apply` over premise alternatives.

## 16. What round 3 changed

- **`split_all` is a Heather tactic; the case split is the host's.**
  `lib/std/tactic/tactic.hthr`'s `split_all(leaf)` closes the ten goals of
  `crates/elab/tests/goal_combinators.rs` (`tactic_split_all.rs`, with
  `reflexivity()` as the leaf). The strategy is Heather: split every local
  of a finite type, introduce binders and split the finite ones, prove `And`
  one side at a time, and split an equation on the `match` one of its sides
  is stuck on, deepest first (`blocker`: a call's arguments, then its head
  normal form's `HMatch` scrutinee, then that scrutinee's own blocker). The
  split itself is a request, because it is the elaborator's: `Cases(e,
  goal)` answers one branch per constructor of `e`'s type, each with its
  new locals (the fields and the equation `e = C(fields)`) and its goal.
- **A split is built from source syntax, twice.** A branch's context and
  statement are whatever the elaborator's own `match` gives its arm, so the
  host does not compute them: it elaborates a skeleton (the `match`, or the
  anonymous constructor for `Constructor`) whose leaves are unwritable
  markers that record their context and expected type, and makes each a
  branch scope. `Close(split, proofs)` checks each proof at its branch's goal
  and elaborates the skeleton again with the proofs at the leaves, so the
  split's proof is exactly what that `match` written in source would be.
  The recording run happens twice with different placeholders, and a
  branch whose statement changes between them (a dependent field, `{ n,
  p: n = 0 }`) is refused rather than stated about a placeholder.
- **The motive is `split_all`'s.** `Cases` abstracts the scrutinee out of
  the goal together with every position that reaches it only through a
  definition (`goal_combinators::co_occurrences`), so `either(p) = (p.left
  || p.right)` splits both sides on `p.left` at once. A goal that does not
  mention the scrutinee is every branch's goal.
- **Branches are scopes with several locals, and siblings.** A scope now
  carries the ids of every local it adds, so a branch's fields and equation
  are ordinary locals (`Lam` still abstracts only a scope that adds exactly
  one). Two branches are siblings: a handle from one is refused in the other,
  which is the binder discipline of §13 applied to arms.
- **`HMatch(scrut)`** is the view of a term whose head (below projections)
  is a `match` or a Nat recursion, with its scrutinee as a handle; `Whnf`
  plus `View` is how a tactic finds what blocks a term.
- **What stays in Rust.** The word-comparison bridge of the Rust
  `split_all` (stating `bitvec_omega` Nat facts in each arm) and its
  restatement of hypotheses an earlier split simplified are not ported:
  both are reading arithmetic, which §8a puts in native code. The Rust
  combinator stays the one `split_all; all_goals { … }` uses.
- **Cost.** The host's answers are cheap; evaluating the tactic between
  requests dominates: for strategy code, forcing the resumed tree's next
  node costs orders of magnitude more than a request in a tight loop does
  (issues/tactic-strategy-step-cost.md). A `split_all` over two booleans
  makes a few hundred requests.


## 17. A block's `let`s are the goal's locals (2026-10-27)

- **What was missing.** `Goal` listed the goal's Γ, and a block `let` is not
  in Γ: the elaborator keeps it as an alias and inlines its value at every
  use (`context::Alias`). So a fact bound by `let step: (e <= t) = …;` was
  no hypothesis to `assumption` or `mono`, which had to be handed it
  (issues/tactic-goal-lists-block-lets.md).
- **A `let` is a local with a value.** The run issues each `let` whose name
  still means it at the goal (no later binder or `let` of that name; written,
  not a `#` name) as a local, with handles to its value and its statement,
  both scoped at the goal. `Goal` lists them between the binders they were
  bound among, most recent first. Their ids follow the goal's binders and
  precede every local the tactic opens or a split adds.
- **`Local(x)` of a `let` is its value**, exactly what the name means in
  source, so conversion sees through it: a goal in which the elaborator has
  already inlined the `let` still matches. `Lam` refuses one (it bound
  nothing to abstract).
- **Splicing.** A `let` the returned `Expr` names outright is recorded as
  spliced, since its value is then in the proof the kernel checks. One reached
  only through a handle (an `Infer` of an `Expr` that named it) is not
  recorded, and its block still hands its value to the kernel
  (let-and-blocks-design §11): at worst a redundant check, never a missed one.

## 18. What class carriers changed

`issues/mono-class-laws.md`: a tactic working inside `section<A:
OrderedField(≈, <, <=, +, *)>` (`mono`, `docs/monotonicity-tactic-design.md`
§8). Two questions, and what each answer turned out to be.

- **How `View` presents a dictionary's operations.** The class's index
  operations (`+`, `<=`) are binders of the section, so `x + y` was already
  `HLocal(+, [x, y])`. Its fields are not: `A.inv(x)` and `A.unit` are
  projections out of the dictionary local, `fst(snd(…(d)))`, which the
  speller reads as `d.inv` (`Speller::field_read`, the recogniser now shared
  as `Elaborator::field_read_parts`) and `View` gave `HOther`. They are now
  `HField(of, name, args)`: the record, the field's name and the arguments
  the field is applied to. A field whose record registers a projection
  definition stays that global's `HGlobal`, as before. The dictionary's own
  type, a value-parameterized record, was `HOther` too (its arguments are not
  recoverable from a constructor shape, so `display_targs` declines); it is
  now `HGlobal(class, name, [carrier, index…])`, read by unifying the type with
  the declaration's template `C#tycode_fn` at unknown arguments, read inline,
  and required to convert back. Type arguments are type handles, value
  arguments term handles.
- **Whether `Match` fills a class lemma's dictionary.** It did not. A lemma
  of a section is `Π A ≈ < <= + (c : OrderedAddGroup<A>(≈, <, <=, +)) x y z …`;
  matching its conclusion `z + x <= z + y` determines `<=`, `+` and the
  points, but neither the dictionary nor the indices the conclusion does not
  mention (`≈`, `<`), and `apply` handed the dictionary to the premise
  tactic, which cannot prove a class. `Match` now fills a parameter whose type
  is a class the way a call fills its constraint argument
  (`docs/operation-indexed-classes-design.md` §5): first from the
  dictionaries in scope, the class's own binder or a descendant's at its
  carrier and the index it passes up (the value-slot ladder's step 2), which
  also solves the carrier and the indices by unifying the parameter's type
  with that instantiation, the parameter being what resolution answers there
  (an upcast from a descendant's binder); and when that does not match, plainly
  as before, with a class parameter whose type the match has determined
  resolved there (instances included). The candidates and resolution's
  answers are computed once per `Match`, not per parameter count. Nothing
  here is trusted: the conclusion still has to convert to the goal and the
  application is checked. A lemma's parameter is the reference spelling
  `El (app(C#tycode_fn; ā))` and the candidates are lowered inline, so the
  parameter is read inline (`unspell_here_in` at the match's metavariables)
  before the two unify.
- **Rejected: an `Instance(ty)` request.** A tactic asking for a dictionary
  would have to state the class's type first, and the indices it does not see
  (`≈`, `<` behind a conclusion about `<=`) are exactly what it cannot state;
  the call path already knows where they come from.

## 19. What round 4 changed

R4 (`issues/heather-checked-construction-api.md`): a Heather generator
builds a small declaration group, and the elaborator checks every member and
publishes all of them where the generator was invoked, or none.

- **Invocation is an item, `generate g(args);`.** The proof-position
  invocation is `by t`; a generator needs a module-level one. `generate` is a
  contextual keyword (an item that starts with `generate` followed by a name),
  so no library name is reserved. `g(args)` is elaborated at
  `Tac<List<Decl>>` with quoting on, exactly as a tactic's arguments are; a
  generator runs in the module's empty context, so the only terms it can quote
  are closed ones, and a type's name in an `Expr` position (`Tm`, a
  parameterless inductive) is quoted as that type. Inside a `section` or an
  `assuming` block it is refused by the parser for now: the generator would
  have to run under the head's binders, and nothing says yet how its
  declarations would then inherit them.
- **One request tree for both.** A generator is the same `Tac` as a tactic,
  run by the same loop (`drive`) in generator mode: it has no goal (`Goal` is
  refused, and its quoted handles start at 0), and it ends with
  `Publish(decls)`, whose response type is `Never`, so nothing can follow it.
  `host_generator(g)` is `g.bind(publish)`. A tactic that sends `Publish` is
  refused at its `by`.
- **Building declarations.** `Assume(ty, name, under)` introduces a local of
  type `ty` in a new scope under `under`'s (or the root); a declaration's
  parameters are such locals, each introduced under the one before it, and its
  statement and body are `Expr`s in the last one's scope. `Decl(form, name,
  params, result, body)` names them; a parameter is implicit when its `Param`
  says so. The same `Assume` makes a binder the body abstracts with `Lam`
  (introduced beside the parameters, not under them). `Expr` gains `Pi(x,
  body)` for a function type over such a local, `Equation(lhs, rhs)` for an
  identity type, and `Blank`, an argument the application's domain check
  solves (a run-scoped hole, so a generator writes `cong(_, _, f, _, _, p)`
  and lets unification find the implicit arguments). `AsType(e)` checks an
  `Expr` as a type and answers its handle.
- **Reading a type's shape.** `Ctors(ty)` answers each constructor of an
  inductive type: its name, its fields (name and type), and the constructor as
  a function of its fields. It reuses R3's skeleton technique: an anonymous
  constructor (or `T::C`) with marker leaves is elaborated twice with
  different placeholders, so a field whose type mentions an earlier field
  comes back without a type rather than with one stated about a placeholder;
  such a constructor has no function either. Codata and indexed families are
  refused.
- **Checked twice, published once.** When the run ends, each member is read
  back in the run: its parameters must form the telescope above (a forged
  local, a `let`, or a parameter that is not under the one before it is
  refused), its statement and body are reified, the body's type must convert
  to the statement there, and nothing may mention an unsolved hole. Then each
  member is elaborated as the same declaration written in source: a surface
  `theorem`/`fn` whose parameter types, result and body are marker leaves
  (`Leaves::Member`) filled with the checked terms, so registration,
  namespacing (`Tm::cong_App` is `Tm`'s member), the kernel gate and the
  module image are exactly the source path's. All members are published in
  one `session_transaction`: a member the elaborator refuses (a name already
  declared, say) rolls back the ones before it, journal included. Errors name
  the generator and the member.
- **Names.** A member's name must be a declaration name (`::`-separated
  identifiers). A parameter keeps its `Assume` name where that is a plain
  identifier, else it is `x{k}`; the names are what named arguments see
  (`Tm::cong_App(hf, ha, f1 := f)`).
- **The customer: `congruences(T)`** (`lib/std/tactic/derive.hthr`), which
  declares `T::cong_C({x1 … : X}, {x2 …}, x_eq: x1 = x2, …): C(x1, …) = C(x2,
  …)` for each constructor with fields, proved one field at a time by `cong`
  and joined by `trans`. Against the hand-written group it would replace
  (`lib/kernel_model/kernel_reduction.hthr`'s `Tm::cong_lam` … `cong_pair`),
  the statements are the same up to the names' case; `cong_proj` and
  `cong_run` differ, since the hand-written ones hold their non-`Tm` field
  fixed (`cong_proj(pr, p)`) where the generated one varies every field. The
  library is not migrated in this round: the kernel model would import the
  tactic protocol for five one-line lemmas, and its 46 call sites cite the
  hand-written shapes.
- **Cost.** As for tactics: evaluating the generator between requests
  dominates, and each member then costs what the same declaration written in
  source costs. A generator's output is not imaged separately; the module's
  image holds the published declarations like any others.
- **Left open.** A member citing an earlier member of its own group (they are
  published only after the run, so `Lookup` cannot find them); `generate` in a
  section or under `assuming`; `Ctors` at a parameterized type (quoting finds
  only parameterless ones) or a dependent field; a field projection in
  `Expr`; R3½'s oracles.

## 20. Building an application one argument at a time (2026-10-31)

Issue `generic-lemma-elaboration-cost`. `mono` at a class carrier cost
seconds per call where its concrete twin cost a fraction of that, and most
of it was `Infer`: a tactic that applies a law to holes for its leading
parameters (`apply_slots`, `cast.hthr`'s `cast_holes` and `cast_slots`)
asks for the type of each prefix, and the host re-read every prefix from the
`Expr` — each `Infer` of `f(h1, …, hk)` re-reified `f(h1, …, h(k-1))`,
re-zonked its type and re-substituted it. A morphism law has nineteen
leading parameters over a record type the size of the morphism's laws, so
the reads were quadratic in the spine over a large type.

- **The host remembers its readings.** `Run::readings` keeps each reified
  application with no `Blank` in it (a `Blank` is a new hole at every
  reading), by scope and `Expr`, with the world it was made in (a hit is
  shifted past the holes made since) and the trail's length then (a
  `Restore` below it drops the reading, since the argument's domain check
  may have relied on a solution it forgets). The prefix of the next `Infer`
  is then a hit, and each request costs one argument's worth.
- **`Holes(e, n)`** answers `e` applied to `n` new holes, one per leading
  parameter, each at its parameter's type with the holes before it as the
  earlier arguments, and records each prefix as a reading, so the tactic's
  `infer` of `cast_apps(e, holes)` is a hit. It makes the holes first and
  instantiates the spine once per hole, where `infer`, `open` and `hole`
  per argument shifted and zonked the whole spine three times each.
  `cast_holes`, `cast_targeted` and `cast_slots` are one request each now
  (`cast_slots` unifies its presets with the first holes afterwards; the
  later holes' types mention them, so nothing is read before they are set).
- **`mono` reads the cast edges once per run** (`Mono.edges`, read where the
  carrier has push lemmas): reading a morphism local checks a law at it,
  and `mono` read every edge again at each leaf's push, order and fact
  probe. `cast_premise_among` and `cast_from_among` take edges a caller
  holds.

What is left of a `mono` call at a class carrier is evaluating the tactic
between requests and `apply`'s `Match`, the same as at a concrete carrier.

## 21. Asking the resolver: `Synth` (2026-11-01)

`Synth(goal: Handle) → Checked<Handle>` runs the search a `:= infer`
parameter runs (`Elaborator::resolve_goal`) at the type the handle stands
for, in the handle's scope: locals, the derived table, instances, and at a
proposition computation and the evidence rules, search rules last. It is
refused, with the search's trace as the reason, when nothing answers, and a
refused search leaves nothing (`SearchMark`). The type must mention no
unsolved hole: the search's trials are the elaborator's own and know
nothing of a run's holes.

Its first customer is facts on demand (`docs/facts-on-demand-design.md` §4):
a generator that asks for a fact must hear "none" rather than fail, which
neither `:= infer` nor a parameter default can say. `lib/std/tactic/fact_request.hthr`'s
`request` is `Synth`, then the requester's budgeted fallbacks. A Heather
tactic that wants instance search or the evidence rules (a `positivity`
written in Heather, say) can use it the same way.

## 22. A term's whole spine: `Spine` (2026-11-02)

`Spine(h: Handle) → Checked<SpineInfo>` reads the term a handle stands for
as a head applied to arguments, peeling the kernel's applications with
nothing reduced: every argument in order, implicit ones and type arguments
included, each with whether the function's type is dependent at it. `View`
lists only the arguments a call writes, which is right for display; a
tactic that compares or rebuilds applications needs the kernel's list. A
type is refused, and a term that is no application is its own head.

Its first customer is `grind` (`docs/grind-design.md` §3), whose graph
nodes are the kernel's curried applications, with dependent arguments kept
in the head.

## 23. Saying something on success: `Say` (2026-11-02)

`Say(msg: String, notes: List<Note>) → True` records a message and notes,
rendered as `Fail` renders them, and the host reports what a run said as
one `tactic-report` warning (`Lint::TacticReport`) at the `by`, once the
run's result checks as the goal's proof. A run that fails reports only its
failure, so a note can never contradict the outcome. Several `Say`s in one
run are one warning, their texts in order (the warning channel keeps one
warning of a lint per span).

Before it, a tactic could only speak by failing. Its first customer is
`grind_report` (`docs/grind-design.md` §9.4), which says which hints its
proof cites, so the call can be narrowed: the used-subset report of
[lemma-selection-and-search](../issues/lemma-selection-and-search.md) piece 3.
A generator's run (`generate`) says nothing yet: its `Say`s are dropped.

## 24. A value's fields: `Fields` (2026-11-02)

`Fields(e: Expr) → Checked<Projected>` takes a term of a non-indexed
inductive type with one constructor (a record, `∧`) apart into its fields:
the type, as the reference `Lookup` answers for its name, and for each field
its name (its position where it has none) and a handle to its projection,
the term `e.name` elaborates to (`project_field`), whose type is the
field's. The type is read as written, unspelled, or once in head normal
form, so a definition whose value is a `∧` (`a.Same(b)`) is taken apart
too. Refused for any other type, and for one with a field a later field's
type mentions (`∃`'s `witness`, whose `proof` is a fact about the value
rather than one of its own): that is the `Σ`'s second component depending
on its binder.

```heather
record FieldProj { name: String, term: Handle }
record Projected { ty: GlobalRef, fields: List<FieldProj> }
```

`Expr` has no projection form, and none is needed: a tactic cites a field by
the handle. Its first customer is `grind`, which reads a conjunction or a
record of equations as its fields (`docs/grind-design.md` §12); `omega`'s
Rust `local_facts` does the same for `∧` alone, inside the elaborator.

## 25. Injectivity and disjointness: `Inj`, `Absurd` (2026-11-05)

`Inj(e: Expr, k: Nat) → Checked<Handle>` is `inj(e, k)`: from `e`, a proof
of an equation between two values of one constructor (as the sides
compute), the equation between their `k`th fields. `Absurd(e: Expr, goal:
Handle) → Checked<Handle>` is `absurd(e)` at the type `goal` holds, from a
proof of an equation between two different constructors' values. Both run
the surface forms' builders on an elaborated proof (`inj_of_term`,
`absurd_of_term` in `inductive.rs`, split out of `build_inj`/`build_absurd`
so the two share every refusal: different constructors for `inj`, one for
`absurd`, a field whose type an earlier field's mentions, sides that are no
constructors' values). `Absurd` reads the goal handle after reifying `e`:
reifying may make holes, which a type read before would not be shifted
past (the cause of a wrong-type result in `round_real`'s first
conversion). Tags 28 and 29. Their customer is `grind` (grind design §14).

Two answers changed with them:

- `Whnf` of a term reads off projections of pairs in its answer
  (`spelling::contract_projections`, what `inj` and `absurd` do to a
  computed side), so a constructor value reached through the checked
  spelling is shown by `View` as the `HCtor` it is.
- `View` calls a `match` applied to arguments (a codata observation, whose
  motive is a function type) `HMatch` of its scrutinee, as it does a bare
  one: it is stuck on the same scrutinee.

`Lookup("False")` answers the kernel's empty type, as `Lookup("True")`
answers its unit.


## 26. Terms whose place types them, and `Abstract` (2026-11-09)

`wlog` (issues/wlog-symmetric-cases.md, `lib/std/tactic/wlog.hthr`) is a
tactic whose arguments are proofs the user writes in place, unannotated:
`by wlog(m, n, λ a b h => …, λ a b le => …)`. Neither `λ` infers a type, and
the type each must have (`(a, b: T) → P(a, b) → P(b, a)` with `P` the
goal abstracted) exists only once the tactic has read the goal. Two
additions serve it, and neither is specific to it:

- **A quoted argument may be held as written.** Where a tactic expects an
  `Expr` and is given a term that infers no type and does not check as an
  `Expr` either, quoting keeps its surface syntax (`Quoted::Surface`) in
  place of an elaborated term, under a handle like any other. The handle can
  stand only where the result gives it a type: as an application's argument,
  where reification checks it at the domain (`Elaborator::check_surface`),
  or as the tactic's whole result, checked at the goal. Every request that
  asks about a handle (`Infer`, `View`, …) is refused for it. It is
  elaborated in the goal's context, where it was written, so the expected
  type must mention no hole and no local the tactic introduced; β-redexes a
  motive's application leaves (`P(a, b)` with `P` a `λ`) are contracted
  first, so the term's binders read as the goal does. A term that fails to
  check is reported as its own error, at its own span, when the run fails.
  Only directly under the goal's context: under a binder of the tactic
  expression itself, the old refusal stands.
- **`Abstract(h: Handle, x: Expr) → Checked<Handle>`**: `λ y => h[y/x]`,
  for `x` a local of the goal's context (a `Local` of the goal or a quoted
  `m`), a function of `x`'s type; a type is abstracted as its code. Two
  abstractions make a two-place motive. Only `h` is abstracted: a later local
  whose type mentions `x` keeps meaning the original, which is still in
  scope, so the result is well typed whatever `h` mentions, and the kernel
  checks the proof that uses it. It reuses the induction-hypothesis
  generalization's renaming (`generalize::rename`). Tag 33.
