# Host elaboration interface: Heather tactics as request trees

Design proposal for the `tac-host-interface` milestone
(`docs/roadmap.md`: "Heather code can read a goal, build a checked term, and
report failure with its search state, through one scoped host interface").
It answers `issues/host-elaboration-interface.md`, retargets
`issues/heather-checked-construction-api.md` (whose customer was burned in
B1) and places `issues/elabcode-abstraction-layer.md`. Round pattern as
usual: this document first, the implementing rounds against §10.

Status: **proposal; §0 is what Minus decides.** Nothing here is built yet
except the probe in §9, which checks that the request tree is writable in
today's surface.

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
   `lib/std/tactic.hthr` now, so that when `it-core` lands `Tac<A>` becomes
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
  (`lib/certgen_code.hthr`) are evaluated in the kernel's value domain by
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
// lib/std/tactic.hthr (round 1 subset)
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
| R1 | `lib/std/tactic.hthr` (protocol, `bind`, helpers), `host.rs` loop, `by`, requests `Goal`/`View`/`Defeq`/`Fail`, the speller's recogniser shared with `View` | `by assumption` closes goals at open types and neutral hypotheses, and its failure lists every hypothesis tried |
| R2 | `Intro`, `Resolve`, `Infer`, `Whnf`, `Check`/`Attempt` with rollback; `exact`, `intro`, `apply`, `first_of` in Heather | a Heather `apply` closes an implication chain; a failed `first_of` reports each branch |
| R3 | `tac-first-port`: `split_all` or `monoid` normalisation in Heather | it closes the same goals as the Rust one on the existing tests |
| R4 | publication (`heather-checked-construction-api`, retargeted): a `Publish(group)` request that checks a small declaration group and adds it only if every member passes the kernel | a Heather generator publishes a lemma group in the caller's scope; a failing member publishes nothing |

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
  fixed by Rust's needs.
- **An effect-system or monad-transformer `TacticM`.** Heather has no
  effects; a request tree is the pure encoding of one, and it is the same
  object the interaction-tree area is building.
- **Waiting for `it-core`.** The host needs two constructors; §3.2's local
  type keeps the protocol identical to the library's tree.
