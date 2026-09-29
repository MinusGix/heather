# Sharing-preserving evaluation: a value-domain whnf for conversion

Status: **design round complete 2026-07-31, no kernel code.** Owning issue:
`issues/whnf-sharing-term-growth.md` (stays open; this document is what its
"lever 1" costs out). Written per the `docs/wf-former-design.md` /
`docs/sprop-design.md` discipline: decisions with rationale, rejected
alternatives priced, acceptance stated before the first kernel line.

The defect, in one sentence: the kernel has a **rewriter**, not an
**evaluator**, so a computed result carried forward as an unforced redex is
re-forced at every enclosing level and nothing shares the copies — ~×2 per
level, ~×22 per loop iteration of the IR interpreter, with time, peak RSS,
substitution work and largest-single-term all sharing one exponent. The fix
that changes the exponent rather than the constant is to reduce into a
**value domain with environments and closures**, so that an eliminator's β
closes over its branch instead of copying it.

This document decides *what* that means for this kernel — a layered modal
type theory with contextual types, boxed code, code recursors, definitional
irrelevance and a δ-lazy definition mechanism — none of which appear in a
textbook NbE.

---

## 0. What this changes, in one line each

- **The declarative theory:** nothing. Not a rule, not a former, not a
  binding form. §11.
- **`reduce.rs`:** survives, unchanged, as ch. 06's relation — now the
  *specification* and the differential oracle, plus `typing.rs`'s whnf. §2.
- **`conv.rs`:** its two whnf stages and every `nf`/`ne` arm move from
  `&Term`/`&Type` to values. §2, §3.
- **`typing.rs`:** untouched. §7.
- **`bounds.rs`, `subst.rs`:** survive; conversion stops being their
  customer. §8.
- **New:** a value domain, an evaluator, and the value-side of the
  universe/global namespaces. §3, §4.
- **No readback function exists.** §7. This is the load-bearing simplifying
  decision of the whole design.

---

## 1. Why NbE and not something smaller

The issue killed four hypotheses and one whole route; they are not
re-litigated here. What is worth restating is why the *smaller* kernel
levers do not reach:

- **Explicit substitutions / suspension nodes in `Term`** (the issue's
  lever 2). They make β O(1) too, but they put an unforced redex *into the
  syntax* — which is precisely the shape the defect is about — and then
  `conv.rs` must compare terms that are equal only after forcing. Ch. 06's
  Determinacy and the WHNF/neutral grammars are stated over a syntax without
  them; every lemma in `docs/ch05-06-lemma-audit.md` that quantifies over
  `Term` acquires a new case. The metatheory bill is not obviously smaller
  than NbE's, and unlike NbE the result is a syntax nobody else has studied.
  Rejected.
- **Constant-factor work** (arena allocation, a smaller `Term` node, killing
  the bounds memo). 1.3–1.5× on a curve whose base is 22: less than one loop
  iteration. Correctly classified on the issue as *not levers*.
- **Restructuring the consumer.** Spent — the defunctionalized step machine
  was implemented and measured strictly worse, and the diagnosis it produced
  is the broader one this document targets.

The positive argument: an environment machine makes the *only* operation
that was quadratic-per-level — instantiating a branch — into extending a
vector. Everything else in the deep-path profile (30% allocate/free/drop,
26% substitution traversal, 21% bounds skip) is downstream of that one
operation.

---

## 2. Scope: what is replaced, what survives

**Decision: a shared-value whnf for conversion, not "full NbE".**

The kernel does not gain a normalizer. It gains an `eval` that maps
(syntax, environment) to a weak-head **value**, and conversion is rewritten
to compare values. There is no normal-form readback (§7), no η-long forms,
no type-directed normalization pass. Conversion stays exactly what ch. 06
says it is — reduce both sides to weak head normal form, compare
structurally, recurse — with "weak head normal form" realized as a value
instead of a term.

Concretely:

| code | fate |
|---|---|
| `reduce.rs` `step_term(_delta)` / `step_type(_delta)` / `whnf_*` | **survives verbatim.** Still ch. 06's relation. Two live consumers: `typing.rs` (§7) and the differential oracle (§12). Not dead code. |
| `reduce.rs` `beta_elim_ty` / `beta_elim_tm` (the ~1300-line code-recursor β) | **survives**, and is *shared*: the evaluator calls the same functions to produce the fired branch as syntax, then evaluates it. The 52 branch telescopes are not transcribed a sixth time. |
| `reduce.rs` `is_whnf_*` / `is_neutral_*` | survive for `reduce.rs`'s own use; the value domain makes them structurally unnecessary on the conversion path (a value *is* its classification). |
| `conv.rs` `Conv::whnf_ty` / `whnf_tm` / `whnf_ty_opaque` / `whnf_tm_opaque` | **replaced** by `eval` + `force`. |
| `conv.rs` `ty_nf` / `tm_nf` / `ty_ne` / `tm_ne` / `tm_nee` / `rec_ca` | **rewritten in place**: same arms, same order, same rules; inputs become values. This is the bulk. |
| `conv.rs` `ctx` / `subst` / `code_eq` / `lev_eq` / `delta_head*` | survive with small edits (§3.4, §5). |
| `typing.rs` | **untouched** (§7). |
| `subst.rs`, `bounds.rs` | survive (§8); conversion stops being their hot customer. |
| `rec.rs` | untouched — telescopes are syntax. |

**The rewriter stays as a differential oracle.** This is recommended and
sized (§13 stage 1). The repo already has the ingredients: `tests/common/wt.rs`
synthesizes **well-typed** `(term, type, level)` triples bottom-up along the
ch. 04 rules over non-trivial Ψ and Γ (boxes, letbox, code recursors, the
whole former list), `perturb_conv` produces a structurally distinct but
convertible twin, and the `law!` macro (`tests/common/mod.rs`) reports
**seed only** on failure — mandatory here, since a disagreeing pair is
exactly the kind of term that OOMs a machine if Debug-formatted.

Two cautions, both already written down in the repo and both load-bearing:

1. **A differential equality test is blind to sharing regressions.**
   `subst_laws.rs` makes this point about itself and asserts on
   `Rc::ptr_eq` instead. The analogue here: `eval` could agree with the
   rewriter on every value and still be exponential. The differential test
   proves *correctness*; only the acceptance bench (§13 stage 0) proves the
   exponent died. Neither substitutes for the other.
2. **No existing test compares two kernel implementations.** The repo's
   oracle patterns are hand-transcription vs. implementation
   (`conv_pair_properties.rs`'s `decode`), generator vs. checker, and the
   four-way transcription of the recursor telescopes. This round creates the
   two-implementation pattern; it should be written to the same standard
   (multiple seed streams — `ch05_06_lemmas.rs` found a real generator defect
   at ~1-in-3000 by varying the schedule, not the count).

---

## 3. The value domain

The design constraint that shapes everything: **a value must make the
kernel's invariants unrepresentable, not merely unviolated.**

### 3.1 The three namespaces are treated differently

DeLaM has three independent namespaces (locals into Γ, globals into Ψ,
universe variables into L). **Only the local namespace is environment-based.**

- **Locals → environment.** Closures, one per binder. This is where the
  exponent lives and this is what the round is for.
- **Universe levels → syntax.** `Level` is a separate sort with its own
  normalization (`count`/`adjust`); it never contains a term and is never
  reduced by `⇝`. Values store `Level` verbatim and `Level::equiv` is
  unchanged. Rejected alternative: level values. They would buy nothing —
  there is no level redex.
- **Globals → syntax, with δ as the one exception.** `apply_global` /
  `shift_global` stay syntactic operations. A global *variable* becomes a
  neutral head (§5).

Consequence, stated as a decision because it is the largest chunk of "new
surface that is not the evaluator": **values need the other-namespace maps**
(`shift_univ`, `inst_univ`, `shift_global`, `apply_global`), because a
closure captures an environment of values and entering a layer-m binder
shifts the ambient scope. They are ordinary structural recursions mirroring
`subst.rs`'s non-local half, applied **eagerly** — this is layer-m-only
machinery, entirely off the IR hot path, and eagerness keeps it out of the
correctness argument. Mitigating fact: at the *root* of a conversion the
environment is the identity environment of neutral variables, so the maps
have nothing to do until a metaprogram builds a genuine closure over a
universe or global binder.

### 3.2 Variables: levels, with an abstract-prefix escape hatch

Standard NbE uses de Bruijn **levels** in values so that pushing a binder
needs no shifting. That is exactly what makes `Vec^l(T; S k) ⇝ Σ(_:T).
Vec^l(T; k)` — today three `shift_local` calls — into a constant closure
with no shifting at all.

**But this kernel's `LocalCtx` may have an abstract base** (`CtxBase::Var(g)`,
a context variable of unknown length), so "level from the outer end" is not
always defined. Decision — a two-part variable identity:

```
Head::Var(lvl)        -- lvl counts the *concrete* entries from their outer end
Head::BaseVar(depth)  -- depth counts into the abstract prefix g, from its inner end
```

Both are stable under pushing binders on the right, which is the only thing
conversion ever does. An index `i` in a Γ with `n` concrete entries splits as
`i < n ⇒ Var(n-1-i)`, `i ≥ n ⇒ BaseVar(i-n)`. This is a genuine deviation
from textbook NbE forced by context variables, and getting it wrong is a
silent scoping bug, so it is pinned by the differential test's open-term
cases (`wt.rs` generates non-empty Γ over all three base shapes).

**Implemented representation note (2026-09-02).** The persistent local
environment has a copyable handle `(arena, head, len)` and arena-owned cells
`(value, next)`. In particular a cell does not recursively embed the whole
handle: doing so repeated the arena pointer and length in every captured
link, doubling a cell from 16 to 32 bytes. The explicit handle length is not
merely a cached convenience; it identifies where indices cross into the
abstract prefix, while cells remain context-independent shared tails.
`issues/value-domain-allocation-constant.md` records two rejected follow-ups:
a virtual one-binding view almost always had to persist immediately, and
putting the length back in every cell traded more cell memory than it saved
in the smaller subset of closure handles.

### 3.3 The constructors, enumerated against `term.rs`

`Type` has 21 variants, `Term` 47. The mapping is mechanical, and the only
interesting decisions are which sub-structures become **closures**, which
stay **syntax**, and which disappear.

**Type values.** Every former keeps its levels as syntax; a sub-structure
under the former's own binder becomes a closure `Clo` (environment + body,
one local binder):

| former | value | binder → closure |
|---|---|---|
| `Nat`, `Ty(l)`, `Unit^l`, `Empty^l`, `SEmpty^l` | atoms | — |
| `Pi`, `Sigma`, `W` | `{levels, dom: Val, cod: Clo}` | codomain / second / positions |
| `Wf` | `{level, shape: Val, arity: Clo}` | arity (a `Nat` term under the shape binder) |
| `Sum` | `{levels, lhs: Val, rhs: Val}` | non-dependent, no closure |
| `Id`, `SEq` | `{level, ty: Val, lhs: Val, rhs: Val}` | — |
| `Vec`, `Fin` | `{…, len: Val}`, **only at a neutral length** | — |
| `El` | **does not exist as a value** | see below |
| `UPi`, `CtxPi` | `{…, body: SynClo}` | binds a *universe* / *global*, not a local |
| `TyPi` | `{ctx: LocalCtx (syntax), levels, body: SynClo}` | ditto |
| `CodeTy` | `{ctx: LocalCtx (syntax), level}` | — |
| `CodeTm` | `{ctx: LocalCtx, ty: Rc<Type> (syntax), level}` | `ty` is scoped in Δ, a *different* local scope |
| `GlobalTy` | neutral type (§5) | — |

`El` disappears because it is exactly a redex-or-neutral: either it decodes
(and the value is the decoded former) or its encoding is neutral, in which
case the value is `VNeutralTy::El { level, ne }`. Making `El` unrepresentable
as a canonical value is the domain enforcing ch. 06's own grammar
(`V := U^δ | El^l ν`).

`Vec`/`Fin` at a *canonical* length likewise cannot be values: they step. The
domain admits them only over a neutral length, which is precisely
`is_whnf_type`'s condition today — again, an invariant made structural.

**`SynClo`** is an environment plus unevaluated syntax with **zero** local
binders and one pending universe/global binder. It is entered by applying
the syntactic instantiation to the body (and, per §3.1, to the captured
environment) and then evaluating.

**Term values.** Canonical forms map one-to-one:

- data: `Zero`, `Succ(Val)`, `Refl`, `SRefl`, `Pair`, `Triv`, `Inl`, `Inr`,
  `Sup` (children a `Val` — it is a function), `Supf` (children a `Val` —
  a `Vec` tuple);
- functions: `Lam { levels, dom: Val, body: Clo }`, and `ULam`/`CtxLam`/
  `TyLam` with `SynClo` bodies;
- the 14 **encodings** (`TmNat`, `TmPi`, `TmTy`, `TmId`, `TmSEq`,
  `TmSEmpty`, `TmSigma`, `TmUnit`, `TmEmpty`, `TmSum`, `TmW`, `TmVec`,
  `TmFin`, `TmWf`) mirror their type formers, with the same closure choices
  (`TmPi.cod`, `TmSigma.snd`, `TmW.pos`, `TmWf.arity` are closures);
- `BoxTy(Rc<Type>)`, `BoxTm(Rc<Term>)` — see §3.5;
- everything else (`Var`, all 15 elimination forms, `GlobalTm`) is a
  **neutral** (§5).

**Closures may be native.** Two β rules synthesize a λ around a recursive
call: `elim_W`'s ih (`λ y. elim_W … (f y)`) and `elim_Wf`'s
(`λ i. elim_Wf … (nth … cs i)`). Today each is built with a template plus
three `shift_local`s. Decision: allow `Clo::Native` — a Rust closure over
already-evaluated components — for exactly these two and for η-expansion.
Cost: two hand-written cases in the algorithm-equivalence argument (§11) and
a `<native>` placeholder in the budget-bounded `Debug`. Benefit: the shift
dance disappears, and with it the class of bug it invites.

### 3.4 `LocalCtx` and `LocalSubst` inside values

Both stay **syntax**, with one exception that matters.

`LocalCtx` appears in `CodeTy`, `CodeTm`, `TyPi`, `CtxApp`, `ElimCodeTy`,
`ElimCodeTm`. In every case it describes a *different* local scope (Δ, the
index context of some boxed code), never the ambient Γ. Conversion compares
two of them with `Conv::ctx`, which walks entries pairwise and calls
`Conv::ty` on each in the *prefix* context — i.e. it evaluates each entry in
a fresh identity environment for that prefix. Keeping Δ as syntax is
therefore both correct and free; making it a value would require an
environment per context, for nothing.

**The exception: a global variable's local substitution `δ`.** `u^δ` /
`U^δ` carry a `LocalSubst` whose `terms` are terms *in the ambient Γ*. If
those stayed syntax, `u^δ` would be a value carrying unforced redexes —
which is the defect class, verbatim, reintroduced by the domain. Decision:
**a neutral's `δ` stores its `terms` as values, evaluated pointwise at
construction; the `tail` (`·^k_{g?}` / `wk^k_g`) stays syntax.** `Conv::subst`
then compares values pairwise, as it compares terms today.

This is the single subtlest correctness point in the domain, and it is worth
a test of its own: a definition applied under a substitution whose payload is
an expensive redex, discharged at several nesting depths.

### 3.5 `box` is an inert atom carrying syntax

Ch. 06 is unambiguous: reduction never enters a `box`, and boxed code
compares by *syntactic* equality (`conv.rs`'s `code_eq`, modulo level
equivalence per ch. 05's Static Code lemma). Layer-c is where code is data.

**Decision: `VBoxTy(Rc<Type>)` / `VBoxTm(Rc<Term>)` carry raw syntax, with
no environment and no closure.** This makes the invariant *unrepresentable
to violate* rather than a discipline to remember: there is no environment in
which the payload could be evaluated, because the constructor does not have
one. `eval` never recurses into a box; `code_eq` reads the payload directly,
unchanged.

The code recursors *inspect* inside a box — `beta_elim_ty`/`beta_elim_tm`
dispatch on the head of the code and build recursive calls
`elim(box code')`. That is inspection, not reduction, and it stays
syntactic: the evaluator hands the box's payload to the existing
`beta_elim_*`, receives a fired branch as **syntax**, and evaluates that.
The 52 branch telescopes are not touched. (`fire`'s universe and global
instantiation stay syntactic, per §3.1; only its final `apply_local` of the
recursive-call payloads becomes environment extension.)

Consequence worth stating because the SProp round turns on it: neither the
`transp` strip nor any irrelevance arm can reach inside a `box`, for the
same structural reason as today. The firewall is unchanged.

---

## 4. Layers: evaluation exists at p and m only

`conv_type` / `conv_term` / `conv_local_ctx` all open with
`debug_assert!(layer.computes())`. Conversion is *never* invoked at layer c
or v: at c, code is compared with `code_eq` from inside a box, and the
layer index in `Conv::Env` restricts which **type** formers may match, not
which terms are reduced.

**Decision: the evaluator carries no layer index.** It takes a `Defs`
(§5), which the caller has already resolved from the layer — exactly the
existing `Conv::defs` gate, moved one call deeper:

```
fn defs(&self, env: &Env) -> Defs<'_> {
    if self.has_defs && env.layer.computes() { Defs::transparent(&env.psi) } else { Defs::opaque() }
}
```

The layer stays where it is today, in `Conv::Env`, gating the layer-m arms
of `ty_nf` and `tm_nf` and bumping to `Meta` for layer-m *term* forms. That
placement is ch. 06's ("the layering index restricts only types") and it is
orthogonal to how reduction is implemented.

Rejected: a layer-indexed evaluator. It would encode the same one-bit
decision twice and create a way for the two copies to drift.

---

## 5. δ: glued evaluation

Today's design (`DESIGN.md`, `docs/metatheory-ch07-extensions.md` §§23–25) is
δ-lazy: weak-head-reduce **without** δ first; if both sides then sit at the
same defined head, compare spines before unfolding; a `NotConvertible`
falls through to unfolding; the whole stage is gated on Ψ actually holding a
definition, because paying for the second pass unconditionally cost
1.35–1.43×. That design must survive. Under values it does, and improves.

**Decision: glued neutrals.**

```
VNeutral { head: Head, spine: PersistentSpine<Elim>, unfold: Option<Thunk<Val>> }
Head ::= Var(lvl) | BaseVar(depth) | Global(u, δ_values) | BoxedGlobal(box-syntax)
```

- `unfold` is `Some` exactly when the head is a `Global(u, …)` that `Defs`
  says is defined. It is a **cached thunk**: forcing it evaluates the
  definition's body under `δ`'s value environment and then replays the
  spine. Recent visits share the value through the query's bounded cache; a
  visit after eviction may recompute it rather than retaining a dead graph
  for the whole query.
- `BoxedGlobal` is ch. 06's `box(U^δ)` / `box(u^δ)` neutral-scrutinee case
  for the code recursors: a canonical box under an eliminator that can never
  fire. Naming it a head keeps `is_neutral_term`'s special case from having
  to be re-derived.

**The δ-lazy order, restated on values.** `Conv::tm` becomes: evaluate both
sides with `Defs::opaque`-equivalent behaviour — i.e. *do not force* the
`unfold` thunks — and compare. `delta_head` / `delta_head_ty` disappear:
they exist today only to discover, by walking syntax, what the value's head
already is. If both heads are the same `Global(u, …)`, compare spines under
the existing `delta_lazy` guard; on `NotConvertible`, force both thunks and
compare the results. Same order, same guard, less work, and the head test is
now O(1).

**The `has_defs` gate survives** unchanged, and is now cheap for a second
reason: a neutral with `unfold: None` cannot enter the stage at all.

**Instrumentation.** `ValueMetrics` is an explicitly supplied aggregate
collector, not evaluator state. A profiled arena counts its environment,
term-closure and type-closure allocations and the two caches' lookups, hits,
inserts, evictions and peak resident entries. The profiled typing entry points
lend one collector to each short-lived conversion arena inside a kernel gate;
the elaborator can lend that same collector to its analyzer arena. Thus a
measurement has a caller-defined boundary and remains meaningful under
parallel tests, without a thread-local or global observer. No counter is fuel
and no counter participates in a rule.

**`Defs::body`'s per-unfold `shift_global`.** Today every unfold recomputes
`t.shift_global(v.0 + 1)`. The rescoping depends only on `v`, never on the
occurrence. Decision: **cache the rescoped body syntax per `GlobalVar`** in
the evaluator (a small map, lifetime of one conversion), and evaluate it per
use under that use's `δ` environment. The value cannot be cached, because
`δ` varies; the syntax can, because it does not. The issue measured
`ShiftGlobal` at 2.5% of the deep-path profile and 8.6% of the routine
`lib/ir_v1.hthr` profile, so this is a real if secondary win, and it retires
the sequencing confusion recorded on `issues/outer-namespace-bounds.md`.

**Termination.** Unchanged and unchanged in shape: Ψ is a telescope, so δ is
well-founded on the global index. Memoizing the unfolding does not weaken
that; it only makes the same well-founded descent happen once.

---

## 6. Fuel and guard semantics

This is where sneaky unsoundness lives, so it gets the most explicit
treatment.

**What must not change.** Fuel is a *trusted-base policy*, not an
optimization. Three properties hold today and must hold after:

1. `OutOfFuel ≠ NotConvertible`. Exhaustion is never a verdict. Every guard
   (`Conv::delta_lazy`, `Conv::strip`) catches `NotConvertible` **only** and
   propagates `OutOfFuel`.
2. **No refund** on a failed guard. Monotone-decreasing fuel is the totality
   argument; refunding breaks it.
3. Fuel is a **single shared budget** across reduction steps and comparison
   nodes, so the checker is total by construction even on ill-typed input.

**Decision: what spends fuel.** One unit per *evaluation step that ch. 06
would have counted*, i.e. exactly the set of situations where `step_term` /
`step_type` return `Some` today:

- every closure application (β at `Lam`, `ULam`, `CtxLam`, `TyLam`);
- every eliminator fire (`ElimNat`, `Case`, `ElimW`, `ElimWf`, `J`,
  `Transp`, `Fst`, `Snd`, `LetBox*`, and each `beta_elim_*` dispatch);
- every `El` decode and every `Vec`/`Fin` unfold;
- every δ-unfold (i.e. the first force of an `unfold` thunk — see below);
- plus, unchanged, one per comparison node in `ty`/`tm`/`ty_ne`/`tm_ne`/
  `ctx`/`subst`, and one per successful `strip`.

There is no readback (§7), so readback spends nothing. That is not a saving;
it is the absence of a category.

**Decision: forcing is fallible, everywhere.** `force(thunk) -> Result<Val,
OutOfFuel>`. No `Deref`-style implicit forcing, no infallible accessor, no
`unwrap`. This is the concrete mechanism by which property 1 survives:
laziness introduces new *places* an `OutOfFuel` can originate, and each one
is inside a guard that must not swallow it. A single infallible force is a
silent conversion of exhaustion into a verdict.

**Decision: a thunk that fails is never memoized as anything.** The first
`OutOfFuel` aborts the whole conversion (the error propagates to the top
today and will continue to), so a "failed" thunk state is unreachable by
construction. Stating it anyway, because a future caller that retried with a
larger budget on the same value graph would otherwise inherit a poisoned
node.

**The property that could actually break, and why it does not.** Laziness
changes *when* work happens, and one could fear that deferring work lets
`tm_nf` inspect an unforced value and answer `NotConvertible` before the
reduction that would have made the two sides agree. The invariant that rules
this out:

> **Comparison never inspects an unforced value.** Every value reaching
> `ty_nf` / `tm_nf` / `ty_ne` / `tm_ne` is in weak head normal form. The only
> laziness in the domain is (a) `unfold` thunks on glued neutrals, forced by
> the δ-lazy stage, and (b) closure bodies, forced by application.

Under that invariant the algorithm decides the same relation as today, and
the only lazy decision — whether to force `unfold` — is the *existing*
δ-lazy heuristic with its *existing* guard.

**Fuel accounting becomes sharing-dependent, and that is fine but must be
recorded.** If the left side's evaluation forces a shared thunk and the
right side reuses it for free, total fuel spent depends on the sharing
structure. This can never produce a wrong verdict (property 1), but it does
mean:

- **Existing fuel-sensitive tests keep their meaning and lose their
  numbers.** `seq_transp.rs`'s sweep asserts the *property* "every
  insufficient budget dies `OutOfFuel`, never as a verdict"; that property
  is preserved exactly. The specific thresholds at which each budget becomes
  sufficient will move (downward — sharing only reduces work) and must be
  re-recorded. Any test that asserts a *particular* budget is insufficient
  is asserting a cost model, not a rule; those get rewritten to assert the
  property or deleted.
- `conv_pair_properties.rs`'s "mutated negatives give `NotConvertible`,
  never `OutOfFuel`" gets strictly easier to satisfy and stays as-is.

---

## 7. Readback: there is none

**Decision: the kernel gains no readback function.** Values are produced by
`eval` and consumed by comparison; the value→syntax direction does not
exist. This is the design's largest simplification and it needs its
customers checked one by one.

- **`conv.rs` comparing under binders.** Does not need syntax: it applies
  closures to a fresh neutral variable and compares the resulting values.
  The four η arms (`Π`, `ΠΠ`, `(g:Ctx)⇒`, `(U:Typ)⇒`) become closure
  application; today they build `App`/`UApp`/`CtxApp`/`TyApp` syntax with
  `shift_local`/`shift_univ`/`shift_global` and re-reduce it.
- **`conv.rs` inferring a neutral's type.** `tm_ne` today returns a `Type`
  built by `apply_local` — e.g. `m1.apply_local(id_Γ.extended(n1))` for
  `elim_Nat`'s `M[ν/x]`. Under values this is instantiating the motive
  **closure** at the scrutinee **value**: no substitution, no syntax. This
  is one of the larger incidental wins, since those `apply_local`s are on
  the hot path.
- **Boxed code.** `code_eq` compares the syntax the box value carries
  (§3.5). No readback.
- **Local contexts and substitutions.** Syntax already (§3.4).
- **Error reporting.** `ConvError` is a two-variant C-like enum with no
  payload; nothing to read back. If `issues/cli-check-diagnostics.md` ever
  wants terms in messages, it will want them from the *elaborator's* source
  spans, not from a kernel value — and if it genuinely wants a value
  printed, that is a `Debug` impl (budget-bounded, `node()`-gated, per
  `CLAUDE.md`), not a readback into `Term`.
- **`typing.rs`.** The one real customer, and the answer is that it keeps
  the rewriter. Nine call sites, all `self.whnf(env, ty)` on a **type**,
  matching on `CodeTy`, `CodeTm`, `Pi`, `UPi`, `CtxPi`, `TyPi` — the
  checking side for `box`/`Lam`/`ULam`/`CtxLam`/`TyLam`, and the inference
  side for `UApp`/`CtxApp`/`TyApp`. What they do with the result is push a
  binder and check under it (`Pi`), or apply a *global*/*universe*
  substitution to the body (`UPi`/`CtxPi`/`TyPi`) — never instantiate a
  local closure. And they are cold: the deep-path profile shows no typing
  symbols at all, and `Conv::ty` itself does not appear. **Decision:
  `typing.rs` is untouched; it keeps calling `reduce::whnf_type_delta`.**
  This is what makes `reduce.rs` a live component rather than a museum
  piece, and it is what removes readback from the round entirely.
- **The elaborator's head-shape probes** (`SemanticOracle::whnf_type` /
  `whnf_term`, 2026-09-05). Same shape as `typing.rs`'s — match a whnf'd
  type on its former — but on *propositions*, whose heads compute
  (`Le(x, dot(row, atoms))` at `Int` is a `match` on a dot product), and the
  rewriter paid the whole computation by substitution to answer "stuck"
  (`issues/elaborator-whnf-probes-on-computing-types.md`). The oracle now
  asks the value machine first and lets it *decide*: a neutral means the
  reducer gets a small step budget for the spelling and past it the input is
  the answer; a former means the reducer runs as before to spell it; out of
  fuel is the answer too (2026-09-29: the reducer, sharing nothing, never
  finishes on less fuel than the machine ran out of, and asked anyway it
  copied a generated program's code for twenty CPU-minutes to agree —
  `issues/closed-length-facts-evaluate-encodings.md`). The only
  value→syntax step is a former with no sub-structure (`Nat`, `Ty l`,
  `Unit`, `Empty`, `sEmpty`, and their codes), which is its own readback and
  is never evaluated again — the invariant below holds as stated.

**The invariant that keeps the exponential out of readback**, stated so a
future round cannot quietly reintroduce it:

> **No value is ever converted back into syntax that is then evaluated.**
> There is no `eval ∘ readback` round-trip in the kernel. `eval` is called
> only on syntax that came from the elaborator, from `Defs::body`, or from
> `beta_elim_*`'s fired branch — never on the output of a value.

That is grep-checkable (the absence of a `readback` symbol) and it is why
the exponent cannot re-enter through this door: the door does not exist.

**The trigger for revisiting.** If a metaprogram-heavy workload ever makes
`typing.rs`'s whnf hot, the fix is to move typing to values too — which
*then* requires either a readback or a value-carrying `tm_check`. That is a
separate round with its own measurement, and it should not be pre-paid here.

---

## 8. Bounds metadata

`bounds.rs` computes per-node free-local-variable bounds, memoized by `Rc`
address, so `SubstLocal`/`ShiftLocal` can skip provably-unchanged subtrees.
It is **21% of the deep-path profile** at a 70% skip rate.

**What stops needing it:** conversion. Every `apply_local` on the conversion
path — eliminator β's branch instantiation, `tm_ne`'s motive instantiation,
the η arms' shifts, `Conv::subst`'s prefix application — is replaced by
environment extension or closure application, which touch no syntax at all.
The 21% does not shrink; it *leaves*, along with the 26% substitution
traversal it was accelerating.

**What still needs it:** `subst.rs`'s local operations survive for
`typing.rs` (motive instantiation, `ty_check`'s descent), for `crates/elab`,
and for the parts of the evaluator that remain syntactic — but note that
those are *other-namespace* operations (`shift_global`, `inst_univ`,
`apply_global`), and `bounds.rs` is local-namespace-only, so it does not
serve them.

**Decision: keep `bounds.rs`, and re-measure it after stage 2 rather than
pre-judging it.** Its own issue
(`issues/bounds-metadata-taxes-one-shot-checking.md`) records that the memo
is a *tax* on one-shot terms — an elaborated declaration built, checked once
and dropped — and pays off only on subtrees traversed repeatedly. After this
round, "traversed repeatedly" is exactly the workload that leaves. The
honest prediction is that the memo's remaining customers are almost all
one-shot and the machinery should then be **deleted**, not tuned; but that is
a measurement, and it belongs to the cleanup stage (§13 stage 4), not to
this document.

---

## 9. SProp and definitional irrelevance

The TYPES 2024 CCobs implementation (Sirman, Lennon-Bertrand, Krishnaswami,
*Implementing a Type Theory with Observational Equality, Using Normalisation
by Evaluation*, DOI 10.4230/LIPIcs.TYPES.2024.5) reports a **negative
result** that is directly aimed at this round: their NbE needed a bespoke
*irrelevant semantic domain*, and they went through three designs to get it.
`docs/sprop-design.md` chose a whnf-based syntactic kernel partly on that
evidence, and `sEq`/`srefl`/`transp`/`sEmpty` have since landed.

So the question is sharp: does moving to a value domain buy back their
problem?

**Decision: no, and the reason is structural — Heather compares, it does not
normalize.**

Their difficulty arises because NbE *normalizes*: a proof term gets
evaluated and read back into a normal form, and if irrelevance is to be
definitional, the domain itself must identify all proofs of an irrelevant
type — otherwise two convertible terms have distinct normal forms. That
forces irrelevance *into the semantics*.

Heather's conversion never normalizes. It reduces each side to **weak head**
form and compares **type-directed**, and the three irrelevance arms
(`Type::Unit`, `Type::SEq`, `Type::SEmpty` in `tm_nf`) accept *any* two
terms without inspecting either. Under values those arms are unchanged
character-for-character: the type value's head is `VUnit`/`VSEq`/`VSEmpty`,
and the arm returns `Ok(())` without touching the term values. A proof is
never forced, never normalized, never read back — so there is nothing for an
irrelevant domain to fix.

Three specific checks:

1. **The `transp` strip transplants, and gets cheaper.** `Conv::strip` today
   whnfs the term, sees a `Transp` head, guard-compares the endpoints, and
   re-whnfs the payload. Under values: the whnf'd value is a neutral whose
   spine ends in an `ETransp` elimination; the endpoints are already values;
   the payload is already a value (it was evaluated in the closure's
   environment). The loop is the same loop with the re-whnf deleted. Guard
   semantics are §6's, unchanged, including the `spend()` per successful
   strip.
2. **The derived closure properties survive.** §1 of `docs/sprop-design.md`
   argues that irrelevance is closed under Π/Σ/Unit *compositionally*,
   because `tm_nf`'s η arms recurse into the codomain and hit the
   irrelevance arm there. Closure application preserves that argument
   exactly — the recursion is the same recursion.
3. **The □ firewall is structural, not disciplinary** (§3.5). Neither the
   strip nor irrelevance can reach inside a `box`, because a box value has
   no environment.

**The coupling, stated so both documents carry it.** The reason this works
is the *absence of readback* (§7). If a future round adds a normal-form
readback — for a `normalize` API, for prettier diagnostics, for a cached
normal form — it walks straight into the TYPES 2024 result and owes the
bespoke irrelevant domain. So:

> **Invariant (shared with `docs/sprop-design.md`): the kernel has no
> normal-form readback. Adding one is an SProp design round, not a
> convenience.**

The known algorithmic-vs-declarative gap recorded on the SProp round — the
strip is head-only, so a stuck-but-strippable `transp` is opaque to
elimination contexts — is neither widened nor narrowed here. It is a
property of where the strip is keyed, not of how reduction is implemented.

---

## 10. The strict-let alternative, priced

The alternative worth pricing (and worth writing down so nobody
re-litigates): give the *object language* a way to force a value — a `seq`/
`force` former, or a strict reading of an existing one — so that a
certificate author can force carried state and the rewriter never carries an
unforced redex.

**Decision: rejected. It does not change the class, and it is not a cheaper
interim.** Four independent reasons, in descending order of how conclusive
they are:

1. **Head-only forcing does not reach the class.** The issue's isolation
   experiment is decisive: `id_val(v) = match v { VNil => VNil; VCons(h,t)
   => VCons(h,t); VCon(a,b) => VCon(a,b) }` — a semantic identity, same
   values, same step count, one wrapper — turns flat into ~×2 per level. A
   `seq` on that value forces the head, gets `VCons(h,t)`, and stops: `h`
   and `t` are still redexes, still carried, still re-forced at every
   enclosing level. Head-only whnf is exactly what the kernel already does.
2. **A deep force on data does not reach it either.** The exponent's carrier
   in the acceptance probe is the *branch bundle* — the pending
   continuation — not the `Val` being computed. `List(Val)` is data and a
   deep force could canonicalize it; the arm-nested `LetMatch`'s pending
   `rest` is a term of the interpreter, and no data-directed force touches
   it. The step-machine round already demonstrated the same asymmetry from
   the other side: it made every *frame return* exponential while leaving
   the data flat.
3. **The ch. 04–07 bill is the wrong shape.** A kernel `force` needs a
   reduction rule keyed on a *deep* normal-form predicate, which is not a
   weak-head rule: ch. 06's grammar, Determinacy, Preservation and Soundness
   lemmas are all stated over weak-head reduction, and `docs/ch05-06-lemma-audit.md`
   would gain a column of new cases. It is a new former (`docs/wf-former-design.md`'s
   bill: syntax, typing, reduction, conversion, five transcriptions, the
   code recursors gain branches — `Wf` cost eight) plus a novel *kind* of
   reduction rule. NbE, by contrast, adds **no rule at all** (§11).
4. **It would be unavailable where it is most needed.** Layer c does not
   compute, so a `force` inside a `box` must be inert — and certificates
   about code are exactly the workload
   `issues/end-to-end-compile-instance.md` is heading for.

**The one honest concession**, recorded so the rejection is not
overstated: for a *specific* certificate whose cost is dominated by a
deeply-nested first-order `Val` (not a continuation), an in-language
canonicalization pass would help, and it needs no kernel change at all —
it is just a function. Nobody should reach for it before measuring that
their probe is data-dominated, and the two probes measured so far are not.

---

## 11. Metatheory obligations

### 11.1 What does not change — stated precisely

- **No ch. 04 rule changes.** No new former, no new binding form, no new
  judgment, no change to any existing rule's premises or conclusion.
- **No ch. 06 rule changes.** The reduction relations `⇝` (types and terms)
  and the nine convertibility judgments are exactly as they are today,
  including the definitions round's δ rule and the `sEq` round's strip.
- **No ch. 07 obligation is created.** The logical relations interpret the
  *declarative* system; the declarative system is untouched. In particular
  the definitions round's outstanding bill
  (`docs/metatheory-ch07-extensions.md` §26: definitional glueing at p,
  neutrality at c, the FT `u`-cases, δ's termination) is neither discharged
  nor enlarged by this round — glued *evaluation* is an implementation of
  the δ rule, not a new semantics for it.
- **Ch. 08's Convertibility and Decidability theorems** are unaffected in
  statement. What changes is which *implementation* claims to decide the
  relation they are about.

### 11.2 The one new obligation: algorithm equivalence

The kernel currently claims "conversion is ch. 06 verbatim". After this
round the claim splits, and the new half must be discharged:

> **Machine adequacy.** Define a relation `v ⊩ w` between values and ch. 06
> weak head normal forms, by induction on the head constructor: heads must
> agree; non-binder children are related pointwise; a closure `c` is related
> to a body `b` when, for every value `a` related to a term `s`, `c(a)` is
> related to the ch. 06 whnf of `b[s/x]`; a box value's payload must be
> syntactically equal; a neutral's spine must be related eliminator-wise and
> its head identical.
>
> **Completeness.** If `t ⇝* w` (ch. 06, with δ, at a computing layer) and
> `ρ ⊩ γ` then, given sufficient fuel, `eval(t, ρ)` succeeds and
> `eval(t, ρ) ⊩ w`.
>
> **Soundness.** If `eval(t, ρ)` returns `v` then there is a `w` with
> `t ⇝* w` and `v ⊩ w`. This is the half that forbids the evaluator from
> inventing reductions ch. 06 does not have — the one that matters for the
> trusted base.

**Against which fuel policy.** Both halves are stated on the *unbounded*
relations; fuel is a separate totality device, and its property is stated
independently and is the one §6 protects:

> For every budget, `eval` either returns a value satisfying Soundness, or
> `OutOfFuel`. It never returns a value that fails Soundness, and it never
> converts exhaustion into a verdict.

**Then conversion follows** from an "arms respect `⊩`" lemma: each `ty_nf` /
`tm_nf` / `ty_ne` / `tm_ne` arm makes the same decision on `⊩`-related
inputs as it does today on the syntax. One case per arm; this is the bulk of
the argument and it is mechanical, because the arms are being rewritten
one-for-one rather than restructured.

**Two hand-checked cases** outside the mechanical pattern, both flagged in
§3.3: `Clo::Native` for `elim_W`'s and `elim_Wf`'s synthesized ih λ. Their
adequacy is the statement that the native closure computes exactly the term
`reduce.rs` builds today.

### 11.3 What `DESIGN.md`'s "ch. 06 verbatim" becomes

Current text: *"Conversion is ch. 06 verbatim plus δ: untyped weak-head
reduction to WHNF/neutral, then structural comparison. Not NbE, not typed
reduction."*

Proposed replacement (to land with stage 2, not before):

> Conversion **decides** ch. 06's relation, plus δ: weak-head reduction to
> WHNF/neutral, then structural comparison, still untyped and still not
> typed reduction. Its *reduction engine* is an environment machine over a
> value domain (`docs/nbe-conversion-design.md`) rather than a term
> rewriter, adopted to kill the exponential of
> `issues/whnf-sharing-term-growth.md`. `reduce.rs` remains ch. 06's
> relation transcribed rule for rule and is the specification the machine is
> proved adequate against; the differential test suite is the standing
> evidence.

The distinction being preserved: **"verbatim" moves from the algorithm to
the specification.** That is a real weakening of the trusted-base story and
should be stated as one — the compensating controls are the differential
oracle (§2), the adequacy statement (§11.2), and the fact that the
declarative system did not move.

### 11.4 Where it gets written

**Decision: not a Part V of `docs/metatheory-ch07-extensions.md`, and not a
standalone metatheory note.** That document is the *ch. 07 pen-and-paper
pass for extensions to the declarative system* — Parts I–III are logical
relations for new formers, Part IV is a new binding form's rules and its
owed LR work. This round extends nothing declarative and owes ch. 07
nothing; filing it there would make the document's own scope untrue.

Instead: **§11 of this document is the record**, and two small
cross-references land with it —

1. one line at the head of `docs/metatheory-ch07-extensions.md` noting that
   the NbE round creates no ch. 07 obligation and pointing here (so a reader
   of that document does not have to derive the absence);
2. an entry in `docs/ch05-06-lemma-audit.md`'s ch. 06 section for the
   adequacy statement, since that document is exactly the register of
   "what the paper states, what the kernel checks, where the gaps are", and
   adequacy is a ch. 06-level property with a verdict (initially **○ —
   open gap**, becoming **✅** when the differential suite lands).

---

## 12. The spike (2026-07-31)

**Question:** can the acceptance instrument — the arm-nested probe, linear
in N — be built as a *kernel* bench family? The bench suite cannot call the
elaborator, so a kernel-term
reconstruction of the probe would be much cheaper to run and to gate on
than an elaborated `.hthr` file.

**Method.** Throwaway worktree, release build, `scripts/test`, three
hand-built kernel term families, conversion against the expected numeral,
timed per level. (The worktree is gone; nothing landed.)

| probe | shape | result over the sweep |
|---|---|---|
| A: branch-nested | `nest(d,e) = elim_Nat (_.Nat) 0 (x,y. nest(d-1,y)) (su e)`, d = 1..9 | **linear**, per-level ratio 0.8–1.5 (noise-dominated, 0.02–0.06 ms) |
| B: interpreter-shaped | one self-referential `elim_Nat` over a fuel index, step body `λn. elim_Nat (_.Nat) 0 (a,b. CONT) (app y n)` — ih in **scrutinee** position, continuation after it, F = 1..14, pad 1 and 16 | **linear**, ratio 0.9–1.4 |
| C: B with a second, never-forced ih occurrence in the dead branch | as B, `CONT = su^pad (app y b)` | **linear**, ratio 0.9–1.5 (max 1.87 once, not sustained) |
| D: C's carried argument moved to **binder depth 1** (stage 0, 2026-07-31) | `E(d+1) = λw. E(d) (fst⟨w, (λu. E(d) w) 0⟩)` — the carried argument is duplicated under a λ, where the depth-zero fast path cannot share it, and `fst` discards without forcing | **linear**, slope 1.44 over d = 1..12 (1.2 → 38 µs), per-level cost flattening from 1.2 to 3.2 µs |

**Finding: the exponent does not reproduce from the *shape* alone.** All
three families have non-tail recursion, a branch that mentions free locals
(so `bounds.rs` cannot skip it), and — in C — a duplicated induction
hypothesis. All three are linear. Family D was built later, during stage 0,
against this section's own explanation — `subst.rs`'s doc says in as many
words that "a payload inserted under `k > 0` binders still costs a full
copy", so D forces the duplication to happen at depth 1 — and it is linear
too. Four families, one conclusion.

**Best explanation, and it is already in the issue.** The issue's dead
hypothesis 3 measured pointer sharing in the *real* workload at **0.05%**
(39 810 hits in 75.9 M visits): "sharing is already gone by the time the
substitution runs". In these small hand-built terms it is *not* gone —
`subst.rs`'s depth-zero fast path returns an `Rc::clone` of the payload, so
a duplicated ih is one allocation, not two, and re-forcing walks it once.
What destroys that sharing in the elaborated interpreter is *shifting*:
payloads inserted under binders get renumbered, which forces a physical
copy. Reconstructing the exponent therefore requires reconstructing the
binder depth and term bulk of the real interpreter — which is
`lib/ir_v1.hthr`, not a fixture.

**Consequences for the plan, and they are not cosmetic:**

1. **The acceptance gate is the elaborated probe, driven at CLI level**
   under `(ulimit -v 8388608 -t 120; …)`, not a kernel bench family.
2. **The instrument must be validated on master before it gates anything.**
   A family that is linear on master proves nothing when it is linear after.
   This is now stage 0 with its own kill criterion (§13).
3. A kernel bench family remains *desirable* (it would run under
   `scripts/bench --check` with an `expect_slope` band like every other
   family) but it is **not** a precondition, and deriving one is explicitly
   sized as speculative.

Secondary finding, recorded because it is cheap and useful: the naive
"nested non-tail recursion is exponential" reading of the issue is too
strong. The title's own caveat — "the instance, not the class" — cuts both
ways: nesting is *necessary* for the observed exponent, and these three
probes show it is not *sufficient*.

---

## 13. Staged plan, with acceptance per stage

Sizes in units of **the definitions round** (one long agent session:
`GlobalBinding::Tm`'s body field, layer-indexed transparency, δ-lazy
conversion, tests, benches, docs, the ch. 07 bill written up).

### Stage 0 — the instrument (0.3)

Build the arm-nested probe as an elaborated `.hthr` file (N = 1..8, the
`LetMatch`-in-arm shape the issue isolated), plus a CLI-level acceptance
test that runs each N under the ulimit wrapper and records wall time and
peak RSS. **Validate it on master**: the per-level ratio must be ≥ 1.8
across at least four consecutive levels.

*Gate:* the master curve is recorded, in the issue and in the test's own
comment, with the ratio.

**Kill criterion — the whole round's:** if no probe reproduces ≥ 1.8 per
level on master, stop. There is then no instrument that can tell the fix
from a no-op, and the correct next action is to re-open the diagnosis, not
to rewrite `conv.rs`. §12 is why this stage exists and why it is first.

Optional, speculative, not on the critical path: try to derive a kernel
bench family with the same ratio, informed by §12's explanation (force the
binder depth up so payload sharing is destroyed). If it works, it is a
better gate; if it does not, say so and move on.

### Stage 1 — value domain + evaluator, unwired (1.5)

`crates/kernel/src/value.rs` (the domain of §3) and `eval.rs` (`eval`,
`apply`, `force`, the glued-neutral machinery of §5, the other-namespace
maps of §3.1). Not called by `conv.rs`. Reuses `beta_elim_*` and `rec.rs`
verbatim.

`crates/kernel/tests/eval_differential.rs`: over `wt.rs`'s well-typed
generator, across ≥ 4 seed streams, assert `eval(t, ρ_Γ) ⊩ whnf(t)` by a
head-shape comparison that recurses one level through forcing —
`law!`-style, **seed-only** on failure. Cases must include open terms in a
non-empty Γ, all three `CtxBase` shapes, boxed code, code recursors, and a
definition-carrying Ψ.

*Gate:* `scripts/test` green; `scripts/bench --check` unchanged (nothing is
wired, so any movement is a bug).

### Stage 2a — make the comparison arms shape-agnostic (0.7)

Refactor `ty_nf`/`tm_nf`/`ty_ne`/`tm_ne` to reach their inputs through a
small accessor trait (head discriminant + typed children), still
instantiated at syntax. **No behaviour change, no test change.** This exists
solely to make stage 2b a instantiation rather than a rewrite, because
stage 2b is otherwise atomic and atomic is the risk.

*Gate:* `scripts/test` green, `scripts/bench --check` at baseline (a
refactor that costs 1.25× is a failed refactor — precedent: the `sEq` round's
whnf-wrapping helper cost 1.35× on `conv/computed-numeral` and was caught
exactly this way).

### Stage 2b — switch conversion to values (1.5) — **the riskiest stage**

Instantiate the accessor trait at values; replace the four whnf helpers with
`eval`/`force`; delete `delta_head`/`delta_head_ty` (§5); move the η arms to
closure application; move `tm_ne`'s inferred types to closure
instantiation; move `Conv::subst` to value comparison (§3.4). Keep the
rewriter path selectable for the duration of this stage so a
conversion-vs-conversion differential can run over
`conv_pair_properties.rs`'s corpus.

*Gate:* full `scripts/test` green including `conv.rs`'s golden suite,
`definitions.rs`, `seq_transp.rs`, `wf.rs`, `acc.rs`; the
conversion-vs-conversion differential green over ≥ 4 seed streams;
`scripts/bench --check` (expect improvements — re-save the baseline, and
expect the fuel-threshold tests of §6 to need re-recording); **stage 0's
probe linear in N**; `conv/simulate-depth` and `conv/simulate-payload` still
within their slope bands; routine `lib/ir_v1.hthr` not regressed.

**Kill criterion:** if the conversion-vs-conversion differential shows a
disagreement that is not traced to a *rewriter* bug within one session,
revert to master. Stage 1's evaluator keeps its value as an oracle-side
artifact and the round is re-scoped, rather than a half-migrated `conv.rs`
being nursed.

**Why this is the riskiest stage:** it is a single migration of a
1852-line trusted file whose correctness is observable only through tests,
it changes the meaning of every fuel-sensitive assertion in the suite, and
its failure mode — a conversion that accepts a pair it should reject — is
soundness, not performance. Stage 2a exists to shrink it; nothing can make
it small.

### Stage 3 — δ glueing (0.7)

Memoized `unfold` thunks on glued neutrals; the rescoped-body cache keyed by
`GlobalVar` (§5). Separated from 2b so that a δ regression is attributable.

*Gate:* `definitions.rs` green in both directions (transparency at p,
opacity at c); `conv/perturbed-pairs` and `conv/computed-numeral` not
regressed; the `has_defs`-gate's 1.35–1.43× lesson re-checked — i.e. a Ψ
with **no** definitions must be no slower than before.

### Stage 4 — cleanup and the record (0.5)

Remove the selectable rewriter path from `conv.rs` (keeping `reduce.rs`
itself). Reword `DESIGN.md` per §11.3. Land the two cross-references of
§11.4. **Re-measure `bounds.rs`** (§8) and update
`issues/bounds-metadata-taxes-one-shot-checking.md` with the verdict —
delete-or-keep, with numbers. Update
`docs/testing-generated-terms.md` if the differential pattern earns an axis.

*Gate:* `scripts/test`, `scripts/bench --save` with a clean `--check` on the
following run, issue log entries.

### Totals

≈ **5.2 definitions-rounds**, of which stage 2b is the irreducible core.
Stages 0, 1, 3 and 4 are independently landable and independently valuable;
2a is a no-op refactor that is worth landing even if the round stalls.

---

## 14. Deliberately rejected, each with its reason

- **Full NbE with readback and normal forms** — buys nothing conversion
  needs, and walks into the TYPES 2024 irrelevant-domain problem (§9).
- **Explicit substitutions in `Term`** — comparable metatheory bill, worse
  novelty (§1).
- **A `force`/`seq` former** — does not change the class, wrong-shaped
  ch. 04–07 bill, unavailable at layer c (§10).
- **A layer-indexed evaluator** — encodes a one-bit decision twice (§4).
- **Level values** — there is no level redex (§3.1).
- **Making `LocalCtx` a value** — Δ is always a different local scope, and
  conversion already compares contexts entry-by-entry (§3.4).
- **Migrating `typing.rs` in this round** — it is cold, and keeping it on
  the rewriter is what removes readback from the design entirely (§7).
- **Trusting a differential equality test as the sole gate** — blind to
  sharing regressions by construction (§2, and `subst_laws.rs` says so about
  itself).

---

## 15. Related work

- **Sirman, Lennon-Bertrand, Krishnaswami, TYPES 2024** (CCobs via NbE),
  DOI 10.4230/LIPIcs.TYPES.2024.5. Two things Heather takes from it: the
  cast-strip belongs in *conversion*, not reduction (already independently
  reached — `docs/sprop-design.md` §5.2), and the negative result about
  irrelevant semantic domains, which §9 argues does not bite a
  compare-don't-normalize kernel and which §9 also converts into a standing
  invariant.
- **Abel, Öhman, Vezzosi, *Decidability of conversion for type theory in
  type theory*** — the shape of the adequacy argument in §11.2 (a logical
  relation between a value domain and the syntactic reduction) is theirs;
  ours is easier because there is no readback to relate.
- **DeLaM itself uses no evaluation-style algorithm anywhere.** Ch. 06 is
  untyped weak-head reduction plus structural comparison; ch. 03's
  normalization for the warm-up system is a logical-relations argument over
  the *same* syntactic reduction; ch. 08 argues decidability by mutual
  induction on convertibility derivations. There is no NbE in the book to
  transcribe, which is exactly why §11.2's obligation is ours and why
  `reduce.rs` must survive as the thing the machine is measured against.
