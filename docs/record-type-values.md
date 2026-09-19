# Record types as type-valued function values

Status: **landed**, 2026-08-01. Tracking issue:
`issues/record-types-as-type-valued-functions.md`. Sibling round:
`docs/constructor-function-values.md` — same disambiguator, pointed the other
way. Follow-on: `docs/record-type-partial-application.md` (2026-09-19) takes
§2's routing one arrow further, so a *prefix* of the value-parameter telescope
is enough and the wrapper `fn` this document's §1 writes by hand is no longer
needed. Prerequisites: `docs/types-as-expressions.md` (a `fn` returning `Type` is
an ordinary `fn`) and `docs/surface-value-parameters.md` §3 (`D(v̄)` in type
position).

---

## 1. What was missing

`docs/types-as-expressions.md` made a *written* type-valued `fn` first class.
A **declared** record did not get the same courtesy:

```heather
record Boxed(v: Nat) { pf: v = v, }

fn mk(v: Nat) -> Boxed(v) { Boxed { pf: refl } }        // ok: type position
fn IsZero(v: Nat) -> Type { v = 0 }                     // ok: fn at Type
fn AllOf(dom: Nat -> Type) -> Type { (n: Nat) -> dom(n) }
fn UseIsZero() -> Type { AllOf(IsZero) }                // ok

fn BoxedT(v: Nat) -> Type { Boxed(v) }                  // was an error
fn UseIt() -> Type { AllOf(λ (v: Nat) => Boxed(v)) }    // was an error
```

Both failures reported the *constructor*'s problem — "cannot infer the value
argument(s) of `Boxed` … put the expression in a checking position" — which is
wrong twice over: `fn BoxedT(v: Nat) -> Type { … }` **is** a checking
position, and `v` is written rather than field-determined. The constructor arm
was never reached; the error came from inference, because the universe arm
that runs *before* it could not read `Boxed(v)` as a type and fell through.

## 2. The scheme: a routing decision, not a second lowering

`elab_check_hinted` already dispatches on `expected` being a universe before it
looks at constructors, and hands off to `elab_at_universe`. That function reads
the expression *as a type* through the free `expr_as_ty`, whose domain is "a
name, an applied name, or a universe" — where **applied name** meant only
`ExprKind::TyApp` (`List<Nat>`), never `ExprKind::App` (`Boxed(v)`). So the
whole round is one more reading, and the reading is the one that already
exists:

```
D<ā>(v̄)  ⇐  Ty l   ⇝   elab_ty(TyKind::OfExpr(D<ā>(v̄)))   then code_of
```

`TyKind::OfExpr` is what the *parser* hands the elaborator for the same text
one syntactic slot over (a type annotation), and `elab_ty`'s handler for it
runs `try_indexed_ty`, then `try_valparam_ty`, then the generic
infer-and-decode. Routing there rather than re-deriving the lowering is the
constructor round's lesson applied verbatim (§3 there: a second copy of the
field-layout knowledge is what goes stale). Indexed families and monomorphized
type parameters therefore come along for free — `Vec<Nat>(n)` and
`Boxed<A>(v)` at `Type` work because their handlers were already on that road.

`crates/elab/src/lib.rs`:

- `type_former_app` — recognizes the new shape: an `App` whose head names a
  declared inductive and is not shadowed. Returns the `OfExpr` reading.
- `elab_at_universe` — tries `type_former_app` **first and committed**, then
  `expr_as_ty` as before; `quote_type_at` is the level check plus `code_of`,
  factored out so both readings quote identically.

### 2.1 Why the ambiguity resolves this way, and why "committed" matters

`docs/constructor-function-values.md` decided that a constructor name in
expression position means the constructor, using the expected type to
η-expand. That stays. The disambiguator here is the same one: **no constructor
inhabits a universe**, so when `Type` is expected the type-former reading is
not a heuristic but the only well-typed one.

That is also why the new branch does not fall through to inference when it
fails. `expr_as_ty`'s branch is deliberately best-effort (`if let Ok(…)`) —
`g(A)` and a variable at `Ty n` reach that position too and must still infer.
The type-former branch has no such competitor, so an error inside it is *the*
error, and reporting it is what keeps the arity diagnostic pointed at the
value-parameter telescope:

| Written at `Type` | Message |
|---|---|
| `Boxed(v, v)` (telescope of 1) | "`Boxed` takes 1 value argument(s), found 2" — `valparam_args`, unchanged |
| `Eqn(n)` (telescope of 2) | "`Eqn` takes 2 value argument(s), found 1" — likewise |
| `Plain(0)`, no value parameters | "`Plain` takes 0 value argument(s), found 1 … write it bare" — new, see below |
| `Boxed(v)` at `Type<1>` | the non-cumulativity message, unchanged |

The third row is the one line of new diagnostic. A declaration with an *empty*
telescope has no handler inside `elab_ty` — `try_valparam_ty` declines on
`valparams.is_empty()`, by design, so that every pre-existing spelling reaches
its old handler — so `type_former_app` says it itself rather than letting the
generic path try to *call* `Plain`.

### 2.2 What stays rejected

**Inference position**, exactly as the constructor round left bare unsaturated
constructors: `let T = Boxed(v);` is still the constructor's inference error,
because no expected type has selected a reading. That is the same boundary
sentence — "needs a checking position" — and both of the issue's motivating
examples are on the right side of it.

**Monomorphized type parameters** are out of scope by the issue's own fence:
`Monoid<Nat>` and `Monoid<Bool>` are unrelated kernel types
(`docs/surface-records.md` §1.1), so `Monoid` as a `Type -> Type` *value* is
not expressible under the current polymorphism model at all. `Monoid<A>(v)`
with `A` open **is** expressible and works (§5.3) — the fence is on abstracting
the type argument, not on having one.

**Value parameters on a non-record `inductive`** are still rejected at
declaration time (`docs/surface-value-parameters.md` §6), so the "does a plain
inductive come along?" question has only two answers here, and both are yes and
cheap: a *bare* inductive name at `Type` already worked (`expr_as_ty`'s `Named`
case), and an *applied* one is now the §2.1 arity message instead of a
constructor error. An indexed family applied to its index rides
`try_indexed_ty`.

---

## 3. Cost

`crates/elab/src/lib.rs` `type_former_app` + `quote_type_at` + the branch, and
two follow-on repairs (§4) that the motivating consumer — not the repro —
forced. No kernel change, no parser change, no new AST node.

---

## 4. What implementing it corrected: two more `El` readers

The routing arm alone makes the issue's repro check. It does **not** make the
consumer work, and the reason is the standing hazard of
`docs/types-as-expressions.md` §4: `El ⌜T⌝ ⇝ T` is a *lazy* decode, and now
there is a new way for a type to arrive wrapped.

A record type reached through a `Val -> Type` **value** is
`El (⌜λ e. NatEnv(e)⌝ env)` — `El` of a **β-redex**, not of a canonical code.
`inductive.rs`'s `decoded` is deliberately context-free and strips `El` off
canonical formers only, so it declines, correctly. Two readers below it then
failed:

| Reader | Symptom | Fix |
|---|---|---|
| `record_of` (via `tag_of`), from `resolve_dot` | `d.shape` → "this is not a record, so it has no field `shape`" | `record_of_at`: try the structural read, and only if it fails pay one `whnf` |
| `unify_ty`, from `apply_implicit` | `sym(d.shape)` → "could not infer the implicit argument `b` of `sym`" | `decoded` the **subject** before the congruence walk |

Both are minimal on purpose:

- `record_of_at` keeps `resolve_dot`'s ordering doctrine intact. The cheap
  negative test (is `f` anybody's field?) still comes first, and the structural
  `record_of` still comes before any reduction, so no receiver that resolved
  before pays anything new. Only the shape that used to *fail* reduces.
- `unify_ty` decodes the subject **after** the pattern's own `El ?A` rule,
  which must keep seeing an undecoded subject so that a meta at a type solves
  whole rather than descending into a code. `decoded` adds no δ and consults no
  context, so the walk stays the pure syntactic matcher it was.

`project_field` needed nothing: it already `whnf`s at every spine step.

The honest reading of this table is that the round's real content was **half
routing and half the fifth and sixth entries in types-as-expressions §4's
table**. Anyone adding a new structural reader of a lowered type should assume
it is on that list until a test says otherwise.

---

## 5. Acceptance

`crates/elab/tests/record_type_values.rs`, seven tests. Every positive one is
elaborated and re-checked by the real kernel, and — following
`docs/testing-generated-terms.md` — every one *uses* the type it built rather
than only elaborating it, since a term that merely sits at `Type` proves
nothing about being the right type.

1. **The repro.** `BoxedT`, the λ-wrapped form, both flowing into `AllOf`, plus
   inhabitants: `AllOf(BoxedT)` is proved, `BoxedT(3)` (literal argument) and
   `BoxedT(v)` (neutral argument) are inhabited, and the wrapper is shown
   convertible with the type-position spelling in both directions.
2. **The payoff, in miniature** (`a_record_domain_can_be_projected_and_
   transported`): a `dom: Nat -> Type` consumer whose hypothesis is a record
   value, with the proof projecting a field off it and transporting along it —
   `j(sym(d.shape), …)`. This is `lib/ir_v1.hthr`'s `RefinesOn` shrunk to one
   file, and it is the test that pins both §4 repairs.
3. **An open element type.** `record Boxed<A>(v: Nat) { val: A, … }`, used as
   `Boxed<A>(v)` inside a declaration whose `A` is open, alongside two closed
   instantiations in the same file whose projections compute.
4. **A field-determined value parameter** — the shape the old message
   complained about — at a universe, with the argument written.
5. **Negative control, the constructor reading.** The record literal, the
   positional constructor, and the unsaturated η-expansion at a Π all still
   mean the constructor, and agree with each other by `refl`.
6. **Negative controls, the diagnostics.** Each row of §2.1's table, plus the
   inference-position boundary (`let T = Boxed(v);` still says "infer").
7. **Shadowing.** A `dom: Nat -> Type` *parameter* named `Boxed` is called, not
   lowered — the routing arm consults `shadowed` before `inductives`.

`lib/ir_v1.hthr` is the acceptance at scale: `RefinesOn(dom: Val -> Type, p1,
i1, p2, i2)` is now written once and generally, `RefinesNat2` is defined as
`RefinesOn(λ (e: Val) => NatEnv(e), …)` over a `NatEnv` record packing the two
embedded arguments, the tail, and the shape proof, and both refinement
directions are re-proved through it. Release check time is unchanged
(41.2s against a ~41s baseline): the added transport is one `j` per direction,
and the δ-stuck `RefinesNat2` head compares before it unfolds.

---

## 6. The audit: the whole roster of `El` readers

Status: **landed**, 2026-08-01. Tracking issue:
`issues/el-reader-decode-audit.md`.

§4 ended with "treat the list as open". This section closes it. Every
structural reader of a *lowered* `Type` in `crates/elab` was enumerated and
tried against a type that arrived wrapped, in both spellings:

- **δ** — a named type-valued `fn` (`fn B(v: Nat) -> Type { Box2(v) }`), which
  is `docs/types-as-expressions.md`'s shape: `El` of a call to a global;
- **β** — a `Nat -> Type` (or `Val -> Type`) function *value*, applied
  (`Dom()(n)`, `HoldsOn(λ (v: Nat) => Outer(v))`), which is §4's shape and the
  one conversion cannot pre-collapse.

Two things came out that the sweep was not looking for. First, **the shape
reaches readers with no function value anywhere in sight**: `El ⌜T⌝ ⇝ T` leaves
the children wrapped, so a record's *field* types are `El`-headed whenever the
record itself was read as a code — which is how the vector readers below were
reached. Second, four of the six repairs are for the **δ** spelling, i.e. they
were already broken by `docs/types-as-expressions.md` and nobody had asked.

### 6.1 Repaired

| Reader | Reachable how | Was | Fix |
| --- | --- | --- | --- |
| `Stmt::LetRecord`'s `record_of` (`lib.rs`) | the right-hand side is inferred, so any `dom(n)`-typed binder | "a `let { … }` pattern needs a record on the right" | `record_of_at` — the §4 fallback, which `resolve_dot` already used. `let { a } = p` and `p.a` are one feature (`docs/surface-records.md` §5); they now read their subject the same way |
| `indexed_of`, from `elab_match`, from inference-position `match`, and from `build_indexed_ctor` (`lib.rs`, `indexed.rs`) | `fn F(n: Nat) -> Type { V<Nat>(n) }` | "`match` needs a `Nat` or a declared inductive"; "the expected type here is not in that family form" | `indexed_of_at` — **not** a `whnf`; see §6.3 |
| `elab_vec_lit` (`lib.rs`) | a record with a vector field, read as a code: the component is `El (TmVec …)` | "a vector literal needs a `[T; n]` expected type" | `decoded` — **not** a `whnf`; see §6.3 |
| `elab_vec_map` / `elab_vec_fold` receivers (`lib.rs`) | the same component, projected | "`map`'s receiver has to be a vector" | `decoded`, same reason |
| the phase-3 motive test in `wf_branch` (`wf.rs`) | **naming the statement** of a container induction — `fn Agree(r: Rose) -> Type { size(r) = size_plus(r) }` | phase 2's rejection ("needs … an equation `a = b` at a type that is") | `motive_head`: one `whnf`, in a `(Γ₀, z : ⟦D⟧)` context rebuilt from what `Tel` already holds. `Id` *is* a weak-head normal form, so here `whnf` cannot overshoot |
| `cong`'s receiver test (`lib.rs`) | not today — the container binder's type is built by `wf.rs`, never decoded | — | `decoded` anyway: one line, and it is the third of three sibling readers of the same thing |

### 6.2 Already fine, and why

Everything below either reduces before reading or cannot receive a lowered
type at all. Each was exercised at the β and δ shapes where it can receive one
(`crates/elab/tests/el_reader_audit.rs`, the last three tests).

- **Reduce at the top.** `build_ctor`, `build_ctor_value`, `elab_lam_check`,
  `refl`'s `Id` read, `j`'s proof read, `apply_explicit` / `apply_implicit` /
  `elab_self_call`'s Π peels, `elab_check_hinted`'s universe fall-through,
  `equation`, `build_absurd`, `build_inj`, `elab_ty`'s `Ty l` check.
- **Reduce at every spine step.** `build_fields`, `project_field`,
  `projection`, the `match` arm field walks in `inductive.rs` and
  `indexed.rs`, `build_children`.
- **Reached only from an already-reduced subject.** `tag_of`, `spine`,
  `read_tag`, `tag_value` (all `decoded` besides); `elab_match_data`'s
  dispatch; `build_elim_wf` and `const_body`'s `Type::Wf` reads, which come
  from `elab_match`'s `head`.
- **Repaired in the previous round.** `record_of_at`, `unify_ty` (§4).
- **Cannot receive a lowered type.** `expr_as_ty`, `type_former_app`,
  `try_valparam_ty`, `try_indexed_ty`, `named_head`, `classify_fields`,
  `occurs` — these read the *surface* `Expr`/`Ty` the parser produced, and the
  lowering happens below them, not above.
- **Indifferent to the wrapper.** `code::code_of` — `El` is its identity case,
  so a wrapped type is already its own code. `vec::strengthen` — a scope test,
  structural over every former including `El`. `synth_motive` — substitutes
  and never inspects. `nat_value` and `elab_vec_lit`'s length check —
  term-level, below the wrapper entirely.

### 6.3 Why two of the repairs are not `whnf`

§4's fallback pays one `whnf` when the structural read fails. That is right for
a *record*: `Σ` is a weak-head normal form, so reducing to find one cannot go
past it. It is **wrong** for the two readers whose shape reduces further:

- `Vec` reduces **on its length**. The whnf of `[T; 0]` is `Unit` and of
  `[T; 2]` a Σ-chain — the very shape `elab_vec_lit` exists to recognize. So
  it uses `decoded`, the context-free single decode, which stops at `Vec`
  exactly. (`elab_vec_lit`'s pre-existing comment "*not* whnf'd" was right for
  a reason that has now been tested.)
- An indexed family reduces **on its index**. The whnf of `V<Nat>(0)` is the
  base branch's Σ-spine, index and all — which is precisely the loss
  `indexed_of`'s doc comment already described. So `indexed_of_at` steps the
  *code* one reduction at a time and re-runs the structural read after each,
  stopping at the **first** success. A redex above the `elim_Nat` is peeled;
  the `elim_Nat` itself is never reached, because the read succeeds the moment
  it surfaces. `F(0)` and `F(Succ(n))` are the two cases a single `whnf` would
  have destroyed, and both are pinned.

So the pattern generalizes to: *structural read first; then reduce as little as
possible, testing after each step.* §4's one-`whnf` fallback is that rule at a
former which happens to be a normal form.

### 6.4 No silent wrong results

`docs/types-as-expressions.md` §4's `tag_value` is the failure mode that
matters — a reader that falls through to a **default** (`⟨⟩` where a pair was
needed) rather than to a diagnostic, and so produces a checked theorem about
the wrong object. The audit found **none** of that kind. Every one of the six
readers above declined loudly, with a message, and the two fallbacks that
*could* have introduced the failure mode by over-reducing are exactly the two
that do not use `whnf` (§6.3).

The negative controls in `el_reader_audit.rs` are there to keep it that way:
the false theorem of the same shape as the container induction, named the same
way and discharged the same way, is still rejected; a named motive that is not
an equation still gets phase 3's message rather than a term; a vector literal
of the wrong length is still counted; a constructor of the wrong family at a
coded expected type still names the mismatch.

### 6.5 The rule of thumb, now stated once

A reader is on this list if it destructures a `Type` it did not build. There is
no shortcut for deciding whether it can receive a wrapped one — a *use* of
anything named (`fn … -> Type`, a record read as a code, a `Val -> Type`
parameter) puts an `El` in front, and the lazy decode keeps it in front of
every child. So: **reduce before reading, and if reducing can overshoot, step
and re-test.**
