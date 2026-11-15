# The Type Session: a surface universe

Status: **scheme**, written before the code per the discipline of
`docs/language/surface-function-types.md`, `docs/language/surface-polymorphism.md` and
`docs/kernel/wf-former-design.md`. §11 is the acceptance checklist; §12 is reserved
for what implementing it corrected.

Tracking issue: `issues/surface-universe.md`.

The kernel side is **free and has been since v0**. `Type::Ty(l)` is a type at
level `1 + l` (`typing.rs:457-460`), `TmTy(l) : Ty (1+l)` is its code
(`typing.rs:756-759`), `El` decodes it (`reduce.rs`), `conv.rs:291` compares
two `Ty`s by level equivalence, and `code.rs:31` already quotes `Type::Ty(l)`
to `Term::TmTy(l)`. So `Type<n> : Type<n+1>` is already true and already
expressible — the surface simply has no spelling for it. This is a surface and
elaborator round, the same risk class as function types, polymorphism and
records: **no trusted-base change, no ch. 07 obligation.**

What makes it a *session* rather than a round is that the missing spelling has
been load-bearing for four previous deferrals (issue §7), and adding it turns
three vacuous mechanisms — the level joins, the `Expr`/`Ty` bridge, the
`Type`-valued binder — into live ones at the same moment.

---

## 1. What the surface gains

```
ty_atom := "Type" ( "<" numeral ">" )?    -- Type<0>, Type<1>, …; Type = Type<0>
         | …                              -- unchanged
```

```heather
record Mon {
    carrier: Type,                        -- the bundled record, finally
    unit: carrier,
    op: carrier -> carrier -> carrier,
}

fn id_at(A: Type, x: A) -> A { x }        -- a Type-valued *value* parameter

theorem m(p: a = b): P(b) {               -- a motive is an ordinary function
    j(p, λ y q => P(y), …)                --   at (y: A) -> (q: a = y) -> Type
}
```

Three things are deliberately **not** in the grammar:

- **No level variables.** `Type<ℓ>` with `ℓ` a name is `UPi`, layer m (§7).
- **No level expressions.** `Type<n>` takes a *numeral*, not `Type<n+1>` or
  `Type<max(a,b)>`. Joins are computed by the elaborator, never written.
- **No `Lift`.** §6.

## 2. The lowering

`Type<n>` lowers to `Type::Ty(Level::constant(n))` at level `n + 1`. That is
the whole lowering, and it is one new arm in `elab_ty` (`lib.rs:813`):

```rust
TyKind::Univ { level: n } => Ok((Type::Ty(Level::constant(n)), Level::constant(n + 1))),
```

A binder at `Type<n>` then uses the existing type-parameter machinery, which is
what this round generalizes. Today `fn f<A>` pushes exactly this
(`lib.rs:373-381`):

```rust
let (ty, lvl) = (Type::Ty(Level::Zero), Level::constant(1));
cx.push(tv.clone(), ty.clone(), lvl.clone());
cx.tyvars.push(TyVar { ty: Type::El { level: Level::Zero, tm: Var(0) }, level: Level::Zero, … });
```

i.e. *bind at `Ty 0`, and use through `El⁰`*. The round takes that from "names
bound by a declaration's `<…>`" to **"any binder whose type is `Type<n>`"**:
`(A: Type<1>, x: A)` pushes `A : Ty 1` and records `⟦A⟧ = El¹(A)` at level 1.
`fn f<A>` stays sugar for a leading implicit parameter at `Type<0>` and needs
no separate path once the general one exists.

**Decision to make in phase 1:** whether `<A: Type<1>>` is spellable, or
whether the sugar stays fixed at `Type<0>` and above-zero binders must be
written in the parameter list. Recommend spelling it — it is one optional
grammar suffix, and a sugar that cannot say what the desugaring says is the
kind of gap that gets rediscovered as a bug.

## 3. Parsing: two collisions

Both live in `ty_atom` (`parser.rs:601`).

**`Type<0>` versus `D<A, B>`.** The applied-inductive rule (`parser.rs:626-651`)
fires on `Ident` followed by `<` and parses each argument with `ty()`. `0` is
not a type, so `Type<0>` would fail with *"expected a type"*. The `Type` rule
must therefore be tried **before** it, and must parse a numeral rather than a
`ty()`.

**Bare `Type`.** With no `<…>`, `ty_atom` falls through to `self.expr()` and
reinterprets a `Var` as a type name (`parser.rs:661-666`), so `Type` currently
becomes `TyKind::Named { name: "Type" }` and the elaborator says *"unknown type
`Type`"*. The fix is symmetric with how `Nat` is already handled one line
above: match the name. No new token, no lexer change.

Consequence: **`Type` becomes reserved in type position.** A user inductive
named `Type` stops being referable. That is a rejection with a message (§9), not
a silent shadow.

## 4. The `Expr`/`Ty` bridge, and why a retired coercion comes back

A motive written as a λ is an *expression whose body is a type*. Handling that
means reading an expression in a position expecting `Ty l` — which is precisely
the coercion `docs/language/surface-polymorphism.md` §5 **implemented and then retired
the same day**. That section's lesson is worth quoting, because this round has
to answer it rather than walk past it:

> The coercion was a feature invented to paper over a spelling collision, and it
> survived exactly as long as the collision did.

**Why it comes back, and why that is not a relapse.** The retirement was correct
*because no position had expected type `Ty l` any more*: `<…>` took over writing
type arguments and `@` stopped making type parameters positional
(`issues/at-and-type-arguments.md`), leaving the arm as dead code — which is
exactly what `lib.rs:950` is today, a message rather than an elaboration. This
round **creates the position for a real reason**: a parameter *declared*
`(A: Type<0>)` takes a type in an argument slot, and a λ *declared* at
`(z: A) -> Type` has a type as its body. The position is now stated by a
declaration rather than conjured by a spelling.

Mechanically the bridge is already half-built. `code.rs`'s `code_of` is the
`Type → Term : Ty l` direction, deliberately partial, returning `None` for a
former with no code and becoming a diagnostic rather than a wrong term. It has
the `Ty` arm already (`code.rs:31`), so `⌜Type<n>⌝ = TmTy(n) : Ty (n+1)` needs
nothing new. What has to be written is the syntactic half — reading an `Expr`
as a `Ty` — which was deleted with the retirement and has no surviving helper
(nothing in `crates/elab` or `crates/syntax` matches `expr_as_ty`/`ty_of_expr`).

**Flag before phase 1:** `ast.rs:274` still documents `TyApp` as "the one form
that can spell an *applied* type where an expression is expected — since a
`Ty 0` argument position reads its expression as a type (§5)", citing the
retired section. Either that behaviour survived the retirement or the comment is
stale. Determine which; do not build on the comment.

## 5. Levels: the joins that were vacuous

`docs/language/surface-records.md` §3 stated the rule and then observed it could not
matter yet:

> there is no level *decision* in this round, only a level *discipline*: the
> generated code must read the join off the spine and must never write
> `Level::Zero`.

This is the round where that discipline is tested, because a `Type`-valued
field is the first thing that makes a record land above 0. Two known sites:

- **`lower_shape`'s empty case** (`inductive.rs:462-472`) returns
  `Type::Empty { level: Level::Zero }` and documents itself as *"this is where
  the level-0 assumption enters … this is the site that changes first."* Take
  it at its word.
- **The hardcoded `Level::Zero`s** at `inductive.rs:162-170`, in the tuple
  spine construction.

`docs/language/surface-function-types.md:390`'s standing claim — "every writable type
sits at level 0" — becomes false the moment phase 1 lands, and should be edited
rather than left to rot.

**Rule: levels are written or zero, never inferred.** No level metas. This is
what keeps `issues/elab-unifier-completeness`'s claim ("no level constraints
exist below layer m") true rather than quietly stale. Level *inference* is a
different feature and must not ride along.

## 6. Non-cumulativity: no lift

DeLaM ch. 04 §Non-cumulativity is deliberate and the kernel bought into it:
`DESIGN.md:19,164`, `typing.rs:19` ("levels compare by `≈`, never `≤`"),
`conv.rs:291`. `Nat : Type<0>` and that is the only universe it inhabits. There
is no lifting operator and this round does not add one.

**Decided: every level mismatch is a hard error** naming both levels and saying
that this system is non-cumulative. Rationale: adding a lift is a metatheory
decision against an argument ch. 04 makes on purpose — it would be the first
trusted-base change and first ch. 07 obligation since `surface-function-types`
— not an ergonomics decision to be taken in a surface round.

The in-system precedent for what to do instead is already written down:
`docs/kernel/unit-empty-level-indexing.md` §2, *"Parameterize rather than polymorphise:
distinct types at distinct levels, exactly as non-cumulative systems do it
(Agda's `record ⊤ {ℓ} : Set ℓ`)"*. That doc is also the record of
non-cumulativity biting for real (`Vec^1(Ty 0; 0)` dropping its level, breaking
ch. 06 Preservation and making `Leaf` unbuildable for a polymorphic `Tree`), so
the failure mode is not hypothetical — it is the second time this system has hit
it, and the first time a *user* will.

## 7. Universe polymorphism: generators, not `UPi` functions

Out of scope, and the reason is structural rather than budgetary. `Type::UPi`
opens with `self.meta_layer(env)?` and lands at `Level::Omega`
(`typing.rs:461-470`); `ω` is never programmer-writable (`level.rs:50`).
Quantifying over `ℓ` is layer m.

The question that has to be answered *here*, because everything downstream is
planned against it: can one at least obtain **code** of a universe-polymorphic
function instantiated at a concrete level?

**No — and the failure is one step further out than expected.** Ch. 04 states
there is no encoding for universe-polymorphic functions and hence no decoding
rule (line 652), and that they cannot be passed around (line 578); the kernel
matches, with no `TmUPi` beside `TmPi`/`TmTy`. Instantiation does not rescue it:
`UApp` returns an ordinary concrete-level type (`body.inst_univ(&phi)`,
`typing.rs:1440`) with nothing ω-tainted, but the **term stays layer-m**
(`typing.rs:1425`), and `BoxTm` checks its payload at `Layer::Code`
(`typing.rs:626`). A layer-m term cannot sit inside a box. So there is no code of
the polymorphic function *and no code of any instantiation of it*.

**What works is the flip: a polymorphic function that returns code.**

```
∀ℓ. □(⊢ T_ℓ @ ℓ)
```

Well-formed, checked against the rules rather than assumed:

- `CodeTy`/`CodeTm` live at **level 0** (`typing.rs:591,599`), so `UPi`'s
  requirement that its body type-check at its declared level (`typing.rs:468`)
  is met with `level = 0`. No ω contamination.
- The boxed code **may mention `ℓ`**: `push_univs` extends the universe context
  and `in_ctx` is `Env { gamma, layer, ..self.clone() }` (`typing.rs:275-277`),
  so crossing into `Layer::Code` preserves it.

And ch. 04 says this is *why* the restriction exists — universe-polymorphic
functions are layer-m "because universe variables must also be visible by the
bindings in global contexts" (581-582). The restriction is shaped to make this
work.

> **Rule for the language.** Anything universe-polymorphic that will later need
> to be *compiled* must be written as a generator (`ℓ → code`), not as a `UPi`
> function. `UPi`-the-function is layer-m convenience only: its results can never
> become code, at any instantiation.

Consequences to carry, not to solve here: a universe-polymorphic library
function is not compilable as such — its generator is, once per level, which
makes `issues/generators-in-the-language` the only route to a level-generic
library. What is lost is a single runtime object polymorphic in `ℓ`; you get n
monomorphic copies, as in Rust's monomorphization. And layers are **not** freely
crossable (`υ < c < p < m`, with code promotion a real operation), so a surface
that lets a definition drift to whichever layer its use demands is an elaborator
illusion that must be able to fail loudly.

## 8. Interactions to observe, not assume

Each is a test, not a claim.

1. **`fn f<A>` still means `Ty 0`.** Every landed polymorphism test must pass
   unchanged after the binder path is generalized (`docs/language/surface-polymorphism.md`
   has 33).
2. **The `lib.rs:950` message survives.** `@f(Nat, x)` must still be diagnosed as
   an argument landing in a type parameter's slot, not silently elaborated by the
   new bridge. This is the round's main regression surface.
3. **`Type` in an equality.** `theorem t(): Nat = Nat` — an equality *type* whose
   endpoints are types is `Id` at `Ty 0`, level 1. Does `TyKind::Eq`'s
   elaboration compute the level or assume 0?
4. **A record with a `Type` field and a `match`.** The braced-literal suppression
   rule (`docs/language/surface-records.md` §6) interacts with a field whose value is a
   type.
5. **`code_of` partiality reaching a user.** A type with no code in a
   `Type`-valued position must produce the diagnostic, not a `None` unwrap.
6. **Tier-0/1 generators above level 0.** The first genuinely non-zero encoding
   goes through `lower_shape`; both `Unit`/`Empty` terminators must take the
   declaration's level, per `docs/kernel/unit-empty-level-indexing.md`.

## 9. Rejections, each with a message

1. `Type<ℓ>` with `ℓ` a name — "universe levels cannot be quantified over at the
   surface: universe polymorphism is layer m (see §7); write a concrete level".
2. `Type<n+1>` / `Type<max(a,b)>` — "a universe level here must be a numeral;
   joins are computed, not written".
3. An inductive or record named `Type` — "`Type` is reserved in type position".
4. A level mismatch — names both levels and states non-cumulativity, per §6.
5. `Type` where a term is expected with no `Ty l` in sight — the existing unbound
   or head-mismatch path, not a new one.
6. `{A: Type} -> …` — still the existing implicit-binder message
   (`parser.rs:581-585`); this round makes it *writable in principle* but the
   structural blocker (no implicit marker in `Type::Pi`) is
   `issues/implicit-binders-in-function-types`, untouched.

## 10. Out of scope

- Universe polymorphism (§7), and with it a fully general `j`/`cong` — the
  special-forms-as-declarations follow-on lands **at concrete level 0**, where
  every current use lives.
- Any lift or cumulativity (§6).
- Level inference / level metas (§5).
- `Type` as a *computed* value — codes are already terms; this round adds no
  large elimination the kernel does not have.

## 11. Acceptance checklist

1. `Type` and `Type<n>` parse in every type position, including under `->`,
   inside `[T; n]`, and as an inductive's type argument.
2. `Type<n> : Type<n+1>` — a declaration whose result type is `Type<0>` checks
   at level 1, kernel-verified.
3. `fn id_at(A: Type, x: A) -> A { x }` declares, and `id_at(Nat, 3)` computes
   to `3`.
4. The bundled record — `record Mon { carrier: Type, unit: carrier, … }` —
   declares, and its encoding lands at level 1 with the join *computed*.
5. Constructing and projecting a `Mon`, kernel-checked.
6. `fn f<A>` and all 33 polymorphism tests unchanged.
7. `@f(Nat, x)` still produces the type-parameter-slot message.
8. A motive as a λ: `j(p, λ y q => P(y), …)` elaborates identically to today's
   `j(p, (y,q) -> M, …)` (phase 3, `issues/motives-as-lambdas`).
9. Every §9 rejection, each asserted on its message.
10. A negative control per `docs/testing-generated-terms.md`: an **open**
    element type, a *checking* position, and a level mismatch that must fail.
11. A non-cumulativity test: a `Type<0>`-typed value rejected where `Type<1>` is
    expected, with the §6 message.
12. Workspace green via `scripts/test`.

## 12. What implementing it corrected

Phases 1, 2 and 4 landed 2026-07-27 (`crates/elab/tests/universe.rs`, 21 tests,
workspace 541). Five corrections, in descending order of how wrong the scheme
was.

### 12.1 The bridge needed a *second* direction the scheme did not have

§4 specified reading an expression as a type. That is only half of it: without
the dual — an **expression in type position**, decoded — a `Type`-valued field
is half a feature. `record Mon { carrier: Type, … }` declares and constructs,
but `m.carrier` cannot be *written as a type*, so nothing outside the
declaration can use the carrier and the bundled record is a container you
cannot open.

So `TyKind::OfExpr` was added: `ty_atom`'s last resort, elaborated by inferring
the expression, requiring its type to be a universe, and wrapping in `El`. It is
not a coercion — `El ⌜T⌝ ⇝ T` is a kernel reduction, so a decoded type
*converts* with the type it decodes to rather than merely resembling it, which
is what `a_decoded_type_converts_with_the_type_it_decodes_to` pins.

The general shape is worth keeping: **a universe is not one bridge but two**,
because types and terms each have a syntax and the universe is where they meet.
Writing only the direction the motivating example needed would have shipped
records whose type fields are decorative.

### 12.2 The flagged regression surface did not exist

§2 and §4 called `lib.rs:950` the round's regression surface, on the strength of
its own comment claiming it caught the pre-`<…>` spelling `@f(Nat, x)`.

It never did. Verified against a clean tree: `@id(Nat, 3)` reported ``unbound
name `Nat` `` *before* this round — which is exactly what that comment predicted
would happen **if the arm were removed**. `@` does not make type parameters
positional, so `Nat` lands at the value parameter's type and the arm is never
consulted. The message was aspirational: dead code describing a customer it did
not have.

Recorded because it is the second instance of the pattern this project keeps
logging — a limitation (or here, a protection) written down as a property of the
system when it was a property of a check that nothing had ever reached. The
test now asserts the *behaviour* (the argument is rejected) rather than the
message.

### 12.3 The bridge must fall through, not reject

The first implementation errored when an expression at an expected `Ty l` could
not be read as a type. That is wrong, and the failure was immediate: a universe
is an **ordinary type**, so ordinary terms live at it. `g(A)` where
`g: Type<0> -> Type<0>`, or any variable at `Type<n>`, reaches that position
legitimately.

So only a reading that succeeds *as a type* is taken; anything else falls
through to ordinary inference. The arm is an opportunity, not a claim.

### 12.4 Phase 2 was already paid

The scheme expected to retire level-0 assumptions. Almost none needed retiring:
`lower_ctor`'s `Level::max` fold already computed the join correctly, so a
bundled record lands at level 1 by arithmetic `docs/language/surface-records.md` §3 wrote
and could not then exercise. Writing the join as a computation rather than a
constant, one round early, is exactly what made this round a grammar change.

`lower_shape`'s empty case (`inductive.rs`) still hardcodes `Level::Zero` and
still documents itself as the site that changes first — a record cannot reach
it, and no declaration this round can write does.

### 12.5 Smaller

- **A bare name in type position keeps its old message.** `-> x` for a term `x`
  is still `TyKind::Named` and still says ``unknown type `x` ``, not "not a
  type": only a *compound* expression reaches the decoded path. Consistent
  enough to leave, noted so the asymmetry is not rediscovered as a bug.
- **`occurs` needed an expression scan.** A decoded type has no type structure
  to read polarity off, so `expr_mentions` is conservative — a mention anywhere
  counts as an occurrence, and the binder-carrying forms (`match`, `j`) answer
  `true` unconditionally. A false positive costs a rejection; a false negative
  would cost positivity.
- **`docs/language/surface-function-types.md` §9.1's claim went false**, as predicted
  there: `Level::max(dom, cod)` is now directly observable, since
  `Type<0> -> Type<0>` is a level-1 function type. Edited in place rather than
  left to rot.

## 13. Phase 3: motives are lambdas, and `=` is an expression

Landed with the rest (`crates/elab/tests/motives.rs`, 12 tests). The scheme
called this phase "nearly free once a motive is an ordinary function at
`(z: A) -> Type`". It was not, and the reason is worth writing down.

**The blocker.** A motive's body is a type, and the commonest motive body in
this codebase is an *equation*. But `=` was deliberately kept out of the
expression grammar — `parser.rs` uses it as punctuation in `let x = e` and in
`calc`'s `e0 = e1 := p`. So `λ z => acc + z = n` did not parse, and "a motive
is an ordinary `ExprKind::Lam`" could not be delivered by a parse-and-desugar
change at all. Either the motive body stays parsed with `ty()` — a λ-shaped
syntax that is not a λ, i.e. the second binder path surviving under a nicer
skin — or equality becomes an expression.

**Decision: equality becomes an expression.** `ExprKind::Eq`, loosest-binding
and non-associative, suppressed in the two contexts that use `=` as
punctuation via a `no_eq` flag mirroring the existing `no_record_lit`. This is
the same move as the rest of the session and follows from it: a type *is* an
expression whose type is a universe, so once `Type<n>` is writable there is no
reason for the equality former to live only in `TyKind`. `ty_atom` now gets its
`TyKind::Eq` from the one expression parse rather than a second one, so the two
spellings cannot drift.

**What retired.** `match … as z -> M` and `j(p, (y, q) -> M, case)`, each
diagnosed with a migration message rather than mis-parsed. `->` is now the type
arrow and nothing else. The elaborator takes a motive apart in one place
(`motive_lam`), which is where "a motive is a function" is understood — there is
no second binder syntax left in the surface.

**Rejections added:** the two retired spellings, a motive of the wrong arity, an
annotated motive binder (its type is fixed by what the motive is *for*, so an
annotation would be a second source of truth), a non-lambda motive, and a
chained `a = b = c`.

**Amendment, 2026-07-31: the motive body is parsed with `ty()` after all —
and that is not the rejected option.** The blocker above framed a choice: keep
`ty()` for the motive body (a λ-shaped syntax that is not a λ), or make
equality an expression. Equality became an expression, which was the right
call and stands. What the framing missed is that the two are not exclusive:
with `ExprKind::Eq` in place, `ty()`'s own fall-through *is* the expression
parse, so parsing a motive body with `ty()` reads `a = b`, a name and an
applied name through exactly the same code path as before and cannot drift
from it. The motive is still an ordinary `ExprKind::Lam`; only its body's
entry point moved.

The reason to move it: a motive body may be a **function type**, and no
expression is one. An IH-generalizing induction has motive
`λ z => (env: Val) -> … -> P(z)` — the arms λ-wrap and `ih` is applied at the
varied arguments (`issues/ih-generalization.md`) — and without this the
`fuel_monotone` of `lib/certgen/ir_v1.hthr` is not statable, never mind provable.
Mechanically: a one-shot `motive_body` flag on the parser, taken by the first
`lambda()` it reaches, so the motive's own lambda parses its body as a type
and a lambda *inside* the body is an ordinary expression lambda. The body is
carried as `ExprKind::TyLit`, produced nowhere else, and read back by
`motive_lam`. Tests: `crates/elab/tests/motives.rs` §6b, which includes the
three old body shapes as the regression.

**Cost, honestly:** every explicit motive in the workspace was rewritten. The
mechanical migration also caught a function type — `Tip(n) = Node(k, xs) -> Nat`
matched the `(a, b) ->` shape — which is a reminder that the old motive syntax
was genuinely ambiguous with the type arrow, i.e. the aesthetic complaint in
`issues/motives-as-lambdas.md` was a real parsing hazard and not only a
readability one.
