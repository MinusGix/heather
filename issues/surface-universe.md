---
title: The Type Session: a surface universe hierarchy
status: open
labels: [frontend,syntax,elaboration,design]
created: 2026-07-27
updated: 2026-07-27
---

`TyKind` cannot say `Type`. Every writable type therefore sits at level 0, and
every level join in the elaborator is vacuous. This issue makes the *concrete*
universe hierarchy writable — `Type<0>`, `Type<1>`, `Type<n>`, with `Type` as
sugar for `Type<0>` — and makes the joins actually compute.

Called "the Type Session" rather than a round because it is not one feature:
it is the missing form, plus the level discipline that has been deferred four
times behind it, plus the `Expr`/`Ty` bridge, plus the scope statement about
universe polymorphism that everything downstream needs in order to be planned.

## 0. Scope, stated before the work

**In:** the concrete hierarchy. `Type<n>` for any numeral `n`, computed joins,
`Type`-valued parameters and fields, and the `Expr`↔`Ty` bridge that makes a
type an ordinary expression when something is checking it at `Ty l`.

**Out, and it is a real boundary, not scope-drawing:** quantifying over `ℓ`.
`Type::UPi` opens with `self.meta_layer(env)?` (`crates/kernel/src/typing.rs:461`)
and lands at `Level::Omega`. Universe polymorphism is layer m, by construction,
and belongs to the modal round. `ω` is never programmer-writable
(`crates/kernel/src/level.rs:50`). See §4 for what that costs and the route
around it.

**Levels are written or zero, never inferred.** No level metas. This keeps
[[elab-unifier-completeness]]'s standing claim — "no level constraints exist
below layer m" — true rather than quietly stale. Level *inference* is a
separate feature and must not ride along on this one.

## 1. The kernel side is free (again)

`Type::Ty(l)` lives at `1 + l` (`typing.rs:457-460`) and `TmTy(l) : Ty (1+l)`
(`typing.rs:756-759`), so `Type<n> : Type<n+1>` is *already true and already
encodable*. `code.rs:31` already maps `Type::Ty(l)` to `Term::TmTy(l)`.

The existing type-parameter lowering is the mechanism this round generalizes:
`fn f<A>` becomes `Π(A : Ty 0)` with `⟦A⟧ = El⁰(A)` at every use in type
position (`docs/surface-polymorphism.md` §2, `lib.rs:373-381`). This round
takes that from *"names bound by a declaration's `<…>`"* to *"any binder whose
type is `Type<n>`"*.

No trusted-base change, no ch. 07 obligation — the same risk class as items
8/9/11/12.

## 2. The `Expr`/`Ty` bridge

A motive written as a λ is an expression whose body is a type, and the surface
has no `Ty`-valued expression form. `Type<n>` in `TyKind` dissolves this rather
than requiring a new invention: checking an expression against an expected
`Ty l` already exists as a code path — `lib.rs:950` — but today it is only a
*diagnostic* arm ("this argument has landed where a type parameter goes"). This
round turns it into a real elaboration, generalizing `code.rs`'s type-to-code
translation.

That arm is also the round's regression surface: its message is load-bearing
for the old `@f(Nat, x)` spelling ([[at-and-type-arguments]]), so replacing it
must keep that failure diagnosed rather than silently elaborating.

## 3. Non-cumulativity: no lift (decision (a))

DeLaM ch. 04 §Non-cumulativity is deliberate and load-bearing. The kernel bought
into it: `crates/kernel/DESIGN.md:19,164`, `typing.rs:19` ("levels compare by
`≈`, never `≤`"), `conv.rs:291` dispatching `Ty` to `lev_eq`. There is **no
lifting operator**. `Nat : Type<0>` and that is the only universe it inhabits.

Today this is invisible because everything joins to 0. The moment `Type<1>` is
writable, a user can build a type a level-0 function cannot accept, with
nothing to coerce it.

**Decided: no lift.** Every level mismatch is a hard error with a message that
says which levels and why. Rationale: adding a lift is a metatheory decision
against an argument ch. 04 makes on purpose, not an ergonomics decision — it
would be the first trusted-base change and first ch. 07 obligation since item 8.
The friction becomes data about what a lift would have to do.

Mitigating, per §4: a generator emits at whatever level it is asked for, so the
pressure for a lift is lower than it first looks.

## 4. Universe polymorphism: generators, not `UPi` functions

The question this round must answer for everything downstream: if `UPi` is
layer-m only, can we at least get *code* of a universe-polymorphic function
instantiated at a concrete level — `do_thing` restricted to `Type<0>`?

**No, and the failure is one step further out than expected.** Ch. 04 is
explicit that there is no encoding for universe-polymorphic functions and hence
no decoding rule (line 652), and that one cannot pass them around (578). The
kernel matches: no `TmUPi` beside `TmPi`/`TmTy`, and `UPi`/`ULam`/`UApp` all
require `meta_layer` (`typing.rs:461, 646, 1425`). Instantiation does *not*
rescue it: `UApp` returns an ordinary concrete-level type
(`body.inst_univ(&phi)`, `typing.rs:1440`) with nothing ω-tainted, but the
**term stays layer-m**, and `BoxTm` checks its payload at `Layer::Code`
(`typing.rs:626`). A layer-m term cannot sit inside a box. So there is no code
of the polymorphic function *and no code of any instantiation of it*.

**What works is the flip: a polymorphic function that returns code.**

```
∀ℓ. □(⊢ T_ℓ @ ℓ)
```

Verified well-formed rather than assumed, since the whole route depends on it:

- `CodeTy`/`CodeTm` live at **level 0** (`typing.rs:591, 599`), so `UPi`'s
  requirement that its body type-check at its declared `level`
  (`typing.rs:468`) is satisfied with `level = 0`. No ω contamination.
- The boxed code **may mention `ℓ`**: `push_univs` extends the universe
  context and `in_ctx` is `Env { gamma, layer, ..self.clone() }`
  (`typing.rs:275-277`), so crossing into `Layer::Code` preserves it and
  `level_wf` on `Level::Var` still passes inside the box.

And ch. 04 says this is *why* the restriction exists: universe-polymorphic
functions are layer-m "because universe variables must also be visible by the
bindings in global contexts" (581-582). The restriction exists to make this
shape work.

So `gen<0>` does not produce a stuck layer-m value; it **computes to a box of
level-0 code** that can be spliced, compiled and certified.

> **Rule for the language.** Anything universe-polymorphic that will later need
> to be *compiled* must be written as a generator (`ℓ → code`), not as a `UPi`
> function. `UPi`-the-function is layer-m convenience only: its results can
> never become code, at any instantiation.

This is load-bearing for the thesis rather than a footnote — a `Compile`
instance consumes code ([[compile-typeclass-design]]), so a universe-polymorphic
library function is not compilable *as such*; its generator is, once per level.

**What is genuinely lost:** a single runtime object polymorphic in `ℓ`. You get
n monomorphic copies. That is Rust's monomorphization and roughly Lean's
erasure story, so it is practically fine — but it *is* a real difference from
Lean's core, where universe polymorphism is uniform. DeLaM confines it to layer
m on purpose, to keep layers c/p vanilla MLTT (ch. 04, 845-858).

**The 90% automation, for a later round.** The surface can still let the user
*write* `fn do_thing<ℓ>(x: Type<ℓ>) -> …` and elaborate it to a layer-m
generator plus automatic instantiation at each concrete level actually used,
splicing the resulting code. One definition written, the replication done by
the machine and every copy kernel-checked. That makes
[[generators-in-the-language]] the *only* route to a level-generic library
rather than an aesthetic preference — logged there.

Caution to carry into that round: layers are **not** freely crossable. The
kernel has a strict order `υ < c < p < m` and code promotion is a real
operation, so "a definition that automatically moves between layers" is a
surface illusion the elaborator maintains, and it has to be able to fail loudly
rather than silently pick a layer.

## 5. Phases

1. `Type<n>` in `TyKind` (+ `Type` as `Type<0>` sugar) and the `Expr`↔`Ty`
   bridge of §2.
2. Joins computed for real: retire the level-0 assumptions, starting with
   `lower_shape` (`crates/elab/src/inductive.rs:406`) and
   `docs/surface-function-types.md:390`'s "every writable type sits at level 0".
3. [[motives-as-lambdas]] — should fall out nearly free once a motive is an
   ordinary function at `(z: A) -> Type`, with `->` no longer overloaded.
4. Records and inductives with `Type`-valued fields: the join in anger, and
   where §3's non-cumulativity first draws blood. Decide in the scheme whether
   a `Type`-valued field is in scope or rejected with a diagnostic.
5. The scope statement of §4, written down so the modal round has a target
   rather than a surprise.

## 6. What it unblocks

- [[motives-as-lambdas]] (phase 3) and, behind it, `j`/`refl`/`cong`/`absurd`/
  `inj` becoming ordinary declarations rather than elaborator special forms —
  round two's organizing principle. **Catch:** in full generality a motive is
  polymorphic in its level, which is `UPi`, which is layer m. So the special
  forms become declarations **at concrete level 0**, where every current use
  lives, and full generality waits for the modal round. State this rather than
  discover it.
- [[implicit-binders-in-function-types]]: `{A: Type} -> …` becomes writable,
  which is the thing that issue said it was waiting on. Its *structural*
  blocker — no implicit marker in `Type::Pi` — is separate and unaffected.
- [[surface-records]]' deferred level question: bundled records, and the
  discipline of computing the join, become reachable rather than vacuous.

## 7. Prior deferrals this discharges

The same sentence, four times, is why this is a session and not a nicety:

- `docs/surface-function-types.md:124,390` — "the surface has no universe …
  every writable type sits at level 0".
- `docs/surface-polymorphism.md:188-192` — "`(A: Type) -> El A -> El A` remains
  unwritable, and deliberately so: that is where a real surface universe
  starts, and it wants its own round".
- [[implicit-binders-in-function-types]]:65 — "Not urgent while the surface has
  **no universe**".
- [[surface-records]]' log — "the level question is not reachable yet (`TyKind`
  has no way to write `Type`, so every writable record joins to 0)".
- [[motives-as-lambdas]]' "Watch for" is the fourth instance seen from the
  motive side: "the surface has no `Ty`-valued expression form today, and
  inventing one is the actual design decision in this round".

## Log

- 2026-07-27: Filed. Came out of asking what should be next after
  [[surface-records]]: item 13 [[motives-as-lambdas]] turned out to be gated on
  the same missing form that three previous rounds had deferred, so the
  universe is the round and the motive is its first consumer. Two things were
  settled while filing rather than left open. (1) Non-cumulativity: **no lift**
  (§3) — reversing ch. 04's argument is a metatheory decision, not an
  ergonomics one. (2) The universe-polymorphism route (§4), checked against the
  book and the kernel rather than assumed: code of a `UPi` function is
  impossible *and so is code of any instantiation of it*, because `UApp` is
  layer-m and `BoxTm` checks at `Layer::Code`; but `∀ℓ. □(⊢ T_ℓ)` — a
  polymorphic *generator* — is well-formed, because code types live at level 0
  and `in_ctx` preserves the universe context. Corrected in passing: an earlier
  claim in this discussion that "`Type`'s own type stays unwritable" was
  scope-drawing, not a kernel fact — `Type<n> : Type<n+1>` has been true and
  encodable since v0.
- 2026-07-27: Scheme drafted: docs/surface-universe.md (grammar, lowering, the two parser collisions, the Expr/Ty bridge, the level sites, no-lift, the layer-m scope statement, 6 interactions, 6 rejections, a 12-item acceptance checklist). Four things reading the code forced, none of them in the issue as filed. (1) The Expr/Ty bridge is a RESURRECTION: docs/surface-polymorphism.md section 5 implemented that exact coercion and retired it the same day, with the lesson 'the coercion was a feature invented to paper over a spelling collision, and it survived exactly as long as the collision did'. It comes back legitimately because this round CREATES the position for a real reason -- a parameter declared (A: Type<0>), a lambda declared at (z: A) -> Type -- rather than conjuring it from a spelling. The scheme has to answer that section rather than walk past it. (2) The syntactic half of the bridge was DELETED with the retirement (no expr_as_ty/ty_of_expr survives anywhere in elab or syntax), while code.rs's code_of half is intact and already has the Ty arm, so only the Expr->Ty reading is new work. (3) ast.rs:274 still documents TyApp as spelling an applied type in expression position 'since a Ty 0 argument position reads its expression as a type (section 5)', citing the retired section -- either that behaviour survived or the comment is stale, and phase 1 must not build on it before deciding which. (4) Type<0> collides with the applied-inductive rule (parser.rs:626-651 parses type arguments with ty(), and 0 is not a type), so the Type rule must be tried BEFORE it and parse a numeral; bare Type is symmetric with the existing Nat special case at parser.rs:661-666. Also pinned rather than left implicit: whether <A: Type<1>> is spellable (recommend yes), and Type becoming reserved in type position. The level sites named for phase 2 are lower_shape's empty case (inductive.rs:462-472, which documents ITSELF as 'the site that changes first') and the hardcoded zeros at inductive.rs:162-170.
- 2026-07-27: Phases 1, 2 and 4 LANDED (crates/elab/tests/universe.rs, 21 tests, workspace 541). Type<n> and Type parse in every type position and in term position, Type<n> : Type<n+1> is kernel-verified, <A: Type<1>> is spellable with Type<0> as the default, a Type-valued value parameter works ('fn id_at(A: Type, x: A) -> A'), and the BUNDLED RECORD -- 'record Mon { carrier: Type, unit: carrier, op: carrier -> carrier -> carrier }' -- declares, constructs, projects from a neutral receiver, and reads its carrier back at Type<0>. No kernel change and no ch. 07 pass, as predicted. Five corrections, in docs/surface-universe.md section 12. (1) The scheme had HALF the bridge: reading an expression as a type is useless on its own, because without the dual -- an expression in TYPE position, decoded -- m.carrier cannot be written as a type and a Type-valued field is a container you cannot open. Added TyKind::OfExpr, elaborated by inferring, requiring a universe, and wrapping in El; not a coercion, since El(code) reduces, so a decoded type CONVERTS with what it decodes to. A universe is not one bridge but two. (2) The flagged regression surface did not exist: lib.rs:950's message claimed to catch '@f(Nat, x)' and never did -- verified against a clean tree, that spelling reported 'unbound name Nat' before this round too, which is what the arm's own comment predicted would happen IF THE ARM WERE REMOVED. Third instance of the project's recurring pattern: a property written down as belonging to the system when it belonged to a check nothing had reached. (3) The bridge must FALL THROUGH rather than reject -- a universe is an ordinary type, so ordinary terms ('g(A)', a variable at Type<n>) legitimately land at that expected type; only a successful type reading is taken. (4) Phase 2 was already paid: lower_ctor's Level::max fold already computed the join, so a bundled record lands at level 1 by arithmetic docs/surface-records.md section 3 wrote and could not exercise -- writing the join as a computation one round early is what made this a grammar change. (5) Smaller: a bare name in type position keeps its older 'unknown type' message since only compound expressions reach the decoded path; occurs() needed a conservative expr scan; and docs/surface-function-types.md's 'every writable type sits at level 0' went false and was edited in place. Still open per the scheme: phase 3 [[motives-as-lambdas]], and phase 5's scope statement is section 7.
- 2026-07-27: Phase 3 LANDED, closing [[motives-as-lambdas]] (crates/elab/tests/motives.rs, 12 tests, workspace 553). The session's phases 1-5 are now all done. Phase 3 was NOT the near-free consequence the scheme predicted: a motive body is a type, the commonest one is an equation, and '=' was deliberately not in the expression grammar, so an ordinary-lambda motive was unreachable without making equality an expression. Done as ExprKind::Eq (loosest, non-associative, suppressed via a no_eq flag in calc steps and ty_atom) -- which is the session's own thesis applied once more: a type is an expression whose type is a universe, so with Type<n> writable the equality former has no reason to live only in TyKind. Written up as section 13. Remaining open, deliberately: universe polymorphism (section 7, layer m, wants [[generators-in-the-language]]), no lift (section 6), and the special forms (j/refl/cong/absurd/inj) becoming ordinary DECLARATIONS -- now unblocked by the motive change but bounded to concrete level 0 until UPi, as section 6 records.
