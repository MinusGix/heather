# Type parameters on `fn` and `theorem`

Status: **scheme**, written before the code per the discipline of
`docs/surface-function-types.md` and `docs/wf-former-design.md`. §9 is the
acceptance checklist; §10 records what implementing it corrected.

Tracking issue: `issues/surface-polymorphism.md`.

The kernel side is **already done and has been since v0**. Level-0 parametric
polymorphism is `Π(A : Ty 0). …` with the parameter used through `El`
(`crates/kernel/src/term.rs:53,895`), and every code the elaborator could
need — `TmNat`, `TmPi`, `TmSigma`, `TmSum`, `TmUnit`, `TmEmpty`, `TmId`,
`TmVec`, `TmFin`, `TmWf`, `TmTy` — is present in `typing.rs`, decoded in
`reduce.rs` and congruent in `conv.rs`. Nothing here touches the trusted base:
no metatheory obligation, no ch. 07 pass. It is a surface grammar and
elaborator round, the same risk class as `surface-function-types`.

What stays out is **universe** polymorphism — quantifying over `ℓ`. A function
polymorphic over `Ty 0` lives at level 1, which the kernel takes in its stride;
a function generic in `ℓ` is `UPi`, layer m, and belongs with the modal round.

---

## 1. What the surface gains

```
decl := "fn"      name tyvars? "(" params? ")" "->" type block
      | "theorem" name tyvars? "(" params? ")" ":"  type block

tyvars := "<" name ("," name)* ">"
```

```heather
fn map<A, B>(f: A -> B, xs: List<A>) -> List<B> { … }

theorem sym_at<A>({a: A}, {b: A}, p: a = b): b = a { … }
```

A type parameter is **a name usable in type position** inside that
declaration's parameter types, result type, and body. It is not a kind, not a
universe, and not writable anywhere else: `TyKind` gains nothing, and there is
still no way to say `Type` in a function type (§3.3).

Expressions gain one form, for the rare case where inference cannot see the
instantiation:

```
postfix := atom ( "<" type ("," type)* ">" )? ( … calls … )*
```

```heather
nil<Nat>()                 -- type arguments given explicitly
map<Nat, Bool>(f, xs)      -- allowed but redundant; both are inferred
```

`<` is also the `lt` infix operator (`parser.rs:520`), so this is parsed
**speculatively**: on `Ident <`, save the position, try to parse
`< ty (, ty)* > (`, and restore on any failure. `a < b` fails at the `>` and
falls back to `lt`; `f<A>(x)` succeeds. Backtracking is free here — the parser
is a `Vec<Tok>` plus an index — and it is total, so no lookahead heuristic can
be wrong about a program.

## 2. The lowering

A type parameter is a **leading implicit value parameter at `Ty 0`**, and the
surface name decodes through `El`:

```
fn f<A, B>(x: P₁, …) -> R  ⇝  λ(A : Ty 0). λ(B : Ty 0). λ(x : ⟦P₁⟧). … ⟦body⟧
                     : Π(A : Ty 0). Π(B : Ty 0). Π(x : ⟦P₁⟧). … ⟦R⟧
```

with `⟦A⟧ = El⁰(A)` wherever the name `A` appears in type position. `Ty 0`
lives at level 1 (`typing.rs:457`), so a polymorphic declaration's *type* is at
level 1 while everything inside it stays at level 0 — which is why
`lower_shape`'s level-0 assumption (`inductive.rs:406`) is untouched by this
round. It is universe polymorphism that would move it, not this.

Nothing else about the declaration lowering changes. `elab_decl_inner` already
closes an arbitrary telescope into `Π`/`λ` with `max(dom, cod)` levels
(`lib.rs:370–384`), and it does not care that the first two entries are
universes. **`theorem` therefore needs no separate treatment** — see §3.2.

### 2.1 Where the type variable lives

In `Cx.tyvars`, which already exists (`lib.rs:2221`) and already does exactly
this job: it maps a surface type name to a kernel `Type` at a binding `depth`,
weakening every use by the binders pushed since. Today it is populated only
while an `inductive`'s field types are lowered at an instantiation; this round
also populates it from a declaration's `<…>`, with

```rust
TyVar { name: "A", ty: Type::El { level: 0, tm: Var(…) }, level: Level::Zero, depth }
```

`lower_named` finds it first, before the inductive table (`inductive.rs:333`),
and the `shift_local(cx.names.len() - depth)` it already performs is exactly
the weakening a use under later binders needs. That path was wrong for open
instantiations until `tyvar-scoping-in-lowered-fields` fixed it on
2026-07-26 — which is the fix this round is standing on.

`lower_ctor` *replaces* `fcx.tyvars` wholesale with the inductive's own
parameters (`inductive.rs:490`). That stays: a constructor's field types see
the inductive's parameters and nothing else. The instantiation arguments are
lowered in the caller's `cx` before the replacement, so an open argument
(`List<A>` inside `map`) is scoped correctly by construction.

**So the answer to the issue's open question 2 is: no new `TyKind`.** A bound
type variable is a `Named { name, args: [] }` resolving to a local binder
rather than a declaration, and the machinery for that is already written.

### 2.2 Codes

Two places need to turn a kernel `Type` into its code (a `Term : Ty 0`):

- a written type argument, `f<List<Nat>>(…)`, and
- a solved implicit type argument (§4).

That is one new function, `code::code_of(&Type) -> Option<Term>`, a
structural quote: `Nat ↦ TmNat`, `Σ ↦ TmSigma`, `Wf ↦ TmWf`, `El t ↦ t`, and
so on down the list in the preamble. It is partial — `Ty l` above the ones
with codes, and any former without one, return `None` and become a diagnostic
rather than a wrong term. `El ⌜T⌝ ⇝ T` is a kernel reduction, so a code that
round-trips wrong is a kernel rejection, never a silent mis-elaboration.

## 3. Three corrections that reading the code forced

Per the house pattern: the places where writing this against the actual
elaborator contradicted the issue's plan.

### 3.1 Inductives do **not** become code-valued type-level functions

The issue's open question 1 offers two options — real Π-parameters on an
`inductive` (a lowering emitting `λ(A : Ty 0). ⌜…⌝`, with every constructor
and recursor gaining a parameter), or monomorphized inductives plus
polymorphic functions, which it says "leaves `map` unable to *return* a
`List<B>` built from a parameter". It concludes "probably the whole thing".

**Neither, and the premise of the second is false.** Instantiations stay
expanded per use, but an instantiation may now be **open**: inside
`fn map<A, B>`, the result type `List<B>` lowers to `⟦List<El B>⟧`, a
perfectly ordinary kernel type with `B` free. `map` returns it. Nothing about
the tier-0/tier-1 generators changes, no constructor or recursor gains a
parameter, and the cost the issue expected to land in the generators does not
exist.

What is genuinely given up:

- `⟦D<…>⟧` is still inlined at every mention, so a large declaration's
  encoding is duplicated per occurrence. That is a term-size cost, not an
  expressiveness one, and it is the cost `inductive.rs` has always paid.
- `D<Nat>` and `D<Bool>` remain unrelated kernel types. Correct, and the same
  as before.
- A type *constructor* still cannot be a parameter (`Functor<List>`). That is
  higher-kinded polymorphism and was never in scope.

### 3.2 `theorem` needs no separate lowering

The issue's open question 5 expects the two to differ, "since theorems are
Ψ-globals and `fn`s are inlined". They share `elab_decl_inner` end to end: the
telescope closure, the kernel gate, and `ParamMeta` are all common code, and
the split is four lines at the very end (`lib.rs:405–428`). A `theorem`'s
statement becomes `Π(A : Ty 0). …` at level 1 and is bound as a `Trm_c` global
exactly as before; a `fn` is inlined exactly as before. Both get type
parameters from the same change. The answer is "yes, in one go, and it is not
two lowerings".

### 3.3 Implicit binders in function types are still out, and this round does
not make them structural

The issue argues that `implicit-binders-in-function-types` "stops being
ergonomics and becomes structural the moment polymorphism exists", because
"without moving it onto the type, every polymorphic call spells its type
arguments positionally".

That does not happen. A type parameter is a *declaration* parameter, so it is
`ParamMeta.implicit` — precisely where implicitness already lives and already
works (`params_of`/`implicit_mask`, `lib.rs:1450–1462`). `map(f, xs)` infers
`A` and `B` by the existing name-directed insertion path; nothing is spelled
positionally.

What stays explicit is applying a polymorphic function **value** — a λ-bound
callback, or a partially applied global. That is the *same* limitation
`surface-function-types` §5.3 already recorded, unchanged in kind and scope by
this round. `implicit-binders-in-function-types` stays open as ergonomics.

The related claim in that issue — that the feature is not properly valuable
"while the surface has **no universe**", because `{A: Type} -> …` is not
writable — also survives: this round adds type parameters to *declarations*,
not a `Type` to `TyKind`, so a function type still cannot quantify over a
type. `(A: Type) -> El A -> El A` remains unwritable, and deliberately so:
that is where a real surface universe starts, and it wants its own round.

## 4. Inference (the issue's open question 3)

The rule, stated so it can be tested rather than discovered:

> **Type arguments are solved from the types of the explicit arguments, by
> structural congruence, in the Miller pattern fragment. Nothing else.**

Concretely, `apply_implicit` (`lib.rs:1928`) already does the whole job:
implicit parameters become innermost Ψ-metas, each explicit argument's
*inferred* type is matched against the parameter's domain by `unify_ty`, and
one `GlobalSubst` discharges the block. Type parameters ride that path with
one extension to `unify_ty`/`unify_tm`:

1. **Full structural congruence.** Today `unify_ty` handles `Id` and nothing
   else (`lib.rs:2387`). It gains `Pi`, `Sigma`, `Sum`, `Vec`, `Wf`, `W`,
   `El`, `Fin`, `Unit`, `Empty` — the formers `inductive.rs` actually builds —
   so that `⟦List<El ?A⟧` versus `⟦List<Nat>⟧` descends to `El ?A` versus
   `Nat`.
2. **The `El` rule.** `El ?A ≟ T` solves `?A := code_of(T)`. This is the only
   new *kind* of solution; everything else is congruence.
3. **Depth tracking and strengthening.** Congruence goes under binders (`Σ`'s
   second component, `Π`'s codomain, `Wf`'s arity), and a meta's solution is
   scoped in `Γ`, not under them. So the descent carries a depth `d`, and a
   candidate solution is accepted only if it is invariant under strengthening
   by `d`.

   The strengthening test needs no new traversal: apply the substitution that
   drops the inner `d` binders (sending each to a marker), re-shift by `d`,
   and require structural equality with the original. A term that mentions one
   of those binders keeps the marker and fails; one that does not is restored
   exactly.

`unify_ty` keeps its existing contract — **it never fails, it only learns**.
An unsolved meta is reported by the caller with a message; a *wrong* solution
is caught by the kernel's re-check of the declaration. That is what makes it
safe to grow.

### 4.1 What this solves, and what it rejects

Solved:

- `map(f, xs)` at `f : Nat -> Bool`, `xs : List<Nat>` — `A` from the domain of
  `f` (depth 0) and again from `xs`; `B` from the codomain of `f` (depth 1,
  strengthened).
- `sym_at(p)` at `p : a = b` on any type — the `Id` congruence that already
  exists, plus the `El` rule for the type parameter.
- Any parameter whose type mentions the variable anywhere inside an encoding
  the congruence covers.

Rejected, with a message naming the restriction and the escape hatch:

- **A type parameter that appears only in the result type.**
  `fn nil<A>() -> List<A>`; `nil()` has nothing to solve from. Diagnosed;
  `nil<Nat>()` is the answer. Result-driven solving means running
  `apply_implicit` in *checking* mode, which is `elab-stage2-metas`' next
  step and not this round's.
- **A λ-argument at a domain that still contains a meta.** `apply_implicit`
  *infers* each explicit argument (`lib.rs:1966`), and an unannotated lambda
  has nothing to infer from, so `map(λ x => Succ(x), xs)` is rejected while
  `map(λ (x: Nat) => Succ(x), xs)` is not. This is the pre-existing
  inference-position rule for lambdas (`surface-function-types` §5.2) meeting
  the pre-existing infer-the-arguments rule; it is not new, but polymorphism
  is the first place it bites, so it gets a message.
- **Anything outside the pattern fragment**, pointing at
  `elab-unifier-completeness`, as `surface-function-types` did.

## 5. Reading an expression as a type

`@f(…)` supplies every parameter positionally, including the implicit ones —
so on a polymorphic callee it needs to spell type arguments *as expressions*.
One arm handles it: in **checking** position at an expected `Ty l`, an
expression is read as a type and elaborated to its code. `@map(Nat, Bool, f,
xs)` then works, and a type variable in scope is passed through as an ordinary
local of type `Ty 0` with no special case at all.

This arm can only fire where the expected type is `Ty l`, which nothing in the
language produces today, so it cannot perturb anything existing.

An expression that is not a nameable type there (`Nat`, a declared type, a
type variable) is a diagnostic pointing at `f<…>(…)`, which is the form that
takes an arbitrary type.

## 6. Interactions to observe, not assume

Each of these is a test, not a claim.

1. **Guarded self-calls** (`match-recursion`). `elab_self_call` filters the
   parameter positions by implicitness (`lib.rs:1223`) and compares the rest
   by *binder position* (`j`), which the leading type parameters shift. The
   claim is that `map`'s recursive call `map(f, tail)` still matches: `f` at
   absolute position 2, `xs` at 3, type parameters skipped because implicit.
   Also that `descends_on_param` (`lib.rs:1177`) still finds the decreasing
   parameter, since it too works in absolute positions.
2. **Container fields** (`container-fields` §4.2). `xs.map(g)` and
   `xs.cong(self)` read the element type off a `Type::Vec`; at an open element
   type that is `El A`. Axis 2 of `docs/testing-generated-terms.md` says this
   is exactly where a shift error hides, so the container tests get an open
   element type.
3. **`infer_ctor`** (`lib.rs:1402`) recovers an inductive's type arguments
   from a field whose type *is* a parameter. At an open instantiation the
   recovered `(Type, Level)` is `El A` and must be weakened like any other —
   the same hazard `tyvar-scoping-in-lowered-fields` names.
4. **Goal holes.** `count_holes` must walk type-argument lists, or a hole
   inside one under-counts the goal prefix. Under-counting is the one thing
   that mechanism cannot survive (`lib.rs:2276`).
5. **`match` on a scrutinee at an open type.** `tag_of` reads the nominal tag,
   which is a closed subterm of the encoding regardless of the instantiation,
   so dispatch should be unaffected. Asserted, not assumed.
6. **A polymorphic prelude.** `sym`/`trans`/`cong_succ` stay monomorphic at
   `Nat` in `prelude.hthr` — regressing 380 passing tests to prove a point is
   not the trade — but a polymorphic `sym` is *declared and used* in the
   acceptance tests, which is the actual claim.

## 7. Rejections, each with a message

| written | message says |
|---|---|
| `fn f<A, A>(…)` | duplicate type parameter |
| `A<Nat>` where `A` is a type parameter | a type parameter takes no arguments (already `inductive.rs:335`) |
| `nil()` for `fn nil<A>() -> List<A>` | cannot infer `A`; write `nil<Nat>()` |
| `map(λ x => …, xs)` | annotate the lambda's binder, or give the type arguments |
| `f<Nat>(…)` where `f` has no type parameters | `f` takes no type arguments |
| `f<Nat>(…)` with the wrong count | `f` takes *n* type argument(s) |
| `@f<Nat>(…)` | `@` and `<…>` both give arguments explicitly; use one |
| a type argument with no code (`Ty l`) | that type cannot be a type argument |
| an expression at `Ty l` that is not a type | write `f<T>(…)` |

## 8. Out of scope

- Universe polymorphism, `Type` in `TyKind`, `(A: Type) -> B`
  (`implicit-binders-in-function-types`, and the layer-m modal round).
- Real Π-parameters on an `inductive` (§3.1 — not needed, not merely
  deferred).
- Higher-kinded parameters.
- Result-type-driven implicit solving (§4.1).
- Implicit binders in function types and lambdas (§3.3).
- A polymorphic prelude (§6.6).

## 9. Acceptance checklist

Grammar and declaration:

1. `fn map<A, B>(f: A -> B, xs: List<A>) -> List<B>` parses, elaborates, and
   the kernel accepts it. **This is the issue's headline: "you cannot write
   `map`".**
2. `theorem` takes type parameters on the same syntax and becomes a Ψ-global
   at level 1.
3. `fn id<A>(x: A) -> A { x }` — the smallest case — and `id(3)` computes.
4. A duplicate type parameter is rejected.
5. A type parameter applied to arguments is rejected.

Inference:

6. `map(f, xs)` needs no type arguments; the solutions come from `f` and `xs`.
7. A type parameter solved from *under a binder* (a `Π` codomain, a `Σ`
   component) is strengthened correctly — the axis-2 control.
8. `nil()` is rejected with the message naming `nil<Nat>()`.
9. `nil<Nat>()` works.
10. `@map(Nat, Bool, f, xs)` works (§5).
11. A negative control: `map(f, xs)` at `f : Nat -> Bool` and
    `xs : List<Bool>` is **rejected**, rather than solving `A` twice and
    keeping the first.

Interactions (§6):

12. `map`'s recursive call is accepted as guarded.
13. A polymorphic declaration over a *container* field, at an open element
    type.
14. A polymorphic `sym`, declared and used at two different types in one file.
15. A hole inside a type argument is counted and dischargeable.
16. `match` on a scrutinee at an open type dispatches.
17. A polymorphic `fn` used at two instantiations in one declaration, to pin
    that they are independent.

Negative controls (axis 4):

18. A wrong type argument (`map<Nat, Bool>(f, xs)` at `xs : List<Bool>`) is
    rejected by the kernel gate, not silently accepted.
19. `f<Nat>()` on a monomorphic `f` is rejected.

## 10. What implementing it corrected

Landed 2026-07-26; `crates/elab/tests/polymorphism.rs` is §9's executable
half (33 tests), workspace green at 465.

### 10.1 Two live defects, both pre-existing, both found by the headline test

Neither is about polymorphism. Both were reachable before this round and
neither had an observer.

1. **A declaration could not be named after a built-in eliminator.**
   `fn map`'s self-call `map(f, tl)` took the *vector* `map` special form
   (`lib.rs:905`), because `shadowed` counted locals, aliases and committed
   globals but not the **enclosing declaration's own name** — which is not in
   `globals` until it is checked. The fix is one clause in `shadowed`, and it
   applies uniformly to `fold`, `inj` and `absurd` as well. Pinned by
   `a_declaration_named_map_can_recurse`, which uses no polymorphism at all.

2. **`wf_branch` projected a container's length in the wrong context.**
   `wf.rs:499` passed `cx` to `projection` while both of the arguments it
   passed had been shifted by `d_body` into `bcx` — two entries short, so the
   identity substitution `projection` builds could not address the outer
   variables. At a *closed* instantiation the constructor encoding's Σ tail
   mentions no ambient variable, so nothing ever addressed the missing
   entries and the bug was the identity. `Rose<A>` at an open element type
   makes an index escape and the kernel's invariant assertion fires.

   That is **axis 2 of `docs/testing-generated-terms.md` for the sixth time**,
   and again the generalization that catches it is one extra context entry.
   Added to that document's evidence table.

### 10.2 Three things the scheme did not predict

3. **Constructors need type application too.** §1 gave `f<T, …>` to `fn` and
   `theorem` only. But `Nil` is exactly the case `infer_ctor` refuses to guess
   — its message already said "annotate the expression" — and `Nil<Nat>` is
   the direct spelling. `Elaborator::ctor_at` handles a constructor head in
   both the bare and the applied form, taking the type arguments as the
   *instantiation* rather than as arguments down a Π spine (a constructor is
   not a Π-typed head, so it could not have gone down that path).

4. **`ty_atom`'s `Ident '<'` early return swallows a type-applied call.**
   `theorem t(): id<Nat>(3) = 3` opens with something that looks exactly like
   an applied type, and the existing early return (`parser.rs:465`) committed
   to that reading and then failed on the `(`. The discriminator is a
   following `(` — an applied *type* is never called — checked after the `>`
   and backtracked, which is the same shape as `group_is_type`'s `->` test.
   Directly analogous to `surface-function-types` §10's first correction, and
   found the same way: by an existing-suite-shaped program rather than by
   reasoning about the grammar.

5. **`apply_explicit` needed a parameter offset.** Its goal-name hints assume
   argument `i` is parameter `i`; after `f<T, …>` has consumed the leading
   type parameters that is off by the number of type arguments, and a goal
   listed under the wrong parameter name is user-visible.

### 10.3 What held

Everything else in §2–§6 behaved as written. Specifically worth recording,
because each was a claim rather than a reading:

- **§3.1 is right**: no generator changed. `inductive.rs` and `wf.rs` are
  untouched by this round except for defect 2 above, and `fn map<A, B>` over a
  declared `List<A>` returns a genuine `List<B>`.
- **§3.2 is right**: `theorem` took type parameters with no code of its own.
- **§6.1**: the guard machinery needed no change. `map(f, tail)` is accepted
  as structurally guarded with two type parameters ahead of `f` in the
  telescope, because they are implicit and `elab_self_call` already filters
  positions by implicitness.
- **§4's strengthening test** fires on the real case (`apply<A, B>(f, x)`
  solves `B` from `f`'s codomain, one binder deep) and the drop-and-reshift
  implementation needed no traversal of `Term`/`Type`.
- **§5**'s `Ty l` checking arm perturbed nothing, as predicted — no existing
  position has that expected type.

### 10.4 Limits found, not fixed

- An implicit *function* parameter still cannot be inferred from an equation:
  `theorem cong_at<A, B>({f: A -> B}, {a: A}, {b: A}, p: a = b)` declares and
  kernel-checks, but `cong_at(p)` cannot solve `f` — `p`'s type mentions `a`
  and `b`, not `f`. That is higher-order pattern unification and belongs to
  `elab-unifier-completeness`; it is the reason the prelude's `cong_succ`
  stays a special case.
- `f<…>` cannot be written after `@` (the parser says so), and a bare `f<…>`
  with no call is a value, per §1.
