# Codata in the elaborator

Status: round 1 implemented (`crates/elab/src/codata.rs`,
`crates/elab/tests/codata.rs`). The kernel former under it is
`docs/kernel-coinduction-design.md`'s `M` / `corec` / `out` (PR #111); this
is that design's §10 step 4. Issue: `issues/codata-elaborator.md`.

The section numbers here are the ones the code and its error messages cite.

---

## 1. Surface

```
codata Stream { SCons(head: Nat, tail: Stream) }
codata CoTree<R>(E: Events) {
    CRet(r: R), CTau(t: CoTree<R>(E)), CVis(c: E.Cmd, k: E.Resp(c) -> CoTree<R>(E))
}
```

`codata` is `inductive`'s grammar with a different keyword. It takes type
parameters and value parameters (`docs/inductive-value-parameters.md`),
plain children (`t: D`) and function children (`k: A -> D`, the domain
possibly depending on earlier payload). Recursion through the children
needs no positivity story beyond the strict positivity the field forms
already have.

Refused this round, each with its own message:

- an **index** (`codata D : (n: Nat) -> Type`): the kernel's `M` is indexed,
  but the elaborator's indexed lowerings are inductive-shaped
  (`issues/codata-indexed.md`). `Bisim` and eutt want it, so it is the
  next round's (§8).
- a **container field** (`[D; n]`): write the children as `Fin(n) -> D`.
- codata in a **certgen** signature, as a parameter or a result: native code
  has no representation for an infinite tree yet.

## 2. Lowering

```
⟦D⟧ = M(I := Unit; _. S; _ s. P(s); _ _ _. ⟨⟩)(⟨⟩)
```

- `S` is tier 1's shape: the nominal tag and every constructor's payload,
  the same `Σ`/`+` spine an `inductive` without children gets. So
  constructor labels, `tag_of`, payload projection and the display all
  reuse tier 1's readers.
- `P(s)` is the positions of constructor `s`'s children, built as a case
  tree over the tag into codes (reusing tier 2's `w_case_tree`): one `Unit`
  per plain child, the domain's code per function child, right-nested
  `TmSum` when there are several, `TmEmpty` when there are none.
- The index is trivial and `next` is `⟨⟩`: the declaration is unindexed.

Parameterised declarations lower per instance (`lower_instance_m`), as tier
2 does; an unparameterised one is lowered once at declaration time.

What is definitional is exactly the kernel's: `out(corec(…))` computes by β,
and nothing else does. There is **no η** (`t ≢ in(out t)`), and two
corecursive definitions of the same tree are not convertible. Equations of
trees are bisimilarities (§8).

## 3. Constructors

A constructor application is the apomorphism's `in`: a `corec` over `Unit`
whose one step returns the constructor's label and exits (`inr`) at every
child.

```
C(a, t, k) ↦ corec⁰(sig; _. Unit; _ _. ⟨ℓ_C(a), λp. inr(kids(p))⟩; ⟨⟩; ⟨⟩)
```

so `out` gives the written children back exactly, at an open payload and at
open children. A function child's codomain is scoped under its own binder.
The round's one encoding bug was that codomain, unshifted, which made `R`
read as `E` under `λ a => CRet(r)`; `function_children_and_dependent_domains`
and `value_parameters_and_approximation` now pin it. `read_ctor`, which
other routes use to see a literal constructor, reads the label off the
corec's step pair.

## 4. `match`

```
match s { C_i(x̄) => b_i }  ↦  (λo. (case fst o of Q) (snd o)) (out s)
```

`Q`'s branch for `C_i` binds the payload from the label and each child as
`snd o` at the child's position: a plain child is `snd o ⟨⟩` (injected into
the position sum), a function child is `λy. snd o (inj y)`. The motive is
**non-dependent** in the scrutinee: `M[s/z]` is the motive at the original
`s`, never at a rebuilt constructor, because without η there is no
equation `s = C(…)` to transport along. So `match` on codata computes
values, and a theorem about a codata value proceeds by observation, not by
case analysis on its shape.

### 4.1 No recursion out of codata

A function *from* codata cannot recurse on it: codata has no structural
order. A self-call under a codata `match` that no enclosing structural
`match` guards is refused with that reason (`count(s)` below), and the
standard move is a `Nat` fuel parameter beside it, which is how `nth` and
`approx` are written:

```
fn nth(s: Stream, n: Nat) -> Nat { match n { Zero => hd(s), Succ(k) => nth(tl(s), k) } }
```

### 4.2 No-confusion and inversion

`match` on a constructor application computes (β under `out`), so
`hd(SCons(n, s)) = n` and `tl(SCons(n, s)) = s` are `refl`. Constructor
disjointness of two codata values is a `match` into `Bool` as for
inductives. What is missing is *inversion* (from `s = SCons(a, t)` to `a =
hd(s)`) at an arbitrary `s`, and that is fine: it is `J` and the
observation.

## 5. Corecursion

A `fn` whose result is codata and whose body calls itself is compiled into
**one** `corec`, the dual of structural recursion's eliminator. The rule is
the guarded one: every self-call must be a **direct child** of the
constructor the step returns.

```
fn from(n: Nat) -> Stream { SCons(n, from(Succ(n))) }
↦ λn. corec(sig; _. Nat; _ x. ⟨ℓ_SCons(x), λp. inl(Succ(x))⟩; ⟨⟩; n)
```

### 5.1 Carrier: fixed and varying parameters

A parameter passed unchanged as itself (`Var(name)`) in every self-call is
**fixed**: it stays an outer binder and the step sees it free (`konst(a)`,
`reads(c)`, `spin(E)`). The rest are **varying**, and the carrier is their
Σ-tuple in declaration order, dependent where their types are (`fib(a, b)`,
`interleave(a, b)` with the two swapped). Fixed-ness is decided syntactically
over the body's self-calls first and then verified at each seed, so a call
that writes a fixed argument as something else is refused rather than
misread. Type parameters are always fixed. A corecursive function takes its
parameters explicitly this round; an implicit value parameter is refused.

The body is elaborated once, against the **step type** `Σ(s : S). Π(p : P
s). X + ⟦D⟧` over a context where the varying parameters are bound, and then
`corec_close` substitutes them by projections of the carrier variable.

### 5.2 The step's two positions

While a corecursive body is open, every checking-mode elaboration passes
through `Elaborator::corec_check`, which recognises the step type's two
positions:

- **at the step type** (a node): a constructor of the declaration becomes
  the step pair, its children checked at `X + ⟦D⟧`; any other tree `e`
  becomes `(λo. ⟨fst o, λq. inr(snd o q)⟩)(out e)`, so `countdown`'s
  `Zero => zeros()` is one observation of an existing tree; `match` and
  blocks fall through to the ordinary elaborator, whose branches come back
  to the hook at the same position (`smap`'s `match s { SCons(h, t) =>
  SCons(Succ(h), smap(t)) }`).
- **at the child type** `X + ⟦D⟧`: a self-call becomes `inl(seed)`, the
  carrier tuple of its varying arguments; anything else is an existing tree,
  `inr(e)`. A function child is a λ whose body is at the child type.

Every other self-call is refused as unguarded: in a payload (`SCons(hd(bad(n)),
…)`), under an observation (`tl(bad(n))`), or alone (`bad()`).

**Nested constructors** above a self-call (`Vis(Ask, λ n => Tau(echo()))`)
need a carrier that remembers the pending constructor. The kernel design's
§6 sketches the elaborator generating those carrier states. This round
refuses the shape with `issues/codata-nested-guards.md`, and the workaround is
to write the state yourself: `echo(w: Phase)` with `Waiting`/`Ticking`.

### 5.3 What it does not do

- No mutual corecursion and no corecursion through a helper function: one
  `fn`, one `corec`.
- No "productive up to" calls (`bind`'s `Ret(r) => h(r)` is the existing-tree
  case, which is fine; a call that is guarded only after an unfolding is
  not).
- No copatterns. Definitions are written with constructors, and observations
  are `match`.

## 6. Layers

`M`, `corec` and `out` exist at layers p and m only. They have no codes yet
(`docs/kernel-coinduction-design.md` §5), and Heather checks every
declaration body at c. So the kernel now admits **term definitions at p** in
Ψ, beside c (`check_global_binding_declaration` in `typing.rs`). A
reference already requires the binding's layer to be at or below the use
site's, so a p binding can never be mentioned at c: not in a box, and not in
a code the code recursor sees. δ stays layer-preserving and inlines a p
definition away, so the extension is conservative.

The elaborator binds a declaration at p exactly when its statement or body
mentions an `M`, `corec` or `out` (or `IWf`/`DVec` and their terms), or a
global already bound at p (`Elaborator::decl_layer`, over the kernel's
`subst::needs_computing_layer`). Everything else stays at c, and a module
without codata never pays for the walk (`Types::any_codata`).
`layers_follow_codata` pins both sides: `hd`, `zeros` and `third` (a `Nat`
function that only *uses* a stream) are p, and `add` and `plain` are c.

Two consequences to keep in mind:

- A codata definition is never quotable. Codes for `M` (the design's §5,
  four recursor branches) are what lifts that, filed as
  `issues/codata-codes.md`.
- Goals, holes, `have`, `rewrite` and `calc` work over codata statements
  (they check at the theorem's layer); certgen refuses codata (§1).

## 7. Testing

`crates/elab/tests/codata.rs`, on the four axes of
`docs/testing-generated-terms.md`:

- **literal and neutral**: `from(2)` and `from(n)`, `konst(a)`,
  `interleave(from(n), zeros())`, constructors at open payload and child.
- **open element type**: `Seq<A>` with `rep<A>`, `ITree<E, R>` with
  `spin<E, R>`, type arguments inferred through `M` (the unifier learned the
  `M` arm), and `CoTree<R>(E: Events)` cut by `approx` into the finite
  library's `ITree`.
- **checking position**: constructors as arguments, `match` and existing
  trees in step position, function children with a dependent domain.
- **negative controls**: a wrong observation, `from(n) = SCons(n, …)` by
  `refl` (no η), unguarded calls in each of the three places, a nested
  guard, recursion out of codata, an index.

Plus a module-image round trip (`codata_round_trips_through_images`): the
declaration, its constructors and a corecursive function written to an
image, replayed, and used from an importing module.

## 8. Next

1. **Indexed codata** (`issues/codata-indexed.md`): the kernel's `M` is
   already indexed. `Bisim` (index: a pair of trees, shape: `Id` on the
   labels) and eutt (shape: an inductive `Peel`) are instances
   (`docs/kernel-coinduction-design.md` §4), and they are what the library
   needs for its laws.
2. **The library** (design §10 step 5): the coinductive `ITree` with `bind`
   and `iter`, `approx` into the finite tree, `Bisim`, eutt, and the bridge
   `Bisim ⇔ Π n. Same(approx n t, approx n u)`.
3. **Nested guards** (`issues/codata-nested-guards.md`): generated carrier
   states, which `bind` and `iter` will want.
4. **Codes for `M`** (`issues/codata-codes.md`), when a metaprogram needs
   to see codata.
