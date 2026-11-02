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

- ~~an **index**~~: done in its own design, `docs/codata-indexed-design.md`.
  The index binders are in scope in the field types and a child writes its
  own index; a constructor's result annotation is refused there, since
  codata has no η.
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
positions (with nesting, at each layer of the carrier):

- **at the step type** (a node): a constructor of the declaration becomes
  the step pair, its children checked at `X + ⟦D⟧`; any other tree `e`
  becomes `(λo. ⟨fst o, λq. inr(snd o q)⟩)(out e)`, so `countdown`'s
  `Zero => zeros()` is one observation of an existing tree; `match` and
  blocks fall through to the ordinary elaborator, whose branches come back
  to the hook at the same position (`smap`'s `match s { SCons(h, t) =>
  SCons(Succ(h), smap(t)) }`).
- **at the child type** `X + ⟦D⟧`: a self-call becomes `inl(seed)`, the
  carrier tuple of its varying arguments; anything else is an existing tree,
  `inr(e)`. A function child is a λ whose body is at the child type, or an
  existing function of trees `k`, which becomes `λy. inr(k y)` (added
  2026-10-22: before, a bare `k` reached the kernel unconverted and was
  refused there; `docs/coitree-design.md`'s `bind_cong` met it).
- **with a constructor nested above a self-call** (§5.4), the carrier has
  layers and the child type is `C_j + ⟦D⟧` at the child's layer: such a
  constructor is a pending node, the child `inl(inr(node))`, the node built
  at the layer below.

Every other self-call is refused as unguarded: in a payload (`SCons(hd(bad(n)),
…)`), under an observation (`tl(bad(n))`), alone (`bad()`), or inside any tree
that is not a constructor of the declaration (`SCons(n, tl(SCons(n, bad(n))))`:
corecursion *up to* a function, `issues/codata-corecursion-up-to.md`).

### 5.3 What it does not do

- No mutual corecursion and no corecursion through a helper function: one
  `fn`, one `corec`.
- No "productive up to" calls (`bind`'s `Ret(r) => h(r)` is the existing-tree
  case, which is fine; a call that is guarded only after an unfolding is
  not).
- No copatterns. Definitions are written with constructors, and observations
  are `match`.

### 5.4 Nested constructors

A constructor nested above a self-call (`Vis(Ask, λ n => Tau(echo(n)))`,
`SCons(n, SCons(Succ(n), pairs(Succ(Succ(n)))))`) needs a carrier that
remembers the pending constructor (kernel design §6). The carrier grows one
layer per extra constructor. Let `F(C) = Σ(s : S). Π(p : P s). C + ⟦D⟧` be a
node over the carrier `C`, the step type's shape. Then

```
C₀ = X                     (the varying tuple)
C_{j+1} = X + F(C_j)       (a seed, or a pending node one layer down)
```

and a definition whose longest chain of nested constructors above a call
has `d + 1` links has carrier `C_d`. The chain is counted on the surface
before the body is elaborated (`corec_nesting`), so every type is known when
the hook runs. With `d = 0` nothing changes: `C₀` is the carrier §5.1
builds.

- **The body** is a node at `F(C_d)`. A child at layer `j` (`C_j + ⟦D⟧`) takes
  a self-call as `inl(inl(seed))` (`inl(seed)` at `j = 0`), an existing tree
  as `inr(e)`, and a constructor with a call inside as
  `inl(inr(node))` with `node : F(C_{j-1})`, its own children at layer
  `j - 1`. The hook finds a child's layer by comparing the expected type
  with each `C_j + ⟦D⟧`, top first.
- **The step** is `case x { inl(v) ⇒ body[v]; inr(node) ⇒ lift(node) }`, and
  the seed is `inl(⟨varying arguments⟩)`. `lift : F(C_{d-1}) → F(C_d)` keeps
  the label and moves each child up a layer with `embed : C_j → C_{j+1}` (a
  seed stays `inl`; a pending node's own children are lifted in turn).
- **No closure conversion.** A pending node is a value built where it is
  written, so it holds whatever it mentions (the `n` a `λ n` bound, the
  varying parameters) as ordinary subterms. Nothing is abstracted, and no
  state needs a type of its own.
- **Observations compute by β**, one per layer: `out` of the definition
  gives the body's node with the nested child as `corec(…, inr(node))`; `out`
  of that runs `lift`, whose seed children are `corec(…, inl(v))`, which is
  the definition itself at `v`. So `tl(tl(pairs(n))) = pairs(Succ(Succ(n)))`
  holds by `refl`, as `tl(from(n)) = from(Succ(n))` does. A nested node is
  not definitionally the constructor written in the source (no η, §4): its
  observation is.
- **Indexed codata keeps one layer** this round: a nested call there is
  refused with `issues/codata-nested-guards-indexed.md`. The indexed carrier
  carries an equation per seed (`docs/codata-indexed-design.md` §6), and a
  pending node sits at its child's index, not the step's.

## 6. Layers

Every declaration over codata is bound at **layer c**, like every other:
`M`, `corec` and `out` are admitted there, and `TmM` is `M`'s code, with
four code-recursor branches (`docs/kernel-m-codes-design.md`). So codata is
an ordinary type argument (`id<Stream>(…)`, `Two<Stream>`: `code::code_of`
quotes `M` to `TmM`), and boxed codata is inert syntax.
`codata_declarations_are_code` and `codata_as_a_type_argument` pin both.

Round 1 had bound codata declarations at layer p instead, through a kernel
extension (bodied term definitions at p in Ψ) and an elaborator walk that
chose each declaration's layer. Both are gone with the codes round.

Goals, holes, `have`, `rewrite` and `calc` work over codata statements;
certgen refuses codata (§1).

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
  `refl` (no η), unguarded calls in each of the three places, a call inside
  an existing tree, recursion out of codata, an index.
- **nested constructors** (§5.4, `nested_constructors_above_a_self_call`):
  two and three layers at literal and neutral seeds, back to the definition
  by `refl`; a pending node under a λ that captures the answer, beside a
  `match` arm that is an existing tree; a bare function child one layer
  down; an open element type; wrong observations at a layer refused by the
  kernel. `lib/_tests/std/itree/coitree_tests.hthr` has the same over
  `CoTree`, and `codata_indexed.rs` the indexed refusal.

Plus a module-image round trip (`codata_round_trips_through_images`): the
declaration, its constructors and a corecursive function written to an
image, replayed, and used from an importing module.

## 8. Next

1. ~~**Indexed codata**~~: done (`docs/codata-indexed-design.md`).
2. **The library** (design §10 step 5): the coinductive `ITree` with `bind`
   and `iter`, `approx` into the finite tree, `Bisim`, eutt, and the bridge
   `Bisim ⇔ Π n. Same(approx n t, approx n u)`.
3. ~~**Nested guards**~~: done for unindexed codata (§5.4); indexed is
   `issues/codata-nested-guards-indexed.md`.
4. ~~Codes for `M`~~: done (`docs/kernel-m-codes-design.md`).
