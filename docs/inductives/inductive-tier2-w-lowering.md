# Tier-2 inductive lowering: recursive function fields on the `W` former

Status: **landed** (2026-10-20). Scheme written before the code, for the roadmap's
`it-function-fields` submilestone (`issues/recursive-function-fields.md`).
The tier scheme is `issues/inductive-compiler.md`'s; this document is its
tier-2 section made mechanical, in the form tier 0 and tier 1 took
(`docs/inductives/inductive-tier0-lowering.md`, `docs/inductives/inductive-tier1-wf-lowering.md`).
§12 records what writing the code changed.

The kernel side is not new: `Type::W`, `Term::Sup`, `Term::ElimW` and their
codes exist, and `crates/kernel/tests/acc.rs` checks `Acc` built on them by
hand (`docs/inductives/acc-via-w.md`). What is new is the lowering from a surface
declaration onto them.

Conventions are tier 0's: `⟦T⟧` for the lowering of a surface type, `⌜T⌝`
for a code with `El ⌜T⌝ ≡ T`, `Γ` the ambient local context, kernel names
from `crates/kernel/src/term.rs`. Everything tier 0 says about the
declaration form, type parameters and the nominal tag carries over and is
not repeated.

The hazard class is the tiers': a bug here does not produce a rejected term,
it produces a **checked theorem about a type the user did not write**.
Review of this document is what catches that.

---

## 1. Scope

A declaration is **tier 2** when some constructor field is a *recursive
function field*:

```
recursive function field  ::=  (y: A) -> D<p₁, …, p_k>     -- or  A -> D<p̄>
```

with `D<p̄>` the uniform occurrence of tier 1 §1 and `A` not mentioning `D`
(strict positivity: `D` occurs only as the codomain). `A` may mention the
type parameters and the constructor's **earlier payload fields** — that is
what makes `Vis(c: Cmd, k: Resp(c) -> Tree)` writable, and it is the case
the milestone exists for.

This round lowers the fragment where

1. the declaration is an unindexed `inductive` (not a `record`, which cannot
   be recursive anyway, and not an indexed family);
2. **every constructor has at most one recursive field**, plain (`t: D`) or
   function (`k: A -> D`). §2.2 says why this is the boundary;
3. no constructor has a container field (`[D; n]`);
4. a function field has **one** arrow (`A -> D`, not `A -> B -> D`);
5. every function field's domain has a code (`crates/elab/src/code.rs`), and
   all of them live at one level `lp`.

Everything outside it is rejected with a message naming the restriction,
never lowered. A declaration with no function field stays on tier 1, byte for
byte: the classification adds a case, it does not move the tier-1 boundary.

Not in this round, each its own follow-up: curried function fields, constructors
with several recursive fields, the course-of-values window, `inj` at a
recursive field, generated-definition naming (`gendefs.rs`; the leaf
predicate's landed 2026-10-21, §13), and the native
and certificate generators (which keep refusing a tier-2 type). Value
parameters on an `inductive` (ITree's `E: Events`) landed 2026-10-21 for both
recursive tiers (`docs/language/surface-value-parameters.md` §6): the codomain
`ITree<R>(E)` is the uniform occurrence when its value arguments are the
declaration's own, in order.

## 2. Why not the bare `W`

The obvious lowering is `⟦D⟧ = W(x : S). P(x)` with `S` the shape and `P(x)`
each constructor's positions. Its constructors and its non-dependent
recursion are fine. Its **dependent** eliminator is not, in two places, and
both are the funext gap of `docs/inductives/branching-inductives-choice.md` §4 (route
A) showing up at the surface.

### 2.1 Leaves: `Π(y : Empty). W` is not a singleton

A constructor with no recursive field has positions `Empty`, so its value is
`sup(ℓ; f₀)` with `f₀ = λy. elim_Empty(y)`. A `match` arm for it is checked
against `M(sup(a; f))` for the step's **abstract** `f`, while the user's arm
proves `M(Leaf(…)) = M(sup(a; f₀))`. Bridging the two needs `f ≡ f₀`. The
kernel has η at `Π` and proof irrelevance at `Empty`
(`docs/kernel/metatheory-ch07-extensions.md` §28), but that rule compares terms *of
type* `Empty`; `f y` and `elim_Empty(y)` are terms of type `W` that merely
live under a `y : Empty`. Relating them is the initial-object η, which §28
declines because conversion would have to decide whether a context is
inconsistent. So `bind(t, Ret) = t` would be unprovable at the `Ret` arm, and
interaction trees are mostly leaves.

### 2.2 Several recursive fields: positions are a sum

`Node(l: D, r: D)` has positions `Unit + Unit`, and its constructor form
stores `λp. case p of inl _ ⇒ l | inr _ ⇒ r`. Bridging that to an abstract
`f` is `f ≡ λp. case p of inl u ⇒ f(inl u) | inr u ⇒ f(inr u)`, which is
η for sums — route B, a research-grade conversion problem. This is the
boundary of §1.2, and it is not a tier-2 restriction in practice: a
declaration whose every recursive field is plain is tier 1, where `Wf` gives
branching for free. What §1.2 refuses is a *mix* — a function field in one
constructor and a branching constructor in the same declaration.

### 2.3 What does bridge by conversion

The other two child shapes need nothing:

- a **plain** child has positions `Unit`, and `λu. f ⟨⟩ ≡ f` by Π-η and
  `Unit`-η (the argument comparison is at `Unit`);
- a **function** child `k : A -> D` has positions `A`, stores `λy. fst (k y)`,
  and a `match` arm rebuilds `k := λy. ⟨f y, c y⟩`; the constructor form of
  the rebuilt `k` is `λy. f y ≡ f` by Π-η.

So the leaves are the only obstacle in the §1 fragment, and §3 removes it.

### 2.4 The fix: carry the leaf equation, and eliminate it with `J`

Cut `W` down to the trees whose leaves are canonical, by a predicate the
constructors prove by `refl`:

```
⟦D⟧ = Σ(t : W₀). El(canon t)
canon(sup(a; f)) = case a of
    leaf constructor  ⇒ ⌜Id(Π(y : P a). W₀; f₀; f)⌝
    plain constructor ⇒ canon(f ⟨⟩)
    fn constructor    ⇒ ⌜Π(y : A). El(canon(f y))⌝
```

At a leaf the arm transports along that equation with `J`, from `f₀`, where
the user's arm is typed, to the abstract `f`. Based path induction fixes the
left endpoint `f₀`, which is a closed term, so the motive is just "`M` at the
tree with `g` in the children slot" and no coherence is owed. On a
constructor value the equation is `refl`, `J` fires, and the arm comes back
**definitionally**, with the payload open. At the other two kinds `canon` only
recurses, so it costs nothing beyond carrying the children's proofs.

This is `Acc`'s coherence predicate (`docs/inductives/acc-via-w.md` §1), with a
different property. It needs no axiom: `Ψ` stays empty, as it did for `Acc`.
What it costs is that `⟦D⟧` equality now sees a proof component. Two values
built by constructors carry `refl` and the children's own proofs, and one
read back from a `match` carries the scrutinee's, so the component never
differs between two spellings of one value that the elaborator produces.
`Id` is relevant, so two *different* proofs of a leaf's equation would make
two different values; nothing builds one.

`sEq` would be the irrelevant choice, and it is the wrong one: since the
2026-09-30 revision it has no eliminator (`docs/kernel/sprop-design.md`), so the
leaf arm could not use it. `Squash` has the same problem.

## 3. The shape `S`

> **`S` is tier 1's shape: tier 0's lowering of `D` with every recursive
> field deleted, plain or function.**

The same `lower_ctor`, so the payload handling cannot diverge between the
tiers. A recursive function field is not in scope in later field types, as
a plain child is not (tier 1 §2).

## 4. The positions `P`

`P` is a type over `(Γ, x : S)`, a large elimination into codes:

```
P(x) = El^{lp}( case x of { inj_i c ⇒ π_i(c) } )        motive Ty lp (constant)
π_i(c) = ⌜Empty^{lp}⌝                      constructor i has no recursive field
       = ⌜Unit^{lp}⌝                       its recursive field is plain
       = ⌜A_i⌝[srefl, fst(snd c), …]       its recursive field is (y: A_i) -> D
```

`A_i` is lowered by the same walk that builds `⟦Cᵢ⟧` (tier 0 §3.1): in the
field context after the nominal tag and the payload fields *before* the
function field, so it is scoped over `(Γ, #tag, p₀, …, p_{j-1})`. In the
branch those binders are replaced by the branch value's projections — the tag
by its canonical inhabitant `srefl` (the tag is an `sEq`, irrelevant), payload
field `m` by tier 0's `fst(snd^{m+1} c)`. The case tree is tier 0 §6.1's
right-nested constant-motive tree.

`lp` is the function domains' common level (§1.5). Non-cumulativity is why it
has to be common: every branch is a code at `Ty lp`.

## 5. The type

```
W₀   = W^{ls, lp}(x : S). P(x)                       at lw = ls ⊔ lp
⟦D⟧  = Σ^{lw, lw}(t : W₀). El^{lw}(canon t)           at lw
canon(t) = elim_W^{ls,lp,lw+1}(x:S. P; _. Ty lw; a f ih. CANON; t)
```

`CANON` is the step over `(Γ, z, a : S, f : Π(y : P a). W₀, ih : Π(y : P a).
Ty lw)`. It cases on `a`, and — tier 1 §6's lesson — it has to **generalize
`f` and `ih` into the case motive**, because outside a branch `P a` is stuck
on the variable `a` and neither `f₀` nor `ih ⟨⟩` typechecks against it:

```
CANON = (case a of Q) f ih
Q(v)  = Π(f' : Π(y : P v). W₀). Π(ih' : Π(y : P v). Ty lw). Ty lw
branch i, value c:
    λf'. λih'. ⌜Id(Π(y : P(inj c)). W₀; f₀; f')⌝     leaf
    λf'. λih'. ih' ⟨⟩                                  plain
    λf'. λih'. ⌜Π(y : A_i[c]). El(ih' y)⌝              function
f₀ = λ(y : P(inj c)). elim_Empty(_. W₀; y)
```

`tag_of` reads the declaration back through the `Σ` and the `W` to the shape
(tier 1 §4's one case more), and `spine` splits the shape exactly as it does
under a `Wf`.

## 6. Constructors

```
⟦Cᵢ(ā)⟧ = ⟨ sup(ℓᵢ; f_i) , q_i ⟩
```

- `ℓᵢ` is tier 0 §4's label, from the payload arguments only — the same
  `build_fields`/`inject` as tier 1.
- leaf: `f_i = f₀`, `q_i = refl(f₀)`.
- plain child `t` (checked at `⟦D⟧`): `f_i = λ(y : P ℓᵢ). fst t`,
  `q_i = snd t`.
- function child `k`, checked at `Π(y : A_i[ā]). ⟦D⟧`:
  `f_i = λ(y : P ℓᵢ). fst(k y)`, `q_i = λ(y : P ℓᵢ). snd(k y)`.

`A_i[ā]` is `P ℓᵢ` read back: the weak-head normal form of `P` at the label,
which unfolds the case to the branch's code and decodes it. Reading it off the
type, rather than re-lowering the field, is tier 0's annotation discipline.

`q_i`'s type is `El(canon(sup(ℓᵢ; f_i)))`, which reduces by `elim_W` β and the
case on the injection to exactly the per-kind form of §5.

As landed the child is bound once, `(λc. ⟨sup(ℓᵢ; f_i[c]), q_i[c]⟩) child`,
so the tree and the proof read one closure of it (§14).

## 7. `match`

Given `M` over `(Γ, z : ⟦D⟧)` at `lm` and a scrutinee `s`:

```
match s ≡ elim_W(x:S. P; w. M'; a f ih. STEP; fst s) (snd s)
M'(w)   = Π(c : El(canon w)). M[⟨w, c⟩/z]
STEP    = (case a of Q_M) f ih
Q_M(v)  = Π(f' : Π(y : P v). W₀). Π(ih' : Π(y : P v). M'(f' y)).
              Π(c : El(canon(sup(v; f')))). M[⟨sup(v; f'), c⟩/z]
```

The result has type `M[⟨fst s, snd s⟩/z]`, which is `M[s/z]` by Σ-η. Branch
`i` is `λf'. λih'. λc. ARMᵢ`, with tier 0's payload aliases (`fst(snd^{m+1}
x)`) and:

| constructor | recursive binder aliases to | `ARMᵢ` |
|---|---|---|
| leaf | — | `J(Π(y : P(inj x)). W₀; f₀; g p. M[⟨sup(inj x; g), p⟩]; arm; f'; c)` |
| plain | `t := ⟨f' ⟨⟩, c⟩` | `arm` |
| function | `k := λ(y : A_i[x]). ⟨f' y, c y⟩` | `arm` |

with `arm` the user's arm checked at `M` at its own constructor form, which is
convertible with `M[⟨sup(inj x; f'), c⟩]` by §2.3 at the plain and function
kinds and is `M[⟨sup(inj x; f₀), refl⟩]`, `J`'s base case, at a leaf.

## 8. Recursion

The ih is a self-call, as in tier 1 §6.4, matched by **term**:

- a call whose decreasing argument is the plain binder's term `⟨f' ⟨⟩, c⟩`
  becomes `ih' ⟨⟩ c`, at `M[⟨f' ⟨⟩, c⟩]`, which is `M[t]`;
- a call whose decreasing argument is `k e` — an application whose head is
  the function binder's term, at **any** argument `e` — becomes
  `(λy. ih' y (c y)) e`, at `M[k e]`. This is the only new guard shape, and it
  is what "structural recursion through `k`" means: every `k e` is a
  subtree, whatever `e` is.

The rest of tier 1's guard carries over unchanged: saturated, descending in
the `match`'s own parameter, generalized parameters applied to the ih.

## 9. No-confusion

- **`absurd`** is tier 1 §7.1 on the `W`: the tag predicate is `elim_W` at the
  constant motive `Ty 0` over `fst s`, its step the constant case tree
  returning `⌜Unit⌝`/`⌜Empty⌝`. No generalization is needed: the predicate
  never reads `f`.
- **`inj`** at a **payload** field is tier 0 §6.2's projection, inside the
  same constant-motive `elim_W`.
- `inj` at a recursive field is **not** generated: the plain child's
  projection would need `f`'s generalization (tier 1 §7's correction), and a
  function child's injectivity is funext. Diagnosed.

`read_ctor` reads a tier-2 value through its `Σ` and its `sup`, and the label
carries everything `absurd` and payload `inj` need.

## 10. Acceptance

Against `docs/testing-generated-terms.md`'s axes, in
`crates/elab/tests/inductive_tier2.rs`:

1. A three-constructor tree with a leaf, a plain child and a function child
   declares, and its constructors check, at open payloads and an open element
   type (axes 2 and 6).
2. Closed computation through a function child: a `match` and recursion
   through `k(e)` evaluate by `refl` (axis 1, literal).
3. β on open subterms: `f(Vis(c, k)) = …f(k(e))…` with `c`, `k` open, by `refl`.
4. A dependent motive at every kind, including the leaf, proved by induction
   at a neutral `t` (axis 3): `first(rebuild(t)) = first(t)`, and
   `first(bind(t, h)) = first(h(first(t)))` at an open element type. Not
   `bind(t, Ret) = t`: its `Vis` case needs `λx. bind(k x, Ret) = k` from the
   pointwise ih, which is funext (§12).
5. A neutral scrutinee does not compute (axis 1, neutral; axis 4).
6. Negative controls: a self-call at a non-subtree is refused; a false
   equation between two trees that differ only under a function child is
   refused (axis 4); every §1 restriction is a rejection with its message.
7. `absurd` between constructors, `inj` at a payload field.
8. A tier-1 declaration still lowers onto `Wf`.

## 11. What this amends elsewhere

- `issues/inductive-compiler.md`: tier 2 has a generator for the §1 fragment.
- `docs/inductives/inductive-tier1-wf-lowering.md` §8: infinitary branching is lowered,
  not merely classified.
- `reject_function_fields` stops rejecting the §1 shape.

## 12. As landed

Mechanized in `crates/elab/src/infinitary.rs` (the type, the constructors,
`match`, and the constant-motive eliminator `absurd`/`inj` use), with the
classification in `inductive.rs` and the guard in `recursion.rs`. Acceptance
is `crates/elab/tests/inductive_tier2.rs`, every term kernel-checked. Writing
it changed or added the following.

1. **One generic case tree, three uses.** The positions `P`, the leaf
   predicate's step and `match`'s step are each a tier 0 §6.1 right-nested
   `Case` over the shape, with the motive composed with the injection at each
   depth. `w_case_tree` takes the branch as a closure, so the composition is
   written once; `wf.rs`'s `wf_case_tree` is the same recursion with a fixed
   branch.
2. **The leaf predicate's `Fn` branch needs no `π_i`.** §5 writes it as
   `⌜Π(y : A_i[c]). El(ih' y)⌝`. The code of `P(inj c)` *is* the case tree at
   that label, which reduces to `π_i(c)`; the branch uses it as is and the
   positions are lowered in one place only. The same holds for the leaf's
   `Id` code.
3. **`k`'s domain is shown, not normalized.** A whnf of `P(ℓ)` takes the case
   on the injection and then δ-unfolds the domain's own head, so `k: Resp(c)
   -> D` read back as `Resp`'s body. `WParts::pos_shown` takes only the case
   steps on injections and one decode step, so a goal shows
   `k : Resp(c) -> Tree` and a constructor checks `k` at `Π(y : Resp(c)). ⟦D⟧`.
   Conversion does the rest wherever it is needed.
4. **Type arguments from a function child.** `Vis(c, k)` in an inferring
   position recovers the instance from `k`'s type: the codomain of its Π,
   strengthened past the binder (`ctor_from_child`). A lambda argument still
   needs a checking position or `Vis<R>(…)`, like any lambda.
5. **The descend diagnostic names the tier-2 rule** (`recursion.rs`): a call at
   a value built *around* `k(e)` is refused with "a recursive field, or the
   function field applied to an argument".
6. **`absurd` and payload `inj` reuse tier 0 whole.** `const_elim_w` is
   `const_elim_wf` on the `W`: `elim_W` at the constant motive over `fst y`,
   its step `const_case_tree` on the label. `read_ctor` reads the label out of
   the `sup`; a child field reads back as a stand-in, since `inj` at a
   recursive field is refused (§9) before it would look.
7. **Kept out of tier-0-only paths.** Every `!recursive` test that meant
   "tier 0" now also excludes tier 2: certgen's result and parameter types,
   `split`'s finite case domains, the function-IR structured source, and an
   index type. `register_gen_defs` is skipped (§1), so tier 2 has no
   generated globals and no module-image entry beyond its field kinds (byte 4).
   (Since §13 it has one: the leaf predicate, `D#canon`.)
8. **What the encoding cannot prove.** Two trees that agree pointwise under a
   `Vis` are not equal: `rebuild(Vis(c, k)) = Vis(c, k)` is refused, and so
   is `bind(t, Ret) = t`, because their `Vis` cases need funext. That is a
   property of `W` without `Ψ` axioms, not of this lowering, and it is what
   `issues/interaction-trees-container-model.md`'s depth-indexed equivalence
   is for: the tree laws are stated up to it, not up to `=`.
9. **Inherited, not introduced:** a deep pattern at a payload field that a
   later field's type depends on (`Vis(Ask, k)`) is accepted by the
   elaborator and rejected by the kernel, at tier 0 as here, since a nested
   `match` on a field has a non-dependent motive
   (docs/language/matching/nested-match-patterns-design.md §10.2). Filed as
   `issues/deep-pattern-dependent-later-field.md`.

## 13. The leaf predicate as a generated definition

Added 2026-10-21 (`issues/tier2-fragment-extensions.md`, generated
definitions), measured first on the library that made it matter,
`lib/std/itree/itree.hthr`.

**Why this one.** `canon` (§5) is a large elimination whose step is a case
tree carrying, per constructor, the children's type, the ih's type and, at a
leaf, an `Id` code over `f₀`, so it writes `W₀` (and with it `P`) out several
times per constructor. Inline it was about 97% of `⟦D⟧`'s spelling for a
four-constructor tree, and `⟦D⟧` is in every `fst`/`snd`/pair annotation of
a tier-2 value: the `match` of §7 alone writes it into the scrutinee's
projections, each recursive binder's alias, and the motive at each branch.
The kernel spent the gate comparing and shifting those copies. `S` and `P`
are an order of magnitude smaller and stay inline.

**The definition.** At declaration time, over the telescope `D#tycode_fn`
uses (`docs/inductives/per-instantiation-type-codes-design.md` §2: every type parameter
at `Ty 0`, the value parameters at their declared types, domains in the
emission spelling):

```
D#canon : Π(A₁ : Ty 0)…(v_m : T_m). Π(t : W₀). Ty lw
D#canon = λ(A₁ : Ty 0)…(v_m : T_m). λ(t : W₀). elim_W(…; t)     -- §5's canon
```

with the body the inline predicate `lower_instance_w` builds in that context
(inline because the key is not registered yet). It is an ordinary bodied Ψ
binding and faces the same gate as every generated definition.

**The spelling.** `lower_instance_w` itself writes the second component as

```
El^{lw}(app(D#canon^δ; ⌜A₁⌝, …, v₁, …, t))
```

(`AppAt` nodes: the head is a global and infers its own Π) whenever the
declaration registered one, every type argument is at level `0`, and the
registered statement ends in `Ty lw` at the instance's own `lw`. Anything
else, today a type argument at another level such as a tree of `Type`s,
keeps the inline `elim_W`. The two spellings are δ-convertible, and
`crates/elab/tests/inductive_tier2.rs` builds, matches, computes and refuses
at both in one module.

**Why the lowering and not an emission respell.** Tier 0 and tier 1 keep
`⟦D⟧` inline as the elaborator's identity and respell only at emission,
behind a structural guard, because their structural readers
(`tag_of`, `spine`, `const_elim_wf`, the fingerprints) pattern-match `⟦D⟧`
itself. No reader looks inside the leaf predicate: `WParts::read` takes `⟦D⟧`
apart at the `Σ` and the `W`, the tag and the spine come from `S`, and every
emission reuses the second component exactly as it was found. So the
reference can be the lowering, with no inline copy to guard against, and
every site that builds a tier-2 annotation shrinks without being touched.
`WParts::read` accepts either spelling of the second component (an `elim_W`,
or an application spine headed by a global), and neither is read further.

**Effect.** On `lib/std/itree/itree.hthr` the gate of each law proved by induction
fell by an order of magnitude and more, with the query, miss and step counts
falling in step; the shape is the per-copy cost of a predicate the terms now
mention once per annotation instead of spelling.

## 14. The child, evaluated once

Added 2026-10-21 (`issues/tier2-left-nested-bind-cost.md`).

**The defect.** §6 writes a child into both components: a plain child as
`fst t` in the tree and `snd t` in the proof, a function child as
`λy. fst(k y)` and `λy. snd(k y)`. Each is an evaluation of its own, because
the evaluator memoizes a closure, not a term, and the two occurrences are
two closures. So reading a constructor's tree and its proof evaluated the
child twice. A `bind`'s `Ask`/`Vis` arm is such a constructor over
`k' = λx. bind(k x, f)`, and `bind(k x, f)` reads both halves of `k x`, so
each level of a left-nested `bind` doubled the work below it: a tactic
`lspin(d)` (`lspin(j).bind(λ _ => tick())`) cost `2^d` in its depth, and an
interaction tree built the same way did the same under `thread`.

**The fix, in three parts, each of which the measurement needed.**

1. *The constructor binds the child once* (`build_ctor_w`):
   `(λ(c : C). ⟨sup(ℓᵢ; λy. fst(c…)), …snd(c…)…⟩) child`, with `C` the
   child's type (`⟦D⟧`, or `Π(y : A_i[ā]). ⟦D⟧`). A plain child is then one
   closure that both projections force; that alone is the whole fix for
   `Tau`-like children.
2. *The kernel shares `fst(k y)` with `snd(k y)`* (`Eval::eval_projected`):
   a projection of an application whose head and argument are both bound
   variables memoizes the application's value by the two closures they are
   bound to (seen through closures that are only a variable: the match's
   alias `k := λy. ⟨f' y, c y⟩` passes each half its own closure of `y`).
   This is what a function child needs, since its halves apply `c` to an
   answer only when asked. The table is the arena's, kept like the force
   cache; `shared_apps` counts its hits.
3. *The tactic host's arena keeps what it forces* (then `ValueArena::retaining`;
   since 2026-10-22 every arena does, `ValueArena::cache_tm`).
   A run builds every resumed tree out of closures earlier resumes forced; with
   the query-sized bound, once a run had forced more values than the cache
   holds, the oldest were evicted and recomputed back through the run's
   history, which brought the steep growth back at a few dozen levels.

**Effect.** A left-nested run is quadratic in its depth instead of
exponential: each request still walks the `d` binds above it, which is the
cost of a left-nested free monad, not of the encoding. A right-nested run is
unchanged in shape. The parts were checked by ablation: without the
first, or without the second, the `2^d` remains; without the third it is
gone at small depths and the growth turns steep again past a few dozen
levels. The remaining wall is the native depth: a run
whose first request sits under a few hundred left-nested binds fails before
answering it.
