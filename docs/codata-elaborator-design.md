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
  SCons(Succ(h), smap(t)) }`). Indexed, a `match` on a term the index
  mentions (`fn v(n) → Bisim(sp(n), sp(n)) { match n { … } }`) hands
  each arm the step type at the *refined* index, `F(C)(idx[n := Zero])`:
  `step_index` reads that index off the named shape's last argument
  (`El(D#mshape ā idx)`), holds the whole step type to it by conversion,
  and the arm's node is built from `MParts::reindexed` there, the match's
  motive carrying it back to the body's index (2026-11-06,
  issues/corec-match-on-index-term.md; before, the arm fell through to
  the ordinary constructor path and was refused as "not the expected
  type"). An inline signature (a type argument above `Ty 0`) has no named
  shape to read, and still falls through
  (issues/corec-match-on-index-term-inline-sig.md).
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

- **under a friend** (§5.5), the carrier is the free algebra of the friends
  and the child type is `C + ⟦D⟧` over it: a friend's call is the child
  `inl(node)`, its codata arguments leaves (seeds, existing trees) or friend
  nodes in turn.

Every other self-call is refused as unguarded: in a payload (`SCons(hd(bad(n)),
…)`), under an observation (`tl(bad(n))`), alone (`bad()`), or inside any tree
that is not a constructor of the declaration and not a friend's call
(`SCons(n, tl(bad(n)))`: `tl` reads two layers, so it is not a friend, §5.5).

### 5.3 What it does not do

- No mutual corecursion and no corecursion through a helper function: one
  `fn`, one `corec`.
- No "productive up to" calls beyond friends (§5.5): `bind`'s `Ret(r) =>
  h(r)` is the existing-tree case, which is fine; a call under a function
  that is not a friend, guarded only after that function's unfolding, is
  not.
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
- **Indexed codata** (added 2026-11-02, `issues/codata-nested-guards-indexed.md`):
  the layers are families over the index,

  ```
  C₀(i) = X(i) = Σ(v : V). Id(I; g[v]; i)
  C_{j+1}(i) = X(i) + F(C_j)(i)
  F(C)(i) = Σ(s : S(i)). Π(p : P(i, s)). C(o(i, s, p)) + ⟦D⟧(o(i, s, p))
  ```

  (the kernel's `m_step_ty` over `C`). Only a seed carries an equation; a
  pending node needs none, since it is built at its child's index `o(g, s,
  p)` and not the step's `g`. So the node's parts are read there
  (`MParts::reindexed`): its payload is checked at the child's index and
  its own children at theirs, and a self-call under it is the coinduction
  hypothesis at that index, checked by conversion as at the top. The
  step's `J` along the carrier's equation moves the `inl` arm only, `case x
  { inl(v) ⇒ J(…; body[v]; snd v); inr(node) ⇒ lift(node) }`, the `inr`
  arm being at `i` already; `lift` and `embed` take the index they work at
  and read each child's own. The node's index is read the way the child
  wrote it (`written_index`: a named signature's `D#mnext` unfolded and
  the projections out of the step's index read off, no other global
  unfolded), so a wrong payload is reported at its own `refl` with both
  sides spelled. `tails(tl(s), tl(s), tails(s, s, sb_two(s))) =
  sb_two(tl(tl(s)))` holds by `refl`, `J` computing at `refl` under the
  `inl` arm one layer down.

### 5.5 Corecursion up to friends

A call may sit under a **friend**: a function of the definition's own codata
type that consumes at most one layer of each codata argument to produce one
layer of output (Blanchette, Bouzy, Lochbihler, Popescu and Traytel,
*Friends with Benefits*, 2017). The customer is the Leibniz (Hurwitz) product
of formal power series, `(fg)' = f'g + fg'`:

```
fn sadd(s: Stream, t: Stream) -> Stream {
    match s { SCons(a, s2) => match t { SCons(b, t2) => SCons(add(a, b), sadd(s2, t2)) } }
}
fn smul(f: Stream, g: Stream) -> Stream {
    SCons(mul(hd(f), hd(g)), sadd(smul(tl(f), g), smul(f, tl(g))))
}
```

**Which functions are friends.** Decided syntactically on the friend's own
definition, with no registration and no proof obligation: the check is the
friend's body elaborating over the free carrier below ("friend mode"), and
the kernel checks the result as part of the definition's `corec`. A candidate
is a call inside one of the declaration's constructors, to a global `fn`
whose result is the definition's codata type, with a corecursive call among
its arguments; a function of another result type is not a candidate, so the
guard's own messages stand for it (`SCons(hd(bad(n)), …)`). In friend mode a
codata parameter `s` (a parameter of the definition's codata type) may be

- the scrutinee of a `match` whose arms bind plain names: the arm reads the
  node of `s` (its label and its children, at `C + ⟦D⟧`);
- an argument of the friend's call to itself, which must be a child of the
  constructor its step returns;
- a child of that constructor, or the whole result (`append`'s `CNil => b`):
  the output is then `s`'s own first node.

A child bound by such a `match` may be passed on as a child or as an
argument to the friend itself (applied, for a function child). Anything
else is refused with the place it happened, said at the definition's call:
reading a child again (`skip(tl(s2))`, two layers, which would make
`f = SCons(n, skip(f))` unproductive), using `s` as a tree (`hd(s)`), a
call to itself outside a child, or a codata argument inside a tree the step
builds. Other parameters are **data**: stored in the friend's node.

**The carrier** is the free algebra of the definition's friends over its
seeds and existing trees, a finitary tree (`Wf`, so the children are a
`Vec`, compared by conversion):

```
S = X + (⟦D⟧ + (A₁ + (… + A_m)))      A_f = friend f's data arguments' tuple
n(a) = case a { X ⇒ 0; ⟦D⟧ ⇒ 0; A_f ⇒ friend f's codata arity }
C = Wf(a : S). n(a)
```

In the body, a corecursive call at a child is the leaf `inl(sup(inj_X(seed);
⟨⟩))`, a friend's call `inl(sup(inj_{A_f}(data); ⟨c₁, …, c_k⟩))` with each
codata argument a seed leaf, a friend node in turn, or an existing tree's
leaf `sup(inj_D(t); ⟨⟩)`; any other child is `inr(t)` as before. The seed
is `sup(inj_X(⟨varying⟩); ⟨⟩)`.

**The step** is structural recursion on the tree,

```
step(x) = elim_Wf(x; a cs ih. (case a of
            X v    ⇒ λcs ih. body[v]
            ⟦D⟧ t  ⇒ λcs ih. (λo. ⟨fst o, λq. inr(snd o q)⟩)(out t)
            A_f d  ⇒ λcs ih. friend_f(d, cs, ih)) cs ih)
```

the case a convoy, since `cs : Vec(C; n a)` and `ih : Π(i : Fin(n a)).
F(C)` are typed at `a`. `friend_f` is the friend's body elaborated over `C`
with its data parameters bound to `d`'s components and its codata parameter
`j` to the carrier value `cs_j`, whose node is `ih(j)`; its own call is a node
of `C` (a child pattern variable `y : C + ⟦D⟧` enters as `case y {inl c ⇒ c;
inr t ⇒ sup(inj_D(t); ⟨⟩)}`). So a friend node's step reads its arguments'
first nodes, which the `Wf` recursion has already computed, and produces one
node: productivity is the `corec`'s, termination the `Wf` recursion's, and
neither rests on the friendliness check, which only decides what elaborates.

**Friend mode** re-elaborates the friend's surface body at each definition
that calls it, under the friend's own module's names (`Cx::hygienic`, the
module's resolution scope), from the declaration a module image keeps. Its
body is not stored as a separate carrier-polymorphic term: that would need
the carrier's universe level abstracted, and the definition's own carrier
is in hand.

**What `refl` keeps.** Observations compute as far as the friend's own
unfolding does: `hd(tl(smul(f, g))) = add(mul(hd(tl f), hd g), mul(hd f,
hd(tl g)))` and `nth(smul(from(1), from(1)), 2) = 14` hold by `refl`, the
friend node's step running both seeds' bodies. A tree under a friend is not
convertible with the friend applied to the trees: `tl(smul(f, g))` is a
`corec` over the friend node, not `sadd(smul(tl f, g), smul(f, tl g))`.
Their equality is a bisimilarity.

**Round 1 did not do** indexed codata, polymorphic friends, friends with
function-valued codata arguments, or constructors nested beside a friend;
round 2 (§5.6) replaced the `Wf` carrier to do them.

### 5.6 The free carrier as an indexed tree (round 2)

Round 2 (`issues/codata-up-to-friends-round-2.md`, 2026-11-03) gives friends
codata arguments **at other indices than their result** and **under a
function**, which the up-to proofs of `docs/coitree-design.md` §7.6 need:

```
fn sb_trans(s, t, u, a: SBisim(s, t), b: SBisim(t, u)) -> SBisim(s, u)   // up to transitivity
fn dbind(t: Dl, h: Nat -> Dl) -> Dl {                                     // bind-shaped
    match t { Now(n) => h(n), Later(t2) => Later(dbind(t2, h)) }
}
```

**The carrier** is now an ordinary `W` type over one sum of shapes, with the
indices kept in a predicate beside it rather than in the tree (an indexed
`W` would fix every child's index by its parent's shape, and a friend's node
does not know its arguments' indices until its label is read):

```
W₀  = W(x : V + Σi.⟦D⟧(i) + [Σi.S(i)] + A₁ + … + A_m). P(x)
P(x) = case x { V ⇒ ∅; ⟦D⟧ ⇒ ∅; S ⇒ positions of the node; A_f ⇒ P_f }
C(i) = Σ(t : W₀). ok(t)(i)                     C = W₀ unindexed
ok   = elim_W(t; a f ih. λj. Σ(e : out(a) = j). Π(p : P a). ih p (child(a, p)))
```

`V` is the seed (the varying parameters' tuple), `⟦D⟧` an existing tree,
the bracketed summand a pending node (constructors nested above a call,
§5.4, now combined with friends), and `A_f` friend `f`'s label: its data
arguments **including the indices its codata arguments sit at** (the
intermediate `t` of `sb_trans`). `P_f` has one position per codata argument,
and a function-valued one `h : Π(y : B). D(o(y))` contributes the summand `B`
(its payload), so its child at `inr(y)` is `h(y)`. `out(a)` is the index a
node sits at (the seed's `g[v]`, the tree's own, the friend's result index
read off its label) and `child(a, p)` the index its children were written
at; `ok` says every node sits where its parent wrote it. All of `P`, `out`
and `child` are cases on the shape into codes, so the kernel computes them
for literal labels and the step's `J` along `fst(ok)` is a `refl` at every
node the definition built.

**The step** is `elim_W` on `fst x` with motive `Π(j : I). El(ok z j) →
F(C)(j)`, each branch moving the node from `out(a)` to `j` along the
proof's first component: the seed runs the body at the varying tuple, a tree
is observed, a pending node emits itself with its children paired with their
proofs, and a friend runs its re-elaborated body with its codata parameter
`j` bound to the carrier value `⟨f(inl j), snd ok (inl j)⟩` (a function
parameter to `λ y. ⟨f(inr y), …⟩`), whose first node is `ih` at that
position. Productivity and termination stay the `corec`'s and the `W`
recursion's; the friendliness check only decides what elaborates.

**Friend signatures** are read in two passes. Pass one binds the friend's
type and value parameters and matches its result type's signature
telescope (`CoTree<R>(E)`'s `R, E`) against the definition's: matched type
parameters are fixed to the definition's, matched value parameters become
aliases of the definition's terms. Pass two classifies the rest: a
parameter whose type is the definition's family at some index, plainly or
under one arrow, is a codata argument (a child of the node); anything else
is data, stored in the label, including type parameters the result does not
fix (`bind_up<A, B>`'s `A`), which the call must then write
(`Eutt::bind_up<Step<A, B>, B>(…)`). A friend's result index must be the
index of the position its call sits at: `sb_trans(s, s, s′, …)` at a child
of type `SBisim(s, s)` is refused at the call ("a friend's result index must
be the one its position wrote"), naming both.

**In friend mode**, beyond §5.5's: `match` on a function parameter applied
to a payload (`match h(n)`, one layer of `h`'s answer at `n`), the applied
parameter as the whole result (`Now(n) => h(n)`), a function child passed
whole as a function child (η-expanded), and friend calls at a friend's
codata argument (`up_to_bisim(…, bind_up(…, λ x => … self …), …)`): the
carrier is the free algebra of every friend the definition calls.

**What it still does not do** (logged in the issue):

- a friend at the top of the body, unguarded (`f(…) = trans(…, f(…))`):
  the seed's step must produce a layer, and a friend node over seeds only
  produces one by stepping the seeds again, which is not structural on the
  `W` tree. Wrap the statement in one constructor (`Eutt(CTau(x), CTau(y))`)
  and peel it with `tau_l`/`tau_r` afterwards, as `iter_cong` does in
  `lib/_tests/std/itree/coitree_eutt_tests.hthr`;
- friends that call other friends in their own bodies, and friends with
  class binders (series over a ring);
- a codata argument at another *instance* of the family as a child
  (`bind`'s `t : CoTree<A>` under a `CoTree<B>` result): it is data, read
  as a whole, which `Eutt::bind_up` uses (its `e : Eutt<A>` is matched as
  data), but a self-call on its children is a data argument, so a direct
  coinductive `rec` through `bind` still waits.

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
  `CoTree` and a `Bisim` that matches two observations per step;
  `codata_indexed.rs` has the indexed cases (two and three layers at
  literal and neutral indices, `Seq<A>`, `match` in step position, a
  function child whose domain is read at the pending node's index, and
  controls: a nested call at the wrong index, a wrong payload, a wrong
  observation).
- **corecursion up to friends** (§5.5): the Hurwitz product up to stream
  addition at neutral and literal streams, a friend with a data argument
  and a fixed parameter, a friend returning its argument (`append` on a
  colist), a friend over function children with the call in a `match` arm
  under a λ, a friend replayed from another module's image beside a
  same-named global, and controls: a wrong observation, a friend reading
  two layers (`skip`), one using its argument as a tree (`peek`), a call in
  a friend's data argument, and nested constructors beside a friend.

Plus a module-image round trip (`codata_round_trips_through_images`): the
declaration, its constructors and a corecursive function written to an
image, replayed, and used from an importing module.

## 8. Next

1. ~~**Indexed codata**~~: done (`docs/codata-indexed-design.md`).
2. **The library** (design §10 step 5): the coinductive `ITree` with `bind`
   and `iter`, `approx` into the finite tree, `Bisim`, eutt, and the bridge
   `Bisim ⇔ Π n. Same(approx n t, approx n u)`.
3. ~~**Nested guards**~~: done (§5.4), unindexed 2026-11-01 and indexed
   2026-11-02.
5. ~~**Corecursion up to friends**~~: round 1 done (§5.5, unindexed,
   monomorphic friends), 2026-11-02; round 2 (§5.6: indexed, polymorphic,
   bind-shaped, nested beside friends) 2026-11-03; what is left is
   `issues/codata-up-to-friends-round-2.md`.
4. ~~Codes for `M`~~: done (`docs/kernel-m-codes-design.md`).
