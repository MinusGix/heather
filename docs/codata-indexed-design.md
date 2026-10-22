# Indexed codata

Status: implemented, 2026-10-22 (`crates/elab/src/codata.rs`,
`crates/elab/tests/codata_indexed.rs`). Issue: `issues/codata-indexed.md`. It extends
`docs/codata-elaborator-design.md` (whose section numbers it cites as
"codata §n") onto the kernel's indexed `M`
(`docs/kernel-coinduction-design.md` §1). It is what `Bisim` and eutt need
(that design's §4, milestone `it-coinductive`).

---

## 1. The decision: the index is in scope, and there are no result annotations

An indexed inductive states each constructor's index as a **result
annotation** (`VCons(…) : Vec<A>(Succ(n))`), and the lowering stores or
computes the equation between that index and the family's
(`docs/inductive-indexed-lowering.md`, `docs/inductive-fording-lowering.md`).
For codata that form is the wrong one, for the reason that makes codata
codata: **there is no η**. The indices codata most wants are trees, and an
equation `Id(Stream, SCons(h, a), s)` holds only when `s` is that constructor
term exactly. `from(0)` is a `corec` over `Nat`, `SCons(0, from(1))` a
`corec` over the out type, and they are not convertible (codata §2). So a
bisimilarity written with result annotations,

```
codata SBisim : (s: Stream) -> (t: Stream) -> Type {
    Same(h: Nat, a: Stream, b: Stream, k: SBisim(a, b)) : SBisim(SCons(h, a), SCons(h, b)),
}
```

could never relate `from(0)` to anything. The index has to be read by
**observation**, and the kernel's `M` already says how: the shape at index
`i` is any type computed from `i`, and the children's indices are computed
from `i`, the shape and the position (`next`).

So the surface puts the index binders **in scope in the constructors' field
types**, and a recursive occurrence **writes its child's index**:

```
codata SBisim : (s: Stream) -> (t: Stream) -> Type {
    Same(heads: hd(s) = hd(t), tails: SBisim(tl(s), tl(t))),
}
```

This is the kernel's `Bisim` (kernel design §4) spelled at the surface, with
the observations written as ordinary functions. eutt is the same with a
computed shape (a peel bounded by `Nat` counts, or an inductive `Peel`
whose index is the observation), and an index that genuinely is an
inductive value (`Count : (n: Nat) -> Type`) needs no special form either:
an equation is a field, `e: n = Succ(m)`, when a constructor wants one.

A result annotation on a `codata` constructor is refused, with this
section's reason.

## 2. Surface

```
codata D<ā>(v̄) : (i₁: I₁) -> … -> (iₙ: Iₙ) -> Type { C(x̄), … }
```

- The **index telescope** is one or more named binders ending in `Type`.
  Each `Iₖ` may mention the type parameters, the value parameters and the
  earlier index binders. Unlike an indexed inductive's, the index types are
  not restricted to `Nat` or a declared inductive: any type with a code.
- Value parameters and an index combine (an inductive refuses the pair;
  `docs/surface-value-parameters.md` §6). `ITree<R>(E)`'s bisimilarity needs
  both.
- The index binders are in scope in every field type of every constructor:
  payload fields and function children's domains.
- A **recursive occurrence** is `D<ā>(v̄, ē)`: the type parameters and the
  value parameters bare and in order, as today (`uniform_occurrence`), then
  one expression per index binder. The expressions may mention the index
  binders, the payload fields declared before the child, and a function
  child's own binder (`k: (y: A) -> D(f(y))`).
- A use is `D<ā>(v̄, ī)`, one argument list: value parameters, then indices.
  A use without the indices is refused, as for an indexed inductive.

## 3. Lowering

```
⟦D<ā>(v̄, ī)⟧ = M(I; i. S(i); i s. P(i, s); i s p. o(i, s, p))(⟨ī⟩)
```

- `I` is the telescope's right-nested `Σ` (the type itself for one binder),
  and `⟨ī⟩` the tuple of the arguments.
- `S(i)` is tier 1's shape (codata §2) with each index binder bound to its
  projection of `i`: the field types are lowered over `(Γ, i)` with aliases
  `iₖ ↦ πₖ(i)`, the same carrier as value parameters' aliases.
- `P(i, s)` is unchanged except that its case tree is over `(Γ, i, s)`, so a
  function child's domain may mention the index.
- `o(i, s, p)` is new: a case on `s`'s tag, then down the sum of the
  constructor's positions (the same tree `match` builds), and at child `r`'s
  leaf its written index tuple, elaborated with the index aliases, the
  payload fields as projections of the branch value, and a function child's
  binder as the position's payload.

An unindexed declaration keeps codata §2's lowering exactly (`I = Unit`).

## 4. Constructors

The unindexed constructor is a `corec` over `Unit` whose step is closed over
the arguments (codata §3). That step cannot be reused: `corec`'s step must
return a node at **every** index `i`, and the arguments only make one at
the expected index `j`. The apomorphism's `in` with the out type as the
carrier is uniform in `i`:

```
C(x̄) at D(j)  ↦  corec(sig; i. Out(i); i x. ⟨fst x, λp. inr(snd x p)⟩; j; ⟨ℓ_C(x̄), kids⟩)
Out(i) = Σ(s : S(i)). Π(p : P(i, s)). D(o(i, s, p))
```

and `out(C(x̄)) ≡ ⟨ℓ_C(x̄), λp. kids(p)⟩`, which is `kids` up to the
kernel's η for functions. Each child is checked at its own index,
`D(o(j, ℓ_C(x̄), pos_r))`, which reduces to the written `D(e_r)` because the
label is a literal injection.

## 5. `match`

As codata §4: `out` the scrutinee and case on the label. Each child is bound
at its own index, `snd o (pos_r ⟨⟩) : D(o(j, ℓ, pos_r))`. The motive stays
non-dependent in the scrutinee, and the index is not refined: it is a term
of `I`, and there is no equation to transport along. What a branch learns
about the index it learns from the payload, which is where §1 puts it
(`heads : hd(s) = hd(t)`).

## 6. Corecursion

A corecursive function into an indexed codata type is coinduction proper:
`fn sb_refl(s: Stream) -> SBisim(s, s) { Same(refl, sb_refl(tl(s))) }`.

- **Carrier.** With result type `D(g(ā))` over the parameters, the carrier
  is the family `X(i) = Σ(varying ā). Id(I; g(ā); i)`. The result type may
  now mention varying parameters (it may not in the unindexed case, codata
  §5.1, and still may not there).
- **Body.** Elaborated once in the body's context against the step type at
  `g(ā)`, `Σ(s : S(g)). Π(p : P(g, s)). X(o) + D(o)` with `o = o(g, s, p)`.
  A child position is now recognised by its shape, `X(e) + D(e)` at any
  index `e`, since each child has its own.
- **Self-call.** `f(ā')` at a child of index `e` is `inl(⟨ā'_varying,
  refl⟩)`, which needs `g(ā') ≡ e`. The elaborator checks that conversion
  itself and names both sides when it fails: this is the coinduction
  hypothesis being used at the index it was stated at.
- **Close.** The step is the body moved from `g(π x)` to `i` along the
  carrier's equation,

  ```
  λ i x. J(I; g(π x); i' e'. Step(i'); b[ā ↦ π x]; i; snd x)
  ```

  and the seed is `⟨ā_varying, refl⟩` at index `g(ā)`. `J` computes at
  `refl`, so `out(f(ā)) ≡` the body's node with each `inl` seed unfolded one
  step, as in the unindexed case.

Nested guards stay refused (`issues/codata-nested-guards.md`).

## 7. What stays out

- Result annotations on codata constructors (§1).
- Index refinement in `match` (§5).
- Certgen and export refuse indexed codata as they refuse codata.

## 8. Testing

`crates/elab/tests/codata_indexed.rs`, on the four axes:

- **literal and neutral**: `sb_refl(from(0))` and `sb_refl(s)` observed by
  `match` (`tails(s, s, sb_refl(s)) = sb_refl(tl(s))` by `refl` is `J`
  computing at `refl` under `out`); `count(2)` and `count(n)` at `Count :
  (n: Nat) -> Type`, two steps deep.
- **open element type**: a bisimilarity over `Seq<A>`.
- **checking position**: a constructor's child at the written index; `match`
  in step position (`sb_sym`, `sb_trans`, whose corecursive argument is
  itself indexed codata); a function child whose domain mentions the index
  (`Fin(Succ(n))`), with a value parameter beside the index; a two-binder
  telescope whose second type depends on the first.
- **negative controls**: a self-call at the wrong index, a result
  annotation, a use without its index, a child at the wrong arity, a wrong
  observation by `refl`.

Plus an image round trip and a goal display (`b : SBisim(s, tl(s))`).
