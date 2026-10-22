# Codes for `M`

Status: implemented, 2026-10-22 (`crates/kernel/tests/m_codes.rs`). This is step 6 of
`docs/kernel-coinduction-design.md` §10, brought forward on Minus's call so
that codata lands at layer c rather than through layer-p definitions
(`docs/codata-elaborator-design.md` §6, PR #131). Issue:
`issues/codata-codes.md`.

## 0. What changes

Today `Type::M`, `Term::Corec` and `Term::Out` pass only `Tc::computing_layer`
(layers p/m), like `IWf` and `DVec`. After this round:

1. **`M`, `corec` and `out` are admitted at layer c.** At c nothing
   computes under a box, so a boxed corecursive definition is a finite
   piece of syntax, and `□` comparison stays syntactic. Bisimilar code stays
   distinguishable as code. This is `Wf`'s situation exactly.
2. **A code former** `TmM` (a term of `Ty`) with its decoding.
3. **Four code-recursor branches**: `ty_m`, `tm_m`, `tm_corec`, `tm_out`
   (56 → 60).

Then PR #131's kernel relaxation (bodied term definitions at p) and the
elaborator's `decl_layer` are dropped: every declaration over codata is
bound at c again.

## 1. The code former

```
I code      u_I : Ty^{li}
i : El u_I  ⊢ u_S : Ty^l
i, s : El u_S ⊢ u_P : Ty^{l'}
i, s, p : El u_P ⊢ o : El u_I
j : El u_I
──────────────────────────────────────────────────────────────
TmM^{l,l',li}(u_I; i. u_S; i s. u_P; i s p. o; j) : Ty^{l ⊔ l' ⊔ li}

El(TmM(u_I; u_S; u_P; o; j)) ⇝ M(El u_I; i. El u_S; i s. El u_P; i s p. o)(j)
```

The index is part of the code, as `TmIWf`'s `at` is (`docs/iwf-former-design.md`
§6): a code is a whole type, and `M(σ)` is not a type until it is applied.
The level is the family level `l ⊔ l' ⊔ li`, the same as the type former's
(design §1.1). Whether the index level must appear there is still heather-coq's
§9 Q1. The code follows whatever that question decides.

`El` decoding is one more arm in both reducers' `El` step and in `code.rs`'s
`El`-of-code reader on the elaborator side. Spelling a lowered codata type
through its code is what lets `code::code_of` (the `Type → code` direction,
`crates/elab/src/code.rs`) cover codata, and that is what quotation needs.

## 2. The four branches

The telescopes follow the house scheme (`crates/kernel/src/rec.rs`):
universe binders first, then the context variable `g`, the code-layer
globals of the former's pieces, and one recursive local per piece. The
result is the motive at the boxed form. Each telescope's view, innermost
last:

**`ty_m`** (a type at c), with univs `l, l', li`:

```
g, U_I : Typ_c(g, li), U_S : Typ_c((g, i : U_I), l),
U_P : Typ_c((g, i, s : U_S), l'), u_o : Trm_c((g, i, s, p : U_P) ⊢ U_I @ li),
u_j : Trm_c(g ⊢ U_I @ li); x_I, x_S, x_P, x_o, x_j
  : M_Typ[l ⊔ l' ⊔ li / ℓ, g, box M(U_I; U_S; U_P; u_o)(u_j)]
```

**`tm_m`** (the code former), with univs `l, l', li`. It is `ty_m` with
`Typ_c(…, l)` replaced by `Trm_c(… ⊢ Ty l @ 1+l)` and `U_X` read through
`El`, as `tm_wf` is `ty_wf`'s. The result is `M_Trm` at `Ty(l ⊔ l' ⊔ li)`.

**`tm_corec`**, with univs `l, l', li, k`. `ty_m`'s five globals, then:

```
U_X : Typ_c((g, i : U_I), k),
u_c : Trm_c((g, i : U_I, x : U_X) ⊢ step(σ, X)[i] @ k ⊔ l ⊔ l' ⊔ li),
u_j : Trm_c(g ⊢ U_I @ li), u_x : Trm_c(g ⊢ U_X[u_j] @ k)
```

with a recursive local for each, for nine globals and nine locals. That is
the widest telescope yet, as the coinduction design predicted (§5). The
result is `M_Trm[family / ℓ, g, M(σ)(u_j) / U_T, box corec(…)]`. The step
type is the kernel's `m_step_ty`, instantiated in the telescope rather than
restated.

**`tm_out`**, with univs `l, l', li`: `ty_m`'s five globals, then
`u_m : Trm_c(g ⊢ M(σ)(u_j) @ l ⊔ l' ⊔ li)`. The result is `M_Trm` at
`m_out_ty(σ, u_j)`.

## 3. The parallel transcriptions

As for every former (the IWf design's "five parallel transcriptions"), each
branch is written once in `rec.rs`'s `branch_specs` and then consumed in
these places:

| site | what |
|---|---|
| `term.rs` | `Term::TmM`, the four `Branches` fields, `BRANCH_NAMES` |
| `rec.rs` | the four `BranchSpec`s |
| `subst.rs` | `map_branches` depths, `TmM` traversal |
| `reduce.rs`, `eval.rs`, `value*.rs` | `El(TmM)` decoding, and recursor β on the four boxed forms |
| `typing.rs` | `TmM` formation; lift the `computing_layer` gate off `M`/`corec`/`out` |
| `conv.rs`, `conv/dom*` | `TmM` structural congruence; branches compared pairwise at `rec.rs`'s types |
| `bounds.rs`, `fmt.rs` | the usual |
| `cache/merkle.rs`, `elab/module_image.rs` | tags (image magic bump) |
| `export` | refuse `TmM`, as it already refuses `M` |
| `tests/common/wt.rs`, random generators | the new forms |

On the elaborator side, `code::code_of` gets `Type::M → TmM`, and the
`match code` surface's arm names come from `BRANCH_NAMES`, so its four new
arms need no parser change. `lib/certgen_code.hthr`
already ends its matches with `_ =>`, so it needs no change.

## 4. Tests

`crates/kernel/tests/m.rs` grows a codes section on the four axes:

- `El(TmM …)` decodes to `M` at a literal and at a neutral index.
- A boxed `corec` is inert at c: `box(out(corec …))` is not `box(…reduct…)`
  (negative control).
- The code recursor's β fires on each of the four boxed forms, and an
  identity recursor rebuilds each one (the existing identity-recursor test,
  extended).
- `M` at c typechecks a declaration-shaped term that previously needed p.

Then #131's `layers_follow_codata` test flips: every declaration is c.

## 5. heather-coq

The codes add nothing to the M metatheory beyond the coinduction design's
§9: code-layer syntax is inert, and a code's decoding is the former. The
question worth asking is the one §9 already lists: that `corec` under a
quote stays inert. Here that holds by construction (reduction never enters
a `box`), and the m.rs negative control pins it.

## 6. Scope note: `IWf` and `DVec`

`docs/iwf-former-design.md` §13 step 4 is the same `rec.rs` round for
`IWf`/`DVec`: six branches (`ty_dvec`, `tm_dvec`, `ty_iwf`, `tm_iwf`,
`tm_sup_i`, `tm_elim_iwf`). The machinery is shared, so the two rounds could
be one, ten branches in all. This round does **`M` only**, so that codata at
c is reviewable on its own, and `IWf`/`DVec` follow in the same pattern.
