# Proof repair as algebra isomorphism: what the paper means for Heather

Status: **survey**, 2026-10-28. Source: E.G. Plante III, Eric Paul, Cosmo
Viola, G.A. Kavvos, Talia Ringer, *Proof Repair and (Co)algebra
Equivalences*, arXiv:2610.36669v1 [cs.PL], 27 October 2026. The PDF is not
committed: arXiv's default licence does not allow redistribution, and the
paper gives no other. The Agda formalisation is at
<https://github.com/trey3p/proof-repair-coalgebra> (Zenodo
doi:10.5281/zenodo.23326858). Section, definition and theorem numbers below
are the paper's. Follow-up is in §7. Read against master at `0db0151`.

The paper is about **type-theoretic proof repair**. When a datatype changes
(unary `Nat` becomes binary `Bin`), a repair tool rewrites the programs and
proofs over the old type into native programs and proofs over the new one.
PUMPKIN Pi drives this with a *configuration*: for each type, its
constructors (`DepConstr`), its dependent eliminator (`DepElim`) and the
eliminator's computation rules (`Iota`), paired up across the two types. The
tool swaps one side's components for the other's and leaves the case data
alone. The paper internalises configurations in Agda and proves what they
are: **a configuration is exactly an algebra isomorphism between two initial
algebras of one polynomial functor** (Theorem 3.11). It then dualises the
whole account to coinductive types and final coalgebras (§4).

Heather has no proof repair tool and is not planning one. It does have
`datarepr` and `reprgen` (`docs/native/datarepr-design.md`), and these do the same
job from the other side. A `datarepr` declaration gives a runtime carrier for
a spec inductive. `reprgen` then transfers each structural spec function to
that carrier and certifies the result. So most of the paper reads as a theory
of machinery Heather already built, and in several places Heather's rounds
reached its lemmas by hand-run before it was written.

---

## 0. The answer in brief

1. **Heather already has the paper's main objects.** There are four of them.
   - The kernel lowering. Every surface inductive becomes a `Wf` or `W` whose
     shape is the constructor tag plus its non-recursive fields, and whose
     positions are the recursive fields. That is the paper's canonical
     "W-type configuration" (Lemma 3.10), built into the elaborator.
     `IWf` carries indexed families, which the paper leaves out.
   - The hand-written initial-algebra kits, `ListAlg` and `TreeAlg`
     (`lib/std/data/list.hthr`, `tree.hthr`). Each has a fold, its β
     equations, pointwise uniqueness and fusion. These are the paper's
     Example 3.8, written as theorems.
   - `datarepr`'s defaulted fold. Its as-landed note says "at a repr whose
     images are certified, the fold anchor is derivable rather than an
     independent obligation". That is the paper's claim that the coherence
     conditions fall out of initiality (§3.3, after Definition 3.13). The
     generated `N_emb` is the paper's repair map φ.
   - `reprgen`'s fragment predicate. An arm's algebra may not mention the
     carrier, and §3.3 of the design doc words this as "spelled once and
     typed twice". That is exactly the hypothesis of the paper's
     Proposition 3.15, "repair by instantiation".
2. **Heather deliberately does not adopt the paper's starting point.** The
   paper's starting point is that an equivalence ties the two types. Minus
   confirmed `abs + inv` over an isomorphism on 2026-08-14
   (`issues/datarepr-separation.md`), and that is the right call for a
   compiler. A machine carrier is not an algebra for `Nat`'s functor at all:
   `Succ` has no total image on `u64` (`docs/native/datarepr-design.md` FINDING 1).
   Heather's refinement is the generalisation. The paper's theorem is the
   special case of a repr with total images and a *canonical-form* `inv`,
   which `BinC` already exercises. §3 sets this out.
3. **The paper assumes function extensionality, and Heather has none.** For
   finitary types this costs nothing: uniqueness of folds is pointwise and
   holds by induction. That is how `list_fold_unique` is proved. For
   infinitary types (`W`, function children) it is fatal: the fold of the
   identity algebra is not provably the identity
   (`docs/inductives/inductive-tier2-w-lowering.md` §12 item 8). So the paper's
   isomorphism (Proposition 2.4) cannot be stated with `=` at tier 2. §4
   gives the boundary.
4. **The coinductive half is unavailable as stated, and deliberately so.**
   The paper's M-types carry a uniqueness rule η for the corecursor
   (Definition 4.14). Its coinduction principle turns a bisimulation into an
   *equality*, through Cubical Agda's paths. Heather's kernel `M` has no η
   and does not assume "bisimilar implies equal"
   (`docs/kernel/kernel-coinduction-design.md` §2.1). The paper's coinductive
   correctness conditions therefore hold in Heather only up to
   bisimilarity. There is no customer for a codata repr yet
   (`issues/iterators-as-list-repr.md` keeps infinite streams out). §5 says
   what would be built when one arrives.
5. **One idea is worth adopting now.** After Proposition 3.15 the paper
   says that "occurrences of the source type in defining data are further
   uses of its algebra structure, repaired by the same swap". Applied to
   `reprgen`, this lifts its sharpest decline: an arm that uses its
   recursive child outside a self-call (`pred`, `tail_of`).
   - On the spec side, the child enters the algebra as `emb(k)`. On the
     carrier side it enters as `emb(abs(a0))`, which is what the anchor
     law's `s1(abs(a0), b0)` is anyway.
   - The certificate needs only `emb_abs` and `emb_inv`. The defaulted fold
     already generates both.
   - A hand-run at `BinC` checks: `pred` and `bump` transfer with `refines`
     and `refines_inv`. The arm without the embedding is refused for the
     reason `reprgen` names.
   - Filed as `issues/reprgen-recursive-child-via-embedding.md`. §6 has the
     hand-run.
6. **Native compilation gains nothing directly.** The native lane's
   representations (`Held::Rep`, words for `Nat`) are refinements onto
   finite carriers. That is the case the paper's framework excludes by
   construction, as item 2 says. Its one lesson there is that Heather is
   right not to look for isomorphisms in the lowering.

## 1. What the paper contributes

**Configurations, internalised (§2).** A constructor's argument telescope is
a `ConstrArity`: `Done`, `Nonrec A k` (a non-recursive argument the rest may
depend on) or `Rec I cs` (an `I`-indexed batch of recursive arguments). A
signature labels constructors with arities. A *constructor algebra* on a
carrier interprets every label. An *inductive algebra* adds an induction
principle and its β law (Definition 2.2), and a configuration is a pair of
these, one on each carrier.

Proposition 2.3 recovers PUMPKIN Pi's three correctness conditions:
- `constr_ok`: the forward map commutes with the constructors;
- `iota_ok`: each eliminator computes on its own constructors;
- `elim_ok`: the eliminators commute with the map.

Proposition 2.4 shows that, given an inductive algebra on one side,
configurations are equivalent to type equivalences. A side result is that
PUMPKIN Pi's `Eta` data is redundant. The formalisation derives it.

**The algebraic reading (§3).** Polynomial endofunctors `P A B X = Σ(a:A).
B a → X`, their algebras and homomorphisms, and homotopy-initiality (the
homomorphism space out of the algebra is contractible). Lemma 3.10 sends
every configuration to a one-constructor "W-type configuration" with the
same repair maps. The shapes are a label plus its non-recursive data, and the
positions are its recursive arguments. Theorem 3.11 says a W-type
configuration *is* an algebra equivalence whose source is initial. The proof
leans on Awodey, Gambino and Sojakova's W-types ≃ h-initial algebras.

**Repair by instantiation (Proposition 3.15).** For any algebra `(Y, γ)`,
`fold_C γ = fold_D γ ∘ φ`. A program written as a fold of carrier-free data
`γ` is repaired by refolding the same `γ` at the new type, and the result
never mentions the old type. Induction is the same move one level up: it is
a fold into the total-space algebra on `Σ(x:C). P x`, with the motive
transported along φ. If `γ` mentions `C`, those mentions are uses of `C`'s
algebra and are repaired by further swaps.

**No univalence (§3.4).** The inductive half needs only function
extensionality, with its computation and uniqueness rules. So repair is
justified in UIP theories such as Lean's.

**The coinductive dual (§4).** Coalgebras, final and homotopy-final
coalgebras, bisimulation, and the coinduction principle "bisimilar elements
are equal" (Proposition 4.10). The paper gives a rule-based presentation of
M-types: `corec`, its two β rules and a uniqueness rule η, with a Σ-level
`η_Σ` for the homotopy tier (Figure 1, Definitions 4.14 and 4.15).
Theorem 4.21 proves that these rules are exactly finality, and the
strengthened rules exactly homotopy-finality. That theorem is new.

Coinductive configurations come with four correctness conditions
(Proposition 4.19): `destr_ok`, `iota_ok`, `corec_ok` and `coind_ok`. The
last needs the homotopy tier, because its proof lifts Rutten's argument one
dimension, to squares. Theorem 4.24 is the dual of 3.11. The running example
is `Stream` with two destructors against `Stream'`, whose one destructor
returns a pair.

## 2. Where Heather already is

| The paper | Heather |
|---|---|
| Lemma 3.10: a signature as one polynomial, shape = label × non-recursive args, positions = recursive args | The `Wf` (finitary) and `W` (infinitary) lowerings do exactly this. A value is a tag and payload with a vector (or function) of children (`docs/inductives/inductive-tier1-wf-lowering.md`, `docs/inductives/inductive-tier2-w-lowering.md`). `IWf` goes past the paper to indexed families (`docs/kernel/iwf-infinitary-design.md`). The paper restricts itself to non-indexed signatures (§2). |
| Lemma 4.23: a cosignature as one polynomial; `Stream` against `Stream'` | Codata lowers onto the kernel's single `out` of `M`, with a named shape and position signature (`docs/inductives/codata-named-signature-design.md`). Multi-destructor declarations reach the kernel already in the paper's canonical form. |
| Example 3.8: recursor, β rules, induction from initiality | `ListAlg`/`list_fold`, `TreeAlg`/`tree_fold`, `TreeElim` (`lib/std/data/list.hthr`, `tree.hthr`). The β equations hold by `refl`, uniqueness and fusion are theorems, and all of it is pointwise (`issues/datatype-container-algebras.md`, 2026-08-18 log). |
| Definition 2.2's inductive algebra on the *new* carrier | `datarepr`'s `Repr_N` record: `mk` images (constructor algebra), `fold` plus `fold_law` (eliminator plus the law relating it to the spec), image laws `C_abs`/`C_inv` (`docs/native/datarepr-design.md` §1.1). It is one-sided: the spec side is the kernel's own inductive. |
| `constr_ok` | The image commutation laws `C_abs : abs(mk_C(…)) = C(…abs…)`, i.e. `abs` is an algebra homomorphism, from the images to the constructors. |
| `elim_ok`, derivable from `constr_ok` plus initiality (§3.3) | The defaulted `fold` (as-landed note on §1.4). `N_emb` is the fold of the spec type into the image algebra, which is the paper's φ. `N_emb_abs` (`abs ∘ emb = id`) is the round trip that initiality forces, proved by induction. `N_fold_via_abs` closes the anchor. The note's "derivable rather than an independent obligation" is the paper's point, reached independently. |
| `Eta` data is redundant (footnote 1) | `Repr_N` never had an η field. |
| Proposition 3.15: repair is re-instantiation of carrier-free `γ` | `reprgen` phase 2: "the structural match becomes `fold` with the algebra read off the arms". The phase 1 predicate and the as-landed "spelled once and typed twice" refusal are the paper's carrier-freeness condition. The paper's remark that "whether a term mentions C is a property of its syntax, which the type theory cannot express internally" is why `reprgen`'s fragment check is syntactic and says so ("honest syntactic predicate; not a soundness boundary"). |
| An algebra isomorphism (Theorem 3.11) | A repr whose `inv` is canonical-form, `BinC`'s `bin_of_nat(bin_abs(r)) = r`. There `abs` is injective on `inv`, `emb` is its inverse on the subtype, and via-derived's weak `abs`-image obligation coincides with carrier equality (`docs/native/datarepr-design.md` §1.2, "canonical-form `inv` the opt-in that makes them coincide"). |

Two of these rows record the same thing from both directions. Heather's
datarepr rounds hand-ran their way to "the fold anchor is derivable" and to
"canonical-form `inv` makes the obligations coincide". The paper supplies the
reason in one line: the image algebra on the canonical subtype is initial, so
everything about it is forced. Neither finding needs revisiting. The survey's
value there is that the next round can cite a theorem instead of re-deriving
it.

## 3. Isomorphism against refinement: why Heather stays different

The paper's goal is to **eliminate the old type**: after repair, nothing
mentions `Nat`. Heather's goal is the opposite. The spec type *is* the
mathematics and is never replaced, and the representation is a certified
refinement of it (`issues/datarepr-separation.md`, "the representation the
kernel checks is not the representation that runs"). Two consequences
follow.

**The paper's motivating change never happens to a Heather spec type.** The
introduction's change, swapping `Nat` for `Bin` across a library for
efficiency, is in Heather a `datarepr` declaration. No library edit is
involved. A Heather spec inductive changes only for proof-side reasons:
reordering constructors, adding an index, generalising a field. Those are
ornaments or other non-isomorphic changes, outside what the paper's
configurations characterise. So the tool the paper founds would have little
to do in Heather's library. Its theory still applies to Heather's
representation layer, which is how the rest of this note uses it.

**Refinement is strictly more general, and the generality is load-bearing.**
The paper's configuration needs both sides to be initial algebras, so it
needs a total constructor algebra on the new carrier. FINDING 1 of
`docs/native/datarepr-design.md` is that the interesting carriers have none: `Succ`
has no total image on `u64`. Heather's answer was to make consumption total
(`abs`, `inv`, `fold`) and construction partial. A repr's images are
operations under the partiality policy.

In the paper's terms, `{r | inv r}` with the images is at best a *partial*
algebra. `abs` is a homomorphism from it onto the initial one where the
images are defined. Nothing about initiality survives the partiality, and
Heather does not need it to: every certificate is stated through `abs`,
pointwise. The isomorphism case is the corner where the images are total and
`inv` is canonical-form. That corner has a known use (carrier equality for
via-derived) and is already reachable as an opt-in.

The decision of 2026-08-14 stands, and the paper confirms its scope from the
other side. The paper's "changes representable by an algebra isomorphism"
(§3.2) are exactly the changes that preserve the inductive structure. A
machine carrier does not preserve it, by design.

## 4. Function extensionality: where the paper's theorems hold in Heather

The paper assumes funext, with its computation rule and uniqueness rule (§1,
Conventions). Uniqueness of folds is stated as contractibility of a
homomorphism space, which compares *functions*. Heather has neither funext
nor univalence, and it has no K: UIP on `Id` "is Hedberg's theorem
territory" (`crates/kernel/DESIGN.md`). Its strict equality `sEq` is
definitionally proof-irrelevant but has no eliminator. So every statement
must be restated pointwise, and whether the pointwise version is provable
depends on the tier.

- **Finitary (`Wf`): everything the repair story needs holds pointwise.**
  Pointwise uniqueness (`h` satisfies the fold equations ⇒ `∀x. h x =
  fold x`) is an induction. The children are a tuple, so the inductive
  hypothesis at each child is an ordinary equation. This covers:
  - `list_fold_unique`;
  - `N_emb_abs`, the round trip of Proposition 2.4's proof;
  - `reprgen`'s `f_is_rec`.

  The function-level `fold_C γ = fold_D γ ∘ φ` is not statable, and nothing
  in Heather needs it: every consumer applies it at a point.
- **Infinitary (`W`): the round trip already fails.** A function child's
  inductive hypothesis is a pointwise equation `∀y. h(k y) = fold(k y)`, and
  closing the case needs `h ∘ k = fold ∘ k` as functions. That is funext.
  Tier 2 records the symptom: `rebuild(Vis(c, k)) = Vis(c, k)` and `bind(t,
  Ret) = t` are refused (`docs/inductives/inductive-tier2-w-lowering.md` §12 item 8).
  So the fold of the identity algebra is not provably the identity, and
  Proposition 2.4's "ψ ∘ φ is a fold into an initial algebra, hence the
  identity" breaks at its first step.
- **What a tier-2 repr would therefore owe.** If a `datarepr` ever targets
  an infinitary spec type (none does: v1 is first-order, §5 of the design
  doc), its `emb_abs` and every certificate through it must be stated up to
  the pointwise equivalence that `issues/interaction-trees-container-model.md`
  defines for trees, not up to `=`. That is a constraint to record in the
  design doc's §5 when the first such repr is chartered. It needs no issue
  now.

The paper's claim that repair needs no univalence therefore sharpens in
Heather to **needs no funext, at the finitary tier**. That is the tier every
current repr lives at.

## 5. The coinductive half

Heather's kernel `M` (`docs/kernel/kernel-coinduction-design.md`) differs from the
paper's M-types (Figure 1) in exactly the rules the paper's coinductive
repair relies on:

- **No η.** Definition 4.14's η says any map that agrees with the source
  coalgebra under the destructors *is* `corec`. That is uniqueness of the
  homomorphism into the final coalgebra, i.e. finality. Heather declined η
  at `M` because it semi-decides bisimilarity in conversion (§2.1 there).
  Heather's `M` is therefore not an M-type in the paper's sense up to `=`.
- **No "bisimilar implies equal".** Proposition 4.10 is a theorem in the
  paper because Cubical Agda's path type admits copattern-defined paths.
  Heather states bisimilarity as an ordinary indexed `M`, and coinduction is
  a `corec` into it. It never yields an `Id`.

So `corec_ok` (`φ(corec_C ec e) = corec_D ec e`) and `coind_ok` cannot be
stated with `=`. Both have honest versions **up to bisimilarity**, and both
are provable by one `corec` into `Bisim`. The relation is "both sides are
`corec`s of the same seed through the two carriers". The paper's
homotopy-final tier is moot. It exists to make `coind_ok` an equality of
*paths*, and Heather has no paths to compare.

There is no customer. A coinductive `datarepr` (a lazy carrier for codata)
is not in the design, and `issues/iterators-as-list-repr.md` keeps infinite
streams out until one appears. If one does, the paper's Definition 4.17
(destructor algebra, corecursor, per-destructor β, function-level
uniqueness) is the record shape to start from. Read its uniqueness field as
"bisimilar to `corec`" and its correctness conditions as Proposition 4.19
modulo `Bisim`.

The coinductive dual of `list_fold_unique` is the library-side precursor:
any `h` satisfying `out ∘ h = P(h) ∘ γ` is bisimilar to `corec(γ)`.
`lib/std/itree/coitree.hthr` does not state it. It is worth one theorem the
day a coitree proof wants to identify two corecursive definitions, but not
an issue before then.

## 6. Adopt: the recursive child as a further use of the repair map

`reprgen` declines an arm that uses its recursive child anywhere except as
the argument of a self-call. That covers:
- `pred`: `Succ(k) => k`;
- `tail_of`: `Cons(h, t) => t`;
- `uses_child`: `Cons(h, t) => length(t)`.

The reason, recorded in `crates/elab/src/reprgen.rs` and the design doc's
§3.3 as-landed notes, is that the child is at the carrier on the repr side
and at `S` on the spec side. No single spelling of the arm is well-typed
under both readings.

The paper's remark after Proposition 3.15 names the way through. The
child's occurrence in the defining data is "a further use of `C`'s algebra
structure", repaired by applying the repair map. In `datarepr` terms the
repair map is `emb : S → R`, the spec recursor over the images.

**The rule.** In the spec-side algebra, a recursive child `k` used outside a
self-call is spelled `emb(k)`. The anchor law's repr-side step is
`s1(abs(a0), b0)`, so on the carrier the same position reads
`emb(abs(a0))`. Now the arm is spelled once and is well-typed twice. The
certificate needs three things, all of which already exist:
- `emb_abs` (`abs(emb(k)) = k`), at each such occurrence in the `abs` walk;
- `emb_inv` (`inv(emb(k))`), where `inv` of the result or of a callee
  argument is owed;
- callee `refines` at `emb(k)`, for an occurrence handed to a resolved
  callee, which then closes by `emb_abs`.

The defaulted fold generates `N_emb`, `N_emb_abs` and `N_emb_inv` already. A
repr with a hand-written fold would need its embedding named (for `Bin`,
`bin_of_nat`). Equivalently, the embedding could always be generated, since
v1 images are total.

**The hand-run.** This was checked against master `0db0151` with
`target/release/heather check --expectations`, on the `BIN_CANON` fixture of
`crates/elab/tests/support/mod.rs`. That is `Bin` under the canonical-form
`inv`, where `inv` obligations have content. The probe's text is in the
issue.
- `pred` and `bump` (`Succ(k) => Succ(Succ(k))`, the child inside an image
  spine) transfer.
- `refines` holds for both, and `refines_inv` for `pred`.
- `pred_derived(B1(B1(BNil)))` computes to two by `refl`.
- The negative control is the same derived body with the child handed back
  raw. It is refused with "this has type `Nat`, but `Bin` is expected
  here", which is exactly the typed-twice failure `reprgen` names.

Cost does not matter here. The derived body rebuilds the child through `abs`
and `emb`, unary at `Bin`, and §1.1's "the fold need not be what runs" covers
that: a hand `Impl` returning `a0` itself is the via-derived override. At a
canonical-form `inv`, `emb(abs(a0)) = a0` is the `inv` hypothesis itself, so
the override discharges with carrier equality.

Why adopt this now, when nothing else in the paper is: it widens an existing
generator's fragment at a known decline, it adds no `Repr` field and no
certificate shape beyond one more law per site, and the decline it removes
covers a common structural shape: destructors such as `pred`, `tail` and a
tree's `left`/`right`.

## 7. Follow-up

Filed:

- `issues/reprgen-recursive-child-via-embedding.md` (heather-in-heather): §6.

Logged:

- `datatype-container-algebras`: the paper as the theory of its design
  question 2 (law boundary). Pointwise uniqueness and fusion hold at `Wf`
  without funext, and the round trip fails at `W` (§4). Its Lemma 3.10 is
  the public `Wf` presentation the issue's question 1 asks about. The
  coinductive dual of `list_fold_unique` holds only up to `Bisim` (§5).
- `datarepr-separation`: one line, pointing here for the isomorphism case
  (§3) and the filed issue.

Not taken, and why:

- **A proof repair tool for library changes.** Heather's spec types do not
  change for efficiency (§3), and the changes they do undergo are not
  isomorphisms.
- **Univalent or cubical machinery for coinductive repair.** Heather's `M`
  declines η and "bisimilar implies equal" on purpose (§5).
- **Function-level statements of fold uniqueness.** These need funext.
  Every consumer applies them at a point (§4).
