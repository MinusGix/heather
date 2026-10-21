# Coinductive types in the kernel: an indexed `M` former

Status: **design, for review** (2026-10-21). No kernel code. Tracking issue:
`issues/kernel-coinductive-types.md`, planned now by Minus's decision of
2026-10-21 ("might as well get full proper power sooner"). Written before
the code, per repo discipline, as the specification a kernel round would be
checked against, in the shape of `docs/wf-former-design.md` and
`docs/iwf-former-design.md`. The library probe of §3 is checked in
(`crates/elab/tests/coinduction_probe.rs`). The questions for heather-coq
are in §9.

---

## 0. Recommendation

Add **one negative former, an indexed `M`**, whose values are observed only
through `out`, introduced only by a **primitive corecursor** (`corec`, the
apomorphism: each child is either a new seed or an existing tree), with β
under `out` and **no η**. Equality of coinductive values stays intensional
in conversion. Bisimilarity is an ordinary type, itself an instance of the
indexed `M`, so a proof by coinduction is a `corec` with the user's relation
as its carrier. **"Bisimilar implies equal" is not assumed.** Guarded
recursion is not adopted now; sized types are not adopted at all.

In one line each, why:

- **Negative, not Coq's positive `CoInductive`.** No guard checker in the
  kernel, and none of Giménez's subject-reduction failure, which needs
  `cofix` unfolding under a dependent `match`.
- **No η.** η at `M` semi-decides bisimilarity (`docs/interaction-trees-fit.md`
  §3.2); with it, ch. 08's decidability is gone.
- **Indexed from the start.** The consumers that motivate the round are
  coinductive *predicates* (bisimilarity, eutt, "always eventually",
  divergence), and every one of them is indexed. An unindexed `M` would
  leave all of them step-indexed, which is what the library already does
  without a kernel change (§3). Minus's rule from the program-logic review
  applies: the ideal version from the beginning.
- **The apomorphism, not plain `corec`.** Constructors then come out of the
  one intro form with their exact β (`out(Vis(c, k)) ≡ (Vis c, k)` up to
  Σ/Π η), where plain `corec` would only give `k` back up to bisimilarity
  (§2.2).
- **No identification axiom.** Heather assumes no funext (`lib/std/itree.hthr`
  works up to `ITree::Same` for exactly this reason), and constructive is a
  principle (`docs/roadmap.md`). Bisimilarity as the working equivalence is
  what the setoid library is for.

What it buys over today, measured in §3: trees and coinductive predicates
**at the level of their events** (the cost of the encodings Heather can
already write is one universe level, and the probe shows it bite at the
first generic library call), and a definitional `out ∘ corec` on that small
type. Everything the finite library proves carries over through `approx`
(§6).

---

## 1. The former

### 1.1 Formation

A signature `σ = (I; i. S; i s. P; i s p. o)` at levels `(l, l', li)`:

```
I        : Type @ li                      index type
i : I    ⊢ S : Type @ l                   shapes at index i
i, s : S ⊢ P : Type @ l'                  positions (children) of shape s
i, s, p  ⊢ o : I                          the index of the child at p

M^{l,l',li}(σ)(j) : Type @ l ⊔ l' ⊔ li    for j : I
```

This is the dependent polynomial ("Petersson–Synek") form: the **shapes
depend on the index**, and each child's index is computed. It is the dual
of `IWf`'s form, in which a constructor determines its *output* index. For a
coinductive type that form would store an equation (`o[a] = j`) in every
value, against `docs/iwf-former-design.md`'s principle that an index
constraint belongs in a type, not in data. Here nothing is stored: the
index of a node chooses which shapes it may have.

Plain `M` is `I := Unit`. A finitary coinductive type (streams) is `P :=
Unit` or `Fin k`; Π over those is a tuple by Unit/Σ η, so no `Vec`
counterpart is needed.

The family level is written `l ⊔ l' ⊔ li` after `IWf`'s `l ⊔ li`; whether
the index level must appear is for heather-coq (§9, Q1).

### 1.2 Elimination: `out`

```
m : M(σ)(j)
───────────────────────────────────────────────────────────────
out(σ; j; m) : Σ(s : S[j]). Π(p : P[j, s]). M(σ)(o[j, s, p])
```

`out` is the only eliminator. It is neutral on a neutral `m`. There is no
dependent case analysis on an `M` value: a motive over `m` cannot be split
by "which constructor `m` is", which is precisely the rule whose η-like
reading breaks subject reduction in Coq.

### 1.3 Introduction: `corec`

```
i : I ⊢ X : Type @ k
i : I, x : X[i] ⊢ c : Σ(s : S[i]). Π(p : P[i, s]). X[o[i,s,p]] +^{k, l⊔l'⊔li} M(σ)(o[i,s,p])
j : I     x : X[j]
───────────────────────────────────────────────────────────────
corec^{k}(σ; i. X; i x. c; j; x) : M(σ)(j)
```

The carrier `X` is a family over the index at **any** level `k`. That is a
rule schema, one rule per `k`, and quantifies over nothing, so it stays
predicative: a coalgebra on a large carrier still lands in the small `M`.
The step returns, at each child, either a new seed (`inl`) or an existing
tree (`inr`). All annotations are written, as for every former, so `corec`
synthesizes.

### 1.4 β

```
out(σ; j; corec(σ; X; c; j; x))
  ⇝ pair(fst(r), λp. case(snd(r) p; y. corec(σ; X; c; o[j, fst r, p]; y); t. t))
    where r := c[j, x]
```

This is the whole computational content: one step, only under `out`. The
reduct mentions `r` twice. The environment machine shares it inside the
step (`eval.rs` builds the pair over one closure); `reduce.rs`, the
substituting oracle, duplicates it, which is §7's cost note.

A constructor is a `corec` whose children all exit, at carrier `Unit`:

```
in(σ; j; s; f) := corec(σ; _. Unit; _ _. pair(s, λp. inr(f p)); j; ⟨⟩)
out(in(s, f)) ⇝ pair(s, λp. case(inr(f p); …; t. t)) ⇝ pair(s, λp. f p) ≡η pair(s, f)
```

So `Vis(c, k)` written in a program gives back exactly `k` under one `out`,
with no bisimilarity in between.

### 1.5 Layers

As `IWf`'s were until its codes round: the former, `out` and `corec` are
admitted at layers p and m only, until a round gives them codes (§5).

---

## 2. Conversion and neutrality

### 2.1 No η

Conversion at `M(σ)(j)` stays intensional, and `tm_nf` gets **no** `M` arm:

- `corec(σ; X; c; j; x) ≈ corec(σ; X'; c'; j; x')` compares the carrier
  family (with its level), the step and the seed, in that order (the step's
  type depends on the carrier). The signature and `j` are forced by the
  type and are not compared, under the typed-congruence discipline of
  `ELIM_CONGRUENCE.md` (heather-coq).
- `corec(…) ≈ neutral` is `NotConvertible`, as `sup ≈ neutral` is at `W`.
- Neutrals compare by spine; `out` joins the neutral eliminators, compared
  structurally at its Σ result type, whose η arm then projects it.

Every comparison is finite: no rule ever unfolds a `corec` outside an
`out` the term itself contains, so conversion terminates on the same
measure as today's. The price is that two `corec`s describing the same
tree are distinct values, and so are `t` and `in(out(t))`. The probe's
`nu_equality_is_intensional` pins the same behaviour for today's encoding.

### 2.2 Why the apomorphism

With plain `corec` (children always seeds) a constructor is still
definable, at carrier `F(M) + M`, but its children come back as
`corec(…, inr(f p))`, a *different* value from `f p` that is only
bisimilar to it. Every pattern match on a written `Vis(c, k)` would then
produce a continuation the program never wrote. The apomorphism costs one
`case` per observed child, which β-reduces at once on a literal `inl`/`inr`,
and makes the constructors exact. It is to `corec` what `elim_W` passing
the subtrees `f` beside the induction hypothesis is to plain iteration.

### 2.3 What stays out of conversion, at any cost

Weak bisimilarity (eutt). Deciding `t ≈ spin` is the halting problem. It
is a type (§4), never a conversion rule.

---

## 3. What Heather can already write (the probe)

`crates/elab/tests/fixtures/coinduction_probe.hthr` builds the two
kernel-free encodings over the existing fuel-cut `ITree` and checks which
laws hold how. Both check today.

**A. `Nu`, the sum of all coalgebras.** `record Nu<R>(E) { X: Type, step: X →
Head<R, X>(E), seed: X }`, with `unfold := Nu(X, step, x)` and
`out(m) := map (repack) (m.step(m.seed))`.

- `Nu::out_unfold`, the β rule above, is `refl` at an open carrier, step
  and seed; `Nu::spin_out` (`out(spin) = NTau(spin)`) is `refl` and holds
  in a checking position.
- Equality is intensional: `spin` and a counting unfolding of the same tree
  are not convertible (`NotConvertible`), exactly as a kernel `M`'s would
  be.
- **The cost is a level.** `X: Type` makes `Nu` one level above its
  events. The library's operations are generic over level-zero types, and
  `ITree::bind` at `Nu` is refused with `LevelMismatch`
  (`nu_is_a_level_up_from_the_library`). The observation itself needed a
  head type of its own (`NuHead`), because `Head<R, X>` takes a level-zero
  carrier. A `Nu` tree cannot be a command's answer, so a `spawn` that takes
  a process is out, and a coinductive predicate in this style is
  Knaster–Tarski's `Σ(R : relation). R ⊆ F R × R(t, u)`, again a level up
  (`docs/interaction-trees-fit.md` §3.7).

**B. `Lim`, the limit of the cuts** (Ahrens, Capriotti and Spadotti, 2015).
`record Lim<R>(E) { at: Nat → ITree<R>(E), coh: (n) → Same(cut(n, at(n+1)),
at(n)) }`, with `unfold` the unrollings of a coalgebra.

- It is at the events' level.
- Coherence holds only up to `Same`: `ITree::unroll_coh` is by induction on
  the depth with the `Vis` case as `SameVis`. As an equation it is `refl` at
  a literal depth (`coherence_is_refl_at_a_literal_depth`) and refused at
  a neutral one (`coherence_is_not_refl_at_a_neutral_depth`).
- `out` is where it costs. The command of the head is read at depth one;
  the child at answer `a` is the subtree of `at(n+1)` under `a`, whose type
  is the answers to depth-`n+1`'s command. The two commands are equal only
  through the chain of coherence proofs, so every child needs a transport,
  and `out(unfold(x))`'s children are `unfold`s of the next seeds only up to
  `Same` at every depth. The probe stops short of writing `out` for this
  reason; it is the encoding's known weak point, not a surprise.

`Nu::approx_unfold` shows the two agree at every depth (again up to `Same`).

**Verdict.** The *computation* a kernel `M` adds is already expressible:
`Nu` has it definitionally. What is not expressible is that computation on
a type at the events' level, and coinductive predicates that are small. A
kernel `M` is `Nu` with the level dropped, and dropping it is what needs
metatheory. That is the round's real content, and it is why `Lim` (the
issue's option 2) does not replace it: `Lim` is small but has no usable
`out`, `Nu` has `out` but is not small.

---

## 4. Bisimilarity, eutt, and coinductive predicates

All are instances of §1 with the index a pair of trees.

**Strong bisimilarity** over a tree type `T := M(σ)(j)` (unindexed for
brevity):

```
Bisim := M(I := T × T;
           (t, u). Id(S, fst(out t), fst(out u));
           (t, u) e. P[fst(out t)];
           (t, u) e p. (snd(out t) p, snd(out u) (J(e; p))))
```

The shapes' equation is `Id` and the positions move across it with `J`,
which computes at `refl`. `sEq` cannot carry it: `transp` and the strip are
removed from the rule set (`docs/sprop-design.md`, revision of 2026-09-30),
so `sEq` has no eliminator. A proof by coinduction is a `corec` into
`Bisim` with the user's relation as carrier; up-to techniques are carriers
that are closures of relations.

**Weak bisimilarity (eutt)** nests an inductive inside: the shape at
`(t, u)` is `Peel(t, u)`, an inductive family (tier 1/2, lowered as today)
that strips finitely many `Tau`s on either side and ends at two matching
heads; its positions are the continuation pairs at the end of the peel.
This is the standard encoding of mixed induction–coinduction (νX. μY. …)
and needs nothing beyond §1 and today's inductives.

**Liveness** ("every request is eventually answered", "always eventually
P") has the same shape: coinductive over the run, an inductive "eventually"
in the shape.

**The bridge to the finite library.** `Bisim(t, u) ⇔ Π n. Same(approx n t,
approx n u)`. Left to right is induction on `n`. Right to left is a
`corec` into `Bisim` with carrier `Π n. Same(approx n t, approx n u)`; it
must merge the depth-`n` proofs of the shapes' equation, so it needs those
proofs equal: UIP on the shapes, which holds for events whose commands
form a set (Hedberg, `Validity/Hedberg.v` has it in the syntax). This is
heather-coq's `eutt_gfp_omega` in reverse (`probes/ItreeDepthBisim.v`,
where the hypothesis is `UIP_Cmd`), and the same caveat.

---

## 5. Codes and the meta layer

Four code-recursor branches when codes come (`ty_m`, `tm_m`, `tm_corec`,
`tm_out`), with the step telescope of `tm_corec` the widest yet (the
carrier family, the step under two binders, the seed). At layer c nothing
computes, so a boxed corecursive definition is a finite piece of syntax;
`□` comparison stays syntactic, so bisimilar code stays distinguishable as
code. A `Code` may mention an `M`; a `corec` under a quote is inert like
every other intro form. This is the same firewall funext would have and
needs nothing new; it waits for its own round, as `IWf`'s codes did.

---

## 6. The library on top

This is the round after the kernel's, sketched so the kernel's rules can be
checked against what the library needs.

- **The tree.** `codata ITree<R>(E: Events) { Ret(r: R), Tau(t), Vis(c:
  E.Cmd, k: E.Resp(c) → ITree) }` lowers to `M` with a label sum for the
  shape, as tier 2 lowers inductives onto `W`. Constructors are `in`.
  `match` on a coinductive value is `case` on `fst(out m)`, non-dependent
  in the scrutinee. There is no `Cut`: a coinductive tree never runs out.
- **Corecursive definitions.** The elaborator compiles guarded
  corecursion into `corec`, the dual of compiling structural recursion
  into eliminators. Minimal rule: a corecursive call may stand as an
  immediate child of the head the definition returns; any other child is
  an existing tree (`inr`); a constructor nested above a call becomes a
  carrier state the elaborator generates. `bind`, `iter` and `mrec` fit:

  ```
  bind(t, h):  carrier ITree<A>; step(t) := match out(t) {
                 Ret(r)    => map inr (out(h(r))),     // the node is h(r)'s
                 Tau(s)    => (Tau, λ_. inl(s)),
                 Vis(c, k) => (Vis(c), λa. inl(k(a))) }
  iter(body, a): carrier A + ITree<Step<A, B>>; a `Continue` emits a Tau
                 and goes to `inl(a')`, so every step is productive.
  ```

  The laws with a constructor on the left hold by `refl` **after one
  `out`** (`out(bind(Ret(r), h)) ≡ out(h(r))`), not as equations of
  trees; as equations they are bisimilarities. The finite library has
  them by `refl` outright. That is the trade, and §0's no-η decision is
  what it costs.
- **Approximation.** `approx(n, t) : ITree`-the-finite-one, the cut at depth
  `n`. Every finite theorem, `Sim` included, applies to `approx(n, t)`, and
  a coinductive tree gives a `Program` (`at := λn. approx(n, t)`, growth by
  induction). Nothing in `lib/std/itree*.hthr` is retired.
- **Naming.** Which tree keeps the name `ITree` is for the library round;
  until then the finite one keeps it.

### 6.1 `Sim`'s converse (S1)

`issues/linux-sim-every-machine-run.md`: a tree that diverges at every fuel
is simulated by any machine, even one that exits. Two ways out, and only
one needs this design:

1. **Kernel-free, available now.** Make a `Tau` cost the machine at least
   one step (CompCert's non-stuttering simulation). A tree with `n` `Tau`s
   before its next event then forces `n` machine steps, so a machine that
   exits after `k` steps meets a tree that does something within `k`
   `Tau`s, and the converse goes through by determinism. Traces do not see
   `Tau`s, so this needs a step-wise reading of `Sim` beside `RunsAs`, not
   only a new `sim_tau`.
2. **Coinductive.** State `Sim` as a coinductive relation between the
   machine's runs and the coinductive tree (an `M` indexed by machine
   state and tree), so divergence matches divergence directly.

The first is enough for "exactly these traces"; the second is the
statement a compiler correctness theorem wants to end with.

---

## 7. Costs and risks

- **Metatheory** (ch. 07) is the long pole, as for every former; §9 says
  what to check first. The edit is per-former if the relation at `M` can
  be written as §9 Q1 proposes; it would be shared (expensive) if it needs
  the reducibility universe changed.
- **The oracle.** `reduce.rs` substitutes, so the doubled `r` in β grows
  the term at every nested observation (`issues/whnf-sharing-term-growth.md`
  again). The differential tests need either a sharing β for `M` in the
  oracle or depth-bounded cases.
- **Elaborator.** Guardedness and carrier generation are new elaborator
  machinery, the dual of tier 2's structural recursion; non-compositional
  guardedness (a call under `bind`) is refused at first, and
  definitions write the carrier, as the bind sketch does.
- **Export.** Lean 4's kernel has no coinductive types; mathlib's
  `PFunctor.M` is built from approximations and its β (`M.dest_corec`) is
  a theorem rather than a conversion, so a
  proof that uses β by conversion does not check there. `M` declarations
  are an unexported fragment at first. Rocq has negative coinductive
  records with primitive projections, where `cofix` unfolds only under a
  projection, so the Rocq route can realise `out`/`corec` with β
  definitional. Minus (2026-10-21): export need not match the language.
- **Performance.** `out` on a `corec` value forces one step; nothing else
  changes. No hot path gains an inference route.

---

## 8. The alternatives

1. **Negative `M`** — chosen, in its indexed, apomorphic form.
2. **`M` from `W` as a limit, no kernel change** (`Lim`, §3). Small, but
   `out` needs transports along coherence, `corec` computes only at literal
   depth, and equations need funext. It is how Lean would receive exported
   trees, which §7 deals with separately.
3. **Guarded recursion with clocks** (Guarded Cubical, CloTT). Productivity
   by typing, and corecursion under `bind` becomes compositional. It costs a
   new modality beside DeLaM's layers (`issues/multimodal-modalities.md` is
   still open on whether they share a mode theory), clock quantification,
   and a normalization argument (Gratzer and Birkedal's stratified Löb is
   the one known route to decidable conversion). Not now. It does not
   compete with an `M`: clock-quantified guarded types are interpreted
   *by* final coalgebras, so it can come later as a surface discipline
   that compiles to `M`.
4. **Sized types.** Not adopted; Agda's consistency history is the reason.

Also rejected: **η at `M`** (§2.1), **an identification axiom**
("bisimilar ⇒ `Id`"; it is the coinductive sibling of funext, which
Heather does not assume, it loses canonicity along every transport, and
nothing in §4–§6 needs it), and **unindexed `M` first** (it would ship the
easy half and leave every consumer step-indexed).

---

## 9. For heather-coq

Ordered by how expensive a bad answer would be to unwind, as
`coq-delam-formalization` ranks them.

1. **The relation at `M`, without the carrier.** `docs/interaction-trees-fit.md`
   §3.4 worried that reducibility at `M` needs `⟦X⟧` for `corec`'s carrier,
   which may live at any level. The proposal: write the relation at `M` the
   way `WRel` is written (both sides reduce to whnfs, the whnfs are
   declaratively equal), and replace `WNf`'s inductive by **observations**:
   `MRel` at depth `n+1` relates `t, t'` when `out` of their whnfs are
   related at `Σ(s : S[j]). Π(p). M(o[…])` with `MRel` at depth `n` at the
   children; `MRel := ∀ n. MRelₙ`. It mentions `domR`/`codR` for the shapes
   and positions, as `WRel` does, and never the carrier. The fundamental
   theorem's `corec` case then uses the *validity* of `c` and `x` at `X`
   (the IH, not part of the relation's definition) and goes by induction on
   `n` with the seed generalized. The ω-intersection is suggested over a
   `CoInductive` `Prop` because a `cofix` proof through the relation's
   lemmas would fight Coq's guard checker. Does this keep the `M` case a
   per-former addition, and does the family level need `li`?
2. **Decidability.** The algorithm of §2.1 (corec congruence, no η, `out`
   neutral) as an instance of the generic equivalence, completeness
   through the fundamental theorem, and the apomorphic β with its `case`.
3. **Subject reduction at β** with the index computed at the child
   (`o[j, fst r, p]`), at a neutral index.
4. **Codes** (§5), later, as M13b/M17c did.
5. **Not needed for the round**, only to keep the door honest: whether
   "bisimilar ⇒ `Id`" is consistent with the no-UIP model
   (`docs/no-uip-model.md`). The recommendation is not to add it, so this
   is low priority.

The bridge of §4 is a theorem about the library, to prove in Heather once
the kernel and library rounds land; `probes/ItreeDepthBisim.v` already has
its Coq shape.

---

## 10. Sequencing

1. **This design reviewed** (Minus). Decision points: indexed from the
   start (§1.1), the apomorphism (§2.2), no identification axiom (§8),
   guarded recursion deferred (§8).
2. **heather-coq, the relation and decidability** (§9 Q1–Q3), before any
   kernel code; it can run beside the library planning.
3. **Kernel round**: `Type::M`, `Term::Corec`, `Term::Out` and their values;
   typing at p/m; eval and whnf; conversion of §2.1; the oracle's sharing
   (§7); `Debug` gated by `node()` (`crates/kernel/src/fmt.rs`); tests on
   the four axes of `docs/testing-generated-terms.md` (literal and neutral
   index and seed, an open carrier, a checking position, and negative
   controls: two `corec`s of one tree, `corec` against a neutral, `t`
   against `in(out t)`).
4. **Elaborator**: `codata` declarations, constructors as `in`, `match`
   through `out`, guarded corecursive definitions (§6).
5. **Library**: the coinductive tree, `approx`, `Bisim` and eutt as `M`
   instances, the bridge of §4, `Sim`'s coinductive form (§6.1).
6. **Codes** (§5), when a meta-program needs them.

## Sources

- Ahrens, Capriotti, Spadotti, *Non-wellfounded trees in Homotopy Type
  Theory*, TLCA 2015 (not in `docs/`).
- Abel, Pientka, Thibodeau, Setzer, *Copatterns*, POPL 2013; Basold and
  Geuvers, *Type theory based on dependent inductive and coinductive
  types*, LICS 2016 (destructor-presented coinductive types with
  corecursion, the shape chosen here).
- Danielsson and Altenkirch, *Subtyping, declaratively* (MPC 2010), for
  mixed induction–coinduction as νμ nesting.
- Xia et al., *Interaction Trees* (`docs/3371119.pdf`), Frumin et al.,
  *Guarded Interaction Trees* (`docs/2307.08514.pdf`), and the fit study
  `docs/interaction-trees-fit.md` §3.
- Gratzer and Birkedal, *A Stratified Approach to Löb Induction*, FSCD 2022;
  Bahr, Grathwohl and Møgelberg, *The clocks are ticking*, LICS 2017.
- heather-coq: `probes/ItreeDepthBisim.v` (MinusGix/heather-coq#9),
  `theories/LogRel/Def.v` (`WRel`), `M13_DESIGN.md`, `M17_DESIGN.md`.
