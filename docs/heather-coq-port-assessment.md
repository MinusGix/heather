# Porting heather-coq into Heather: blockers and challenges

Status: assessment, 2026-10-24. Nothing is ported. This note serves the
roadmap milestone `math-metatheory` and relates it to `hih-kernel-model`
(`docs/kernel-model-design.md`). The umbrella issue is
`issues/heather-coq-port.md`.

Surveyed at heather-coq `bb9dd75` (M18a, 2026-10-24) and Heather master
`87348e3`.

## 1. The question

Minus asked (2026-10-24) what stands in the way of a copy of heather-coq
written in Heather. heather-coq stays the primary repository: the abstract
formalization with the nice properties. The copy is for experience in
writing metatheory in Heather, and for the tools that writing it would force
into existence. Heather-in-Heather proper would later prove things relative
to the copy, and may grow tooling of its own, since it will look different.

The answer has one limit that comes from logic and cannot be engineered
away, and a list of language and tooling gaps that can be:

- **The limit (§3).** heather-coq's headline results (normalization,
  canonicity, consistency, decidability of conversion and of type checking)
  are, in substance, a consistency proof for Heather's own kernel. By
  Gödel's second incompleteness theorem, Heather cannot prove that about
  itself. heather-coq gets around this because Coq's impredicative `Prop`
  makes Coq stronger than Heather, and the logical relation leans on exactly
  that impredicativity. So a Heather copy can define everything and prove
  the syntactic metatheory, but it can carry the semantic half only for
  fragments that are strictly weaker than Heather.
- **The gaps (§4, §5).** Heather has no surface form for mutual inductive
  families. It has no indexed families with infinitary premises. `match`
  does not invert at a recursive index type. There is no proof search, no
  `inversion`, no rewrite sets, no sections and no user notation. And the
  copy would be about twice the size of the whole of `lib/` today, in a
  style that relies on automation.

None of the gaps is a reason not to start. They are close to the list of
things the `tactics` and `language` areas want anyway, and a copy is a
demanding customer for them. §8 proposes an order of work.

## 2. What heather-coq is

heather-coq formalizes DeLaM (Hu and Pientka) and Heather's kernel extensions
to it. It follows logrel-coq's architecture: a Kripke logical relation over
reduction, with the generic equivalence of Abel, Öhman and Vezzosi
instantiated twice, once declaratively and once algorithmically. Its
milestones run from M1 (the MLTT core) to M18a (the `M` former, as probes).
It has no admits and no axioms.

| Measure | Value |
|---|---|
| `.v` files (theories, probes and the spike) | 213 |
| Lines of Coq | about 108,000 |
| `Lemma` / `Theorem` | 6,716 / 204 |
| Uses of `rewrite` / `destruct` / `induction` | 5,254 / 5,851 / 724 |
| `auto` / `eauto` | 1,874 / 1,199 |
| `inversion` | 425 |
| `lia` | 914 |
| `match goal` / `Ltac` definitions / `Hint`s | 874 / 540 / 195 |
| `Section`s / `Proof using` clauses | 316 / 1,625 |
| `Notation`s | 547 |
| A clean build | 10 to 26 minutes at `-j4` |

For comparison, all of Heather's `lib/` is about 50,000 lines.

The tree has four layers, each built on the one before:

1. **`Syntax/`.** Hand-written de Bruijn syntax in four mutual sorts (`ty`,
   `tm`, `ctx`, `lsub`), with about 90 constructors between `ty` and `tm`.
   It has renamings and substitutions for local variables, globals and
   universe levels, each as a mutual fixpoint. It also has levels with
   *semantic* equivalence (equal under every valuation), untyped weak-head
   reduction (ch. 06), normal forms, and the code recursor's tables.
2. **`Typing/`.** Seven mutual `Prop` judgments (`wf_glob`, `wf_ctx`,
   `wf_ty`, `wf_tm`, `eq_ty`, `eq_tm`, `eq_ctx`) with 236 rules, indexed by
   global context, layer, context, terms, types and levels. On top of them
   is the syntactic metatheory: weakening, substitution, functionality,
   presupposition, Static Code, inversion, and the algorithmic judgments.
3. **`LogRel/`.** `LR n rec G Γ T T' l R`. It is a `Prop` inductive whose
   index `R : tm → tm → Prop` is the term relation. It is staged by a level
   measure `n`, and its Π, Σ, W and modal cases have Kripke premises
   (`∀ ρ : kwk G Γ, LR … (domR ρ)`). Irrelevance, symmetry, transitivity,
   weakening, escape and the ω tier come with it.
4. **`Validity/`.** Validity, the fundamental theorems at the layers it
   covers, and their consequences: weak-head normalization, injectivity and
   discrimination of formers, canonicity, consistency, completeness and
   decidability of algorithmic conversion, and decidable type checking.

`probes/` holds standalone checks that Heather's design rounds asked for:
the `IWf` lowerings, the `M` former's model and its relation case, the
no-UIP components and depth-indexed bisimilarity.

## 3. The hard limit: predicativity and Gödel

### 3.1 Where heather-coq uses impredicativity

The relation is `Prop`-valued "as required by the universe hierarchy"
(`LogRel/Def.v`, citing logrel-coq-spike's `SPIKE_UNIVERSES.md`). That
decision does real work in three places:

- `LR`'s index `R` is itself a relation into `Prop`, and so are `domR` and
  `codR` in the Π case. The inductive lives in `Prop` anyway, because `Prop`
  is impredicative.
- The universe case's term relation `URel rec G Γ l0` says `∃ R, rec l0 …
  R`. It quantifies over relations, yet it is again a relation into `Prop`.
  This is what lets every stage `n` live in the same sort.
- Saturation (`releq R canonical` in every case) quantifies over all
  relations equivalent to the canonical one. It is what keeps the relation's
  metatheory free of axioms.

Heather is predicative, by decision (`docs/sprop-design.md`;
`docs/interaction-trees-fit.md` §3.7 meets the same wall for `eutt`). In
Heather, a relation over `tm` into `Ty 0` lives in `Ty 1`. So stage `n`'s
term relations live in `Ty (n+1)`, because the universe case at stage `n`
quantifies over stage `n−1`'s relations. A family of stages needs a
universe level that a natural number computes, and Heather's levels are
level expressions, not terms. `UΠ` abstracts over levels but cannot take
one from a `Nat`.

### 3.2 Why it cannot be engineered away

M7 proves consistency of the object theory. That theory is DeLaM plus Σ, Id,
sums, W, `Wf`, `IWf`, strict equality and truncation, which is Heather's
kernel up to presentation. If Heather proved the fundamental theorem for
its own kernel, it would prove its own consistency, and by Gödel's second
theorem it would then be inconsistent. So a Heather copy of heather-coq's
semantic half can only cover object theories strictly weaker than Heather.
Here that means fewer universes than the meta level uses:

- **No object universe.** The relation fits in `Ty 1` with no staging. This
  covers MLTT with Π, Σ, Nat, Empty, sums, Id and W, which is where M1, M8,
  M11 to M13 live.
- **`k` object universes.** Write one stage as a level-polymorphic function,
  from the stage below at level `ℓ` to a relation at level `ℓ+1`, and apply
  it `k` times by hand. The meta level uses `k+1` universes. The ω tier, with
  `UΠ` and level variables ranging over all levels, is out of reach, because
  it needs a meta universe above every finite one.

The results that come out of the relation are the ones that inherit the
limit. They are normalization, injectivity of formers, canonicity,
consistency, and completeness and decidability of conversion and of type
checking. They also include anything that uses them: heather-coq's typed
reduction notes that the β case of preservation needs Π-injectivity, which
only the relation gives (`M1_DESIGN.md`, "Typed reduction includes its
equation").

### 3.3 What this means for Heather-in-Heather

This fits Minus's framing, and it explains it. Heather-in-Heather should
**state** things relative to the copy's definitions. It should **cite**
heather-coq for the metatheorems about Heather's full kernel, and never
re-prove them. `docs/kernel-model-design.md` §5 already splits trust this
way ("the metatheory of the calculus itself … stays heather-coq's job").
The copy makes that sentence formal: there is a Heather definition of the
reference relation, and it is checked against the Coq one (§7.3).

How close Heather can get to the full result anyway (a reflection schema, a
tracked axiom, a reparametrized heather-coq) is §11.

## 4. Language blockers (fixable)

Each item says what heather-coq needs, where Heather stands, and who owns it.

### 4.1 Mutual inductive families

The syntax has four mutual sorts and the judgments have seven. Heather's
kernel route is known: one `IWf` indexed by `Σ(tag). I_tag`, checked in
heather-coq's own rules, with the tag-dependent case included
(`probes/IwfLowering2.v`; `docs/iwf-former-design.md` §12.2). But there is no
surface form. `crates/syntax` has no mutual inductive declaration, and
`issues/indexed-families.md` explicitly leaves mutual declarations out of
scope. Writing the Σ-tag encoding by hand for 236 rules is not a port.
Owner: new issue `mutual-inductive-declarations`.

### 4.2 Indexed families with infinitary premises

`LR`'s Π, Σ and W cases, and the modal cases at M, have premises quantified
over Kripke worlds. These are infinitary premises in an *indexed* family,
and the index includes relations, so it is large. Heather has two partial
answers, and neither covers this case:

- `IWf` is finitary: its children are a `DVec` of a computed length.
- Tier 2 (`docs/inductive-tier2-w-lowering.md`) is infinitary but unindexed,
  with at most one recursive function field per constructor.

There are three options, in order of how much they change:

1. **Indexed `W` in the kernel.** This is the most direct. It is a former
   round at `IWf`'s yardstick, and heather-coq would need an M-milestone for
   it first, as `IWf` had M17.
2. **A tier-2 lowering for indexed families.** Use `W` plus an index
   well-formedness predicate, in the spirit of `acc-via-w.md`. This needs no
   kernel change. It needs no funext either, as long as derivations are only
   eliminated and never compared, and that is the case for a relation used as
   a predicate.
3. **A finitary redesign of the relation.** Store one domain derivation and
   prove that weakening preserves it, instead of quantifying over worlds in
   the premise. logrel-coq quantifies precisely so that it can avoid that
   lemma during the definition. Whether a finitary variant goes through is a
   research question, best asked in a probe in heather-coq first.

Owner: new issue `indexed-infinitary-families`. Option 2 is the recommended
first probe.

### 4.3 Inversion at recursive index types, and tier-3 unification

heather-coq uses `inversion` 425 times, nearly always on a judgment at a
constructor-headed term index (`wf_tm G i Γ (app …) T l`). Heather's `match`
inverts at a constructor-headed index only for `Nat` and flat declared index
types. At a recursive index type, such as a `Wf`-lowered `tm`, it falls back
to abstraction (`issues/iwf-inversion-recursive-index.md`, open). Proper
unification without K, with deletion at index types that have decidable
equality (Hedberg), is tier 3 of `docs/iwf-former-design.md` §8.3. It is
deferred "when an example needs it", and this port is that example. The
syntax has decidable equality, so Hedberg's K is available and no axiom is
needed.

### 4.4 Scale of a single declaration

The term syntax has about 90 constructors, and `Declarative.v` has 236 rules.
`IWf` lowers each family to case trees over the shape (`n`, `o`, `c`, and
convoys on the position), so the generator's output and the elaborator's
work grow with the constructor count. The largest inductive in `lib/` today has
17 constructors (`Asm`, in `lib/std/arch/x86_64/x86_64_asm.hthr`). heather-coq's own build-time gotchas
(quadratic case splits, raw fixpoints, failing searches against every
former) are the Coq face of this. Heather will meet its own versions, in the
elaborator's whnf (`computed-types-elaborator-cost` in project memory) and
in kernel term size. The first rung (§8) should measure a 90-constructor
syntax and a 100-plus rule judgment before anything is built on them.

### 4.5 Sections, notation and level placement

These are smaller items:

- **Sections.** There are 316 sections and 1,625 `Proof using` clauses.
  `RecS*` splits a section across files through a hypothesis class
  (`docs/gotchas.md`, "A section split across files"). Heather has no
  sections, so every section variable becomes an explicit or implicit
  parameter. Heather's classes can carry the hypothesis bundles, which is the
  shape `RecHyps` already has.
- **Notation.** heather-coq has 547 notations, for example
  `[ G ; Γ ⊢[ i ] t : T @ l ]`. `issues/notation-extensibility.md` is open.
  Without notation the judgments are spelled `wf_tm(G, i, Γ, t, T, l)`. This
  is readable, but it is a real cost to reviewing a port line by line
  against the original.
- **Relevance.** Coq's `Prop` becomes Heather's `Ty 0` (or a squash). Proofs
  become relevant data, so the large derivation terms are kept, not erased.
  Definitional irrelevance is lost too, and no heather-coq proof relies on
  it.

## 5. The automation gap

The bulk of heather-coq's 108k lines is "one case per constructor, closed by
automation". The table maps its working set onto Heather's.

| heather-coq | Uses | Heather today | Gap |
|---|---|---|---|
| `auto`/`eauto` with hint databases, `econstructor`, per-case constructor search (`wk_step`) | about 3,000 | `apply`, `assumption`, `first_of`, `constructor`, `split_all` (`lib/std/tactic/tactic.hthr`); no hint database, no depth-bounded search | the largest gap; owned by `tac-general` |
| `inversion` | 425 | `match` with tier-1/2 inversion | §4.3 |
| `rewrite`, and the generated `push_*` head tables | 5,254 | `rewrite`, `subst`, `rewrite` in a hypothesis | no rewrite *sets* (a simp set keyed by head), which is what the push tables are |
| `lia` | 914 | `omega`, with fact arguments | covered |
| `congruence` | 124 | none | `tac-general` (congruence closure) |
| `match goal`, 540 `Ltac` definitions, `Ltac … ::=` hooks | 874 matches | `Tac<A>` reads the goal and builds checked terms (`goal`, `view`, `match_conclusion`) | no hypothesis-pattern combinators, and no late-bound hooks |
| `induction` on mutual judgments, with 16 `Scheme`s | 724 | `match` with recursive calls, and mutual `fn` groups | depends on §4.1 |
| `Proof using`, `vos`/`vok` | | sealed theorems; per-module images and the early cutoff | comparable |

Two consequences follow.

- **A hand port in term mode is not realistic.** The first rung should be
  written by hand on purpose, to learn which tactics are missing. The second
  should not start until search, rewrite sets and inversion exist.
- **The demand is general, not port-specific.** Every row above is already
  on the `tactics` roadmap (rank 2) or the `language` area. The port gives
  those rows a concrete, measurable workload, for example "every weakening
  case closes by one call".

## 6. What carries over cleanly

None of the following hits §3, and after §4.1 to §4.3 they hit no language
gap either:

- **Syntax and the substitution calculus.** The sorts, renamings,
  substitutions, their composition and commutation laws, and levels with
  semantic equivalence (a `∀` over valuations, so no funext). heather-coq
  uses no axioms, and renamings as functions `nat → nat` are only applied,
  never compared.
- **Untyped weak-head reduction and normal forms** (ch. 06). This is the
  reference relation that `kernel_reduction.hthr` currently re-derives on
  its own seven-constructor fragment.
- **The declarative judgments and their syntactic metatheory.** Weakening,
  substitution, functionality, presupposition and Static Code. These are
  first-order statements about finitary derivations.
- **The algorithmic judgments, as definitions.** Their soundness is not on
  this list. `AlgSound.v` takes the right-hand pieces of the declarative
  congruences from `AlgPrereq`, which requires `Validity/Reducible*`, so
  soundness uses the relation's consequences just as completeness does.
  For a fragment, both come with rung 3 of §9.

Everything in heather-coq's `Typing/` qualifies. No file there imports
`LogRel/` or `Validity/`. Preservation is not in it, because it lives in
`Validity/` after canonicity.
- **Probes.** `MCoind.v` and `ItreeDepthBisim.v` map onto Heather's `M`
  former and `lib/std/itree`. The kernel already has the former, and the
  coinductive library has `eutt`.
- **The semantic half for fragments.** MLTT without universes (§3.2) at
  meta level `Ty 1`. After §4.2, this is exactly what the roadmap's
  `math-metatheory` names: "a small logical-relation proof".

## 7. Routes

### 7.1 A hand port of a vertical slice (recommended to start)

Take the MLTT fragment through all four layers: syntax, typing, a relation
with no universe, and normalization and canonicity for that fragment. It
exercises every blocker in §4 and §5 at a size where the failures are
legible. It gives the experience Minus asked for.

### 7.2 Generating both sides from one rule table

heather-coq already generates its push tactics (`tools/gen_push.py`).
Heather's kernel transcribes its recursor telescopes from heather-coq's
`RecSpec` binder for binder, by hand (`issues/iwf-former.md`, 2026-10-22). The rule tables could be the shared artifact: the syntax
constructors, the typing rules, and the recursor branches. A generator would
emit both the Coq declarations and the Heather ones, so the copy cannot
drift from the primary as heather-coq gains formers. The proofs would still
be written separately on each side. This is the strongest answer to
"keeping a copy" over time, but it is worth building only once the
hand-written slice has fixed what the Heather side should look like.
(Project memory notes one existing drift: heather-coq's recursor numbering
runs one ahead of Heather's from branch 51. A shared table would remove that
kind of mismatch.)

### 7.3 Checking the copy against the original by export

`crates/export` prints Heather's kernel terms for Lean and Rocq. If the
copy's definitions (syntax, reduction, judgments) are exported to Rocq and
proved isomorphic to heather-coq's in Coq, then "the Heather definition is
the reference relation" becomes a checked fact, not a convention. The cost is
real. The export emits `IWf` lowerings, not native Coq inductives, so each
isomorphism is a proof. But it is the step that lets Heather-in-Heather's
theorems inherit heather-coq's metatheorems honestly. It also extends the
`heather-in-lean-coq` area, which Minus wants more than import.

### 7.4 Importing Coq proof terms (not recommended)

A Coq-to-Heather importer of elaborated proof terms would bring the
syntactic half over in bulk. But it gives none of the experience that is the
point. It must compile Coq's `fix`/`match` into Heather's eliminators at
236-rule scale, and it fails on every impredicative definition (§3.1).
`lean-fragment` already faces the same problem for Lean, and that milestone
is the place for it if it is ever wanted.

## 8. Relation to the Heather-in-Heather ladder

`hih-kernel-model` (PR #155) models the kernel's weak-head reduction on its
own locally nameless λ+Nat fragment and takes "the reference relation as
given". The copy supplies that relation, so the two ladders meet in three
places:

- **Rung 2 (`hih-km-runs`) needs Σ and projections.** heather-coq's syntax
  already has them. Two paths are possible. The model could keep its own
  `Tm` and prove one translation lemma, from locally nameless to de Bruijn,
  when the copy's syntax covers the fragment. Or the model could move onto
  the copy's syntax. The recommendation is to keep the model's `Tm`
  separate until the copy's first rung lands, so the kernel model is not
  blocked on the copy's language gaps. Then prove the translation once.
- **Rung 4 (strategy changes) needs conversion in the model.** heather-coq's
  algorithmic conversion (M6) is the natural specification. The copy's
  algorithmic judgments (§6) are what an evaluator strategy should be
  proved to refine. Their soundness for the full kernel is cited from Coq
  (§3.3), not re-proved.
- **Trust.** Kernel-model theorems are stated against the copy's
  definitions. The copy's definitions are checked against heather-coq
  (§7.3). The metatheorems about the full kernel stay in Coq (§3.3).

## 9. Proposed rungs (under `math-metatheory`)

Each rung names the Heather tool it is expected to force. These are
proposals for Minus's review and are not in the roadmap yet.

1. **Syntax and reduction slice.** MLTT syntax (Π, Σ, Nat, Empty, sums, Id)
   in heather-coq's representation, with renaming and substitution, their
   laws, and untyped whnf reduction. It forces a rewrite-set (simp) tactic
   for the substitution laws. It measures §4.4 at the slice's width, and
   then at the full syntax's width by a generated stress declaration.
2. **Declarative typing and syntactic metatheory.** It forces
   `mutual-inductive-declarations`, `iwf-inversion-recursive-index`, tier-3
   inversion, and constructor search (`tac-general`). It ends with weakening
   and substitution.
3. **A logical relation with no universe.** Normalization, canonicity and
   consistency of the slice. It forces `indexed-infinitary-families`. This
   is `math-metatheory`'s current "done when".
4. **One object universe.** A stage written level-polymorphically, applied
   twice. It is the predicativity experiment (§3.2), and nothing in Heather
   has tried it.
5. **Algorithmic conversion, and the bridge to the kernel model** (§8).
   The judgments are definitions. Soundness and completeness are proved for
   the rung-3 fragment, and cited from Coq for the full kernel. Optionally
   the export check of §7.3.

The following stays out of scope, by §3: the full fundamental theorem for
Heather's own kernel, the ω tier, and the code layers' relation at M.
DeLaM's layers, `□` and the code recursor are syntactic, so they can be
added to rungs 1 and 2 later, at a cost that grows with the 66 recursor
branches.

## 10. Decisions for Minus

- Accept §3's limit: the copy carries the semantic half only for fragments,
  and Heather-in-Heather cites heather-coq for the rest.
- Choose a route: a hand slice first (§7.1), with a shared rule table
  (§7.2) only once the slice settles the Heather side's shape.
- Choose the representation the kernel model meets: keep it separate and
  translate once (§8), or migrate the model to the copy's syntax.
- Choose the infinitary option for §4.2 (indexed `W` in the kernel, a
  tier-2 lowering, or a finitary redesign probed in heather-coq first).

## 11. Follow-up: how close to "the full thing" Heather can get

This section answers Minus's follow-up (2026-10-24). His preference is to
have the whole result available inside Heather, to prove against and to
trust, and not to rely on heather-coq as a separate repository.

### 11.1 What Gödel actually connects

Gödel's second theorem is about a proof system as a mathematical object. It
is not about the Rust program. If the copy's object theory `S` is a faithful
presentation of Heather's rules, then the statement "`S` is consistent" is
one way of writing Heather's consistency. Heather can show internally that
every one of its derivations is an `S`-derivation, since that is the
identity on a faithful embedding, and the derivability conditions hold for
any reasonable deep embedding. So the connection is automatic, and it does
not depend on how the Rust kernel works.

Trust in the kernel we actually run splits into two claims:

1. **The checker accepts only derivable judgments.** This means the Rust
   kernel is contained in `S`. It is a statement about an algorithm and a
   relation, and Gödel says nothing against it. This is the
   `hih-kernel-model` ladder: rung 5 is an evaluator proved to compute what
   the model's reduction computes. Heather can prove all of this.
2. **`S` is consistent and normalizing.** Only this claim hits the limit.

So the gap is narrower than "heather-coq is a separate world". The
implementation half can be fully internal. Only the consistency of the rule
set needs something stronger than Heather. The converse also holds. If
Heather ever proved claim 2 for its full kernel, then either the
formalization differs from the kernel, or Heather is inconsistent. That is
the one place where the connection matters, and Gödel guarantees it there.

### 11.2 Three ways to have it inside, with the gap made explicit

1. **The reflection schema (no axioms).** Write the relation once,
   parametric in a bound `n` on the object theory's universes and on the
   valuations of its level variables. Then Heather proves
   `Con(Heather≤n)` for each concrete `n`, at a meta level about `n` plus a
   constant. Every closed derivation names finitely many levels, so every
   theorem anyone actually proves lives in some `Heather≤n`, and you choose
   `n` after the fact. What Heather can never have is the single statement
   "for all `n`". This is the type-theoretic analogue of ZFC proving the
   consistency of each of its finite fragments (reflection). That MLTT with
   one more universe proves normalization of MLTT with fewer is the expected
   outcome, and it is what the stage-by-stage construction of §3.2 does. It
   should still be checked for this rule set, with `W`, `IWf`, `M` and the
   code recursor included, not assumed.
2. **A tracked axiom.** State the full fundamental theorem as an explicit
   axiom with provenance (`docs/axiom-provenance-design.md`), discharged by
   heather-coq. Theorems that depend on it carry the tag. This makes the
   separation visible inside Heather instead of hiding it in a convention.
   Heather plus that axiom is consistent whenever Heather is sound, so the
   axiom is an honest assumption, not a contradiction.
3. **A stronger meta universe.** Add one universe that is closed under
   everything the object theory has. It could be a super-universe, a
   Mahlo-style universe, or induction-recursion. Heather plus that universe
   proves the full fundamental theorem for Heather without it. The gap
   moves up one level and never closes, and the stronger universe is now
   the thing whose soundness is trusted.

**Recommendation:** combine 1 and 2. The schema covers every concrete
theorem with no axiom. The tracked axiom covers statements that really
quantify over all levels, and it marks which theorems those are.

### 11.3 Changing heather-coq so the two match

The impredicativity in heather-coq (§3.1) sits in a few places: the sort of
the term relations, the universe case's `∃R`, and the uniform sort across
stages. A refactor could make the relation parametric in a *tower of
semantic sorts*, `Sem 0 ⊆ Sem 1 ⊆ …`, where `Sem (n+1)` is closed under
`∃` over relations into `Sem n`. Coq instantiates every `Sem n` as `Prop`
and gets today's full theorem. Heather instantiates `Sem n` as `Ty n`,
bounded by the reflection schema (§11.2). One proof gives two instances,
and the Heather copy then follows heather-coq's structure.
Saturation needs only `↔`, so it survives in `Type`. Level variables need
valuations bounded by the tower's height. This is worth a probe in
heather-coq before anything else in §9 is built. It decides whether
"closer copy" and "full thing inside" are one project or two.

## 12. Follow-up: tools that suit type theory better than Coq's

Coq is not designed for metatheory of type theories. heather-coq's
`docs/gotchas.md` is largely a list of workarounds: generated push tables,
hand-ordered dispatchers, raw fixpoints exposed by `cbn`, quadratic former
splits, and section-splitting classes. Heather can treat these as features.
Each item below names what it replaces.

**Syntax and substitution.**
- **A syntax declaration.** It generates multi-sort syntax with several
  binder kinds (local, global and universe variables, as heather-coq has),
  all the renaming and substitution operations, and their laws with proofs.
  This replaces the hand-written `Term.v`/`Subst.v`/`Commute.v` and
  `SYNTAX_SPIKE.md`'s reasons for not using Autosubst.
- **A σ-calculus normalizer as a certified tactic** (Autosubst's `asimpl`,
  with the decidable σ-calculus behind it). It replaces the `push_*` tables
  and `tools/gen_push.py`.
- **Definitional substitution laws, if Heather gets local computation
  rules** (rewrite rules, in the spirit of heather-coq's "Encode the Cake"
  agenda). Then commutation lemmas disappear into conversion. This is a
  kernel question with soundness obligations of its own, and it should be
  probed in heather-coq first.

**Declarations.**
- **Mutual inductive families** (`mutual-inductive-declarations`).
- **Indexed families with infinitary premises**
  (`indexed-infinitary-families`).
- **Induction-recursion.** The Abel–Öhman–Vezzosi relation is naturally
  inductive-recursive: type reducibility is inductive, and term reducibility
  is defined by recursion on it. That removes the relation index and the
  saturation device. Induction-recursion adds proof-theoretic strength,
  which also makes it one form of §11.2's option 3.
- **Modular signatures.** A former is a module that contributes
  constructors, rules, recursor branches and proof cases. The closed syntax
  and judgments are generated from the modules that are present, in the
  style of "Meta-Theory à la Carte" or second-order generalized algebraic
  theories. One heather-coq milestone would be one module, which keeps a
  copy close milestone by milestone and makes a new former cost a module,
  not edits across 200 files.

**Proof automation for metatheory.**
- **Generated generation lemmas.** These are inversion up to conversion, per
  former, derived from the rule table. They replace 425 `inversion`s and
  the manual `Inversion.v`/`InvAny.v`.
- **A rule dispatcher indexed by the conclusion's head**, using a
  discrimination tree instead of hand-ordered `first [...]`. It replaces the
  "dispatcher order" and "failing apply on every case" gotchas.
- **A "for each former" proof combinator.** Most metatheory lemmas are one
  case per constructor, each the same shape. One combinator states the
  case pattern once, and the per-former residue is all that is written.
- **Head discrimination as a primitive.** A tag per constructor, compared as
  a `Nat`, so mismatched former pairs close by conversion. This removes the
  quadratic-split gotcha, and Heather's kernel already accelerates `Nat`.
- **A level-algebra decision procedure.** The max-plus algebra with
  semantic equivalence, certified. It replaces `LevelEq*`.
- **Mutual induction with bundled motives**, generated from the family
  declaration. It replaces the 16 `Scheme`s and selecting hypotheses by
  shape.

**Reflection, which Heather has and Coq does not.** DeLaM's code layer
gives Heather quoted types and a recursor over them (`elim_Typ`/`elim_Trm`).
A `Tac<A>` metaprogram, or a code-layer function, could generate per-former
lemma statements from a signature by recursion over codes. That is the
mechanism behind most of the items above, built into the language.

**Further out: synthetic Tait computability** (Sterling and Harper).
Normalization is proved internally to a modal type theory, so the logical
relation is a construction rather than a hand-built inductive. Heather
already has modalities (DeLaM's layers and `□`). The missing pieces would be
extension or realignment types and a strict gluing modality. This is the
"idealized formalization" direction at its furthest, and it is not a
near-term rung.

Rungs 1 and 2 of §9 are the place to try the syntax declaration, the σ
normalizer and generated inversion. A copy that uses them is less literal,
but each choice can be recorded the way heather-coq records its deviations
from the paper.
