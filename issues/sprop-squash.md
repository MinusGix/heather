---
title: Squash ∥·∥ and SProp inductives: the restricted eliminator
status: open
labels: [kernel,delam,design]
created: 2026-08-02
updated: 2026-08-25
---

Deferred from [[sprop-strict-prop]] at filing and still wanted: the
user-facing half of SProp. The landed formers serve the generators — `sEq`
carries fording's index equations, `sEmpty` its no-confusion targets — but
the issue's own charter says SProp exists for "evidence that should be
invisible (index constraints, guard predicates, side conditions)", and
squash `∥·∥` is the former that lets a *user* put ordinary evidence behind
the irrelevance wall.  It now has a promoting stdlib customer:
[[finite-trapping-stack]] needs a squashed `len(contents) <= capacity` field
so reconstructed bounded lists have ordinary equality without making callers
thread validity proofs separately.

The promoted round is deliberately the narrow user-facing squash slice:
formation/introduction, definitional irrelevance, restricted elimination, the
minimum elaborator target recognition needed to present that restriction, and
its metatheory/tests.  The kernel, not that recognition, must enforce soundness
by the eliminator's result shape. General user-declared SProp inductives remain
separable follow-on scope and must not make the `BoundedList` customer wait.

## Scope

1. **Squash `∥A∥`** — the truncation former, with its restricted eliminator
   designed (the part named as "needs designing" at filing). The working
   narrow rule is dependent elimination into a **squash-headed family**, so a
   squashed witness cannot be observed relevantly and the kernel need not ask
   whether an arbitrary result type "is SProp". Whether the first landing also
   gets atomic bridges into `sEq` and `sEmpty` is an explicit scope decision
   below, not hidden inside a generic classifier.
2. **SProp inductives generally** — whether user-declared propositions
   (conjunction, guard predicates) arrive as formers, as squash-of-Σ, or not
   at all. The enumeration invariant makes this a real design choice, not a
   generalization.
3. **Surface SProp target recognition** — elaborator-only, per the dissolved-
   sort decision (`docs/sprop-design.md` §1): the kernel never learns a
   generic classification; the elaborator owns the policy and may synthesize
   admissible elimination routes (as it already owns "`Id` is the surface
   `=`, `sEq` stays generator-internal"). One design section here, not a
   kernel judgment.

## Working eliminator direction (2026-08-25, not yet rule-frozen)

The candidate core rule is genuinely dependent, but its result former is
fixed rather than classified:

```
Γ ⊢ A : Type @ l
Γ, z : ∥A∥ ⊢ B(z) : Type @ l'
Γ, x : A ⊢ b(x) : ∥B(squash(x))∥
Γ ⊢ q : ∥A∥
--------------------------------
Γ ⊢ ind_∥∥(q; z.B; x.b) : ∥B(q)∥
```

with `ind_∥∥(squash(a); z.B; x.b) ⇝ b[a/x]`. Ordinary `bind`, `map`
and `join` are derived by constant motives. The outer `Squash` is the trusted
restriction: representative coherence is automatic because both branch
results inhabit a squash type, while a buggy elaborator still cannot emit an
elimination into `Nat`.

This first rule is a strict dependent squash modality, not by itself a
reflector into every type whose inhabitants the current conversion checker
treats as irrelevant. The distinction is concrete:

- **`Unit`.** Elimination is unnecessary: ignore `q` and return `trivial`.
- **Π with irrelevant codomain.** Introduce the ordinary argument and
  recursively eliminate into the codomain. Even when its domain mentions
  `q`, in a branch `q ≡ squash(x) : ∥A∥` by squash irrelevance, so the
  two domain instances convert and the introduced argument checks.
- **Σ with irrelevant components.** Reconstruct the first component by a
  restricted elimination, then the second. In the witness branch, the
  reconstructed first component and the branch's witness-specific first
  component are definitionally equal at their irrelevant type, so the
  dependent second-component types convert. This is exactly where
  irrelevance vaporizes the apparent coherence obligation. It does **not**
  work when the first component is relevant, nor should such a Σ be
  classified as irrelevant.
- **`sEq` bites atomically.** From `q : ∥A∥` and
  `f : (x : A) -> sEq(I; a; b)`, the narrow rule produces at best
  `∥sEq(I; a; b)∥`; there is no way to lower that to `sEq(I; a; b)`.
  A general SProp eliminator would allow it, but the no-classifier design
  needs a dedicated squash-to-`sEq` eliminator whose result shape the kernel
  checks directly.
- **`sEmpty` bites atomically and observably.** From `q : ∥A∥` and
  `f : A -> sEmpty`, the narrow rule produces only `∥sEmpty∥`, which
  cannot feed `elim_sEmpty`. A dedicated squash-to-`sEmpty` eliminator would
  turn a squashed contradiction into strict absurdity and hence permit
  elimination anywhere. In particular, without that bridge `∥Empty∥` is
  uninhabited in the empty theory but is not internally usable as `False`.

There are therefore three honest scope points: (a) direct squash-valued
dependent elimination only (enough for `BoundedList`); (b) add the two fixed
atomic `sEq`/`sEmpty` bridges, with `Unit`/Π/Σ synthesized
compositionally; or (c) introduce a generic kernel judgment/sort of SProp
targets. The first is the minimum promoted slice, the second remains a
plausible closed enumeration, and the third reopens the declined-sort bill.
No customer currently forces moving past (a).

**Semantic decision (2026-08-25): this is propositional truncation, not an
assertibility/provability predicate.** `squash(a)` seals an actual inhabitant
available at the live program layer; it does not internalize the claim that a
possibly unsound proof system or piece of syntax asserts `A`. Consequently a
release into an already definitionally irrelevant target is semantically
ordinary quotient elimination, not reflection from provability to truth.
In particular, the `sEq`/`sEmpty` bridges above are principled parts of the
eventual truncation universal property, even if lack of a first-round customer
keeps one or both out of the initial kernel slice. A future self-applicable
assertibility notion, if wanted, is a separate code-facing modality and must
not inherit these release rules by analogy.

The staging boundary supports the distinction: code may analyze an explicitly
quoted `squash(a)` and see the syntax of `a`, while no operation turns a live
`q : ∥A∥` into code for or relevant access to its hidden representative.

**Metatheory point found before code.** `Unit`/`sEq`/`sEmpty` use a total
term relation that records no weak-head fact. Squash's eliminator makes
normalization at an irrelevant type operationally load-bearing. The leading
candidate is therefore a **normalizing-total** relation: both related terms
must weak-head normalize, but their resulting canonical/neutral shapes and
the constructor payloads are ignored. Its eliminator case analyzes each
scrutinee independently (constructor gives β plus semantic substitution;
neutral gives a neutral eliminator), while the result relation remains total.
The ch. 07 sketch must establish this and closed canonical forms before the
rule freezes; no normal-form readback is involved.

## Constraints inherited, not re-decidable here

- **The irrelevant-former set is closed and enumerated** in
  `docs/sprop-design.md` — extending it (which squash does) is a design
  round with a ch. 07 obligation and a stated abort criterion, wf-former
  discipline, not a patch. Budget yardstick: the sEq round's rec.rs bill
  was 7 branches + five transcriptions.
- **No third sort.** Squash lands as another `Typ` former with an
  irrelevance arm; if its eliminator restriction turns out to *need* a
  kernel-side classification of "lands in SProp", that is the §1 declined
  alternative resurfacing and the design doc's abort framing applies.
- **The kernel has no normal-form readback** (shared invariant with
  [[whnf-sharing-term-growth]]'s round): any design here that wants one is
  an SProp design round with the TYPES 2024 bill attached.

## What it assumes from elsewhere

- **[[sprop-strict-prop]]** owned the base round. Assumed here: the frozen
  design (per-former arms, no sort) and the landed `sEq`/`sEmpty` formers.
- **[[metatheory-ch07-sprop]]** owns the FT pass for the landed formers.
  Assumed here: squash's own ch. 07 case starts from that pass's
  whnf-then-strip evaluation notion, whatever its final form.

## Log

- 2026-08-02: Filed as the residue owner for [[sprop-strict-prop]]'s
  deferred formers, so that issue can close. No round scheduled; promotion
  needs a customer (a guard predicate, a side condition, an existence proof
  a user wants invisible).
- 2026-08-16: Note from the true-prop discussion (2026-08-16): the 'UProp = Prop | SProp' idea — its disciplined cousin is Rocq-style sort polymorphism (definitions quantified over a sort variable). A union sort proper fails on principal sorts (the two sorts differ in conversion via the SProp strip). Currently no customer: kernel Unit eta already gives True judgmental proof irrelevance without SProp, so sort-generic machinery waits for a real demand.
- 2026-08-25: PROMOTED from unscheduled: [[finite-trapping-stack]] is the first
  ordinary-library customer.  Its `BoundedList` must store an irrelevant fit
  proof while retaining ordinary equality for LIFO laws.  The first round is
  squash plus only the surface classification required by its restricted
  eliminator; general SProp inductives do not gate the customer.
- 2026-08-25: Pre-kernel discussion selected a dependent squash-headed
  eliminator as the working narrow rule and separated trusted result shape
  from elaborator target recognition. `Unit`/Π/Σ targets can be synthesized
  compositionally; `sEq` and `sEmpty` are genuine atomic bridges and remain
  an explicit first-round scope choice. The ch. 07 sketch now owes a
  normalizing-total squash relation and closed canonical forms before freeze.
- 2026-08-25: Semantic direction settled: `Squash` is genuine propositional
  truncation of a live inhabitant, not assertibility/provability of coded
  syntax. Release into a definitionally irrelevant target is therefore
  principled quotient elimination; whether the fixed `sEq`/`sEmpty` bridges
  land immediately remains an implementation-scope question rather than a
  soundness or philosophical objection. Quoted squash syntax stays
  intentionally inspectable across the existing code firewall.
- 2026-08-25: The narrow squash slice LANDED. The kernel now has formation,
  annotated introduction, dependent squash-headed elimination and β;
  conversion uses the normalizing-total rule (both terms reach whnf before
  payloads are ignored). The code universe has four distinct structural
  branches for the type, its encoding, introduction, and elimination. Surface
  syntax accepts `∥A∥` / `Squash<A>`, inferred or checked `squash(a)`, and
  `squash_ind(q, λ z => B, λ x => b)`. No general SProp classifier and no
  `sEq`/`sEmpty` bridge landed; those remain explicit follow-on choices.
- 2026-08-25: The issue remains OPEN for its second half: deciding whether
  user-defined SProp inductives, a target classifier, or either atomic bridge
  has a concrete customer. None of those are required by the implemented
  squash former.
