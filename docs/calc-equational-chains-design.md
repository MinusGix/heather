# calc chains: justification, contexts, and the relations it does not chain

Design record for `issues/calc-equational-chains.md`, 2026-08-18. The issue's
title says "instead of trans/j towers", and the first thing this round did was
notice that the *form* already exists: `calc` landed 2026-07-24 as pure parser
desugaring (`issues/surface-operators.md`), and since 2026-08-17 it pins each
step's endpoints on the emitted `trans` **by name**
(`docs/named-arguments-design.md`). So the open questions are the three the
issue actually asks — how a step names its justification, how a context is
spelled inside a step, and what happens to relations other than `=` — and the
first deliverable was to *measure* what the existing pieces already compose to,
because yesterday's round (`docs/congruence-in-inference-position-design.md`)
changed the answer after the issue was filed.

**Scope guard, restated from the issue's 2026-08-18 log entry because it is
binding:** calc's value case is readability and hand-override certificates.
It is not what unblocks the library's congruence sites — the measurement below
confirms the recorded split rather than revising it — and this document does
not sell it as that.

## 1. What HEAD already does inside a calc step (measured)

Three probes against the built `heather` at HEAD, before any change:

**1.1 The terse `cong(p)` works inside a calc step — for spelling-level
contexts.** `add_comm`'s `Succ` arm as the surface-v1 §1 block, with the
middle step `= Succ(n + k) := cong(ih)`: **checks.** Two mechanisms compose
to make this true, neither of them built for calc: the desugaring pins
`a`/`b`/`c` by name, so every step proof has a fully-determined domain — a
*checking* position — and the result-only-implicit deferral
(`call_defers_for_result_only`, 2026-08-18) elaborates `cong(p)` at that
type, where the LGG generalizes. This is the §1.1 bucket of
`docs/congruence-in-inference-position-design.md` cleared *by construction*:
a calc step is the one place the author has already written both endpoints,
so the failure mode "the middle endpoint is not in the expected type" cannot
occur.

**1.2 The computation wall stands inside calc, exactly as measured outside
it.** `addNat_zero_l`'s `Succ` arm as a calc step,
`addNat(OfNat(0), Succ(k)) = OfNat(Succ(k)) := cong(ih)`: **fails**,
`cannot generalize`, same error as in plain checking position. Nothing else
was possible — a calc step states its sides in the same unreduced terms the
theorem does, and the wanted context (`isucc`) appears in neither side's
spelling. Calc changes where the expected type comes from, not what it says.

**1.3 The author can state the computation fact — as a refl step.** The same
`addNat_zero_l` arm with the reduct written as an intermediate endpoint:

```heather
calc {
    addNat(OfNat(0), Succ(k))
        = isucc(addNat(OfNat(0), k)) := refl,
        = isucc(OfNat(k))            := cong(ih),
        = OfNat(Succ(k))             := refl,
}
```

**checks**, terse `cong` included. The wall says no anti-unifier can *see*
the conversion fact; it never said the human cannot *state* it, and a calc
chain's explicit intermediate endpoints are exactly the place to state it.
The `refl` step costs one line and buys the reader the δι-step the tower
kept implicit inside a `cong_int(isucc, …)` motive. This is the calc-native
spelling of a computation-level context, and it is a *spelling*, not a
mechanism: nothing was inferred, the author wrote the reduct.

Consequence for this round: **the mechanism is done; what was missing is the
record, the pinned tests, and the library evidence.** No parser or elaborator
change is needed for decisions 1 and 2, and none is made.

## 2. Decision: a step's justification is `:= expr`, and stays that

The step discharge spelling was settled in surface-v1 §1 (round-0's `by`
dropped: there is no proof "mode"; every proof position is an ordinary
expression position). No new evidence arrived, so it is not relitigated.
What this round adds is the *seam* the issue asked to leave for
`issues/grind-port.md` and its kin, and the seam is: **the slot after `:=` is an
ordinary expression in checking position at the step's stated equation, and
that is the whole contract.**

Everything automation-shaped this surface already has arrives as an
expression form — `decide<…>()`, `?goal` holes with `on` discharge — and
therefore already flows into the slot. Measured (and pinned by a test):
`= Succ(n + k) := ?mid` raises a goal *named and typed by the step*,
dischargeable by `on ?mid := cong(ih)` at the declaration block. That is
tactic-shaped workflow today: state the chain, leave the steps open, fill
them below. When grind exists, `:= grind()` (or whatever its expression
spelling is) needs nothing from calc — the step hands it exactly the goal a
tactic wants, both endpoints written.

Rejected: a per-step keyword (`by`, `via`, `..`) distinguishing "term" from
"tactic" justifications. It would reintroduce the two-language split that
surface-v0 → v1 deliberately removed, and it buys nothing: the distinction it
marks does not exist in this elaborator, where automation *is* expressions.

## 3. Decision: the context spelling inside a step is `cong(p)`, plus a refl step when the context is computational

The calc-native spelling of rewriting-under-a-context is the terse
`cong(p)` — no calc-specific syntax, because a calc step *is* the checking
position the 2026-08-18 deferral was built to reach (§1.1). For the §1.2
bucket, the spelling is the reduct-as-refl-step pattern of §1.3: one `refl`
step to the reduced form, then `cong(p)` where both sides now spell the
context. Where the extra line is noise rather than information — a chain
already long, a reduct uglier than the motive — the explicit lemma
(`cong_int(isucc, p)`, `cong_nat(λ …, p)`, `@cong(…)`) remains available and
remains the right call; the library rewrites below use both, deliberately.

One boundary of the terse spelling surfaced during the library rewrites and
is recorded on `issues/congruence-by-anti-unification.md` (2026-08-18 datum): a
cross-type context through a constructor — `cong(nat::mul_assoc(…))` at an
expected `neg(OfNat(X)) = neg(OfNat(Y))` — is refused because the two sides'
elaborated `OfNat` annotations spell the inductive's type differently
(raw Σ-code vs `El(code)`), convertible but unequal, so the LGG sees a
spurious differing position at the annotation. Those steps keep
`cong_ofnat`/`cong_int`, which is no loss inside a chain: the step still
states its endpoints.

**That boundary is wider than this paragraph reads, measured 2026-09-19.**
Converting `docs/showcase/calc_text.hthr` — the first client outside the file
the rule was born in — offered terse `cong` 15 sites and it was refused at
four, in three different shapes: under `Cons(·, …)` at `Char`, under a lowered
inductive's constructor (`Plus(·, …)` at `Expr`), and under a defined function
(`spell(d, ·)`). Two of the four are the cause above — a type spelled as a raw
code on one side and `El` of that code on the other. The other two are *not*:
the terms at the differing position part at a constructor payload (`pair`
against `variable`), which is a pattern-derived constructor against a written
one, so the family is "an elaboration detail the surface spelling drops" rather
than the `El` wrapper specifically. Either way it is not confined to cross-type
constructor contexts, and a chain author should expect the explicit lemma to be
needed wherever the context's arguments carry structure the author did not
write. The refusals are now self-explaining
(`issues/lgg-error-hides-the-implicit.md`); before that round two of the four
produced a message that named the same two terms as both the difference and the
match.

The consequence for §3's decision is none — `cong(p)` remains the calc-native
spelling where it fires, and the explicit lemma remains the fallback the
decision already names. What changes is the *expectation*: a chain over a
library's own inductives will use the explicit lemma more often than "one
recorded cross-type case" suggests.

Rejected alternatives, with reasons:

- **Hole-in-term contexts** (`= Succ(_) := p`, Isabelle-style): decides by
  *spelling* what §1.2 proved is a fact about *computation* — `Succ(_)`
  written against `addNat(OfNat(0), Succ(k))` matches nothing until a δι
  step has happened, so the form would work exactly where `cong(p)` already
  works and fail exactly where it fails, while adding a second binding form
  to the grammar.
- **Per-step rewrite directives** (`= rhs at 2 := p`, occurrence selection):
  this is `rewrite`, it belongs to the layer-m tactic surface
  (`docs/congruence-in-inference-position-design.md` §1.3 argues this from
  the same data), and building it into calc's grammar would pin tactic
  design decisions inside a parser desugaring.
- **Motive sugar on the step** (`= rhs by cong isucc := p`): strictly worse
  than writing `cong_int(isucc, p)` in the slot that already exists.

## 4. Decision: relations other than `=` are residue, filed with their shape pinned

Lean's calc mixes `=`/`≤`/`<` via `Trans R S T` instances. The library now
has the raw material — `Le`/`Lt` at `Nat` and `Int`, `le_trans`, `lt_trans`,
`le_of_lt` — and the traits layer has value-generic instances, so the
*eventual* design is clear and is recorded on the residue issue: a step
carries its relation token (`=`, `<=`, `<`), and the fold emits a call on a
`Trans`-class method resolved per adjacent pair, exactly as `+` resolves
`add`.

Not this round, for three reasons, in strength order:

1. **The library does not ask for it yet.** The order kits' transitivity
   sites are few (single-digit `le_trans` call sites per file) and none is a
   *chain* — each is one composition, already one line. The library-drives-
   features rule says the ranking datum is a stalled lib row, and there is no
   stalled row.
2. **The kit lemmas do not have the shape the desugaring needs.** `trans` is
   pinned by *named* endpoints (`a := …, b := …, c := …`); `le_trans` is
   spelled `le_trans(n)(m, l, h1, h2)` — curried, positional, endpoints
   explicit — and `nat::le_trans` and `int::le_trans` do not even share a
   calling convention. A parser desugaring over those spellings would encode
   two library-private shapes; the honest prerequisite is a `Trans` class,
   which is a traits-layer design with its own review.
3. **Mixed chains need the mixed lemmas** (`=`-into-`≤` transport,
   `<`-absorbs-`≤` on both sides), which do not exist yet and should be
   demanded by a consumer, not stocked speculatively.

Filed as `issues/calc-over-order-relations.md` with the design shape above,
triggered on the first library proof that wants an inequality *chain*.

**Built 2026-10-15** in that shape once the rationals hit the trigger: see
[calc-order-chains](calc-order-chains.md). Reason 2 was answered by a `Trans`
class plus explicit-endpoint helpers in `relation_props`, not by the kit
spellings; reason 3 by the mixed lemmas the rational order round added.

## 5. What the desugaring keeps (and the property that makes §1 true)

Unchanged, restated as commitments because §1 leans on them:

- **Explicit endpoints on every emitted `trans`, pinned by name.** This is
  what makes every step proof a checking position (and gives `refl` steps
  their type). Any future change that drops an endpoint to "let it infer"
  reverts §1.1 by construction; the elaborator test suite now pins the
  composed behavior, not just the emitted shape.
- **Right-nested fold; single-step calc is the bare proof.**
- **`=` in endpoint position is the step separator** (suppressed as the
  Id-former; parenthesize to state an equality-between-equalities), and the
  chain proves `e0 = e_last` — the first step is the only one that writes
  its left side.

## 6. The library evidence (acceptance for the readability case)

Representative towers rewritten as calc chains, statements untouched —
chosen where the form pays and left alone where it does not:

- `lib/std/num/nat.hthr`: `mul_succ_left`, `mul_comm`, `mul_shuffle` (the
  4-deep pure-monoid tower; the poster child), `pow_mul`.
- `lib/std/num/int.hthr`: `neg_add`'s `isucc` arm (the file's deepest
  single-arm tower), `mul_neg_l`, and `mul_assoc`'s two worst sign cases
  (the `sym(trans(…))` towers, which a chain states forward instead of
  composing backwards).

Deliberately not rewritten: two-leaf `trans(p, sym(q))` one-liners (`calc`
is longer and says less), the `int_ind` two-step arms (borderline; the
towers above were the case to make, and a wholesale migration is a style
decision the file owners — future rounds — can take with the pattern now
established), and everything behind the §1.2 wall that would need a reduct
step per line without a reader gain.

The terse-`cong` inside these chains is used where the endpoints already
spell the context (per §3); the previous round's decision not to migrate the
84 plain congruence sites stands untouched — those sit outside calc blocks,
and their arithmetic is unchanged.

## 7. Tests

`crates/elab/tests/operators.rs` grows the composed-behavior pins, on the
`docs/testing-generated-terms.md` axes where they apply: terse `cong` in a
calc step at a **neutral** scrutinee and at an **open** context (checking
via the step, the §1.1 clearance); the §1.2 shape as a **negative control**
(must still fail, so the wall's retreat would be noticed); the
reduct-as-refl-step pattern (must pass); the `?hole`-in-step seam with `on`
discharge; and the existing parser desugaring tests stay as they are.
