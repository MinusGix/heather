---
title: "A std/logic module: the connectives, with surface syntax"
status: closed
labels: [stdlib,frontend,syntax,design]
created: 2026-08-16
updated: 2026-08-16
---

The library has **no propositional connectives at all**. Grep `lib/` for
`Empty`, `Unit`, `Not`, `And`, `Or`, `Iff`, `Exists`: nothing. Every
proposition currently stated in `lib/std` is either an equation or a `->`
chain, and that is *why* the library drifted to the `= True` idiom —
`leb(x, y) = True` was the only available way to say a non-equational thing.

This issue owns one claim: **the connectives are missing, they are writable
today, and they should exist before another theorem is written.** Nothing
here needs a language feature that has not landed.

## Contents

> **As built (2026-08-16): `docs/library/logic-connectives-design.md` is the source of
> truth, and it differs from the sketch below in two ways the round found by
> building it — `And`/`Iff` take TYPE
> parameters rather than value parameters of type `Type` (a `Type`-carrying
> record sits at level 1), and `Iff` is a record with named directions
> (`mp`/`mpr`) rather than a `fn` into `And`. Falsity IS `False` as sketched;
> the log's (a) records the day it spent as `Empty` and the resolution round
> that bought the name back. The sketch is kept as filed.**


`True` is **already done** and is not declared here: [[true-prop-trivial-hypotheses]]
landed it 2026-08-16 as the kernel's `Unit^0` claimed as a surface type name,
with `trivial` its canonical inhabitant, always in scope. Declaring an
`inductive True { intro }` in `std/logic` would throw away the whole point —
the kernel's η rule gives **judgmental** uniqueness of the inhabitant, i.e.
definitional proof irrelevance at `True`, which a one-constructor inductive
does not have. So:

```heather
inductive False {}
fn Not(P: Type) -> Type { P -> False }
record And(P: Type, Q: Type) { left: P, right: Q }
inductive Or<P, Q> { inl(p: P), inr(q: Q) }
fn Iff(P: Type, Q: Type) -> Type { And(P -> Q, Q -> P) }
record Exists<A>(P: A -> Type) { witness: A, proof: P(witness) }
```

Two questions `False` raises that `True` answered differently:

- **Declaration or claimed kernel type?** The kernel has `Empty` (and a
  separate `sEmpty`; `sprop-strict-prop` deliberately kept them distinct —
  `sEmpty` hypotheses are convertible, `Empty` neutrals structural). A
  declared `inductive False {}` is writable today and is the cheap answer.
  Claiming kernel `Empty` the way `True` claims `Unit` is the alternative,
  and the argument that forced it for `True` (η) has **no analogue here** —
  there is no inhabitant to be unique. Recommendation: declare it, unless
  [[empty-eta-conversion]] turns up a reason not to.
- **How is it eliminated?** By a zero-arm `match`, which works — the empty
  type's "takes no arms" diagnostic exists. Note that surface `absurd`
  currently requires an *equation* (`crates/elab/src/inductive.rs`, the
  `self.equation(cx, arg, "absurd", …)` call), so it does **not** apply to a
  `False` hypothesis. Extending it, or naming the zero-arm match as the
  spelling, is a small decision this issue owns.

`Exists` is the one that needs checking rather than assuming: record **value**
parameters landed with [[surface-existential]], and `lib/certgen/ir_v1.hthr`'s
`Converges` is already this shape, so the record form is expected to work —
confirm before relying on the `P: A -> Type` parameter specifically.

## Syntax

The theorems are unreadable without it — `Or(Le(n, m), Le(m, n))` versus
`n <= m \/ m <= n`. [[comparison-operators]] established that an infix
operator is a lexer token plus one desugar row, and [[type-definitions]]
landed types-as-expressions, so `/\` in type position is an ordinary call.

**Unicode is the spelling** (user, 2026-08-16), not an alternative to an ASCII
digraph set. The repo already establishes it: `λ`, `∙` and the operator
designations lex today, so this is a precedent being followed rather than one
being set.

| spelling | target | notes |
|---|---|---|
| `¬P` | `Not(P)` | prefix, tightest |
| `P ∧ Q` | `And(P, Q)` | |
| `P ∨ Q` | `Or(P, Q)` | looser than `∧` |
| `P ↔ Q` | `Iff(P, Q)` | loosest; **`<->` also accepted** as the casual spelling |
| `∃ x: A, P` | `Exists(λ x: A => P)` | **not** a table row: a binder rung |
| `∀ x: A, P` | `(x: A) -> P` | binder rung; a **synonym**, not a new form |

`<->` is the one deliberate ASCII survivor, on the grounds that it is the
connective people reach for casually. No ASCII `/\`, `\/` or `~`.

Precedence, tightest to loosest: `¬`, `∧`, `∨`, `->`, `↔`; all looser than `=`
and `<=`, which sit at the existing non-associative comparison rung. `->` is
already right-associative and is not touched.

**One consistency question this raises, worth deciding here rather than
drifting:** implication is already spelled ASCII `->`, and it sits *between*
`∨` and `↔` in the table above. Either the connective set accepts one ASCII
member on the grounds that `->` is the function arrow and predates the logic
(the cheap answer), or `→` is admitted as a synonym for symmetry. Same
question for `∀` versus the existing `(x: A) ->`, where the ASCII form is the
dependent function type and is not going anywhere — so `∀` would be a
*synonym*, not a target, if it is admitted at all.

The `exists` rung is the only non-trivial parser work — one binder form,
modelled on the existing `λ` parse.

## What it assumes from elsewhere

- **[[comparison-operators]]** owns the comparison rung and the infix desugar
  table. Assumed here: only that a new operator is a token plus a row, and
  that the rung's non-associativity is where `=`/`<=` live.
- **[[surface-existential]]** owns record value parameters. Assumed here: only
  that they landed and are in use in `lib/certgen/ir_v1.hthr`.
- **[[prelude-option-and-friends]]** owns module residency for `Option`/`List`.
  Assumed here: nothing — `std/logic` is a new module under the same scheme.

## Acceptance

Every declaration above elaborates; each operator has a use site in a real
statement (the first customers are [[nat-order-kit]]'s `le_total` and
trichotomy); a precedence test pinning `¬P ∧ Q` as `(¬P) ∧ Q` and
`P ∨ Q -> R` as `(P ∨ Q) -> R`; `<->` and `↔` shown to agree; a negative
control that `¬` does not capture an application.

## Log

- 2026-08-16: Filed out of the std-API design discussion. The finding that
  produced it: planning a Prop-first Nat order kit turned up `le_total`
  needing `Or` and trichotomy needing both `Or` and `Not`, and neither
  exists — the connectives were an unstated prerequisite of every wave.
  See [[std-api-waves]] for the sequencing.
- 2026-08-16: LANDED (2026-08-16), in full, and the issue CLOSES per tracker rule 3 — both residues left with owners rather than keeping it open. `lib/std/core/logic.hthr` is 138 lines: Empty + its zero-arm elimination, Not as a `fn` into Type (so `¬P` stays definitionally an implication), And and Iff as records, Or as a two-constructor inductive, Exists as the value-parameterized Σ, plus the small kit each owes (absurd_of, mt, and_curry/uncurry, or_elim/or_resolve, iff_refl/sym/trans). THE MODULE NEEDED NO LANGUAGE CHANGE AT ALL: every declaration elaborated on the first attempt, which is the sense in which the connectives were missing rather than unsupported. The whole of the work is grammar — a lexer window, three parser rungs, a precedence flag and two rewinds. Docs: new docs/library/logic-connectives-design.md is the source of truth. THREE FINDINGS, each of which changed the plan this issue was filed with. (a) THE NAME IS `Empty`, NOT `False`, and that is not the preference: `bool::False` is a CONSTRUCTOR exporting the same name, and the resolver keys constructors and type names into one namespace, so a file importing both is told `False` is ambiguous IN TYPE POSITION, where a constructor could never have been meant. `True` escapes only by not being a declaration. Filed as [[false-collides-with-bools-constructor]] with the sharper half recorded: the two type positions DISAGREE about the diagnosis (an annotation says ambiguous, a result type says 'cannot be used here'), so whatever consults the namespace is not the same code in both. When it lands this is a rename. (b) `Exists` DOES NOT INFER ITS TYPE ARGUMENT from the predicate — `Exists(λ (k: Nat) => …)` is refused, `Exists<Nat>(…)` checks — even though the lambda's own annotation determines it and the match is first-order. Introduction is fine (the expected type supplies it). Filed as [[exists-type-arg-not-inferred]]; the `∃` sugar hides it at every site that uses the sugar, by supplying the argument from the binder, which is an argument for filing it rather than letting the notation close the question. (c) THE ISSUE'S OWN `Unit` WAS WRONG and was corrected before implementation: `True` had landed the same day as the kernel's `Unit^0`, so the module declares no unit type and — the part that matters beyond this issue — `Unit`'s η makes `True` JUDGMENTALLY proof-irrelevant, which is now recorded on [[nat-order-kit]] as the strongest argument for its recommended `Le`. NOTATION, as decided in discussion and then built: Unicode IS the spelling (¬ ∧ ∨ ↔ ∃ ∀), following the λ/∙ precedent, with `<->` the single deliberate ASCII survivor lexing to the SAME token as ↔. ∀ is a synonym desugaring to `(x: A) -> P`, so nothing downstream learns a second spelling of the dependent function type; ∃ desugars to `Exists<A>(λ …)` with A taken from the binder. Precedence, tightest first: comparison rung, ¬, ∧, ∨, ->, ↔ — the connectives LOOSER than comparison, which is the opposite of where &&/|| sit and deliberately so (Boolean doubles are arithmetic; these combine propositions). ∧/∨ right-associative on `++`'s proof-relevant reasoning; ↔ non-associative like the comparison rung, with its own message. TWO PIECES OF MACHINERY the design discussion did not predict, both found by building it: `Parser::no_iff` (set by `Parser::cod` at the three codomain sites, mirroring `no_eq`) is what actually makes ↔ looser than ->, since the arrow's codomain reaches `expr()` and would otherwise take the ↔ for itself; and `ty_atom`'s two early-returning atom rules (an applied `D<A>`, a parenthesized group) both had to learn to DECLINE and rewind when a connective follows, the same move the `D<A>` rule already made for a following `(`. Also built and not planned: a targeted message for the flat multi-group quantifier (`∀ x: A, y: B, P`), caught by a two-token lookahead because `:` is not in the expression grammar — without it the parse ends at the name and the error surfaces a span away as whatever the declaration expected next. Tests +25: crates/elab/tests/logic.rs is new (20 — the module, the existential, each connective's notation, five precedence claims each pinned by handing the sugar a hypothesis written in the DESUGARED spelling with the rival reading refused beside it, the two grammar refusals, and controls that &&/|| and the comparison rung are unmoved), and crates/syntax/src/parser.rs gains 5 for what the elaborator cannot see: the lexer windows (`<->` vs `<=` vs `<`, ¬ at two bytes vs ∧ at three, λ unmoved) and the desugared node shapes. RESIDUE, both owned: (a) and (b) above. Nothing else is owed — [[nat-order-kit]] is the customer and its dependency is now met.
- 2026-08-16: Follow-up (2026-08-16, same day): BOTH residues are closed, so this issue owes nothing. (a) [[false-collides-with-bools-constructor]] is fixed by resolve-by-position and `lib/std/core/logic.hthr` now declares `False` rather than the placeholder `Empty` — the module reads as designed, and the one-day detour is recorded there rather than here. (b) [[exists-type-arg-not-inferred]] is fixed, so `Exists(λ (k: Nat) => …)` writes without the type argument and the ∃ sugar is now an ergonomic rather than a workaround. Test names changed accordingly: `false_is_not_available_as_the_empty_types_name` became `the_two_falses_coexist` (plus a control that a `fn` of the same name still stands the expected-type route down), and `exists_does_not_infer_its_type_argument` became `exists_infers_its_type_argument_from_the_predicate` (plus controls for an undetermined parameter and for a partial type-argument list). Suite 25 -> 29 tests from this round.
- 2026-08-16: 2026-08-16: First customer found a real defect in what this issue shipped, fixed in [[nat-order-kit]]'s round (docs/library/nat-order-design.md §5). false_elim and absurd_of took their goal as a VALUE parameter of type Type, which forces an absurd match arm to spell its own goal — long, and sometimes impossible, since or_pick(Inr(bad), x, y) = y cannot infer Inr's left type argument from anything present. Both are type-parameter forms now (false_elim<P>(h: False): P), filled from the checking position the arm is already in. Also landed on logic.hthr: or_pick, the Or-scrutinee branch that replaces algebra's cmp_pick, and or_pick_dec. or_pick is a fn and not a theorem deliberately — or_elim computes the same thing but is opaque, so a decision spelled through it never unfolds in conversion. Two notation gaps this module's grammar has, both filed: [[quantifier-notation-in-type-arguments]] (∃ cannot reach a type-argument slot, parenthesized or not) and [[comparison-inside-type-arguments]].
