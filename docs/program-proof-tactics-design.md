# Tactics for proofs about programs

Status: proposal, 2026-11-15. Nothing here is built. Thread "Build tactics
for program proofs".

## 1. The goal

A proof about a program should state the fact that matters and leave the
program's control flow to a tactic: which branch ran, what a loop kept,
what a call returns. The user should not name generated equations
(`clamp::False::True`), restate a loop's body as lambdas, or write the
`let next: ((i + 1).toNat() = i.toNat() + 1) = bv_omega;` lines that only
move a fact to where a solver can read it.

Heather already has most of the parts: `split_all` (case analysis on what
blocks the goal, with each comparison's Nat fact), `bv_omega`, the generated
branch equations (`f::True`, `f::False`, `f::Ctor`), the loop equations
(`f::step`, `f::done`), `simp` with conditional laws, and the loop rules
(`BitVec::loop_up`, `BitVec::run_up_invariant`). What is missing is mostly
where those parts stop short of real programs, plus one new piece: induction
that follows a function's own recursion.

## 2. What programs look like today

Probes run on master `33e8e3f` (the probe files are in the thread's
scratch, reproduced inline here). Each row is a shape that recurs in the
library's program proofs.

| # | Shape | Today |
|---|---|---|
| 1 | One function, its tests decided by the goal: `clamp_inside`, `clamp_within`, `dist(a, b) = dist(b, a)`, `a <= max(a, b)` | `split_all; all_goals { bv_omega }` proves it. |
| 2 | A call nested in a call: `clamp(clamp(x, lo, hi), lo, hi) = clamp(x, lo, hi)`, `a <= max(max(a, b), c)` | Fails. The leaf is handed a goal where the outer comparison is unfolded to its bit-level fold, and the error prints it raw (`if if if fst[0,0]((Σ[0,0](sEq[0](Nat; 988502892; …`). |
| 3 | A precondition that is a Bool function: `h: is_digit(c) = True ⊢ c.toNat() - 48 < 10` | Fails, as a hypothesis and as a binder. Nothing splits `is_digit`'s tests, since the goal does not mention it. |
| 4 | Taking a branch because the context decides it: `lo <= x, x <= hi ⊢ clamp(x, lo, hi) = x` | `simp_only(clamp::True, clamp::False::True, clamp::False::False, discharge := omega(a, b))` fails: no discharger proves `¬(x < lo)` from word facts. The SHA-256 stream proof writes each such step by hand: `Sha256::push::False(s, fill, byte, λ same => { let n: (fill.toNat() = 63) = cong_fn(λ (x: u64) => x.toNat(), same); omega })`. |
| 5 | A loop's result from an invariant: `tally(start, acc) = acc + (8 - start.toNat())` | Fourteen lines (`bitvec_loop_tests.hthr`): the loop body restated as lambdas three times, `loop_up` and `run_up_invariant` applied by hand, two staging `let`s inside the invariant step. |
| 6 | A loop proved by hand induction over its count: `Sha256::zeroed_block` | A `match n { Zero => …, Succ(m, ih) => … }` over the fuel the rule introduced, each case restating the step. |
| 7 | A `for` loop's invariant: `count_words`'s spec | No rule (`issues/loop-invariant-rules.md`). |

Row 1 is what the README now shows. Rows 2 to 7 are the ones a reader
of a larger program meets on its second page.

## 3. The proposal

Four pieces, in the order I would build them. A and D extend tactics that
exist; B is new surface; C is a policy change that wants Minus's call.

### A. `split_all` follows the program into calls and hypotheses

Three changes to the existing combinator (`crates/elab/src/goal_combinators.rs`):

1. **Nested calls (row 2).** After a split, simplify calls that sit in an
   argument position of a comparison or of another stuck call, not only at
   the head (`issues/case-split-reaches-arguments-of-stuck-calls.md`). In
   `clamp(clamp(x, lo, hi), lo, hi)`, once `x < lo` and `hi < x` are split,
   the inner call is `x`, `lo` or `hi`, and the outer comparison is one the
   split already knows or a new one to split. A comparison is never unfolded
   into its bit-level fold to find a blocker; a goal that would need that is
   reported, not handed on.
2. **Hypotheses (row 3).** Revert into the motive each hypothesis whose type
   mentions a call the split can simplify, and re-introduce it in each case
   at its simplified type, as Lean's `cases` does
   (`issues/split-all-revise-hypotheses.md`). A hypothesis whose test is
   itself the thing to split (`is_digit(c) = True`) is searched for a
   blocker like the goal is. A case where a hypothesis becomes
   `False = True` is closed by the split, as a refuted case is today.
3. **Readable failures.** A leaf that fails reports the case path as the
   source spells it (`x < lo: no; hi < x: no`) and the goal in source
   spelling, never a raw kernel term.

After A: rows 2 and 3 are `split_all; all_goals { bv_omega }`. This
changes what an existing tactic does, so it needs the whole library
elaborated again before it merges, and it is Minus's to merge.

### B. Induction that follows the function: `f::induct` and `induct`

For each recursive function (structural, or `decreases`) whose body the
step-equation generator already reads, generate a functional induction
principle beside `f::step`/`f::done`: one case per branch, each with the
branch's test as a hypothesis and an induction hypothesis at each recursive
call's arguments. For `tally`:

```heather
// generated, not written
theorem tally::induct(motive: (i: u64) → (acc: Nat) → Type,
    step: (i: u64) → (acc: Nat) → i < 8 → motive(i + 1, acc + 1) → motive(i, acc),
    done: (i: u64) → (acc: Nat) → ¬(i < 8) → motive(i, acc)):
    (i: u64) → (acc: Nat) → motive(i, acc)
```

It is proved once, by the same measure recursion as `tally` itself, and the
kernel checks it like any theorem. A `for` loop needs no generated
principle: it is `List::foldl` of a named step, and one library theorem
(`List::foldl_induct`, generalising the accumulator) serves every loop.

The tactic step, written `induct tally(start, acc); all_goals { … }` like
`split_all`'s sugar (or `by induct(…)` as a Heather tactic), does what the
hand proofs do today:

- abstracts the call's arguments in the goal, reverting the hypotheses that
  mention them (`below: start <= 8`), so the motive generalises the
  accumulator without the user restating anything;
- applies `f::induct`, and in each case rewrites the call by that case's
  equation (`f::step`, `f::done`, `f::True`), which the case's hypothesis
  makes unconditional;
- proves each induction hypothesis's premises with the leaf tactic where it
  can, and hands the leaf the specialised hypothesis (`bv_omega` cannot use
  an implication; it can use `tally(i + 1, acc + 1) = acc + 1 + (8 - (i + 1).toNat())`).

Row 5 becomes:

```heather
theorem tally_gains(start: u64, acc: Nat, below: start <= 8): tally(start, acc) = acc + (8 - start.toNat()) {
    induct tally(start, acc); all_goals { bv_omega }
}
```

and rows 6 and 7 the same shape with the invariant as the statement. This is
new surface and a new generated declaration per function, so Minus decides
it. Its cost is the same order as the branch equations' (one theorem per
recursive function, not per branch).

### C. Calls as contracts

Splitting into every callee is right for small functions and wrong for a
program's top level: the case tree multiplies across calls. The modular
alternative is the one `clamp_twice` already uses by hand: prove a fact
about `clamp(x, lo, hi)` once (`clamp_within`) and use it wherever the call
appears.

Proposed: a theorem marked as a function's contract (say `contract theorem
clamp_within(…)`, or a `facts` set as `simp` has sets) is instantiated by
`split_all` and `bv_omega` at every call of that function in the goal and
its hypotheses, with its premises discharged by the leaf; and `split_all`
does not split into a function that has a contract. `clamp_twice` then
needs no named lemma at its call.

The decision for Minus is the default: open every call (white box, today's
`split_all`) and use contracts only where marked, or the reverse. I
recommend white box by default with contracts opt-in, since the small
functions the README and tests show want the white box, and a contract is
something an author chooses to state.

### D. Branches taken by the context

`simp` with a function's branch equations as conditional laws is symbolic
execution; what stops it (row 4) is that no discharger proves a word
comparison or its negation from word facts. Add `bv_omega` as a discharger
(`discharge := bv_omega`), and let `simp_only(f)` on a function with branch
equations mean all of them (`f::True`, `f::False::True`, …) rather than
the unfolded body. The SHA-256 step above becomes
`simp_only(Sha256::push, discharge := bv_omega)`.

This is small, and mostly library (`simp.hthr`'s discharger) plus one
resolution rule in the host's `Resolve`.

## 4. Order and what each needs

| Piece | Rows | Kind | Verification |
|---|---|---|---|
| A | 2, 3 | Existing tactic's behaviour | Whole-library re-elaboration; Minus merges |
| D | 4 | Library discharger, one `simp` resolution rule | `scripts/test --pr`; resolution rule is surface, Minus merges |
| B | 5, 6, 7 | New generated theorem and tactic surface | Whole library (generation runs on every recursive fn); Minus merges |
| C | 2 at scale | Policy and surface | After A and B |

Each lands with probes in `lib/_tests/std/tactic/` covering the four axes
of `docs/testing-generated-terms.md`, and with the library proofs it
shortens converted in a follow-up (SHA-256 stream, `bitvec_loop_tests`,
`Sha256::zeroed_block`), so the measure of success is lines removed from
real proofs, not only new probes.

## 5. Not proposed

- A weakest-precondition tactic for these pure functions. `native-program-logic-design.md`'s
  `Wp` is about machine code; for Heather functions, the function is its own
  semantics, and the branch equations plus induction are the program logic.
- Hiding the generated equations. They stay nameable, so a proof can still
  cite `clamp::True` where it reads better, and they are what the tactics
  above emit.
