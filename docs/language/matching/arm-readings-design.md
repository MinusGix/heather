# A hypothesis has two readings in an arm

Design for `issues/match-eqbind-generalizes-passed-hypotheses.md`
(2026-11-17). **Status: adopted (Minus, 2026-11-17: stage 1, then stage
2). Both are built: stage 1 in §6, stage 2 in §5's "As built".**

It replaces two syntactic exceptions in `generalize::select_refined`:

- **the beside rule** (`passed_beside`,
  `docs/elaborator/goal-motive-synthesis-design.md` §4.7): under
  `match h:` at a computed scrutinee, a hypothesis an arm passes as an
  argument of one call beside `h` is not refined;
- **the takes-an-equation rule** (`takes_equation_about`,
  `issues/match-eqbind-refines-hypothesis-it-is-passed-to.md`): under
  `match h:`, a hypothesis whose type takes an equation about the
  scrutinee is not refined.

Both decide, before any arm is elaborated and by the shape of the source,
that a hypothesis will be wanted as written. Both are right about the
proofs they were written for and wrong one step away from them (§1).

## 0. The rule

> **In an arm of a case split, a hypothesis about the scrutinee can be used
> at either spelling: with the scrutinee as written, or with the arm's
> constructor in its place. The place it is used decides; where nothing
> decides, it is the constructor's.**

Nothing in that sentence mentions calls, argument positions or `h`. A
reader who knows only that `e` *is* `C(x̄)` in the arm for `C(x̄)` would
predict it. The rest of this note is why it is cheap to build, what it
costs, and how far the same idea goes.

Words used below. In the arm for `C(x̄)` of a split on `e`, with
`w: P(e)` in scope before the split:

- the **written reading** of `w` is `w: P(e)`;
- the **refined reading** is `w: P(C(x̄))`.

## 1. What is wrong with deciding by shape

**It guesses before it knows.** Whether an arm wants `w` as written is a
fact about the *type each use of `w` is checked against*. The beside rule
approximates that by "`w` and `h` are arguments of one call somewhere in
some arm". It is decided once for the whole match, so one arm's call
unrefines `w` in every arm, and it is decided from names, so a name that
means something else in the arm misleads it (§6 has one on master).

**The error lands far from the cause.**
`issues/named-match-third-level-kernel-rejects.md`, point 2: the last arm
writes `subst(compiled, linked)`, which passes `compiled` beside `linked`,
so `compiled` is not refined anywhere, and it is `None => absurd(compiled)`
two lines up that fails (`absurd needs both sides of the equation to be
constructor applications`). Nothing at the failing line mentions the call
that caused it.

**The natural proof is refused and the roundabout one accepted.**
`Bisim::of_obs` (`lib/std/itree/coitree.hthr`):

    fn Bisim::of_obs<R>(…, e: CoTree::obs(E, t) = CoTree::obs(E, u)) → Bisim<R>(E, t, u) {
        match h: CoTree::obs(E, u) {
            ORet(r) => BRet(r, prelude::trans(e, h), h),
            …

`BRet` wants `ht: obs(t) = ORet(r)`. Refined, `e` *is* that, and the arm
would be `BRet(r, e, h)`. The beside rule keeps `e` as written because
`trans(e, h)` passes it beside `h`; delete the `trans` and `e` is refined,
write it and it is not. Neither spelling should be an error.

**Equivalent spellings differ.** `lemma(h, w)` is beside; `let p =
lemma2(w); lemma(h, p)` is not; `(lemma(h))(w)` is not; a method call's
receiver is not. The takes-an-equation rule reads `g: (b = False) → A` and
misses `g: Wrapper(b)` whose definition unfolds to the same arrow.

**It is the same defect twice.** The 2026-11-14 round met `False => g(h)`
and added one exception; the 2026-11-16 round met `lemma(…, slot, within,
…)`, `trans(e, h)` and `j(s, …, spare)` and added another. The next
idiom adds a third. The exceptions share one cause, and §3 removes the
cause.

## 2. What other systems do

| System | A hypothesis about a computed scrutinee | Getting the other spelling |
|---|---|---|
| Lean 4, `match h : e with` | Not refined. Hypotheses are generalized only when the discriminant is a free variable; a term is abstracted in the expected type alone. Generalization is abandoned whole if the new motive is ill-typed. | By hand: `h ▸ w`, `rw [h] at w`, `simp [h] at *` |
| Rocq, `destruct e eqn:h` | Not refined unless an occurrence clause names it (`in w`, `in *`). | `rewrite <- h in w`; ssreflect makes the choice explicit, `move: w; case h: e` |
| Agda, `with e in eq` | Refined: every occurrence in the goal and the argument types is abstracted. "Not always type correct and may result in a (sometimes cryptic) type error." `eq` keeps `e` as written. | By hand: `subst`, `rewrite` |
| Heather before #727 | Not refined under `match h:` at a computed scrutinee (Lean's rule) | The convoy written by hand, 204 written motives in the native compiler's proofs |
| Heather since #727 | Refined (Agda's rule), minus the two exceptions | Rely on the exception firing |

Each fixes **one** reading per hypothesis per arm and hands the other to
the author as a transport. That is the fiddly step this project's proofs
should not contain. Lean's `h ▸ w` is the nearest thing to a remedy: an
elaborator that looks at the expected type and at `w`'s type and finds
which way to rewrite. It is still written by the author at every use.

One detail of Lean's implementation is the seed of this design. Its
`match` generalizes by *adding binders* and says: "We do not clear the
generalized variables, but they become inaccessible since they are
shadowed by the pattern variables." Both readings are in scope in the
term; the surface hides one. Heather's lowering does the same
(`Generalize::wrap_arms` binds the refined copy under the hypothesis's own
name, and the outer binder is still there).

The semantic ideal is older: **smart case** (Altenkirch, "The case of the
smart case", 2011; Abel's MiniAgda experiments, 2009). Each branch is
checked under the *definitional* equation scrutinee ≡ pattern, so there
are no two readings to choose between. It needs conversion under
equational assumptions in the kernel, it is known to be undecidable at
higher-order types, and Abel's position was that completeness is what one
gives up. It is not proposed here (§8). The rule of §0 is what smart case
looks like from the surface, delivered by the elaborator, with the kernel
unchanged.

Sources: Lean 4 `src/Lean/Elab/Match.lean` (doc comments on `generalize`
and `withEqs`); the Rocq reference manual, "Reasoning with inductive
types"; the Agda manual, "With-abstraction"; Altenkirch's Shonan 2011
slides and the 2009 agda-list thread "Smart case".

## 3. The design

### 3.1 Both readings are already bound

When a match refines `w`, its motive quantifies the refined copy,
`λ z => (e = z) → Π(w: P(z)). G(z)`, each arm is wrapped in `λ w =>`, and
the eliminator is applied back to the outer `w`. In the arm's context:

    Γ, w: P(e), …        the context before the match   (written reading)
    x̄                     the constructor's fields
    h: e = C(x̄)           under `match h:`
    w: P(C(x̄))            the wrapped binder             (refined reading)

The outer `w` is a variable the arm's term may mention like any other. It
needs no transport and no equation: using it is weakening. So the written
reading costs **nothing** in the kernel's term. It only has to be
reachable from the name.

### 3.2 A name with two readings is resolved by the type it is used at

`Cx` records, for each binder a match wrapped, the binder it was copied
from (a chain under nested matches: innermost refinement first, the
hypothesis as bound last).

- **Checking position**, `w` against `T`: the innermost reading whose type
  converts with `T`. This is a decided conversion per candidate, run only
  for a name that has two readings and only when its innermost type is not
  syntactically `T`. No other checking site pays anything
  (`MismatchNotes`' rule, recording is not probing, stands).
- **Argument of a call whose implicits are still open**: the refined
  reading teaches the implicits, as any inferred argument does, and
  stands unless its type clashes with an implicit already solved. Then
  another reading takes its place if it settles the parameter's type and
  converts with it. Where the parameter's type is already known,
  conversion decides, as in checking position. (Not built: if an argument
  with no second reading clashes with an implicit a refined reading
  taught, elaborate the application once more with every two-reading name
  as written. The library has no such call.)
- **Inference position** (`absurd(same)`, a `let` without a type, a
  receiver): the refined reading. It is the informative one, and it is
  what the plain `match` gives.
- If no reading fits, the mismatch is reported **at the use**, with both
  types: "`w` has type `P(C)` here (`P(e)` as written), but `T` is
  expected".

### 3.3 `h` has two readings too

`h: e = C(x̄)` is itself a hypothesis about the scrutinee. Its refined
reading is `C(x̄) = C(x̄)`, and that one has a canonical inhabitant,
`refl`. So `h` checked against a type of that shape elaborates to `refl`.
Its default reading is the written one: the refined one says nothing.

This is what makes the readings *closed under calls*. If a callee takes
the equation and a hypothesis, both arguments can be read refined
together or written together:

| Arm, as the author wrote it | Elaborates as |
|---|---|
| `False => g(h)`, `g: (b = False) → A` | both as written (§3.4), so the term is today's; `g` refined with `h` as `refl` also types |
| `InSlot => t.goes_word_to_slot(…, slot, within, …)` | no implicit is open, so each argument is checked at the callee's parameter type: `slot` and `within` as written |
| `ORet(r) => BRet(r, prelude::trans(e, h), h)` | `trans`'s ends are known from `BRet`: `e` refined is `obs(t) = ORet(r)`, `h` against `ORet(r) = ORet(r)` is `refl` |
| `ORet(r) => BRet(r, e, h)` | `e` refined. The proof the beside rule could not accept next to the one above |
| `j(s, λ b _ => …, spare)` | `spare` is checked at the written motive's instance: written |
| `Some(whole) => … subst(compiled, linked) …` and `None => absurd(compiled)` | each use on its own: `absurd` infers, so `compiled` is refined there whatever the other arm writes; in `subst` it is refined too, and `linked` takes the reading `subst`'s motive asks for |

No row consults the shape of another row. That is the whole claim.

### 3.4 What is generalized: a hypothesis whose refined reading is used

Today's selection is by name: a hypothesis about the scrutinee is
generalized if some arm's source mentions its name or the goal mentions
it (`select_refined`). With two readings the right criterion is by use:

> A hypothesis is generalized into the motive when the goal mentions it,
> or when an arm **uses its refined reading**.

The name scan stays as the first guess (it is a sizing decision, as
`generalize.rs`'s module doc says of `varying_params`). After the arms
are elaborated, a hypothesis that was generalized on the guess and whose
refined reading no arm used is dropped, and the match is lowered once
more without it. So the kernel's term does not carry a `Π` nothing reads,
and a `match` in a function body stays the term it was when it only ever
passed its hypotheses along as written: `fn pick`'s `match h: b { True =>
f(h), False => g(h) }` keeps `f` and `g` out of the motive when the
written readings check, which is what `unify-through-match-arms` and the
`f_unfold` walk rely on. The second lowering happens only where the guess
was wrong, which today is exactly where one of the two exceptions fires
(§6 has the count).

For that to select the written readings of `g(h)` first, a call whose
head is a refined hypothesis and whose every argument is the equation or
a refined hypothesis, the equation among them, is tried as written before
refined (`Readings::as_written`). One sentence covers it: *a call that
hands the equation to facts about the scrutinee is taken as written if it
checks as written.* It is the single place the order is not "refined
first", and it exists for the term's sake, not for typing: both orders
type.

**As built, and narrower than the sentence above.** The second lowering
happens only at a match with an equation, and never where an arm calls
the declaration being elaborated. The first version applied it to every
match and changed a recursive `fn`'s term: `walk_expect`
(`lib/_tests/std/analysis/continuous_time_tests.hthr`) stopped unfolding
at `Succ(m)` by `refl`. A recursion's match generalizes its parameters
for its calls as well as for its arms' names, and a name count does not
see that. Nothing wants the written reading at a plain match anyway
(§3.6), so the narrowing loses nothing known. Why the wider version broke
that function in particular (the same shape over `Nat` was unharmed) was
not run to ground, and is the first thing to understand before widening
it.

### 3.5 A hypothesis that cannot be refined says so where it is used

A refined reading can fail to exist: the abstraction is ill-typed
(`goal-motive-synthesis-design.md` §4.6; Agda's "cryptic type error";
Lean abandons the generalization). Today that is silent: the match falls
back, the hypothesis stays as written, and some arm fails later for a
reason it does not state.

With readings in `Cx` the outcome is recorded per hypothesis. A use that
fails at the written reading of such a hypothesis is reported with the
reason: "`same` is read as written here: this match cannot refine it,
because abstracting `fits(w)` leaves `h: z = True` where `fits(w) = True`
is expected". That is the issue's third "done when".

**As built.** Three things are said, each where the reader is looking:

- A use that neither reading fits names both: "this has type `Some(Cons(w,
  p)) = Some(c)`, but `… = None` is expected here; in this arm `same` is
  also `emits(Leaf(w), p) = Some(c)` (with the match's test as written),
  which is not what is expected here either" (`Readings::refusal_note`,
  read by the mismatch note's probe, so it costs nothing on a declaration
  that checks).
- A hypothesis read through a call whose abstraction is ill-formed
  (`matching::hypothesis_through_calls` answers `NotRead::IllFormed`) is
  recorded as `ReadingKind::Kept`, and an arm's refusal at a use of it
  ends "the match around this could not read `same` at its case, because
  taking the match's test out of its type leaves something ill-typed, so
  `same` has its type as written here". This holds at a plain `match` as
  well. It does not print the ill-typed motive: the sentence says which
  hypothesis and which match, not which subterm.
- A goal left open in an arm lists a refined hypothesis as `same :
  Some(Cons(w, p)) = Some(c)   (or as written: emits(Leaf(w), p) =
  Some(c))`, and a match with a hole in an arm keeps every hypothesis it
  refined, since what fills the hole may want any of them.

Not covered: a hypothesis left as written for a reason other than an
ill-formed abstraction (its type is stuck on something other than the
test, §4.7's `kept_or`) gets no note.

### 3.6 The same rule for every match

Nothing in §3.1 and §3.2 needs `h`. A plain `match e` and a match on a
variable wrap their arms the same way and leave the outer binder in
scope, so the written reading is reachable there too. It is rarely
wanted there (a result stated as written cannot be brought to the arm's
refined goal without the equation), and it is never chosen when the
refined reading fits, so nothing that checks today changes. The point is
that the rule has no "under `match h:` at a computed scrutinee" clause.
Only §3.3 is specific to the named form, because only there is there an
`h`.

Parameters a structural recursion generalizes (`varying_params`) are not
readings: the arm's `m` is a different value from the outer one. Only
positions `refined_hypotheses` adds have a written reading.

## 4. Guarantees

Stated so that a sweep can check them and a later change can be held to
them.

1. **Conservative over "refine nothing".** An arm that checks with every
   hypothesis as written (the behaviour before #727, and Lean's) checks:
   the written reading always exists, and every use that states its type
   finds it. The exception is a use that states no type and is constrained
   later (`let p = w; lemma(h, p)`): `p` is refined. §5 closes that.
2. **Conservative over "refine what a plain match refines".** An arm that
   checks under the plain `match`'s refinement checks under `match h:`,
   `h` unused.
3. **Local.** Which reading a use gets depends on that use's expected
   type, and on nothing in another arm or another statement.
4. **The term is canonical.** The motive generalizes exactly the
   hypotheses the goal mentions or an arm uses refined.
5. **Refusals are at the use**, with both readings shown and, where there
   is only one, why.

## 5. Stage 2: the arm's equation as a coercion

Stage 1 gives a hypothesis *name* two readings. The same sentence is true
of any term in the arm: a call's result stated about `e` where the arm's
goal is about `C(x̄)`, or a `let`-bound fact. There the other reading is
not already bound, and it is produced by transport along `h`.

At the checking fallback (where `Tested::coerce` already turns a
`When<T, P>` into its `T`), with `t: T_got` against `T_exp` inside an arm
whose match has an equation:

1. Prefilter, syntactic and linear: `e` occurs in one of the two types
   and they are not syntactically equal. Otherwise nothing runs.
2. Abstract `e` in `T_exp` to `M`. If `M(C(x̄))` converts with `T_got`, the
   term is `subst(sym(h), t)`.
3. Else abstract `e` in `T_got` to `M'`. If `M'(C(x̄))` converts with
   `T_exp`, the term is `subst(h, t)`.
4. Under nested matches, innermost equation first.

This is Lean's `h ▸ t`, with the `h` found by the elaborator because the
arm has exactly one candidate per enclosing match.

What it buys beyond stage 1:

- **Motive synthesis becomes monotone.** §4.5 of the motive design
  records three library proofs that broke when a new rung specialised a
  goal they had proved as written, found only after merge. With the
  coercion, an arm that produces the goal as written is accepted at the
  specialised goal, so *a rung that finds more can no longer break a
  proof*. Every later improvement to the ladder (cumulative rungs,
  `case-split-reaches-arguments-of-stuck-calls`) stops needing a library
  rewrite to land.
- Guarantee 1 loses its exception.
- A mixed spelling, `P(e, C(x̄))`, is neither reading of `w` and is
  reached by one transport.

A plain `match` has no `h`, but it has the pending equation of
`dependent-match-compiler-design.md` §4: in scope always, paid for when
read. The coercion is one more reader. A plain match whose arm needs the
transport is retried as a convoy, as `omega` already makes it do.

Stage 2 is a separate change with its own sweep. It inserts `subst` terms
where there was a refusal before, so it cannot change a term that checks
today.

### 5.1 As built

`Readings::coerce` (`crates/elab/src/readings.rs`), called at the checking
form's last resort, after inference and after `Tested::coerce`.

- **Only a decided disagreement.** The two types are compared once, and
  only an answer of "not convertible" goes on; convertible or out of fuel
  leaves the term exactly as it was. The comparison runs only when an
  enclosing match's test is spelled in one of the two types, which is a
  syntactic scan. So a declaration that checked before stage 2 has the
  term it had.
- **The transport is a `J` written out**, as `rewrite` writes its own, so
  it needs no library: forward along `h` when the term's type spells the
  test, and along `sym(h)` (itself a `J`) when the expected type does.
  The motive is the type with the test abstracted, checked well-formed
  (`motive_well_formed`) before it is used.
- **Every match with an equation records it**, not only one that
  generalized a hypothesis (stage 1 registered the equation's `refl`
  reading inside the generalizing path only).
- **A plain `match`** hands its arms its test beside the pending
  equation's identity (`Cx::pending_tests`). A term that would be carried
  marks the match (`match_eq_carried`) and the arm goes on unchanged. Once
  the arms are done, a marked match is elaborated again as its convoy with
  the equation registered; that version stands if it elaborates. If it
  does not, the match is elaborated a third time with its test out of
  sight, which is the match as it was before stage 2, error and all. The
  mark is not an error on purpose: the first version raised the mismatch
  at the use, and a recursion's own refusal (`argument n has to be _`)
  was replaced by a worse one wherever the convoy failed too.
- **Cost shape.** Nothing on a declaration whose types convert. On one
  with a decided mismatch that spells a test, each marked plain match is
  elaborated two or three times, so nesting multiplies: the worst case is
  exponential in the depth of marked matches, and it is reached only by a
  declaration that is being refused.

What the first sweep showed (every `lib/**/*.hthr`, fresh cache): no
library proof changed, and three probes that pinned a refusal check.

- `walk_shape` (`recursion_case_split_tests.hthr`,
  `issues/recursion-case-split-dependent-ih.md`): a recursive call's
  result, stated at the split parameter `n`, where the arm's goal is at
  `Zero`. The issue's log had named the fix as "a match refinement, not a
  recursion one".
- `wild_under_deep` (`wildcard_arm_tests.hthr`): a `_` arm whose
  scrutinee is not rebound.
- `loose_or` (`match_refines_through_calls_tests.hthr`): a record value
  at the record as written, where the motive read inside it.

Not built, and where it would go:

- **One site only.** The dot-call and projection branches of the checking
  form record their mismatch without asking (`note_check_mismatch` at five
  sites in `checking.rs`), and so do literals. A method call's result
  that needs carrying is not carried.
- **Arguments the application engine infers** before the parameter's type
  is settled are compared there (`argument_type_converts`), not at the
  checking form.
- **One equation per term.** A type that needs two enclosing matches'
  equations at once is not reached; innermost first, the first that
  closes the gap wins.

## 6. Census, and the prototype

**Census.** `select_refined` instrumented on master `fde9b6fa`, every
library module re-elaborated (2026-11-17). Under `match h:`, a hypothesis
about the scrutinee that an arm names is a candidate for refinement at 61
sites. At 16 of them an exception leaves it as written:

| | computed scrutinee | variable scrutinee |
|---|---|---|
| refined | 43 | 2 |
| beside rule | 6 | (not applied) |
| takes-an-equation rule | 6 | 4 |

Thirteen of the sixteen are in `lib/_tests`, most of them probes written
to pin the exceptions. The library proper has three: `Bisim::of_obs`'s `e`
(§1) and two in `lib/std/parser/parser.hthr` (`right_bound` and
`right_law`, beside `shape`). The idioms #727's sweep
named (`goes_word_to_slot`, `j(s, …, spare)`) do not appear: their
hypotheses are not about the scrutinee by occurrence, so no rule touches
them. The exceptions guard few sites, and they cost every other site
their unpredictability.

**The same sweep found a defect of the current rule.**
`lib/_tests/std/core/branch_equations_tests.hthr` is refused on master
when re-elaborated (the PR lane replays it). `first_seen`'s generated
branch equation takes a hypothesis `got: first_of(xs) = None` and matches
`match got: first_of(xs)`. The arm's `got` is the equation, but the name
scan sees `got` in the arm, takes it for the hypothesis and refines it,
and the refined copy shadows the equation. A hypothesis named like the
equation cannot be named by an arm; the prototype says so in
`select_refined`.

**Prototype** (this branch, `crates/elab/src/readings.rs`): §3.1 to §3.4
as written, both exceptions deleted, with §3.5's messages as its "As
built" paragraph describes. `Cx::readings`
records each refined copy's outer binder and the equation's name; the
checking form and the application engine's inferred-argument branch ask
it; a match with an equation is lowered a second time when a hypothesis
it generalized was never used refined.

- `lib/_tests/std/core/match_readings_tests.hthr` checks: each row of
  §3.3, both spellings of §1's pairs (`chain_by_trans` and
  `chain_refined`, `beside_written` and `beside_and_refined`), both
  readings of one hypothesis in one arm, a hypothesis refined by two
  nested splits used at its outermost spelling, and a refusal where
  neither reading fits.
- The probes that pinned the exceptions check unchanged: `pick_by` with
  `pick_by_true` by `refl`, the `taken_*` family, `passed_h`,
  `passed_beside`, `Bisim::of_obs`.
- **The whole library re-elaborated with no proof changed** at §3.1 to
  §3.3 (fresh
  cache, no stale images, every `lib/**/*.hthr`): one file fails, and it
  is the file that fails the same way on master
  (`constructor_equation_tests.hthr`, an expectation that no longer
  matches its refusal). `branch_equations_tests.hthr`, which master
  refuses, checks. The first sweep found one regression, in the
  application engine's use of the readings: with implicits still open,
  "the unifier reported no clash" is not "this reading fits", and
  `BinaryOp::bit_written`'s `cong_fn(extended, holds)` was handed the
  written `holds`. The rule that came out of it is in §3.2: the name as
  it elaborated stands unless it clashes with a solved implicit, and
  another reading replaces it only if it settles the parameter's type at
  its own.

- `scripts/test --pr` at §3.1 to §3.3 found what §3.4 is for:
  `goal_combinators::splits_a_convoy_whose_arm_uses_its_equation` proves
  a fact about `fn pick`'s `match h: is_zero(n) { True => d, False =>
  k(h) }` by `split_all`, and with `k` generalized and `h` read as `refl`
  the split's leaves no longer had the shape its lemma states. §3.4 was
  built for it, and the test passes.
- With §3.4 in: the whole library re-elaborates with no proof changed
  (the same one inherited failure), and `scripts/test --pr` has one
  failure, the library gate on that same file.
- Merged with master after `cases h` (#748) landed there: master's
  `passed_beside`, `takes_equation_about` and `Refined::explain` are
  removed, master's probe `beside_told` (one arm passes the hypothesis
  beside the equation, another needs it refined), which pinned the
  refusal, checks, and `cases h` needed no change: it emits an ordinary
  `match e: test`. Every library file re-elaborates and the PR lane is
  green; master had fixed the inherited failure by then.

## 7. What it costs, and what could go wrong

- **Elaboration cost.** A conversion per candidate reading, at uses of
  two-reading names whose type is not syntactically the expected one. A
  second lowering of a match whose guess over-generalized. Both are on
  paths the two exceptions occupy today; no hot path gains a probe.
- **An application elaborated twice on a clash.** Bounded at two, and
  only for applications that used a refined reading.
- **`refl` for `h`** needs the expected type's two sides to convert.
  One conversion, at uses of `h` whose written type did not fit.
- **Ambiguity is benign.** Where both readings fit, the two terms are
  propositionally equal by `h` and the choice changes no typing
  downstream at that site; the order (refined first, §3.4's one
  exception) makes it deterministic.
- **Display.** A goal report shows a hypothesis at its refined reading
  with the written one beside it when they differ. Without that the rule
  is invisible exactly when it matters.
- **Risk: generated consumers of a match's shape.** The `decreases`
  rewrite, `f::step`/`f::done`, the runtime reflector (`Tm::convoy`'s
  shape) read lowered matches. §3.4 keeps a match that passes its
  hypotheses as written at the term it has today, so they should see no
  change; the sweep is the check.
- **Risk: the inference default flips a proof.** A proof that relied on
  the beside rule in a position with no expected type would now read
  refined. Guarantee 1's exception is the same case. The census says how
  many exist.

## 8. Alternatives

- **Keep adding exceptions.** §1.
- **Lean's rule** (refine nothing under `match h:`): brings back the
  hand-written convoys #727 removed.
- **Agda's rule** (refine everything, transport by hand): the three
  idioms become `subst(sym(h), …)` at every such argument, and the
  transport's motive is the callee's parameter type restated.
- **Say it in the syntax**, `match h: e generalizing w` or ssreflect's
  `move: w`: predictable, and it asks the author for what the types
  already say. It could exist later as an override, like a written
  motive.
- **No generalization under `match h:`, every refined reading a
  transport along `h`.** The motive becomes `(e = z) → G(z)` with no
  selection at all, which is attractive. It loses on hypotheses that
  depend on one another (`w₂: Q(w₁, e)` needs a transport over the pair,
  where a `Π` telescope is just longer), and it puts a `subst` in terms
  that have none today.
- **Smart case in the kernel.** The real thing. It is a change to
  conversion in the trusted base, undecidable in general, and the
  opposite of `small-trusted-kernel-study`'s direction. The surface rule
  here would stay true if it ever came, and the elaborator's work would
  shrink to nothing.

## 9. Decisions for Minus

Decided 2026-11-17: adopt the rule, stage 1 then stage 2 (items 1 and 4).
Items 2 and 3 are built as proposed; item 5 holds for `cases h` already
and is open for `split_all`.

1. **The rule of §0** as the surface contract for case splits, replacing
   both exceptions.
2. **Refined in inference position** (§3.2). The alternative, written in
   inference position, is Lean's behaviour with opt-in refinement and
   breaks `absurd(same)`.
3. **§3.4's use-based selection** with its one ordering exception, or
   accept a `Π` nothing reads and no exception.
4. **Stage 2** in this thread after stage 1, or filed.
5. `split_all`'s `Cases` and the `cases h` tactic
   (`issues/split-all-revise-hypotheses.md`, the case-split thread)
   should register the same readings in `Cx`, so a tactic's arm and a
   written arm obey one rule. Proposed as the follow-up that makes this
   one mechanism and not two.

## 10. Slices

1. Readings in `Cx`; resolution at the checking fallback and in the
   application engine; `h` as `refl`; delete `passed_beside` and
   `takes_equation_about`. Probes in
   `lib/_tests/std/core/match_readings_tests.hthr`: each row of §3.3's
   table, both of §1's pairs, the nested chain, and refusals with their
   messages. Whole-library sweep.
2. Use-based selection (§3.4) and the per-hypothesis refusal note (§3.5).
3. Display of both readings.

   Slices 1 to 3 are built. Left from them: the spill and deferred
   argument branches of the application engine do not ask the readings
   (only the declared-spine inferred-argument branch does), and §3.4's
   second lowering is not applied at a plain `match` (its "As built").
4. Stage 2 (§5), with its sweep; then delete the proofs' remaining
   hand transports where the sweep's review lint finds them. Built
   (§5.1) except the lint, which does not exist: nothing yet finds a
   hand transport that has become redundant.
