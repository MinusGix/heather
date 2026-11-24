# Proof patterns: what costs, and what the language wants

The rules rounds kept rediscovering, checked against master on 2026-10-29
([[proof-patterns-audit-2026-10]] in issues/ has the probes and what was
retired). Each rule says why, so it can be dropped when the reason goes.
A rule that names an open issue is a workaround for that issue, not a
property of Heather.

What a proof costs is this document; how definitions, data and proofs
should read is `docs/library/program-and-proof-style.md`.

## 1. Closed facts: evaluate once, in the kernel

- **A closed verdict is evaluated once, by the kernel, in any of its three
  spellings**: `b = True` by `refl`, `b.IsTrue()` by `trivial`, or
  `b.IsTrue()` by `decide`. `trivial` reads its expected type only within a
  small step budget and leaves a verdict past it to the gate; `decide`'s
  application no longer reduces the goal once its `P` is solved. A false
  verdict is still reported at the `trivial` or `decide` that claimed it,
  the elaborator reducing it only after the gate refused
  ([[closed-verdict-evaluated-twice]], closed; the probes are
  `lib/_tests/std/core/closed_verdict_tests.hthr`). The kernel's cost is
  the same for all three since it compares a verdict's type in one run
  ([[type-conversion-one-sided-delta-steps]]); before that, the `IsTrue`
  spellings cost several times the `= True` one.
- **One equation per computed value.** Each `refl` is a conversion of its
  own, and nothing one computes is kept for the next: three equations about
  the three fields of one computed record evaluate it three times. State
  one equation about a record of the parts and project in a lemma
  (`EmitsAs` and `Emitted::emits_as`, `function_ir_compile.hthr`).
- **Never compare two separately computed values by `refl`.** Conversion
  unfolds both sides in lockstep, a δ-step on each side per step. Small
  lists cost about three single evaluations; an allocation's `Homes = Homes`
  ran out of memory, and whole `MachineState` equalities run out of fuel.
  Decide equality with a Bool function and state `same(a, b) = True`.
- **A computed value is shared only by closure identity.** Two textual
  copies are two evaluations, and so are two reads of one `let`: the
  elaborator puts the value wherever the name is read
  ([[elaborated-let-sharing-lost]]; a planner that read its `let`s twice
  per level of nesting was the memory of
  [[compile-x86-certificate-memory]]). What is computed once is an
  argument: pass the value to a function (`shared(v, λ x => …)`,
  `nat_map.hthr`, or a helper taking it as a parameter), hold it in a
  record field a constructor computes (`Layout::of` holds the leaf pool),
  or put `Option::some_get` around a compile. In evaluated Nat code write
  `q * 2`, not `q + q`.
- **Decide a number equality with `same` or `eq_dec`; `equation` is for a
  transport that has to compute.** `Nat::equation` builds its `refl` a
  successor at a time, at two literals too, and a checker that asks it
  about a width pays the width at every ask (the type-code checks of
  [[native-function-emission-in-parts]]). `eq_dec` decides by `same`,
  which the kernel runs over both numbers at once, and reads its proof off
  `same_sound`. Making `equation` itself decide by `same` first was tried
  and cost a proof over open terms a quarter more steps.
- **Never run a loop at a constant fuel by conversion.** It runs out of
  fuel. Instantiate a generic lemma whose statement is syntactic instead.
- **Prove at a neutral parameter, instantiate at the literal.** A lookup at
  a literal width converts in lockstep (about 10k steps) where the same
  lemma at a variable width costs about 130. Stretches over an abstract
  label are elaborated once and cited with `refl` at each use.
- **Read a compiler's promise off at an abstract output.** Projecting a
  soundness conclusion (`Tm::LowerHolds(t, …, Tm::lower(t, …))(…).right`)
  makes the elaborator spell the computed output inside the conclusion's
  type, and that grows with the program: `wc_step`'s did not finish. A
  lemma taking `r: Option<Lowered>` and the promise at `r`, matching on `r`
  and projecting there, costs what the abstract proof costs; the
  instance passes `Tm::lower(t, …)` for `r` and lets the kernel evaluate it
  once (`wc_step_lowered`, lib/_tests/native/runtime/rt_lower_tests.hthr).

## 2. Statements and proof shape

- **Split a long proof into stage theorems with written statements.** One
  theorem composing stages inline took 80 s and once ran out of memory; the
  same stages as five theorems took 0.2 s each. A proof whose state λ holds
  many lets makes every later let dearer (388 s, split to 27 s + 12 s).
- **Annotate a λ binder you match on when the expected type is computed.**
  The annotation is what the binder gets; unannotated, it gets the computed
  domain and the match spells its unfolding (20–170× kernel steps).
- **Put case analysis of a trace or other inductive in a small lemma over
  its own type**, not inside a recursion or under a computed binder.
- **Membership over sets with decidable membership is `by sets()`**
  (`lib/std/tactic/set_tactic.hthr`), not a chain of `mem_append_l`,
  `union_right`, `mem_filter_of`, `union_has`, `Bool::is_true_and`
  citations: the goal and the membership (`Mem`, `s.has(x) = True`,
  `.IsTrue()`, `¬`, `!`), `=`, `≠`, inclusion and spelled
  (`absent(x, s).IsTrue()`, `holds`) hypotheses about its element become a
  truth table that the kernel checks by evaluation; `∧` and records of such
  facts split. Any carrier with a `DecSet` instance is read (lists, `Span`,
  `SpanSet`, a client's own), its operations through their `SetUnion`,
  `SetInter`, `SetMinus`, `SetInsert`, `SetFilter` instances
  (`lib/std/data/set/dec_set.hthr`); a client imports `dec_set` beside
  `set_tactic`, as instances come from direct imports. Relations between sets
  (`a.within(b)`, `disjoint(xs, ys)`) are read too: a hypothesis at the
  element, a goal `= True` by its intro law, `= False` by an element on the
  wrong side; so are equations between elements and their spellings
  (`x.same(y)`, `a.matches(b)`), and equations between two memberships of one
  element (`(a ++ b).has(x) = (b ++ a).has(x)`). A new carrier or operation
  declares its instance; a Boolean spelling of list membership that is not
  a carrier's `has` registers a `SetBitEntry` with its `SetBitLaw`, a new
  relation a `SetRelEntry` with its elim and intro laws, an equality
  spelling a `SetEqEntry` with its `SetEqLaw`, beside its definition. Each
  atom, element and predicate doubles the table, so keep a big literal
  behind a name. A call costs a few tenths of a second, mostly the tactic's
  own run; a one-step citation is cheaper.
- **A chain of rewrites by known laws is `simp_only(l₁, …, lₙ)`**
  (`docs/tactics/simp-design.md` §10), not a `calc` with one law per line or nested
  `rewrite`s: both sides are normalised by the listed laws, along `=` and
  along a designated `≈`, and the goal closes where they meet. The list is
  the whole set, so the proof does not move when a lemma is added elsewhere.
  Induction hypotheses go in the list (`a.simplify_same()`); a call at a
  constructor computes first, so a definition's own equations are not
  listed. At a goal about a common carrier, `by simp()` brings the default
  sets of the types in it (`List::shape`, `Nat::arith`, `Regex::same`:
  `lib/std/tactic/simp_laws.hthr`), with `extra := [h]` for the call's own
  laws; a new carrier registers a `SimpSet` beside its lemmas. In `lib/`
  prefer the pinned list. `then := e` proves what is left, `using := h` closes from a fact
  with the same normal form, `discharge := e` proves side conditions the
  scope does not hold. Write `simp_show(…)` to read the normal form and the
  route, then replace it: it never closes a goal. A refusal lists each step
  as `law: lhs ⟶ rhs` and the laws blocked with their unmet condition;
  read that before adding a law. A law may be `P ↔ Q` between statements
  (`List::mem_append_iff`): it rewrites the goal, an operand of `∧`, `∨`,
  `↔`, `¬`, `→`, and the body of a `∀`, and equations reach those places
  too (§12 of the design), as do instances below an `∃`. An instance under
  a λ handed to a function fires when that function has pointwise evidence
  (`list_pointwise` for `map`, `filter`, `count`; §13): there is no funext,
  so a new higher-order function states its own `_ext` lemma and
  `evidence theorem`. Not reached yet:
  a goal a named `match h: test` left unfolded past its `≈`, which is
  restated in a one-step `calc` ([[case-split-unfolds-the-goals-relation]]).
- **A record is its fields rebuilt, by conversion: write no `T::eta`.**
  `R(r.a, r.b) = r` is `refl` for a neutral `r`, at an open type
  parameter, a dependent or function-valued field, a receiver headed by a
  call, and in any type that mentions either side: a record lowers to the
  Σ spine of its tag, fields and `Unit` (`docs/inductives/inductive-tier0-lowering.md`
  §3), and the kernel has η at all three. A `match r { R(_, _) => refl }`
  lemma, or a `cong_fn` that only rebuilds a record, is a step to delete
  (`lib/_tests/lang/record_eta_tests.hthr`). The same η makes a state
  record a fine induction variable: quantify over the record, not over its
  fields.
- **State lemmas in the goal's spelling.** `x - y` against `x + -y` makes
  `rewrite` and generic-lemma matching convert, or fail before instance
  search (`hi + -lo`, not `hi - lo`, for a generic lemma at `Rat`).
- **Name one object by one spelling throughout a statement a generated
  instance is checked against.** A class or builder that says `w.tys` in one
  place and `w.over(cs, b).tys` in another states the same table twice, one
  projection apart, and by hand nobody pays for it. A generator's instance
  is gated at its literal spelled out in full, and there the kernel, missing
  on the respelled argument, compares the literal's reductions beside it: the
  cost climbed as a high power of a shift count in the reflection until it
  ran out of fuel. Give the object one function (`World::at(w, callees, b)`)
  and reach every part of it through that, its projections included
  ([[conversion-respelled-world-compares-reflection]]).
- **State a word fact modulo `2^n`; add a bound only to read the value as a
  Nat.** Every word operation is `ofNat` of the Nat one at every width
  (`BitVec::add_eq_ofNat`, `ofNat_add`, `toNat_add_mod`, `bitvec_nat`), and
  a word identity is `ring`'s at `BitVec(n)` (`import bitvec_ring;`, with
  `int` imported for its coefficients), `-` included: a carrier whose `-` is
  an operation of its own names the law with a `SubtractionLaw` instance
  ([[ring-carrier-subtraction-law]]). A `fits` premise threaded only to a
  no-overflow lemma whose modular form would do is a premise too many: a
  word equation needs none (`BitVec::zero_iterate_increment`,
  `word_of_nat_eq_ofNat`, `BitVec::ofNat_add_of`, `Target::at_rip`); a
  `toNat` reading, a sign or zero test and a canonical-address bound do.

## 3. omega

- **Give it what it cannot read yet.** A Nat `a - b` is split into its two
  cases, so no `Nat::sub_add_cancel` beside the call
  ([[omega-nat-truncated-subtraction]]). An `Exists`'s `.proof` is read as
  its contractum (`omega(e.proof)`), with no restating `have`; so is a
  pattern-bound fact by `linarith`/`nlinarith`. A Bool guard
  (`F.canonical(m, b).IsTrue()`, a record's `ok` field) is read by its
  `&&`/`||`/`!`/`leb` structure, through a Bool definition's `let`s, so
  `omega(g.ok)` replaces an `is_true_and`/`leb_sound` chain or an `_elim`
  whose conjuncts only feed omega ([[omega-reads-bool-guards]]); a stuck
  `match` inside the guard is still not read.
- **Bind no `refl` to open a term for it.** `omega` computes a closed call
  to its numeral (`zero.toNat()`), opens `a * Succ(b)` to `a * b + a`,
  names a call at the fields of an argument that computes to a
  constructor (`Sha2::ending(z, l).len()` is `Succ` of its tail's length,
  `spelled(Cons(w, rest)).len()` four successors of `spelled(rest).len()`),
  follows a definition to its arithmetic (`x.doubled(0)` is `x`, a fold
  over `[b0, b1, b2, b3]` the sum it builds; a non-recursive one whose body
  is arithmetic at open arguments too: a defined distance `dist(a, b) =
  (b + 4 - a) % 4` is its body, subtraction split and all, design §26),
  and states every word's range
  `w.toNat() < 2^n` at a literal width, met in the goal or only in a fact,
  so no `toNat_lt_pow` beside a `bv_omega` either
  ([[omega-opens-closed-terms]], design §22). Each opening is bounded; a
  term a bound stopped is listed after the residual as `left as atoms by a
  bound [...]`, and that is the term to state if a fact is still needed.
- **Over records and layouts at a literal program, prefer Nat step lemmas**
  (`Nat::le_trans`, `add_le_mono_l`) or a generic lemma over Nat variables.
  The kernel converts the atoms' definitions. omega does read a field at
  closed arguments as what was put there (`Lay::of(3).size` meets
  `Lay::of(3).cap`), so a failure there is a missing fact, not an atom.
- **It reads every hypothesis in scope**, and each atom a fact brings
  widens every row of the certificate. A written `omega`'s proof is lifted
  into a lemma of its own at the gate (design §27), so an inline call is no
  longer substituted with the body under every binder: that halved or
  better the word map's proofs with `omega` in deep contexts. What still costs is the
  certificate's width: a context with many unrelated facts over the same
  atoms, or `Rat` facts (unfolded into Int cross products), still pays for
  them. And the truncated-subtraction split (design §16) takes facts
  newest first, at most six deep: in a context holding many distances an
  inline call can spend them on unrelated facts and get stuck where the
  same facts as a lemma close. Measured on the word map, a remainder step
  inline cost more than its lemma and the call together: state it as a
  lemma over bare numbers, as `step_before_back` and `moved_clear` in
  `word_map_laws.hthr` are. `omega(h, …)` names the load-bearing facts (an `Exists`'s
  `.proof` is read only when named); whether it should read *only* those is
  [[omega-listed-facts-only]], an open decision.
- **Remainders by a literal with subtractions inside are its costly
  shape.** `(s + 4 - j) % 4` is a subtraction split under a quotient atom,
  and the real shadow fails on integrality, so each leaf is a CutSat case
  analysis: a lemma about slot distances costs seconds even over bare
  numbers. Name a fact once and cite it rather than re-deriving it.
- **No hand proof for a word under a low mask.** `bv_omega` reads
  `x & (2^k - 1)` as `toNat(x) % 2^k`, and a masked sum or difference
  through its wrap (`(j - i) & 3` is `(j + 4 - i) % 4` for slots below
  four, borrow and all), so no `toNat_band_low_mask` or
  `toNat_sub_mod`/`mod_pow_mod` chain (bv-omega-design §3.2).
- **Products of `pow` terms: restate the step over variables.** `omega`
  over `Nat` facts whose atoms are `m * pow(2, …)` products re-reads their
  structure; the same facts handed to a lemma over bare `Nat`/`Int`
  variables cost a hundredth (`eft.hthr`'s `vk_kt_arith`, `vk_kn_arith`:
  `vk_bound` went from twenty seconds to a third of one).
- **Annotate a `let` with the type its term has.** An annotation that
  differs from it by a computation (`(h * Q).int() <= g.H()` for a term at
  `(F.down(h * Q)).H() <= g.H()`) makes the checker evaluate the
  computation to compare them, which can run out of memory; annotate the
  term's own type and convert with `omega` and the equation.
- **It needs a checking position:** `let k: (T) = omega(…);`. Where
  nothing is expected the refusal says so (as for `ring`, `linarith`,
  `nlinarith`, `bv_omega`, `positivity`;
  [[checking-tactic-in-inference-position-diagnostic]], closed).
- **A Boolean identity is two `omega`s.** `Bool::eq_of_is_true_iff(a, b,
  λ h => omega(h), λ h => omega(h))` proves `a = b` for Booleans built
  from `&&`/`||`/`!`/`leb`/`same` and atoms: the guard rounds are a truth
  table over the atoms. An applied record field (`nb.number(a)`) does not
  spell yet ([[omega-applied-field-atom]]), nor does a field of a call that
  unfolds to a record ([[omega-field-of-record-valued-call]]): state the
  identity over the spelled components (`Span::covers` in
  `lib/std/data/set/span_set.hthr`) and let the kernel convert.
- **Linear arithmetic at `Rat`/`CReal` is `linarith`**, not `omega`, which
  unfolds Rat facts into Int cross products.
- **nat.hthr and int.hthr cannot import omega.** Facts about Nat and Int
  still live there; prove them by case splits and the order kit.

## 4. Matches and recursion

- The convoy `match h : obs(t)` refines the goal, including hypotheses
  taken as arrows after it. If unsure, take `(o) → obs(t) = o → …` and match
  on `o`.
- A recursion that varies another parameter returns a function
  (`(self fuel): (n: Nat) → …`), with the matched parameter first. The
  elaborator generalizes a varied parameter itself
  (`docs/tactics/ih-generalization-design.md`), but not for a self-call under an
  `∃` in a `Type`-valued `fn`; curry that one by hand (`summation.hthr`'s
  `List::RecSum_of`, [[ih-generalization-under-exists]]).
- A case split on another parameter inside a recursion is fine: the guard
  is the `match` a self-call descends through
  ([[recursion-guard-takes-nearest-parameter-match]]). Not yet in a theorem
  about the split parameter, whose ih mentions it; split in a helper there
  ([[recursion-case-split-dependent-ih]]). An outer split works too, unless
  the calls change its parameter: then the branch is refused, since the
  recursive calls would skip it ([[recursion-branch-on-varied-parameter]]).
- A motive-less nested match on a `Cons` tail needs a written motive
  ([[nested-match-on-list-tail-motive]]).
- **A `match` whose arms fail with "`trivial` proves `True`, but the whole
  goal is expected" has lost its motive.** When the scrutinee is not
  written in the goal, the elaborator spells the goal's stuck head to find
  it, under a small step budget, and falls back to the goal as it stands
  without saying so. A scrutinee that reads through a few projections is
  enough (`StructuredRegion::emit_calls_runs`'s `Conditional` arm, once the register file
  was a record of slots). Write the motive with `as`
  ([[match-motive-stuck-spelling-budget]]).
- **Don't match on a large theorem call's result.** `match lemma(..) as
  .. { Exists(f, fh) => .. }`, or a match on `w.left` for `let w =
  lemma(..)`, makes the elaborator and the kernel unfold the proof (an
  order of magnitude more steps in `eft.hthr`; a split on a small lemma
  is cheap). Pass the proof to a helper theorem that matches on its
  parameter, or move the result with `j` over an equation:
  [[match-on-proof-call-cost]].
- **The same holds for projections chained through theorem results.**
  `let au = below_both(a.witness, ..); let ad = below_both(au.witness, ..)`
  and then a body over `ad.witness` made the kernel normalise the nested
  witnesses, proofs and all (`DerivOn::chain` and `DerivOn::mul` in
  `real_fn.hthr`: 8.3M and 8.9M steps). Compute the `∃` results with `let`,
  then hand them all to a `*_close` theorem whose parameters they are; its
  body projects variables (`DerivOn::chain_close`: 0.9M steps for both
  halves) — [[library-gate-module-cold-rail]].
- **An interface definition is an atom at open arguments outside its
  module** (`docs/language/interface-definitions-design.md`): `refl` and lemma
  statements that leaned on its body are refused, with a note naming the
  equations. Move a fact across the call with its arm equation,
  `rewrite(f_unfold_Ctor(…), in := h)` (or `sym(…)` for the other
  direction), or declare the proof `unfolding f` when it really is about
  the body. A call at closed arguments still computes, so §1's verdicts are
  unchanged.
- **A corecursive proof whose self-call would sit under `trans` (up-to
  coinduction, not built for indexed codata): generalise the hypothesis**
  to the relation the step lands in, so the next call's arguments are
  whatever the step produced. `Io::reads_loop` takes "the pass's reading
  `≈ u`" for any `u`, not "`= step`"; `Eutt::mrec_bind_from` takes
  `Bisim(p, bind(q, k))`, not `p = bind(q, k)`. Through a function of
  trees, follow the drops with `CoTree::after_map`'s exact count
  (`docs/itrees/coitree-design.md` §7.9).
- `absurd` needs a constructor clash; `False` goes by `false_elim`.
- Tier-2 laws through `Vis` are not provable with `=` (no funext): state
  them up to the tree's equivalence.

- **A function that branches on tests of its arguments is proved by
  `match h: test` on the same tests, in the same order.** The goal may
  mention the test only under the function's call, below binders, under a
  defined relation or an `↔` (`Regex::alt_same`): the motive synthesis
  reads the reduced goal there (`docs/elaborator/goal-motive-synthesis-design.md`
  §4.5). No second definition with the tests as parameters. Do not also
  write the test in the statement; take it from `h`. A call that is only
  an argument of another stuck call (`k.leb(f(n))`, `Mem(f(n), xs)`) is
  not reached: state the theorem at a name, `(p: Nat) → p = f(n) → …`,
  and give the corollary at the call
  (`issues/case-split-reaches-arguments-of-stuck-calls.md`). If an arm must
  keep the goal as written, say so with `as λ _ => <goal>`: an arm
  proved about the unreduced call is refused by the kernel once the
  split specialises the goal.
- **A claim about a recursive function is proved by `induct f(x̄)`, not by
  restating the loop as a fold.** Every recursive `fn` whose body is a tree
  of tests (`decreases` or structural) has `f::induct`, and `induct f(x̄);
  all_goals { bv_omega }` does the induction along its own recursion: the
  hypotheses about `x̄` are reverted, each case gets its test, its equation
  and an IH at each recursive call, and the leaf proves the IH's premises
  before it sees the IH. Name the arms (`induct f(x̄) { True => …, False =>
  … }`) when the cases need different proofs; a `for` loop is
  `List::foldl_invariant` over its step
  (`docs/tactics/functional-induction-design.md`).
- **Each case of an induction says which fact of the specification it is;
  shared work is a lemma or a tactic, never repeated plumbing.** An
  `induct` whose arms each restate the same chain of rewrites, threading
  hypotheses by position (`cut_two(…, h3, h4, rewrite(win.left(i + 1),
  bv_omega))` beside `cut_three(…, h5, h6, …)`), tells a reader nothing the
  function's own tests did not, and breaks when a test moves. Split on
  readable logic instead: one lemma per kind of case (a sequence of length
  `k` accepted, refused, or cut off by the end), stated once for every `k`,
  so each arm is a citation of the fact it is; or close arms alike with one
  shared tactic under `all_goals`. Hypotheses reach a lemma by their type
  (`rewrite` finds a side condition among them,
  `docs/tactics/equation-rewrite-design.md` §6.1), not by their generated
  names. Minus, 2026-11-18, on the UTF-8 example's thirteen-arm window
  proof: "We shouldn't be doing such manual manipulation except by logical
  means" (`issues/utf8-example-elegance.md`).
- **A loop counting a word up to a closed bound, run to its value, is
  `BitVec::loop_up`, not unfolding.** A `decreases` function whose
  body is one test with an equation (`if h: P { … } else { … }`, `match h:
  b { True => …, False => … }`) gets `f::step(x̄, h: P)` for the arm that
  calls it again and `f::done(x̄, h: ¬P)` for the one that stops. Give
  `BitVec::loop_up` the step as a function `g(s, i)` with its found proofs
  dropped (`vector_update`/`vector_get` for `v.put(i, x)`/`v.at(i)`, which
  is what they unfold to) and the two equations; it answers the loop as
  the exit at the bound from `BitVec::run_up(g, s, i, k)`, which at a
  closed count computes, and `BitVec::run_up_invariant` carries what each
  step keeps (`lib/_tests/native/crypto/sha256_schedule_tests.hthr`,
  `issues/loop-invariant-rules.md`).
- **A `runtime fn`'s induction is its principle applied by hand, with a
  stated lemma per case.** Its `f::induct` case binders carry no test
  names, so `induct`'s arms cannot cite `empty` or `hit`, and a case λ's
  binders past the motive get no types
  ([[runtime-fn-induct-test-names]]). Write the motive's body as a `fn …
  → Type`, one theorem per case whose result is it, and pass
  `λ x̄ tests eq => case(…)` (`WordMap::find_found`,
  `lib/native/runtime/word_map_laws.hthr`). A module whose `decreases`
  functions should get equations at all imports `logic` and `bool`;
  without them they are skipped silently
  ([[branch-equations-silent-without-logic]]).
- **`refl` between a wrapper and the measured call it makes at a literal
  runs out of fuel; state record η at a neutral record.**
  `f(x) = g(x, 4)` where `f`'s body is `let r = g(x, 4); Mutated(r.after,
  r.value)` is refused: the kernel unfolds `g` at the literal before
  η-expanding. `mutated_eta(r): Mutated(r.after, r.value) = r { refl }`
  instantiated at `g(x, 4)` converts at once (`WordMap::insert_is`).
- **A function that tests is cited by its branch equations, never
  restated.** A `fn` whose body (after its `let`s) is an `if`, `if h:` or a
  `match` on a `Bool` has `f::True(x̄, h: P)` and `f::False(x̄, h: ¬P)`:
  the call is the arm, under the condition as the source wrote it (`b =
  True` for a `Bool`), and `f::False::True` where the `else` tests again.
  A `match` on a parameter `x` of an inductive type has `f::C(x̄, ȳ, h: x
  = C(ȳ))` per written constructor arm.
  Pass the hypothesis as the comparison it is: a word's `i < 64` is
  `i.toNat() < 64` by conversion, so a typed `let lt: (i.toNat() < 64) =
  omega` is accepted for it. They are `simp` laws too, with the hypothesis
  found in scope (`issues/definition-branch-equations.md`).

## 5. Names and syntax

Diagnosed by the elaborator and by design: `let p: (a = b) = …` needs the
parentheses; a parameter with a default is passed by name; declarations are
used after they are declared; records have unqualified names; `split`,
`match`, `fun`, `if` and `Type` are not binder names; `Zero` and `Succ` are
built in; identifiers are ASCII.

Not diagnosed well yet:

- A member's bare base name is its self-reference: inside `Prog::Sim`,
  `Sim()` is a recursive call. Reach the global as `<module>::Sim`
  (`prelude::cong` for the prelude,
  [[self-reference-hides-same-named-global]]).
- Inside a section or class body, `+` and `*` are the carrier's operations
  even at Nat operands: spell `Nat::add(a, b)`.
- A generic lemma whose explicit arguments don't mention the carrier needs
  it written (`sound_rel<Rat>(…)`, [[partial-type-application]]).
- An all-numeral relation (`0 < 1`) is at Nat: write `Rat::Lt(0, 1)`
  ([[all-numeral-relations-default-to-nat]]). Numerals at `BitVec` need
  `import algebra;`, characters at a byte `import char;`
  ([[literal-classes-need-importing]]).
- `[x] ++ ys` has no carrier: write `Cons(x, ys)` or `List::append`
  ([[list-literal-left-of-append]]). A statement may start with a literal
  (`[1, 2] = xs`); `[` opens a vector type only when `;` follows its
  element ([[statement-leading-list-literal-parse]]).
- Generated source: never `list::Nil` (bare `Nil` resolves by expected
  type), and Int numerals as `int::OfNat(k)`.

## 6. Before pushing lib/

- `heather check --cache --review <file>` on each touched module: plain
  `check` hides the review tier of lints, and some suite tests assert none
  fire.
- `scripts/fmt` on new or edited `.hthr` files.
- New surface syntax: `scripts/check-tree-sitter`; a new keyword in
  tree-sitter-heather/syntax-inventory.json, a new symbol a row of the token
  kinds' table (`lib/lang/lexer/lexer_kinds.hthr`, `crates/linked/CLAUDE.md`).

## 7. Measuring a proof's cost

- Use a fresh `--cache-dir` per run: a warm store, and an identical
  declaration earlier in the same process, answer from verdicts and make
  items look 10–50× cheaper.
- `--only module::Owner::name --timings f.tsv` probes one declaration over
  a replayed prefix; read the table with `scripts/timings`.
