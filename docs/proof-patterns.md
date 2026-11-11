# Proof patterns: what costs, and what the language wants

The rules rounds kept rediscovering, checked against master on 2026-10-29
([[proof-patterns-audit-2026-10]] in issues/ has the probes and what was
retired). Each rule says why, so it can be dropped when the reason goes.
A rule that names an open issue is a workaround for that issue, not a
property of Heather.

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
  (`docs/simp-design.md` §10), not a `calc` with one law per line or nested
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
  read that before adding a law. Not reached yet: a law `P ↔ Q`
  ([[simp-iff-laws]]), an instance under a λ ([[simp-under-binders]]), and
  a goal a named `match h: test` left unfolded past its `≈`, which is
  restated in a one-step `calc` ([[case-split-unfolds-the-goals-relation]]).
- **State lemmas in the goal's spelling.** `x - y` against `x + -y` makes
  `rewrite` and generic-lemma matching convert, or fail before instance
  search (`hi + -lo`, not `hi - lo`, for a generic lemma at `Rat`).
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
- **Over records and layouts at a literal program, prefer Nat step lemmas**
  (`Nat::le_trans`, `add_le_mono_l`) or a generic lemma over Nat variables.
  The kernel converts the atoms' definitions. omega does read a field at
  closed arguments as what was put there (`Lay::of(3).size` meets
  `Lay::of(3).cap`), so a failure there is a missing fact, not an atom.
- **It reads every hypothesis in scope.** Keep its context small: put
  arithmetic in small lemmas, never `omega` inside a stretch or with `Rat`
  facts in scope. Inside a claim of trees (a `Goes` built from nested
  lets and lambdas) even a one-fact `omega` read the whole context and
  took minutes; stating the step's arithmetic as a lemma over bare
  numbers (native_compile_perform's `push_arith`) made it free. `omega(h, …)` names the load-bearing facts; whether it
  should read *only* those is [[omega-listed-facts-only]], an open decision.
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
  (`docs/ih-generalization-design.md`), but not for a self-call under an
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
  enough (`emit_calls_emits`'s `Conditional` arm, once the register file
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
  module** (`docs/interface-definitions-design.md`): `refl` and lemma
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
  (`docs/coitree-design.md` §7.9).
- `absurd` needs a constructor clash; `False` goes by `false_elim`.
- Tier-2 laws through `Vis` are not provable with `=` (no funext): state
  them up to the tree's equivalence.

- **A function that branches on tests of its arguments is proved by
  `match h: test` on the same tests, in the same order.** The goal may
  mention the test only under the function's call, below binders, under a
  defined relation or an `↔` (`Regex::alt_same`): the motive synthesis
  reads the reduced goal there (`docs/goal-motive-synthesis-design.md`
  §4.5). No second definition with the tests as parameters. Do not also
  write the test in the statement; take it from `h`. A call that is only
  an argument of another stuck call (`k.leb(f(n))`, `Mem(f(n), xs)`) is
  not reached: state the theorem at a name, `(p: Nat) → p = f(n) → …`,
  and give the corollary at the call
  (`issues/case-split-reaches-arguments-of-stuck-calls.md`). If an arm must
  keep the goal as written, say so with `as λ _ => <goal>`: an arm
  proved about the unreduced call is refused by the kernel once the
  split specialises the goal.

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
- New surface syntax: `scripts/check-tree-sitter`, and new lexer symbols in
  tree-sitter-heather/syntax-inventory.json.

## 7. Measuring a proof's cost

- Use a fresh `--cache-dir` per run: a warm store, and an identical
  declaration earlier in the same process, answer from verdicts and make
  items look 10–50× cheaper.
- `--only module::Owner::name --timings f.tsv` probes one declaration over
  a replayed prefix; read the table with `scripts/timings`.
