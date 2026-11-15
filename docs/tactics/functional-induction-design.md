# Functional induction

How a proof about a recursive function follows the function's own
recursion: the generated principle `f::induct`, the `induct f(x̄)` step that
applies it, and `List::foldl_induct` for `for` loops. Piece B of the
program-proof tactics proposal (`docs/program-proof-tactics-design.md`,
`issues/loop-invariant-rules.md`).

The customer is the proof that had to restate a loop as a fold over a count
before it could do induction: `tally_gains`
(`lib/_tests/std/bitvec/bitvec_loop_tests.hthr`) went through
`BitVec::run_up_invariant` with the step written out twice, and the SHA-256
padding proof (`lib/native/crypto/sha256_stream_agreement.hthr`) needed a
separate fold function `Sha256::zeroed`, a theorem that the loop *is* that
fold, and a theorem about the fold. Now:

```
theorem tally_gains(start: u64, acc: Nat, below: start <= 8): tally(start, acc) = acc + (8 - start.toNat()) {
    induct tally(start, acc); all_goals { bv_omega }
}
```

and `Sha256::zero_block` is one `induct Sha256::zero(s, i) { True => …, False => … }`
over the loop itself.

## 1. The principle

A recursive `fn` whose branch equations the elaborator reads gets one more
theorem, minted `f#induct` and designated `f::induct`, with the equations at
every leaf it is proved from (`f::True`, `f::Cons`, …). A `decreases`
function gets them when it is declared; a structural one when a declaration
of its module first asks (§6):

```
theorem f::induct(fixed…, motive: (varying…) → Type,
    case_True:  (varying…) → (h: P) → (eq: f(x̄) = leaf) → (ih: motive(args)) → motive(x̄),
    case_False: (varying…) → (h: ¬P) → (eq: f(x̄) = leaf) → motive(x̄),
    varying…): motive(varying…)
```

- **Which functions.** The ones `branch_equations`
  (`docs/language/recursion/decreases-unfolding-design.md` §6) reads: a
  body that is a tree of tests (a `Bool` test, `if h:`, a constructor match
  on a parameter), with `let`s on the way. A `decreases` function is read
  through `f_unfold` (`Recursion::Measure`); a structural one through its
  first constructor match, which must be the body's first test
  (`Recursion::Structural`). A function with nothing to read gets no
  principle, and the reason is recorded with the step equations' refusals.
- **Cases.** One per leaf, in the branch equations' order, named by the
  leaf's path: `case_True`, `case_False_True`, `case_Cons`. A case
  quantifies the varying parameters, the fields and hypotheses on the way
  (a constructor test substitutes the constructor for its parameter, as an
  induction on it would, and drops the equation), the leaf's equation `eq`,
  and an induction hypothesis `ih`, `ih2`, … at each recursive call the
  leaf makes outright (not under a `λ` or a match arm, whose variables the
  case does not bind).
- **Fixed and varying.** A parameter every recursive call passes unchanged
  and no test matches is *fixed*: a parameter of the principle ahead of the
  motive, so the motive does not quantify it and every IH is at the same
  value. The rest vary.
- **`let`s and `mut self`.** A leaf's `let`s are inlined into the IH's
  arguments. A `mut self` body threads its state through
  `\0mutated(x.m(a))` markers that rebind `x` implicitly; the principle
  reads them as `x := m(x, a).after`, so the IH of `s.zero(i + 1)` after
  `s.put(i, 0)` is at the state the put left (`threaded_lets`).
- **Proof.** By the same recursion as `f` (its `decreases` copied, or
  structural): a tree of `f`'s own tests whose leaves apply the case to the
  branch equation and to the principle at the call's arguments. The kernel
  checks it like any declaration, so nothing generated is trusted; a
  principle it refuses is skipped and the refusal recorded.

The principle is a theorem like any other, applied by hand where that reads
better (`up_by_principle` in `lib/_tests/std/tactic/induct_tests.hthr`).

## 2. The `induct` step

```
induct f(ā); all_goals { block }
induct f(ā) { True => block₁, False => block₂ }
```

at a goal `G`, in a block's result position.

1. **The principle** is `f::induct`, resolved from the call's head. A
   function with implicit parameters needs `@` so every argument is
   written.
2. **Varying arguments** must be distinct local variables: the principle
   quantifies them, so a literal or a computed argument has nothing to
   generalize (`induct_at_a_literal` is the negative control). A fixed
   argument may be anything that does not mention a varying one.
3. **Revert.** Every local after the first varying one whose type mentions
   a varying local, directly or through another reverted one, is reverted:
   the goal becomes `Π R̄. G`. So a hypothesis `below: start <= 8` is a
   premise of every IH and is reintroduced, under its own name, in each
   case. Locals that do not mention the varying ones stay as they are,
   so a fixed argument can name them.
4. **The goal alias.** `G` with the call abstracted is
   `#induct_goal = λ x̄ r. Π R̄. G[ā := x̄, f(ā) := r]`, a term the
   elaborator builds (`generalize_expected`, `abstract_local`) and the
   surface refers to by name through a `Cx` alias. The motive is
   `λ x̄ => #induct_goal(x̄, f(x̄))`.
5. **Each case** is a `λ` over the case's binders, the varying ones under
   the user's names, that rewrites the call by the case's own equation with
   `j(sym(eq), λ v _ => #induct_goal(x̄ₖ, v), …)`: a transport of the
   alias's hole, so no occurrence of `f(x̄)` has to be found again in a goal
   that may have been reduced on the way. The reverted locals are
   introduced, and the block is checked.
6. **The leaf.** Before the block runs, each IH is restated at its
   normal form (the motive applied and decoded), so a decision procedure
   reads `tally(start + 1, acc + 1) = …` and not an application of a
   motive. Under `all_goals` the block is also tried, speculatively, on
   each premise of each IH (a reverted hypothesis at the call's
   arguments): where it proves one, the IH is handed over applied; where it
   does not, it stays an implication. So `bv_omega` proves
   `start + 1 <= 8` from the case's `start < 8` and then the claim from the
   IH. In the arms form the IHs are named `ih`, `ih2`, … and only restated:
   the arm says what to do with them.

Arms are named by the case's path: `True`, `False`, `Cons`, and `Cons::True`
for a constructor test followed by a `Bool` one.

The step is an elaboration of surface terms built around the user's block,
so a mistake in it is a kernel refusal of the result, never an accepted
wrong proof.

## 3. `for` loops: `List::foldl_induct`

A `for` over a list lowers to `List::foldl` of a generated step
(`docs/language/sequencing-surface-design.md` §5.2), so its rule is one
library theorem, not a generated one per loop (§7.2 there):

```
theorem List::foldl_induct<A, B>(self xs: List<A>, f: B → A → B, P: List<A> → B → Type,
    step: (done: List<A>) → (x: A) → (s: B) → P(done, s) → P(done ++ [x], f(s, x)),
    done: List<A>, z: B, start: P(done, z)): P(done ++ xs, xs.foldl(f, z))
```

with `List::foldl_invariant` its instance at the empty prefix. The invariant
sees the prefix folded so far, which is what a loop invariant usually
mentions ("the count is the number of elements seen"). `loop_count_len` in
`induct_tests.hthr` proves a `for` loop's spec through it.

## 4. Module images

`f::induct` is a designated name like `f::True` and `f::step`, and designated
names are global. Two modules that each define a function named `apps` both
designate `apps::Nil`; replaying their images used to refuse the second as a
conflict. A designation is now idempotent, and the replay check refuses only
a designated name that would map to a *different* minted name
(`designate_access`, `module_delta`).

## 5. What it does not do

- **Mutual recursion**, and recursion through a higher-order argument
  (`xs.map(λ x => f(x))`): the leaf's calls under a `λ` get no IH.
- **A structural function whose first test is not the match on the
  decreasing parameter**: no principle; the refusal is recorded.
- **A structural function from another module** whose own module did not
  build its principle (§6).
- **Functional induction on a call nested in the goal at arguments that are
  not variables.** State the claim for variables and instantiate it, which
  is what the refusal says.
- **`for_in`** (a loop with `break` or `return`) has no rule yet;
  `List::for_in_invariant` is the same shape over `ForStep`.

## 6. Cost, and when a principle is built

Building the equations and the principle for every recursive function cost
about a third of a cold elaboration of the SHA-256 tree
(`lib/native/crypto/sha256_agreement.hthr` and what it imports), the
equations two thirds of that. Nearly all of it was large structural
functions nobody proves about by induction: the runtime reflection's and
the layout library's generators (`rt_held_do`, `laid_fields`), each with
dozens of leaves.

So the two kinds are built at different times:

- **A `decreases` function** builds its equations and principle when it is
  declared. Loops are what program proofs are about, they are proved in
  other modules (the SHA-256 padding loop is declared in `sha256_filling`
  and proved in `sha256_stream_agreement`), and there are few of them; the
  cold tree's time is master's, within noise.
- **A structural function** is recorded as written
  (`ModulePass::recursions`) and built the first time a declaration of its
  module does `induct f(…)`, names `f::induct` or names one of its equations (`f::Cons`)
  (`DeclarationsMut::demand_principles`, run before the declaration). Later
  declarations, and importers, find it by its designated name. A module
  that imports a structural function whose module never asked for its
  principle cannot build it: the written body does not travel in a module
  image (`issues/function-induction-across-modules.md`), and the step says
  so.

## 7. Where it lives

- `crates/elab/src/function_induction.rs`: the principle (`induct`) and the
  step (`FunctionInduction::induct_step`, `induct_leaf`).
- `crates/elab/src/branch_equations.rs`: the tests along each path
  (`PathStep`, `PathTest`) and the structural reading
  (`Recursion::Structural`).
- `crates/elab/src/declarations.rs`: `elab_recursion_equations`, which
  builds both and designates them; `demand_principles`, which builds a
  structural function's on demand from `ModulePass::recursions`.
- `crates/syntax/src/parser.rs`: `induct f(ā); all_goals { … }` and
  `induct f(ā) { arms }`.
- `lib/std/data/list.hthr`: `List::foldl_induct`, `List::foldl_invariant`.
- `lib/_tests/std/tactic/induct_tests.hthr`: probes and negative controls.
