# Induction-hypothesis generalization

How a `fn` or `theorem` whose self-calls **vary a non-decreasing parameter**
is elaborated (`issues/ih-generalization.md`). The customers are the curried
definitions of `lib/std` — `sub`, `Le`, `leb`, `take`, `drop`, `foldl` — and
every accumulator proof that wrote its motive by hand
(`lib/certgen/ir_v1.hthr`'s `eval_mono_succ`, `le_add`, `add_loop_runs`).

## 1. What was refused, and why it was not the guard

`sub` written the way anyone writes it:

```
fn sub(m: Nat, n: Nat) -> Nat {
    match m {
        Zero => 0,
        Succ(m2) => match n { Zero => Succ(m2), Succ(n2) => sub(m2, n2) },
    }
}
```

was refused with "recursive call to `sub` must pass `n` unchanged". The
refusal was honest: `match m` compiles to one `elim_Nat`, whose induction
hypothesis is the value at `m2` *for the `n` in scope* — a term of type
`M[m2]` where `M` was abstracted from the goal `Nat` and mentions no `n`. A
call at `n2` has no term to lower to. The library's answer was to curry
(`fn sub(m: Nat) -> Nat -> Nat`, arms `λ (n: Nat) => …`), which makes the
motive `Nat -> Nat` by hand; proofs did the same with an explicit
`match fuel as λ f => (env: Val) -> …`.

Both are the same move: **the motive quantifies the varying parameter**. This
round makes the elaborator do it.

## 2. The transformation

For a `match` in checking position, descending on parameter `n`, with goal
`G` and a set `V = {m₁ < … < m_g}` of parameters the arms' self-calls vary:

1. **Goal.** `G` becomes `Ĝ = Π(y₁ : T_{m₁}) … Π(y_g : T_{m_g}). G`, where
   every reference to `mᵢ` inside the domains and in `G` points at `yᵢ`
   (`generalize::rename`, a renaming substitution `Γ → Γ, y₁ … y_g`).
2. **Motive.** Ordinary motive synthesis
   (`docs/goal-motive-synthesis-design.md`) abstracts the scrutinee out of
   `Ĝ`, domains included — so `h : Le(n, m)` becomes `Le(z, y)` under the
   motive's `z`, which is what lets the ih be stated at the predecessor.
3. **Arms.** Each arm body `e` becomes `λ m₁ … m_g => e` — unannotated
   lambdas under the parameters' **own names**, so the body reads exactly as
   written and its `m` is the generalized one. The domain comes from the arm's
   expected Π, the one place it is already right.
4. **Self-calls.** Inside an arm, `f(k, e₁, …)` finds the ih at type
   `Π(y₁ : …) … . G[k/z]` and applies it to the arguments written at the
   generalized positions, in position order, through the ordinary explicit
   application engine — which checks each against its Π domain
   (`recursion::elab_self_call`). Every other parameter still has to be passed
   unchanged, by binder.
5. **Result.** The finished recursor has type `Ĝ` and is applied back to
   `m₁ … m_g`, which lands it at `G` syntactically
   (`generalize::instantiate_generalized`).

Nothing is forced to the body root. The `match` can sit anywhere a goal is
known: the parameters are abstracted from *that* goal and re-applied there.
What the issue's sketch called "forcing the match to the body root" was a
consequence of thinking in terms of the declaration; thinking in terms of
the goal, the transformation is local to the expression, as the
course-of-values one is (`docs/course-of-values-recursion-design.md` §2).

**It is still one recursor**, so closed arguments compute: `sub(5, 2) = 3`
is `refl`, `Le(2, 3)` is `trivial`.

**The empty case is a no-op.** `V = ∅` — every recursion written before this
existed — takes the old path and emits the old term.

## 3. Which parameters, and why the scan is only a sizing decision

`V` is read off the surface arms by name (`Elaborator::varying_params`): a
self-call's argument at a non-decreasing position is *unchanged* when it is
the bare parameter name, *varying* otherwise. Then the set is closed under
dependency: a later parameter whose type mentions a generalized one is
generalized too (`h : acc = b` goes with `acc` and `b`), since its type is
only right at the generalized value.

Names can lie — a `let m = …` or `λ (m: Nat) => …` in the arm shadows the
parameter — and, as for `cov_depth`, neither direction of wrong produces a
wrong term:

- **Missed** (a shadowing name reads as unchanged): the by-binder check in
  `elab_self_call` sees a variable that is not the parameter and refuses,
  exactly as it always did. The negative control
  `a_shadowing_name_does_not_fake_an_unchanged_argument` pins this.
- **Over-included** (something read as varying that is not): the motive
  carries a Π the arm applies to the parameter itself. A bigger term,
  never a wrong one.

What a call *lowers to* is decided by comparing binder positions and by
checking each varied argument against the ih's domain, and the kernel checks
the whole recursor afterwards. The scan never authorizes anything.

One exclusion is the scan's own: a parameter the *scrutinee's* type depends
on is an index (`fn append(n: Nat, xs: Vec(n), …)` descending on `xs`), and
an indexed `match` already rebinds it at each arm's own pattern variable
(`docs/inductive-indexed-lowering.md` §6, `Guard::rebind`). Generalizing it
would change the scrutinee's type, so it is never a candidate; the route
handles it, and where the family is not indexed the by-binder refusal
stands. Other parameters of an indexed recursion are generalized as usual
(the indexed routes read the plan off the guard like the rest).

## 4. How it composes

- **Course-of-values windows** (`docs/course-of-values-recursion-design.md`):
  the window's components are now Π types; a self-call at depth `j` projects
  component `j` and then applies it. The window's motive is the generalized
  one, so convoying through a nested `match` reindexes it like any other.
  `composes_with_a_course_of_values_window` pins depth 2 with a varying
  accumulator.
- **`Wf` inductives** (`docs/inductive-tier1-wf-lowering.md` §6.4): each
  child's ih is `M[child/z]`, now a Π; the call applies it. `take<A>` and
  `foldl<A, B>` are pinned at an **open** element type, `fold_count` with a
  dependent motive.
- **Nested `match` on a generalized parameter.** Inside the wrapped arm the
  parameter's name resolves to the lambda binder, which is not a parameter,
  so `descends_on_param` declines and the inner `match` keeps the outer
  guard. This is what makes `match n { Succ(k) => match m { … sub(k, l) } }`
  work: the inner `match` is an ordinary one and `sub(k, l)` reaches the
  outer ih.
- **Implicit parameters.** A varying implicit is generalized like any other
  and must be passed, so the call has to be `@`-marked; a plain call meets a
  message naming that (`an_implicit_parameter_varied_without_at_is_named`).
- **Over-application** (`issues/call-site-overapplication.md`): arguments
  beyond the declaration's arity are applied after the generalized ones, so
  `le_trans(k, m2, l2, a, c)` with the hypotheses behind arrows works
  unchanged.

## 5. What it does not do

- **The context is refined by a non-recursive `match`, not by the
  recursion's own.** Since `issues/elab-match-refines-hypothesis-kernel-
  rejects.md`, a motive-less `match` on a local in checking position also
  generalizes the later binders whose type mentions the scrutinee (directly
  or through another) and that an arm names or the goal mentions, with the
  binders their types need (`Elaborator::refined_hypotheses`), through the
  same three steps: Π goal, wrapped arms, re-application. Only those: a
  `match` in a function body or a motive is a computation that must stay the
  term it restates, and the machinery's binders (`#ih`, a measure
  recursion's `__dec_h`) are read as they were. So `h : Le(n, m)` *is* `Le(Succ k, Zero)` in
  `match m { Zero => … }`. A `match` on a parameter whose arms make a
  self-call keeps exactly the generalization above: a self-call can pass
  only declared parameters, so a refined local that is not one would leave
  the ih a Π nothing can instantiate. There a hypothesis behind an arrow
  (or a sequent binder) is still the way to have it refined, which is how
  the library writes `le_trans`.
- **Inference position.** A `match` whose type is inferred has no goal to
  abstract from. A written motive that does not quantify the parameter meets
  the old refusal, which now says under what conditions generalization
  happens and points here.
- **The equation binding** (`match h: n { … }`) makes the ih
  `Π(h : n = k). M[k]`, which no self-call can instantiate; recursion under
  an equation binding was unsupported before this round and still is.
- **Cost.** A generalized motive is a bigger term at every arm, and the issue
  measured that cost on the manual route (`step_mono`, 2026-07-31). The
  elaborator-computed motive is the *same* term; what changes is who writes
  it. Nothing here makes it smaller (`issues/simulate-conversion-cost.md`).

## 6. Where it lives

- `crates/elab/src/generalize.rs` — the scan, the Π goal, the arm wrapping,
  the re-application; unit tests for the renaming substitution.
- `crates/elab/src/lib.rs`, `elab_check`'s motive-less `match` arm — the
  entry: descends on a parameter and varies something, or refines a
  hypothesis → the path above.
- `crates/elab/src/recursion.rs` — `Guard::generalized`, and the self-call
  applying the ih to its varied arguments.
- Guard construction sites (`matching/routes.rs`, `wf.rs`, `indexed.rs`,
  `forded.rs`) read the planned generalization off `Cx::generalized`, keyed
  by the `match`'s span so a nested `match` on the same parameter — whose arms
  were not wrapped — never inherits one it cannot honor.
- `crates/elab/tests/ih_generalization.rs` — acceptance;
  `crates/elab/tests/match_refines_hypotheses.rs` for the refined
  hypotheses.

No kernel change.
