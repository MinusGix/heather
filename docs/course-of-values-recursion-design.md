# Course-of-values recursion on `Nat`

How a `fn` whose self-call lands on the *predecessor's* predecessor is
elaborated (`issues/recursion-at-deeper-subterms.md`). The customer is
`lib/std/nat.hthr`'s parity section — `half`, `Even`, `Odd` — and the classic
`fib`.

## 1. What was refused, and why the guard was not the problem

`half` written the way anyone writes it:

```
fn half(n: Nat) -> Nat {
    match n {
        Zero => 0,
        Succ(k) => match k { Zero => 0, Succ(l) => Succ(half(l)) },
    }
}
```

`l` is structurally smaller than `n`, so the old refusal — the call must
descend to `k` — read as a checker being needlessly strict. It was not.
`match_recursion`'s discipline compiles an arm into the kernel's **`elim_Nat`**
step, and the induction hypothesis a recursor binds is the value at the
*immediate* predecessor, because that is the only thing a recursor has.
Inside `match k { Succ(l) => … }` the enclosing ih is still the value at `k`,
i.e. at `l + 1`. Relaxing the comparison would have accepted the call and left
the elaborator with no term to emit.

So this is an **elaboration strategy**, not a loosened check. The guard still
compares binder positions and can still only reject; a wrong analysis produces
a term the kernel refuses, which is `match_recursion`'s stated safety property,
unchanged.

## 2. The transformation

A recursion whose deepest self-call is at depth `d` is elaborated into one
`elim_Nat` that computes the **last `d` values** as a right-nested Σ-tuple,
with the source's own value projected back out:

    F(0)      = (f(0), …, f(0))
    F(Succ k) = (step(k, F(k)), π₀F(k), …, π_{d-2}F(k))
    f(n)      = π₀ F(n)

The body the writer wrote is *unchanged*: the nested `match` stays as written,
and a self-call at depth `j` becomes `π_{j-1}` of the tuple ih. For `half`,
`d = 2` and `F(n) = (half(n), half(n-1))`:

    F(0)      = (0, 0)
    F(Succ k) = (match k { Zero => 0; Succ(l) => Succ(π₁F(k)) }, π₀F(k))

`half(l)` became `π₁F(k)`; nothing else moved.

**It stays local to the `match` expression.** The recursor's first component is
exactly the value the source's `match` had, so the expression still has type
`M[scrut/z]` and the surrounding term is untouched — no declaration-level
rewrite, and `d = 1` emits the term it always did, `Σ`-free.

**It is still one `elim_Nat`**, which is the property the library is written to
keep: closed arguments still compute, `half(7) = 3` is `refl` and `Even(4)` is
`trivial`.

## 3. The tuple's type, and why `pred` appears

Component `i` of the tuple at `z` is the motive at `pred^i z`:

    T(z) = Σ(M[z], Σ(M[pred z], … Σ(M[pred^{d-1} z]) …))

with `pred` the kernel term `elim_Nat(λ _. Nat; 0; λ k ih. k; -)`. A
non-dependent motive (`half`, `Even`, `fib`) never notices, but a *dependent*
one — every `theorem` proved by two-step induction, `half_le` included — does,
and this is what makes the two annotations line up **by computation** rather
than by lemma:

- in the step, `π_{i-1}F(k) : M[pred^{i-1} k]` is wanted at
  `M[pred^i (Succ k)]`, and `pred (Succ k) ⇝ k`;
- in the base, each component is wanted at `M[pred^i 0]`, and `pred 0 ⇝ 0`.

So the kernel converts, and neither the writer nor the elaborator states a
transport.

## 4. The base's deeper components are the `Zero` arm again

`F(0)`'s components below the first stand for values *before the start*, which
have no definition. They are filled with the `Zero` arm's own value — the one
term of the right type already to hand (§3: all `d` components of `T(0)` are
`M[0]`).

Nothing can read them, and the reason is scoping rather than a check:
a call at depth `i` can only be written inside `i` nested `Succ` arms, so the
component is only ever reached when the scrutinee is at least `i`. The issue
predicted a syntactic side condition here — "a depth-`d` recursion must supply
base arms at every depth below `d`, and one that does not is refused". No such
refusal exists, because the nested `match` the writer had to write in order to
*name* the deeper variable is already that base arm.

## 5. The nested `match` must convoy the window

§3 is not enough on its own, and the gap is worth stating plainly because the
issue that costed this work did not predict it.

The arm's window has type `T(k)` for a *variable* `k`, so its second component
has type `M[pred k]` — and `pred k` is **stuck**. Inside
`match k { Succ(l) => … }` the elaborator wants that component at `M[l]`, and
nothing connects the two: a `match` arm does not tell its body that the
scrutinee was `Succ(l)`.

For a non-dependent motive this never shows — `M[pred k]` and `M[l]` are the
same type, which is why `half`, `Even`, `Odd` and `fib` all worked before this
section existed. Every two-step *proof* — `half_le`, `even_or_odd`,
`half_add_half`, and `even_dec`, whose result type mentions its argument — has
a dependent motive and none of them checked.

The fix is the move the library already writes by hand for hypotheses
(`le_trans` in `lib/std/nat.hthr` convoys two): a nested `match` on the chain's
end is elaborated with its window as an **argument**, not as something in scope
around it.

    match k as λ y => T(y) -> Goal(y) { … } (window)

In the `Succ(l)` arm the convoyed binder has type `T(Succ l)`, whose second
component is `M[pred (Succ l)]` — and *that* reduces to `M[l]`. The refinement
the arm failed to give the context, it gives the argument's type instead.

Three things fall out of this, all of them checked:

- **A call at the outer `k` inside the arm** now lowers to the convoyed
  component at `M[Succ l]` rather than `M[k]`. That is the consistent choice,
  not a compromise: motive synthesis abstracts every occurrence of `k` from the
  arm's goal, so the arm's goal was refined to `Succ l` too.
- **The `Zero` arm gets a convoy binder as well**, and its components sit at
  `M[pred^i 0]`. A call at `k` there lowers to the value at `0`, again matching
  the refined goal.
- **Nothing is convoyed when nothing is carried.** A one-step recursion has no
  component below the chain's end, so `chain_convoy` declines and the emitted
  term is byte-for-byte what it always was. The convoy is not a new cost on
  ordinary code.

The guard therefore carries the recursion's *motive family* along with the
window, plus the context that family was written in — a family cannot be
reindexed by shifting, so the two travel together.

### 5.1 The window is anchored at the chain's head, and a second nesting lifts it

At depth three and below there is a second `match` to convoy through, and the
invariant that makes it work is worth stating because getting it wrong
typechecks nowhere and reads like an off-by-one anywhere:

> The window always holds the values at the chain read **from its head**:
> component `i` is the value at `preds[i]`. So it stays anchored at `preds[0]`
> however deep the nesting goes.

The first nested `match` scrutinizes the head itself, so it convoys the window
at its own scrutinee. The second scrutinizes the value one *below* the head, so
it must convoy the same window at `Succ` of its scrutinee — and the `j`-th at
`Succ^{j-1}`. Re-indexing the window at each new scrutinee instead slides every
component by one, and the arm then asks for the value at `l` from a tuple whose
head is the value at `l`.

The reduction that makes it land is again `pred (Succ x) ⇝ x`, now applied
`i` times: in the `Succ(m)` arm of the third level the window sits at
`Succ²(m)`, whose components are the values at `k`, `l` and `m` exactly.

`fib` and `trib` never see any of this — a non-dependent motive makes every
anchoring agree — so the depth-3 and depth-4 tests that pin it are
**dependent** on purpose (`crates/elab/tests/match_recursion.rs`).

## 6. The depth scan is a sizing decision only

`cov_depth` reads the surface arm and answers how deep its self-calls reach.
It works on **names**, so a shadowed binder can make it wrong — and neither
direction of wrong can produce a bad term:

- too small: the real check finds no ih at that depth and refuses the call,
  which is the refusal that stood before any of this existed;
- too large: the recursor carries a component nothing reads.

What a call *lowers to* is decided elsewhere, by comparing binder positions
(`elab_self_call`), which no spelling can fool. Keep it that way: the scan must
never become the thing that authorizes a lowering.

## 7. The chain is followed by binder, not by name

`GuardKind::Nat` carries `preds` — the chain `k`, `l`, … the enclosing
`match`es bind — and the window those index into. A nested `match` extends the
chain only when its scrutinee **is** the binder at the chain's end;
`match m { Succ(l) => … }` on some other variable leaves the guard as it was,
so a call at that `l` is refused. This is the same by-binder comparison that
already stopped shadowing from faking a one-step guarded call.

The window's width is the depth the recursor was actually built for. A call deeper
than that is refused with a message that names the mechanism, because the bare
rule reads as strictness and sends a reader to the wrong file.

## 8. What this is not

- **Not well-founded recursion.** `div`/`mod`/`gcd` descend by a *measure*,
  not by a fixed number of constructors, and are `issues/termination-measures.md`.
- **Not mutual recursion**, same issue.
- **Not `Wf` inductives** — *was*, until 2026-09-18.
  `docs/list-course-of-values-design.md` carries the window to any
  **chain-shaped** declaration (every constructor with at most one recursive
  field and no container): the same transformation with `pred` replaced by the
  recursive-field projection `tail_D`, the chain followed by term rather than
  by binder, and the convoy re-anchored by rebuilding the arm's constructor.
  `lib/std/utf8.hthr`'s fuel-free `decode` is the customer. A **branching**
  arm's ih is still one per recursive field; extending the window to a
  grandchild there is a different tupling and has no customer, so a tree keeps
  the refusal — with the message extended to say what chain-shaped means.
- **Not a kernel change.** No new former: Σ, `pair`, `fst`/`snd` were already
  there from the branching-inductives round
  (`docs/branching-inductives-choice.md`).
