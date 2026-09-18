# Course-of-values recursion on `Wf` inductives — design

Status: **design, 2026-09-18**; owner `issues/list-course-of-values-recursion.md`.
Extends `docs/course-of-values-recursion-design.md` (the `Nat` design, read it
first; §8 there deferred this case "until a customer"). The customer is
`lib/std/utf8.hthr`: `decode` consumes one to four bytes per step, so its
self-call lands on a grandchild of the scrutinee, and today it recurses on a
fuel because of that. Heather code below is a sketch and unchecked.

## 1. Scope: chain-shaped inductives only

The `Nat` transformation carries the last `d` values along the *predecessor
chain*. The same chain exists in any inductive whose constructors each have
**at most one recursive field** and no container field: `List`, `Option`-like
wrappers of a recursive type, a user `inductive Run { Stop, Step(payload, next: Run) }`.
A constructor with two recursive fields (a tree) has no chain; its window
would be a tree of values, and there is no customer. Those keep today's
`GuardKind::Wf` and today's refusal, with the message extended to say the
window exists for chain-shaped types and why a tree is not one.

So the feature is: **the `Nat` window, with `pred` replaced by the
recursive-field projection**, on tier-1 inductives whose shape is a chain.

## 2. The projection that plays `pred`

`pred` is `elim_Nat(λ _. Nat; 0; λ k ih. k; -)` with `pred 0 ⇝ 0`
(`matching/routes.rs`, `pred_tm`). Its `Wf` counterpart is

    tail_D(z) = elim_Wf(λ _. D; λ a f ih. case tag(a) of
                    recursive ctor  ⇒ f(ι₀)        -- the one child
                    base ctor       ⇒ z;           z)

a constant-motive `elim_Wf` in the shape `const_elim_wf` already builds
(`wf.rs` §7), with the outer `z` in scope for the base arms so that
`tail_D(Nil) ⇝ Nil` exactly as `pred 0 ⇝ 0`. The two computation facts the
`Nat` design leans on (§3) hold for the same reason: `tail_D(Cons(h, t)) ⇝ t`
is `elim_Wf` β on a `sup`, and at a base constructor `tail_D` is the
scrutinee itself.

Component `i` of the window at `z` is `M[tail_D^i z]`; `cov_comps`,
`cov_ty`, `cov_tuple`, `cov_proj` are reused with `tail_D` in place of
`pred_tm`. `tail_D` is bigger than `pred` (a case tree on the tag), so
`issues/cov-window-term-size.md`'s O(d²) shape gets a larger constant; note
it there, do not measure.

## 3. The transformation

Unchanged from `Nat` §2, per arm:

- a **recursive** constructor's arm gets the child's tuple ih (the
  `elim_Wf` ih at `ι₀`, which `GuardKind::Wf` already holds as
  `children[0]`), and emits `(body, π₀ ih, …, π_{d-2} ih)`; a self-call at
  depth `j` in the body lowers to `π_{j-1} ih`;
- a **base** constructor's arm emits its own value `d` times (§4 of the
  `Nat` design: the nested `match` the writer had to write to name the
  deeper binder *is* the base arm, and nothing can read the copies);
- `f(z) = π₀ F(z)`; `d = 1` emits today's term byte for byte.

It is still one `elim_Wf`, so closed lists compute: `decode` at a literal
byte list stays `refl`-checkable, which is the acceptance the round is for.

## 4. The convoy, by term rather than by binder

`Nat` §5–§7: a nested `match` on the chain's end convoys the window as an
*argument* so that in the recursive arm its type is at the rebuilt
constructor and `tail_D` computes. Two differences here:

- **The chain is followed by term, not binder position.** A `Wf` arm binder
  is an *alias* to a projection term (tier 0 §5.1), which is why
  `GuardKind::Wf` already compares terms. The chain becomes
  `Vec<Rc<Term>>`: `chain[0]` is the arm's own child term, `chain[1]` the
  child a nested `match chain[0]` binds, and so on. `chain_convoy` extends
  it only when the nested scrutinee *is* (term-equal to) the chain's end.
- **Re-anchoring rebuilds the constructor with its payload.** `Nat` §5.1
  convoys the `j`-th nesting at `Succ^{j-1}` of its scrutinee. Here the
  `j`-th nesting convoys at `C_{j-1}(payload_{j-1}, C_{j-2}(…, y))`, where
  each `C_i(payload_i, ·)` is the recursive constructor of the `i`-th
  enclosing arm applied to that arm's non-recursive aliases — all in scope,
  since they are the arm's own binders. The elaborator already builds
  constructor terms from a constructor and its fields (`constructor.rs`);
  reuse that, do not spell `sup` by hand.

The window stays anchored at `chain[0]` (§5.1's invariant); component `i` is
the value at `chain[i]`.

## 5. Sizing, refusals, what does not change

- `cov_depth` (name-based, sizing only — `Nat` §6) gains the `Wf` case:
  nested matches on the chain-end *name* whose arms call self at a deeper
  name. Wrong in either direction is still safe for the same reasons.
- A call deeper than the window, or on a binder off the chain, is refused
  with the message that names the mechanism.
- Container fields (`ContainerIh`) are out: an arm with one is not
  chain-shaped for this purpose and keeps today's behaviour.
- Not a kernel change; Σ/`fst`/`snd`/`elim_Wf` all exist.
- `decreases` and mutual recursion are untouched.

## 6. Round scope and acceptance

1. **Verify first, on a hand-lowered term**: write the depth-2 list window
   for one function (e.g. `alternate(xs)` summing every other element) as
   the elaborator would emit it and check it through the kernel gate before
   wiring the general path. If `tail_D` at a base constructor cannot be
   spelled with `z` in scope, STOP and report; that is the one assumption
   §2 makes about `const_elim_wf`.
2. The general path in `wf.rs`/`matching/routes.rs`/`recursion.rs` per
   §2–§5, with a `GuardKind::Wf` extension (a chain + window + comps +
   motive/gamma, mirroring `GuardKind::Nat`'s fields) rather than a third
   kind.
3. Tests in `crates/elab/tests/match_recursion.rs`, mirroring the `Nat`
   set: depth 2, 3 and 4 on `List` with a **dependent** motive each (the
   `Nat` design found that a non-dependent motive hides every anchoring
   bug), a two-depths-in-one-arm case, closed computation by `refl` with a
   wrong-value control, a nested `match` on another variable not extending
   the chain, a user chain-shaped inductive with two base constructors, and
   the tree refusal with its message.
4. **Customer**: `lib/std/utf8.hthr` — `decode_at` and its fuel go;
   `decode` recurses on `rest`, `rest2`, `rest3`, `rest4` directly. Theorems
   3–6 must close again (they should get *simpler*: no fuel arithmetic in
   `push_step`/`decode_at_encode_chars`), tests in
   `crates/elab/tests/lib_std_utf8.rs` unchanged in meaning. Keep
   `push_step` stated at `emit` (`issues/utf8-decode-conversion-blowup.md`
   is not this round's).
5. Update `docs/course-of-values-recursion-design.md` §8 to point here, and
   `issues/utf8-encode-decode-strictness.md`'s route if the fuel-free
   decoder changes it.

## 7. What the implementation corrected

Implemented 2026-09-18 (`crates/elab/src/wf.rs`, `matching/routes.rs`,
`recursion.rs`). Five amendments, each recorded against the section it
changes; everything else above stands as written.

1. **§2: `tail_D` goes through `build_elim_wf`, not `const_elim_wf`.** Tier 1
   §7's own correction applies to it verbatim: a constant motive frees the
   step from `ih` but *not* from `cs`, and reading a child out of `cs` needs
   the literal arity that only a tag branch has. `tail_D` is therefore a new
   `Branches::Tail` beside `Branches::Child` — it takes the one child at
   *every* recursive constructor, which `Child` cannot, since a chain-shaped
   declaration may have several (`Run { Stop, Halt, Step(p, next), Skip(next) }`).
   The one assumption §6.1 was to test held: the base arms' default is an
   ordinary term of the caller's, so the outer scrutinee goes there and
   `tail_D(Nil) ⇝ Nil`.

2. **§4: the constructor is rebuilt from the arm's own label.** Not by
   re-running `constructor.rs` — that builds from surface `Expr`s, and an
   arm's payload is a projection, not an expression. The arm already *has*
   its label `ℓᵢ`, so re-anchoring is `sup_f(ℓᵢ; (y, ⟨⟩))`: only the children
   tuple is new, and the payload travels as the label it already is. Nothing
   is re-elaborated, and the label cannot drift from the one the branch was
   entered under.

3. **New: the convoy carries *two* anchors.** `Nat` needs one because motive
   synthesis hands it the refined goal for free — the arm's value is `Succ k`
   and the nested scrutinee `k` is a subterm of it, so abstracting the
   scrutinee out of the goal refines it. A `Wf` arm's value is
   `sup_f(ℓ; cs')` and its child is `nth(cs'; ι₀)`, which is **not** a
   subterm; synthesis has to recover it from a *reduced* goal, and at depth
   three it does not. So the convoyed `match`'s codomain is built here
   instead: `M_outer[goal(z)]`, where `goal` is the enclosing arms'
   constructors rebuilt around `z` — including the recursion's own arm, which
   is exactly the constructor `window` stops one short of. The two differ by
   that one constructor and compose identically, `anchor_new(y) =
   anchor_old(Cᵢ(payload, y))`, so the deeper nesting costs no new case.

   Both are stored as λs. Their bodies mention the enclosing arms' payload
   binders, which are not ambient, so as λs they shift like ordinary closed
   terms; they are applied by substitution, and no β-redex reaches an
   annotation.

4. **New: a window arm's goal is spelled at the rebuilt constructor.** The
   telescope states the step at `sup_f(ℓ; cs')`; the window's components are
   built at `sup_f(ℓ; (child, ⟨⟩))` instead. The two are convertible — `cs'`
   is a one-element `Vec`, and η gives `(nth cs' ι₀, ⟨⟩) ≡ cs'` — and the
   rebuilt spelling is the one with the child as a *subterm*, which is what a
   nested `match` on it needs in order to refine anything at all. This is the
   same observation as (3) from the other side.

5. **§5: the depth scan is a max over the arms.** One motive serves every arm,
   so one width does: each recursive arm contributes the depth its own body
   reaches from its own child binder, and the window is sized for the
   deepest. The scan itself is the `Nat` one with the step generalized — a
   `Succ` arm's predecessor, or a recursive constructor's field binder — and
   it stays a sizing decision only, for the reasons `Nat` §6 gives.

Not needed, and so not done: no kernel change, no new `Branches` beyond
`Tail`, and `d = 1` still emits the term it always did — every `Wf` `match`
written before this one is byte-for-byte unchanged.
