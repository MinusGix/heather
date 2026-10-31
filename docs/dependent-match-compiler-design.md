# One dependent-match compiler

Design note for `issues/dependent-match-compiler.md` (item 2 of the
fundamental-improvements memo of 2026-10-31). The issue asks for one `match`
compiler that always gives each arm the equation `scrutinee = pattern`,
infers the motive by abstraction, infers non-dependent matches in inference
position, and compiles nested patterns to case trees with per-clause
equations. Its "done when" is this note, decided by Minus, with the slices
filed.

**Status: decided (2026-10-31, §13); slices 4, 1 and 3 implemented (§8.1, §4.3.1, §6.1).** No kernel change is needed and none is
proposed. Everything here is elaborator front end over the route lowerings
that already exist.

## 0. What this note decides

1. **§3: the one compiler is a front end, not a new lowering.** One
   `MatchProblem` pass decides the discriminant, the motive, the equation and
   the arms. The route back ends (Nat, Fin, declared data, indexed family,
   IWf, Empty, codata) stay as they are. They already consume a motive as an
   opaque type over one binder (`docs/match-equation-split-design.md`
   §1.1(a)), so a uniform front end costs them nothing.
2. **§4: the equation is in every arm, and it enters the term only when
   something reads it.** An arm sees an anonymous `scrutinee = pattern`, or
   `h` when the user writes `match h:`. If no arm reads it, the elaborated
   term is exactly today's. If an arm reads it, the match is re-elaborated as
   the convoy. Function bodies therefore keep their shape, and the
   whole-library measurement the issue asks for becomes "only the items that
   read an equation changed".
3. **§5: the motive is abstracted from the goal and from every local whose
   type mentions the scrutinee, for computed scrutinees too.** Today only a
   local variable scrutinee refines hypotheses
   (`Elaborator::refined_hypotheses`).
4. **§6: inference position infers a constant motive from any arm**, not only
   from an arm that binds nothing, and accepts `match h:`.
5. **§7: clause equations come from §4 + §5, with no composition proof.** A
   deep pattern already compiles to nested matches on column variables
   (`patterns.rs`). The outer equation mentions those columns, so once §5
   refines it at each inner level, the leaf sees `s = C(x, D(y, t))`.
6. **§8: the `decreases` unfolding walk learns one node, the convoyed match.**
   A variable-scrutinee match becomes the special case where the equation
   goes unused.
7. **§9: on an indexed family the equation is the packed one,**
   `⟨i, s⟩ = ⟨idx(C), C(…)⟩` in `Σ(i: I). F(i)`. It is homogeneous, so it
   replaces the refusal in `docs/match-equation-split-design.md` §4.
8. **§10: written motives become overrides**, and the library sweep removes
   the ones that are redundant. A sample of 379 shows that 47% are redundant
   today (§1.2).

## 1. Census (master `35b223d`, 2026-10-31)

### 1.1 The library

| what | count |
|---|---|
| `match`/`split`/`if` keywords in `lib/` | 6525 |
| written motives `as λ` | 1443 |
| written equation bindings `match h:` | 28 |
| hand convoys applied to `refl` (`…})(refl)`) | 145 |
| matches applied to arguments (`…})(`) | 356 |

The written motives, classified by shape (script over the motive text, 1443
found, 1443 classified):

| shape | count | what it is |
|---|---|---|
| dependent, with an arrow (`λ z => H(z) → G(z)`) | 601 | a hypothesis carried into the motive by hand, so that it is refined (§5) |
| non-dependent (`λ _ => T`) | 339 | mostly inference position (§6), some redundant in checking position |
| equation convoy (`λ z => (e = z) → M(z)`) | 259 | the equation written by hand (§4) |
| dependent, no arrow | 244 | the goal names the scrutinee, often only after unfolding a callee |

The 259 equation convoys and most of the 601 arrow motives are exactly what
§4 and §5 write for the user. `lib/std/text/decimal.hthr`'s `leb_no` is the
issue's example:
`(match a.leb(b) as λ found => (a.leb(b) = found) → found = False { … })(refl)`.

### 1.2 How many written motives are already redundant

`heather check --cache --review` runs the redundant-motive lint
(`issues/lint-redundant-match-motive.md`). It removes each written motive in
checking position, re-elaborates, and kernel-checks the result. On five
files:

| file | written motives | redundant today |
|---|---|---|
| `lib/std/num/float/round.hthr` | 170 | 122 |
| `lib/kernel_model/kernel_runs.hthr` | 45 | 33 |
| `lib/native/function_ir/function_ir_lower.hthr` | 32 | 21 |
| `lib/std/text/utf8.hthr` | 43 | 4 |
| `lib/std/bitvec/bitvec.hthr` | 89 | 0 |
| **total** | **379** | **180 (47%)** |

`bitvec.hthr`'s motives are recursions on the width, `λ k => BitVec(k) → …`,
where the goal is a function type over the index. Those are genuinely
needed until the motive can be read off a Π over the index. The other 47%
are historical: the synthesis ladder
(`docs/goal-motive-synthesis-design.md`), IH generalization and hypothesis
refinement landed after they were written. So the sweep (§10, slice 7) is
large even before any new inference.

### 1.3 The open issues

Forty-one open issues have `match`, motive, convoy, equation, pattern,
unfolding or `split_all` in their titles. Section 11 maps each one to the
slice that closes it, or says why it is not this round's.

## 2. What exists today

The pieces are good. What is missing is that they are opt-in and
position-dependent.

- **Checking position**, `lib.rs` `elab_check_skel_slots`,
  `ExprKind::Match { motive: None }`:
  1. infer the scrutinee;
  2. IH generalization: varying parameters of a structural recursion
     (`generalize.rs` `varying_params`);
  3. hypothesis refinement, but **only when the scrutinee is a local
     variable** (`refined_hypotheses`), and only for hypotheses an arm names
     or the goal mentions;
  4. `matching::synthesize_motive`'s ladder: abstract the scrutinee from
     the goal as written, then as a field rewrap, then from the exposed goal
     up to conversion at stuck positions;
  5. `elab_match`, or `elab_convoy` when `match h:` is written.
- **Inference position**, the same file: a written motive is elaborated by
  route (IWf, indexed, plain). A motive-less match goes to
  `infer_match_constant_motive`, which takes its type from **an arm that
  binds nothing**, and only when there is no equation binding.
- **`elab_match`** (`matching/routes.rs`): `prepare_arms` compiles deep
  patterns and `_` into nested surface matches on column variables
  (`patterns.rs`, motive `None`, `generated: true`). It then dispatches on
  the scrutinee's type to `elab_match_iwf`, `elab_match_indexed`,
  `elab_match_data`, `elab_match_fin`, `ElimEmpty` or `elab_match_nat`.
- **The convoy**, `matching::plan_convoy` / `finish_convoy`: motive
  `Π(e = z). M`, arms wrapped in `λ h =>`, applied to `refl`. It is
  type-transparent and used by `match h:`, by `split_all`
  (`elab_convoy_dependent`) and by the measure rewrite's `__dec_eq`
  refinements (`measure.rs` `refining_match`).
- **The measure rewrite** (`measure.rs`) let-binds a computed scrutinee as
  `__dec_scrut_N`. That is an alias, so it is not a generalization, and the
  arm gets an equation only when the refined measure mentions the scrutinee.
- **The unfolding walk** (`measure.rs` `match_at_anchor`,
  `docs/decreases-unfolding-design.md` §3) re-matches a variable scrutinee
  under `λ s => lhs(s) = rhs(s)`. It refuses a computed scrutinee, a written
  motive and an equation binding.
- **Course-of-values windows** (`chain_convoy`, `wf_chain_convoy`) and
  `split_all` each build convoys of their own on top of the same pieces.

### 2.1 Probes on master

Each of these was run with the release CLI on `35b223d`. The probe files are
in §12.

| # | program | today |
|---|---|---|
| P1 | `match n.leb(3) { …, False => absurd(h) }` with `h: n.leb(3) = True` | refused: `h` is not refined at a computed scrutinee (§5) |
| P2 | `match a.leb(b) { True => …, False => refl }` with no `h:`, where the `True` arm needs `a.leb(b) = True` | no equation in scope (§4) |
| P3 | `let x = match t { A(n) => n, B(m) => m }` | "`match` in inference position needs a motive", because every arm binds (§6) |
| P4 | `match h: mk(n) { Cons(x, Cons(y, t)) => { let k: (mk(n) = Cons(x, Cons(y, t))) = h; … } }` | **the elaborator accepts it and the kernel rejects it** (`NotConvertible`): `h` is the one-level equation `mk(n) = Cons(x, #col)` (§7) |
| P5 | `#316`'s `count_down` with `match h: Nat::leb(s.m, 0)` | the function checks; `count_down_unfold` is refused because the lifted `#obl_1` does not take `h` (§8) |
| P6 | the same function **without** `h:` | refused: the obligation `n - 2 < n` has no guard to read (§4, §8) |

P4 is a soundness-of-diagnostics defect (the elaborator believes something
the kernel does not). It is filed separately as
`issues/eqbind-deep-pattern-kernel-rejects.md` and owned by slice 5.

## 3. The front end

A match is compiled in four steps. Every surface form takes them: `match`,
`split`, `if`, `if let`, a generated match from `prepare_arms`, the measure
rewrite, `split_all` and the course-of-values windows.

```
MatchProblem {
    scrutinee: Term, scrutinee_type, level,
    discriminant: Var(x) | Computed,         // §3.1
    motive: Type over Γ, z  (+ generalized locals),   // §5
    equation: Anonymous | Named(h) | Off,    // §4
    arms: Vec<Arm>,                          // after prepare_arms
}
```

1. **Discriminant.** A local variable is its own discriminant. Anything
   else is abstracted: the motive binds `z`, and the equation relates the
   original term to `z`.
2. **Motive (§5).** The written motive if there is one, otherwise the
   synthesis ladder over the generalized goal. The locals that mention the
   scrutinee are generalized into that goal first.
3. **Equation (§4).** In scope in every arm. In the term only when read.
4. **Lowering.** `elab_match`'s dispatch, unchanged.

This is close to what `elab_check`'s motive-less arm already does. The work
is to make it the only path: the inference arm, the written-motive arm,
`split_all`'s convoys and the measure rewrite should go through it rather
than through their own combinations of the same calls. Section 10 says
which parts of today's code become callers of this one.

## 4. The equation, always in scope, paid for when read

### 4.1 The rule

Every arm of every match has the hypothesis `scrutinee = pattern`, in that
direction (`docs/match-equation-split-design.md` §3.2: `refl` inhabits it
without a `sym`).

- With `match h: e`, it is named `h`, as today.
- Without it, it is anonymous. The name is reserved: it cannot be spelled in
  source, so it cannot collide with or shadow a user binder. It is visible to
  the readers of hypotheses: `omega` and `linarith` (as a fact), `split_all`,
  `rewrite`'s hypothesis search, `absurd`'s search and goal display.

`omega`'s certificates are source and cannot name a `#` binder
(`omega_cert.rs` `local_fact_entries`). The anonymous equation therefore
gets a `__`-reserved name, as `__omega_local_N` does. Shadowing between
nested matches is already handled by `source_context`'s renaming.

### 4.2 Why not just convoy every match

A convoy changes the term: `elim(e, Π(e = z). M, λ h. bᵢ)(refl)` is not
convertible with `elim(e, M, bᵢ)` at a neutral `e`. A `match` in a function
body is a computation, and statements restate it. So does a motive that
spells a callee's body (244 such motives, §1.1). `refined_hypotheses`
already avoids this for exactly that reason: it refines only a hypothesis
something reads. Native compilation reads function bodies too
(`function_ir_source`), and a convoy there is a new shape for it to
recognise. Convoying everything would also enlarge every term in the
library, which is the issue's own warning.

### 4.3 How "read" is decided

The equation starts as a **pending** hypothesis. It is in the arm's `Cx`,
so names resolve to it and tactics list it, but it is not in Γ and there is
no convoy. The first time anything resolves it, a `MatchEquationWanted`
signal carrying the match's identity unwinds to that match. The match then
rolls back its speculation (`MatchRollback`, the same transaction the
constant-motive probe uses) and re-elaborates as the convoy, with the
equation a real binder.

- Code that never touches the equation pays nothing, which covers almost
  all function bodies.
- A match whose arm names `h` pays one aborted arm elaboration. That arm
  needed the convoy anyway.
- `omega` lists every local fact, so an arm that runs `omega` reads the
  equation even when its certificate turns out not to cite it. This
  over-approximation is safe: the cost is one unused λ in a proof. To keep
  a function body's term stable, the pass re-elaborates without the
  equation when it was listed but never cited. That case is bounded (an
  `omega` obligation inside a function-body match) and measurable.
- Nested matches each have their own identity, so an inner request unwinds
  only the inner match.

The alternative was a syntactic trigger: convoy when an arm names `h` or
contains a tactic. It is simpler, but it is wrong in both directions. A
macro or generated arm can read hypotheses without a visible tactic, and an
arm can contain `omega` that reads nothing. The pending binder is exact for
names and conservative only for fact listing.

### 4.3.1 As implemented (slice 1, 2026-10-31)

The pending binder landed in a narrower form than §4.3, which the slice
showed to be enough for the readers that exist.

- **Elaborator.** A motive-less `match` with no `h:` on a non-indexed
  scrutinee (`Elaborator::elab_match_pending`, `lib.rs`) pushes an id onto
  `Cx::pending_eqs` and elaborates as today. `omega` (`elab_omega`) and
  `linarith`, when they get stuck, mark every pending id in scope as wanted
  (`Attempt::match_eq_wanted`). Marking at listing time instead
  re-elaborated every failing arm that ran `omega`, which made a
  refusal-heavy test about a third slower. No
  signal unwinds: the arm runs to its end. Only if it fails, and a reader
  wanted the equation, does the match roll back and re-elaborate as the
  convoy with the equation bound as `__match_eq` (`MATCH_EQ`). If the retry
  fails too, the first error is reported.
- **What that buys.** An arm that listed the equation and succeeded without
  it keeps its plain term. That is §4.3's "listed but never cited" case,
  with no second pass. The convoy appears only where the arm cannot
  succeed without it.
- **What it leaves out.** The anonymous equation is not resolvable by name,
  since `__match_eq` cannot be written. `split_all`, `rewrite`'s hypothesis
  search and `absurd` do not mark it wanted yet. Each is one call to
  `want_match_equations` when a customer needs it.
- **`decreases` bodies.** A lifted obligation is stated over the telescope
  the body rewrite writes (`measure.rs`), not over the elaborator's `Cx`, so
  the pending binder cannot reach it. There the rule is applied to the
  rewrite itself (`AutoEqs`):
  - A candidate is a plain `match` on a computed scrutinee, with no
    equation binding and a recursive call in an arm.
  - The declaration is lowered with every candidate bound as `__dec_meqN`.
    It is lowered again with only the candidates whose equation a lifted
    obligation quantifies, which `measure_local_evidence`'s trial decides.
  - The companions are generated under the same choice. A candidate nobody
    reads keeps its plain match in `f#body`.
  - `Respell::convoy_at_anchor` lets the two sides of the walk carry
    different equations, since `f_unfold`'s right side is the source, which
    binds none.
- **Probes.** P2 checks (`omega_tests.hthr` `guard_unnamed_in_arm`, with a
  negative control). P6 checks, and `half_unfold` is generated (same file,
  `half_step`). Both are refused on master.

### 4.4 What it retires

- The 259 hand-written equation convoys and the 145 `(refl)` applications:
  `leb_no` becomes `match a.leb(b) { True => { …omega… }, False => refl }`.
- P2 and P6: `half` in §12 checks with no `h:`. The measure rewrite's
  obligation sees the anonymous guard (`omega` reads `b = False` since
  PR #316).
- The `__dec_eq` refinement in `measure.rs` becomes the general equation
  (slice 4).

## 5. The motive by abstraction, for every local

`refined_hypotheses` generalizes the later binders whose type mentions a
local-variable scrutinee, provided an arm names them or the goal mentions
them. Each arm then sees them at its constructor, in the kernel's term and
not only in the elaborator's display. Three changes:

1. **A computed scrutinee is abstracted the same way.** A binder whose type
   contains the scrutinee term (`==`, as the ladder's rung 1 decides
   occurrence) is generalized. Its type becomes `T[z/e]` in the motive. The
   scrutinee may only mention binders that precede it, which is a necessary
   condition checked first. This is P1.
2. **The selection rule stays.** Generalize what an arm names or the goal
   mentions, plus what those depend on. This is the same cost argument as
   §4.2: a hypothesis nobody reads should not change the term.
3. **The pending equation of an enclosing match is a local like any other.**
   So an inner match on a column refines the outer equation. This is what
   §7 needs.

Rung 3 of the ladder (conversion at stuck positions) is not used for
hypotheses. A hypothesis is a fact the author wrote, so a syntactic
occurrence is what they can see, and conversion candidates are budgeted
for the goal alone (`STUCK_CANDIDATES`).

## 6. Inference position

`infer_match_constant_motive` takes the first arm that binds nothing and
infers. The change: **any arm** is a candidate. It is elaborated in its own
binder context and its type is strengthened past those binders. A type that
mentions a binder is not a constant motive, so that arm declines and the
next one is tried. The first candidate whose whole match checks wins, as
today, inside the same speculation. `match h:` in inference position
becomes allowed: its motive is the constant one and the equation is §4's.

This closes P3, which is the sequencing design's probe P2
(`docs/sequencing-surface-design.md` §5.1: "the annotation is required").
It also removes a large share of the 339 `λ _ => T` motives.

A dependent match in inference position still needs its motive. Inferring
one from the arms would need higher-order unification, which is
`issues/elab-unifier-completeness.md`'s and not this round's.

### 6.1 As implemented (slice 3, 2026-10-31)

- **The probe.** When no non-binding arm infers, `matching::probe_arm_type`
  lowers the match once, through its ordinary route, at a marker motive:
  `Unit` at a universe variable no declaration binds. `Cx::arm_type_probe`
  carries the sink.
- **The interception.** `elab_check` intercepts a body checked against the
  marker in a context with the probe set. It infers the body instead, then
  strengthens the type past the binders the route pushed
  (`matching::strengthen_past`, the same substitution test the `if` probe
  uses).
  - The first arm whose type survives, and mentions no marker level (an arm
    returning its own `ih`), is recorded, and the lowering stops.
  - An arm whose type mentions a binder gives a dummy term, and the route
    goes on to the next arm.
- **Why this way.** Every route (`Nat`, data, `Fin`, deep patterns, W and
  indexed families) builds its own arm contexts. The probe reuses them all,
  rather than recomputing field types per route. The whole lowering is
  rolled back. The real lowering then runs at the constant motive found, as
  before.
- **`match h:` in inference position.** The same search runs, and the real
  lowering is `elab_convoy` at the constant motive
  (`ConstantMotiveElab::lower_constant_convoy`). The probe at the marker goes
  through the convoy too, so an arm that reads `h` is probed in a context
  where `h` is bound.
- **Tests that pinned the old refusal.** `motive_synth.rs`
  `every_arm_binding_still_asks_for_a_motive` became the positive test. Its
  negative control is now an arm type that mentions its binder. The three
  receiver probes in `records.rs` use arms that do not infer at all.

## 7. Clause equations

`prepare_arms` turns `Cons(x, Cons(y, t)) => b` into
`Cons(x, #c) => match #c { Cons(y, t) => b, … }`, with `generated: true`.
With §4 the outer level has `#e₁ : s = Cons(x, #c)`, and the inner level
has `#e₂ : #c = Cons(y, t)`. With §5 the inner match is on a **local
variable** (`#c`) that `#e₁` mentions, so if anything reads `#e₁` it is
refined. In the inner arm it is `s = Cons(x, Cons(y, t))`. That is the
clause equation, with no `trans` or `cong` written.

What remains is naming. `match h:` binds `h` to the outermost equation, and
the refinement makes it the clause equation at the leaf. The inner levels'
equations stay anonymous. This also fixes P4: today the inner generated
match does not refine `h` in the term, yet the elaborator accepts the
annotation, which is the same class of defect as the closed
`elab-match-refines-hypothesis-kernel-rejects`.

The `decreases` walk then needs no special case for nested patterns. It
sees nested convoyed matches on variables (§8).

## 8. Unfolding through a convoyed match

The walk (`docs/decreases-unfolding-design.md` §3) re-matches a variable `v`
under `λ s => lhs(args[v ↦ s]) = rhs(args[v ↦ s])`, and both anchors reduce
into the arm. A computed scrutinee reduces neither, which is why `merge`,
`decimal` and `cd_loop` get no `_unfold`.

With §4, a match whose equation is read is a convoy:
`elim(e, Π(p: e = z). M, λ p. bᵢ)(refl)`. Abstract the convoy's own
eliminator: for a fresh `s` and `p: e = s`, the two renderings
`elim₁(s)(p)` and `elim₂(s)(p)` are the bodies at a **variable**
scrutinee. So the walk proves

```
elim(s, λ s => Π(p: e = s). elim₁(s)(p) = elim₂(s)(p),
     C(x̄) => λ p => ⟨walk of the arm with p in scope⟩)  (e)(refl)
```

In each arm both sides step, because the eliminator is at a constructor,
and the arm's walk has `p` in scope at its pattern. This is the
variable-scrutinee rule with one more binder. A variable scrutinee whose
equation nobody read is the old rule, unchanged.

Two more parts:

- **Lifted obligations quantify over the arm's equation.**
  `measure::arithmetic_fact` already accepts a Bool equation since PR #316.
  The missing piece is that `f#obl_N`'s telescope does not include an
  equation binder (P5). After §4 every arm has one, and it joins the
  telescope when the obligation's trial elaboration reads it.
- **The equation's proof at the anchor is `refl`**, bound by the same `let`
  spelling the walk already uses for `__dec_eq` (§5 of the unfolding note).

Closes `unfolding-computed-scrutinee`, generates `cd_loop_unfold` and
`count_down_unfold`, and unblocks R3b of `pure-imperative-statements` (the
`while … decreases` lowering, sequencing design §7.3).

### 8.1 As implemented (slice 4, 2026-10-31)

Slice 4 landed ahead of slice 1, on what the surface already writes: a
`match h:` equation binding on any scrutinee, and a computed scrutinee
without one. `measure.rs` `Respell::convoy_at_anchor` is the node.

- **Rendering.** `L(s, q)` is `f#body`'s own spelling of the match. A fork of
  the body rewrite (`Rewrite::fork`) produces it, with the same obligation
  numbering and transports and without advancing the walk. `__dec_k`,
  `__dec_ih` and `__dec_h` are then replaced by the anchor's arguments. In
  `f_unfold`, `__dec_ih` becomes the partial application `f#rec(e)`, since
  every use of the ih is a call and a λ would need annotations.
- **Arm anchors.** Inside such an arm, `f#rec(…)` does not reduce, so
  `Respell::anchors` holds the two arm bodies, and the anchors of a nested
  variable match are taken from them.
- **Enclosing refinements.** The rendering names their `__dec_eq`
  binders, which are bound to `refl` by `let`s around the proof, as a leaf
  binds them.
- **Lifting.** Two fixes were needed:
  - The body rewrite let-binds a computed scrutinee as `__dec_scrut_N`, and an
    arm's equation used to be stated about that name. A lifted obligation
    has no `let`, so there the name was an unrelated parameter (the root
    cause of P5). The equation is now stated about the expression.
  - Any arm equation is a candidate fact, where before only `b = True` or
    `b = False` were. The refinement's own `__dec_eq` is excluded.
- **Still refused:** a `_` arm around a recursive call, a recursive call in a
  scrutinee, and a written motive.

The anonymous equation of slice 1 reaches this node with one change
(§4.3.1): the two sides may carry different equations, and an anchor that is
an arm's plain `match` is given its constant motive, since it stands on one
side of the motive's `=`.

## 9. Indexed families: the packed equation

`docs/match-equation-split-design.md` §4 refuses `match h:` on an indexed
family because `s = C(…)` would relate values at two indices. The
homogeneous statement exists: pack the index with the value,

```
⟨i, s⟩ = ⟨idx(C, x̄), C(x̄)⟩ : Σ(j: I). F(j)
```

It lives at one type, it is `refl` at the scrutinee, and the convoy's
motive `λ j z => Π(p: ⟨i, s⟩ = ⟨j, z⟩). M(j, z)` is an ordinary two-binder
family motive (`elab_match_indexed`, `elab_match_iwf` already take one).
Readers get the index equation as `cong(fst, p)` and the value as a
transport, which is what an inversion lemma states by hand today. This is a
slice of its own (slice 6) because `iwf_match_motive`'s index inversion
(tiers 1–2) has to commute with it. Until then the anonymous equation is
simply absent on indexed families, which is today's behaviour minus the
error.

## 10. Written motives become overrides

`as λ z => M` stays the surface for a motive the front end cannot recover.
The cases are a dependent match in inference position (§6), a goal that
needs more than one unfolding, and a Π over an index (`bitvec`). It replaces
step 2 of §3 and nothing else: generalization (§5) and the equation (§4)
still apply around it, as `match h: e as λ z => M` does today.

The sweep (slice 7) runs `heather check --review` over the library and
applies the lint's deletions. It then rewrites the hand convoys whose
equation §4 now supplies, and the arrow motives whose hypothesis §5 now
refines. Each step is a `--source-patch` A/B (`scripts/perf ab`).

What stops being its own code:

| today | becomes |
|---|---|
| `elab_check` motive-less arm, `elab_infer` written-motive arm, `infer_match_constant_motive` | the front end's motive step |
| `elab_convoy`, `elab_convoy_dependent`, `plan_convoy`/`finish_convoy` | the equation step's convoy (kept as the mechanism) |
| `measure.rs` `refining_match` / `__dec_eq`, `__dec_scrut_N` | the equation step |
| `split_all`'s convoys (`goal_combinators`) | callers of the front end |
| `chain_convoy` / `wf_chain_convoy` windows | unchanged in this round; their equations become §4's when `cov-*` is picked up |

## 11. Slices, and which open issues each closes

Each slice is a PR with its own tests: positive, negative control,
checking and inference position, a literal and a neutral scrutinee and an
open element type (`docs/testing-generated-terms.md`).

| slice | issue filed | closes / retires |
|---|---|---|
| 1. Pending equation in every arm (§4) | `match-equation-in-every-arm` | P2, P6; `leb_no`-style convoys become writable without the convoy; groundwork for 4, 5 |
| 2. Generalize locals at a computed scrutinee (§5) | `match-refines-computed-scrutinee` | P1; `split-all-revise-hypotheses` (its splits go through the front end); `cov-window-in-theorem-arms`' first half |
| 3. Constant motive from any arm; `match h:` in inference position (§6) | `match-infers-constant-motive` | P3 (sequencing P2) |
| 4. Unfolding through a convoyed match (§8) | `unfolding-through-convoyed-match` | `unfolding-computed-scrutinee`, P5; unblocks R3b of `pure-imperative-statements` |
| 5. Clause equations (§7) | `match-clause-equations` | P4 / `eqbind-deep-pattern-kernel-rejects` |
| 6. Packed equation on indexed families (§9) | `match-equation-indexed-family` | the §4 refusal of the equation-split design |
| 7. Motive and convoy sweep (§10) | `match-motive-sweep` | `match-motive-surface-audit`'s census, `uncurried-recursions-library-sweep`'s remaining motives, most of `lint-match-function-application`'s sites |

Slices 1 and 3 are independent. 2 is independent of 1. 4 and 5 need 1, and
5 also needs 2. 7 should go last, so that it removes what 1–3 made
redundant in one pass.

### 11.1 The other open issues

| issue | relation |
|---|---|
| `convoyed-window-vs-written-motive`, `cov-convoy-motive-second-ambient` | course-of-values windows: they keep their own convoy this round (§10) |
| `nested-match-on-list-tail-motive`, `wf-nested-match-motive-synthesis-kernel-refusal` | nested motive-less matches whose binder types are not specialised. Plausibly slice 2 (the tail binder's dependents are locals that mention it), to be checked there and not claimed here |
| `deep-pattern-dependent-later-field` | slice 5 neighbourhood: the column's later field depends on it, which is §5's dependent-locals rule. Checked in slice 5 |
| `split-all-through-decisions`, `split-all-through-recursive-definitions`, `omega-guard-reads-nat-match`, `bv-omega-definition-summaries` | tactic search for *which* match to split. The front end changes what a split builds, not what it finds |
| `group-unfolding-equations` | the mutual walk; slice 4's convoy node is reusable there |
| `if-let-negative-evidence` | the failure branch's evidence is a negation, not `s = pattern`; separate |
| `result-propagation-dependent-motives` | written motives through `?`; separate, though §10 makes fewer motives written |
| `recursion-guard-takes-nearest-parameter-match`, `guard-matches-self-calls-by-term` | termination analysis, orthogonal |
| `iwf-inversion-recursive-index` | index inversion; slice 6 must commute with it, does not close it |
| `elab-emits-normal-form-of-matched-type-argument`, `conv-query-identity-env-per-gamma`, `list-instance-match-wf-sigma-decline` | performance of matching, orthogonal |
| `match-code-recursive-motive-level-mismatch`, `and-at-match-predicate-implicit-level-mismatch`, `generic-congruence-inferred-type-arg-level-mismatch` | level inference defects, orthogonal |
| `inner-column-diagnostic-span`, `lint-redundant-match-motive`, `lint-vacuous-match`, `tree-sitter-match-code-scrutinee`, `rewrite-pattern-occurrences`, `special-forms-as-declarations`, `interface-definitions`, `elab-unifier-completeness`, `surface-syntax`, `have-rhs-ignores-let-shadowing` | adjacent; unaffected (title matched the census search only) |

## 12. Cost, and how it is measured

The rule of §4.2 is what keeps the cost bounded. An item whose matches read
no equation and refine no new local elaborates to the **same term**. So
each slice is checked as follows:

- **Whole library, counters.** A `--timings` run before and after, compared
  with `scripts/timings --diff`. Identical count columns prove that items
  are unchanged. The items that move are listed in the PR and must be the
  ones that read an equation or refine a local.
- **The probes.** Copies of P1–P6 go to `lib/_tests` as
  probes (positive) and `expect-error` controls (negative) in the slice
  that closes each one.
- **Slice 7** is a pure library change, measured with
  `scripts/perf ab --source-patch`.

The pending-equation abort (§4.3) re-elaborates one arm per match that reads
its equation. The library has 28 named equations and 145 hand convoys, so
the re-elaborations are a few hundred arms at most. That is measured in
slice 1, not assumed.

### 12.1 Probe sources

```heather
// P1
theorem comp_hyp(n: Nat, h: n.leb(3) = True): n <= 3 {
    match n.leb(3) { True => omega, False => absurd(h) }
}
// P2
theorem anon_eq(a, b: Nat, h: b < a): a.leb(b) = False {
    match a.leb(b) { True => absurd(h), False => refl }
}
// P3
inductive Two { A(n: Nat), B(m: Nat) }
fn all_bind(t: Two) → Nat { let x = match t { A(n) => n, B(m) => m }; x }
// P4
fn mk(n: Nat) → List<Nat> { [n, n] }
theorem deep_eq_comp(n: Nat): Nat {
    match h: mk(n) {
        Cons(x, Cons(y, t)) => { let k: (mk(n) = Cons(x, Cons(y, t))) = h; y },
        _ => 0
    }
}
// P5
record CdState { m: Nat, out: List<Nat> }
fn cd_loop(s: CdState) → CdState decreases s.m {
    match h: Nat::leb(s.m, 0) {
        True => s,
        False => cd_loop(CdState(s.m - 1, Cons(s.m, s.out))),
    }
}
theorem uses(s: CdState): cd_loop(s) = cd_loop(s) { let e = cd_loop_unfold(s); refl }
// P6
fn half(n: Nat) → Nat decreases n {
    match Nat::leb(n, 1) { True => 0, False => Succ(half(n - 2)) }
}
```

(P2's `True` arm is written `absurd(h)` above, which is today's
diagnostic. With slice 1 the arm is `omega`, reading `h` and the anonymous
`a.leb(b) = True`.)

## 13. Decisions

Decided 2026-10-31. Minus left the choice to what is best for the language,
and the recommendations below were taken.

1. **§4.2–4.3: the equation enters the term only when read.** A pending
   binder is re-elaborated as the convoy on first read; the alternative was
   convoying every match. Function bodies keep their shape, and the library
   measurement becomes a counter diff.
2. **§4.1: the anonymous equation is visible to tactics but not spellable**
   in source. A fixed spellable name such as `eq` would shadow user binders.
3. **Slice order**: 4 first (landed, §8.1), then 1, 3, 2, 5, 6, and 7 last.
