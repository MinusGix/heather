# Unfolding equations for `decreases`-defined declarations

`issues/decreases-unfolding-equations.md`. A `fn f(x̄) -> T decreases e { body }`
is one `elim_Nat` on a bound (`docs/language/recursion/termination-measures-design.md` §1). At an
open argument the eliminator still *steps* — `Succ(e)` is a constructor
whatever `e` is — so `f(x̄)` reduces to the body; what it does **not** reduce to
is the body's self-calls spelled as `f(ȳ)`. Inside, a self-call is the recursor
at the bound's predecessor under a transported proof. So

```
theorem hv_id(n: Nat): hv(n) = n {           // hv(n) = match n { 0 => 0, Succ k => Succ(hv(k)) }
    match n { Zero => refl, Succ(k, ih) => nat::cong_nat(λ x => Succ(x), ih) }
}
```

is refused (`NotConvertible`, probed), and every proof *about* a
`decreases`-defined function at an open argument is refused with it. This
round generates the equation that unblocks them:

```
theorem f_unfold(x̄): f(x̄) = body[f]
```

with `body` the body **as written** — self-calls plain `f(ȳ)`, no `__dec_…`
anywhere (§5) — and with `hv_id` above going through once its two `refl`s
become `hv_unfold(0)` and `hv_unfold(Succ(k))`. Both halves of that pair are
probed end to end (§7).

## 1. The obstruction is real, and the shape of the fix is forced

Write `F` for the recursor and `B` for its `Succ` arm, so that
`F(Succ k, x̄, h) ≡ B(k, λ ȳ p. F(k, ȳ, p), x̄, h)` (probed: `refl`) and
`f(x̄) ≡ F(Succ(e[x̄]), x̄, lt_succ_self(e[x̄]))`. Then

- `f(x̄)` reduces to `B` with the ih at bound `e[x̄]`,
- `body[f]` is `B` with each self-call at bound `Succ(e[ȳ])`,

so the equation is exactly **bound irrelevance**, `F(n, x̄, h) = F(m, x̄, h')`,
pushed through the body. Bound irrelevance is proved by induction on `n` with
`m` generalized into the motive; its `Succ`/`Succ` case is
`B(k, F(k), …) = B(l, F(l), …)`, which needs the two ihs to be interchangeable
*inside* `B`. That is the functional-extensionality obligation every
well-founded-recursion story owes (Coq's `Fix_eq` takes it as the hypothesis
`F_ext`; Lean gets it from `Prop` proof irrelevance on `Acc`).

Heather has neither. There is no funext in `lib/` and none is wanted
(`docs/inductives/branching-inductives-choice.md` route A was declined on exactly this
axiom), and definitional irrelevance is a property of *fixed kernel formers*
(`docs/kernel/sprop-design.md` §1) — `nat::Lt` at open arguments is a stuck neutral,
so two proofs of it are not convertible, and no squashing of the bound
hypothesis rescues the argument because the two **bounds** genuinely differ,
not just the two proofs.

**Decision.** Generate the extensionality proof instead of assuming it. We
wrote the body, so we can walk it: a congruence proof over the body's own
structure, with the self-call sites as its leaves. Nothing is added to the
kernel and no axiom is taken.

## 2. What is generated, and why the recursor is a named global

For `fn f(x̄) -> T decreases e { body }` the elaborator now emits, in order:

| name | statement |
|---|---|
| `f#obl_N` | `(the binders it names) -> nat::Lt(e[ȳ], e_i)` — one per self-call site, the obligation lifted (§4) |
| `f#body` | `(__dec_k: Nat, __dec_ih: (x̄) → nat::Lt(e, __dec_k) → T, x̄, __dec_h: nat::Lt(e, Succ(__dec_k))) -> T` — the rewritten body of §1/§3 of the measures doc, verbatim |
| `f#rec` | `(__dec_z: Nat) -> (x̄) → nat::Lt(e, __dec_z) → T` — the `elim_Nat`, whose `Succ` arm is `λ x̄ h => f#body(k, ih, x̄, h)` |
| `f` | `f#rec(Succ(e), x̄, nat::lt_succ_self(e))` |
| `f#ext` | `f#body(a, g1, x̄, h1) = f#body(b, g2, x̄, h2)` given `hg : (ȳ) → (p) → (q) → g1(ȳ,p) = g2(ȳ,q)` |
| `f#irrel` | `f#rec(z, x̄, h1) = f#rec(w, x̄, h2)` |
| `f_unfold` | `f(x̄) = body[f]` |

`f`'s own lowering therefore changes shape: the eliminator moves out of the
declaration into `f#rec`. This **amends `docs/language/recursion/termination-measures-design.md`
§1 and §5** and is not free-floating — it is what makes `f#irrel` statable at
all. Two lifted helpers, not zero:

- `f#irrel`'s *statement* names the recursor. Re-spelling the inline recursor
  there (and again in `f#ext`, and again in `f_unfold`) would inline the whole
  body three more times and re-run the obligation solving in each, in a
  *statement* — where an unsolved `?decN` has no `on` to reach it.
- `f#ext` is about the arm, not the recursor, and wants the arm alone.

Nothing is lost by lifting: `F(Succ k, x̄, h) = B(k, λ ȳ p. F(k, ȳ, p), x̄, h)`
is `refl` (probed), a `fn` is transparent, so `gcd(12, 8) = 4` still computes
by `refl` through the indirection.

`#` in a minted name is the existing precedent (`{name}#skel`,
`crates/elab/src/inductive.rs`) and `#` never begins a surface identifier, so
the three helpers are unspellable by construction — the weak form of
`issues/unnameable-generated-names.md` that costs nothing here. `f_unfold` is
deliberately *on the other side of that line*: it is the artifact users cite,
so it is an ordinary name (`List::nth_unfold` for a member). A user
declaration already holding that name is a hard error naming the collision,
not a silent overwrite.

## 3. Generation is by re-spelling surface source, as the lowering is

`measure.rs` builds surface `Expr`/`Decl` values and hands them to the ordinary
checker; the companions are built the same way and for the same reason —
everything they need (`match` with a written motive, the equation binding,
`j`, `nat::le_trans`) is surface the user can write, and a mis-generated proof
is refused by the checker rather than trusted. Two consequences the probes
pinned:

- **The proof terms must be re-spelled exactly, not equivalently.** `sym` is a
  `theorem` and a `theorem` is opaque, so `sym(refl)` does *not* reduce to
  `refl`: a congruence step that spells the obligation transport in its
  reduced form is refused (`NotConvertible`, probed), while one that spells
  `j(@sym<Nat>(p, p, refl), …)` — the convoy's own shape with the arm's
  equation instantiated — is accepted. The walk that emits the companion is
  therefore the *same* walk that emitted the body, carrying the same
  refinement stack (`measure.rs`'s `Rewrite::refinements`), with each
  enclosing equation variable replaced by `refl` at the arm's pattern.
- **Congruence is spelled with `j`, not with a `cong_*` lemma.** `T` is
  arbitrary; `nat::cong_nat` happens to work for a `Nat`-valued probe, and the
  type-generic `j(p, λ y _ => C[a] = C[y], refl)` was probed in its place.

The walk is one generator with two instantiations, differing only in how the
right-hand side is rendered and in what closes a self-call leaf:

| | RHS rendering | leaf proof |
|---|---|---|
| `f#ext` | the body again, convoyed, ih `g2` | `hg(ȳ, Q₁, Q₂)` |
| `f_unfold` | the body **as written** — plain `match`, plain `f(ȳ)` | `f#irrel(…)` |

The `f_unfold` instantiation is why the RHS can be the user's own spelling: a
convoyed `match __dec_eq1: n {…}` and a plain `match n {…}` are *not*
convertible at a neutral `n` (the convoy is a different motive applied to
`refl`), but the walk equates them arm by arm, matching on the scrutinee under
a motive that mentions both. Probed.

Shapes the walk handles, and what it refuses:

- no self-call in a subterm ⇒ `refl`; a self-call in an argument position ⇒
  one `j` per changed argument; a `match` whose scrutinee holds no self-call ⇒
  re-match under the motive `λ s => lhs(s) = rhs(s)`, recurring in each arm,
  with every binder the arms' proofs mention generalized into the motive and
  re-applied (probed — an un-generalized `h2` is refused with
  ``this has type `Lt(n, w)`, but `False` is expected here``);
  a `let` whose right-hand side holds no self-call ⇒ substituted (`let` is
  zeta-transparent).
- **a self-call under a `λ` is refused** — that is funext again — as is a
  self-call in a `match` scrutinee or a `let` right-hand side, in this round.

**Amended by the implementation (2026-09-05).** Two shapes this section
claimed are *not* in the fragment:

- **A `match` on a computed scrutinee.** The anchors are `f#body(a, g1, x̄, h1)`
  and `f#body(b, g2, x̄, h2)`; a match on a *variable* the arguments mention is
  re-matched under `λ s => lhs(args[v↦s]) = rhs(args[v↦s])` and both sides then
  *reduce* into the arm, which is what makes the walk cheap. A stuck scrutinee
  (`match nat::le_dec(x, y)`) reduces neither side, so the motive would have to
  spell the arms out — rendering the body into the motive twice, and with it
  every obligation hole twice more (a named hole is single-use). `gcd`, `runs`
  and a nested-`match` polymorphic list function are in; **`merge` is out**, and
  is the negative control that says so.
  **Amended again (2026-10-31):** a computed scrutinee, and a `match h:`
  equation binding, are back in. The walk spells both sides of the match
  out at a fresh scrutinee and re-matches on it, rendering `f#body`'s side
  with a fork of the rewrite. Obligations are lifted, so the render carries
  no holes (`docs/language/matching/dependent-match-compiler-design.md` §8). `merge` is now a
  positive test.
- **An obligation left to `omega`.** See §4: `omega` is not a function of the
  goal alone, so the *first* implementation had to refuse such a body. Lifting
  the obligation (§4, "resolved by lifting") puts `halve_steps` and
  `even_or_odd_wf` back in, and the only thing left outside is a site whose
  statement names a binder the generator cannot type.

**Amended again (2026-11-01, issues/decreases-unfold-convoy-scrutinee.md).**
Obligations are lifted now, so a stuck scrutinee no longer costs a named hole
twice, and the rendering cost was the only thing keeping it out. `merge` is
in, and so is `match h: c` (a convoy), which every measured `runtime fn` uses
for its loop test. `Respell::match_spelled` proves such a match by the match
again, at a motive that spells both sides with the scrutinee generalized:

`(match c as λ s => (e: c = s) → L(s, e) = R(s, e) { C => λ h => p_C })(refl)`

`L(s, e)` is the left side's convoy at `s`, each arm the walk's left
rendering of it, and `R` is the same with the right renderings. A plain match
drops `e`. At `s := c, e := refl` both sides are the anchors' own matches by
conversion. Each arm's `let`s (convoy equations at `refl`, obligations) are
repeated around its renderings, because the motive sits outside the arm. The
match must be at the anchor, since the motive needs the result type. Below
the anchor (inside an argument) it is still refused.

**Amended again (2026-11-12, issues/decreases-no-companions-nested-match-calls.md,
issues/decreases-mut-call-statement-companions.md).** Two loop shapes a
measured `runtime fn` needs:

- **A branch under the loop test's arm.** An arm of a match the walk spells
  out has the declaration's result type, as the anchor does, so a match
  there is spelled out again by the same congruence (`Respell::match_below_anchor`
  → `match_spelled`): two ways round a loop, or one way round and an early way
  out, under one `match h:`. `if` is walked as the match on its decision.
  Only an argument position (whose type the walk does not know) still
  refuses a match. Two inner matches are declined because `f#body` spells
  them with an equation the source lacks: one on a variable the measure
  mentions (the rewrite refines it), and one on a computed scrutinee whose
  arms' lifted obligations read its `AutoEqs` equation (`match g:` it
  instead).
- **A `mut self` call statement before the self-call.** `x.m(a);` and `let p
  = x.m(a);` rebind `x` (`statements::elaborate_mut_call`), so substituting
  the block's `let`s must rebind it too: from there on `x` is
  `\0mutated_after(x.m(a))` and `p` is `\0mutated_value(x.m(a))`, private
  markers the elaborator reads as the statement does (the `Mutated` record's
  fields, or the receiver and the call when `m` is not `mut self`). Dropping
  the statement as a `let` nothing reads proved an equation about a body
  without the store, which the kernel refused against `f#body`.

**Amended again (2026-11-15, issues/runtime-mut-self-let-read-walk.md,
issues/measured-loop-inner-if-companions.md).** A `let` before a branch, and
a plain `if` under the loop's test: insertion sort's inner loop reads the
byte below once, `let below = s.byte_within(n, j - 1)`, and tests it.

- **A `let` stays in the walk's scope.** Substituting a block's `let`s into
  its result and walking that changed what the walk saw from what the
  rewrite saw building `f#body`: a test after the `let` read the parameters
  where `f#body`'s read the `let`'s name, so its equation became a fact a
  lifted obligation selected, and the re-emitted call passed one argument
  more than `f#obl_N` takes. The walk now goes on over the body as written,
  with the `let` bound in the rewrite's scope as `Rewrite::stmt` binds it,
  and substitutes it (`Respell::let_env`, unless a later binder shadows it)
  only into the terms it builds, before the arms' patterns.
- **A claimed call's rebinding is a `let` of its own.** `let p = x.m(a)`
  is spelled `let p = \0mutated_value(x.m(a)); let x = \0mutated_after(x.m(a))`
  (`rebind_marked`) in every block before anything is substituted. A read
  `let v = c.total()` rebinds `c` too (to itself), and substituting that
  into an arm's own `c.tick(v);` used to put a value where the statement's
  place was.
- **Type arguments are substituted into.** An `if`'s test is `decide_bit`'s
  type argument, which `subst` left alone, so a `let`'s variable stayed free
  in the companions.
- **An inner plain `if` follows `f#body`'s equation.** The walk numbered a
  computed inner scrutinee as an `AutoEqs` candidate wherever an arm
  recurses, but the rewrite numbers only one it gives an alias (one whose
  type it can write); the two now agree. Where the candidate is admitted,
  `f#body` matches with an equation the source lacks, and
  `Respell::match_spelled_eqs` spells each side with its own: both for
  `f#ext`, only the left for `f_unfold`. The refusal "bind it as `match g:
  …`" is gone.

A lifted obligation used to quantify over the walk's `__dec_scrut_N` alias as
if it were a parameter, which made `h: __dec_scrut_N = False` unprovable in
the lifted statement. It now substitutes the alias's value into the statement
instead.

Refusal is **not** an error on `f`: the companion is simply not emitted, and
`f` checks exactly as it does today. A later reference to `f_unfold` is what
reports, naming the body shape that stopped the walk and this section — the
reason is recorded on the elaborator against the `f_unfold` name and surfaces
through the same `NameRes::Restricted` path a generated name uses
(`resolve_name`), so the reader gets "no unfolding equation for `f`: …, see
docs/language/recursion/decreases-unfolding-design.md §3" rather than "unbound name". The
negative-control tests pin that message path. A hard error would regress
programs that are accepted now for the sake of a theorem they never cite.

A companion the walk *builds* but the **checker** refuses is treated the same
way, with the checker's own message as the reason. The generator is untrusted
by construction, so a term it got wrong must not take `f` down with it; the
quoted message keeps the case diagnosable.

## 4. Obligations are lifted, one declaration per site

**This section records a refutation and its fix. The design it opens with —
re-solving the obligation in each of the three terms — is what the first
implementation did; it does not work, and the last part of the section is what
the code does now.**

Each self-call's leaf needs the *same* obligation proof the body used —
`nat::Lt` is neutral, so `g(ȳ, P)` and `g(ȳ, Q)` are convertible only when
`P ≡ Q`. The walk re-emits the obligation the way it emitted it the first
time: `omega` where the body defaulted to `omega` (deterministic — the
certificate is a function of the goal), and the goal hole `?decN` where the
writer discharged it by hand, with `decl.body.ons` copied verbatim onto the
companion. `on` goals elaborate in the goal's own context — `gcd`'s
`on ?dec1 := nat::mod_lt(a, Succ(k), trivial);` names the arm binder `k` from
the end of the block — and the walk re-binds the same names in the same
places, so the copy resolves.

One wrinkle, pinned by probe: **a named hole is single-use per block**
(``hole `?h` is already used in this block``), and `f#ext`'s leaf wants the
obligation twice, once per side. The leaf therefore binds it once —
`let __dec_oN: nat::Lt(e[ȳ], e) = ⟨obligation⟩;` — and uses the name on both
sides; `let` is transparent, so the two sides still reduce into the body's own
spelling. (The annotation is needed: the right-hand side is a bare hole.) The
same `let` block also binds each enclosing arm's convoy equation at `refl`
(§5). Those bindings sit at the **leaf**, not at the arm that introduced them:
only at a leaf is every enclosing pattern substituted, and `Succ(k)` two arms
up is `Succ(Succ(l))` by the time the innermost arm has bound `l`. Placing them
at the arm states them at the wrong pattern and the transport chain no longer
climbs back to the ih's own measure — that is a real bug the first
implementation had.

**Refuted by §8 item 5 (2026-09-05): `omega` is not deterministic in the goal.**
`omega_cert::reconstruct` takes the local context as well as the goal, so two
identical goals in two different contexts reconstruct two different — and
non-convertible — certificates. Pinned directly:

```
fn o1(k: Nat, h: nat::Lt(k, k)) -> nat::Lt(k, Succ(k)) { omega }
fn o2(k: Nat)                   -> nat::Lt(k, Succ(k)) { omega }
theorem same(k: Nat, h: nat::Lt(k, k)): o1(k, h) = o2(k) { refl }   // NotConvertible
```

`f#body`'s context and `f#ext`'s differ by construction (one bound hypothesis
against two, under different names), so an obligation that defaulted to `omega`
cannot be re-emitted by re-running `omega`. The round therefore **refuses** a
body with an `omega`-defaulted obligation, with a message naming the site and
the `on ?decN` that gets through; every `on`-discharged obligation works, since
the `on` expression is the writer's text and elaborates to the same term in
both contexts.

### Resolved by lifting (2026-09-05)

The fix is to **lift the obligation itself**, exactly as §2 lifts the
recursor. One generated

```
theorem f#obl_N(the binders its statement names) : e[ȳ] < e_i
```

per self-call site, whose body is the `omega` — or the writer's `on ?decN`
expression, moved here with its `on` — and `f#body`, `f#ext` and `f_unfold`
all *reference* `f#obl_N(ȳ)` at the site. The three spellings of a self-call
are then identical by construction, the context `omega` reconstructs against
is the lifted declaration's own (one context, not three), each obligation is
solved **once**, and the 3× cost §7 noted goes with it. `f#obl_N` is a
`theorem`, so it is opaque: nothing can unfold two references into two
certificates again.

What is quantified is the binders in scope the statement — or the `on`
expression — actually names, under their own names and in binding order: the
declaration's own parameters, and the enclosing arms' binders, which the
refined measure `e_i` mentions by construction (`gcd`'s `on ?dec1 :=
nat::mod_lt(a, Succ(k), trivial)` names the arm binder `k`, so `k` is a
parameter of `gcd#obl_1`). The scrutinee itself drops out where the pattern
replaced it, which is why the reference reads the same on both sides: `f#body`
spells `f#obl_1(a, k)` inside `match b { Succ(k) => … }`, and the companion —
which substitutes the pattern for `b` — spells `f#obl_1(a, k)` too.

The transport chain of §3 does **not** move: it stays in the body and in the
companions, at the refined measure, with only its leaf becoming a reference.

One thing the walk cannot read off the surface: an arm binder's **type**, and
a declaration parameter needs one. The elaborator answers (`BinderTys`, the
constructor's stored field types instantiated at the scrutinee's type
arguments); where it declines — a pattern under an unannotated `let`, an
indexed family — the site is not lifted, the obligation stays at the call as
it was before this round, and only the companions are declined. Likewise, a
lifted obligation the **checker** refuses re-lowers the declaration in the
un-lifted spelling and declines the companions: a statement this syntactic
pass got wrong must not take `f` down with it, and a genuinely unprovable
obligation fails again there with the message
`docs/language/recursion/termination-measures-design.md` §2 pins. (A sibling obligation that had
already checked stays behind as an unreferenced global; it is unspellable, and
nothing reads it.) A body that discharges its
goals by *statement* (`on _: P := e`) is not lifted at all — the plan rests on
one named goal per generated declaration.

## 5. The convoy does not leak

`f`'s real body carries the §3 refinement convoy: `match __dec_eq1: b {…}`
with hidden equation binders. `f_unfold`'s right-hand side is the *other*
rendering — the body as written — so the equation a user reads and rewrites
with mentions no `__dec_…` binder at all. The convoy survives only inside the
proof, where the walk instantiates each `__dec_eqN` to `refl` at its arm's
pattern (§3). Probed: `hv_unfold`'s statement is
`hv(n) = match n { Zero => 0, Succ(m) => Succ(hv(m)) }`.

## 6. One equation, not one per arm

The equation is stated for the whole body. Per-arm equations (`f(Succ k) = …`)
are then *computation*, not further generation: `f_unfold(0)` has type
`hv(0) = match 0 {…}`, whose right-hand side reduces to the arm. The customer
proof uses it exactly that way — `Zero => hv_unfold(0)` checks against
`hv(0) = 0` — so N generated theorems would buy nothing over one. Probed.

### 6.1 One equation per arm of a test (2026-11-14)

The exception is a body that is one **test with an equation**: `if h: P`,
which lowers to the convoy on `decide_bit<P>()`, or a written `match h: b`
on a `Bool`. There `f_unfold`'s right-hand side does not reduce to an arm at
open arguments, since the bit is stuck, and choosing the arm by hand meant a
match whose motive the arms' use of the equation made ill-typed. So two
more theorems are generated after `f_unfold`, under the test
(issues/loop-invariant-rules.md):

- `f::step(x̄, h: P)`: `f(x̄)` is the arm that calls `f` again;
- `f::done(x̄, h: ¬P)`: `f(x̄)` is the arm that does not.

For `match h: b` the hypotheses are `b = True` and `b = False`. Each is
`trans(f_unfold(x̄), Bool::convoy_true(bit, λ e => yes, λ e => no, e₀))`,
where `e₀` is the bit's equation read back from the hypothesis
(`decide_bit_of`), so the arm is stated exactly as `f_unfold` spells it:
its lifted `f#found_N` proofs included, applied to the hypothesis.
`convoy_true` is `Bool::taken_true` with its arms given; that one is
proved by `j` on the hypothesis, with the convoy's own `refl` generalised
in the motive, so no axiom is needed. `let`s before the test (a `mut
self` body's `let s__1 = s;`) are kept on both sides, and a test that reads
them is declined. Nothing is generated where both arms or neither call
again, or the body is not one test; a reference then says why.

**Spellings (Minus, 2026-11-14).** The two are minted `f#step`/`f#done`
and designated `f::step`/`f::done`, as `f::ext` and `f::rec` are, so no name
a module may declare is taken: generating them as `f_step`/`f_done` took
names four tests and a hand-proved module had already used. The unfolding
equation is cited as `f::unfold` too; it is still declared as `f_unfold`,
which stays a deprecated spelling of it (§2) until the declaration itself
moves.

## 7. When it is generated, and what it costs

- **`fn` only.** A `theorem` is opaque (`crates/elab/src/lib.rs:2544`), so
  `f(ȳ)` in the equation's right-hand side would never unfold and `f#irrel`
  could not connect the two sides. A `theorem … decreases` gets no companion,
  and none is wanted: nothing rewrites with a proof's value.
- **Always attempted**, for every `decreases` `fn`, and silently skipped where
  §3 refuses the body. `grep decreases lib/` is empty today — the feature
  landed this week and the library has no customer yet — so the library cost
  of "always" is exactly zero, and the acceptance file is the only place the
  extra elaboration is paid. Revisit if a `lib/` customer makes it visible.
- Polymorphic and implicit parameters are quantified on every companion the
  way `measure.rs`'s motive already quantifies them; `f_unfold<A>(x̄)` for an
  `f<A>`. A companion quantifies an implicit value parameter *explicitly* and
  pins the type parameters at every call site (`f#body<A>(…)`), so nothing in
  the family depends on inference at an argument no type mentions.
- **Cost.** Each obligation is solved **once**, in its own `f#obl_N`, and the
  body and both companions reference it (§4). The three solves per obligation
  the first implementation paid were not a cost worth accepting — they were
  the bug — and both went away together. What the companions still cost is the
  two walks themselves, each proportional to the body, plus one extra
  declaration per self-call site.

The end-to-end probe (scratch, `halve` written out by hand as `Fh`/`Body`/
`hv`): `Body_ext`, `Fh_irrel`, `hv_unfold` with a plain-`match` right-hand
side, and `hv_id` — the customer — all check, while `hv_id` against a
`decreases`-defined `hv` with no equation is refused. That is the whole chain
of §1–§6 with the generator's work done by hand.

## 8. Cheap verification items for the implementation's first hour

Each is a few minutes and each can refute a section above.

1. **Lifting is free.** Reshape `wrap_measure` to emit `f#body`/`f#rec` and
   run `crates/elab/tests/termination_measures.rs` unchanged. If
   `gcd_12_8`/`merge_demo`/`runs_demo` still pass, §2's indirection costs
   nothing; if they do not, the `refl`s are the deviation to report.
2. **A `#` name is registrable for a `fn`.** `inductive.rs` mints `#skel` for
   *types*; confirm a value global takes one, and that nothing in the module
   image, the respell pass, or the dependency graph trips on it.
3. **The module image carries the companions.** The image encodes a
   `ModuleDelta` (`crates/elab/src/module_image.rs`); confirm the companions
   ride along as ordinary globals, and bump the magic only if they do not.
4. **`on` copies resolve, and the `let` trick works.** Emit `f#ext` for `gcd`
   and check the copied `on ?dec1 := nat::mod_lt(a, Succ(k), trivial);` closes
   the leaf from a nested arm (§4). If the nested block rejects the hole, take
   the duplicate-`on` fallback and amend §4.
5. **`omega` is deterministic.** Emit `f#ext` for `halve_steps` (no `on`
   anywhere) and confirm the re-run certificate is convertible with the body's
   — §4 assumes it, and it is the one assumption a caching or ordering change
   could quietly break.
6. **Refusal is silent.** A `decreases fn` with a self-call under a `λ` still
   checks; only a reference to its `f_unfold` reports (§3).

Then the acceptance tests, per `docs/testing-generated-terms.md`: the customer
theorem at an **open** argument and at a literal; an **open** element type
(`List<A>` rather than `List<Nat>`); `f_unfold` used in a *checking*
position (rewriting inside a larger goal, not only as a whole proof); and the
negative controls — the self-call-under-`λ` refusal message, and a
`theorem … decreases` having no `_unfold` at all.

## 9. What the verification items found (2026-09-05)

1. **Lifting is free — confirmed.** `wrap_measure` reshaped into `f#body` /
   `f#rec` / `f`, and `crates/elab/tests/termination_measures.rs` passes
   unchanged, `gcd_12_8` / `merge_demo` / `runs_demo` `refl`s included.
2. **A `#` name is registrable for a value global — confirmed.** Nothing in
   the name tables, the respell pass or the dependency graph notices; the
   names are unspellable because the *lexer* never produces them, and the
   generator builds AST rather than text.
3. **The module image carries the companions — by construction.** They commit
   through `commit_decl` like any global, so they ride in the `ModuleDelta` as
   ordinary bindings; no format field changed and the magic is not bumped.
4. **`on` copies resolve — confirmed.** `gcd`'s
   `on ?dec1 := nat::mod_lt(a, Succ(k), trivial);` closes the leaf in `f#ext`
   and in `f_unfold`, from the nested arm, with the `let` of §4 and no
   duplicate-`on` fallback needed.
5. **`omega` is deterministic — REFUTED**, and the refutation is what §4's
   lifting answers: the obligation is a declaration of its own, so `omega`
   runs once, in one context, and all three terms reference the result.
   `halve_steps` and `even_or_odd_wf` are in the fragment, and
   `an_obligation_left_to_omega_is_lifted_and_carries_the_equation` is the
   test that was the refusal's negative control.
6. **Refusal is silent — confirmed.** A `decreases fn` with a self-call under a
   `λ` still checks; only a citation of its `f_unfold` reports.

The customer chain of §1 (`hv_unfold` at `0` and at `Succ(k)`, and `hv_id`
through them) is generated and checks, as does `gcd`'s, a polymorphic
`List<A>` function's with a nested refinement, and a use of the equation in a
checking position inside a larger goal.

## 10. What the lifting pass found (2026-09-05)

- **A hole can be the whole body of a generated declaration**, `on` and all:
  `theorem obl(a, k: Nat): nat::Lt(nat::mod(a, Succ(k)), Succ(k)) { ?dec1 on
  ?dec1 := nat::mod_lt(a, Succ(k), trivial); }` checks (probed), as does the
  `omega` spelling — §4's shape was not blocked anywhere, and `count_holes`
  counts the lifted hole through its ordinary body walk.
- **The oracle is the only new elaborator query.** Everything else the lift
  needs, the walk already tracked; what it did not have was an arm binder's
  type, and `Elaborator::ctor_fields_of` answers from the constructor's stored
  surface fields.
- **`halve_steps` and the `even_or_odd_wf` shape are in**, so the round's own
  negative control became a positive test. A `decreases` **member**
  (`List::nth2`, recursing under its base name, its equation cited as
  `List::nth2_unfold`) is the acceptance the earlier pass was missing.
- **Nothing in `termination_measures.rs` moved**: the obligation diagnostics
  (`must decrease the measure`, the refined-statement message, the
  `omega`-less unsolved goal) all still read at the call, since a lifted
  obligation the checker refuses re-lowers un-lifted and reports there.

## 11. Designed spellings for the recursor and its step (2026-10-26)

`f#rec` and `f#body` have designed spellings, `f::rec` and `f::body`
(`docs/native/repr-access-spellings-design.md`), and the minted names leave the
surface as any designated name does. They are for a proof that cannot go
through `f_unfold`, which is not generated where the body matches on a
computed scrutinee (§3; every word loop decides on a comparison):

- `f::rec(z, x̄, h)` is `f` at a bound `z` on its measure, `h : e < z`;
  `f(x̄)` is `f::rec(Succ(e), x̄, nat::Nat::lt_succ_self(e))` by `refl`.
- `f::body(k, g, x̄, h)` is one step, its recursion any `g`, and
  `f::rec(Succ(k), x̄, h)` is `f::body(k, λ ȳ p => f::rec(k, ȳ, p), x̄, h)`
  by `refl` (§2).

A claim about `f` at an open argument is then a claim about `f::rec` by
`Nat` induction on the bound, each step a claim about `f::body` with `g`
abstracted, which `split_all` proves when the step is a tree of `match h:`
convoys (`docs/tactics/goal-combinators.md`). The verified native compiler states
its loop agreement this way (issues/function-ir-loop-measure-recursion.md).
The spellings are designated after the companions are generated, which are
spelled with the minted names; another module writes them under the
declaring module's name, `m::f::rec`.

