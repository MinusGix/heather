# `rewrite(h, e)`: rewriting a goal along an equation

Design record for `issues/equation-rewrite-in-goal.md`, 2026-10-21. The issue:
rewriting a goal along an equation was written as a transport with a
hand-written motive,

```heather
j(n.add_comm(k), λ y q => y <= k + m,
  j(m.add_comm(k), λ y q => n + k <= y, k.add_le_mono_r(n, m, h)))
```

and the motive is the goal with one subterm replaced by a binder, which the
elaborator can write itself: the match-motive synthesis already does exactly
that abstraction (`docs/goal-motive-synthesis-design.md` §3). The same proof
is now

```heather
rewrite(k.add_comm(n), k.add_comm(m), k.add_le_mono_r(n, m, h))
```

## 1. The form

`rewrite(h₁, …, hₙ, e)`, n ≥ 1, at a **checking** position with goal `G`:

- each `hᵢ` is a proof of an equation `aᵢ = bᵢ` (its type is read up to weak
  head normal form, so a definition that unfolds to `=` is one);
- in turn, every occurrence of `aᵢ` in the current goal becomes `bᵢ`, and the
  next equation sees the goal its predecessor left — `rewrite(h, …, e)` is
  `rewrite(h, rewrite(…, e))`;
- `e` is checked at what remains. When the rewrite leaves something `refl`
  closes, `e` is `refl`: `rewrite(p, refl)` is congruence.

This is the direction of Lean's `rw [h]` and Rocq's `rewrite h`: the goal's
left sides become right sides. The opposite direction is `sym(h)`, an
ordinary expression; nothing in the form spells or guesses a direction
(`issues/relational-rewrite-controls.md`: "do not silently guess symmetry").
A goal that does not mention `aᵢ` but does mention `bᵢ` is an error whose
hint says `sym(…)`.

It is an elaborator entry point recognised by name at a checking position,
like `ring(h, …)` and `rel_cong(h)`, not a keyword: a local, an alias or a
declaration named `rewrite` is an ordinary name, and nothing in the parser or
the editor grammar changed. In inference position it is an error that says
it needs an expected type.

Rejected: Lean's `h ▸ e`. Its direction is the transport one (`e : P(a)`
proves `P(b)`), the opposite of `rw`, and Lean resolves the ambiguity by
trying both — the guess this design declines. A block statement
(`rewrite h; …`) reads well but is new grammar; the expression form composes
with every block form that exists (`let`, `on`, `calc` steps) and can grow a
statement spelling later without changing meaning.

## 2. What it elaborates to

For one equation `h : a = b` at goal `G`:

1. `M := G.abstract_local_any(spellings of a)` — a type over `Γ, y : S` with
   every occurrence of `a` replaced by `y`. An occurrence is `a` itself
   (`==` on de Bruijn terms), or, since round 2, a subterm under no binder
   with `a`'s head that converts to it (§6.2).
2. `M` is checked to be a type, at the goal's level, by the kernel's type
   formation. Abstracting a term that something *else's* type depends on —
   `v : P(n)` in a goal `v = v`, rewriting `n` — leaves `Id(P(y), v, v)`,
   which is not one. The error says so and points at `j`; it is not left to
   the declaration gate, whose message would name a motive nobody wrote.
3. `e` is checked at `M[b/y]`.
4. The term is `J(sym h; y q. M; e) : M[a/y]`, and `M[a/y]` is `G` —
   syntactically when every occurrence was `a` itself, up to conversion when
   one was a respelling, which the kernel's gate checks like any other
   expected type. `sym h` is written out as `J(h; y q. y = a; refl a)`, so the
   form needs no library import.

Nothing is trusted: the declaration still passes the kernel gate.

**Where `a` is looked for.** The goal as written, then — only when that finds
nothing — its exposed form (head and an equation's sides one weak-head step
down, the synthesis's §4.3 rung). Not deeper. A
goal whose occurrence appears only after reduction (`Nat::Even(Succ(l) +
Succ(l))` stepping to `Even(Succ(Succ(l) + l))`) is out of reach; such a site
keeps its `j`, whose motive states the reduct, or restates the goal first
with an annotated `let`. That is the same boundary `cong(p)` has
(`docs/calc-equational-chains-design.md` §1.2).

## 3. Occurrences

`rewrite(h, e, at := k)` and `at := [k₁, …]` rewrite only the listed
occurrences, counted from 1 in the order the kernel's traversal meets them:
left to right through the goal as written. Selection is against the goal as
written only — a number that meant one position as written and another after
reduction would be worse than a refusal. A number past the last occurrence is
refused with the count. With several equations `at :=` is refused: it could
not say whose occurrences it numbers, and the nested spelling
`rewrite(h₁, rewrite(h₂, e, at := k))` says it.

The kernel side is one more caller of the existing abstraction:
`Type::abstract_local_at(pat, at)` is `abstract_local` whose mapper counts the
occurrences it meets and replaces only the selected ones. An occurrence passed
over is descended into like any node, which finds nothing — a term does not
contain itself — so the binder bookkeeping stays in `subst.rs` alone. The
obligation argument is unchanged: every replaced position held `a`.

Library evidence that the control is needed: `nat.hthr`'s
`div_lt_of_lt_mul` rewrites `n` to `n.div(d) * d + n.mod(d)` in
`n.div(d) * d <= n`, where the `n` inside `n.div(d)` must stay: `at := 2`.

Numbers are the Rocq/Lean `at` spelling and are fragile under edits to the
goal; a pattern-based selection (SSReflect's `[X in _ <= X]`) would not be.
The explicit motive — `j` — is that pattern today, and remains the spelling
for anything numbers express badly. `relational-rewrite-controls` owns the
shared spelling when relational rewrites grow one; this form's `at :=` is the
`=` case of it, so the two should agree when that issue is designed.

## 4. Library adoption

Converted mechanically per site (each `j(p, λ y q => M, c)` whose motive does
not mention `q` became `rewrite(sym(p), c)`, or `rewrite(p', c)` where `p` was
`sym(p')`; nested towers flattened), kept only where the module still checked,
then tidied by hand (`sym(a.add_comm(b))` is `b.add_comm(a)`). The sites that
stayed `j` stayed for one of three reasons, all expected:

- **reduction**: the motive is stated about a reduct of the goal (`a.pow(Succ(k))`
  written as `a.pow(k) * a`, `Even(n + n)` stepping under `Succ`);
- **partial occurrence**: the motive keeps some occurrences of the right side
  fixed in a way `at :=` was not worth spelling;
- **a motive about the proof**: the motive mentions `q` — a genuinely
  dependent elimination, which is `j`'s job.

The per-module counts are in the PR description.

## 5. What it does not do

- **No relations other than `=`** in this first form. Rewriting along `≈`,
  `<=` or any other relation is §9's, which the same spelling reaches.
- **No rewriting in hypotheses** in this form. Lean's `rw … at h` is a
  different elaboration — the hypothesis is a term to transport, not a goal
  to prove — and has its own spelling, `rewrite(h, in := hyp)` (§7).
- **No search.** It does not try `sym` or unfold the goal beyond one exposed
  layer. Conversion is asked only at subterms that already share the left
  side's head (§6.2), never at every node.

Follow-ups are filed: `rewrite-lemma-instantiation.md` and
`rewrite-keyed-conversion-matching.md` (done in round 2, §6),
`issues/subst-local-equation.md`,
`rewrite-in-hypothesis.md`, `rewrite-pattern-occurrences.md`,
`rewrite-setoid-relations.md`, `rewrite-conveniences.md`.

## 6. Round 2: unapplied lemmas and keyed matching

Lean's `rw [Nat.add_comm]` takes the lemma unapplied and finds its arguments
in the goal; this round does the same, and finds occurrences the way Lean's
`kabstract` does — by head symbol, then conversion — instead of by `==`
alone (`issues/rewrite-lemma-instantiation.md`,
`issues/rewrite-keyed-conversion-matching.md`).

### 6.1 Instantiation

The proof's type is read up to weak head normal form as a telescope
`Π x₁ … xₖ. a = b` (k ≤ 32). With k = 0 nothing changes. Otherwise the `x`s
are pattern variables and the goal's terms under no binder
(`Type::root_terms`, in the order `at :=` numbers by) are tried in turn,
filtered by **key** — the same application head and argument count as `a`.
The first that matches fixes every `x`, the proof is applied to them, and
the step continues with that instance like an applied equation: every
occurrence *of that instance* is rewritten, which is Lean's semantics.
`rewrite(Nat::add_comm(k), …)` (a partial application) and a hypothesis of
telescope type (`w : (x: Nat) → f(x) = x`) are the same case.

Matching is first-order along application spines: a variable binds the
subterm it meets (and must meet a convertible one if already bound); a part
of the pattern that mentions no variable must be equal or convertible; a
part that mentions variables but is not an application (a constructor
value annotated with a type argument, `Nil` at `A`) is deferred until the
variables it mentions are bound by other arguments, then instantiated and
compared. Spine annotations are not read during matching — the instance is
built from the bindings and §6.2's conversion test re-checks it, so a match
that read past a differing annotation finds no occurrence rather than a
wrong one.

Refused: a left side that is itself one of the arguments (it would match
every subterm), and an argument only the right side mentions (nothing in the
goal determines it — the error names it and asks for it explicitly).

**A law about a class's operation** (`issues/rewrite-class-law-instantiation.md`,
2026-10-28). A theorem stated in a class's section takes the section's
operations and dictionary as arguments, so `Semiring::mul_range_l`'s left
side `c * ∑ k < n, f(k)` is headed by a pattern variable, `*`. Such a
pattern is keyed by its first argument that is no pattern variable (here the
sum, keyed by `range`), and the head binds to whatever operation the
candidate applies; a pattern of nothing but variables still has no key. The
dictionary is not a part matching can bind — the left side mentions it only
inside what it builds from it (the sum's monoid) — so once the arguments
before it are bound, a class-dictionary argument left unbound is *resolved*
at its instantiated type. Nothing resolving refuses the candidate: `c + ∑ …`
binds `*` to `+`, and `Semiring(≈, +, +)` has no instance. The same holds
at a concrete carrier (`Rat`'s `*` against the instance). The 256-candidate
cap bounds the looser key.

A pattern `λ z. g(z)`, `z` not in `g`, is matched as `g` (η), against what
the candidate contracts to by η, or the candidate λ itself: the law's
`λ k. f(k)` binds `f`, which occurs nowhere else. A candidate body that is
no η-redex (`λ k. f(k) + 1`) binds `f` to that λ, and the instance's right
side carries the β-redex `(λ k. f(k) + 1)(k)`, which conversion reads.

Applying an unapplied commutativity lemma twice rewrites the first instance
back (`rewrite(Nat::add_comm, Nat::add_comm, …)` on `k + n <= k + m` turns
`k + n` into `n + k`, then the first `_ + _` is `n + k` again). That is
Lean's behaviour too and the fix is the same: pin an argument,
`Nat::add_comm(k)`.

### 6.2 Keyed occurrences

An occurrence of `a` is `a` itself or a term under no binder, with `a`'s
head **global** and argument count, that converts to `a` at its type
(`MotiveSynthesisElab::motive_candidate_converts`, which also checks the
candidate's own type, the guard the motive synthesis needed at irrelevant
types). At most 256 candidates per step are tested; misses cost one
bounded conversion each, and a goal with no same-headed term costs none.
All spellings are abstracted in one pass (`abstract_local_any`), so the
motive never sees half a rewrite; `at :=` numbers them together
(`abstract_local_at` takes several patterns).

A local-variable head is matched by `==` only: a variable converts to
nothing but itself short of a `let`, and the elaborator inlines those.

What this recovered, measured by re-running the per-site conversion over
the `j` sites round 1 left: 13 more convert (bitvec 6, utf8 4, int 2, nat 1)
— occurrences whose spelling differed from the equation's below the head,
the `BitVec::ofNat_toNat` sites among them. The rest are what §4 already
said: motives stated about a reduct the goal reaches only after more than a
head step, and motives that mention the proof. And the bit-vector site PR #93 had to write with `sym`
(`ofNat(toNat(x))`, whose implicit width was spelled differently in the goal
and the equation) is `rewrite(none, refl)` again.

## 7. Rewriting a hypothesis: `rewrite(h, …, in := hyp)`

`issues/rewrite-in-hypothesis.md`. Lean's `rw [h] at hyp`, Rocq's
`rewrite h in H`: from `hyp : P` and `h : a = b`, a proof of `P` with every
`a` turned into `b`.

```heather
let moved = rewrite(es, in := fl.left);
```

is `j(es, λ y _ => m * Nat::pow(2, Succ(y)) <= h, fl.left)` — the motive is
`fl.left`'s type with `es`'s left side abstracted, which the elaborator writes.

**The form.** `rewrite(h₁, …, hₙ, in := hyp)`: every positional argument is
an equation, applied in turn exactly as in the goal form, and `at :=` selects
occurrences with one equation (several: rewrite one at a time, nesting
`in :=`). It is an **inference** form: the result's type is what the rewrite
leaves, so the customer — an unannotated `let` — needs no annotation. At a
checking position it is inferred and compared, like any inferred term.

**Direction.** The same as the goal form: left sides become right sides,
`sym(h)` reverses, nothing is guessed. Applied to a type that is *proved*
rather than *wanted*, that direction is `J`'s own: the step is
`J(h; y q. M; hyp) : M[b/y]`, with no `sym`. Unapplied lemmas are
instantiated against the hypothesis's type (§6.1), and occurrences are keyed
(§6.2), unchanged.

**Why this spelling.** The candidates were a second name
(`rewrite_at(h, hyp)`), a named argument on the existing form, and a `let`
statement form (`let hyp' = rewrite(h) in hyp;`).

- The library's customers (§7.1) are all `let x = j(p, λ y _ => M, hyp);` —
  an expression in a `let`. A statement form would need new grammar to say
  what `let x = <expression>;` already says.
- A second name would be a second entry point with the same equations,
  direction, `at :=` and instantiation; one form with a named argument is one
  set of rules. `at` already means occurrences here, so Lean's `at hyp`
  reading was not available.
- `in :=` is Rocq's word for the same operation and reads as what it does.
  It is a named argument, not a keyword: `in` stays an ordinary identifier
  everywhere, and the parser and editor grammar are unchanged.

The issue's worry — that a named argument makes it "not a checking-position
form" — is the point rather than a cost: the hypothesis is a term with a type
of its own, so inference is the natural mode, and checking positions still
work through the ordinary fallback.

### 7.1 Library adoption

The customers were the `let` sites whose right side is a `j` transport of a
hypothesis with a motive that does not mention the proof. Converted
mechanically (`let x = j(p, λ y _ => M, hyp);` → `let x = rewrite(p, in :=
hyp);`, annotated lets too), kept only where the module still checked. A site
stays `j` for the reasons §4 lists for the goal form: its motive abstracts
only some occurrences in a way `at :=` was not worth spelling, states a
reduct, or names a different left side than the equation's spelling reaches.
The per-module counts are in the PR description.

## 8. Eliminating a variable: `subst(h, e)`

`issues/subst-local-equation.md`. `rewrite` refuses when abstracting the left
side leaves a motive that is not a type: `v : P(n)` in a goal `v = v`,
rewriting `n` (§2). When the side being replaced is a **local variable**, the
rewrite can always be done — Lean's `subst` — by generalising everything that
depends on it.

```heather
theorem t(P: Nat → Type, n: Nat, v: P(n), h: n = 0, k: (w: P(0)) → w = w): v = v {
    subst(h, k(v))
}
```

**The form.** `subst(h, e)` at a checking position with goal `G`. `h` proves
`t = x` or `x = t` where `x` is a local and `t` does not mention it; when
both sides qualify, the right one is eliminated (Lean's order). `e` is
checked at `G` with `t` for `x`, in a context where:

- every **later local whose type depends on `x`** — directly, or through `h`
  or another such local — is bound again, under its own name, at its type
  with `t` for `x`;
- `x` itself is a `let` alias of `t`, so an annotation in `e` that says `x`
  says `t`;
- `h` is a `let` alias of `refl` at `t = t`;
- every `let` alias that mentioned `x`, `h` or a reverted local means what it
  does at them.

**What it elaborates to.** With `Γ = Γ₀, x : A, Δ` and the reverted locals
`d₁ … dₖ` (in context order), the motive over `Γ, y : A, q : t = y` is

```text
M = Π (d₁' : T₁σ) … (dₖ' : Tₖσ). Gσ        σ = [y/x, q/h, d'/d]
```

and the term is `J(p; y q. M; λ d₁' … dₖ'. e) d₁ … dₖ` with `p : t = x`.
At `y := x, q := p`, `σ` is the identity on everything it mapped, so the
term's type is `G` syntactically. No local leaves `Γ` and none is reordered:
`x` stays a binder the case no longer mentions, which is what lets `t`
mention locals declared after `x` (`h: x = y + 1` with `y` later) without the
reordering Lean's `revert` would need.

**`h` itself.** With `h : t = x`, `p` is `h` and `h ↦ q` in the motive, so a
goal that mentions `h` sees `refl` in the case — the elimination is genuinely
dependent, `J` with the goal as its motive. With `h : x = t`, `p` is
`sym(h)`, and `h ↦ sym(q)` would leave `sym(sym(h))` where `h` was, which is
not `h` again (`Id` is proof-relevant). So in that orientation `h` is mapped
only when nothing mentions it; when the goal or a reverted local does, `h` is
reverted like any other dependent local and the case sees it at `t = t`.

**Refused**, each with its own message: a proof of something other than an
equation; neither side a local the other side does not mention (pointing at
`rewrite`); a `t` that mentions a local depending on `x` (it would be
reverted out from under itself); inference position.

What it does not do: eliminate a variable bound in the global context or a
`let` (aliases are inlined, so `h : k = 3` with `let k = n` is `h : n = 3`
already), or search for which equation to use. It is an elaborator entry
point recognised by name at a checking position, like `rewrite`; a local or
declaration named `subst` is an ordinary name.

## 9. Rewriting along a relation

`issues/rewrite-setoid-relations.md`, 2026-10-26. Rocq's `setoid_rewrite`,
Lean's `grw`: from `h : R(a, b)` for a relation `R` other than `=`, the same
`rewrite(h, e)` turns `a` into `b` in a goal whose shape says how it respects
`R`, consuming the compatibility evidence `rel_cong` consumes
(`docs/proof-position-relational-congruence.md`). Built the way mengine's
rewriter is (`docs/mengine-survey.md` §4.3): bottom up, one step per changed
node, one result per node, so it is linear in the goal as a DAG from the
start. `crates/elab/src/rewrite/relation.rs`.

```heather
theorem Rat::add_neg_cancel_r(self x, y: Rat): (x + y) + -y ≈ x {
    rewrite(x.add_assoc(y, -y), y.add_neg(), x.add_zero(), refl)
}
```

### 9.1 Which proofs are relation steps

A step's proof is read **as written** below its Π telescope: when that is a
relation application `R(a, b)` — an `El` of a two-argument application whose
two domains are one carrier `C` — the step is a relation step. Read up to
weak head normal form instead, `x ≈ y` at `Rat` is an equation between `Int`
cross-products, and §1's form would rewrite those; that reading was never what
a proof of `≈` meant in a goal about rationals.

One exception keeps the equation form wherever it already served: a relation
that **unfolds to equality of its own two sides** (`RelId(a, b)`,
`Steps(R, 0, a, b)`) is that equality and rewrites as one, a single
transport with no evidence. Nothing else is guessed: direction is the written
one (`issues/relational-rewrite-controls.md`), and an unapplied law is
instantiated as §6.1 says, the first node the walk meets that matches the
left side fixing its arguments.

### 9.2 Goals and polarity

The goal is one of:

- a relation application `S(l, r)` at the carrier `C`, `S` the rewrite's
  `R` or another relation;
- a non-dependent implication `P → Q` between such goals (so `¬P` too,
  whose `False` has nothing to rewrite);

and a goal that mentions `a` in any other shape (an `=`, a `↔`, a predicate
`P(t)`) is refused with what it is: nothing says how it respects `R`. A goal
that does not mention `a` is refused as in §1, with a hint when it mentions
`b`.

A goal to prove is reached *from* its rewritten form (`G' → G`), a
hypothesis (`in := hyp`, §7) is carried *to* it (`G → G'`), and an
implication's premise is rewritten the other way from its conclusion. The
walk builds a plan once and emits it at either **polarity**: for `S(l, r)`
read backward, `e : S(l', r')` becomes `S(l, r)` by

```text
chain(S, R ⇒ S)(l', r', r, e, sym(R(r, r')))    : S(l', r)
chain(R, S ⇒ S)(l, l', r, R(l, l'), ·)          : S(l, r)
```

where `chain` is `Transitive<C>(S)`'s `rel_trans` when all three relations
are one, else `Trans<C>(…)`'s `rel_chain` — the classes `calc` composes with,
so `x + z <= z` rewrites along `≈` through `Rat`'s `Trans` pairs. Only a
changed side takes a step, and only the right side needs `Symmetric<C>(R)`:
a non-symmetric `R` (monotone rewriting along `<=`) rewrites left sides
only. `P → Q` read backward is `λ p. Q-back(e(P-forward(p)))`.

### 9.3 The walk

Each node of the goal is rewritten once, children first, and the result is
kept per node identity:

- an **occurrence** of `a` becomes `b`, with `h` as its proof. An occurrence
  is `a` itself, or a term with `a`'s global head whose arguments convert to
  `a`'s one by one. Argument-wise, not §6.2's whole-term conversion: the head
  is the same operation on both sides, and a miss would unfold it on both
  (rational arithmetic) only to compare the parts that differ. A respelled
  implicit argument still matches.
- an **application** whose arguments changed gets one congruence step, over
  its last two arguments (`Respects2<C, C, C>(R, R, R, op)`, an unchanged one
  held by `Reflexive<C>(R)`), its last one (`PreservesRelation(R, R, f)` with
  `f` the partial application), or any single other one
  (`PreservesRelation(R, R, λ z. f(…, z, …))`, the λ spelling registrations
  such as `linux_answered`'s use). A binary operation changed only in its
  last argument takes unary evidence when only that is registered. Several
  changed arguments in no such position are refused by name.
- an **unchanged** node gets nothing, and a node of another kind (a λ, a
  former that is no application) is left as it is unless it contains `a`,
  which is refused: half a rewrite is worse than none.

A context that does not map `C` to itself (an argument into `size: A → Nat`)
cannot state evidence of either shape, and is refused: the rewrite stays in
`R`'s carrier.

### 9.4 The proof

The proof is kernel terms: each step an `app@` spine over the evidence
(`docs/app-by-head-type-design.md`), so no argument is spelled again in an
annotation and every shared node's step is one shared term. Evidence
statements are the only text the rewrite elaborates — once per operation, not
per node — and resolution answers them as it answers `rel_cong`'s. What it
does not find is an **obligation** exactly as `rel_cong` leaves one: a goal
labelled `?compatibility` (`?fixed` for an unchanged argument without
`Reflexive`, `?symmetry`, `?transitivity` at the goal), discharged by
`on ?label := …` in the block or reported with its statement. Nothing is
trusted; the declaration gate checks the term.

### 9.5 Sharing, and what is still a tree

On `rewrite/setoid-let-addr0`, one relation rewrite at the bottom of a
k-let chain changes every link, 2^k paths to the occurrence, and costs k
congruence steps: linear, as the bench family records.

The same round removed §2's tree walks from the equation form. The
abstraction keeps one result per shared node when no occurrence is selected
(`AbstractLocal`'s node memo; a selection numbers occurrences by path, so
`at :=` still walks the tree), and `Type::root_terms` lists and walks each
shared node once, so the motive is a DAG the kernel's typing memo shares and
the candidate search is linear. `rewrite/let-addr0` fell from 2^k to about
k² and `rewrite/let-nary` to its linear bound. What `let-addr0` still pays is
its spelling: k rewrites, each over the whole goal. One rewrite of every
instance of an unapplied law would meet the bound
(`issues/rewrite-every-instance.md`).

There is no memo across steps. mengine keys a persistent one by equation,
context and node, which pays off when one equation is applied again and
again; each step here uses a new equation (§1: `rewrite(h₁, …, hₙ, e)` is n
equations in turn, and an unapplied law is instantiated per step), so its
results would never be asked for again.

### 9.6 What it does not do

Each is a follow-up issue:

- ~~**Under binders**~~: done, §10.
- **`↔` goals** (`issues/rewrite-setoid-iff-goals.md`): `Iff` is a record,
  so its two directions are projections and a constructor the plan would
  build around each half.
- **Leaving the carrier** (`issues/rewrite-setoid-heterogeneous.md`):
  congruence through a function `C → D` needs a relation at `D`, which the
  walk would have to infer per node, as Rocq's `Proper` search does.
- **`at :=`**: refused, with the pointer to
  `issues/relational-rewrite-controls.md`; a DAG walk has no tree positions to
  number.

## 10. Rewriting along a relation under binders

`issues/rewrite-setoid-under-binders.md`, 2026-10-28. §9's walk stopped at a
λ, refusing an occurrence inside one. It now goes in, as Rocq's
`setoid_rewrite` does with `pointwise_relation`: mengine crosses binders by
funext, which Heather does not assume, so the crossing is evidence.

```heather
theorem rewrite_law_under_sum(n: Nat, f: Nat → Rat, e: ∑ k < n, f(k) ≈ 0): ∑ k < n, (f(k) + 0) ≈ 0 {
    rewrite(Rat::add_zero, e)
}
```

### 10.1 The pointwise relation

`relation_props::Pointwise<D, C>(R)(f, g) := (z: D) → R(f(z), g(z))`. A λ's
body is rewritten one binder down; from `p : R(t, t')` there, the λ node's
result is `λ z. t'` with `λ z. p : Pointwise(R)(λ z. t, λ z. t')`, which
checks because the relation unfolds to the Π `p` inhabits up to β. A λ whose
body is a λ (`antidiag`'s `λ i k => …`) is related by
`Pointwise(Pointwise(R))`, one per binder, so one crossing serves a curried
consumer. The relation is non-dependent: a binder whose type mentions the one
before it is refused.

`Respectful(RelId, R)` is not it: that asks `R(f(x), g(y))` of every pair of
equal points, so a proof of it from a pointwise one costs a transport per
point, and nothing gains from the extra generality.

### 10.2 Crossing a binder's consumer

A λ is an argument of something: `MonoidRel::range(op, n, λ k => …)` for
`∑`. That application gets one step, by evidence

```text
PreservesRelation(Pointwise<D, C>(R), R, λ g. f(…, g, …))
```

its context always written as a λ (even in the last position, where §9.3
writes a partial application), because that is how a rule states it: an
argument a function consumes is a λ in the source. Resolution answers it as
§9.4 says — a hypothesis in scope, else an evidence rule, else a
`?compatibility` obligation. A changed λ beside another changed argument is
refused by name: no evidence shape relates both.

The sum's rules live in `big_operator.hthr`, `MonoidRel::range_pointwise` and
`MonoidRel::antidiag_pointwise`, each a corollary of `range_cong`. They are
evidence rules with every parameter in braces, outside the section: a rule
cannot take a class premise (Paterson's measure reads only propositions), and
an instance head cannot key on a λ argument, so the dictionary is a brace the
conclusion's `range(op, n, f)` fixes by unification. One rule serves every
carrier, `Rat` and an open semiring's `+` and `*` alike.

`range_cong` is *bounded*: its premise asks for `f(k) ≈ g(k)` only below the
bound. The rule discards that bound (`λ k _ => h(k)`): a rewrite's per-node
proof never consults a hypothesis, so offering `k < n` to the body would buy
nothing until a rewrite under conditions exists.

### 10.3 Depth, the memo, and instances below a binder

The walk keeps the binders it is below. Results are memoized per node *and
binder scope* — one scope per λ node, not per depth, since two λs at one
depth may bind different types, and evidence and conversion below them
depend on that. A shared λ node is still walked once, at its parent's scope.
The step's left side, right side and proof are shifted once per depth and
kept.

An unapplied law is instantiated by the first node the walk meets that
matches (§6.1), now below binders too, matching in the binders' context.
When the bindings mention a bound variable (`f(k) + 0` against
`(y) → y + 0 ≈ y`) the instance is kept **relative** to the innermost
binders it mentions: `f(k) + 0` under `λ k` is also `f(j) + 0` under a
second sum's `λ j`. The instance's relation and carrier must not mention a
bound variable; that is refused.

### 10.4 Evidence below binders

A context that mentions no bound variable (`range(+, n)` inside an outer
sum, `c * ·`) is looked up at the rewrite's own context, once for every
depth it occurs at, and shifted. One that does (`∑ k < m - i, …` under
`λ i`, or `g(k, ·)`) is stated in the binders' context; there resolution's
answers mention the binders and nothing is kept. Missing there, the
obligation is closed over the binders and applied back to them:

```text
?compatibility : (z: Nat) -> PreservesRelation(Same, Same, g(z))
```

so `on ?compatibility := c` discharges it with `c` a hypothesis for every
index. An unchanged argument without `Reflexive` evidence is the same
(`?fixed`).

### 10.5 What it does not do

- Dependent binders, and a sum's bound offered to its body (§10.2).

`rel_cong`/`rel_derive` under binders (§10.6) and laws about a class's
operation (§6.1, `Semiring::mul_range_l` at an open semiring, which is the
case that bites below a binder: its arguments mention the bound index) were
follow-ups of this round. `big_operator.hthr`'s `range_mul_range` and
`range_cauchy` are now one `rewrite(Semiring::…, …)` each; its other
`range_cong` proofs use the bound `k < n`, which a rewrite does not offer.

### 10.6 `rel_cong` and `rel_derive` under binders

`issues/rel-cong-under-binders.md`, 2026-10-28. `rel_cong(h)` walks the
goal's two sides in lockstep (§9.3's ancestor), and stopped at a λ. Now an
application whose two sides differ in exactly one argument, a λ on each side,
is crossed as the rewrite crosses it: the λs' shared binders (as many as both
have with the same type, non-dependent) give the relation
`Pointwise<D₁, …>(…(R))`, the consumer's evidence is
`PreservesRelation(Pointwise(R), R, λ g. f(…, g, …))` — §10.2's statement,
so `MonoidRel::range_pointwise` answers both tactics — and its proof
argument is `λ z₁ … zₖ. p` for `p : R(a, b)`, the bodies walked below the
binders.

The builder spells its proof as source text over aliases at the goal's depth.
Below a binder it keeps that shape one level down: the binder is pushed onto
its context, the body walked there (aliases, evidence, the supplied proof's
sides shifted once per depth), the text elaborated *there* to a term, and the
context restored, so nothing made below survives — it mentions the binder.
The λ around that term is aliased at the outer depth with its pointwise type.
Evidence missing below binders is an obligation closed over them and applied
back, §10.4's `(z: Nat) -> PreservesRelation(Same, Same, g(z))`. A consumer
whose context does not map those functions into the carrier is not crossed,
and the walk goes on to its other rules, ending in the usual mismatch.
