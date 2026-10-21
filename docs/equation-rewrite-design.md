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

1. `M := G.abstract_local(a)` — a type over `Γ, y : S` with every occurrence
   of `a` replaced by `y`. Occurrence is `==` on de Bruijn terms; no
   conversion call, so the walk is linear (the synthesis's §3 decisions,
   inherited, not re-made).
2. `M` is checked to be a type, at the goal's level, by the kernel's type
   formation. Abstracting a term that something *else's* type depends on —
   `v : P(n)` in a goal `v = v`, rewriting `n` — leaves `Id(P(y), v, v)`,
   which is not one. The error says so and points at `j`; it is not left to
   the declaration gate, whose message would name a motive nobody wrote.
3. `e` is checked at `M[b/y]`.
4. The term is `J(sym h; y q. M; e) : M[a/y]`, and `M[a/y]` is `G`
   **syntactically**, because the abstraction replaced only positions that
   held `a`. `sym h` is written out as `J(h; y q. y = a; refl a)`, so the
   form needs no library import.

Nothing is trusted: the declaration still passes the kernel gate.

**Where `a` is looked for.** The goal as written, then — only when that finds
nothing — its exposed form (head and an equation's sides one weak-head step
down, the synthesis's §4.3 rung). Not deeper, and not up to conversion. A
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

- **No relations other than `=`.** A proof of `≈`, `<=` or a setoid relation
  is refused with a pointer to `rel_cong(h)` and `calc`. The maths library's
  `Rat`/`CReal` rewriting is mostly setoid rewriting, which is
  `relational_context`'s; this form serves `Nat`, `Int`, lists, bit-vectors,
  and the interaction-tree laws stated with `=`.
- **No rewriting in hypotheses.** Lean's `rw … at h` is `rewrite` applied to
  the hypothesis's *type* as a goal, which is a different elaboration (the
  hypothesis is a term to transport, not a goal to prove) and has no
  customer yet.
- **No search.** It does not try `sym`, unfold the goal beyond one exposed
  layer, or match up to conversion. Each would be a guess with a cost on
  every miss.

Follow-ups are filed: `issues/rewrite-lemma-instantiation.md`,
`rewrite-keyed-conversion-matching.md`, `subst-local-equation.md`,
`rewrite-in-hypothesis.md`, `rewrite-pattern-occurrences.md`,
`rewrite-setoid-relations.md`, `rewrite-conveniences.md`.
