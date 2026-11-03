# Coinductive interaction trees

Status: round 1 implemented, 2026-10-22 (`lib/std/itree/coitree.hthr`,
`crates/elab/tests/lib_std_coitree.rs`); eutt and the bridge to programs
(§7) implemented the same day (`lib/std/itree/coitree_eutt.hthr`,
`crates/elab/tests/lib_std_coitree_eutt.rs`); loops and binds against the
fuelled programs (§8) on 2026-10-24 (`lib/std/itree/coitree_bridge.hthr`,
`crates/elab/tests/lib_std_coitree_bridge.rs`). Milestone `it-coinductive`
(`docs/roadmap.md`); issue `issues/coitree-library.md`. It builds on the
`codata` surface (`docs/codata-elaborator-design.md`,
`docs/codata-indexed-design.md`) over the kernel's `M`
(`docs/kernel-coinduction-design.md`), and on the finite library
(`lib/std/itree/itree.hthr`, `lib/std/itree/itree_trace.hthr`).

---

## 1. What it adds

The finite `ITree<R>(E)` has a `Cut` leaf: a program is a family of trees
indexed by fuel, growing along `ITree::Below`, and divergence is a property
of the family ("no member returns"). `CoTree<R>(E)` is the same three nodes
without `Cut`, as codata: one value is the whole, possibly infinite, tree.

```
codata CoTree<R>(E: Events) {
    CRet(r: R),
    CTau(t: CoTree<R>(E)),
    CVis(c: E.Cmd, k: E.Resp(c) → CoTree<R>(E)),
}
```

`spin` is `CTau(spin)`, and `iter` goes round its body with no fuel (each
`Continue` is guarded by a `CTau`, so every pass is productive). The finite
library stays the place where traces and refinement are proved:
`approx(n, t)` cuts a tree at depth `n`, the approximations grow
(`approx_grows`), and so `CoTree::program(t)` is a `Program` whose members
are its approximations. `spin_diverges` is then `Program::Diverges` with no
fuel argument anywhere.

## 2. Observations, not constructors

There is no η for `M` (kernel design §0) and no dependent `match` on codata
(indexed §5): a tree is never *equal* to the constructor it observes as, and
a proof cannot case on a tree and learn which node it is. What a proof can
take apart is the tree's **observation**,

```
inductive Obs<R>(E: Events) { ORet(r: R), OTau(t: CoTree<R>(E)), OVis(c, k) }
fn CoTree::obs(t) → Obs { match t { CRet(r) => ORet(r), … } }
```

an ordinary inductive with the same three cases whose children are trees.
`obs(tree(o)) = o` by `refl`; the other direction is a bisimilarity
(`Bisim::tree_obs`). Two habits follow, and the library keeps both (they
are Coq's `_observe` style, which has the same lack of η):

- **Corecursion is seeded by an observation.** `bind_obs(o, h)` matches on
  `o : Obs`; `bind(t, h) := bind_obs(obs(t), h)`. A corecursive self-call
  is `bind_obs(obs(s), h)` at the child `s`. The unfolding law
  `obs(bind(t, h)) = Obs::bind(obs(t), h)` is then a `match` on the
  observation with `refl` in each case, and after δ a proof meets `obs(t)`
  *syntactically*, where `j` can rewrite it (`obs_bind_at`).
- **A proof about a tree matches its observation with the convoy**,
  `match h : CoTree::obs(E, t) { … }`, and carries `h : obs(t) = ORet(r)`
  (etc.) into what it builds.

`translate` and `iter` are written the same way. `map` is `bind` with
`CRet ∘ f`.

## 3. Strong bisimilarity

`Bisim` is indexed codata over two trees, each constructor stating both
trees' observations and relating the children again:

```
codata Bisim<R>(E: Events) : (t: CoTree<R>(E)) → (u: CoTree<R>(E)) → Type {
    BRet(r, ht: obs(t) = ORet(r), hu: obs(u) = ORet(r)),
    BTau(t2, u2, ht: obs(t) = OTau(t2), hu: obs(u) = OTau(u2), next: Bisim(t2, u2)),
    BVis(c, k1, k2, ht: obs(t) = OVis(c, k1), hu: obs(u) = OVis(c, k2),
         next: (a: E.Resp(c)) → Bisim(k1(a), k2(a))),
}
```

The command is shared (`c` once), so the relation never compares commands;
the equations are what tie it to the two trees, as indexed §1 prescribes.

- `refl` (convoy on `obs(t)`), `sym` (swap), `of_obs` (equal observations
  give a bisimilarity, the children related by `refl`).
- **`trans`** meets the middle tree's two observations. Matching on the
  first relation says what `obs(u)` is; the second relation is read through
  `Bisim::step(u, v, b) : Obs::BisimTo(obs(u), v)`, a type computed from an
  observation alone, as `ITree::Same` is read off its left tree
  (`itree.hthr`). Moving `step`'s result along `obs(u) = OVis(c, k2)` by `j`
  gives `VisTo(c, k2, v)`: `v` observes as `OVis(c, k3)` with
  `k2(a) ~ k3(a)` for every `a`. Neither the command equation nor the
  dependent continuations ever need transporting, and the mismatched cases
  never arise.
- **The monad laws up to bisimilarity:** `bind_ret_l` (`of_obs` by
  `refl`), `bind_ret_r` and `bind_assoc` (corecursive, with `obs_bind_at`
  rewriting each side's observation), `map_id`.
- **A congruence for `bind`:** `t ~ u` and `h1(a) ~ h2(a)` for every `a`
  give `bind(t, h1) ~ bind(u, h2)`, corecursive on the first relation; at a
  leaf it re-observes the continuations' relation through `obs_bind_at`.
- **The bridge to the finite library:** `Bisim::approx` — bisimilar trees
  have `ITree::Same` approximations at every depth, by induction on the
  depth and two `j` rewrites per case.

## 4. What stayed out of round 1

- **eutt** (weak bisimilarity, finitely many `CTau`s peeled on either side):
  §7.
- **The bridge to the fuelled programs**: bisimilar and eutt-related trees
  give programs that refine each other (§7.4), and `CoTree::program(iter(…))`
  and `Program::iter` refine each other (§8).
- **Certgen and export** refuse codata (codata §7), so nothing here is
  exported yet.

## 5. Cost

The library was what `docs/codata-named-signature-design.md` was written
for: before naming each codata signature, a proof over `Bisim<R>(E, t, u)`
paid for the nested inline signatures of both trees at every node. With the
names, proofs check in time proportional to their size, and the longest
declarations are the ones with the most `j` rewrites (`Bisim::approx`,
`bind_assoc`).

## 6. Testing

`crates/elab/tests/lib_std_coitree.rs` (the `family_library` binary), on the
axes of `docs/testing-generated-terms.md`:

- the module checks from images, and every item of the kit is named;
- **literal and open**: approximations of `spin` at depth 2 and at
  `Succ(n)`, a counting loop's observation and approximation at literals,
  and `iter_continue` at an open counter;
- **open element type and events**: every law is stated over `R`/`A, B, C`
  and an arbitrary `E`;
- **checking position**: a client's own corecursive `Bisim` (`spin ~ spin`)
  whose observation equations are `refl` in each constructor; the bridge
  and `trans` used at a composite;
- **negative controls**: a wrong approximation and a bisimilarity between
  different leaves are refused by conversion;
- a goal over `Bisim` names it with its trees.

## 7. Equivalence up to taus

`lib/std/itree/coitree_eutt.hthr`. Issue `issues/coitree-eutt.md`.

### 7.1 Counts instead of an inductive peel

Kernel design §4 spells eutt as an `M` whose shape is an inductive peel. The
surface has no inductive part in a codata shape, and needs none: a drop is a
count. `after(n, t)` is what `t` observes after dropping up to `n` leading
`CTau`s, stopping at the first node that is not one, so a count larger than
the number of taus is harmless.

```
codata Eutt<R>(E: Events) : (t: CoTree<R>(E)) → (u: CoTree<R>(E)) → Type {
    ERet(nl, nr, r, ht: after(nl, t) = ORet(r), hu: after(nr, u) = ORet(r)),
    ETau(nl, nr, t2, u2, ht: after(nl, t) = OTau(t2), hu: after(nr, u) = OTau(u2), next: Eutt(t2, u2)),
    EVis(nl, nr, c, k1, k2, ht: after(nl, t) = OVis(c, k1), hu: after(nr, u) = OVis(c, k2),
         next: (a) → Eutt(k1(a), k2(a))),
}
```

This is Coq's `eutt` with `EqTauL`/`EqTauR` counted rather than stacked.
`ETau` is still needed: two trees that both step silently forever are
related by `ETau` at every node, and a tree that diverges silently is related
to no tree that returns or calls. `Bisim` is `Eutt` with every count zero
(`of_bisim`), so `refl`, the monad laws and anything else proved step for
step carry over; `tau_l` (`CTau(t) ≈ t`) and `sym` are direct.

### 7.2 Moving counts

Two operations take a relation apart along the left tree's taus:

- `peel_l`: more taus in front of the left tree. If `t` reaches `CTau(s)`
  after `k` drops and `s ≈ u`, then `t ≈ u` with every left count raised by
  `k + 1` (`after_join`).
- `drop1`/`drop_l`: fewer. If `obs(t) = OTau(s)` then `t ≈ u` gives `s ≈ u`:
  a positive count goes down by one (`after_drop1`), and a zero count was an
  `ETau` at `t` itself, whose child is `s` already (`drop1_tau`). `drop_l`
  iterates it along `after(n, u) = OTau(u2)`.

The proofs by recursion on a count follow one rule: the convoy
`match h0 : obs(t)` refines the goal, so the hypotheses that mention
`after(Succ(m), t)` are taken as arrows after the match and arrive already
reduced (`after(m, t1) = …` in the `OTau(t1)` arm, a constructor clash in
the others).

### 7.3 Transitivity

`trans(a: t ≈ u, b: u ≈ v)` corecurses on `a`. Where `a` stops at a leaf or a
call of `u`, `b` is read at that observation: `to(b, h)` turns
`after(n, u) = o` (with `o` settled) into `Obs::EuttTo(o, v)`, which says `v`
settles at the same leaf, or at the same call with continuations related to
`u`'s (`EuttRetAt`, `EuttVisAt`). `to` drops `u`'s taus one at a time with
`drop1`, so it never needs injectivity of observations or a transported
continuation, the same reason `Bisim::trans` reads through `BisimTo`
(§3).

Where `a` steps silently to `(t2, u2)`, `b` is advanced past the same taus of
`u` (`drop_l`) and matched:

- a leaf or a call of `u2`: `sym(next)` read with `to` says where `t2`
  settles, and `t`'s count is raised past `t2` (`after_via`);
- a silent step of `u2`: `ETau` on `t2` and `v`'s child, with the
  corecursive call on `next` and `b`'s child pushed back over the taus it
  dropped (`peel_l`).

Every corecursive call is guarded by the node it builds, and the state is
the whole tuple of trees and relations. Inside `Eutt::trans` the bare name
`trans` is the declaration itself (a member's base name is its recursion
name), so the prelude's equality `trans` is not available by that name
there; `after_via` packages the one composition it needed.

### 7.4 Programs

`Eutt::refines(e)`: `t ≈ u` gives
`Program::Refines(CoTree::program(t), CoTree::program(u))`, and `refined`
the converse through `sym`. Each trace of `approx(n, t)` is one of some
`approx(n', u)`, by induction on `n` (`Eutt::traces`):

- a silent step of `t` is dropped off the relation (`drop1`), at depth
  `n - 1`;
- a leaf or a call is read with `to0` where `u` settles, after `m` drops;
  `converges_after` lifts a trace of `u`'s settled observation to `u`
  itself, because the drops are `Tau`s and traces do not see them. A call's
  answered trace recurses into the continuations.

`Bisim::refines` is the same statement through `Same` approximations
(`Bisim::approx`, `ITree::refines_of_same`).

### 7.5 `bind` is a congruence

`Eutt::bind_cong`: `t ≈ u` and `h1(a) ≈ h2(a)` for every `a` give
`bind(t, h1) ≈ bind(u, h2)`, corecursive on `t ≈ u` as `CoTree::bind_cong`
is on `Bisim`. `bind_cong_l` and `bind_cong_r` fix one side.

- A silent step or a call carries over at the **same counts**:
  `after(k, t) = o` with `o` not a leaf gives `after(k, bind(t, h)) =
  Obs::bind(o, h)` (`CoTree::after_bind`, by induction on `k` with
  `obs_bind_at`). A leaf reached early is excluded by `Obs::NotRet`: there the
  remaining drops would spill into `h(r)`.
- At a leaf the count is only an upper bound, so the counts do not shift
  into `hh(r)`. The branch is an existing relation instead,
  `bind(t, h1) ≈ h1(r) ≈ h2(r) ≈ bind(u, h2)` by `trans`, which the
  corecursive surface takes as a whole node (codata §5.2).
  `Eutt::bind_leaf` gives `bind(t, h) ≈ h(r)` from `after(k, t) = ORet(r)`,
  by recursion on `k` (`peel_l` per tau).

### 7.6 What is not here

- **Up-to techniques** (a corecursive call under `trans` or `bind`). The
  `codata` surface's guard is constructors (codata §5.2, §5.4), not
  functions, or friends on unindexed codata (codata §5.5); `Bisim`/`Eutt`
  are indexed, so every proof here is written so its self-calls sit under a
  constructor (`issues/codata-up-to-friends-round-2.md`). §7.9's proofs show
  the way round that so far: a self-call that would sit under `trans` is
  avoided by generalising the hypothesis to a relation the step lands in.

### 7.7 Cost

Before the change in `docs/codata-named-signature-design.md` §8, a `match`
on an `Eutt` bound each payload field to a projection annotated with every
earlier field's type, and the constructor's children were shifted copies of
those projections; `sym` paid for a term whose tree size grew with the
product of the fields' dependencies. With checked projections the module is
dominated by `trans`, `traces_vis` and the declaration itself, each in
proportion to its size.

### 7.8 Testing

`crates/elab/tests/lib_std_coitree_eutt.rs` (the `family_library` binary):

- the module checks from images, and every item of the kit is named;
- **literal and open**: counts at literal trees by `refl`
  (`CTau(CTau(CRet(1))) ≈ CRet(1)` with counts `2, 0`, and counts larger than
  needed), `after` at an open count;
- **open element type and events** throughout;
- **checking position**: a client's own corecursive `spin ≈ spin` with
  different counts on each side, and `trans` composing silent steps;
- **negative controls**: a count too small to reach the leaf, and different
  leaves, are refused by conversion;
- the bridge used at `CTau(CTau(t))` and at `bind(t, CRet)`, and a goal over
  `Eutt` names it with its trees;
- `bind_cong` at a literal tree with taus on both sides of the bind, at a
  neutral tree through each side, into refinement, and a leaf continued at
  another value refused (`lib/_tests/std/itree/coitree_eutt_tests.hthr`).

### 7.9 Loops, recursion and readings up to taus

`issues/eutt-iteration-and-io-reading.md` (2026-11-03). Every proof is
direct corecursion; none waits on up-to coinduction.

- **One tool for every function of trees.** `CoTree::after_map`: a function
  `F` that is a function `Fo` of observations (`obs(F(t)) = Fo(obs(t))`) and
  maps a silent step to a silent step takes `after(k, t) = o` to
  `AfterIs(F(t), Fo(o))`, a count of its own and `after(m, F(t)) = Fo(o)`.
  The count is `t`'s real number of drops, not `k`: a function that turns a
  settled node into a silent step (a loop going round, a call being
  answered) would otherwise spill the rest of `k` into what follows.
  `iter_from`, `mrec` and `Io::against_co` are instances, each by `refl`.
- **`Eutt::iter_from_cong`** (`iter_cong` at a start): pending passes
  `t ≈ u` and bodies `hb(a): body1(a) ≈ body2(a)` give equivalent loops. A
  `Continue(a)` leaf is one `CTau` on both sides to the next passes, which
  `hb(a)` relates, so the self-call sits under `ETau`. `iter_from(body, t)`
  is the loop resumed inside a pass; `iter(body, a)` is `iter_from(body,
  body(a))` by `δ`.
- **Unfolding.** `CoTree::iter_unfold` is a `Bisim`: `iter(body, a)` is
  `bind(body(a), iter_next)` with `iter_next(Continue(a)) = CTau(iter(a))`.
  `Eutt::iter_unfold` drops the tau (`iter_again`).
- **Recursion.** `Eutt::mrec_cong`/`rec_cong` (pointwise-equivalent bodies,
  equivalent pending trees). At a command of the pending tree the two sides'
  step is classified once by `CoTree::mrec_step` (a `match c as …`), into
  an inductive `MrecStep` the corecursive body matches on: a call is a
  silent step to `bind(body(d), k)` on both sides, related by `bind_cong`;
  a command of `E` is answered as `CTau(mrec(k(a)))`, which is
  `mrec(CTau(k(a)))` by `δι`, so the children are runs again with no nested
  constructor. `Eutt::mrec_bind`: running `bind(t, k)` is running `t` then
  `mrec ∘ k`. Stated plainly it needs up to `trans` at a call, where the
  bind reassociates (`bind_assoc` is only a `Bisim`); generalised over a
  pending tree `p` with `Bisim(p, bind(q, k))` it is direct, the
  reassociation landing in the hypothesis.
- **`Returns::eutt`**: a return is seen through `Eutt` (`Eutt::to`), so specs
  stated with `Returns` never mention it.
- **The world's reading** (`lib/std/os/linux/linux_world_co.hthr`,
  `docs/effects-capabilities-design.md` §4): `Io::against_co` answers each
  `CVis` from the world as one `CTau`; `against_co_cong`, `against_co_bind`
  (a `Bisim`), `Io::Reads` as `Eutt` at every world, `reads_ret`,
  `reads_trigger`, `reads_bind`, and the loop lemma `reads_iter`. The loop
  lemma's plain statement needs up to `trans` (the next pass's reading is
  only equivalent to the step's); `Io::reads_loop` generalises it to "the
  pass's reading is equivalent to the iteration's pending pass `u`" and
  traces each silent step or return of the reading back to the pass
  (`pass_tau`, `pass_ret`, by induction on the count).

---

## 8. Against the fuelled programs

`lib/std/itree/coitree_bridge.hthr`; issue
`issues/coitree-program-bridge.md`. The finite library builds programs out
of fuel (`Program::iter`, `Program::bind`), and a coinductive tree is a
program through its approximations. The two produce the same traces, so
each refines the other, and a theorem proved on one side carries to the
other with no fuel in its statement.

### 8.1 The embedding

`CoTree::of_tree(t)` copies a finite tree constructor for constructor, with
`Cut` as `spin`. It is a corecursive function whose seed is the finite tree
(the `match` is on an inductive, so nothing about codata is new), and
`spin` at the `Cut` is an existing tree returned whole. Neither a `Cut` nor
`spin` produces anything past the empty trace, so the embedding has exactly
the tree's traces: `of_tree_traces` by induction on the depth,
`of_tree_converges` by induction on the tree, and `of_tree_refines` /
`of_tree_refined` against `Program::tree(t)`, the tree at every fuel.

Approximation is not a left inverse of the embedding at any fixed depth (a
tree with an infinitely branching call has no depth bound), which is why the
statements are about traces and not `Same`.

### 8.2 Loops

`CoTree::iter_refines` and `iter_refined`: for a finite body,
`CoTree::program(CoTree::iter(of_tree ∘ body, a))` and
`Program::iter(body, a)` refine each other. Both loops are read from the
middle of a pass: `ITree::iter_rest(n, body, t)` is what is left of a pass,
`t`, followed by `n` more passes, and `CoTree::iter_rest(body, t)` the same
with no fuel. A whole loop is the pass `body(a)`, by `δβ`.

- **Depth to fuel** (`iter_traces`, induction on the depth `n`): fuel counts
  passes and depth counts constructors, and every pass costs at least one
  constructor (the `CTau` before the next pass), so depth `n` is within `n`
  more passes. A silent step or a call of the pass spends depth and no fuel;
  the fuel left over is grown back by `ITree::iter_pass_grows` (in
  `itree_trace.hthr`, beside `iter_grows`, which now uses it). The whole
  loop then takes fuel `n + 1`, the pass itself being the first.
- **Fuel to depth** (`iter_converges`, induction on the fuel, and inside it
  `iter_pass_converges`, induction on what is left of the pass): the depth is
  read off the trace's derivation, one more for each constructor it goes
  through, the passes after the current one handed in as `IterFrom(n)`.
  This is the only place the proof needs two inductions, and it keeps them
  apart (`IterFrom` is the outer one's hypothesis) because recursion is
  structural on one argument.

### 8.3 Sequencing

`CoTree::bind_refines` and `bind_refined`: for any coinductive `t` and `h`,
`CoTree::program(bind(t, h))` and
`Program::bind(CoTree::program(t), CoTree::program ∘ h)` refine each other.
This is stronger than the issue asked (a finite tree embedded), and the
finite case follows through §8.1.

- `bind_traces`: depth `n` of the bind is within depth `n` of each side.
  The continuation is reached one constructor later on the bind's side than
  the shared fuel allows, so it is grown back along `approx_grows`.
- `bind_converges`: depth `n` of `t` and `k` of `h` is within `k + n` of the
  bind (`k + Succ(m)` is `Succ(k + m)` by computation, so the induction is on
  `n`); a leaf of `t` raises `h`'s depth with `IsTrace::up`.

Both are written as the eutt bridge is (§7.4): one level at an observation
`o` with `obs(t) = o` as a hypothesis, the recursion's hypothesis named as a
type (`BindTracesAt`, `BindConvergesAt`), and `obs_bind_at` moving the
bind's observation.

### 8.4 Testing

`crates/elab/tests/lib_std_coitree_bridge.rs` (the `family_library`
binary): the kit; the embedding's observations at a literal and an open tree
and at `Cut`, by `refl`, and a wrong leaf refused; a literal loop that
returns at fuel 3 and depth 5, carried across both ways and for an open
body, with too little fuel and too little depth refused; an embedded `Cut`
claiming nothing, and a bind's return carried from the bound programs.

---

## 9. Recursion

`lib/std/itree/coitree_rec.hthr`: `CoTree::rec` runs a body whose calls to
itself are events, as a loop over the pending tree. It is the fuel-free
`ITree::rec`. With it come fixpoint induction, termination by a measure and
`CoTree::get`, so a partial function can be specified with no fuel. The
design is in `docs/partial-functions-design.md` (§8 says what was built).
Not yet done: the refinement against `Program::rec`
(`issues/coitree-rec-program-bridge.md`).
