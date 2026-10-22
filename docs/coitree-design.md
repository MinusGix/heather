# Coinductive interaction trees

Status: round 1 implemented, 2026-10-22 (`lib/std/coitree.hthr`,
`crates/elab/tests/lib_std_coitree.rs`). Milestone `it-coinductive`
(`docs/roadmap.md`); issue `issues/coitree-library.md`. It builds on the
`codata` surface (`docs/codata-elaborator-design.md`,
`docs/codata-indexed-design.md`) over the kernel's `M`
(`docs/kernel-coinduction-design.md`), and on the finite library
(`lib/std/itree.hthr`, `lib/std/itree_trace.hthr`).

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

## 4. What stays out of this round

- **eutt** (weak bisimilarity, finitely many `CTau`s peeled on either side):
  kernel design §4 spells it as an `M` with an inductive peel in the shape.
  `issues/coitree-eutt.md`.
- **The bridge to the fuelled programs**: that `CoTree::program(iter(…))`
  and `Program::iter` refine each other, and that bisimilar trees give
  equivalent programs (`Bisim::approx` is the core of the second).
  `issues/coitree-program-bridge.md`.
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
