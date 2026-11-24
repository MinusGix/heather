# Scoped proof worlds: inside-to-outside internal logics (`within`)

Status: **design and v1 implementation**, 2026-11-23. Tracked by
`issues/proof-worlds.md` (`area: language`, `milestone: [lang-proof-modularity]`).

## 1. The idea

Many proofs are dramatically cleaner when written inside a **proper inside
representation** (an internal logic or modality) and translated back to an
**outside representation** (an ordinary Heather proposition and constructive
proof term) at the scope boundary:

- **Double negation (`Dne<P>`):** inside the block, classical excluded middle
  `Dne::em(P) : Dne<P ∨ ¬P>` is provable **constructively with zero axioms**;
  exiting requires `Stable<G>` (`¬¬G → G`), which holds for `False`, `¬P`,
  `And`, any `Decide<G>`, and `CReal::Le` (`¬(y < x)`).
- **Propositional truncation (`Squash` / `∥P∥`):** inside the block, a
  squashed witness `q : ∥A∥` opens via `let x <- q;`; exiting works for
  `False`, `∥G∥`, or any `Decide<G>`.
- **Directed filters (`Eventually<I>(le, P)`):** inside the block, an index
  variable `n : I` is in scope and `let u <- e;` pulls in any fact that holds
  eventually along `(I, le)`, automatically combining thresholds via
  `Directed<I>(le)::combine` (`Nat::max`, `Rat::min`, set union, stack room)
  with no manual `max`/`le_trans`/`omega` plumbing. When the outer goal does
  not mention `n`, the block exits automatically via `Eventually::extract`.
- **Custom user worlds:** any `Bind`/`Pointed` carrier with an exit function
  `M(G) → G`, or any indexed predicate world with `always`/`use`/`extract`.

**No kernel change and no trusted rule.** Both forms of `within` lower to
ordinary Heather calls (`Bind::seq`, `Pointed::ret`, `W::exit`, `W::always`,
`W::use`, `W::extract`) and are checked by the kernel like handwritten proofs.

---

## 2. Surface syntax

Two forms, both headed by the contextual keyword `within` (Rule 1 of
`docs/language/let-and-blocks-design.md` §5.2: recognized only when an
identifier follows `within`, so local variables, parameters, and methods
named `within` keep working everywhere):

### 2.1 Monadic proof world: `within W { body }`

```heather
theorem creal_le_example(x, y: CReal): x <= y {
    within Dne {
        if lt: x < y {
            CReal::le_of_lt(lt)
        } else {
            ... // lt : ¬(x < y)
        }
    }
}
```

`W` is either:
- a **world type/namespace** that defines `W::exit` (such as `Dne` or
  `Squash`), or
- any **exit expression** `f : M(G) → G` (such as `Dne::exit`,
  `Squash::recover`, `unsquash_empty`, or a user's `or_zero`).

Inside `{ body }`:
- `let x <- e;`, `e;`, `(<- e)`, and `match <- e` work via Heather's existing
  `Bind::seq` lowering (`docs/language/sequencing-surface-design.md`).
- **Native classical `if` inside `Dne`:** inside any `Dne<_>` goal (including
  `within Dne { … }`), `if [h:] P { yes } else { no }` (and chained `else if`)
  tries decidable `if` (`Decide<P>` / `Bool`) first; if no `Decide<P>` instance
  exists and `P` is a valid proposition type, it falls back constructively to
  `Bind::seq(Dne::em(P), λ #dne_em => match #dne_em { Inl(h) => yes, Inr(h) => no })`
  with zero axioms.
- **Direct `within Squash` on primitive `∥A∥`:** `Bind<λ (A: Type) => ∥A∥>` and
  `Pointed<λ (A: Type) => ∥A∥>` resolve directly against `∥A∥` via
  `constructor_spelling`, so `within Squash { let h <- q; … }` and
  `within Squash::recover { let h <- q; … }` work directly on `q : ∥A∥` with no
  wrapper record.
- Tail leaves of `{ body }` (descending through nested blocks, `match` arm
  bodies, and `if` branches) are wrapped in `Pointed::ret(...)` automatically,
  so branches write ordinary proofs of `G` rather than repeating
  `Pointed::ret(...)`. A tail leaf written `(<- e)` unwraps directly to `e`
  (already in `M(G)`). An empty `match h {}` has zero leaves and checks
  directly at `M(G)`.
- At the boundary: if `W` is a world type whose head already matches the
  expected type (e.g. a helper returning `Dne<P>`), the lowered block is
  elaborated directly without calling `W::exit`; otherwise `W::exit` (or `W`
  itself when `W` is an exit expression) wraps the lowered block.

### 2.2 Pointwise / indexed proof world: `within W for x { body }`

```heather
// Goal is `Eventually<Nat>(Nat::Le, λ n => P(n))`:
within Eventually for n {
    let u <- hx;    // hx : Eventually<Nat>(Nat::Le, A)  ⇒  u : A(n)
    let v <- hy;    // hy : Eventually<Nat>(Nat::Le, B)  ⇒  v : B(n)
    combine_proof(n, u, v)
}

// Goal is `G` (does not mention `j`): `require` synthesizes eventual facts
// from registered `evidence theorem`s and exits automatically via `extract_with`:
within Eventually for j: Nat {
    require g1: Rat::inv_pow2(j) + Rat::inv_pow2(j) <= 1;
    require sc: W * Rat::inv_pow2(j) <= Rat::inv_pow2(m);
    let g = Rat::inv_pow2(j);
    let p = h.at(j);
    ... // proves G
}
```

An optional type annotation on the index binder is allowed:
`within Eventually for n: Nat { ... }`. Inside `within W for x`, `require [h:] P;`
is a contextual statement that lowers to `let h <- W::synth(λ x => P);`,
resolving `Eventually<I>(o.le, λ x => P)` from registered `evidence theorem`s
(using `DefaultOrder<I>`, e.g. `Nat::Le` for `Nat`).

---

## 3. Lowering of `within W for x { body }`

Inside a pointwise world `W` (any type/namespace providing `W::always`,
`W::use`, and `W::extract`):

1. **Statement partitioning.** Walk the block's top-level statements in order,
   tracking `inner_vars = { x }`:
   - A pure `let y = rhs;` / `have y = rhs;` / `let { ... } = rhs;` whose RHS
     mentions no variable in `inner_vars` (and does not shadow a name in
     `inner_vars`) stays in `outer_stmts`, outside `λ x`. Thus a pure binding
     like `let h = e / 2;` before `let u <- hx(h, ph);` is in scope for `e`.
   - A pure binding whose RHS mentions a variable in `inner_vars` (e.g.
     `let p = h.at(j);`) goes into `inner_stmts`, and its bound name(s) join
     `inner_vars`.
   - A binding statement `let pat <- e;` or expression statement `e;` records
     `(pat, e)` in `binds` and adds its bound name(s) to `inner_vars`. If `e`
     mentions any variable in `inner_vars`, parsing/lowering refuses it with a
     clear error: a filter threshold cannot depend on the universally
     quantified index `x` or on an earlier bound fact.
2. **Combinator chain.** For `binds = [(p₁, e₁), …, (pₖ, eₖ)]`:
   - When `k = 0`: `W::always(λ x => { inner_stmts; tail })` (or
     `W::extract(W::always(…))` when exiting to a constant goal `G`).
   - When `k = 1`: `combined = e₁` and `lam = λ x p₁ => { inner_stmts; tail }`.
   - When `k ≥ 2`: fold `e₁, …, eₖ` bottom-up via `W::both` (`combined =
     W::both(… W::both(e₁, e₂) …, eₖ)`), projecting each `pᵢ` from `#wboth`
     at the head of `lam = λ x #wboth => { …; inner_stmts; tail }`.
   - Because `combined` infers `I`, `le`, and the combined predicate
     completely bottom-up with no metavariables, passing `(combined, lam)` to
     `W::map` (when staying in `W` or in inference position) or
     `W::extract_with` (when exiting to a constant goal `G`) puts `x` and
     every `pᵢ` in full checking position with zero annotations and linear
     term size.
3. **Boundary dispatch.** The elaborator checks whether the expected type's
   WHNF is already headed by `W`:
   - If yes (e.g. `Eventually<I>(le, Q)`), elaborate `acc_k` directly.
   - If no (e.g. a constant goal `G`), elaborate `W::extract(acc_k)`.
   - In inference position, elaborate `acc_k` directly (yielding `W(Q)`).

---

## 4. Library: `lib/std/core/world.hthr`

| Item | Purpose |
|---|---|
| `record Dne<P> { run: ¬¬P }` | Constructive double-negation proof world (`Bind<Dne>`, `Pointed<Dne>`) |
| `Dne::em<P>() → Dne<P ∨ ¬P>` | Constructive excluded middle inside `Dne` (zero axioms) |
| `Dne::by_contradiction<P>(f: ¬P → False) → Dne<P>` | Proof by contradiction inside `Dne` |
| `class Stable<P> { dne: ¬¬P → P }` | Types that can exit `Dne` (`False`, `Not`, `And`, `Iff`, plus `Stable::of_decide`) |
| `Dne::exit<P>(m: Dne<P>, s: Stable<P> := infer) → P` | Boundary exit for `within Dne { ... }` |
| `Squash::exit` / `class SquashOut<P>` | Boundary exit for `within Squash { ... }` (`False`, `∥A∥`, `Decide<P>`) |
| `class Directed<I>(le: I → I → Type)` | Any directed preorder (`base`, `refl`, `trans`, `combine`, `left`, `right`); `Nat` under `Nat::Le` (`max`) |
| `record Eventually<I>(le, P)` | Pointwise filter world with `always`, `use`, `both`, `map`, `from`, `of`, `extract` |

---

## 5. Future extensions

- **Filter instances beyond `Nat`, multi-index `within Eventually for m, n`,
  and `Slack` world** (`issues/proof-worlds-multi-index-and-slack.md`): `PosRat`
  under `>=` (`min`), `FinSet` under `⊆` (`union`), and approaches
  (`issues/asymptotic-relations.md`).
- **Native verification worlds** (`issues/proof-worlds-native-wp.md`):
  weakest-precondition / framing (`within Wp`), stack-room budgets, and
  coinductive bisimulation (`within Bisim`).
- **Nested `let <-` inside `match`/`if` arms of `within W for x`:** lifting
  branch-local filter facts when needed.
