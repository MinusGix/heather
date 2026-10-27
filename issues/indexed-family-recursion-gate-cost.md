---
title: Recursion over typed-syntax and function-field families is superlinear in constructors, nearly all in the gate
status: closed
labels: [kernel,elaboration,inductives,performance]
area: language
milestone: [math-metatheory]
created: 2026-10-26
updated: 2026-10-27
---

Found by the intricate-inductive bench families
([[intricate-inductive-bench-families]], `inductive/typed-syntax` and
`inductive/function-fields`). Both declare cheaply; a structural `size`
over them and a one-step `refl` unfolding are where the time goes, and it is
90 to 98% kernel gate.

**Function fields** (`IWf` on `W`, [[indexed-infinitary-families]]): `Tr :
(n: Nat) -> Type` with `Lf : Tr(0)` and `n` constructors `Brᵢ(n: Nat, k: (y:
Nat) -> Tr(n)) : Tr(Succ(n))`, a `size` through `k(0)`, a closed and an open
`refl`. `heather check --timings`, release, width one:

| ctors | `size` total / gate | queries | closed `refl` | open `refl` |
|---|---|---|---|---|
| 4 | — | — | — | — (0.28 s whole file) |
| 8 | 509 / 498 ms | 664,979 | 215 ms | 99 ms |
| 16 | 5,556 / 5,515 ms | 7,158,355 | 715 ms | 811 ms |

×11 from 8 to 16 constructors (queries ×10.8), about the cube. **Control:**
the same family with `k: Tr(n)` (no function field) at 16 constructors is
84 ms for `size` and 10 to 19 ms per `refl`, so it is the `W` route, ×60.

**Typed syntax**: `Tm(J(Γ, A))` — variables, weakening, λ, application and
`n − 4` binary operators, indexed by a declared judgment type (one index per
family today, `docs/inductive-indexed-lowering.md` §8.4), `size` at the
rebound judgment, an open and a closed `refl`:

| ctors | `size` total / gate | queries | open `refl` | closed `refl` |
|---|---|---|---|---|
| 5 | 247 / 225 ms | 229,378 | 361 ms | 250 ms |
| 12 | 4,135 / 3,932 ms | 4,105,404 | 2,396 ms | 1,483 ms |

The constant is the striking part: a one-step `refl` of a three-node closed
term costs a quarter of a second at five constructors and a second and a
half at twelve, so a theorem file over a real object language pays seconds
per lemma statement.

Not attributed. The two share a shape — an `IWf` whose `ok`/index
predicates and motives are re-walked by conversion per constructor — and
[[elab-whnf-family-transport-cost]] is the last round that moved this layer.

Acceptance: both families' slopes fall towards 1, re-recorded from below,
and the per-`refl` constant at twelve constructors drops by an order of
magnitude.

## What it assumes from elsewhere

- **[[indexed-infinitary-families]]** owns the `IWf`-on-`W` encoding. Assumed
  here: only that a function child is checked through `ok`.
- **[[indexed-families]]** owns the routes and the one-index limit (§8.4).
  Assumed here: only that `Tm` takes the `IWf` route, which the bench fixture
  asserts.

## Log

- 2026-10-26: Attributed and mostly fixed, three kernel changes, no
  elaborator change. Stack samples and a per-variant count of the checker's
  inferences showed the gate re-judging the same few hundred nodes about a
  thousand times each: the inner nodes of the shape's case trees (`n`, `o`,
  `c`, and on `W` the `ok`/code trees), reached inside motives that every
  level of a convoy case tree re-checks, each time under a Γ that differs
  only in entries those nodes never read. At sixteen function-field
  constructors the literal `0` alone was inferred 6.3M times.
  1. **Strengthened typing-memo scopes** (`typing.rs` §The typing memo): a
     tail-free node that reads only Γ's innermost `k ≤ 8` entries, whose types
     stay inside them, is keyed by those entries instead of by Γ.
  2. **Closure identity across spine lengths** (`conv/dom/values.rs`
     `env_identity`): two closures over one body agree when the captures the
     body reads agree, whatever the spines' lengths past them (a body with a
     substitution tail still needs equal lengths).
  3. **`elim_IWf`'s ih as a value** (`Val::IWfIh`, `eval.rs`), as `elim_Wf`'s
     and `elim_W`'s already were: the recursive call is the eliminator
     re-indexed at the child, sharing its step, so conversion compares a
     recursive call's step with the function's own by identity instead of
     normalizing the whole case tree.

  `heather check --timings`, release, width one, cloud box, before → after:

  | family | item | before | after |
  |---|---|---|---|
  | function fields, 16 | `size` | 7,074 ms | 48 ms |
  | | closed / open `refl` | 920 / 731 ms | 26 / 50 ms |
  | typed syntax, 12 | `size` | 6,111 ms | 947 ms |
  | | open / closed `refl` | 3,345 / 1,886 ms | 448 / 490 ms |

  Bench slopes re-recorded from below: `inductive/typed-syntax` 1.78 → 1.13,
  `inductive/function-fields` 1.67 → 0.88 (fixed cost dominates that range).
  The function-field family meets the acceptance; typed syntax does not yet:
  its `refl`s fell 7× and 4×, not 10×. **What is left**, measured: about half
  of every typed-syntax item is `iwf_sig_wf`, the family signature checked
  again at each `IWf(…)` it meets (26 checks for `size` at twelve, ~19 ms
  each). Its index terms name declared constructors (`J`, `Ext`), and a
  global reference carries its context's length in its substitution tail,
  so (a) the strengthened scope cannot apply to them and (b) every shift
  copies them, the shape [[open-payload-shift-copies]] parks behind a
  representation change. An elaborator-side alternative that needs no
  representation change is to emit `n`, `o`, `c` as generated definitions,
  so a signature is three global references; not attempted here. Left open
  for that.
- 2026-10-27: The elaborator-side alternative, done, and closed
  (`docs/iwf-named-signature-design.md`, with
  [[mutual-group-recursion-gate-cost]]): `n`, `o`, `c` are generated
  definitions, an instance is three references, and a `match`'s ih type a
  fourth. For typed syntax it first had no effect: registration, which runs
  after the index type's code was pushed, built index values from the
  attempt's shared constructor annotations, keyed without the Ψ scope, so
  they named every global one too close and the kernel refused `Tm#iout`;
  the family stayed inline without a word. Those caches are now keyed by
  `lowering_scope` too, with a unit test whose control fails without it.
  Release, width one, cloud box, total ms:

  | typed syntax | master | now |
  |---|---|---|
  | 12 ctors: `size` | 246 | 11 |
  | open / closed `refl` | 228 / 231 | 14 / 11 |
  | whole file | 721 | 87 |
  | 32 ctors: `size` | 1,981 | 24 |
  | whole file | 3,537 | 115 |

  The `refl`s fell about 20× at twelve constructors and stay flat with
  size; `Tm`'s declaration now pays for its definitions (2 → 34 ms at
  twelve, linear). `inductive/typed-syntax` re-recorded from below at 0.58
  (the declaration's fixed cost dominating 5..8, each size ~16× cheaper).
  Both families meet the acceptance.
