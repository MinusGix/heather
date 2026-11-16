# Lazy global offset in the value machine

Status: design for the round on `issues/refl-theorem-step-cost.md`. Numbers
live in that issue, not here.

## 1. The defect

`Defs::body` (`crates/kernel/src/reduce.rs`) hands the evaluator a
definition's body **rescoped into the ambient Ψ** with `shift_global(v + 1)`,
memoized in a `BodyCache` that `typing::check_term` creates per gate call.
Every gate call therefore re-copies every definition it unfolds, and a closed
refl theorem over the certified parser unfolds the parser. The rescoping is a
whole-term copy: it allocates a new `Term`/`Type` graph, and its cost is
invisible to fuel, to `steps` and to `queries`, because no rule counts it.

A cross-item cache cannot help: the shift amount `v + 1` is the *distance*
from the occurrence's Ψ to the definition's own prefix, so the same binding
needs a different copy in every later Ψ.

## 2. The change, in one sentence

A syntactic closure carries a **global-index offset** and the machine
evaluates the *unshifted* body under it: `shift_global` becomes a pending
number instead of a copy, materialized only where syntax leaves the value
path.

Adequacy is one equation, and it is the only thing to believe:

> **(A)** `eval(shift_global(k, t), ρ) = eval(t, ρ @ k)` for every `t`, `ρ`
> whose free globals all sit at global depth 0 in `t`.

The side condition in (A) is not a caveat, it is the invariant that makes the
site list finite — see §4.

## 3. Where the offset lives: `Env`, not `TmClo`

The offset is a field of [`value::Env`], the closure's captured local
environment, rather than a fourth field of `TmClo::Syn`/`TyClo::Syn`:

```rust
pub struct Env<'v> { node: Option<&'v EnvNode<'v>>, len: u32, gshift: u32 }
```

`gshift` is *the amount to add to a free global index of any syntax paired
with this handle to name the same binding in the ambient Ψ*. Three
consequences, all of them the reason for the choice:

- Every `eval_tm(t, &env)` and every `TmClo::syn(env, body)` in the kernel
  already pairs syntax with the environment it is read in, so the offset
  propagates with no new parameter threading and no site can silently forget
  it; destructuring `Syn { env, body }` keeps the pair together by
  construction.
- `Env` is 16 bytes on 64-bit either way (the `u32` lands in existing
  padding), so closures stay four words and the domain pays nothing.
- `Env::ident` and `Env::ptr_eq` are the sole identity of a syntactic
  closure, so adding `gshift` to both gives trap 1 (closure identity must
  include the offset) for free, everywhere at once: `CloId`, the conversion
  verdict memo, the transducer cache, and the `ptr_eq`-plus-body reflexivity
  shortcuts in `conv/dom/values.rs`.

Environment *entries* are closures with environments of their own, so each
carries its own offset; `Env::push` never touches `gshift`.
`Env::with_gshift(k)` is a handle copy that reuses the same entry chain —
correct because `gshift` governs only the syntax paired with the handle, and
never the entries.

## 4. The invariant: the offset is always at cutoff 0

`ShiftGlobal` (`subst.rs`) is cutoff-sensitive: `v.0 < at.global` is left
alone. A pending offset carries no cutoff, so the design forbids the case:

> **(I)** A closure whose body sits **under a global binder** is built with
> its offset already materialized, and therefore has `gshift == 0`.

The global binders of the syntax are `CtxPi.body`, `TyPi.body`,
`CtxLam.body`, `TyLam.body`, `LetBoxTy.body`, `LetBoxTm.body` (each `+1`),
and the motive/branch telescopes (`+1 … +7`). The evaluator only ever reads
syntax at the root of a closure body, so with (I) every `GlobalTm`/`GlobalTy`
/`CtxBase::Var`/`SubstTail` it meets is at global depth 0 and `var + gshift`
is unconditionally right — which is exactly (A)'s side condition, discharged
structurally rather than checked.

Materializing under a binder is `shift_global_above(k, 1)` (the six body
positions); materializing at the root is `shift_global(k)`.

## 5. Site list (from `impl Mapper for ShiftGlobal`, `subst.rs` ~996)

`ShiftGlobal` changes exactly four things: `global_ty`, `global_tm`,
`ctx_base`, `tail`. Every place the machine turns syntax containing one of
them into a value or a lookup is a site.

### Lazy — the hot path, no copy

| site (`eval.rs`) | treatment |
| --- | --- |
| `Term::GlobalTm { var, subst }` | `Head::Global { var: var + k }`; the δ-body lookup uses the ambient index |
| `Type::GlobalTy { var, subst }` | `VNeTy::Global { var: var + k }` |
| `eval_subst`'s `SubstTail::Wk { ctx_var }` | `VTail::Wk(ctx_var + k)` |
| `eval_subst`'s `SubstTail::Empty` | unchanged: `VTail::Empty` takes the **ambient** base (`Eval::base`), which is not read off the syntax |
| every `tclo`/`yclo` sub-structure | inherits `k` through `Env` |
| `Elim::ElimW`/`ElimWf`'s captured `env` | keeps `k`: its templates are built from those closures' own bodies |

`Eval::global_tm` asks `Defs::body_unshifted` (new, beside `Defs::body`) for
the body as it is stored, and builds its glued unfolding as a closure over
`Env::at(v_ambient + 1)` extended with δ's payload **values**. The δ payload
entries are `TmClo::Val`, so they carry no scope of their own to confuse.

### Eager at the root — `shift_global(k)`, once, where syntax leaves the value path

`Val::BoxTy`/`BoxTm` (trap 2: boxes carry raw syntax with no environment and
compare syntactically — a box must be ambient or layer c breaks), the `ctx`
of `TyLam`/`TyPi`/`CodeTy`/`CodeTm`/`CtxApp`/`LetBox*`/`ElimCode*`, the `ty`
annotations of `CodeTm`/`LetBoxTm`/`ElimCodeTm`, `TyApp.arg`, and the
`Motives`/`Branches` tables of `ElimCodeTy`/`ElimCodeTm`. `whnf_ty_syntax`
(the rewriter, by design) therefore receives ambient syntax, as it does
today.

### Eager under the binder — `shift_global_above(k, 1)`

The six body positions of (I). Each is built as
`TmClo::syn(env.with_gshift(0), shifted_body)`, so **consumers need no
change at all**: `letbox`'s β still reads `body.as_syn()` and
`apply_global`s an ambient payload into ambient syntax, and
`fire_code_ty`/`fire_code_tm` still evaluate the fired branch under the
elimination's captured `env` — which for `ElimCode*` is stored as
`env.with_gshift(0)`, because its `ctx`, tables and annotation were
materialized.

This is the point where trap 2 is bigger than "boxes are small": eager boxes
and a lazy body would meet inside `letbox`'s β, substituting ambient code
into an unshifted body. Materializing the six binder bodies is what keeps
the two eager things on the same side of every β.

### Cost of the eager sites

They are layer-c/metaprogram syntax — `box`, `letbox`, the code recursors,
context and type abstraction. The rescoping there moves from *once per
definition per gate call, over the whole body* to *once per occurrence
reached, over that occurrence's payload*. A hot loop over a definition that
carries a `box` therefore pays per iteration what it used to pay once, so
the `shift_global_nodes` counter is the acceptance test and not an
assumption: the whole-module figure must fall to the rewriter's remainder.
If a workload is found where the per-occurrence eager sites dominate, the
memo is a `(ptr, k)`-keyed table in the query arena — deliberately not built
now.

### `value::shift` (conversion's telescope weakening)

`shift::tm_clo`/`ty_clo` on a `Syn` closure stop copying the body: a
weakening by `g` becomes `gshift += g` (uniform cutoff-0 shifts compose, and
the environment entries are still rebuilt, each with `+g` of their own).
`reenv_tm`/`reenv_ty` — which weaken only the captured environment because
the body is *already* written in the extended scope — keep the closure's own
`gshift`, which by (I) is 0 there; a `debug_assert` records that.

## 6. What stays eager, and why

The **rewriter** path is untouched: `step_term_delta`'s δ (`reduce.rs:391`),
typing's cold `whnf`, and `Eval::whnf_ty_syntax`. `reduce.rs` substitutes and
re-reduces; it has no closure to hang an offset on, and Δ stays syntactic by
design (`docs/kernel/nbe-conversion-design.md` §3.4). `Defs::body` stays for them,
with the new `Defs::body_unshifted` beside it for the machine. The
`BodyCache` stays, and now serves only the rewriter.

`docs/kernel/nbe-conversion-design.md` §3.1's decision — locals go through the
environment, universe levels and globals stay syntax — is **not** reversed:
globals remain syntactic and de Bruijn-indexed. What the closure gains is an
offset, not a global environment. §7's "no readback" is untouched; `rbemit`
reads closures through `as_syn` plus `eval_tm`, so it inherits the offset.

## 7. Adequacy and where it is recorded

(A) of §2, proved by the `ShiftGlobal` mapper's own shape: it is the identity
on every node except the four hooks of §5, and at each of those the machine
now adds `k` to the same index the mapper would have added it to, at the same
cutoff by (I). `docs/kernel/ch05-06-lemma-audit.md`'s machine-adequacy row gains one
sentence pointing at (A); it is a refinement of that row's obligation, not a
new one, so no new row.

## 8. Tests

- The existing differential oracle (`crates/kernel/tests/eval_differential.rs`,
  eval against the rewriter) is the main net: the rewriter still shifts
  eagerly, so every disagreement in (A) is a failure.
- A new oracle fixture whose definitions reference *other* definitions at
  several Ψ depths, including through a `box`, a `letbox` and a context
  abstraction — so that an offset applied at the wrong site resolves to the
  wrong binding and is detectably ill-typed rather than accidentally
  well-typed (trap 3).
- The whole-library acceptance tests and the native x86 certificate gates:
  the largest bodies of real Ψ-depth the repo has.
- `debug_assert`s: `gshift == 0` in `reenv_*`.

## 9. Acceptance

`shift_global_nodes` on the showcase's root module falls to the rewriter's
remainder; the conversion verdicts and their accounting — `misses`,
`queries`, δ-steps — are **unchanged to the unit** on every item; the full
`scripts/test` and `scripts/bench --check` green; no new kernel dependency,
no `unsafe`.

`eval_steps` is the one count that moved, and only on the closed refl
theorem family (`+1,188` on each, ~13%, against a 95% fall in their time),
alongside `global_ref_rescopes` (+17%): conversion runs the `u^δ`-vs-`u^δ`
rule some tens of times more inside the same misses. The cause is located
rather than guessed — reverting the single site that makes an offset nonzero
(`Eval::global_tm` back to the copied body, leaving every other site of §5
in place and inert) restores **every** counter to the unit, so the delta is
a property of reading the stored body graph, not of a materialization site.
Reading it shares syntax the copy did not, and the identity-sensitive
shortcuts of the comparison therefore take a different — cheaper — route
through the same verdicts. Numbers in `issues/refl-theorem-step-cost.md`.
