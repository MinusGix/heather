# Annotation-component respelling — design

Deliberate perf round on `issues/wf-field-conversion-cost.md`, 2026-08-13. The
predecessor (`docs/family-type-code-defs-design.md` §10, the 2026-08-12
extension) landed `GenDef::TyCode` and collapsed every *whole-type* occurrence
of `⟦D⟧` in the two `match` lowerings to `El (D#tycode^δ)`. The issue stayed
open on a measured residual, and its attribution — not its opening suspects,
all three closed — is this round's charter:

1. **per-application `dom`/`cod` annotations**: every `Term::App` carries the
   callee's declared parameter and result types verbatim, so a call to
   `cert_chain(ir: Ir, ih: Ihp) -> Cert` writes `⟦Ir⟧` (1,712 nodes) and
   `⟦Cert⟧` (which carries three copies of `⟦Ir⟧` by law 2) into the term,
   per call, and a partially-applied spine carries the whole remaining `Π`
   chain at each step;
2. **field-binder projection chains**: `Elaborator::projection`'s `Fst`/`Snd`
   chain annotates every step with the Σ components of `⟦cᵢ⟧`, and those
   components *contain the field types* — `⟦Ir⟧`, `⟦Pre⟧` — verbatim; a
   `match` arm's payload binder aliases to such a chain, so every *use* of
   the binder replays it.

The spine (38 k of 21 M) and the `Supf`/`ElimWf` shape slots (1.3 k) are
measured negligible and are not touched (`issues/wf-shape-annotation-slots.md`
keeps the shape slots).

## 1. The observation that picks the design

Both residual families are made of types that are **already nameable**. An
`App`'s `dom` is very often *exactly* some declaration's registered lowering;
a projection chain's components are Σ shells of size O(fields) whose mass is
the embedded *field types*, and a field type is again some declaration's
registered lowering. Nothing in the residual needs a new kind of code — it
needs the existing `TyCode` reference written into two more families of
annotation slots, including **inside** compound annotations (a `Π` chain, a
Σ tail) whose top node is not itself a declared type.

So the round's mechanism is one function:

```text
respell_ty_deep(cx, ty, depth) — rebuild `ty` with every sub-type that IS a
registered declaration's lowering replaced by El (D#tycode^δ), guarded per
node by the same structural comparison ty_type_ref has always made; None if
nothing changed.
```

Top-down: at each node first try the whole-node respell (`respell_ty`, whose
guard compares against the registry's inline copy and can only *decline*,
§10.4 of the family-code design); on decline, recurse into the node's type
components (`Pi` dom/cod, `Sigma` fst/snd, `Sum` lhs/rhs, `Vec` elem, `Wf`
shape, `Id`/`SEq` ty). `depth` tracks binders crossed (`Pi` cod, `Sigma` snd
bind one each), and a hit at depth `d` is the reference shifted by `d` — the
same `shift_local` the motive respell already uses, sound because a type that
compares equal to the registry's *closed* copy is itself closed. Terms inside
types (`Id` endpoints, `Vec` length, `El` codes) are not walked: annotations
live in type slots, and a term walk would be new surface for no measured mass.

Idempotence is inherited from `respell_ty`: an already-`El`-headed reference
declines at the top and has no components to recurse into.

## 2. The three site families

The line held throughout is §3.1's, unchanged: **structural reads keep the
inline type; only emitted annotations take the reference.**

### 2.1 Statements (the "statement-side respelling" lever, taken)

`elab_decl_inner`'s closing loop (`lib.rs`, "Close over the telescope") builds
the declaration's statement `Π(x₁:A₁)…. R` and the body's outer `λ`s from the
same `param_info`. Both copies of each `Aᵢ`, and the result `R`, are respelled
there — after the body is elaborated (so every structural read during
elaboration saw inline types, zero behavior change inside the declaration) and
before `apply_global` (so the reference's `goal_base` padding is renumbered
exactly as every body-internal reference already is). Binder `i`'s type sits
under `i` binders and the result under all `n`, which is the `depth` argument;
references are minted against the empty context, matching the `LocalCtx::nil`
the statement is checked and pushed in.

This is the high-leverage half, because it **cascades**: once a callee's Ψ
statement spells its `Π` components as references, *every* later application
of it — in bodies, in theorem statements, in other statements — reads its
`dom`/`cod` annotations off that statement and emits them small, with no
per-`App` work at all. `apply_explicit`/`apply_implicit` are not touched; the
annotations they copy have already shrunk at the source. Within-file
declaration order does the rest (a callee is declared before its callers).

Two consequences, both acceptable and both recorded:

- an *argument* is now sometimes checked against `El (D#tycode^δ)` rather
  than the inline `Wf`. That is not a new situation: a type that arrives as a
  code is `docs/types-as-expressions.md`'s shipped path, every consumer whnfs
  first (`build_ctor`, `elab_match`, `tag_of` through `decoded`), and the
  elaborate phase is 1–6% of a file's cost against the gate's 94–99%;
- `unify_ty` learns nothing through an `El` head — and can lose nothing here,
  because a component respells only if it *is* a closed, unparameterized
  declaration's lowering, which mentions no metavariable and no parameter.

`meta fn` statements (`quote.rs`) are deliberately not in scope: their cost
story is the Layer::Meta gate (`issues/certgen-harness-cost.md`), their
domains are `Ctx`/code types the registry never names, and `gen_ref`'s
meta-numbering is only exercised *inside* meta bodies today.

### 2.2 Projection chains

`Elaborator::projection` (`inductive.rs`): the emitted `Fst`/`Snd` steps take
`respell_ty_deep` on their `fst_ty`/`snd_ty` (`snd` at depth 1 — the Σ
binder). The loop's own working copy (`cur`) and the *returned* field type
stay inline: the return value becomes a `match` binder's alias type, which
§10.3's table already pins as a structural-read position. Every caller —
tier-1 `wf_branch` payload binders, tier-0 `case_tree` arms, `read_ctor`,
`ConstBody::Field`/`Arity` — inherits the small annotations through the one
helper.

### 2.3 Constructor field tuples

`build_fields_skel` (`inductive.rs`): the emitted `Pair`'s `fst_ty`/`snd_ty`
(again `snd` at depth 1) — the same Σ components at the value-construction
side that `projection` copies at the elimination side. A constructor *value*
of an `Ir`-field declaration currently carries `⟦Ir⟧` in its label tuple's
annotations; a `refl` pin between two such values pays it twice. The checking
of each field argument (`elab_check` against `fst`) keeps the inline
component, per the line.

`inject`'s `Inl`/`Inr` lhs/rhs (the sum spine at constructor values and case
trees) are **left alone**: the draft measures them at 38 k nodes of 21 M, and
the charter says not to chase them. If this round's counters show them
dominating what remains, that is the successor's first line, not a rider.

## 3. Rejected shapes, with reasons

- **A projection-chain code (`GenDef` per constructor component / sum tail),
  the issue's second filed lever.** It would name the O(fields) Σ shell and
  the sum tails that no whole-type code can name — but the measured mass of
  the chains is the embedded *field types*, which the existing `TyCode`s
  already name; the shells themselves are small. A new code family costs a
  registration boundary, a look-alike-negative surface, and a recognizer
  story per key kind, to collapse nodes the deep respell already collapses
  minus an O(fields) remainder. Filed as the fallback if measurement had
  said otherwise; it did not (§5).
- **Respelling inside `lower_instance` itself** (making `⟦D⟧`'s field types
  references at the source). Largest possible win on paper — it would shrink
  law 2's 3·|⟦T⟧| in the structural copy too — and rejected outright: the
  inline lowering is the *identity* every structural reader and both
  recognizer fingerprints anchor on, and `ty_type_ref`'s guard compares
  against it, so a registry whose copies were themselves respelled would turn
  every guard comparison into a spelling-sensitive one. That is the credulous
  read the fingerprint rounds exist to prevent.
- **Per-`App` respelling at the three `Term::App` emission sites.** Correct
  and local, but strictly dominated by the statement-side respell: it pays a
  guarded comparison per application forever, shrinks nothing in Ψ, and
  misses the `Π`-chain `cod`s that the statement respell gets for free.
- **Walking terms inside types** (respelling `App` annotations embedded in an
  `Id` endpoint of a *statement*). The cascade makes it moot for everything
  elaborated after this round lands — those `App`s are born small — and a
  term walk would touch every `Term` variant for no measured residual mass.

## 4. Correctness argument, and the test plan

The reference and the inline type are convertible by construction (the code
is `code_of` of the registry's copy; `ty_type_ref` declines anything else),
so every change is a spelling choice in an annotation slot the kernel checks
by conversion — the same conservativity argument as §1.3 of the family-code
design, now applied at component granularity. The guard's look-alike
negatives (`wf.rs mod tycode`) already pin the dangerous direction (a type
`tag_of` routes to `D` that is not `⟦D⟧`; `El` of the wrong code; a
byte-identical user global), and `respell_ty_deep` adds no new resolution
path — it calls the same guarded `respell_ty` per node.

New tests (`wf.rs mod tycode`, extending the existing module), on
`docs/testing-generated-terms.md`'s axes:

- the deep respell itself: a compound type (`Π` over two coded declarations,
  a Σ chain with a coded component under the binder) respells its components
  and *only* them, at the right depths — checked structurally;
- a statement really is respelled: a declared `fn f(t: T) -> T`'s Ψ statement
  carries `El (T#tycode^δ)` in its `Π` dom, and a *call* to it emits an `App`
  whose `dom` is the reference (the cascade, pinned rather than assumed);
- the four axes crossed with the new spellings: literal and neutral
  scrutinees through calls and field projections, an **open** element type
  (the parameterized `Box<A>` respells nothing and still elaborates beside
  coded declarations — coexistence), **checking** positions (a constructor
  literal checked against a respelled `dom`; a `refl` pinning a computation
  through respelled projections), and the negative control (a false equation
  through the respelled paths is still refused);
- depth: a projection chain under a `match` binder used in a *proof* (the
  shift-sensitive case — axis 2's reason).

## 5. Measurement

Per the issue's protocol: release build, wall best-of-3 under the CLAUDE.md
ulimits, exact node counts from a throwaway counter at the two kernel-gate
sites (reverted before final verification), A/B via a temporary env
kill-switch on `respell_ty_deep` (also removed before final). Workloads: the
`ir_v1` declarations prefix, prefix + landed `certgen_cert`, prefix + the
`Ir`-field draft (the issue's reproducer), prefix + `certgen_code`, and the
whole `lib/` trio as the suite sees it. Numbers live in the issue log only;
this document keeps shape claims.

Success criteria, from the charter: a measured reduction on the draft
reproducer and on `lib/certgen_code.hthr`'s program-layer helpers, and — as
evidence for the deferred certgen constructor-fields feature — a re-run of
the non-Nat design §2.2 cost shape showing the with-fields configuration no
longer threatens the harness rail.

---

## 6. Landed (2026-08-13), and the two findings the counters forced

Everything in §1–§4 shipped as designed, plus one extension the per-site
counters demanded and two findings that were not in the charter. Numbers are
in `issues/wf-field-conversion-cost.md`'s log, per policy; the shapes:

1. **A fourth site family: `inject` at constructor values** (§2.3's last
   paragraph, revised). The charter's "spine is negligible" was measured on
   a *match body*; on **values** — every constructor value written in a
   theorem statement or an arm — the `Inl`/`Inr` annotations carry the sum
   tails, each embedding every remaining field type, per injection step per
   value. `build_ctor` now injects over an emission copy of the spine
   (`respell_spine`), components deep-respelled; the structural spine
   (checking, container projection) is untouched. The match lowerings' own
   spine uses stay inline, still per the charter.

2. **Two-thirds of what then remained was `Level` trees, not types.** The
   lowering's level joins (`lower_shape`/`lower_ctor`) accumulated raw
   `Max` trees that compound quadratically across the Σ/Sum spine and are
   copied into every level slot; a single nullary constructor value carried
   a level-tree multiple of the whole type's size. Fixed at the two joins
   with `normalize().canonical()` — `equiv`-preserving by construction, so
   again a spelling change. This was worth roughly as much wall time on
   `lib/certgen_code.hthr` as the respell itself. (The closed
   `issues/level-normalization-allocation.md` was about comparison-time
   allocation; this is emission-side size — a different defect at the same
   type.)

3. **A latent kernel conversion gap, found by the statement respell and
   fixed in the kernel** (`conv.rs`, `tm_w`): term conversion never
   δ-unfolded its *type*, so two canonical values at `El (u^δ)` for a
   defined `u` fell into the neutral-type arm and compared `NotConvertible`
   — even two identical literals. Unreachable while defined codes never
   stood in the type slot of an `Id` (typing whnfs types before comparing;
   the elaborator's speculative auto-`refl` passes the `Id` component raw),
   and surfaced as every `{}` hole over a coded declaration's result type
   going unsolved (`lib/list_algos.hthr`). The fix is the mirror of
   `ty_w`'s existing δ stage, gated by the same `has_defs` and layer rules;
   pinned kernel-side (`crates/kernel/tests/definitions.rs`,
   `canonical_values_compare_at_a_defined_el_type`) and end-to-end
   (`wf.rs mod tycode`,
   `an_auto_refl_hole_solves_at_a_respelled_result_type`).

4. **The reflection boundary needs the inverse spelling** — found by the
   full suite, not the workloads. A `meta` analyzer reads a fn's statement
   *as code*, and at layer m a boxed global reference is syntax by design —
   so the respelled statement made every enumeration-result fn opaque to the
   certgen signature checker (an in-language decline) and to the Rust
   agreement peel (a "fragment drift" panic). The opaque-globals round's own
   doctrine names the fix: unfolding-for-analysis happens **at the
   reflection boundary**. `Elaborator::unspell_ty_deep` (the exact inverse
   walk, replacing `El (D#tycode^δ)` with the registry's inline copy) now
   runs in `fn_type_code` and in `certgen.rs`'s `sig_peel`, so the analyzer
   sees the very type it analyzed before the respell existed. One subtlety
   worth the comment it got: the two sites resolve references against
   *different worlds* (`fn_type_code` rescopes to the current Ψ; `sig_peel`
   reads the raw prefix-scoped statement), so the resolver takes the anchor
   length explicitly rather than guessing — the padded `gen_def_of`
   arithmetic is wrong at both.

What remains open on the issue after this round, re-attributed by wall time
rather than node count: the `Supf`/`ElimWf` **shape/arity slots at values**
(one whole shape and one arity per constructor value — dominant in
value-heavy statements now that everything nameable is a reference), which
is [[wf-shape-annotation-slots]]'s fix shape at a site that issue should now
record; and conversion's own cost on large values, which no spelling change
reaches.
