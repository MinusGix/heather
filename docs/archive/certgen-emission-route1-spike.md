# Route 1 (Ψ-staging) for in-language certificate emission — verification spike

> **Burned in B2 (2026-10-24).** `ir_v1` and the certifying generator over it were deleted
> (`docs/native/native-program-logic-design.md` §3.2, `issues/ir-v1-retirement.md`); FunctionIR is
> the source IR the verified compiler reads. The document stays for its reasoning. The last
> commit with the code is `82521eab`; a frozen copy of `ir_v1.hthr` is the frontend bench's
> heavy corpus case (`crates/elab/benches/frontend/fixtures/`).

Run 2026-08-12 against `issues/in-language-certificate-emission.md`. The issue
names three verification items for whoever opens route 1; this is those three,
each pinned by a test, plus a fourth the list did not name and which is the
reason the recommendation below is *conditional* rather than a plain go.

Tests: `crates/elab/tests/certgen_route1_spike.rs` (14, all cheap — the whole
binary runs in 0.25 s) and one positive plus one control appended to
`crates/elab/tests/ir_v1.rs::the_full_ir_library_checks`, which already pays
for the library's elaboration (see §3 on why they ride there). Suite 1448 to
1462, the delta being exactly the new binary; nothing else moved.

Line numbers are `crates/kernel/src/typing.rs` unless said otherwise; book
citations are `docs/delam/04_dependent_layered_modal_type_theory.tex` by line.

---

## 0. The one-paragraph answer

**(a) yes, (b) yes, (c) yes — and route 1 as literally worded still does not
close.** All three kernel facts the issue leaned on are real, and two of them
are *already reachable from the surface* with no new machinery at all: a
`meta fn` may take an `Ir` and `match` it today, and it may return a
`Code(· ⊢ …)` whose statement is built from Ψ globals. What does not exist,
and what the item list did not name, is the fold's **recursive step**: proving
`Converges(p, env, LetCon(t, a, rest), vs)` consumes a certificate about
`rest`, and `rest` is a binder of the arm — not a Ψ global. So the recursion's
result type follows the scrutinee, which is a dependent code type, which is
route 3. Staging the *top* `Ir` into Ψ does not reach the sub-`Ir`s.

Route 1 is therefore not dead but **re-shaped**: the fold has to be driven by
something that can mint a Ψ entry per instruction (the elaborator, or the
emitted text itself), with the in-language part supplying the *shape* — which
is exactly the transcriber's own architecture, one phase later. §5 says what
that costs.

---

## 1. Item (a) — elim over a Wf-lowered inductive at `Layer::Meta`: **CONFIRMED**

**Kernel.** The eliminators are layer-generic. `Term::ElimWf`'s rule opens at
line 1435-1436 with `self.not_var_layer(env)?` — not `meta_layer`, and not a
`Layer::Prog` equality — and `not_var_layer` (376-378) refuses exactly one
layer, `Var`. `Term::ElimNat` (932) and every other MLTT form are the same
shape. That is the implementation of ch. 04's "A Note on Layer `v` Rules"
(l. 1616-1624): *only* the local-variable, local-substitution, global-variable
and conversion rules are indexed by layer `v`; every other MLTT rule is
indexed by a generic layer `i`, and layer `m` is "MLTT extended with …"
(Table feat, summarized in `docs/delam/README.md`). Nothing about `Wf`, `Vec`,
`Fin` or the `nth` schema the tier-1 lowering emits is special-cased.

**Pinned three ways**, because a rule read is not a rule run:

- `ir_is_wf_lowered` — the premise. `Ir` copied verbatim from `lib/certgen/ir_v1.hthr`
  really does lower to `Type::Wf`, so this is about `elim_Wf` and not about
  `elim_Sum`. (Three of its constructors carry two recursive fields, which is
  what puts it on the tier-1 route, `docs/inductives/inductive-tier1-wf-lowering.md`.)
- `elim_over_a_wf_lowered_inductive_checks_at_the_meta_layer` — the term the
  elaborator committed for a real structural recursion over that `Ir`
  (**neutral** scrutinee: the parameter; all eight arms using the ih, so the
  full `elim_Wf` route rather than the ih-free `const_elim_wf` shortcut) is
  re-checked with `check_term` at `Layer::Meta` and passes, next to the same
  check at `Layer::Prog`.
- `elim_over_a_wf_lowered_inductive_computes_at_the_meta_layer` — the
  **literal** half of the scrutinee axis (`docs/testing-generated-terms.md`),
  and the half a fold consumes: `Layer::computes` is `Prog | Meta`
  (`layer.rs:29-31`), so ι fires and `conv_term` decides the numeral at both
  layers. With the negative control that says the conversion decided
  something: the same term is *not* convertible with its answer minus one.

**The surprise, and the first correction to the issue.**
`a_meta_body_may_match_a_wf_lowered_ir`: this needs **no new surface**. A
`meta fn` may already take an ordinary program-layer parameter and `match` it
— the analyzer round widened the slice that far
(`docs/archive/certgen-transcriber-in-language-design.md` §9.1 option A, landed) — and
the whole declaration is kernel-checked at `Layer::Meta`, so the test passing
*is* an `elim_Wf` over `Ir` typed at layer m with all eight arms.

## 2. Item (b) — a code type indexed by a just-minted global: **CONFIRMED**

**Kernel.** `Type::CodeTm`'s formation (630-635) is `meta_layer`, then
`ctx_wf(env, Layer::Prog, ctx)`, then
`self.ty_check(&env.in_ctx(ctx.clone(), Layer::Prog), ty, level)`. The
statement is checked at layer p **in the quote's context**. `Term::GlobalTm`
(748-763) enforces only the binding invariant `i' ≤ i` against `env.layer`,
and the elaborator binds a declaration at `Layer::Code`
(`crates/elab/src/lib.rs:1705/1975/1984`), so `Code ≤ Prog`
admits the reference. The box body (657-663) is checked at `Layer::Code`,
where `Code ≤ Code` admits it again — and type conversion for a layer-c term
runs at `typeof(c) = p` (`conv_ty`, 359-360, via `Layer::type_layer`), which
is why a code-layer `refl` can close an equation only δ/ι decides.

**Book.** Ch. 04 l. 1037-1039 is the formation rule:

    Γ ⊢_m ok    Ψ; Δ ⊢_p T @ l    ⊢_L l : Level
    ------------------------------------------- (□-Trm formation)
    Ψ; Γ ⊢_m □(Δ ⊢ T @ l) @ 0

and l. 1077-1081 is the global-variable rule, admitted at *every* layer
(`i ∈ {v, c, p, m}`, `i' ≤ i`). Together: a contextual type's statement may
name Ψ, at any layer. Ch. 04 l. 905-906 says it in prose — "this `T` may refer
to the index type at layer p introduced by meta-functions above".

**Pinned by three positives.** `a_code_type_may_be_indexed_by_a_just_minted_global`
(`Code(g |- seven() = 7)` with `seven` declared in the same file),
`the_statement_may_apply_a_global_to_global_arguments` (a *predicate* global
applied to argument globals — one step from `Converges(prog, env, ir, out)`),
and `the_payload_may_name_the_global_its_statement_mentions` (the box body
naming a global too, not only the type).

**And by two negatives**, so route 3's boundary stays visible:

- `a_code_type_indexed_by_a_meta_local_is_still_refused`. Surface-side the
  refusal is *name resolution* — a `meta fn`'s code type elaborates with no
  locals in scope at all, the same enforcement that makes a `match code`
  motive constant — so the diagnostic is "unbound name `k`", not a layer
  complaint. Worth knowing: the surface never reaches the kernel rule here.
- `the_kernel_refuses_a_local_indexed_code_type_too` — the kernel saying the
  same thing, which is the fact the surface rule is *for*. `Env::in_ctx`
  (288-290) **replaces** the local context rather than extending it, so the
  ambient meta-level Γ is discarded wholesale and a `Var` of it is
  `UnboundLocalVar`, not merely ill-layered. That is the implementation of the
  formation rule above, where Γ appears in the conclusion and *not* in the
  premise for `T` — and it is why `docs/archive/certgen-transcriber-in-language-design.md`
  §5's "unstatable" is a shape fact rather than a spelling problem. Paired
  with its own control: the same statement with the local replaced by a closed
  term is a well-formed code type.

## 3. Item (c) — kit lemmas quotable at their statement types: **CONFIRMED**

A `theorem` is an ordinary Ψ global, so this is item (b) with the global in
the payload's *head* position instead of its type's. The fold never reads a
proof — body reflection's opacity policy
(`docs/metaprogramming/opaque-globals-analysis-design.md`) is about `fn_body_code` and is
simply not what a fold needs — it names the lemma and applies it.

**Against the real kit**, in `crates/elab/tests/ir_v1.rs::the_full_ir_library_checks`:

```heather
fn cert_env() -> Val { VNil }
fn cert_ir()  -> Ir  { Ret(RNil) }
fn cert_out() -> Val { VNil }
meta fn ret_cert(g: Ctx)
    -> Code(g |- Converges(add_prog(), cert_env(), cert_ir(), cert_out()))
{ code { ret_conv(add_prog(), cert_env(), RNil, cert_out(), refl) } }
```

This is the real `Converges` record, the real `ret_conv`, and `gather`'s side
condition discharged by a layer-c `refl`. It elaborates and kernel-checks.

**It rides in that test rather than in a suite of its own, deliberately**, for
that test's own stated reason: the library is **120 CPU-seconds** to elaborate
(measured 2026-08-05; `crates/elab/tests/ir_v1.rs` header), against
`scripts/test`'s 300-second `ulimit -t`, and two full elaborations do not fit
the rail. The addition itself is free — a `meta fn` with no `match code` pays
no 52-branch `rec_ga` gate, and the whole `ir_v1` binary measured 58.7 s wall
/ 60.3 s user with the additions in (2026-08-12, dev with the workspace
overrides), i.e. inside the same envelope the header records. The
**miniature** lives in the spike file for the inner loop:
`a_boxed_payload_may_apply_a_lemma_global_at_its_stated_type` and
`a_boxed_payload_may_compose_two_lemma_globals` — the second is the one that
matters, since a fold is *composition*: one lemma's conclusion feeding
another's hypothesis, at layer c, with both lemmas and both indices
Ψ-resident. That is the certificate shape, one instruction wide.

The real-kit negative rides along too: the same statement with the `Ir` at a
meta-level local is refused.

## 4. Item (d) — the one the list did not name: **the fold's recursive step is blocked**

This is the spike's finding, and it is a *negative*, which the round's brief
calls a fully successful outcome when the cause is precise. The cause:

1. Code types are meta-only (`meta_layer` at 624/630), so anything returning
   code lives at layer m. A program-layer `fn` — the only thing in Heather
   that recurses today — cannot return code, and says so:
   "`Ctx`/`TyCode`/`Code` are meta-layer types". Pinned in
   `a_meta_fn_cannot_call_itself_or_another_meta_fn`.
2. At layer m there is no recursion at all. A `meta fn` is elaborator-held,
   not Ψ-resident (`docs/metaprogramming/in-language-map-design.md` §8), so it is not in scope
   in its own body ("unbound name `m`") and not in another's ("`a` cannot be
   used here"). Same test.
3. Even granting (1) and (2), the fold's result type **varies with the
   scrutinee**. `letcon_conv`'s hypothesis is
   `Converges(p, VCons(VCon(tag, fs), env), rest, vs)`, and `rest` is bound by
   the `LetCon` arm. So the recursion wants `Code(· ⊢ P(ir))` with `ir` a
   local — refused, by §2's two negatives, met one level in. Pinned directly
   as `a_certificate_statement_cannot_follow_the_ir_it_is_about`.

And the good half, which bounds the damage:
`code_may_be_built_by_matching_an_ir_at_a_constant_statement` — a `meta fn`
*may* match an `Ir` and return code, today, provided every arm's code has the
**same** statement. Building code by recursion over a value is not blocked in
itself; only a statement that follows the value is. This is §3's
constant-motive discipline reappearing one level out, and it is the same
sentence §9.1 of the transcriber design already had to learn once.

**So the issue's "fold the ∃-composition kit IN CODE by recursion over the Ir
value" is the half that does not hold.** The rest of route 1's paragraph does.

---

## 5. The corrected remaining-machinery list

The issue names two: "ordinary match/recursion in a meta body
(meta-body-statement-loop territory) and staged elaboration order". Corrected:

| the issue said | actually |
| --- | --- |
| ordinary **match** in a meta body | **already exists.** Landed with the analyzer round; verified here over a Wf-lowered `Ir` at layer m. Nothing to build. |
| ordinary **recursion** in a meta body | **missing, and it is not `meta-body-statement-loop`.** That issue is about annotated `let` in a meta body — a different, smaller gap. The real one is **Ψ-resident meta definitions** (`docs/metaprogramming/in-language-map-design.md` §8, and `docs/archive/certgen-transcriber-in-language-design.md` §11's last-but-one bullet): a `meta fn` cannot name itself or another. `issues/meta-body-statement-loop.md` should not be cited as route 1's prerequisite; the Ψ-resident-meta-defs deferral should. |
| staged elaboration order | **confirmed missing**, and it is the load-bearing one — see below. |
| *(unnamed)* | **the fold's dependent statement** (§4). Not a surface gap; a calculus gap, and it is route 3's. |

`meta-body-statement-loop` is genuinely untouched by route 1 either way: the
transcriber design already recorded that the round did not consume it, and the
fold needs no annotated `let` that a plain `let` (which works) cannot do.

**What staged elaboration order has to mean, given §4.** Not merely "declare
the prog first, then run the builder". If the fold cannot recurse in code,
then every intermediate statement that the fold needs to *state* must be a Ψ
entry — i.e. the staging is **per instruction**, not once per function:

    ir_0 := Ret(RNil)                       -- a definition
    c_0  := ret_conv(p, env_0, RNil, …)      -- a theorem: Converges(p, env_0, ir_0, …)
    ir_1 := LetCon(tag, args, ir_0)
    c_1  := letcon_conv(p, env_1, …, c_0)    -- statement mentions ir_0, ir_1: both globals
    …

Each step's statement mentions only globals, so each step is individually
statable — which is exactly item (b), applied *n* times instead of once. The
recursion has moved from inside code to the thing that mints the globals.
That thing is the elaborator (or the emitted text). This is a real design, it
is a straight generalization of what the Rust emitter does today, and it is
the version of route 1 that the verified facts support.

Its cost, named honestly: one Ψ definition and one Ψ theorem per IR
instruction, where today the whole certificate is one theorem. That is a
question for `issues/certgen-harness-cost.md` and for whoever owns the emitted
file's readability, not a soundness question — every entry is still
individually kernel-checked, which is the charter property route 1 exists to
keep.

## 6. Seams the staged order can reuse

- **Analyzer slots** (`docs/metaprogramming/meta-def-registration-design.md` §11, summarized in
  `docs/archive/certgen-transcriber-in-language-design.md` §6.1). The contract is
  whole-signature convertibility against an expected signature *written in
  Heather* and elaborated in the declaring file's scope, so a
  `certgen.emit_certificate` slot costs one vocabulary entry and one expected
  signature — no new registration kind. The Π order being *fixed* by the slot
  (rather than merely constrained) is what lets the caller build the spine,
  and a staged emitter needs exactly that: the caller supplies the staged
  globals in a canonical order.
- **The evaluation hook** (`docs/archive/certgen-transcriber-in-language-design.md`
  §6, `crates/elab/src/certgen.rs`). All five steps carry over unchanged in
  kind: apply a Π spine, **spine-directed** δ-transparent WHNF (only what is
  inspected is reduced — the memory discipline CLAUDE.md's superlinear warning
  demands), readback with its own `READ_BUDGET`, and `MetaDef::at` rescoping,
  which a staged emitter needs *more* than the transcriber does: it grows Ψ
  between invocations, which is precisely the staleness the rescope fix
  (§6 step 5b) exists for. A staged fold is that hook run in a loop with Ψ
  growing under it, and the one piece that is genuinely new is the readback
  target — a certificate-expression datatype rather than `FnIr`.
- **`Elaborator::fn_body_code` / `fn_type_code`** (the pull reflection API):
  not needed by the fold, which analyzes an `Ir` value rather than code. Named
  here only so a later round does not go looking.

## 7. Recommendation: **conditional go, and not as one round**

Do not schedule "route 1" as written. Schedule its two halves separately,
because the spike showed they have different risk:

1. **Round A — the certificate-expression datatype and its renderer, in
   `lib/`, with the emission still driven from Rust.** Zero new calculus, zero
   new surface: an inductive for "a certificate application chain", ordinary
   `fn`s that fold an `Ir` into one, and a readback. This is the transcriber
   round's shape verbatim, one phase later, and it is where the actual
   difficulty of phase 3 lives (the argument spellings, `env` evolution,
   `gather` side conditions). It banks most of the value — the heuristic
   becomes a library file a test can perturb — and it needs *none* of (a),
   (b), (c). Low risk, and the honest first round.
2. **Round B — staged Ψ emission**, per §5: the elaborator mints a definition
   and a theorem per instruction from round A's data, with the statements
   assembled from the globals it just minted. This is where (b) and (c) are
   consumed, and where the cost question (one Ψ pair per instruction) has to
   be answered against `issues/certgen-harness-cost.md`. Medium risk, and it
   is *optional*: without it the certificate is still emitted as text and
   re-elaborated, exactly as today.

Do **not** schedule an "in-code fold" round. §4 says it needs dependent code
types over meta data, which is route 3, which the issue already resolved to
hold as a customer list riding with the delayed-substitution extension and to
be designed against the external Coq formalization first. Nothing here changes
that verdict; item (d) adds one more name to route 3's customer list, and that
is the right place for it.

**What would change the recommendation.** If route 3 ever lands, the in-code
fold becomes the natural shape and rounds A/B become its front end rather than
its replacement — round A's datatype is what a dependent motive would range
over either way, so neither round is wasted work under either future.
