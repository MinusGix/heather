# Tier-0 (non-`Nat`) parameters for the certifying generator

> **Status, 2026-08-14: LANDED**, same round as the design. A file of its own
> rather than a section of the tier-1 doc because the issue's staging names it
> as a stage of its own and every previous stage got one document; §1's
> hand-run and §10's checklist are this round's record.

Design for `docs/certifying-generator-design.md` §8 item 2's **last widening
of the parameter position**: a fragment `fn`'s non-recursion parameters may be
**tier-0 enumerations** — unparameterized, unindexed, non-recursive, and (this
round) **payload-free** — consumed via `match` (`Term::Case` at the kernel
level) and passable to callees. This closes the §8 item 2 list except for
parameterized instantiations (`issues/datarepr-separation.md`), leaving
loopification and `prog-extension-lemma` behind it.

The principle inherited from `issues/certifying-generator.md`, protected by
every decision below: **the generator is untrusted.** A wrong arm order, a
mis-slotted scrutinee, an argument spelled at the wrong embedding — each is a
certificate the kernel refuses, never an unsound theorem. Declining is a
supported answer and negative controls are mandatory.

---

## 1. The hand-run, and what it sized

Before any machinery, the target emissions were written **by hand** and
kernel-checked against the *unchanged* `lib/certgen/ir_v1.hthr` — three shapes, green
on the first attempt:

- `pick(f: Flag, a, b) -> Nat { match f { Off => a, On => b } }` — the
  if-shape;
- `gate(f: Flag, n) -> Nat` (a tier-0 match) called by
  `route(f: Flag, n) -> Nat { gate(f, n) }` — the enum parameter **flowing to
  a callee**, the charter's composition item;
- `fnot(f: Flag) -> Flag` — the tier-0 parameter and the tier-0 **result**
  stages composed.

What that establishes:

- **`lib/certgen/ir_v1.hthr` grows nothing** — again. `LetMatch` scrutinizes any slot
  with any arm count; `letmatch_conv`'s `hl` premise
  (`Flag_gen_embed(Off) ≡ VCon(0, VNil)`) and the rebind's goal
  (`gate(Off, n)` ι-reduces at the closed pattern) close by `refl`. The
  tier-1 round needed β-on-open-children; tier-0 arms have **closed**
  patterns, so nothing is even open.
- **The invariant is the tier-1 emitter's shape with the induction deleted**:
  the matched parameter is the theorem's one declared binder, the rest ride
  in the returned function, the surface `match f { Off => λ… }` **infers its
  own dependent motive** (probed and hand-checked), and there are no
  induction hypotheses at all — every arm is a plain kit fold.
- **The depth-fuel model is unchanged**: a tier-0 `LetMatch` costs
  `1 + max(arm, 1)` exactly as the `Nat` one, and both exactness fixtures
  (`eval(2, …) = Out(…)`, `eval(1, …) = OutOfFuel`) held as computed.
- **Composition needs per-slot embeddings and nothing else**: `route`'s
  `letcall_conv` gathers `VCons(Flag_gen_embed(f), VCons(embed_nat(n), VNil))`
  and consumes `gate_gen_conv_in_route(f, n, VNil)` — the callee's invariant
  re-derived in the caller's program, applied in the tier-0 induction-free
  shape, which is exactly `cert_app`'s existing `RecT` spelling.

## 2. Scope

**In.** A fragment fn's parameters may each be `Nat`, the (at most one) tier-1
recursion parameter, or a **tier-0 enumeration**: unparameterized, unindexed,
non-recursive, ≥ 1 constructor, **no constructor fields**. Any number of
tier-0 parameters. A tier-0 parameter may be:

- the scrutinee of the body's one root `match` (one arm per constructor, arms
  ordinary fragment expressions — no self-calls, since a tier-0 type has no
  structural position to recurse on and the surface refuses the recursion
  anyway);
- a **callee argument** — a callee's signature may now contain tier-0
  enumeration parameters (result still `Nat`), and the caller passes its own
  parameter of the same type;
- the returned value, when the result type is the same enumeration;
- unused ballast beside a `Nat` or tier-1 recursion.

**Out, with homes.**

- *Constructor fields on a tier-0 parameter's type* — deferred. The asymmetry
  against the result position (fields allowed) and the tier-1 payloads
  (allowed) is the arm-binder convention: a tier-0 arm reads fields by
  `Fst(Snd^j ·)` over the branch's own binder, a third accessor coordinate
  the marker pass does not mint this round. The machinery it would land on
  (the `RFld` marker, the arm headers, `Parts`) already exists; nothing else
  is missing. Declined at the **rim** (`ParamTy::of`'s field rule) while the
  in-language checker accepts the shape — the established
  checker-accepts/rim-declines split, recorded in §8, because `SEnum(k)`
  deliberately does not record whether a summand carries fields.
- *A constructor **value** passed at a callee's tier-0 slot* (`gate(On, n)`)
  — declined. The chain's positional typing has no slot for a freshly built
  enum temporary that is neither returned nor a `Nat`; §7's per-slot check is
  where it declines cleanly. Passing the caller's *parameter* is the
  composition the charter names, and it is in.
- *Non-`Nat` callee results* — unchanged decline (the marker convention).
- *Parameterized instantiations, tier-1 results, containers* — unchanged,
  with their owners.

## 3. The body shape, and the marking

Probed (2026-08-14): a surface `match` on a tier-0 parameter elaborates to a
right-nested `Term::Case` tree — the root scrutinizes the parameter, each
`case_r` binds the sum rest and the next node scrutinizes it at `Var 0`, each
branch **implicitly binds** its payload (no λ wrapper, unlike the tier-1
recursor's `λ cs'. λ ih'.` skeleton), and a payload-free arm never references
its binder. For `n > 2` the nesting is exactly the tier-1 case tree's; for
`n = 2` it is one node. The `Case` motive is the fn's result type (constant),
bound and never read by the walker.

**The marker pass validates and re-packages, exactly as the tier-1 round's**
(`mark_case_t0`, mirroring `mark_wf_tree` minus the skeleton): the root
scrutinee must be a tier-0 parameter (by de Bruijn identity against the
declaration-derived table `MarkCx::t0`), each nested scrutinee must be the
`case_r` binder, each arm is marked with the branch internals (payload and
sum-rest binders, `skel = ys + 1`) declined as values, wrapped in the
existing arm-header marker at field count 0, and every scrutinee is replaced
by the parameter's marker. What the walker receives is **convention 5's case
tree with no eliminator around it** — no new marker shape exists.

A nested `match` (any kind, either nesting order) declines in `mark` or at
the walker exactly as before; a tier-0 `match` in a value position (`Succ(match …)`)
declines at the walker (a `TArms` is not a value).

## 4. The walker's widening (in-language)

One arm and two helpers; **no new `TA` constructor, no shell edit** — the
52-branch shells are untouched, because `tm_case` and the accessor markers
were landed tag-generically by the tier-1 round:

- `ta_finish` gains a `TArms(lvl, parts)` arm: a bare collected case tree at
  the fn's root is a tier-0 parameter match. `ta_arms_finish` checks the
  dispatch level names a parameter (`lvl < arity`) and `ta_arms_at` renders
  `LetMatch(arity−1−lvl, ⟨arms at their own base depths⟩, Ret(RCons(0, RNil)))`
  through the tier-1 round's own `ta_wf_chain` — the arm-rendering path is
  shared, with every field count 0.

The `Nat` and tier-1 eliminator paths are byte-identical; convention 6 in the
file header records the root-position rule.

## 5. The signature checker's widening (in-language)

`sig_pi` accepts two more domain states — `SPure` (a one-constructor
enumeration) and `SEnum(k)` — routed through the same continuation as `SNat`
(arity + 1, `wf` untouched), so tier-0 parameters compose freely with the one
tier-1 position. `SFlds` as a domain still declines (a fielded one-constructor
payload); a fielded summand *inside* `SEnum(k)` is invisible to the shape walk
by design and declines at the rim (§2). `SigOut` is **unchanged** — no pin
moves — because a tier-0 parameter needs no verdict field: which declaration
each position names is the rim's question, answered per-index by
`ParamTy::of`.

## 6. The certificate fold: ZERO edits, predicted and verified

`lib/certgen/certgen_cert.hthr` is untouched. A tier-0 match is `cert_body_w` with
`kids = 0` — the tier-1 entry point at the all-childless mask, which gives
every arm `IhNo` (so a self-call in any arm declines, the honesty check for
free) and one `CMatch` per constructor. The `CertOut` shape is `CRecW`, the
model's is `RecT`; §8.1 of `docs/certgen-cert-expression-design.md` keeps its
score: four features, one constructor-level edit total.

## 7. The rim: names, rendering, and the model

`crates/elab/src/certgen.rs`:

- **`ParamTy` generalizes to both parameter tiers**: it gains a
  `recursive` flag, and `ParamTy::of` accepts a non-recursive enumeration
  with payload-free constructors (any field declines — §2). `kids_mask` is
  naturally 0; `pattern`/`field_slots`/`literal`/`embed_text` all degenerate
  correctly (bare patterns, no slots, the first constructor as the fixture
  literal, a non-recursive `embed_T` byte-identical to `ResTy`'s for the same
  type — required, because the two share the `embed:{T}` support key).
- **`Emission` carries its `pts`**: a caller re-deriving a callee's invariant
  needs the callee's parameter descriptions (binder types, per-slot
  embeddings), so the re-derivation uses the callee's stored `pts` instead of
  the old all-`Nat` assumption.
- **`MarkCx` gains the tier-0 table** (`level`, constructor count per tier-0
  parameter), built beside the `Wf` table from the unspelled Π spine;
  `sig_peel` (the agreement oracle) accepts `Sum`/`Sigma` domains; and
  `MarkCx::callee` unspells the callee's type and accepts tier-0 domains
  (result still `Nat`), so a tier-0-parameter callee has a marker.
- **The `RecT` emitter's non-recursion binders consult `pts`** (they were
  hard-coded `Nat`, correct while tier-1 was the only non-`Nat` parameter);
  the `Rec` and `Plain` paths already did.
- **`render_cert`'s `Call` arm checks each argument slot against the
  callee's declared parameter type** — a `Nat` slot must carry `embed_nat`,
  a tier-0 slot that type's embedding — which is both the §2 decline for
  constructor-value arguments and a clean decline (instead of a downstream
  kernel refusal) for a mis-typed argument.
- The agreement guard distinguishes the tiers: `wf` still counts only the
  tier-1 position; the recursive-`pts` count (≤ 1) is what it is compared
  against.

Everything else — records (`Compile{T…}{R}` naming was tier-general already),
instances, fixtures, `chain_from_rir`, `fn_ir_from_rir` — needed **nothing**:
the tier-1 round's `RecT` path serves the tier-0 match end to end once
`pts[scrut]` describes the type.

## 8. Declines, and where each lives

| decline | where |
| --- | --- |
| a fielded tier-0 parameter type | rim (`ParamTy::of`; checker accepts the shape — §2, §5) |
| a parameterized instantiation (`TksP<Nat>`) | rim, by name (unchanged split) |
| two tier-1 parameters / tier-1 result | in-language (unchanged) |
| a fielded one-constructor payload as a domain | in-language (`sig_pi` over `SFlds`) |
| a tier-0 `match` not at the body's root | walker (`TArms` is not a value) |
| a nested `match` in a tier-0 arm | `mark` (branch mode declines eliminators) |
| a branch internal (payload / sum rest) used as a value | `mark` |
| a `match` on a non-parameter | walker (`ta_arms_finish`'s level rule) |
| a constructor value / mis-typed slot at a callee argument | renderer (§7's per-slot check; a nullary-vs-`Succ` arity clash declines one step earlier in the chain typing) |
| a self-call in a tier-0 arm | in-language (`cert_body_w` at mask 0), behind the surface's own refusal |
| a tier-0-parameter callee that is *not* generated yet | closure (unchanged) |

## 9. Cost

Not a perf round. Shape: `lib/certgen/certgen_code.hthr` grows two small helpers and
one `ta_finish` arm (no new `TA` constructor, no shell arm — the size law's
expensive coordinates are untouched); the new fixtures live in their own test
binary (`certgen_t0param.rs`) with its own rail, its acceptance-class tests on
the `--fast` skip list (`issues/certgen-harness-cost.md` has the entry).

## 10. Acceptance — run 2026-08-14, all items met

1. ✅ The §1 hand-runs retired into generated form: `pick`, `gate`, `route`
   (two-member program, `gate_gen_conv_in_route` re-derived inside it,
   applied at the caller's own `Flag` parameter), `fnot` — generated,
   elaborated, kernel-checked end to end (`crates/elab/tests/certgen_t0param.rs`).
2. ✅ `sel3` (three constructors — a tag past 1 — a foreign call in an arm),
   `wsum` (a tier-0 parameter riding a `Nat` induction *and* passed to a
   callee from inside it), `tsel` (a tier-0 parameter beside a **tier-1**
   recursion: the tier stages compose, `CompileToksFlagNat`).
3. ✅ The library states its own acceptance: `t0_case_transcribes` (the
   hand-run's `pick` body byte for byte), `t0_case_on_a_nonparameter_declines`,
   `t0_case_in_value_position_declines`; `sig_t0_param`,
   `sig_t0_param_beside_nat`, `sig_t0_params_two`, `sig_t0_beside_tier1`,
   `sig_t0_fielded_payload_domain_declines`. All held on their first
   elaboration.
4. ✅ Byte-stability: every existing emission byte-identical; all `IR_*` pins
   and every mutation control green untouched; `SigOut`, `TA`, `Cert` moved
   **no** pins.
5. ✅ Declines of §8 asserted with their attributions; no signature
   disagreement anywhere. **One fixture flip** recorded at its site:
   `ParamTy::of`'s "non-recursive inductive parameter" decline is gone (that
   shape is the round's positive); the fielded-parameter decline replaces it.
6. ✅ The perturbed-library control mutates `ta_arms_at`'s dispatch slot
   (`LetMatch(j, …)` → `LetMatch(Succ(j), …)`): the mutated `pick` renders as
   a plausible `Nat`-induction emission over the wrong parameter, its
   exactness fixture *passes* (the depth-2 literal happens to agree), and the
   kernel refuses it at the open-argument invariant — the strongest of the
   three refusal sites. The library's own `t0_case_transcribes` refuses the
   mutation first, asserted before the theorems are stripped.
7. ✅ `scripts/test --fast` green in-round; the full suite and
   `scripts/bench --check` are the coordinator's final gate as usual.

## 11. Rejected alternatives

- **A new marker shape for tier-0 arms**: nothing to mark — payload-free arms
  reference only parameters, and the tier-1 round's header/scrutinee-marker
  conventions already carry the arm split. The only new coordinate would be
  field accessors, which are out of scope with fields (§2).
- **A `CertOut` case of its own (`CCase`)**: `CRecW` at mask 0 *is* the
  tier-0 certificate, and a separate constructor would re-state the same fold
  minus the `Ihp` plumbing — a size-law cost for a distinction the renderer
  derives from the declaration (`recursive` on `ParamTy`), exactly as the
  tier-1 round argued for `CIh`'s missing child index.
- **Recording tier-0 positions in `SigOut`**: the rim resolves every
  parameter's declared type by index anyway (`ParamTy::of`), and the tier-1
  position is carried only because *at most one* is a fragment rule the
  library owns. Tier-0 positions have no such rule, so a verdict field would
  duplicate rim knowledge.
- **Supporting `gate(On, n)`** (constructor values at callee slots): needs
  look-ahead typing of temporaries (which callee slot a temporary feeds),
  the first non-positional rule in the renderer — deferred until something
  needs it; the decline is honest and the parameter-passing form covers the
  composition charter.
