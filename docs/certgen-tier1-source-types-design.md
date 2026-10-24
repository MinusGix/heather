# Tier-1 source types for the certifying generator

> **Burned in B2 (2026-10-24).** `ir_v1` and the certifying generator over it were deleted
> (`docs/native-program-logic-design.md` §3.2, `issues/ir-v1-retirement.md`); FunctionIR is
> the source IR the verified compiler reads. The document stays for its reasoning. The last
> commit with the code is `82521eab`; a frozen copy of `ir_v1.hthr` is the frontend bench's
> heavy corpus case (`crates/elab/benches/frontend/fixtures/`).

> **Status, 2026-08-14: LANDED**, same round as the design. §10's checklist
> was worked through in order; the verdicts are recorded there. Two §4/§6
> decisions were reversed by the implementation and are recorded in place
> (the arm-header markers replacing the `fcounts` parameter, with §11's
> last entry carrying the reason; the fold's `kids` mask as a `Nat`).

Design for `docs/certifying-generator-design.md` §8 item 2's **final staged
widening**: a fragment `fn` may structurally recurse over a **tier-1**
(recursive, finitary-branching) inductive parameter — the encoding tier
`issues/tier1-branching-constructors.md` settled on the `Wf` former. Round
pattern as usual: this document first, the implementation against §10.

The customer is named by the showcase (`docs/showcase/README.md`, the
derive-`Compile` row): `calc.hthr`'s `eval` recurses over `Expr`, whose
`Plus`/`Times` constructors have **two** recursive fields. The fragment this
round lands covers that shape — recursion over an unparameterized tier-1
inductive with `Nat` payload fields and any number of recursive fields per
constructor, other parameters `Nat`, cross-function calls included — so the
acceptance fixture set contains an `eval`-shaped function end to end.

The principle inherited from `issues/certifying-generator.md`, protected by
every decision below: **the generator is untrusted.** A wrong arm order, a
mis-numbered field, an induction hypothesis routed to the wrong child — each
is a certificate the kernel refuses, never an unsound theorem. Declining is a
supported answer and negative controls are mandatory.

---

## 1. The finding that sizes the round: the proof schema needs NOTHING new

Before any machinery was designed, the target emission was written **by
hand** and kernel-checked against the *unchanged* `lib/certgen/ir_v1.hthr` — the same
method that started the whole generator (the `add` hand-run). Two hand-runs,
both green on the first attempt:

- a linear tier-1 recursion (`Toks { TNil, TCons(n: Nat, rest: Toks) }`,
  `tsum` summing the spine), and
- a branching one with a payload read
  (`Expr2 { Lit2(n: Nat), Plus2(l: Expr2, r: Expr2) }`).

What that establishes, item by item:

- **`lib/certgen/ir_v1.hthr` grows nothing.** `Val` is untyped constructor trees, so
  a recursive `embed_T` is just a *recursive generated `fn`*
  (`VCon(i, ⟨fields, children embedded at `embed_T` itself⟩)`); `LetMatch`
  scrutinizes any tag with any arm count; the ∃-composition kit is
  tag-generic and arm-count-generic already. The non-`Nat` round's "the
  library gains nothing" finding extends verbatim to the recursive case.
- **The `Converges` induction over `T` is the surface's ordinary structural
  `match`,** in exactly `calc.hthr`'s `compile_pushes_eval` style: the
  theorem's one declared parameter is the recursion parameter, the varying
  arguments (other parameters, `tail`) ride in the returned function, the
  motive is inferred, and **the induction hypothesis is an over-applied
  self-call** — `tsum_gen_conv(gf1, VNil)` — not a bound `gih`. No explicit
  motive text is needed at all, which makes the tier-1 invariant *simpler*
  to emit than the `Nat` one.
- **The conversion facts all close by the tier-1 β-on-open-children
  property** — the very thing route C of the branching-inductives decision
  bought. `Toks_gen_embed(TCons(gf0, gf1))` reduces at *open* `gf0`/`gf1`,
  so `letmatch_conv`'s `lookup` premise is `refl`; and
  `tsum(TCons(gf0, gf1)) ≡ Succ(tsum(gf1))` definitionally, so the rebind's
  goal closes. The generator's schema is a direct consumer of the `Wf`
  former's design property.
- **Per-arm shape**: one `letmatch_conv` per constructor arm (`ctag` = the
  declaration index), `fields` = the constructor's fields embedded in
  declaration order (`embed_nat` for payloads, `embed_T` for children), the
  arm's chain folded from the same kit, each self-call's `hc` the ih at that
  child. Multiple children per arm need nothing beyond one `letcall_conv`
  per self-call — the multiplicity lives in the *spelling* of each `hc`
  (`f_gen_conv(gf0, VNil)` vs `f_gen_conv(gf1, VNil)`), which the renderer
  derives from the gathered slot as it derives every other spec.

## 2. Scope

**In.** A fragment fn may take **one** parameter whose type is a tier-1
inductive `T`:

- unparameterized, unindexed, recursive (`Inductive::recursive`), lowered by
  the `Wf` scheme (`docs/inductive-tier1-wf-lowering.md`);
- every constructor field either `Nat` (payload) or `T` itself (a recursive
  child), interleaved freely in declaration order;
- at least one constructor with no recursive field (otherwise the fixture
  literal cannot be built; such a type is uninhabited anyway).

The other parameters stay `Nat`; the result stays `Nat` or a tier-0
enumeration (the previous stages' rule, untouched); structural recursion, if
any, must be on the tier-1 parameter (a `Nat`-recursive body beside an unused
tier-1 parameter is also fine — the paths are independent). Recursive values
(children, or the tier-1 parameter) are consumed **only** as the match
scrutinee and as self-call arguments; a child used as a value declines.
Cross-function calls keep the existing rule: a callee is `Nat → … → Nat`
(so a tier-1 fn may call generated `Nat` functions, and a tier-1-parameter
*callee* declines with its own message).

**Out, with homes.**

- *Parameterized instantiations* (`List<Tok>`): a monomorphized lowering has
  no name to spell `embed_T` with — the same boundary as `Option<Nat>` at
  the result, owned by `issues/datarepr-separation.md`. The in-language
  checker *accepts* the shape (it is a recognizable `Wf`) and the rim
  declines by name — the established "checker accepts what the rim cannot
  spell" decline, not a drift. `run` over `List<Tok>` therefore stays a gap;
  `eval` over `Expr` does not.
- *Two tier-1 parameters*: `SigOut` carries one position; nothing needs two.
- *Tier-1 result types*: unchanged decline (a certificate would need to
  *build* embedded trees from IR output generically).
- *Tier-0 (non-recursive) inductive parameters*: still out — their `match`
  lowers to a bare `Term::Case` with no `ElimWf`, a different body shape
  (`docs/certgen-non-nat-embeddings-design.md` §2.1's list). The recursive
  case lands *first* because the `Wf` former gave it a recursor whose step
  the marker pass can read; the irony is noted.
- *Container fields* (`[Rose; len]`), *mutual/indexed families*: out with
  their tiers.

## 3. What a tier-1 body looks like, and the marking that makes it walkable

The elaborated body of a tier-1 recursion is (probe, 2026-08-14):

```
λ(params…). elimWf(⟨shape/arity annotations⟩; M ⟨result⟩;
    s app(app(case(M P; …;
            l λ(cs'₁). λ(ih'₁). ⟦arm₁⟧;
            r case(…; l λλ⟦arm₂⟧; r λλ⟦arm₃⟧; y);
            a);
          cs);
        ih);
    ⟨param⟩)
```

— the step lives under the kernel's three telescope binders `(a, cs, ih)`,
cases on the label with `cs`/`ih` **generalized** into the case motive and
re-applied (`docs/inductive-tier1-wf-lowering.md` §6.2), and inside branch
`i` the surface binders are *compound accessors*: payload field `j` is
`fst(snd^{j+1} c)` and the ih at the `t`-th recursive field is
`ih'(ι_t)` at a literal `Fin` index.

**Decision: the marker pass normalizes the accessors; the walker walks the
eliminator.** The split follows the transcriber round's own boundary — scope
resolution is Rust's for a calculus reason (`tm_var` cannot distinguish
variables, so *which* binder an occurrence or an accessor names is
unobservable at layer m), and everything structural stays in-language:

- `mark` validates the §6.2 skeleton by de Bruijn identity (the two trailing
  applications really apply *the* `cs` and `ih`; each case's scrutinee really
  is the label / the sum rest; each branch really is two λs) and **elides
  it** — the generalization plumbing carries no fragment information once
  its identity is checked, and every variable under it is about to become a
  closed marker anyway. What survives is `ElimWf(…; step = ⟨case tree with
  bare marked arm bodies⟩; scrut = ⟨param marker⟩)` with every case scrutinee
  replaced by the same recursion-parameter marker. (Marked code is never
  re-checked, so the ill-typed residue is harmless — established by the
  fields round's annotation experiment.)
- Accessor occurrences become **two new marker shapes**, distinguishable
  structurally (variable identity being unobservable, λ-arity is the only
  discriminator — the same reasoning that made the callee marker a λ-chain):

  | occurrence | marker | walker reading |
  | --- | --- | --- |
  | parameter `i` (unchanged) | `(λx.x) ⌜i⌝` | `RLvl` at the stable level `arity−1−i` |
  | field `t` of the enclosing arm (surface declaration order) | `(λx.λy.y) ⌜t⌝` | `RFld(t)` — deferred: field `t` sits at distance `t` in the arm's environment, at *any* depth |
  | the ih at the recursive field `t` | `(λx.λy.λz.z) ⌜t⌝` | `PSelf(t, ·)` — a self-call gathering field `t` in the recursion slot |
  | the arm's field count | `(λ⁴. w) ⌜fᵢ⌝` applied *around* the arm | `TArm(fᵢ, …)` — the base depth `arity + fᵢ` the arm renders at |

  One mechanical fact the implementation surfaced, recorded for the next
  marker: a marker `App`'s `cod` annotation must carry the chain's remaining
  Π spine — the code recursor eliminates a λ *at its ascription* and is
  stuck on a λ ascribed a non-Π (`reduce.rs`'s `beta_elim_tm`). Marked code
  is never type-checked, but it is walked, and the walk reads annotations
  structurally.

  `Nat`'s own convention (`field = level arity`, `ih = level arity+1`) is
  kept verbatim — byte-stability — and is the degenerate instance: `Nat` is
  a tier-1 type with `Succ`'s one field recursive.
- A **nested eliminator declines in `mark`** now (it must: canonical
  markers are arm-relative, so a second eliminator's binders would alias the
  enclosing arm's). The old in-language level-bound decline
  (`nested_binder_sticks`) keeps pinning the walker's behavior on raw
  levels, but the *live* decline for nested `match` moved one stage earlier.

## 4. The walker's widening (in-language)

`lib/certgen/certgen_code.hthr`. The environment story first, because it is the whole
trick: in the IR, a `LetMatch` arm sees the matched `VCon`'s fields prepended
in slot order, so **field `t` is at distance `t` from the arm's base** — a
constant the depth never moves — while a parameter's *level* (`arity−1−i`)
is what stays constant. `RFld` carries the former, `RLvl` the latter, and
`pref_lvl` converts both at rendering, where the arm's base depth
(`arity + fᵢ`) is known.

- `PRef` gains `RFld(t)`; `Pre`'s `PSelf` gains the child's field index
  (`PSelf(t, rest)` — the `Nat` path emits `PSelf(0, ·)`, and `self_arg_lvl`
  generalizes to "slot `j` reads level `base−1−t`", of which the old
  "slot `j` reads level `k`" is the `base = k+1, t = 0` instance).
- `TA` gains the marker heads `TIdLam2`/`TIdLam3`/`TIdLam4` (payload-free),
  `THdr(f)` (a header awaiting its arm), `TArm(f, pre, res, len)` and
  `TArms(lvl, parts)` over a new list `Parts(f, pre, res, len, rest)` — arms
  stay *unrendered*, each carrying its field count, until the eliminator
  supplies the recursion index.
- New arms in the `transcribe` shell: `tm_case` (the dispatch tree — checks
  every scrutinee is the same parameter marker, collects header-wrapped arm
  values into `Parts`) and `tm_elim_wf` (reads the recursion index off the
  scrutinee marker exactly as `ta_elim` does, then renders arm `i` at base
  `arity + fᵢ` and assembles
  `LetMatch(j, Arm(…), Ret(RCons(0, RNil)))`). The shell's signature is
  unchanged — the per-arm field counts travel as the §3 headers, so no new
  parameter and no new argument-construction machinery at the rim. The
  unused branches' recursive results (shape, arity, motive) are never
  forced — the value-domain evaluation is lazy, which is what makes the
  global references inside the `Wf` annotations harmless.

The `ElimNat` path is untouched; every existing pin and emission is
byte-identical (the one mechanical pin move is `PSelf` gaining its field).

## 5. The signature checker's widening (in-language)

The reflected type arrives with registered lowerings already unspelled
(`fn_type_code`), so a tier-1 parameter reads as a structural
`Wf(x: S). n` — and `S` is, by the lowering's own definition, **tier 0's
lowering with the recursive fields deleted**, i.e. exactly what the existing
`SPure`/`SFlds`/`SEnum` states already recognize. So:

- `SA` gains `SWf`; a new `ty_wf(s, n)` arm answers `sig_wf(s)` — `SWf` when
  the shape reads as an enumeration(-with-`Nat`-fields), `SNo` otherwise.
  The arity walk `n` is deliberately unread (its recursive result is never
  forced): which fields are recursive is a declaration fact the rim already
  owns, and reading it in-language would drag term arms into a type walk
  for nothing the verdict states.
- `SigOut` becomes `SigYes(arity, res, wf)` with `wf = 0` for an all-`Nat`
  parameter list and `wf = Succ(d)` when the tier-1 parameter sits at
  distance `d` from the *end* of the parameter list (suffix-counted because
  the walk folds from the right; `sig_pi` over `SNat` leaves it unchanged,
  over `SWf` sets `Succ(a)`, and a second `SWf` declines). The `Nat` pins
  respell with the third field — an argued pin move, the verdict widened.
- `sig_peel` (the Rust agreement oracle) accepts one `Type::Wf` parameter
  after unspelling and reports its position; `generate_in_language` compares
  positions as it compares arities.

## 6. The certificate fold's widening — the §8.1 prediction lands

`docs/certgen-cert-expression-design.md` §8.1 predicted tier-1 source types
would be the first feature to touch `Cert`, as a constructor-level edit.
Verdict: **true, on `CertOut` exactly** — `Cert` itself is untouched (a
`CMatch` already carries an arbitrary `ctag`, a `CIh` already carries its
gathered args, and *which child* an ih is about is derivable from the
gathered recursion-slot reference, so no constructor needs a child index).

`lib/certgen/certgen_cert.hthr` gains:

```heather
inductive CArms { CANil, CACons(c: Cert, rest: CArms) }
CertOut += CRecW(scrut: Nat, arms: CArms)

fn kid_bit(n: Nat) -> Ihp                     -- the mask's parity
fn kid_rest(n: Nat) -> Nat                    -- the mask shifted right once
fn cert_arms_w(scrut, whole: Ir, after: Ir, arms: Ir) -> Nat -> Nat -> CArms
fn cert_body_w(ir: Ir, kids: Nat) -> CertOut  -- the tier-1 entry point
```

`cert_body_w` takes the per-constructor **has-children bits** (`kids`, a
little-endian `Nat` bitmask supplied from the declaration — a `Nat` because
the fold is invoked as a plain value-domain application, and a `Nat` literal
is the one library value the rim can build without lowering knowledge) and
gives each arm the
`Ihp` its constructor earns — so a self-call in a childless arm still
declines, the same honesty check as the `Zero` arm's, now per-constructor.
Arms are still selected through the library's own `pick_arm`. `cert_body`
(the `Nat`/plain entry point) is byte-identical; the rim calls `cert_body_w`
precisely when the scrutinized parameter is tier-1, which it knows from the
declaration — the `Ir` alone deliberately cannot tell a two-constructor
tier-1 match from a `Nat` match, and nothing needs it to.

## 7. The rim: names, rendering, and the model

`crates/elab/src/certgen.rs` grows names and rendering only:

- **`ParamTy`** — the parameter-position sibling of `ResTy`: the tier-1
  type's name, `{T}_gen_embed` (now a *recursive* generated fn — the
  emitter embeds a recursive field at the type's own embedding), and the
  constructor table with per-field kinds (`Nat` payload / recursive child).
  Resolved from the declaration registry; every entry is an identifier.
- **The model**: `FnIrKind` gains `RecT { rec_idx, arms: Vec<Chain> }`; the
  readback builds it when the scrutinized parameter is tier-1 (arm count
  checked against the constructor table, per-arm depth `params + fᵢ`,
  self-calls only in arms with children).
- **`render_cert`**: the `CMatch` arm generalizes — `ctag` indexes the
  parameter type's constructor table, `fields` is the embedded field chain
  over fresh `gf{t}` binders, the arm-chain names are `{m}_gen_arm{i}` —
  and the ih (`RCert::Ih`) renders as the **over-applied self-call**
  `{conv_name}(gf{t}, others…, VNil)`, the child read off the gathered
  recursion-slot reference. The `Nat` path keeps `gih` and its
  `zero`/`succ` arm names byte-for-byte.

  *(2026-08-16, `issues/certgen-emission-idiomatic-style.md`: this line and
  §1's `tsum_gen_conv(gf1, VNil)` described the n-ary form from the start,
  while the emitter actually wrote `{conv_name}(gf{t})(others…, VNil)`. Same
  term, different text, and nothing could catch the divergence — the tests pin
  the emission against its own literal, never against this document. The
  emitter was flipped in that round, so the form described here is now the
  form emitted.)*
- **`emit_invariant`** gains the tier-1 statement: the recursion parameter
  is the theorem's one declared binder, the rest curried, the body a plain
  `match` with `C_i(gf0, …)` patterns and λ-wrapped arms — no motive text
  (§1). The fixture evaluator already runs constructor trees; the literal
  argument for a tier-1 parameter is a depth-2 value built from the first
  spine constructor over the first base constructor.
- **Records**: a signature containing a non-`Nat` parameter names its record
  by its whole spelling — `Compile{T₁}…{T_k}{R}` (`CompileToksNat`,
  `CompileThNatNat`) — while all-`Nat`-parameter signatures keep the legacy
  `CompileNat{k}`/`CompileNat{k}{T}` names untouched.
- `RESERVED` widens to the `gf{t}` binder family.

## 8. Declines, and where each lives

| decline | where |
| --- | --- |
| parameterized/indexed tier-1 parameter (`List<Tok>`) | rim, by name (checker accepts the shape — §2) |
| two tier-1 parameters | in-language (`sig_pi` over a second `SWf`) |
| tier-1 result | in-language (unchanged: `SWf` is not a result state) |
| non-`Nat` field that is not the type itself | rim table + the shape walk's field rule |
| a child (or the tier-1 parameter) used as a value | `mark` (an accessor outside a self-call/scrutinee position) |
| nested `match` | `mark` (§3 — moved one stage earlier, reason recorded) |
| a tier-1-parameter callee | `mark`'s callee rule (unchanged shape, new message) |
| self-call in a childless arm | in-language (`cert_body_w`'s `Ihp`) |
| no base constructor | rim (fixture literal is unbuildable) |

## 9. Cost

Not a perf round. Expected shape (measured in the round, numbers on
`issues/certgen-harness-cost.md`): the walker file's elaboration grows by a
few `TA` constructors and two shell arms (the 52-branch gate's *count* is
unchanged — all branches were always checked); generation stays tens of
milliseconds per fixture (the value-domain reader); each new fixture's
emission adds ~1 s of `_gen_conv` kernel checking, the known per-function
increment. New fixtures live in their own test binary (`certgen_tier1.rs`)
with its own 300 s rail, warm-prefix-gated like its siblings; its
acceptance-class tests join the `--fast` skip list.

## 10. Acceptance — run 2026-08-14, all items met

1. ✅ The two §1 hand-runs, retired into generated form: `tsum` (linear) and
   an `eval`-shaped `esum` (`Plus2(l, r) => add(esum(l), esum(r))` — two ihs
   in one arm, a foreign call combining them, a two-member program with
   `add_gen_conv_in_esum` re-derived inside it) generate, emit, and
   kernel-check end to end (`crates/elab/tests/certgen_tier1.rs`).
2. ✅ `th` (three constructors, payload fields on either side of children, a
   second `Nat` parameter, a foreign call) — the arm-count/field-order axes —
   plus `thas`, a tier-1 parameter WITH a tier-0 enumeration result: the two
   previous stages compose with no special-casing (`CompileToksFlag`).
   Plus `tlen0` and `wnat` — a tier-1 parameter that is NOT the recursion
   parameter, beside a plain body and beside a `Nat` induction: §2's "the
   paths are independent" sentence exercised, which caught the one emitter
   gap the end-to-end fixtures alone would have missed (the unused
   parameter's slot must embed at its own embedding in a `Nat`-shaped
   invariant).
3. ✅ The library states its own acceptance: `tier1_field_marker` /
   `tier1_ih_marker` / `tier1_arm_header`, `tier1_linear_transcribes` (the
   hand-run's body, byte for byte), `tier1_payload_arm_renders`,
   `tier1_mixed_scrutinee_declines`, `tier1_headerless_arm_declines`; the
   five `sig_*` tier-1 pins; `tier1_body_splits_the_arms` and
   `tier1_childless_self_call_declines` in the fold's file. All held on
   their first elaboration.
4. ✅ Byte-stability: every existing emission (`Nat`, non-`Nat` result,
   fields) byte-identical; all existing `IR_*` pins and every mutation
   control green untouched. The argued pin moves: `PSelf` gained its
   child-index field (`PSelf(0, ·)` on the `Nat` path), `SigYes` its third.
5. ✅ Declines of §8 asserted with their attributions; no signature
   disagreement anywhere. One fixture FLIP recorded at its site, the
   `tocmp` discipline again: `certgen.rs`'s `evalish2` (a `Val` parameter)
   is in the fragment now, replaced by a two-tier-1-parameters decline.
6. ✅ A mutation control on the *widened* walker — with a better mutation
   than the sketch's: the arm-order swap dies as a *decline* (the childless
   arm's self-call check catches it), which is the weaker control, so the
   landed control perturbs `ta_ih_at` to hand back the arm's first field as
   the self-call's value (`RLoc(0)` → `RFld(0)`). That renders — right
   instruction, right arity, references in range — terminates, and is
   refused by the kernel at the emission's own exactness fixture; the
   library's pins refuse it first, asserted before they are stripped.
7. ✅ Full `scripts/test`: 1498 passed, 0 failed (+2, the new binary);
   `scripts/bench --check`: 18 comparisons within thresholds; the showcase
   README's derive-`Compile` row updated (`eval`'s shape is in the fragment;
   `run`'s parameterized `List<Tok>` stays out, with its owner named).

## 11. Rejected alternatives

- **Walking the raw §6.2 skeleton in-language** (no eliding, no accessor
  markers): refuted by the `tm_var` opacity fact — the walker cannot verify
  *which* variable an application head or a projection root is, so the
  skeleton's identity checks are scope resolution, which is the marker
  pass's charter. The alternative was not cheaper in-language code but
  *unsound-to-the-fragment* in-language code (it would have to trust shapes
  it cannot identify), plus `nth`-schema recognition for nothing.
- **Rust-side restructuring of the whole eliminator** (mark hands the walker
  a pre-digested arm list): guts the in-language story — the `LetMatch`
  assembly *is* the transcription. Eliding only the identity-checked
  generalization plumbing is the narrow cut.
- **A `gih`-binder induction for tier-1** (the `Nat` emitter's style):
  needs per-child ih binders in patterns and an explicit motive; the
  over-applied self-call style is checked (§1), simpler, and is the style
  the showcase itself writes.
- **Carrying the child index on `CIh`**: derivable from the gathered
  recursion-slot reference; a redundant field on a `Wf`-lowered inductive
  is exactly what the size-law rules say not to add.
- **`fcounts` as a shell parameter** (a `Refs` argument, like `arity`): this
  was the design's first cut, and the implementation reversed it — building
  a `Refs` *literal term* in Rust means hand-constructing the library
  inductive's `Supf` lowering, exactly the lowering coupling the reader's
  pinned-shapes block exists to quarantine. The arm-header marker keeps the
  fact in the marker coordinate system the reflection boundary already owns,
  and dropped the shell-signature change with it. (The fold's `kids` mask
  stays a parameter because a `Nat` literal costs nothing to build — the
  asymmetry is the two types' lowering costs, not taste.)
