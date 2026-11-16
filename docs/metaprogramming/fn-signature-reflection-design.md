# Signature reflection for analyzers: the pull API's first cut

Design for the "cheap first step" of `issues/fn-reflection-for-analyzers.md`:
the certifying generator's fragment *signature* check moves in-language, fed by
the first reflection primitive an analyzer can request — "this fn's type as
code". Round pattern as usual: this document first, the implementation against
§7's acceptance list.

Context it builds on, and does not restate: the transcriber round
(`docs/archive/certgen-transcriber-in-language-design.md`) moved the *body* half of the
fragment definition into `lib/certgen/certgen_code.hthr`, leaving the signature half in
Rust (`certgen.rs`'s `marked_body`, where peeling the Lam spine doubles as the
`Nat → … → Nat` check — its §5 table files that under "a fact about the
*declaration*"). The reflection issue names that split a drift vector: the two
halves are coupled only by the design doc and the cross-check. This round
closes the *signature* half of the vector; the body half's endpoint is
`issues/code-variable-analysis-api.md`.

## 1. The pull API, mechanically

**Decision: "pull" is a reflection primitive on the elaborator, consumed by
the analyzer *invocation*, with the analyzer's own signature declaring what it
pulled.** Concretely, three pieces:

1. **The primitive.** `Elaborator::fn_type_code(name) -> Option<Term>`: a
   declared fn's elaborated statement, rescoped to the current Ψ and boxed —
   a term of type `TyCode(·)` (kernel `CodeTy { ctx: ·, level: 0 }`), i.e.
   *the fn's type as code*, ready for the type-code recursor. Nothing is
   stored per declaration and nothing is emitted at declaration time: the
   type already lives in Ψ (a fn is an ordinary `GlobalBinding::Tm`), and the
   primitive reads it on request. That is the whole difference from push —
   the issue's constraint — and it is also why the primitive is honest about
   staging: when the elaborator is Heather, this is an ordinary metaprogram
   operation over Ψ.

2. **The declaration of appetite.** An analyzer that wants a signature takes a
   parameter of type `TyCode(g)` — a code-of-a-type value — in its slot
   signature. The slot's expected signature (written in Heather,
   `slots::AnalyzerSpec::signature`) is where the pull is *visible*: a reader
   of the slot vocabulary sees exactly which reflected data each analyzer
   receives. No new registration machinery: whole-signature convertibility
   (`docs/metaprogramming/meta-def-registration-design.md` §11) already fixes the Π order, so
   the invoking Rust fills the `TyCode` position from the primitive in the
   slot's canonical order, exactly as it fills the `Code(g |- Nat)` position
   of `certgen.transcribe`.

3. **The invocation.** The harness (here: `generate_in_language`) names the fn,
   calls the primitive, applies the registered analyzer to `(Γ = ·, the boxed
   type)`, and reads the answer back. The "request" of the issue's pull
   framing is this call: reflection happens per invocation, for the one fn the
   analyzer is being run on.

**The interface/implementation seam, stated for the opaque-globals round.**
The interface is: *name in, a `CodeTy(·, 0)`-typed `box`ed type out* (plus the
`TyCode(g)` parameter spelling on the analyzer side). Today's implementation
reads the elaborator's own global table and applies `shift_global` by the Ψ
growth since the binding (the same `v + 1` convention `Defs::body` uses —
prefix-scoped kernel data used at the end of Ψ). The opaque-globals kernel
round replaces that *body* with `u^δ` unfolding-for-analysis under its ch. 07
obligations; `lib/certgen/certgen_code.hthr` and the slot signature do not change,
because they only ever see a `TyCode(g)` value. That is requirement (1) of the
issue discharged by construction: the analyzer cannot observe where the code
came from.

Level note: `TyCode(g)` elaborates at code level 0, matching the `Code`-binder
slice. A fn whose type is not a level-0 layer-c type produces a value the
walker's default arm answers `SigNo` to — a decline, never wrongness, per the
untrusted-generator architecture. No level polymorphism is added.

## 2. The in-language checker

**Decision: the checker joins `lib/certgen/certgen_code.hthr`** (the transcriber
design's §4 reason 3 — the whole fragment definition in one readable file —
is exactly what this round is for; a sibling file would re-open the two-homes
problem one directory closer).

The data and helpers, ordinary program-layer Heather in the file's style:

```heather
inductive SigOut { SigNo, SigYes(arity: Nat) }
```

`SigYes(a)` read off the raw walk means "this type is `Nat → … → Nat` with `a`
parameters"; only the `ty_nat` arm mints `SigYes(0)`, so "the domain is
*exactly* `Nat`" is the one-line test `sig_pi` performs:

- `sig_pi(dom, cod)`: fragment Π iff `dom = SigYes(0)` (a bare `Nat` — a
  higher-order `Nat → Nat` domain arrives as `SigYes(1)` and declines) and
  `cod = SigYes(k)`; result `SigYes(Succ(k))`.
- `sig_finish(s)`: declines `SigYes(0)` — a nullary fn has no calling
  convention to certify — so the *whole* fragment signature rule, arity
  included, is in the file. Declining is total: `SigNo` propagates, like
  `TStuck`.

The shell, beside `transcribe` in the file's layer-m block:

```heather
meta fn check_sig(g: Ctx, sig: TyCode(g))
    for certgen.check_sig -> SigOut
{
    sig_finish(match code sig as SigOut {
        ty_nat        => SigYes(0),
        ty_pi(s, t)   => sig_pi(s, t),
        _             => SigNo,
    })
}
```

`ty_pi` binds two recursive results (`x_S`, `x_T` — rec.rs's `ty_pi`
telescope, ch. 04's `G_Typ` second premise, where `x_T` lives at an extended
local context: the constant-motive argument applies to the type walker
verbatim). Everything else — `ty_sigma`, `ty_w`, the inlined lowerings of
user inductives, dependent codomains that are not `Nat`-chains — hits the
default arm and declines.

Refl-pin theorems in the file's existing style: `add`'s and `dbl`'s signature
verdicts (`SigYes(2)`, `SigYes(1)`), the nullary decline, and the
higher-order-domain decline.

**Composition with the body verdict**: sequential, not braided. The signature
checker answers first (it decides *whether the fn is in the fragment* and what
its arity is); the marker pass and `transcribe` then run at that arity. A
`SigNo` is a decline before any marking happens. The two verdicts never
disagree with each other because they answer different questions about
different inputs (the type; the marked body).

## 3. The honest widening, chosen

The issue names two candidates: "the type motive stops being `Unit`, or a
second `match code` over a `Typ` code". The first is **already moot** — the
transcriber round's landed slice uses *one* constant motive for both motives
(`elab_match_code` builds `Motives { ty_motive: T, tm_motive: T }`), so the
eight `ty_*` arms have been writable since that round; nothing here widens
arms or motives.

What is actually missing, checked against the kernel rather than assumed:

1. **`match code` over a type-code scrutinee.** The kernel recursor exists in
   full — `Term::ElimCodeTy` (typing.rs:1674: scrutinee at
   `CodeTy { ctx, level }`, result `M_Typ` instantiated; ch. 04's `\ELIMTYP`
   conclusion at l. 1135), its β on `BoxTy` (reduce.rs:706 →
   `beta_elim_ty`), and its neutrality on a non-`box` head (reduce.rs:2202) —
   and it shares motives, branches and the `rec_ga` gate with `ElimCodeTm`,
   so the surface widening is one dispatch: `elab_match_code` accepts a
   scrutinee whose type WHNFs to `CodeTy` and emits `ElimCodeTy` instead of
   `ElimCodeTm`. Same 52 arms, same constant motive, same default-arm rule.

2. **`TyCode(g)` as an ordinary `meta fn` parameter.** The surface spelling
   already parses (`TyKind::TyCode`); `meta_sig` refused it because its only
   imagined role was the Ψ-extending *binder* delivering `$a` type splices,
   which the binding invariant rules out for templates ("`TyCode` returns
   with the analysis story" — quote.rs's `MetaBinder` note, now cashed in).
   This round admits the *other* role only: `sig: TyCode(g)` becomes an
   ordinary Π-bound local of kernel type `CodeTy { ctx: g, level: 0 }`
   (`Sig::Local`), exactly parallel to `Code(g |- T)` locals. The
   Ψ-extending `TyCode` binder — and with it `$a` splices for analyzers —
   stays out; nothing in this round needs to *build* code mentioning a
   reflected type.

Cost honestly stated: a second `match code` shell in the library file means a
second 52-branch `rec_ga` check per elaboration of the file (and its own
registration re-elaboration). The `SigOut` motive is far smaller than `TA`, so
the increment is well under the transcriber shell's ~9 s; the stack budget
(`RUST_MIN_STACK=8388608`, transcriber design §8) now covers two shells per
test thread, verified by running the suite rather than argued.

## 4. What the cross-check now pins

Rust `marked_body` still runs on the in-language path, split into its two
halves without changing what it computes: `sig_peel` (peel the body's Lam
spine against the type's Π spine; the `Nat`-only, `Nat`-result and non-nullary
checks) and `mark` (the de Bruijn→level renaming). `marked_body` remains their
composition, frozen in behavior.

**The agreement property**: for every fn the in-language path is asked to
generate, the in-language verdict `check_sig(type-as-code)` and the Rust
verdict `sig_peel` either both decline, or both accept **with equal arity**.
`generate_in_language` runs both and:

- both accept, arities equal → proceed (with the peeled body, marked at that
  arity);
- both decline → decline, wording the reason as the in-language checker's
  (the *decision* is in-language; the Rust decline is the residue agreeing);
- anything else → an error whose message says `signature disagreement` and
  prints both verdicts. Still an `Err` (the generator is untrusted and must
  not panic on library input), but tests assert the string never appears:
  every negative-control decline is checked *not* to be a disagreement, so a
  drift between the two halves is a loud test failure, never a silent decline
  onto the Rust path.

The surface-AST checks in `fragment()` (which `generate()` and the emission
share) are untouched — they are the *Rust path's* fragment definition and the
frozen oracle discipline of `issues/retire-rust-transcriber.md` keeps them
passing; the byte-identical emission cross-check on `add`/`dbl`/`third3` is
unchanged and keeps pinning the layout interface.

Ordering note that the controls depend on: `generate_in_language` consults the
signature verdicts **before** `fragment(d)`, so a non-`Nat` parameter, a
non-`Nat` result or a nullary fn is declined *by the in-language checker* (the
tests assert the message says so), while body-shape declines (`let`
statements, non-fragment arms) still surface from the residue afterwards with
their existing wording.

## 5. The residue that stays Rust, and why it is mechanical

- **Scope resolution / marking** (`mark`): unchanged, and stays for the stated
  kernel reason — `tm_var` abstracts over the variable at layer v, so
  occurrence→level renaming is not expressible in-language until closed-term
  substitution sugar lands (`issues/code-variable-analysis-api.md`). It
  consults no fragment knowledge.
- **The body peel** (`sig_peel`'s spine walk): marking needs the body under
  its binders and the binder count; peeling is coordinate bookkeeping. Its
  *checks* are kept only as the agreement oracle of §4 — the fragment
  decision they used to be is now the library's.
- **Parameter names and the reserved-name check** (`fragment()`): facts about
  the emitted *proof text* (which binds `gz`/`gk`/`gih` and spells parameter
  names into specs), not about the fragment; the walker has no names by
  design.
- **Readback and emission**: unchanged homes (transcriber design §5's table).

*Widened 2026-08-12* (`docs/certgen-non-nat-embeddings-design.md@4acf2fe` §5): the
signature rule is still whole in `lib/certgen/certgen_code.hthr`, but `SigOut` is no
longer its own accumulator — the walk runs on an `SA` state type and the
verdict is `SigYes(arity, res)`, where `res = 0` is a `Nat` result and
`res = k ≥ 1` an enumeration with `k` constructors. `sig_pi`'s domain rule is
unchanged; `ty_unit`/`ty_sigma`/`ty_sum` arms were added. §4's agreement
property gains the result term: the Rust residue resolves the declaration's
result type by *name* (an identifier no reflected form carries) and the two
verdicts must agree on the constructor count as well as on the arity.

After this round the fragment definition reads off one file:
`lib/certgen/certgen_code.hthr` decides the signature (`check_sig`) and the body
(`transcribe`); Rust contributes coordinates, names, and the kernel-checked
emission. The drift vector the issue names is closed for v1's fragment; it
reopens only if a new fragment feature lands with a Rust-side check, which
stage 1 of `issues/retire-rust-transcriber.md` forbids.

## 6. Declined and deferred, with homes

- **Body reflection** ("this fn's marked body" as a pull primitive) — the
  invocation already passes the marked body, but *naming* it as a primitive
  belongs with the opaque-globals round that changes how it is computed.
  Stays on `issues/fn-reflection-for-analyzers.md`.
- **Reasons in `SigOut`** (a decline that says *which* parameter offended) —
  the file's decline discipline is one value (`TStuck`, `SigNo`); reasons live
  at the Rust rim. Widening declines into data is a per-analyzer choice for a
  future analyzer that needs it.
- **The Ψ-extending `TyCode` binder** (`$a` splices from analyzed types) —
  out, as before; its consumer is a transformation pass, not an analysis.
- **User-declared analyzer slots** — deferred with user-declared slots
  generally (`docs/metaprogramming/meta-def-registration-design.md` §10).
- **`generate()`'s Rust path consulting the in-language checker** — no: the
  Rust path must keep working in a session with no library loaded (the
  no-regression rule), and the frozen walker is not extended, only agreed
  with.

## 7. Acceptance

1. `TyCode(g)` as an ordinary `meta fn` parameter elaborates (kernel-checked
   at `Layer::Meta`); the template-role refusal is gone and the binder role
   still has no entry point.
2. `match code` on a `TyCode` scrutinee elaborates to `ElimCodeTy` and
   computes through the `ty_*` branches; existing `quotation.rs` diagnostics
   unchanged.
3. `lib/certgen/certgen_code.hthr` gains `SigOut`, `sig_pi`, `sig_finish`, their refl
   pins, and the `check_sig` shell claiming `certgen.check_sig`; the file
   still elaborates whole (its theorems are its own acceptance).
4. Positives: `add`, `dbl`, `third3` byte-identical to the Rust path; `seven`
   still IR-identical with the recorded spec-spelling divergence; `mul` still
   declines by neutrality naming the global.
5. Negative controls, each declined by the in-language checker with the
   message saying so, and none a disagreement: a non-`Nat` parameter, a
   non-`Nat` result, a nullary fn.
6. The agreement property of §4 asserted on every fixture above.
7. Full `scripts/test` green, including both whole-library acceptance tests.
