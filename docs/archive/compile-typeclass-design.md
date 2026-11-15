# `Compile` certificates: design sketch (v1)

Status: **design sketch, pre-implementation** (2026-08-01). Written before
the code, per repo discipline; when the implementing round lands, this file
becomes the specification it is checked against.

Tracking issue: `issues/compile-typeclass-design.md`. The milestone this
unblocks is `issues/end-to-end-compile-instance.md`. Adjacent decisions live
where they are owned: the IR and its `converges` interface in
`docs/archive/ir-simulate-design.md` (closed round), the representation boundary in
`issues/datarepr-separation.md`, the derived-artifact story in
`issues/generators-in-the-language.md`.

The design principle, stated once: **the certificate is logical; everything
else about `Compile` is operational.** A `Compile` instance's `equiv`-shaped
field is the only part the kernel is asked to believe. Which instance the
compiler picks, how instances are found, how artifacts are deduplicated —
all of that is policy about *which correct IR runs*, and none of it can
threaten soundness, because every candidate carries its own proof. Every
decision below is scored against that split.

---

## 1. Role, and what is already settled

The contract (`issues/compile-typeclass-design.md`, unchanged since filing):
a function is compilable iff it has a `Compile` instance containing (a) IR
production and (b) a certificate that the IR simulates to the same result as
the kerneltime function. The compiler consumes only proof-carrying
instances — privileged operationally, never logically.

Settled in the sketch rounds (`docs/archive/surface-v1.md` §6, `v2.md` §1,
`v3.md` §1) and **not reopened here**:

- Dictionaries are first-class ordinary values; trait-vs-typeclass is
  resolution policy, not semantics.
- Coherent by default; named instance values as the multiple-structures
  escape; `let instance C for T = v;` as the scoped, certificate-carrying
  override.
- Multiple targets by indexing the class — `Compile[Cpu] f`, `Compile[Gpu]
  f` — coherence per (f, target).
- Context-specific compilation as *smart instances*, not smart resolution:
  `ir(ctx: CallCtx)` with one ∀-ctx `equiv`; artifact dedup keyed on
  (function syntax, ctx descriptor).
- Instances keyed on **syntax** (boxed code is intensional); refactoring a
  function invalidates its instance, deliberately.

What this round adds is the answer to the issue's one standing open
question — "is `typeclass` even the right notion?" — and the concrete v1
shape the milestone checks.

## 2. Decision: the v1 instance is an ordinary record value

The question "typeclass or something bespoke" dissolves once it is split
along the logical/operational line:

- The **logical** content of an instance is a record: IR production plus a
  certificate field whose type mentions the earlier fields. The surface has
  had exactly this since `surface-records` — a dependent field spine is what
  `record` *is* — and `lib/certgen/ir_v1.hthr` already exports the certificate type
  it wants (`Converges`, the ∃-form; that issue's 2026-08-01 entry says in
  so many words that this is the shape a `Compile` instance wants).
- The **operational** content — resolution, coherence, `[Cpu]` indexing,
  `.code` keying — needs machinery that does not exist yet (a compiler
  walking the call graph from `main`, quote/boxed code at the surface,
  `issues/elaboration-determinism.md` as an enforced guarantee). None of it
  is needed to *state or check* a certificate.

So: **v1 builds no class mechanism at all.** A `Compile` certificate is a
record type; an instance is a value of it; the milestone is one such value,
kernel-checked. The class layer arrives when its consumer (the resolver)
does, and §5 records what it will look like so nothing here pre-commits
against it. This answers the issue's open question in the deflationary
direction *for v1*, and defers the real notion-choice to the round that
builds resolution — with the note that by then it is a choice about
*surface syntax and policy*, since the semantics is already fixed as
"record value."

## 3. The v1 certificate record

Per-signature and monomorphic, matching what records are today
(monomorphized type parameters, no `Type`-valued fields):

```heather
// in lib/certgen/ir_v1.hthr — there is no module system, and a sibling file would
// have to re-declare the whole IR (ir-simulate-design items 3–4 note)
record CompileNat2(f: Nat -> Nat -> Nat) {
    prog: Prog,
    entry: Ir,
    cert: (a: Nat) -> (b: Nat)
          -> Converges(prog,
                       VCons(embed_nat(a), VCons(embed_nat(b), VNil)),
                       entry,
                       VCons(embed_nat(f(a)(b)), VNil)),
}
```

Reading it against the contract:

- **(a) IR production** is `prog` + `entry`: the program (callee
  environment) and the body the certificate is about, exactly the pair every
  `ir_v1` theorem quantifies. v1 stores IR, not an `ir()` function — the
  ctx-parametric form (§5) generalizes this field to `CallCtx -> …` later,
  and `refines_of_bounded`-style bridges mean nothing proved against the
  constant form is lost.
- **(b) the certificate** is ∀-args convergence to the embedded spec result.
  The ∃-form (`Converges`) rather than a `∀ fuel ≥ bound` schema, so the
  statement names no fuel; `conv_loosen` recovers a bound when a consumer
  wants one.
- **The coupling is by value parameter.** `CompileNat2(f)` mentions the spec
  function in the *type*, so "which function is this an instance for" is
  part of what the kernel checks — coupling via same-typeclass membership
  (settled sufficient at filing) lands here as coupling via the parameter.
  Two spellings of the spec that are convertible give the same type, which
  is right for the *logical* layer: intensional keying is the operational
  layer's concern (dedup, invalidation) and waits for `.code` (§5).
- **The embeddings are baked in** (`embed_nat` at both ends), which is what
  makes the record per-signature. The generic story — per-type embeddings
  as derived artifacts, n-ary argument spines — is exactly
  `issues/generators-in-the-language.md` + `issues/datarepr-separation.md`
  territory, and a level-1 bundled record (`carrier: Type`) is a
  `Type`-in-`TyKind` round (`docs/surface-records.md` §3 names it). Until
  then, one record per signature is honest monomorphization, consistent
  with the rest of the surface.

## 4. The milestone instance

`issues/end-to-end-compile-instance.md`, at last concrete. The ingredients
all exist in `lib/certgen/ir_v1.hthr`:

```heather
fn add_spec(a: Nat) -> Nat -> Nat { λ (b: Nat) => add(b, a) }

fn add_instance() -> CompileNat2(add_spec) {
    CompileNat2 {
        prog:  add_chain(),
        entry: ir_call2(),
        cert:  λ (a: Nat) => λ (b: Nat) => add_converges_through_calls(a, b),
    }
}
```

Notes the implementing round must respect:

- **The spec is spelled the way the loop computes.** The theta-loop counts
  `a` down onto `b`, so the implemented function is `λ a b. add(b, a)`
  (`ir_v1`'s own "THE CERTIFICATE" comment). `add_spec` states that
  honestly. An instance for `add` itself (arguments unswapped) is the same
  record with `add_comm` composed into the certificate — a good second
  instance, not the milestone.
- `cert`'s field type instantiates at `f := add_spec`, so checking the
  literal asks conversion for `embed_nat(add_spec(a)(b)) ≡
  embed_nat(add(b, a))` under two binders — δ then β, no new machinery.
- **Negative controls** per `docs/testing-generated-terms.md`: a
  wrong-result instance (`cert` claiming `f(a)(b) = add(a, a)`-shaped
  results) must fail to check; a junk `entry` must make the certificate
  unprovable, witnessed by the existing `Stuck` theorems. The elab test
  asserts the failure, not just the success.
- **Budget:** `crates/elab/tests/ir_v1.rs` runs at ~198s debug against
  `scripts/test`'s 300 CPU-s rail. The instance is a record declaration
  plus repackaging of landed theorems — small — but the header's budget
  note is the thing to update, and if the additions push the rail, the
  negative controls move to the always-on cheap test alongside the
  existing wrong-claim refutation.

When this checks, the milestone's sentence is true with no asterisk: one
small pure function, a hand-written instance producing IR for it, an
equivalence certificate checked by the kernel. The certifying generator is
then automation of a *value* whose type already exists.

## 5. Recorded for the class layer (not v1, each with its prerequisite)

> **Superseded 2026-08-07** by the general traits design
> (`docs/traits-design.md`, issue `traits`): resolution-from-`main` becomes
> "the compiler is one client of the general resolver"; `[Cpu]` indexing is
> **struck** (Compile certifies function → IR, which is arch-agnostic; arch
> belongs to the IR→native stage, and class indexing dissolves into ordinary
> record parameters); `let instance` and `.code` keying carry over into that
> design. `CallCtx` stays owned here (§8). Also stale below in §6: the
> level-1 bundled-record round landed 2026-07-27.

- **Resolution-from-`main`** — the compiler walks the call graph resolving
  in-scope instances per site. Prerequisite: a compiler consuming
  instances at all (`issues/certifying-generator.md`,
  `issues/datarepr-separation.md`).
- **`Compile[Cpu]` target indexing and coherence per (f, target).**
  Prerequisite: same as above; until a second target exists the index is
  vacuous.
- **`let instance` scoped override.** Prerequisite: resolution. The v2
  sketch's safety argument (override is safe *because* certificates pin
  semantics) is inherited unchanged — it is the §0 principle.
- **Intensional keying on `.code`** and per-syntactic-definition
  coherence/invalidation. Prerequisites: surface quote,
  `issues/elaboration-determinism.md` as enforced.
- **Ctx-parametric instances** (`ir(ctx: CallCtx)`, ∀-ctx certificate,
  dedup on (syntax, descriptor)). Prerequisite: `CallCtx` descriptor
  design — the coarseness lever, still owned here, still open.

## 6. Deliberately rejected

- **Building any resolution/class machinery now.** Nothing consumes it; it
  would be designed against zero call sites and one instance. (The whole
  of §5.)
- **A signature-generic `Compile` via bundled records** (`carrier: Type`
  fields). Blocked on the level-1 record round and on per-type embeddings;
  premature generality that `generators-in-the-language` will do properly.
- **Forcing `cert` to reference a sibling `runtime_func` field.** Coupling
  by membership/parameter was settled sufficient at filing; producing IR
  standalone stays legitimate (a `CompileNat2(f)` value *is* usable as
  "IR for `f`" without any function object in the record).

## 7. Acceptance sketch (for the implementing round)

1. `CompileNat2` declared in `lib/certgen/ir_v1.hthr`; `heather check` green.
2. `add_spec` + `add_instance` check; this closes
   `issues/end-to-end-compile-instance.md`.
3. Negative controls in `crates/elab/tests/ir_v1.rs`: wrong-result
   certificate refuted; the budget note updated with measured times.
4. A second instance for the *same* spec through a different IR
   (`ir_loop()` directly, via `add_converges`), demonstrating
   coherence-is-policy: two values of one type, either usable, semantics
   pinned by both certificates. Cheap — both certificates are landed
   theorems.

## 8. Open questions

- `CallCtx` descriptor shape (carried from `ir-simulate-design` §12;
  the lever is coarseness).
- Where instance values are *registered* once a resolver exists — a
  declaration form (`instance … for …`), or discovery over ordinary
  globals of `Compile*` type. The v2 sketch's syntax assumed the former;
  nothing in v1 commits.
- Whether `prog`/`entry` stay two fields or become one packaged
  `(Prog, Nat)` function reference once `Prog` grows real function tables
  (`Apply`-heavy IRs want the entry to be an index, not a body).
