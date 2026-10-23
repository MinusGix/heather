# The certificate expression, and its fold, in the language

Design for **Round A** of `issues/in-language-certificate-emission.md`, as
scheduled by `docs/certgen-emission-route1-spike.md` §7: the ∃-composition
kit's fold stops being Rust string assembly and becomes an ordinary
program-layer datatype plus ordinary program-layer `fn`s in `lib/`, with the
*emission* — the proof text — still rendered from Rust.

Round pattern as usual, and the shape is `docs/certgen-transcriber-in-language-
design.md`'s verbatim, one phase later: data and helpers in `lib/`, invocation
through the evaluation hook, readback in Rust, the emitters downstream
unchanged. The predecessor round moved phase 2 (transcription); this one moves
the *decision half* of phase 3 (certificate emission), which that document's §5
table listed as **Rust, blocked**. What unblocks it is not new calculus: it is
noticing that the fold's *statement* is what route 1 could not build, while the
fold's *structure* is first-order data that layer p has always been able to
compute.

The principle inherited from `issues/certifying-generator.md`, unchanged and
now one step wider: **the generator is untrusted.** A wrong fold picks the
wrong lemma, spells the wrong sub-IR, or routes the induction hypothesis to a
foreign call — and every one of those is a *refused certificate*, because the
kernel checks the emitted theorem against the emitted body. Round A's payoff is
that the wrongness now lives in a library file a test can perturb with one
edit (§8), which is the sentence the spike memo used to justify scheduling it.

Line references are `crates/elab/src/certgen.rs` unless said otherwise.

---

## 1. What Round A is, and the two things it is not

**Is.** `lib/certgen/certgen_cert.hthr`: an inductive `Cert` whose constructors are the
kit lemmas of `lib/certgen/ir_v1.hthr` (`ret_conv`, `letcon_conv`, `letcall_conv`,
`letmatch_conv`), an inductive `CertOut` for a whole invariant, and the `fn`s
that fold an `Ir` — the transcriber's own output value — into one. Plus, in
Rust, a readback and a renderer that turn that value into the proof text, byte
for byte what `conv_of_chain`/`emit_invariant` used to assemble directly.

**Is not (1): the Ψ-staging of route 1.** No code type, no box, no `meta fn`,
no new slot. `Cert` is exactly the "calculus-legal `Code2`" the issue's
2026-08-12 entry names: an ordinary inductive replicating the *shape* of a
proof, folded at layer p where recursion exists. Turning a `Cert` into a
kernel-checked theorem is done by *printing it and re-elaborating*, which is
what the generator has always done; doing it by minting Ψ entries per
instruction is Round B and is optional.

**Is not (2): a verified fold.** `Cert` is not indexed by the `Ir` it is about
and there is no theorem relating them. That statement — "this `Cert` proves
`Converges(p, env, ir, vs)`" — is precisely the dependent statement item (d) of
the spike blocks (memo §4), and it is route 3's. What we have instead is the
certifying property, and it is enough: the *rendered* certificate is checked.

## 2. The datatype

```heather
inductive Ihp  { IhNo, IhYes }
inductive Cert {
    CStuck,
    CRet(rs: Refs),
    CCon(tag: Nat, args: Refs, hr: Cert),
    CIh(args: Refs, hr: Cert),
    CCall(c: Nat, args: Refs, hr: Cert),
    CMatch(scrut: Nat, ctag: Nat, ha: Cert, hr: Cert),
}
inductive CertOut { CPlain(c: Cert), CRec(scrut: Nat, zero: Cert, succ: Cert) }
```

One constructor per kit lemma, with the exception that `letcall_conv` gets
**two** — and that split is the round's one genuinely load-bearing decision, so
it is justified below rather than in passing.

Field by field, against the lemma signatures (`lib/certgen/ir_v1.hthr` ll. 841–905) and
against what the Rust fold used to spell:

| `Cert` | lemma | fields ↔ arguments |
| --- | --- | --- |
| `CRet(rs)` | `ret_conv(p, env, rs, vs, hg)` | `rs` is the lemma's `rs`, spelled literally. `p`, `env`, `vs` are names (§3); `hg` is always `refl`. |
| `CCon(tag, args, hr)` | `letcon_conv(p, env, tag, args, rest, fs, vs, hg, hr)` | `tag` and `args` verbatim; `rest` is `hr`'s own chain (see below). `fs` is the gathered field list — derived from `args` against the env, i.e. names. |
| `CIh(args, hr)` / `CCall(c, args, hr)` | `letcall_conv(p, env, callee, args, rest, cargs, ws, vs, hg, hc, hr)` | `c`/`args` are `callee`/`args`. `hc` — the *callee's* certificate — is the split: `CIh` says "the induction hypothesis", `CCall` says "closure member `c`'s invariant, applied". `cargs`, `ws` are names. |
| `CMatch(scrut, ctag, ha, hr)` | `letmatch_conv(p, env, scrut, arms, rest, tag, fields, ws, vs, hl, ha, hr)` | `scrut` verbatim; `ctag` is the constructor arm being proved, which is *induction-step* data, not IR data. `arms` is a name (§3); `rest` is `hr`'s chain. `fields`, `ws`, `vs` are names. |
| `CStuck` | — | the decline. |

**The `rest` arguments are not carried, because the chain is its own IR.** The
three lemmas that take the remaining region as an argument take *exactly* the
region their sub-certificate is about, so it is recovered by printing the
sub-certificate (`ProofCx::cert_ir`) rather than stored twice. Two reasons
beyond tidiness, and the second is the reason it is a decision rather than a
preference:

- the `rest` a certificate spells is in **closure** coordinates while the `Ir`
  the fold reads is in the walker's (§3), so a carried `Ir` would have to be
  renumbered on the way out anyway — the printer is where the numbering is
  converted, which is where it already was;
- an `Ir`-typed **field on a `Wf`-lowered inductive is astonishingly expensive
  to elaborate**: the first cut of this file, identical but for `rest: Ir` on
  three constructors and `after: Ir` on `CMatch`, cost **163 CPU-seconds**
  against **1.0 s** for the version above (measured 2026-08-12, per item: a
  single `match` on the `Ir`-carrying `Cert` cost 4–7 s and a nested one 25–46
  s). At three test sessions that is the difference between comfortably inside
  `scripts/test`'s 300-second per-process rail and far outside it. The general
  rail, for `issues/certgen-harness-cost.md`: an inductive **field** whose type
  is another `Wf`-lowered inductive multiplies the cost of every elimination
  over the container, and a nested `match` on such a type multiplies it again.
  Carry `Nat`s and let the printer recover the rest.
  *(Corrected 2026-08-12, `issues/wf-field-conversion-cost.md`: the mechanism
  round could not reproduce the 163 from this recorded shape — the faithful
  reconstruction is 8.5×, ~30 CPU-s with the six `Cert` eliminations — and
  "Wf-lowered" is not the operative predicate; the cost is Θ(arms × |lowered
  field type|), quadratic in the field type's constructor count, a named
  match-lowering pathology with a sized fix. Read that issue, not this
  paragraph, before designing around it.)*

**Why `CIh` and `CCall` are different constructors.** In the rendered text the
two hypotheses are unrelated: the ih is `gih(a, …, VNil)` — a *local* the
emitted `match` binds, with the recursion argument dropped — and a foreign call
is `add_gen_conv_in_mul(a, b, VNil)`, an application of a Ψ theorem whose
spelling depends on the callee's own recursion index. Both are name-side, so
the datatype could have carried one constructor and let the readback decide by
`c == 0`. It does not, deliberately: *which certificate discharges a call* is
the single most interesting decision the fold makes (it is the difference
between an induction and a lie), and putting it in a constructor is what makes
it perturbable in one library edit (§8) and readable in the file's own `refl`
pins. The readback then only *renders* the choice; it never re-derives it.

**`CertOut`'s two cases** are the shape of an invariant, not of an `Ir`:
`CPlain` is a straight-line body (`emit_invariant`'s `FnIrKind::Plain` arm),
`CRec` is the induction over the scrutinized parameter, whose two arms are
proved separately — so a `CRec` carries two whole `CMatch` certificates, one
per constructor tag, because the emitted proof applies `letmatch_conv` *inside
each arm of the induction* rather than once.

**Declining is `CStuck`, and it is recognized at the rim.** The first cut
propagated stuckness through smart constructors, so that a stuck node anywhere
collapsed the whole answer in-language; that cost six `Cert` eliminations (~90
CPU-seconds of the 163 above) and bought nothing the readback does not do
anyway — it reads the whole certificate, and a `CStuck` in it is an `Err`. So
the fold *places* the decline, the readback *recognizes* it, and the reason is
one sentence at the rim, exactly as `TNo`'s and `SigNo`'s are
(`run_transcriber`, `run_sig_checker`).

**What is deliberately absent.** No fuel, no `Converges`, no `Prog`, no `Val`:
a `Cert` mentions nothing the kit's *statements* mention, only what its
*applications* spell. That is what keeps it a first-order description of a
chain of applications rather than a half-built proof.

## 3. The split: structure in the library, names in Rust

The rule, stated once: **the library computes with slots, tags and sub-IRs; Rust
supplies every identifier.** The transcriber round settled the same question
the same way (`docs/certgen-transcriber-in-language-design.md` §6 step 5:
`base_specs`/`chain_from_rir` derive the spec expressions at readback because
"the walker has no names to hand over"), and the reason is unchanged: Ψ carries
bodies, not the identifiers they were written with.

Concretely, what the readback supplies and the library cannot:

| the emitted argument | example | why Rust |
| --- | --- | --- |
| the program | `mul_gen_prog()` | a generated *name*, minted by the emitters. |
| the environment `env` | `VCons(embed_nat(a), VCons(embed_nat(gk), tail))` | built from **spec expressions** — source parameter names, the emitted `gk`/`gz`/`tail` binders, and applications of the *source* function. |
| the goals `vs`, `ws`, `fs`, `cargs` | `VCons(embed_nat(mul(a, gk)), VNil)` | same: spec expressions. |
| the ih application | `gih(a, VNil)` | the binder `gih` is one the emitted proof text binds (`RESERVED`, l. 134). |
| a foreign certificate | `add_gen_conv_in_mul(a, gk, VNil)` | the conv-name convention (l. 602) and the callee's own recursion index. |
| `letmatch_conv`'s `arms` | `Arm(mul_gen_arm_zero(), Arm(mul_gen_arm_succ(), NoArm))` | the arms are spelled by *generated fn name*, not as the `Ir` value they equal. This is the one place where a structural argument is nevertheless a name. |
| closure indices | `LetCall(1, …)` inside a `rest` | the walker numbers callees in its own coordinate system (0 = self, foreign tags verbatim — `lib/certgen/certgen_code.hthr` convention 3); the program closure is computed downstream, from names. |

And what the library owns, which is everything else: which lemma applies at
each instruction, the order of the chain (which is the `rest` argument, §2),
each instruction's `tag` and `args`, the arm split and its constructor tags,
the rebinding continuation's shape, the ih-versus-foreign routing, and every
decline.

**Spec expressions are derived, not carried — and now in exactly one place.**
Before this round the derivation lived in `chain_from_rir`, which
stored a `spec: String` on every `Instr` and a `ret_spec` on every `Chain` for
`conv_of_chain` to read. The renderer now derives them itself as it walks the
`Cert`, by the same two rules (`Zero`/`Succ(x)` for a constructor, `f(…)` for a
call, parameters and `gk` at the base), so those three fields are **deleted**
from the model: one derivation, at the rim, is the whole naming story. The
model keeps only structure (`dists`, `tag`, the callee's *name*), which the
chain renderer, the closure computation and the fixture evaluator consume.

**The environment's evolution is structure, and it is in the library** — as the
`Cert` chain's shape: every `CCon`/`CIh`/`CCall` binds exactly one slot, so the
readback's env stack is a mechanical consequence of the constructors it walks,
not a decision it makes. What Rust adds to each pushed slot is its *name*.

## 4. The fold

`lib/certgen/certgen_cert.hthr`, ordinary program-layer Heather over `lib/certgen/ir_v1.hthr`'s
declarations prefix (`Ir`, `Refs` and `pick_arm` come from there — the file
imports nothing and redeclares nothing, exactly as `lib/certgen/certgen_code.hthr`
does).

```heather
fn cert_chain(ir: Ir, ih: Ihp) -> Cert       -- one straight-line region
fn cert_rebind(after: Ir) -> Cert            -- the root match's continuation
fn cert_arms(scrut: Nat, arms: Ir, after: Ir) -> CertOut
fn cert_body(ir: Ir) -> CertOut              -- the entry point
```

`Ihp` (`IhNo`/`IhYes`) is the *availability of the induction hypothesis*, which
is a property of the position and not of the instruction: the `Succ` arm of the
root match has one, the `Zero` arm and a non-recursive body do not. So
`cert_chain(ir, IhNo)` meeting `LetCall(0, …)` — the walker's self-call —
declines, and that is the in-language home of two Rust checks that used to be
only `fn_ir_from_rir`'s ("a self-call in the Zero arm cannot be structural"; "a
self-call outside a match is outside the fragment"). Those two survive in Rust
as well, because the model's fixture evaluator would recurse forever on a
zero-arm self-call and must not be handed one.

`cert_body` recognizes the two body shapes the fragment has: a root
`LetMatch(scrut, arms, after)` becomes `CRec` with one `CMatch` per constructor
tag, and anything else is `CPlain(cert_chain(ir, IhNo))`.

**The arms are selected with the library's own `pick_arm`**, not by
destructuring the arm chain. `letmatch_conv`'s `ha` hypothesis is *stated*
against `pick_arm(arms)(tag)`, so choosing the arm the same way makes the fold
and the lemma agree by construction rather than by a comment; an arm chain too
short answers `NoArm`, which `cert_chain` declines; and a chain too long is not
a decline at all, because a `Nat` induction has two cases and a third arm is
unreachable from either. (The Rust model still refuses a non-two-arm match,
which is where that shape check remains.)

**Termination** is the ordinary structural one: `cert_chain` recurses on the
`rest` field of the instruction it matched, which is how every `Ir`-consuming
function in `lib/certgen/ir_v1.hthr` is written.

## 5. Invocation: no slot, an ordinary application

**Decision: the fold is reached as a plain global application, not through an
analyzer slot.** The registration seam exists to route *layer-m* templates and
analyzers whose contract the surface cannot otherwise state
(`docs/meta-def-registration-design.md` §11); `cert_body` is a program-layer
`fn` of one `Ir` argument, so there is nothing for a slot to buy. Adding one
would cost a vocabulary entry, an expected signature, and — decisively — a
`meta fn` shell, which is a 52-branch `rec_ga` check at ~9 s and the stack rail
of `docs/certgen-transcriber-in-language-design.md` §8. The spike's §6 advice
("reuse the seams; do not invent a registration kind unless forced") is
honoured by *not* using this one.

What the hook does instead, in `run_cert_fold`, is the same steps the
transcriber's hook takes, minus the modal ones:

1. **Reference.** Resolve `cert_body` in Ψ by name and build `u^δ` for it — the
   `GlobalVar(|Ψ| - 1 - abs)` construction with the empty-context delayed
   substitution that `resolve.rs`'s `derived_ref` makes for any written name,
   and the matching `shift_global(|Ψ| - abs)` on its type that
   `Elaborator::fn_type_code` (lib.rs 1311–1318) makes for a reflected one. No
   rescoping table is needed and none is kept: unlike a `MetaDef`, a Ψ global
   *is* Ψ-resident, which is the staleness class the transcriber round had to
   fix by hand (§6 step 5b there) and this path simply does not have.
2. **Apply.** One `Term::App`, its annotations peeled off the global's own Π
   type, to the `Ir` **term** the transcriber's evaluation already produced. The
   argument is not re-elaborated and not rebuilt: it is the very subterm the
   readback of `TYes` looked at, so the fold sees exactly the value the
   transcriber emitted.
3. **Evaluate and read back**, spine-directed, through the *same* `Reader` with
   the same `FUEL` and the same `READ_BUDGET`. Only what is inspected is
   reduced (CLAUDE.md's memory discipline), and a value deeper than the budget
   declines rather than recursing — the lesson §8 of the transcriber design
   paid for once already.

A file that never declares `cert_body` declines with that sentence, exactly as
a file that never declares the transcriber does.

## 6. The readback, and what stays Rust

`RCert`/`RCertOut` mirror the library types with the callee **tags already
resolved to names** — the one conversion the readback owns, per convention 1 of
the library file — and with `CStuck` turned into the decline. `Reader::cert`
carries the same `READ_BUDGET` and the same fuel as every other read here, and
declines any shape it has no case for rather than mis-reading one: the
literalness the existing `Reader` block argues for, inherited unchanged.

`render_cert` then replaces `conv_of_chain`, one match arm per `Cert`
constructor, with the format strings moved over **verbatim** — byte-identity to
the previous output is the acceptance bar, and the cheapest way to hold it is
not to retype the strings. Two small walks sit beside it: `ProofCx::cert_ir`,
which prints a sub-certificate as the `Ir` the kit lemma's `rest` argument
names (§2), and `ProofCx::ret_spec`, which derives the spec of the value a
chain returns — `CMatch` needs it *before* its arm is rendered, as the arm's
`ws` and as the goal the arm is proved against, and it is what
`Chain::ret_spec` used to carry.

Staying in Rust, and named honestly rather than fudged:

- **every spelling** (§3's table), including `letmatch_conv`'s `arms` argument,
  which is a structural argument spelled by generated fn name. The library
  computes the arm split; it cannot know what the arms will be *called*.
- **the closure**, its prefix property, and the tag→index renumbering: the
  program is a fact about the set of functions generated so far, which lives in
  `GenCtx` and not in any one body.
- **`emit_invariant`'s scaffolding** — the theorem's binders, the induction's
  `match … as λ gz => …` motive, and the `Zero`/`Succ(gk)` spelling of the
  scrutinee. That text is the *statement*, not the fold, and its every token is
  a name.
- **the fixture evaluator, the IR emission and the instance** — untouched, as
  they were in the transcriber round.

## 7. Cost, and which file

`lib/certgen/certgen_cert.hthr`, a file of its own, on two criteria:

- **Elaboration cost per test session.** The new code is inductives and `fn`s —
  no `match code`, so no `rec_ga` gate and no `RUST_MIN_STACK` exposure. Putting
  it in `lib/certgen/certgen_code.hthr` would tie it to that file's two shells, which
  are the expensive thing every certgen test already pays for once and which the
  perturbation controls have to keep to one per thread
  (`crates/elab/tests/certgen.rs` header, `issues/certgen-harness-cost.md`).
  A separate file keeps the fold's own perturbation control cheap and keeps the
  option of a *fold-only* test that pays for no shell at all.
- **Subject matter.** `lib/certgen/certgen_code.hthr` is the fragment's *definition* —
  which signatures and bodies transcribe. This file is downstream of that
  question entirely: it consumes an `Ir` and knows nothing about code, markers
  or layers. One artifact, one file, is the same rule the transcriber round
  applied when it put its shell beside its helpers.

Two costs were measured, both because they threatened the rail rather than out
of curiosity (CLAUDE.md — this round adds no inference route to a hot path, so
there is no perf protocol): the file's own elaboration, §2's 163 s → 1.0 s
finding, and the **fold's evaluation**, ~3.5 CPU-seconds per generated
function (spine-directed WHNF of `cert_body` over the `Ir`, plus the readback,
on the same lazily-re-reduced spine the transcriber's readback walks). The
second is inherent to the architecture — it is the price of the decision living
in a library — and it lands on `crates/elab/tests/certgen.rs`'s budget as
roughly +30 s across its two generating tests. `issues/certgen-harness-cost.md`
is where a lever would go — and where this round had to *pull* one. Those
~30 s pushed `crates/elab/tests/certgen.rs` past `scripts/test`'s **300-second
`ulimit -t`**, which is per *process*: the binary's fourth test was killed
mid-run, and the suite reported a truncated total rather than a failure, which
is the shape that mis-read costs a session if nobody knows it. The lever taken
is the free one — `ulimit -t` is per binary, and every perturbation control
builds its own elaborator anyway, so the two perturbed-library controls moved
to `crates/elab/tests/certgen_controls.rs` and the fold's to
`crates/elab/tests/certgen_cert.rs`, leaving `certgen.rs` with the two
positives. Nothing was made cheaper; the work was redistributed across three
rails. (The 8 MiB `RUST_MIN_STACK` rail is a different limit — per *thread* —
and still says one `match code` shell per test.)

## 8. Test plan

Across the axes of `docs/testing-generated-terms.md`, and with the perturbation
story first because it is the round's point:

1. **The library states its own acceptance**, as `lib/certgen/certgen_code.hthr` does:
   `refl` theorems giving the `Cert` of `dbl`'s and `add`'s IRs (the recursive
   shape, the ih routed to `CIh`), of `mul`'s (the *foreign* call routed to
   `CCall` beside a `CIh` — the one fixture where the two-constructor split is
   observable), and of `seven`'s (a plain chain, no match, no ih), plus the
   declines: a self-call in the `Zero` arm, a self-call with no match at all, a
   nested `LetMatch`, a non-rebinding continuation, a three-arm match.
2. **Byte-identity**, which is the acceptance bar: the five existing emissions
   (`add`, `dbl`, `seven`, `third3`, `mul`) are elaborated and kernel-checked
   unchanged in `emissions_check_and_controls`, and the `IR_*` literals and
   every mutation control there stay green untouched. Checked directly as well,
   once, during the round: the concatenated text of all five emissions, dumped
   before and after the port, `diff`s empty — including `mul`'s two invariants,
   the cross-function case where the callee's proof is re-derived inside the
   caller's program.
3. **A perturbed fold is refused by the kernel** — the control this round
   exists to add, in the style of
   `a_perturbed_transcriber_is_refused_by_the_kernel`, and in a **binary of its
   own** (`crates/elab/tests/certgen_cert.rs`): one shell per thread for the
   stack rail, and its own `ulimit -t` for the kit it needs (§7). One edit to
   `lib/certgen/certgen_cert.hthr` — `cert_rebind` rebinding the arm's result at slot 1
   — and the emission must *fail to check* rather than prove anything. It
   arrives as two controls for the same reason the transcriber's did: the
   file's own theorems refuse the mutation at its declaration, and with those
   stripped the emitted invariant is the only thing on trial.

   The mutation is chosen to be one that **renders**. A fold that emits
   something structurally impossible (a `Succ` instruction with no argument, a
   callee tag with no name) is refused one step earlier, by the readback — a
   decline, and a weaker control. The slot perturbation produces a complete,
   plausible, false certificate, which is the shape a real fold bug has: it is
   refused because `letmatch_conv` at the wrong continuation proves a
   `Converges` about a different `Ir` than `dbl_gen_body()`.
4. **The open/neutral axis** is already covered by the shape of the artifact:
   every invariant is proved for *open* parameters (`a`, `b`, `tail`), and the
   `mul` fixture consumes a callee certificate at an open argument.
5. **A negative control on the invocation**: a session that elaborates the
   transcriber but not the fold declines by naming `cert_body`, rather than
   emitting a body-only file. It rides in the same test as (3), before the
   mutated copy is elaborated into that session — which is the cheapest place
   in the suite for it to happen.

## 8.1 The perturbability claim, tested — 2026-08-12

Round A's value proposition was "a new fragment feature should be absorbable as
constructor-level edits to `Cert`, in a library file a test can perturb". The
first fragment feature after it — non-`Nat` result embeddings
(`docs/certgen-non-nat-embeddings-design.md`) — is the test, and the answer is
**stronger than the claim**: `lib/certgen/certgen_cert.hthr` needed *no* edits at all.

Why, stated so the next feature can predict its own answer: a `Cert` describes
a chain of kit applications over an `Ir`, and the widening changed neither the
`Ir`'s shape nor the induction. A constructor tag was already a `Nat` field of
`CCon` (tags 0/1 were never `Zero`/`Succ` *here* — that reading lives in the
renderer, `ResTy::ctor_spec`), and the scrutinized parameter is still a `Nat`,
so `CRec`'s two arms are still the two arms. What moved instead was the
**renderer's** notion of a slot: an environment entry now carries *how it is
embedded* beside its spec expression, decided by position rather than by
inference.

The prediction that follows: the first feature that *will* touch `Cert` is
tier-1 source types, because an induction over `T` rather than over `Nat` is a
different `CertOut` — and that one is a constructor-level edit, exactly as this
section's claim describes.

**The prediction landed, 2026-08-14** (`docs/certgen-tier1-source-types-design.md`):
tier-1 source types touched the certificate expression, and as predicted it
was a constructor-level edit — on `CertOut` exactly: `CRecW(scrut, arms)`
over a new `CArms` list, one `CMatch` per constructor, plus the `kids`-mask
decode that gives each arm its `Ihp`. `Cert` itself needed **nothing**: a
`CMatch` already carried an arbitrary `ctag`, and *which child* an ih is
about is derivable from the gathered recursion-slot reference, so `CIh`
gained no field. Three features, three verdicts, all §8.1's: two absorbed
untouched, the third a constructor-level edit at the one place the shape of
the induction lives.

**Tested a fourth time, 2026-08-14** (`docs/certgen-tier0-params-design.md`):
tier-0 **parameters** — a `match` over a `Term::Case`-lowered enumeration
parameter — needed **zero** edits again: `cert_body_w` at the all-childless
`kids` mask (0) *is* the tier-0 certificate, every arm `IhNo`, one `CMatch`
per constructor. The tier-1 constructor-level edit turned out to be the last
one the parameter position needed; the running score is five features, one
`CertOut` edit.

**Tested a second time, 2026-08-13** (`docs/certgen-ctor-fields-design.md`):
constructor **fields** at the result type were implemented whole — walker,
signature checker, rim, end-to-end kernel-checked instance — and
`lib/certgen/certgen_cert.hthr` again needed **zero** edits, verified on the
implementation rather than assumed. Same reason, one step further along: a
`CCon`'s arguments are a `Refs`, so the fold is already field-count-agnostic,
and the induction is still over the scrutinized `Nat`. What moved was again the
renderer's notion of a slot — now a *positional rule* deciding each temporary's
type (that doc's §5) rather than a single result type for all of them. The
tier-1 prediction above stands, and is now the only unfalsified half of it: the
feature was deferred on cost, not on `Cert`.

## 9. Corrections to the documents this round touches

Recorded here; the coordinator owns the issue edits.

1. `docs/certgen-transcriber-in-language-design.md` §5's table, row 3
   ("Certificate emission — Rust — blocked, and by a calculus fact"): the row is
   **split**. What is blocked is the *statement* (a code type over meta-level
   data — the spike's item (d), route 3); the fold's *structure* was never
   blocked and is in-language as of this round. The two futures that section
   names are unaffected.
2. `docs/certgen-transcriber-in-language-design.md` §6 step 5 — "the
   derivation lands in the readback path only (`chain_from_rir`)" — is
   superseded: the spec derivation is the *certificate renderer's* now
   (`render_cert`), and `chain_from_rir` carries no strings at all. The reason
   given there (the walker has no names) is unchanged and is why the split
   exists at all; only the address moved, and it moved so that one walk
   derives each name once.
3. `docs/certgen-emission-route1-spike.md` §7 item 1 calls Round A "the
   certificate-expression datatype **and its renderer**, in `lib/`". The
   renderer stays in Rust and only the datatype and the fold move; §3 above is
   why, and the memo's own §5 already said the argument spellings were the hard
   part. The round's value — "the heuristic becomes a library file a test can
   perturb" — is unaffected, because the heuristic is the fold, not the
   printer.
