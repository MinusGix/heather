# Re-homing the certifying generator's transcriber into the language

Design sketch for the migration step named by `issues/generators-in-the-language.md`
(2026-08-02 verdict, migration order) and staged as item 4 of
`docs/certifying-generator-design.md` §8: the certifying generator's *fragment
transcriber* stops being Rust that walks a surface AST and becomes a layer-m
function that walks **code**. Round pattern as usual: this document first, the
implementing round against §10's acceptance list.

The predecessor is `docs/in-language-map-design.md` — the **quotation** stage
(`meta fn`, `code { … }`, `$`-splices, the elaborator-held `MetaPrograms` registry,
the evaluation hook). This round opens the **analysis** stage: the first
surface use of `elim^Trm`, the kernel's code recursor.

The principle inherited from `issues/certifying-generator.md`, protected by
every decision below: **the generator is untrusted.** Everything it emits is
kernel-checked, so it may be heuristic, incomplete, and wrong; a bad emission
is a refused certificate, never an unsound theorem. Moving it into the
language does not change that — it *widens* it, because now the heuristic part
is a library file a test can perturb.

---

## 1. The finding that reshapes the round: variables are opaque

The 2026-08-02 expressiveness verdict measured this round's feasibility as
"the v1 fragment coincides almost exactly with what `elim^Trm` can walk —
`elim_N` + constructors + variables, no global references". Walking is right.
**Distinguishing is not**, and it is the one thing transcription is made of.

Checked against the kernel and the book rather than the log:

- `rec.rs:651` (`tm_var`): the variable branch's telescope is
  `(ℓ, g, U_T : Typ_p(g, ℓ), u_x : Trm_v(g ⊢ U_T^id @ ℓ))` — a universe, a
  context, a *type* global and a **layer-v global standing for the variable**.
  The branch body is one term, valid for every variable at once.
- `reduce.rs:1115` (`beta_elim_tm`): a `Term::Var(x)` scrutinee fires that
  branch with `GlobalEntry::Tm(Var(x))` substituted for `u_x`. The variable is
  *passed*, so it can be re-boxed and re-emitted — but nothing at layer m can
  observe which variable it is: there is no code equality (verdict blocker 3),
  and `U_T` is a layer-p global the branch cannot case on either.
- Ch. 04 says so directly (ll. 1204–1207, and the β rule at 1533–1542): "the
  type of the variable is captured by `U_T` … it is obtained externally";
  "`u_x` can only receive a variable as it is typed at layer v".

Transcription is exactly the map from a variable *occurrence* to an
environment *slot*. So a pure in-language walk of the fn's code cannot produce
a single `Ref`. This is not the "no context computation" blocker restated —
that one (verdict blocker 4) says you cannot build code under a computed
number of binders; this one says you cannot read a de Bruijn index out of
code at all, at any fixed number of binders.

**Decision: the marker convention.** The elaborator hands the transcriber the
fn's body with every bound-variable *occurrence* replaced by a closed marker
term carrying the binder's de Bruijn **level**:

    mark(n)  :=  (λ (x : Nat). x) ⌜n⌝          -- a β-redex at Nat

with levels assigned in binder birth order — parameters `0 … k-1` (peeled off
the declaration's Lam spine), then the eliminator's field `k` and its
induction hypothesis `k+1`. The result is **closed** code: it type-checks in
the empty context, and no `Var` node survives outside the markers themselves.

Why this is a substitution and not an analysis: the pass is a mechanical de
Bruijn→level renaming. It consults no fragment knowledge, no types beyond
"this variable is a `Nat`", and no declaration table; it is the same
information in a different coordinate system. What stays Rust is *scope
resolution*, and it stays there for a stated kernel reason, not for
convenience.

Why a β-redex and not a bare numeral: the fragment's own source contains
numerals (`Num(n)` compiles to a `Succ` spine), so a numeral marker would be
ambiguous. Code does not compute (`Layer::computes` is `Prog | Meta` only,
`layer.rs:30`), so the redex is stable syntax, and `beta_elim_tm` dispatches
on the *head constructor* of the payload — an `App` fires `tm_app`, never β.
The fragment contains no other application (cross-function calls are global
references, which are neutral — §3), so "application with an identity-lambda
head" is unambiguous *within the fragment*, and everything outside the
fragment declines.

**The seam closes later, and the doc says where.** Marking is expressible
in-language the day two things exist: surface delayed substitution
(`$u[x := t]`, `docs/sketches/surface-v0.md` finding 2, deferred by the map
round's §8) to mark a branch's sub-code, and a meta-layer re-entry (fuel-driven
recursion at layer m) to re-walk the marked sub-code, because a branch's
`box (u^δ)` is neutral until its global is concrete (`reduce.rs:2206`). Both
are real rounds; neither is this one.

## 2. Where the pieces stand (surveyed 2026-08-11)

- **The recursor is complete, monolithic, and reachable only from Rust.**
  `ElimCodeTm` (typing.rs:1702) requires `Layer::Meta`, a scrutinee of type
  `Code(Δ ⊢ T)` — an ordinary Π-bound local, exactly what the map round's
  correction (1) predicted code arguments to be — and `rec_ga` (typing.rs:1742)
  checking **both motives and all 52 branches** at their instantiated types.
  No elaborator path emits it.
- **52, not 37.** `rec.rs:208` is the authority: ch. 04's 13+9 branches plus
  the Id/Σ/Unit/Empty/Sum/W/Vec/Fin/Wf/sEq extensions. Every log and sketch
  that says "37 branches" (`issues/certifying-generator.md` 2026-08-02,
  `docs/sketches/surface-v0.md` §6) is quoting the paper, not the kernel.
- **The branch table stays Rust under any plan** — it recurses over the
  *signature* (three binder namespaces, above-`k` shifts) and is consumed by
  both `conv` and `typing`. A surface `match code` is a *client* of that
  table, keyed to it by branch name; it never restates it.
- **Global references are neutral, and that is the fragment boundary.**
  `is_neutral_term` (reduce.rs:2206): `ElimCodeTm` on `box (u^δ)` is neutral.
  So any call to another function inside the analyzed body stops the walk —
  which is exactly v1's fragment (no cross-function calls) and exactly why
  v2's cross-function transcription **cannot** move in-language yet.
- **Recursion arrives as an eliminator, and the self-call as a variable.**
  `elab_self_call` (lib.rs:3908ff): "the recursive result is definitionally
  the arm's induction hypothesis, so the lowering is a variable — no motive
  surgery, no fixpoint." So a fragment fn's code is `Lam … Lam (ElimNat …)`
  with `Zero`/`Succ`/variables inside, and the walker inherits termination
  from the eliminator instead of re-deriving it (Rust's "self-call is not
  structural" decline becomes vacuous on this path).
- **Ψ can be referenced from layer m.** `GlobalTm`/`GlobalTy` enforce
  `i' ≤ i` (typing.rs:596, 756) with the binding invariant `v/c` for terms and
  `c/p` for types, so a layer-m term may name the library's inductives and
  call its functions; δ-unfolding of a code-layer body is what the hook's
  `whnf_term_delta` already does for `map_code`.
- **No `CodeTy` and no `LetBoxTy` are needed.** The certgen issue's 2026-08-02
  entry expects the transcriber's inputs to "arrive as `CodeTy` locals
  letboxed into recursors, the stage `TyCode` was reserved for". For the
  Nat-only v1 fragment that is not so: the analyzed code's type is the closed
  type `Nat`, so the recursor's type annotation is concrete and the input is
  an ordinary `Code(g ⊢ Nat)` local. `TyCode` enters with §8 item 2 (non-Nat
  embeddings), not here.
- **The artifact being re-homed** is `crates/elab/src/certgen.rs`'s
  `Compiler` (ll. 240–429): 190 lines of AST walk producing `FnIr`. Everything
  after it — chain rendering, the ∃-kit fold, the fixture evaluator, the
  instance — consumes `FnIr` and nothing else.

## 3. The analysis surface: the minimal honest `match code`

`docs/sketches/surface-v0.md` §6 designed `match code` with two default-arm
flavors. This round adopts **one**, and the choice makes the 52-branch problem
disappear:

> **Decision: constant motives only.** The `match code` of this slice
> annotates one result type for the term motive and one for the type motive;
> neither may mention the scrutinee, its context, its type or its level.

With a constant motive every branch has the *same* expected type, so the
mandatory `_ => expr` default arm can fill all 45 unwritten branches with one
term — and every recursive-result binder in every arm also has that same type,
including the ones that live at *extended* contexts (a `Succ` arm's body, an
`elim_Nat` step arm). A dependent motive would need those results strengthened
back down to the ambient context, which the calculus does not offer without
delayed substitution. Constancy is what buys the round.

The slice, stated as restrictions:

1. **One motive, used for both.** ~~Term motive `TA`, type motive `Unit`.~~
   *Corrected in implementation:* the surface writes **one** type and the
   elaborator uses it for the term motive and the type motive alike, so the
   eight `ty_*` branches and the type-motive recursive results (`lam`'s
   domain, `elim_nat`'s motive) are filled by the same default arm and no
   `Unit` spelling is needed at all. This round analyses terms; it does not
   analyse types, and one motive says that as clearly as two did.
2. **An arm names only its recursive-result binders.** Sub-code binders
   (surface-v0's `$n` splice-patterns) are *not* in the slice: no arm of this
   walker mentions its sub-code, because everything it needs is computed
   bottom-up. Writing `$n` is a diagnostic naming this section.
3. **Universe binders are implicit and unmentionable.** Arms like `tm_lam`
   push universe variables the surface cannot spell (there are no level
   variables — `issues/implicit-level-polymorphism.md`); with a constant
   motive no arm body needs them, so the elaborator binds them anonymously and
   an arm body that would need one cannot be written at all.
4. **Arms are keyed by `rec.rs`'s branch names.** ~~Only the six this round
   needs are writable.~~ *Corrected in implementation:* **every** name in the
   kernel's table is writable, and the six the fragment needs (`tm_zero`,
   `tm_succ`, `tm_var`, `tm_lam`, `tm_app`, `tm_elim_nat`) merely lead the
   unknown-name diagnostic. A whitelist would have been a second table beside
   `rec::BRANCH_NAMES`, which is exactly what §2 says the surface must not
   build; the kernel's own list is the authority, and an arm whose branch this
   round has no use for is simply an arm nobody writes.
5. **`match code` is layer-m machinery**, so it appears only in a `meta fn`
   body — the map round's answer to surface-v0's open "inferred vs declared"
   question, kept.

Spelling, **as landed** — arm names are the kernel's own
(`heather_kernel::rec::BRANCH_NAMES`, read at elaboration rather than
restated), and each arm binds that branch's recursive results positionally:

```heather
meta fn transcribe(g: Ctx, arity: Nat, body: Code(g |- Nat))
    for certgen.transcribe -> TOut
{
    ta_finish(arity, match code body as TA {
        tm_zero                    => ta_zero(),
        tm_succ(t)                 => ta_succ(t),
        tm_var                     => ta_var(),
        tm_lam(dom, b)             => ta_lam(dom, b),
        tm_app(dom, cod, hd, arg)  => ta_app(arity, hd, arg),
        tm_elim_nat(m, z, s, sc)   => ta_elim(arity, z, s, sc),
        _                          => ta_stuck(),
    })
}
```

Two corrections the implementation forced. The arm names carry their `tm_`
prefix, because keying them to the kernel table is what keeps the surface from
drifting when a branch's telescope changes — a stripped alias would be a second
table. And the whole `match code` sits *inside a call*: the walker's answer is
a `TA`, and `ta_finish` is what turns it into the `TOut` the slot's signature
promises.

Note what is *not* here: no quotes, no splices, no letbox, no `Ctx`
computation, no recursion at layer m. The whole meta fn is one elimination
whose arms are calls.

## 4. The artifact: `lib/certgen_code.hthr`

**Decision: the analysis logic is ordinary program-layer Heather; the modal
layer contributes only the traversal.** (This section's artifact is *not
writable in the meta slice as it stands* — §9.1 records the refutation, why the
code-returning alternative fails, and the two ways out.) The `ta_*` helpers above are ordinary
`fn`s over ordinary inductives, and the `meta fn` is a seven-line shell. Three
reasons, in force order:

1. It keeps the meta slice minimal. Layer m needs to support *calls and
   variables* and nothing else — no `match` at layer m, no meta recursion, no
   annotated `let` (so `issues/meta-body-statement-loop.md` and
   `issues/let-inside-quotation.md` are untouched by this round: neither
   constrains it, neither is consumed by it).
2. It makes the analysis testable as ordinary code — and, later, *provable*:
   the helpers are exactly the functions a verified-transcriber round would
   state lemmas about.
3. It puts the whole fragment definition in one readable file, which is the
   thesis' claim (a generator is a library, not a compiler internal).

The data, in the shape the composition wants — instruction prefixes with
**level** references, converted to distances once, at rendering:

```heather
inductive PRef  { RBase(lvl: Nat), RLocal(j: Nat) }     // a binder, or my j-th instruction
inductive PRefs { QNil, QCons(r: PRef, next: PRefs) }
inductive Pre   { PEnd,
                  PCon(tag: Nat, args: PRefs, rest: Pre),
                  PCall(callee: Nat, args: PRefs, rest: Pre) }
inductive TA    { TStuck, TNum(n: Nat), TVarLeaf, TIdLam,
                  TExp(pre: Pre, res: PRef, len: Nat) }
```

- `TNum` is a numeral spine (`Zero`, `Succ` of a numeral) — the marker's
  payload, and also a source literal;
- `TVarLeaf`/`TIdLam` exist only to recognize a marker: a `var` is a leaf, a
  `lam` whose body is a leaf is the identity, an `app` of the identity to a
  `TNum(i)` is `TExp(PEnd, RBase(i), 0)` — an occurrence of binder `i`;
- `TExp` is an expression compiled to a prefix of instructions plus the
  reference its value lands at. Composition (`ta_succ`, and the arm assembly)
  concatenates prefixes and shifts `RLocal` indices — an ordinary recursive
  function, which is why the round needs no arithmetic at layer m beyond what
  the library already has.
- `TStuck` is the decline, and it propagates: every helper returns `TStuck`
  when any input is `TStuck`. Declining is total, not partial.

Two shapes the helpers must get right, both inherited from the Rust model and
both re-derivable from it:

- **The induction hypothesis.** An occurrence of binder `arity+1` is the ih.
  It emits `PCall(0, <ih-placeholder>)` on the spot; the enclosing `elim_nat`
  assembly rewrites the placeholder into the real argument references (the
  parameters, with the field at the recursion position) — a same-length
  rewrite, so no index moves. Binder `arity` is the field; a level `≥ arity+2`
  is a nested eliminator, i.e. outside the fragment: `TStuck`.
- **The root.** The eliminator is accepted **only at the body's root** (the
  fragment's own "at most one match" rule): `ta_elim` renders both arms and
  the `LetMatch(scrut, Arm(zero, Arm(succ, NoArm)), Ret(RCons(0, RNil)))`
  wrapper, where `scrut` comes from the scrutinee being a bare parameter
  marker (anything else declines). A plain body renders directly.

Rendering — levels to distances against the emitted layout — is one more
ordinary function, and it is the single place where the marker convention and
the IR's environment layout meet. Pin them in one comment there; a mismatch is
a non-converging IR, i.e. a refused certificate, which is what §7 is about.

**As landed** (`lib/certgen_code.hthr`, 412 lines): the data above, a dozen
`fn`s, and seven `theorem`s that are the file's own acceptance — `dbl`'s and
`add`'s transcriptions written out and checked by `refl` against exactly what
the Rust `Compiler` emits, plus three declines. Two notes worth keeping:

- The composition never concatenates two prefixes, because in this fragment it
  never has to: every node with a compiled sub-expression has exactly **one**
  (`Succ` of one argument; a self-call's arguments are markers, which compile
  to no instructions at all). So `Pre` is consed at the front and reversed once
  at rendering, and the round needs no list append and no reference shifting.
- `PSelf` replaced the design's placeholder-and-patch: the self-call's argument
  list depends on the recursion index, which only the enclosing eliminator
  knows, and since the *renderer* already receives that index there is nothing
  to patch — the instruction is expanded when it is rendered. One fewer pass,
  and no rewrite that could move an index.

Cost, measured once while wiring it up (not a perf round — CLAUDE.md — just a
rail to watch): the file elaborates in ~2 s, and the `meta fn` shell costs ~9 s
to check, which is the 52-branch `rec_ga` gate paid against a real motive plus
the analyzer registration's re-elaboration of the expected signature. The
certgen harness was already the suite's second-most expensive binary; this puts
the in-language acceptance at ~16 s on top of it.

## 5. Scope of the port: what moves, what stays, and why

The Rust generator has four phases. The split is not a matter of taste; three
of the four boundaries are forced by facts checked above.

| Phase | Home after this round | Why |
| --- | --- | --- |
| 1. Fragment check — signature | **Rust** | It is a fact about the *declaration* (arity, `Nat`-only parameters, reserved names the proof text binds), not about the code. It falls out of peeling the Lam spine before boxing. |
| 1. Fragment check — body | **in-language** | It *is* the walker's decline set (§7). Structural recursion is no longer checked at all: the eliminator carries it. |
| 2. Transcription | **in-language** | The round's point. |
| 3. Certificate emission (the ∃-kit fold) | **Rust** | Blocked, and by a calculus fact, not effort — see below. |
| 4. Fixture fuels (the mini-evaluator) | **Rust** | Could move (the library owns `eval`), but it computes a *literal* for a test fixture; moving it buys nothing this round and costs an evaluation-in-elaboration round trip. |

**Why phase 3 cannot move.** The map round's correction (1) — a code type can
be indexed only by globals, never by a local's payload — generalizes exactly to
the certificate: the emitted proof's statement is
`Converges(prog, env, body, out)` where `prog` and `body` are the transcriber's
*output*, a meta-level value. `Code(g ⊢ Converges($prog, …))` is unstatable
for the same reason `Code(g ⊢ Vec($a; $k))` was. Two futures, both real, both
elsewhere:

- **Dependent code types over meta-level data** — a kernel/theory round (ch. 04
  has no meta-layer Π over terms at all), which would also give the analysis
  stage its natural motives.
- **The fold as a lemma**: one theorem in `lib/ir_v1.hthr`, by induction over
  `Ir`, of which today's per-function kit folds are instances. That is the
  route that also retires `issues/prog-extension-lemma.md` — but note it
  changes the trust story from *certifying* to *verified*, so it is a
  departure from this issue's charter and must be argued there, not assumed
  here.

**Cross-check discipline, from the map round.** The Rust `Compiler` stays, as
the oracle: for every fixture, the in-language `Ir` and the Rust `Ir` are
compared by `conv_term` at `Layer::Prog`. Adequacy is not soundness — a wrong
transcriber yields a refused certificate, not a wrong theorem — but the
conversion check is what turns "it checks" into "it is the same program".

**Addendum, 2026-08-12 — the cross-check discipline is RETIRED**
(`issues/retire-rust-transcriber.md` stage 2). The oracle is deleted: `generate`,
`generate_forced`, `generate_inner`, `Compiler`/`compile`/`compile_arm` and the
surface fragment walk are gone from `crates/elab/src/certgen.rs`, and
`generate_in_language` is the only generator. What replaced the comparison,
per the issue's four covers: (a) `lib/certgen_code.hthr`'s own `refl` theorems
pin `add`, `dbl` and `mul` in-language, one layer below the readback; (b) the
positive fixtures in `crates/elab/tests/certgen.rs` make a silent decline a
panic; (c) each emission's exactness fixtures catch different-but-converging
output at a concrete run; (d) the kernel judges the rest. The one property with
no cover of its own — the *emitted layout*, which two independent
implementations used to agree on — is pinned as literal expected text
(`IR_ADD`, `IR_DBL`, `IR_THIRD3`, `IR_SEVEN`, `IR_MUL` in that test file), and
its sole normative statement is now `lib/certgen_code.hthr`'s
three-conventions header plus the emitters (a *fourth* convention — non-`Nat`
constructor values — was added 2026-08-12 by the non-`Nat` embeddings round). The rows of the table above stand
unchanged for phases 2–4; row 1's "signature" home became **in-language** at
the fn-signature-reflection round, and what is left in Rust is the *names*
(`surface_params`: reserved-binder collisions and implicit parameters), which
no reflected form carries. Three Rust-only declines went with the walker: a
non-structural self-call, refused earlier and harder by the elaborator; a
`Succ` arm without a self-call, which is now accepted — the eliminator carries
structural recursion, so ignoring the induction hypothesis is an ordinary
transcribable body; and a `let` in the body, which elaborates to an alias and
so was never a fact about the code at all — the analysis reads Ψ, and what Ψ
holds is transcribable.

## 6. The evaluation hook, and how output re-enters elaboration

**Decision: the emission stays surface text; the port's interface is `FnIr`.**
Nothing downstream of the `Compiler` changes. In-language, `FnIr` is obtained
by evaluating the meta fn and reading its result back.

The hook, extending the map round's:

1. **Fetch and mark.** The declaration is already in Ψ as a `Layer::Code`
   global with a body (lib.rs:1594/1864). Peel `k` `Lam`s (arity and the
   `Nat`-only signature check fall out), rename every `Var` occurrence to
   `mark(level)`, box the result. A non-`Nat` variable, or a body that is not
   a Lam spine, is an honest decline here.
2. **Apply.** `CtxApp(transcribe, ·)` — the marked payload is closed, so the
   context argument is the empty context — then `App`s for `arity` and the
   boxed body, exactly as `elab_vec_map` builds its spine.
3. **Evaluate.** Iterated δ-transparent WHNF under elaborator fuel, as
   `map_code` does — but driven **spine-directed**: WHNF to a constructor
   head, read that constructor, recurse into the fields it has. Only what is
   inspected is reduced. This matters for the memory discipline (CLAUDE.md's
   superlinear warning): no deep normalization of an encoded value.
   *(2026-08-13: the demand order is unchanged, but the evaluation under it is
   no longer the rewriter — `Reader` forces closures in the kernel's value
   domain. `docs/analyzer-evaluation-design.md` has the measurement and the
   reason; nothing about this step's contract moved.)*
4. **Read back.** `read_ta` / `read_ir`: the encoded inductive value to Rust's
   `FnIr`. New code, and the only genuinely new *plumbing* the round adds
   (there is no existing value readback; `inductive::decoded` is types only).
   It is untrusted like everything else: an unrecognized spine is a decline,
   a *mis*-read spine is a refused certificate.
5. **Reconstruct.** `FnIr`'s `spec` strings — the source expressions the proof
   text spells into environments and certificate applications — are **not**
   in the IR, and cannot be: the walker has no names. They are, however,
   *redundant* with it: a temporary's spec is determined by its instruction
   and the specs of its argument slots (`Succ(·)`, `Zero`, `f(…)`), and the
   base specs are the parameter names plus `gk`. ~~So certgen's `Instr::spec`
   becomes derived rather than carried, on both paths.~~ *Narrowed in
   implementation:* the derivation lands in the readback path only
   (`chain_from_rir`), and the Rust transcriber keeps carrying its specs. Two
   reasons: the Rust path's specs come from the *source*, where a numeral
   literal reads as `3` rather than as `Succ(Succ(Succ(Zero)))`, so the two
   are not the same string function; and rewriting a working proof emitter
   for tidiness is exactly the churn a round like this should not spend. The
   two paths are compared where it counts — the emitted IR (§5's
   cross-check) — and both emissions are checked end to end.
5b. **Rescope.** A meta definition is *elaborator-held*, so nothing rescopes it
   when Ψ grows — and a `GlobalVar` counts from the end of Ψ, so every
   declaration elaborated after the analyzer moves what its references mean.
   `MetaDef` therefore records `|Ψ|` at registration and every use site shifts
   by the growth (`MetaDef::at`). **This was a live bug, not a precaution**: the
   first `add` transcription came back as a stuck application of the wrong
   global. It never bit the map round because a pure-quotation template
   references no globals at all — which is exactly the difference between a
   template and an analyzer, and the reason it surfaced the moment arms became
   calls. The hook (`try_code_template`) now rescopes too, where it is a no-op
   today and a fix for the first template that names a library function.

6. **Route.** ~~As the map round routes `map_code`: the name is the contract,
   documented at the dispatch site.~~ **Corrected 2026-08-11 (§9.1):** routing
   by name was retired by the registration seam
   (`docs/meta-def-registration-design.md` §2 — a template declares a typed
   *slot* with a `for` clause, and an unclaimed `meta fn` is never dispatched).
   The transcriber is not slot-shaped (an analyzer has no payload Π spine), so
   its dispatch is the open question §9.1 hands back: a second registration
   kind, or an explicit invocation surface. What survives unchanged: if the
   transcriber is not available, the Rust `Compiler` runs and a file that never
   declares it behaves exactly as today.

### 6.1 How the elaborator finds the transcriber: **analyzer slots**

§9.1 handed back a question this section had answered wrongly (routing by
name, retired by the registration seam). The answer the round took, in full in
`docs/meta-def-registration-design.md`'s §11 extension and in summary here:

The seam gains a second kind of slot. An **analyzer slot** keeps everything a
template slot has — the `for family.name` clause, the closed Rust vocabulary,
declaration-time loudness, one template per slot, no soundness role — and
changes only what "has the slot's type" means. A template's contract is its
*payload's* Π spine, because that is where a template's argument order lives.
An analyzer has no payload: its arguments are its own Π binders, so its
contract is the **whole signature**, checked by conversion against an expected
signature *written in Heather* and elaborated in the declaring file's scope.

That last detail is forced by §9.1's fourth finding rather than chosen: an
inductive is inlined, not a Ψ global, so a Rust-built expected type has nothing
to reference and a Heather-written one has everything. It also gives the
diagnostic for free — a file that has not declared `TOut` fails at the `for`
clause, naming the slot.

And whole-signature convertibility buys the invoking Rust something the
template path has to work for: the Π order is *fixed*, not merely constrained,
so `run_transcriber` applies `(Γ = ·, arity, box marked)` in the slot's
canonical order and consults the template's signature for nothing but its
`CtxPi` head. `docs/meta-def-registration-design.md` §3 says the order must be
enforced somewhere the caller can rely on; this is that, with the enforcement
one step stronger.

The vocabulary gained one entry, `certgen.transcribe`, and the round gave it
one client. User-declared analyzer slots are deferred with user-declared slots
generally.

## 7. The untrusted-generator property, concretely

The Rust generator declines in five shapes and has one forced-emission honesty
control. In-language the decline set is *larger* and cheaper to state, and it
lands in three places:

- **In the walker** (`TStuck`, one value): the default arm — 46 branches
  covering every non-fragment node; an application that is not a marker; a
  lambda that is not the identity; a leaf or an identity lambda where a value
  was needed; a binder level `≥ arity+2` (nested eliminator); an eliminator
  whose scrutinee is not a bare parameter marker.
- **In the hook**: a non-Lam body or a non-`Nat` parameter (step 1); evaluation
  stuck or neutral within fuel — the map round's stuck-head risk, and the *most
  likely* real decline, because a fragment body that calls another function is
  neutral by `reduce.rs:2206` and must be reported by naming the stuck head,
  never by emitting a half-reduced term; an unreadable value spine (step 4).
- **In Rust, unchanged**: closure/prefix-property declines, reserved-name
  collisions, arity mismatches (phases 3–4).

Two of these moved, as landed. The global-reference decline is the *marker
pass*', not the walker's: the marker pass meets the global first and names it
as the neutrality it is ("`elim^Trm` is neutral on `box (u^δ)`") rather than
reporting some anonymous application — a better message from an earlier place.
And the readback gained a decline of its own, `READ_BUDGET` (§8).

Every one of them affects only *which* functions compile. And the honesty
control gets stronger, not weaker: alongside the existing `generate_forced`,
the round adds an **in-language forced transcriber** — a copy of the library
file with one deliberate defect — whose emission must fail to check rather than
prove anything. That control is the demonstration the whole architecture exists
for, and it is now a one-line library edit instead of a Rust hook. It also
turned out to be *two* controls, because the library states its own acceptance
and refuses the defect before anything downstream sees it (§10 item 6a).

## 8. What can go wrong, named in advance

- **A wrong library can drive the *reader* off a cliff, and fuel does not
  catch it.** Found by the honesty control (§10.6a): a perturbed transcriber
  produced a value whose readback overflowed the test thread's stack — not
  because anything looped, but because reduction is recursive and the reader
  followed a value deeper than 8 MiB of frames allow, with a fuel counter that
  never came close to expiring. The reader now carries its own **budget**
  (`READ_BUDGET`) and declines past it, and its fuel is the kernel's ordinary
  default rather than a bespoke larger one — a generous budget on a recursive
  reducer buys nothing but a later crash. The general lesson is the round's
  own thesis pointed at itself: the analysis input is untrusted, so *the code
  that consumes its output* has to be bounded too, not merely the code that
  produces it.
- **The marker convention is a heuristic recognizer.** A lambda whose body is a
  variable is *read as* the identity; in the fragment none other exists, but
  the walker cannot prove that. Deliberate: the kernel is the careful party. It
  is stated here so nobody later "fixes" it with a code-equality wish.
- **The layout mismatch.** Marker levels count binders in birth order; the IR's
  environment counts slots most-recent-first. They are inverses of one another
  and one place must own the conversion. Getting it wrong is a `Stuck`
  certificate, which the acceptance fixtures catch immediately — but silently
  *rendering* against the wrong base while the fixture still converges is the
  expensive shape, so the cross-check (§5) is not optional.
- **The 52-branch check cost, and its *stack*.** Every `match code` occurrence
  makes the kernel check both motives and all 52 branch telescopes once per
  meta-fn check. Two consequences, and the second was not predicted here:
  time (~9 s per shell — a rail to watch, not a perf round; levers live on
  `issues/certgen-harness-cost.md`), and **stack depth**. `scripts/test` already
  raises `RUST_MIN_STACK` to 8 MiB because the `tm_elim_wf` branch telescope
  embeds the `nth` schema; with a *library inductive* as the motive rather than
  `Nat`, those telescopes are bigger again, and a test thread that checks the
  shell more than once can overflow. The fix is to check it once per thread —
  which is also the cheaper arrangement.
- **The meta slice may need more than calls.** §4 is designed so that layer m
  needs only variables and calls. If the implementing round finds the slice
  cannot even do that, the honest move is to widen the *slice*, not to move
  logic back into Rust.

## 9. Verification items — **run 2026-08-11; results and one refutation**

Cheap, and each could refute a paragraph above (the map round was refuted
twice, which is what these sketches are for). Three confirm; item 3 splits,
and its surface half is a refutation — §9.1.

1. **Confirmed.** The elaborated bodies are exactly the shape §2 claims:

       dbl2 : λ(Nat). elimN[0](M Nat; z 0; s S(S(x0)); x0)
       add2 : λ(Nat). λ(Nat). elimN[0](M Nat; z x1; s S(x0); x0)
       seven2 : S(S(S(S(S(S(S(0)))))))

   Constant motive `Nat`, the ih a bare `Var` (`x0` in the step arm), the
   scrutinee a parameter variable, no `El` wrappers and no annotations to trip
   on. `add2`, which recurses on its **second** parameter, reads its first as
   `x1` in the base arm — the slot-map axis acceptance item 4 asks for. A
   numeral literal is a `Succ` spine, not a global, so `TNum` recognition (§4)
   is over kernel constructors.
2. **Confirmed.** Those bodies are β-normal — no `App` node occurs anywhere in
   the fragment's elaborated code — which is what makes the marker redex
   unambiguous.
3. **Split: kernel half confirmed, surface half refuted (§9.1).** The kernel
   accepts a layer-m Π over `Nat` and a layer-m λ whose body *calls a
   code-layer bodied global*, and δ-transparent WHNF unfolds it and computes at
   layer m (`twice(2)` reduces head-first to `S(S(elimN …))` — WHNF, exactly
   what spine-directed readback wants).
4. **Confirmed, and cheap**: 596 µs for one `rec_ga` check of a
   constant-motive 52-branch recursor (`Motives { Nat, Nat }`, all 52 branches
   `Zero`), so per-arm sugar costs nothing at the gate. Two facts fell out
   beside it: a boxed marker `box ((λ(x:Nat).x) 1)` **fires a branch rather
   than β-reducing** — the marker convention verified at the kernel instead of
   argued — and `scripts/test`'s `RUST_MIN_STACK=8388608` exists because a
   52-branch recursor's `tm_elim_wf` telescope is deep, so the elaborator path
   inherits that requirement.

### 9.1 The refutation: the meta slice is narrower than §3–§4 assumed

**A `meta fn` today takes only `Ctx` and `Code(g ⊢ T)` parameters, must return
`Code(g ⊢ T)`, and its body must be a quote** (`quote.rs`'s
`elab_meta_decl_inner`: "a `meta fn` parameter is `Ctx` or `Code(g |- T)` in
this slice"; "a `meta fn` returns code"). And dispatch is no longer by name:
the **registration seam** (`docs/meta-def-registration-design.md`, landed after
the map round and after this document's reading list) routes a template through
a typed *slot* claimed by a `for family.name` clause, where a slot's type is a
code template's payload Π spine — and "a `meta fn` without a `for` clause is
never dispatched, whatever it is named".

So §4's artifact — `(g: Ctx, arity: Nat, body: Code(g ⊢ Nat)) -> TA` — is not
writable in the slice as it stands, and §6's routing-by-name contradicts the
seam's central decision.

**The obvious workaround does not work, and the reason is worth keeping.** Keep
the meta fn returning code — motive `Code(g ⊢ TA)`, arms building quotes like
`code { ta_succ($sub) }`, the elaborator evaluating the resulting
*program*-layer term. That needs no widening at all, and the calculus refutes
it: the recursion results of the `lam` and `elim_nat`-step branches live at
**extended** contexts, so their type is `Code((g, x) ⊢ TA)`, and `elab_quote`
refuses a splice whose context is not the quote's ("the slice has no context
re-indexing"). §3's constant-motive decision is therefore stronger than it
looked: the motive must be not merely uniform but **context-free**, hence
ordinary data, hence the widening is unavoidable.

**A fourth finding from the same probe.** An inductive is *not* a Ψ global: in
the probe `Colour` elaborated inline as `Σ(Unit).Unit + Σ(Unit).Unit` inside
`flip`'s type, and Ψ held neither a `GlobalTy` nor a Tarski code for it.
Consequences: `TA`/`Ir` as a meta fn's parameter or result type are structural
types elaborated from the surface name (there is no global to reference), and
§6's readback peels the Sum/Σ lowering with no constructor table to key on —
`read_ir` is written against the *lowering*, which is a bigger and more
brittle piece of Rust than §6 budgeted for.

**What a round has to choose** (this document cannot settle it alone: it
crosses `docs/meta-def-registration-design.md`, which this round does not own):

- **(A) Widen the meta slice.** Program-layer types as `meta fn` parameters and
  result, and a meta body that may be an ordinary expression (calls, and
  `match code`) rather than only a quote. The kernel is ready (item 3's
  confirmed half); the work is `quote.rs`'s signature and body grammar plus a
  dispatch route for *analyzers*, which are not slot-shaped — an analyzer has
  no payload Π spine, so `slots.rs`'s `ITy` vocabulary cannot state its type.
  Either a second registration kind (analyzer slots, typed by signature rather
  than by payload) or an explicit invocation surface for the certgen harness.
- **(B) Keep the slice and move the round's boundary.** Land `match code`
  against a *code-returning* client and re-open the transcriber once the
  analyzer-registration question is answered. Cheaper; banks §1's finding; but
  it re-homes nothing.

## 10. Acceptance — **landed 2026-08-11**, with the deviations named

1. ✅ **The slice.** `match code e as T { … }` — one constant motive used for
   both, a mandatory `_ => expr` default, universe binders implicit, arms
   binding recursive results positionally, elaborating to `ElimCodeTm` and
   gated by the `Layer::Meta` check of the enclosing `meta fn`
   (`crates/syntax` for the form, `quote.rs`'s `elab_match_code` for the
   elaboration, seven diagnostics in `tests/quotation.rs`).

   *Deviation:* **all 52 branch names are writable**, not only the six the
   fragment needs. Restricting them would have meant a second table beside
   `rec::BRANCH_NAMES`, which is the one thing §2 says not to build; the
   unknown-name diagnostic leads with the six instead. Sub-code binders are
   still out, by having nowhere to be written: an arm binds recursive results
   and only those.
2. ✅ **The artifact.** `lib/certgen_code.hthr`: the `TA`/`Pre`/`PRef`/`PRefs`/
   `TOut` data, the `ta_*` helpers and their renderer as ordinary `fn`s, seven
   `theorem`s stating the file's own acceptance (`dbl` and `add` transcribed,
   checked by `refl` against the Rust emitter's output, plus three declines),
   and the `transcribe` shell claiming `certgen.transcribe`. The shell lives in
   the *same* file as the helpers, against §4's sketch — one artifact, one
   file, and the header can state the two conventions once.
3. ✅ **The hook.** The marker pass, the application spine in the slot's
   canonical order, spine-directed evaluation, the tier-0/tier-1 readback into
   `FnIr`, and routing through the analyzer slot (§6.1). Two changes: the
   derived `spec` strings are the readback path's only (§6 step 5), and the
   round found and fixed a live staleness bug in elaborator-held meta
   definitions (§6 step 5b).
4. ✅ **Positives, across the axes of `docs/testing-generated-terms.md`:**
   `seven` (non-recursive, literal-only body), `dbl` (1-ary recursive, a `Succ`
   arm nesting two constructors around the ih), `add` (2-ary, recursion on the
   *second* parameter — the slot-map axis — with a `Zero` arm that is a bare
   parameter and no instructions) and `third3` (3-ary). `seven`'s emission is
   checked end to end in the expensive test; the other three emit *byte-identical
   files* to the Rust path, which the cheap test asserts and the existing
   acceptance already checks end to end.
5. ✅ **The cross-check**, sharper than designed. ~~`conv_term` at
   `Layer::Prog` between the two `Ir`s.~~ The two transcribers are compared by
   **equality of the emitted text**: the model is all the emitters see, so an
   equal IR and equal parameter names make an equal file. That is strictly
   finer than conversion (which on closed constructor data would be equality
   anyway), costs no elaboration at all, and localizes any divergence to a
   diff. `seven` is the one fixture where the texts differ, and only in the
   spec *spelling* — the source says `7`, a walker that never saw the source
   says `Succ(…)` — so it is the one whose emission is checked on its own.
6. ✅ **Negative controls.** (a) The in-language honesty control: a copy of the
   library whose `ta_succ` emits the `Zero` tag. It arrives as *two* controls,
   because the library states its own acceptance — the file's theorems refuse
   the mutation at its declaration, which the test asserts first — and then,
   with those stripped, the emission the perturbed transcriber produces fails
   the kernel gate at its **exactness fixture**, a `refl` on a concrete run
   that needs nothing but the declarations prefix. It lives in a test of its
   own for the stack reason in §8. (b) `mul` declines
   by neutrality, naming the global at the head of the spine, while the Rust v2
   path generates it in the same test. (c) A `let` body and a non-`Nat`
   parameter decline in the hook. (d) Seven slice diagnostics in
   `tests/quotation.rs`: missing default, unknown arm name, wrong binder count,
   a motive that would mention a local, `match code` outside a `meta fn`, one
   inside a quote payload, and the positive that all six arms elaborate.
7. ✅ **No regression.** A file that never declares `transcribe` takes the Rust
   path exactly as before (every existing certgen positive and control is
   unchanged and green). Two quotation tests **flipped from refusal to
   positive** and are retargeted in place with the reason: a `meta fn` may
   return ordinary data, and a `meta fn` body may name an ordinary global.

## 11. Declined and deferred, with homes

- **v2 cross-function transcription in-language** — blocked by neutral global
  references (verdict blocker 1, `reduce.rs:2206`). Needs a recursor branch for
  globals (an intensional-analysis kernel extension with ch. 07 obligations) or
  elaborator-side inlining-for-analysis. Stays on
  `issues/generators-in-the-language.md`.
- **Certificate emission in-language** — blocked as §5 explains; the two
  futures (dependent code types over meta data; the fold-as-a-lemma) belong to
  a kernel round and to `issues/prog-extension-lemma.md` respectively.
- **In-language marking** (closing §1's seam) — wants surface delayed
  substitution (`$u[x := t]`) and meta-layer re-entry; file it where
  surface-v0's finding 2 lives.
- **`_(rebuild)` default arms** (surface-v0 §6's transformation flavor, backed
  by the kernel's `identity_branches`) — this round writes an *analysis*, not a
  pass; the first transformation pass is its customer.
- **Sub-code binders and splice-patterns in arms**, **dependent motives**,
  **`ty_*` arms**, **`CodeTy`/`LetBoxTy` inputs** — all four arrive together
  with the first artifact that analyzes *types* (§8 item 2, non-Nat
  embeddings). *[Corrected 2026-08-11 by the signature-reflection round
  (`docs/fn-signature-reflection-design.md`): the first type-analyzing
  artifact needed only a `CodeTy`-typed input plus the `ty_*` arms — which
  were already writable, all 52 names, per §10.1's deviation. Sub-code
  binders and dependent motives did not arrive and were not needed.]*
  *[Confirmed again 2026-08-12 by the non-`Nat` embeddings round
  (`docs/certgen-non-nat-embeddings-design.md`), which IS §8 item 2: it needed
  four more **term** arms (`tm_triv`/`tm_pair`/`tm_inl`/`tm_inr`) and three
  more **type** arms (`ty_unit`/`ty_sigma`/`ty_sum`), all already writable
  under the one constant motive. Sub-code binders, dependent motives and
  `CodeTy`/`LetBoxTy` inputs still did not arrive and still were not needed;
  this bullet's prediction can be retired.]*
- **Fixture fuels and the loopification pass** — unchanged homes
  (`docs/certifying-generator-design.md` §8 items 1 and 3).
- **User-declared analyzer slots** — deferred with user-declared slots
  generally (`docs/meta-def-registration-design.md` §10, first bullet): the
  open question is what the contract is when there is no Rust signature to
  check against.
- **The readback's dependence on the lowering.** `read_ir` is written against
  the tier-0/tier-1 *value* shapes, pinned in one comment block in
  `certgen.rs`. It is decline-safe by construction — a shape it has no case for
  is an `Err`, never a mis-read — but a lowering round that changes those
  shapes will turn the in-language path off rather than corrupt it, and should
  expect to update that block. A general value readback (the thing
  `inductive::decoded` is for types) is the real answer and has no other
  customer yet.
- **The walker's own size.** `TA` is the single constant motive, so every state
  the analysis needs is a constructor of it and every `match` on it pays
  Θ(arms × |lowered field type|) (`issues/wf-field-conversion-cost.md`). Two
  rules the non-`Nat` round had to learn the hard way, and the file now states:
  never nest a `match` on `TA` inside another (split into one-`match`
  helpers), and never *return* `TA` from a helper whose callers only want a
  value (`ta_val` returns a two-constructor `VOut`). Both are why that round
  could add two states for +17% rather than +40%.
- **The shell's check cost** (~9 s: a 52-branch `rec_ga` against a real motive,
  plus registration re-elaborating the expected signature). Left alone — this
  is not a perf round — but it lands on the suite's second-most expensive
  binary, so `issues/certgen-harness-cost.md` is where a lever would go if the
  analysis stage grows a second artifact.
- **Ψ-resident meta definitions** — still the map round's deferral
  (`docs/in-language-map-design.md` §8); nothing here needs meta fns to
  reference each other.

## 12. Documents this design amends

Recorded as corrections, per repo discipline; the coordinator owns the issue
edits.

1. `issues/generators-in-the-language.md`, 2026-08-02 verdict — "elim_N +
   constructors + **variables**" overstates the variable case: `elim^Trm` walks
   variables but cannot distinguish them (§1, with the kernel and ch. 04
   citations). The migration order is unaffected; the *shape* of the step is,
   and this is a fifth blocker in the same family as (1)–(4), narrower than (4).
2. `docs/certifying-generator-design.md` §8 item 4 — repeats the same sentence;
   same amendment, plus: the blockers gate the *later* stages **and** the
   variable seam gates this one.
3. `issues/certifying-generator.md`, 2026-08-02 — two corrections: the surface
   story is 52 branches, not 37; and the transcriber's inputs do **not** need
   `CodeTy` locals letboxed into recursors (§2, last bullet) — the Nat-only
   fragment's recursor annotation is a closed type.
4. `docs/sketches/surface-v0.md` §6 — "37 fixed branches" is the paper's count,
   not the kernel's (`rec.rs:208`); and of the two default-arm flavors this
   round adopts only the constant one.
5. `docs/meta-def-registration-design.md` — binding here, and missed by this
   document's first draft: it retired routing by name, and its slot vocabulary
   types *code templates* by their payload Π spine, which an analyzer does not
   have. **Amended by this round**: that document now carries a dated §11
   extension specifying analyzer slots (contract by whole-signature
   convertibility, expected signature written in Heather, caller builds the
   spine), plus two smaller consequences — ordinary parameters and results on a
   `meta fn`, and globals nameable from a meta body — and the elaborator-held
   staleness fix.
6. `docs/certifying-generator-design.md` §10, third bullet ("slot-map
   convention: the code comments own the layout") — with two transcribers the
   layout is now an *interface*, and §4's rendering function plus the §5
   cross-check are where it is pinned.
