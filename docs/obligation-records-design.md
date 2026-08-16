# Obligation records: inline proofs, reporting holes, and the `impl` surface — design

Status: **as landed** (2026-08-15). Produced from the settled pre-charter
discussion recorded in `issues/impl-declaration-surface.md`, revised by
discussion rounds 4 and 5 — which moved the design from *file-wide obligation
slots* to **inline-first** — and then implemented. Where an earlier draft of
this document and rounds 4–5 disagreed, rounds 4–5 won and this text is the
result; §9 keeps the rejected shape with the analysis that rejected it, because
the analysis is the reusable part.

Unlike `docs/datarepr-design.md`'s first draft, **every Heather snippet below
has been run** — the design round ran them through the built CLI (release binary
at `f42dcce`, ulimit-wrapped) on the `Bin`-repr fixture from
`crates/elab/tests/support/mod.rs`, and the implementation round turned the
surviving ones into tests. §10 is the probe log, marked with which probes the
revision reuses and which the revision retired.

Owners of the seams this touches: `issues/datarepr-surface-ergonomics.md`
(items 1+2, the audit this grew from), `issues/repr-access-spellings.md` (the
reference spelling, which §3 hands back to it deliberately),
`issues/repr-fold-via-abs-default.md` (the clause-default collision §1.2
resolves), `issues/unnameable-generated-names.md` (why §4.4 does not namespace
derived artifacts yet), `issues/theorem-field-projection-oom.md` (a bug §1.3
now names as a bug and nothing here bends around),
`issues/intrinsic-certification-style.md` (§7), `issues/ai-facing-tooling.md`
(§6), `issues/generators-in-the-language.md` (the eventual home of §4.3's
routes), `issues/proof-scale-abbreviations.md` (the companion piece: what makes
inline proofs writable at scale).

The design principle inherited unchanged: **the elaborator is untrusted because
every output carries its own certificate.** Nothing below is justified by "the
form is careful". The inline-first rule is the sharp end of it: **a file that
checks is a file that is certified.** There is no state in which a declaration
is on the books and its obligations are outstanding.

---

## 0. The shape in one paragraph

`impl f for Rp` is a **record literal whose theorem-valued fields are
obligations** — the field statements computed from (spec fn, repr) by §1.2 of
the datarepr design, over one general mechanism whose other customers are
`datarepr`'s clause laws and, later, certgen's equivalences and user class laws.
Clauses accept **inline expressions of every shape the surface has**, by
splicing the user's AST into the generated declaration instead of re-spelling it
as text (§4.2). A clause may instead be `?`, a **reporting hole**: the
declaration fails, at the `?`'s own span, printing the statement that clause
owes (§1.2) — the typed-hole workflow, and the only thing `?` does. Omission
keeps its own meaning, *take the default*, and the two never blur. A whole
`impl` may be `:= derive()`, which runs the transfer generator and fails at the
declaration with the decline reason verbatim; a `refines` clause may be
`via_derived(p)`, which checks `p` against the synthesized weak abs-image
equation and assembles the certificate by transitivity (§4.3). Every obligation
is discharged **where it is written**; provenance is recorded on the registry
entry and printed by the tooling, never consulted by a certificate.

Findings, gathered for the coordinator's eye:

- **FINDING A (§2.1)**: the §1.2 statement schema was implemented **twice** —
  `elab_impl` and reprgen's phase 3 each computed the `S ↦ R` restatement, the
  `inv` hypotheses and the conclusion independently. The round's first commit
  was the extraction, not new code: `ImplSchema` is now the single source, and
  the `?` error and the obligations listing print from it.
- **FINDING B (§4.2)**: nothing about inline clause expressions is hard except
  `spell_expr`. Probed: λ, unannotated λ, `match`, `let`-blocks and inference-
  bearing terms **all check** in exactly the 0-ary-declaration shape the
  emission already uses; the only refusal was the deliberate one in
  `spell_expr`, which declines rather than render lossily. The fix was not a
  wider printer.
- **FINDING C (§1.2)**: "omitted field = obligation" collides with
  `issues/repr-fold-via-abs-default.md`, which is about to give omitted clauses
  *defaults*. Under both rules an omitted `Succ_inv` would silently become an
  open obligation. Under inline-first the collision cannot arise at all:
  omission defaults, `?` reports and fails, and there is no third state.
- **FINDING D (§3, downgraded)**: `A::b` is a **single lexer token** with one
  join, so a multi-segment `::` path needs new grammar. Round 5's verdict —
  lexers do not get votes — makes this a cost note rather than a design input,
  and inline-first makes the cost zero: obligation paths are **print-only**.
- **FINDING E (§4.3, new this round)**: at one `(repr, operation)` key there can
  only ever be one `Impl`, so `via_derived`'s "use the derived `Impl` if it is
  already registered" branch is unreachable in v1 — the route always derives.
  The route therefore consumes reprgen's *artifacts* and not its registration,
  which is why `ReprEmission` now reports where its trailing `impl` block
  starts.
- **FINDING F (§2.2, new this round)**: the surface has **no expression type
  ascription**. `(e : T)` is not a production — `:` appears in binders and
  declaration heads only. Ascription on a clause is therefore deferred with no
  grammar invented, and the interim is the named-theorem route (state the
  theorem at your own type, name it in the clause, let the field type check it
  by conversion — probe 4's δ/α acceptance is what makes that work).

---

## 1. The mechanism: obligation records, inline-first

### 1.1 What an obligation-bearing declaration is

Three parts, and none of them is a new kernel notion:

1. **A record type** whose fields are the artifacts — data fields (`body`,
   `R`, `abs`, `fold`) and theorem fields (`refines`, `refines_inv`, the
   commutation and closure laws). It is generated per owner, as it already was.
2. **An owner key**, the identity the registry uses. For `impl` it is
   `(repr name, operation name)`. For `datarepr` it is the repr's name.
3. **A statement schema**: for each theorem field, the statement it owes,
   computed from the owner's own data and carried as **spelled source text**
   (§2.1). This is what a `?` prints, what the listing prints, and what the
   emitted declaration is checked against.

A declaration form decides **which of its fields are obligations**. v1's answer,
decided:

> Only **theorem fields** are obligations. `impl`'s are `refines` and (at a
> repr-typed result) `refines_inv`; `datarepr`'s are the commutation and closure
> laws and `fold_law`. `body`, `R`, `abs`, `inv`, `fold` and the `mk` images are
> **data the statements are computed from** — a `?` there would leave the schema
> with nothing to synthesize, so it is an error that says exactly that.

RECOMMENDED against: marking obligation-ness *in the record type* (`record R {
obligation refines: … }`). These record types are generated from the owner's own
data, so a marker in them carries no information the declaration form does not
already have, and it would put a second, weaker source of truth next to the
form. Revisit when a user writes an obligation-bearing record type by hand —
exactly what a user-defined class with laws will want, and the natural v2 of
this section.

**"Discharged" means a declaration exists.** Filling field `(owner, field)`
emits one ordinary declaration — `theorem <OwnerNamespace>::<field>():
<synthesized type> { <proof> }` — into the owner's namespace, and the assembled
record value is emitted after the last one. That was true before this round and
is unchanged; what the round adds is *what may stand in the proof position*.

### 1.2 `?` is a reporting hole; omission is the default — FINDING C

An obligation may be written `<field> := ?` (or `?name`, which only labels it
in the message). Its meaning is exhausted by one sentence:

> **`?` makes the declaration fail, at the `?`'s own span, printing the
> statement that clause owes.**

It is not deferral. Nothing is registered, no state survives the error, and
there is no later declaration that discharges it — the author reads the
statement out of the error, writes the proof where the `?` was, and re-checks.
That is the typed-hole workflow, and it is the whole of the mechanism.

Omission keeps its current and future meaning: *take the default* (`refl` today;
`fold := via abs` and `inv := True` once `issues/repr-fold-via-abs-default.md`
lands). The two rules therefore never meet, which is FINDING C dissolved rather
than adjudicated. The clause rule in one sentence, for that round to inherit:
**omitted takes the default, `?` demands and reports, and anything else is
checked as today.**

Why `?` earns its place even though it *only* fails:

1. **It reports.** The statement of a generated obligation is the one thing a
   proof author cannot guess and cannot read off the source; before this, the
   way to see it was to write a wrong proof and read the conversion error.
2. **It cannot be forgotten.** A misspelled clause name still errors as it did;
   a `?` errors; an omission defaults. Every path is loud.
3. **Grammar cost zero.** `?` already lexes (`TokKind::Hole`,
   `issues/goal-holes.md`) and already reached the elaborator — it died in
   `spell_expr`, which is precisely what §4.2 replaced.

Two recorded wants, neither built here:

- **Checking should continue past a `?`** so that downstream breakage — a user
  of the interface whose call no longer typechecks — surfaces before the proof
  is written (round-5 verdict, "not too important right now"). That is
  error-tolerant elaboration, a diagnostics-mode change, and it is logged as a
  want on `issues/ai-facing-tooling.md` rather than built here.
- **`?` inside a proof body** is the existing goal mechanism and is untouched;
  the difference in scope (a body hole is solved by inference within one
  declaration, a clause hole is answered by the author) is exactly what §6's
  listing exists to make visible.

### 1.3 Where the artifacts live: the namespace

An obligation's proof is declared **in the owner's namespace**
(`Impl_BinNat_add::refines()`), and consumers reach it there. Round 5's
methodology verdict requires this to stand on its own merits, so:

1. **The statement is source text before it is a term.** The schema is built as
   surface source (§2.1), and a namespace declaration is the one shape that
   takes a *written* type directly — which is what lets `?` and the listing
   print a statement a human can read, without decoding kernel terms
   (`issues/goal-display-decodes`; probe 8 shows what the alternative looks
   like).
2. **Laws must be reachable without assembling the value.** A transfer closes a
   callee step with that callee's `refines` while the callee's own record value
   may not be built yet — and, at a `datarepr`, the laws are consumed by the
   *generator* of the very value they are fields of. A namespace member has no
   such ordering problem; a projection does.
3. **One name per obligation is what tooling needs.** Provenance, the listing
   and the `?` message all key on a declaration, not on a field access.

`issues/theorem-field-projection-oom.md` — projecting a theorem-valued field off
an assembled record value exhausts memory and dies on the ulimit — is a **live
bug, not a design input**. An earlier draft of this section used it as the
justification, and round 5 ruled that bugs do not get to hold designs back. The
rule above would be the rule with the bug fixed; the bug is to be fixed
(its priority was raised on that verdict), and when it is, nothing here changes.

### 1.4 Discharge scope: inline, in the declaration

Cross-file filling is out by user verdict; **within-file deferral is out by the
round-4 analysis** (§9). A declaration's obligations are discharged in the
declaration, in the clause. What that costs and what it buys:

| | inline (v1) | file-wide slots (rejected, §9) |
|---|---|---|
| elaborator state | none — a clause is an expression | an open table, an end-of-file check, a declared-but-uncertified state |
| what "checked" means | certified | certified *or* still owed, distinguished by a later error |
| a helper lemma the proof needs | inside the proof expression, at exactly the scope it deserves (`issues/proof-scale-abbreviations.md`) | between the block and the proof, at top level |
| named statement-free proof | not available | available — deferral's one unique cargo |
| generator emission | contiguous block, as today | contiguous block |

The **adjacent certification region** — `proof refines { … }` immediately after
the block, owner implicit, the shape Coq's `Next Obligation` and Isabelle's
proof blocks take — is ledgered as the extension to reach for **if inline proves
insufficient at scale**, and nothing in v1 precludes it: it would be a second
filling route into the same emission, exactly like `derive()`.

### 1.5 There is no open state

The asymmetry the earlier draft needed — a body that exists while its
certificate does not — does not arise. An `impl` block either produces its
record value and its registry entry, or it produces a diagnostic and nothing
else. Consequences worth stating because they are the *point*:

- `impl_global(repr, op)` never returns an entry whose certificate is
  outstanding, so no consumer needs a second failure mode;
- monotonicity is trivially preserved (declarations accumulate; nothing mutates
  or retracts) rather than preserved by an argument about a slot table;
- a failing block leaves the artifacts it had already emitted — the record type,
  `body` — in Ψ, because they were checked. That is the ordinary behaviour of a
  failing generated declaration, not a promise about the failed one.

## 2. Statement synthesis and ascription

### 2.1 One schema, formerly written twice — FINDING A

The `impl` statements come from `docs/datarepr-design.md` §1.2: the signature
with `S ↦ R` at every occurrence, an `inv` hypothesis per repr-typed argument,
and a conclusion by result type (`body(x̄) = f(⟦x̄⟧)`, or `abs(body(x̄)) =
f(⟦x̄⟧)` plus `inv(body(x̄))` at a repr-typed result). It was implemented twice —
`elab_impl` building `binders`/`at_repr`/`hyps`/`refines_ty`/`inv_ty` as
strings, and reprgen phase 3 rebuilding `params`, `law_binders` and `spec_call`
for the same schema at the derived `Impl`.

> **`ImplSchema`** (`crates/elab/src/datarepr.rs`, beside `impl_record_name`) is
> now the single computation: from `(the spec fn's declaration, the repr view)`
> it carries the parameter list at `R`, the repr-typed parameters, the `inv`
> hypotheses, the spec-side arguments, the result type and `res_is_spec`, each
> as spelled source, and it answers `body_ty`, `law_binders`, `spec_call`,
> `refines_ty(call)` and `inv_ty(call)`. `elab_impl` consumes it, reprgen phase 3
> consumes it, `?` prints from it, `via_derived` states its obligation from it,
> and §6's listing prints from it. The extraction commit changed no behaviour and
> no emitted byte, which is what made it a safe first step.

Statements for `datarepr`'s obligations come from where they already did —
`abs_law_ty`, `inv_law_ty`, `fold_law_ty` — which were already the
"statement as a value" shape `ImplSchema` copies.

### 2.2 Ascription: deferred, with the named-theorem interim — FINDING F

The plan of record was `<field> := <expr> : <statement>`, a checked ascription
so that a reader sees what is being proved next to the proof. It is **deferred**:
the surface has no expression ascription production at all (FINDING F), and
round 5's charter is explicit that no new grammar is to be invented for it here.

The interim costs one line and is what the fixtures already do: state the
theorem at your own type, name it in the clause.

```heather
theorem my_refines(ra: Bin, rb: Bin, h0: (Zero = Zero), h1: (Zero = Zero)):
    bin_abs(bin_add_derived(ra, rb)) = add(bin_abs(ra), bin_abs(rb))
{ bin_iter_abs(ra, bin_abs(rb)) }

impl add for BinNat { body := bin_add_derived, refines := my_refines, … }
```

That this *works* — that a statement written in the author's own vocabulary
discharges the generated obligation — is probe 4's result, and it is the finding
that makes ascription worth having later. What conversion accepts, probed at
`Bin`:

| ascribed statement differs by | verdict |
|---|---|
| δ: `bin_abs` for `Repr_BinNat::abs()`, `bin_inv` for the generated `inv`, `bin_add_derived` for `body(…)` | **accepted** |
| δ to the bottom: `h0: (Zero = Zero)` for `h0: bin_inv(ra)` | **accepted** |
| α: different binder names | accepted |
| hypotheses reordered (`ra, h0, rb, h1`) | **rejected**, `NotConvertible` |
| equation orientation swapped | **rejected**, `NotConvertible` |

So when ascription lands it must be **definitional**, checked by the ordinary
field-type conversion and not syntactically: syntactic checking would reject the
first three rows, including the one that makes the feature worth having.
Orientation and argument order — the two things a reader actually relies on —
are pinned either way.

### 2.3 What a disagreement looks like

The failing check is a field type mismatch inside generated source, which is the
diagnostic `elab_generated` already wraps. The round owes it two
specializations, and both landed:

- the error is located at the **clause's own span** (`cl.span`), not at the
  owner declaration, so an inline proof's failure points at the inline proof;
- the generated declaration is still quoted, because it *is* the obligation —
  the field's statement is exactly what is not obvious.

A `?` produces the same information deliberately:

```
error: `refines` of `impl add for BinNat` is not proved
  --> file.hthr:120:16
    |
120 |     refines := ?,
    |                ^
    |
  `Impl(add, BinNat)::refines` owes:
    (ra: Bin) -> (rb: Bin) -> (h0: bin_inv(ra)) -> (h1: bin_inv(rb)) ->
      Repr_BinNat::abs()(Impl_BinNat_add::body()(ra)(rb))
        = add(Repr_BinNat::abs()(ra), Repr_BinNat::abs()(rb))
```

The statement is printed in the *generated* vocabulary, because that is the
vocabulary the schema is built in and the one the kernel will compare against;
§2.2's interim is how an author restates it in their own. Sharpening that — a
divergence trace, a statement re-spelled through the user's own definitions —
is `issues/ai-facing-tooling.md`'s subject and is not v1.

## 3. The obligation path spelling: `::`, print-only — FINDING D

An obligation is a **member of its owner's namespace**, and `::` is the member
operator. That is the whole argument, and round 5 ratified it on exactly those
grounds, with the standing instruction that a lexer artifact is a cost to pay
and not a vote to count. So:

- `Impl(add, BinNat)::refines` — the `impl` form, which has no name of its own,
  written as §1.2's `Impl<Rp>(f)` registry type applied;
- `BinC::Succ_inv` — a named obligation-bearing declaration, its own name.

**In v1 these are print-only**: they appear in `?` messages, in failure
diagnostics and in §6's listing, and nowhere else. Under inline-first nothing
*references* an obligation from outside the declaration that owes it, so no
production is needed and none was added. The cost note stands for whoever needs
the grammar later: `A::b` is one lexer token with one join
(`lexer.rs:130-137`), `::` never follows an application, and modules will force
that lifting anyway.

**Reference position is deliberately not settled here.** Citing a certificate
inside another proof keeps today's `Impl_BinNat_add::refines()`, and the pretty
spelling belongs to `issues/repr-access-spellings.md`, which should take
`<owner>::<obligation>` as the *shape* to extend. Note for that issue: a `.`
form would mean value projection and inherits
`issues/theorem-field-projection-oom.md`; a `::` form does not, which is a
second, independent reason the member operator is the right one.

## 4. The `impl` surface

### 4.1 Grammar

```
impl <op> for <repr> { <clause>, … }          // the form today, widened by §4.2
impl <op> for <repr> := derive();             // pinning: the transfer, at declaration time

clause  ::= <name> := <expr>                  // ANY surface expression (§4.2)
          | <name> := ?                       // a reporting hole (§1.2)
          | <name> := ?<name>                 // …labelled
          | refines := via_derived(<expr>)    // the §1.2 route (§4.3)
```

`datarepr`'s clause list is the same grammar and gains the same two widenings.
No keyword was added: `derive` and `via_derived` are ordinary applications in
clause position, recognised by the elaborator, which is what keeps §4.3's
promise that they can become ordinary metafunctions later.

### 4.2 Inline expressions: splice the AST, do not widen the printer — FINDING B

A clause used to be turned back into **text** by `spell_expr`, which handled
`Var`/`Num`/`App`/`TyApp`/`Dot` and deliberately declined on everything else
rather than fall back to `_` (which would parse back as a *hole* and let
inference invent content). The blocker was only the round-trip: probe 2 checked
an annotated λ, an **unannotated** λ, an inline `match`, a `let`-block, and a
term needing implicit-argument inference, in the exact 0-ary-declaration shape
the emission uses. All five check.

> **The skeleton is generated with a placeholder, parsed, and the placeholder
> replaced by the user's `Expr` before `elab_decl`.** One patch point per
> clause, no printer, and every surface form the parser accepts works the day it
> is added.

Two boundaries, both deliberate:

- **The `R` clause is still spelled**, not spliced: it is used as a *type* in a
  dozen positions of the generated source, so it has to survive as text.
  `spell_expr` keeps exactly that job and its decline message now says so.
- **A placeholder only ever occupies a whole generated body**, so the
  substitution is a body-root replacement and not a general AST walk — no
  ~25-variant traversal to keep in sync with the surface.

Rejected: a **total expression printer**. It would have to cover every
`ExprKind` plus patterns, arms and blocks, stay in sync with the surface
forever, and re-derive `spell_expr`'s decline discipline at every new form — all
to reproduce text that is immediately re-parsed into the AST we started with.

Recorded limitation, unchanged: `Span` is a bare `(start, end)` with no file
identity, so a spliced subtree's spans index the *user's* file while the
enclosing generated declaration's index the generated text. The round improved
the report to the **clause's** own span, which is in the user's file and is
right; pointing at a failing *sub-term* inside an inline proof wants span
provenance and stays deferred (§8).

### 4.3 The routes, and what each leaves open

**`derive()`** — the pinning form, and the first transfer ever requested from
surface source. `reprgen(op, repr)` is already pure: it reads the registries and
returns source text including the `impl` block itself. The surface form is
therefore a *caller*: elaborate the emission, or fail at the declaration with
the decline reason **verbatim**. It fills body and every obligation, so a
derived `impl` never has an unproved field. Provenance `Derived` is recorded on
the registry entry the emission's own `impl` block installs.

**`via_derived(<proof>)`** — **function-shaped**, per the round-4 verdict: the
composition *is* `trans`, so the surface should look like the application it is.
Written at `refines`, it

1. derives the `Impl` of the same operation at the same repr — see FINDING E:
   at one key there is only ever one `Impl`, so "reuse it if present" is
   unreachable in v1 and the route always derives, consuming reprgen's
   *artifacts* (the derived body, its `refines`, the lemmas) and not its
   registration;
2. checks `<proof>` against the synthesized **weak abs-image equation**

```
(ra: Bin) -> (rb: Bin) -> (h0: bin_inv(ra)) -> (h1: bin_inv(rb)) ->
    Repr_BinNat::abs()(Impl_BinNat_add::body()(ra)(rb))
      = Repr_BinNat::abs()(add_derived(ra, rb))
```

3. and assembles `refines` as `trans(<proof>, <derived refines>)` — **no
   congruence step**, because the obligation is already stated under `abs`.
   (At a result that is *not* the spec type the same shape holds with `abs`
   dropped from both sides.)

Carrier equality remains available as the strongest discharge — the author
writes the `abs`-free equation as their own theorem and `cong_abs` it — since
`abs` composed with equal carriers is equal; that is `docs/datarepr-design.md`
§1.2's settled paragraph and it needs nothing from this surface.

**At a repr-typed result, `via_derived` does not fill `refines_inv`.**
`inv(body(x̄))` does not follow from an abs-image equation — that is precisely
what non-injective `abs` costs — so the declaration demands `refines_inv` and
the error **says why** rather than repeating the generic "you also need a
`refines_inv`".

**Two special powers, named, and elaborator-owned for now.** `via_derived` is
written as a function and will become one when the meta layer can provide (a)
**expected-type synthesis** — its argument's type is computed from the
declaration it appears in, which no ordinary call can do — and (b) the
**derive-if-absent registry effect**. Until then it is recognised by the
elaborator in clause position. The surface was chosen so that nothing changes
on the day it stops being special: it is an application, its argument is an
ordinary expression checked at an ordinary type, and its result is an ordinary
proof. Same for `derive()`.

**Plain terms** — inline or named, per §4.2 — are checked against the
synthesized statement with ordinary bidirectional inference (probed: an inline
`trans` with an uninferable implicit fails with the ordinary message, so clauses
are in checking position as they should be).

### 4.4 What today's form becomes, and byte-stability

**Decided: the named-artifacts block stays valid, unchanged, and stays the
generator emission target.** Every clause form is a widening; `impl add for
BinNat { body := bin_add_derived, refines := … }` means exactly what it meant.
This is not politeness — reprgen emits that text, and the user's ratified
motivation for the whole surface is that *tuned impls will themselves be
generated*, so the emission form must remain the plainest one.

**Decided and held: reprgen and datarepr emissions are byte-identical after this
round.** No emitted text changed; the new surface adds callers, a splice table
and an obligations ledger. `crates/elab/tests/reprgen.rs` pins emissions by
`contains`, which is the cheap check that it stayed so.

One thing this **defers rather than decides**: reprgen names derived artifacts
at top level (`add_derived`, `add_is_rec`, `add_derived_refines`). Reached from
a user-written `impl add for BinNat := derive()`, those land in the user's
namespace. The Q2 verdict asks only that provenance be *distinguishable on
inspection*, which §6's listing satisfies with a registry-side `Provenance` enum
(`Derived | ViaDerived | Inline | Named`) — recorded, never consulted by a
certificate. Moving derived artifacts under the owner's namespace is the better
answer and belongs with `issues/unnameable-generated-names.md`, whose marker
they should carry; doing it here would change emission bytes for no v1 benefit.

### 4.5 `runtime_fn`, as an aside only

Nothing here infers an entry to runtime; the verdict stands. The short form the
user allowed — "treat the derived definition as a runtime fn without rewriting
it" — has a natural spelling (`runtime_fn f at Rp;`, resolving the registry and
erroring when there is no `Impl`), and is **not** part of this design. Recorded
so the shape is not re-derived.

## 5. The second customer: `datarepr` clause laws

`datarepr` already had everything: generated statements (`abs_law_ty`,
`inv_law_ty`, `fold_law_ty`), a namespace, and a value assembled last. It gains
exactly what `impl` gains, through the same code: inline clause expressions and
the `?` reporting hole.

```heather
datarepr BinC for Nat {
    R := Bin, abs := bin_abs, inv := bin_canon,
    mk Zero := BNil, mk Succ := binc,
    Succ_abs := bin_succ_abs_canon,
    Succ_inv := λ a0 h0 =>
        trans(j(bin_succ_abs(a0), λ y q => bin_of_nat(bin_abs(binc(a0))) = bin_of_nat(y), refl),
              j(h0, λ y q => binc(bin_of_nat(bin_abs(a0))) = binc(y), refl)),
    fold := bin_fold, fold_law := bin_fold_law_canon,
}
```

Writing `Succ_inv := ?` instead fails the `datarepr` at that span, printing the
closure law's statement — which is how the proof above gets written in the first
place. Two interactions held:

- **`repr-fold-via-abs-default` is unblocked, not blocked.** The two rounds
  wanted the same clause-reading code and disagreed about omission; the rule is
  now landed and is one sentence (§1.2), so that round can proceed
  independently: it defines what *omitted* produces and touches nothing `?`
  does.
- `datarepr`'s clause laws inherit §1.4 note 5's friction (a law clause's binder
  list includes the `inv` hypotheses even when unused). Inline clauses do not
  fix it and do not make it worse; the λ can simply ignore them, as above.

## 6. Tooling

**The obligations listing.** `heather obligations [--json] <file>` — one row per
obligation-bearing field of every such declaration in the file:

```
owner                     field         state      provenance  statement
impl add for BinNat       refines       supplied   inline      (ra: Bin) -> (rb: Bin) -> …
impl add for BinNat       refines_inv   supplied   named       (ra: Bin) -> (rb: Bin) -> …
datarepr BinC             Succ_inv      supplied   inline      (a0: Bin) -> (h0: bin_canon(a0)) -> …
datarepr BinC             Succ_abs      defaulted  —           …
impl length for ListTok   refines       supplied   derived     …
```

Under inline-first a listed file is a *checked* file, so the `state` column
never says "open": it distinguishes **supplied** (the author wrote a proof),
**defaulted** (omitted, `refl`), **derived** and **via** — which is precisely
the Q2 verdict's "distinguish provenance on inspection", and precisely what an
AI-facing tool needs to know before it starts editing. The statement column
prints the **synthesized source text** the schema holds (§2.1). That is worth
stating as a design property rather than an implementation detail: because the
schema is built as surface source, the listing is legible **without**
`issues/goal-display-decodes` — probe 8 shows the alternative, an unsolved goal
printing `Id[0](Nat; app(app(u5^{·^1}; …)))`.

**Failures return data.** Two shapes, both keyed to an obligation:

- *a `?`* — the §2.3 message: the owner, the `::` path, and the statement;
- *a declined `derive()`* — reprgen's reason verbatim (it already names the op,
  the constructor and the shape it could not read), tagged with the declaration
  it was asked to fill, so a tool can distinguish "the fragment does not cover
  this" from "you have not proved it yet".

## 7. Forward: intrinsic style (v2, precluded by nothing here)

`issues/intrinsic-certification-style.md` owns it. What this design owes it is
only that it stay reachable, and it does: an intrinsic definition elaborates by
splitting the recursion skeleton into values and proof components, and the proof
components have to *go* somewhere — the extrinsic artifacts. **Clause routes**
are that somewhere. The third route beside `derive()` and `via_derived(p)` is a
clause saying "this owner's obligations are filled by the splitter of definition
`f`", and it fits §1.1 with no change: a route produces the proof, the kernel
checks it, provenance records which route did it. Nothing in §1–§6 assumes the
proof was written by a human, and — since inline-first removed the open state —
nothing assumes there is a gap in time between the declaration and its
certificate.

## 8. Staging

### v1 — as landed (2026-08-15)

In order, each step green before the next:

1. **`ImplSchema` extraction** (§2.1). Behaviour-preserving; emissions
   byte-identical; reprgen phase 3 rewritten against it.
2. **AST splice for clauses** (§4.2), replacing `spell_expr` at the value-clause
   positions in both `elab_impl` and `written_clauses`; errors relocated to the
   clause span.
3. **`?`, the reporting hole** (§1.2), for both customers, printing the
   synthesized statement and the `::` path.
4. **The routes** (§4.3): `:= derive()` and `refines := via_derived(p)`, with
   `Provenance` on the registry entry.
5. **`heather obligations`** (§6), text and `--json`.

### Deferred, with cost recorded

- **Clause ascription** (§2.2, FINDING F): no surface production exists; the
  named-theorem route is the interim. Cost: one top-level name per proof the
  author wants labelled — the very friction this round removed elsewhere, so
  this is the first thing to revisit if inline proofs get long.
- **Error-tolerant checking past a `?`** (§1.2): a file with a `?` stops at the
  `?`. Cost: downstream breakage is found one fix at a time.
- **Span provenance for spliced ASTs** (§4.2): inline-proof errors locate to the
  clause, not the sub-term. Cost: one hunt inside a long inline proof; fixing it
  means giving `Span` a file identity, which touches every construction site.
- **Reference spelling** (§3): citing a certificate still spells the minted
  namespace path. Cost: minted names stay in hand-written proofs, exactly the
  friction `issues/repr-access-spellings.md` was filed for.
- **Derived artifacts in the owner's namespace** (§4.4): provenance is visible
  in the listing but not in the name.
- **Obligation-bearing record types written by hand** (§1.1): user classes with
  laws cannot use the mechanism until obligation-ness is expressible in a
  hand-written `record`.
- **The adjacent certification region** (§1.4): ledgered, to be reached for only
  if inline proves insufficient at scale.
- **Cross-file discharge**: out by verdict, not by cost.

## 9. Rejected alternatives (shape claims only)

- **File-wide obligation slots** — a slot table `(owner, field) ↦ (statement,
  state)`, `proof <owner>.<slot> { … }` declarations, order-free discharge
  within the file, an end-of-file completeness check, and a
  declared-but-uncertified state in between. This was the delivered design and
  round 4 rejected it, on one observation: **its only unique cargo is named
  statement-free proofs.** Everything else it was carrying — statement synthesis,
  inline clause expressions, a body written before its certificate, the routes,
  the obligations listing, monotonicity — survives without it, while the state
  it introduces is exactly the state that makes "this file checks" stop meaning
  "this file is certified". The local alternative for its one real benefit is
  better anyway: a helper lemma belongs *inside* the proof expression, where its
  scope is right (`issues/proof-scale-abbreviations.md`), not at top level
  between the block and the proof.
- **Omission as the open marker** — FINDING C, §1.2. Silent deferral, and a
  collision with the defaults round.
- **A statement-omitted `theorem`** as the filling form. Dropped pre-charter
  (user: a theorem without a visible statement is a trap).
- **The trailing proof-keyword form** (`impl … { … } proving refines { … }`).
  Dropped in discussion round 2 as redundant with first-class proof
  declarations — and those are now gone too, which leaves §1.4's adjacent region
  as the surviving shape of the idea.
- **A total expression printer** to make clauses inline-able — §4.2.
- **Obligation-ness marked in the record type** — §1.1; revisit for hand-written
  law-carrying records.
- **`<owner>.<slot>` as the obligation path** — §3. It was chosen because it
  parses today, which round 5 correctly identified as a lexer artifact deciding
  a semantic question; `.` also *means* value projection, which is the operation
  §1.3 has a live bug about.
- **`via derived` as a bare keyword route** rather than a function application.
  Round 4: the composition is `trans` and the user's proof is its argument, so
  the surface should be the application it is — and then it needs no new keyword
  and can stop being special without a grammar change.
- **Provenance consulted by resolution** (e.g. preferring hand impls over
  derived ones at a use site): never. Provenance is recorded for humans and
  tools; the registry has exactly one entry per key and the certificate is the
  same four names whatever produced them.

## 10. Probe log

Release CLI at `f42dcce`, every run `(ulimit -v 8388608 -t 120)`, fixture =
`bin_base!()` + `BIN_REPR` + `BIN_ADD` extracted from
`crates/elab/tests/support/mod.rs`. Marked with what the inline-first revision
did with each.

1. **Today's `impl` block** — the named-artifacts form checks; `body := λ …`,
   `body := match …`, `body := { let … }` all die at ``clause `body` is not a
   shape this round can spell``; a repr-typed result without `refines_inv` dies
   with §1.2's message. → *reused*: §4.1, §4.2, and the negative controls.
2. **The 0-ary emission shape with inline content** — annotated λ, unannotated
   λ, inline `match`, `let`-block, and an implicit-bearing term all check
   against a synthesized Π type. → *reused*: FINDING B, §4.2, and the acceptance
   tests of step 2.
3. **Slot-path candidates** — `::` after an application is a parse error in
   every arrangement; `.`-chains parse; `A::b` is one lexer token with one join;
   `@` is a claimed prefix. → *retired as a design input* by round 5's verdict,
   kept in §3 as the cost note for whoever writes the grammar.
4. **Ascription equality** — δ and α accepted; hypothesis reordering and
   equation orientation `NotConvertible`. → *reused*, and now the justification
   for §2.2's named-theorem interim rather than for a form that does not exist.
5. **The open-slot state machine, by hand** — record type with obligation
   statements, `body` filled at declaration, unrelated declarations intervening,
   the two theorems filled later in the user's vocabulary, the value assembled
   last: checks. → *retired with the mechanism* (§9). Its surviving content is
   probe 4's: a later, differently-spelled theorem discharges a generated
   obligation.
6. **`via_derived` synthesis** — the abs-image obligation, `refines =
   trans(obligation, derived_refines)` with no congruence step, and
   `refines_inv` as a separate obligation: all check. → *reused* as §4.3's
   shape and as the route's acceptance test.
7. **`proof` as a keyword** — `fn proof(n: Nat) -> Nat { n }` checks; no
   occurrence in `lib/`. → *retired*: there is no `proof` declaration.
8. **`?` in clause position** — `refines := ?` and `refines := ?later` parse and
   reach `spell_expr`; a `?` in a *body* prints an undecoded kernel goal. →
   *reused*: §1.2 (grammar cost zero) and §6 (why the listing prints source
   text).

Nothing probed refuted a settled frame item, in the design round or in the
implementation round; the stop-condition did not fire.
