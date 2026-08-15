# Obligation records: open proof slots, inline implementations, and the `impl` surface — design

Status: **design round, pre-implementation** (2026-08-15). Produced from the
settled pre-charter discussion recorded in `issues/impl-declaration-surface.md`
(the three 2026-08-15 log entries); this document develops those positions, it
does not relitigate them. Everything marked **RECOMMENDED** goes beyond the
settled constraints and awaits the user's yes/no; everything marked **FINDING**
is a place where the settled positions rub against the elaborator as it stands,
with the resolution this document argues for.

Unlike `docs/datarepr-design.md`'s first draft, **every Heather snippet below
has been run through the built CLI** (release binary at `f42dcce`, ulimit-
wrapped) on the `Bin`-repr fixture from `crates/elab/tests/support/mod.rs`. §10
is the probe log: what was run, what it showed, and which section each result
decides. Two sections changed shape because a probe contradicted the sketch
(§3's slot path, §1.2's open marker); one section exists only because a probe
found something the charter did not anticipate (§2.1's duplicated schema).

Owners of the seams this touches: `issues/datarepr-surface-ergonomics.md`
(items 1+2, the audit this grew from), `issues/repr-access-spellings.md` (the
reference spelling, which §3 hands back to it deliberately),
`issues/repr-fold-via-abs-default.md` (the clause-default collision §1.2
resolves), `issues/unnameable-generated-names.md` (why §4.4 does not namespace
derived artifacts yet), `issues/theorem-field-projection-oom.md` (why §1.3 is a
rule and not a preference), `issues/intrinsic-certification-style.md` (§7),
`issues/ai-facing-tooling.md` (§6), `issues/generators-in-the-language.md` (the
eventual home of §4.3's routes).

The design principle inherited unchanged: **the elaborator is untrusted because
every output carries its own certificate.** Nothing below is justified by "the
form is careful". In particular: an obligation slot is not a promise, it is a
*missing declaration*, and until it is filled nothing that depends on it exists
to be consumed.

---

## 0. The shape in one paragraph

A **record literal may leave theorem-valued fields open**, each becoming a
named **obligation slot** on the declaration that wrote it. `impl f for Rp` is
sugar that mints the schematic record type of §1.2 of the datarepr design — the
field statements computed from (spec fn, repr) — over that one general
mechanism; `datarepr`'s clause laws, certgen's equivalences and future class
laws are its other customers. A slot is filled by a **`proof <owner>.<slot>
{ … }` declaration**, optionally carrying a **checked ascription** of the
statement it discharges, checked by **conversion** (probed: delta and alpha
yes, reordering and orientation no — §2.2). Clauses accept **inline
expressions** of every shape the surface has, by splicing the user's AST into
the generated declaration instead of re-spelling it as text (§4.2). A clause
may instead say `derive()` (the transfer generator fills body *and*
obligations, failing at declaration with the decline reason) or `via derived`
(the obligation becomes §1.2's weak abs-image equation and the certificate is
assembled by transitivity — probed, §4.3). Discharge is **same-file** and
order-free, with an end-of-file completeness check; an owner with open slots is
**declared-but-uncertified** — its body is referenceable, its certificate is
not, and every consumer errors naming the slot. Provenance is recorded on the
registry entry and printed by the tooling, never consulted by a certificate.

Findings, gathered for the coordinator's eye:

- **FINDING A (§2.1)**: the §1.2 statement schema is implemented **twice** —
  `elab_impl` (`crates/elab/src/datarepr.rs:911-963`) and reprgen's phase 3
  (`crates/elab/src/reprgen.rs:349-373`) each compute the `S ↦ R` restatement,
  the `inv` hypotheses and the conclusion independently. Ascription checking
  needs the statement as a value, not as two inlined string-builders, so the
  round's first commit should be the extraction — not new code.
- **FINDING B (§4.2)**: nothing about inline clause expressions is hard except
  `spell_expr`. Probed: λ, unannotated λ, `match`, `let`-blocks and inference-
  bearing terms **all check** in exactly the 0-ary-declaration shape the
  emission already uses; the only refusal is the deliberate one in
  `spell_expr`, which declines rather than render lossily. The fix is not a
  wider printer.
- **FINDING C (§1.2)**: "omitted field = obligation" collides with
  `issues/repr-fold-via-abs-default.md`, which is about to give omitted clauses
  *defaults*. Under both rules an omitted `Succ_inv` would silently become an
  open obligation whenever its default fails to check — silent deferral, the
  one failure mode this design most wants to avoid. Open must be **written**.
- **FINDING D (§3)**: `A::b` is a **single lexer token** (`lexer.rs:130-137`,
  one join, no compound paths) and `::` never follows an application. Every
  `::`-shaped slot path in the charter's list therefore needs new grammar,
  while `.`-shaped ones parse today. The recommendation follows the lexer.

---

## 1. The mechanism: obligation records

### 1.1 What an obligation-bearing declaration is

Three parts, and none of them is a new kernel notion:

1. **A record type** whose fields are the artifacts — data fields (`body`,
   `R`, `abs`, `fold`) and theorem fields (`refines`, `refines_inv`, the
   commutation and closure laws). It is generated per owner, as it already is.
2. **An owner key**, the identity the slot table and the registry share. For
   `impl` it is `(repr name, operation name)` — the key `self.impls` already
   uses (`datarepr.rs:1042`). For `datarepr` it is the repr's name.
3. **A slot table**: `(owner key, field name) ↦ (synthesized statement,
   state)`, where state is `Open` or `Filled(provenance)`.

A declaration form decides **which of its fields may be left open**. v1's
answer, decided:

> Only **theorem fields** are slots. `impl`'s slots are `refines` and (at a
> repr-typed result) `refines_inv`; `datarepr`'s are the commutation and
> closure laws and `fold_law`. `body`, `R`, `abs`, `inv`, `fold` and the `mk`
> images are **data the statements are computed from** — leaving them open
> would leave the slot table with nothing to synthesize, so it is an error
> that says exactly that.

RECOMMENDED against: marking open-ability *in the record type* (`record R {
obligation refines: … }`). These record types are generated from the owner's
own data, so a marker in them carries no information the declaration form does
not already have, and it would put a second, weaker source of truth next to the
form. Revisit when a user writes an obligation-bearing record type by hand —
which is exactly what a user-defined class with laws will want, and is the
natural v2 of this section.

**"Filled" means a declaration exists.** Filling slot `(owner, field)` emits
one ordinary declaration — `theorem <OwnerNamespace>::<field>(): <synthesized
type> { <proof> }` — into the owner's namespace. When the last slot of an owner
closes, the assembled record value is emitted and the registry entry recorded.
That is the whole state machine, and §10's probe 5 runs it by hand, front to
back, at `Bin`.

### 1.2 Open is written, not omitted — FINDING C

**RECOMMENDED**: an open slot is spelled `<field> := ?`, or `<field> := ?name`
to give the slot a local name. Omission keeps its current and future meaning:
*take the default* (`refl` today; `fold := via abs` and `inv := True` once
`issues/repr-fold-via-abs-default.md` lands).

Three reasons, in order of weight:

1. **No silent deferral.** With omission meaning "open", a clause the author
   forgot and a clause the author deferred are the same text, and the file
   still checks. A missing proof would be reported only at end of file, at a
   declaration the author is no longer looking at.
2. **The defaults collision** is real and imminent (FINDING C). Under the
   written form the two rules never meet: omission defaults, `?` opens, a
   misspelled clause name still errors as it does today.
3. **`?` already lexes** (`TokKind::Hole`, `issues/goal-holes.md`), and probe 8
   shows `refines := ?` and `refines := ?later` reach the elaborator today —
   they die in `spell_expr`, which is precisely the place the round is
   changing. Grammar cost: zero.

It also reads right: `?` is the language's existing mark for "this is a goal".
The difference from a body hole is scope — a body hole is solved by inference
within one declaration, a clause hole is discharged by a later declaration —
and that difference is exactly the one §6's listing exists to make visible.

### 1.3 Where the artifacts live: the namespace, never the value

An obligation's proof is declared **in the owner's namespace**
(`Impl_BinNat_add::refines()`), and consumers reach it there. This is not a
style preference:

> Projecting a theorem-valued field off an **assembled record value** exhausts
> memory and dies on the ulimit — `issues/theorem-field-projection-oom.md`, a
> live user-reachable abort. Every path this design introduces reaches through
> the namespace. The assembled value is consumed **whole** or not at all.

Two consequences the implementing round must hold: the `proof` declaration
emits a namespace member (never a projection), and §6's listing renders
statements from the **synthesized source text**, never by decoding a projected
field (see §6 on why that also dodges `issues/goal-display-decodes`).

### 1.4 Discharge scope: same file, order-free, checked at end of file

Cross-file filling is out by user verdict. Within the file the charter offers
latitude to require adjacency ("the proof block comes right after"). Weighed:

| | adjacency | order-free in file |
|---|---|---|
| elaborator state | still needs the open table (a slot is filled by a *later declaration* either way) | same table |
| declaration cache | unaffected — the emitted artifacts are ordinary declarations in file order either way | same |
| helper lemmas between owner and proof | forbidden (must precede the owner) | allowed |
| generator emission | contiguous block | contiguous block |
| failure mode | reported at the next declaration | reported at end of file |

**RECOMMENDED: order-free within the file**, with adjacency as the *style* the
generators emit and the docs teach. Adjacency buys no simplification anywhere
that matters — the open state has to exist regardless, because §1.5's
declared-but-uncertified state is the whole point — while costing the one thing
a proof author actually wants, which is room to state a lemma between the
implementation and its certificate.

The end-of-file check is a hard error listing every unfilled slot with its
owner and statement. Monotonicity is preserved exactly as ratified:
declarations accumulate and discharge, nothing mutates or retracts, and file
order is dependency order only.

### 1.5 Open-state semantics

An owner with at least one open slot is **declared-but-uncertified**:

- its **data** fields exist and are referenceable — `Impl_BinNat_add::body()`
  is an ordinary declaration and other code may call it;
- its **registry entry does not exist**. `impl_global(repr, op)` returns
  nothing, and every consumer — a transfer closing a callee step, a
  `runtime_fn` resolving an operation, a `via derived` route asking for the
  derived certificate — errors **naming the open slot and its statement**,
  never "no `Impl` found";
- **nothing is retracted** if the file ends open. The error is at end of file;
  the declarations already made stay made and stay checked.

The asymmetry is deliberate and is the reason `body` is not a slot: an
uncertified body is an ordinary function, and pretending otherwise would make
the open state contagious for no gain.

## 2. Statement synthesis and ascription

### 2.1 One schema, currently written twice — FINDING A

The `impl` statements come from `docs/datarepr-design.md` §1.2: signature with
`S ↦ R` at every occurrence, an `inv` hypothesis per repr-typed argument, and a
conclusion by result type (`body(x̄) = f(⟦x̄⟧)`, or `abs(body(x̄)) = f(⟦x̄⟧)`
plus `inv(body(x̄))` at a repr-typed result). It is implemented **twice**:

- `crates/elab/src/datarepr.rs:911-963` — `elab_impl` builds `binders`,
  `at_repr`, `hyps`, `body_ty`, `refines_ty`, `inv_ty` as strings;
- `crates/elab/src/reprgen.rs:349-373` — phase 3 rebuilds `params` (`S ↦ R`),
  `law_binders` (parameters plus `h0`) and `spec_call` for the same schema at
  the derived `Impl`.

The two agree today because both were written against the same paragraph, and
the second is narrower (one repr-typed parameter, `h0` only). Ascription
checking needs the statement as a **value** — something to compare an ascribed
type against and to print in a listing — so the round's opening move is:

> **Extract `ImplSchema`** (`crates/elab/src/datarepr.rs`, beside
> `impl_record_name`): computed from `(the spec fn's declaration, the repr
> view)`, carrying the parameter list at `R`, the `inv` hypotheses, the body
> type, and the two conclusion types, each as spelled source. `elab_impl`
> consumes it, reprgen phase 3 consumes it, the slot table stores it, and §6's
> listing prints it. No behavior changes in that commit; the emissions stay
> byte-identical, which is what makes it a safe first step.

Statements for `datarepr`'s slots come from the same place they already do —
`abs_law_ty`, `inv_law_ty`, `fold_law_ty` (`datarepr.rs:785-835`) — which are
already the "statement as a value" shape `ImplSchema` should copy.

### 2.2 Ascription is checked by conversion — probed

`proof <owner>.<slot> : <statement> { … }` elaborates the ascribed statement
as the declared type of the emitted theorem. The check that the ascription
*is* the obligation then happens where it already happens: the assembled record
literal checks each field against the field type, by conversion. **No new
comparison machinery.** Probe 5 runs exactly this, split across intervening
declarations, and it checks.

What conversion accepts, probed at `Bin` (probe 4, four variants):

| ascribed statement differs by | verdict |
|---|---|
| δ: `bin_abs` for `Repr_BinNat::abs()`, `bin_inv` for the generated `inv`, `bin_add_derived` for `body(…)` | **accepted** |
| δ to the bottom: `h0: (Zero = Zero)` for `h0: bin_inv(ra)` | **accepted** |
| α: different binder names | accepted |
| hypotheses reordered (`ra, h0, rb, h1`) | **rejected**, `NotConvertible` |
| equation orientation swapped | **rejected**, `NotConvertible` |

This settles the charter's question. **Syntactic checking would reject the
first three rows** — including the one that makes ascription worth having,
where the author writes the statement in their own vocabulary (`bin_abs`)
rather than in the generated one (`Repr_BinNat::abs()`). Ascription is
therefore **definitional**, and the recorded consequence is honest: an
ascription may differ from the synthesized statement by arbitrary unfolding, so
it is a *legibility aid the kernel guarantees is the same statement*, not a
normal form. Orientation and argument order — the two things a reader actually
relies on — are pinned.

### 2.3 What a disagreement looks like

The failing check is a field type mismatch inside generated source, which is
the diagnostic `elab_generated` already wraps (`datarepr.rs:397-412`). The
round owes it one specialization, because "the generated declaration" is the
wrong frame when the user wrote the statement:

```
error: the ascribed statement is not the obligation `refines` of `impl add for BinNat`
  --> file.hthr:120:20
    |
120 |   proof Impl(add, BinNat).refines : add(bin_abs(ra), bin_abs(rb)) = bin_abs(body(ra, rb)) {
    |                                     ^^^ the sides are swapped
    |
  the obligation is:
    (ra: Bin) -> (rb: Bin) -> (h0: bin_inv(ra)) -> (h1: bin_inv(rb)) ->
      bin_abs(body(ra, rb)) = add(bin_abs(ra), bin_abs(rb))
```

The "the sides are swapped" line is aspirational (it wants
`issues/ai-facing-tooling.md`'s divergence trace); the two mandatory parts are
naming the slot and printing the obligation, both of which are available as
text today.

## 3. The slot path spelling — FINDING D

The charter asks for one designed spelling and names three candidates. The
lexer decided most of it:

| candidate | probe result |
|---|---|
| `Impl_BinNat_add::refines()` (plain namespace path) | **works today** — it is the elaboration target |
| `Impl(add, BinNat)::refines` | parse error at `::`: `::` never follows an application |
| `Impl<BinNat>(add)::refines` | same |
| `Impl[add, BinNat]::refines` | parse error: `[…]` is a single index, no commas |
| `add@BinNat::refines` | parse error — but *free* grammar space; lexes as `add`, `@`, `BinNat::refines` |
| `Impl(add, BinNat).refines` | **parses today**, reaches name resolution |
| `add.at(BinNat).refines`, `BinNat.impl(add).refines` | **parse today**, reach name resolution |

Two structural facts behind that table: `A::b` is one token joined in the lexer
(`lexer.rs:130-137`) with **one join only**, so no three-segment `::` path
exists to be spelled; and `@` is claimed as a **prefix** (fully-explicit call,
`parser.rs:2492-2505`), so a postfix `@` is unambiguous but overloads one sigil
with two unrelated meanings.

**RECOMMENDED**, in two parts:

1. **The slot path is a key, not an expression.** It is parsed in the `proof`
   declaration's own head position and resolved **in the slot table**, never by
   name resolution. This is what keeps `proof BinC.Succ_inv` away from the
   value-projection abort of §1.3: `BinC` names an assembled record *value*,
   and dot-projecting a theorem field off it is the live OOM — as a slot key
   the same text never becomes a projection.
2. **The spelling is `<owner>.<slot>`**, with the owner grammar per form:
   - `datarepr` and any future named obligation-bearing declaration: its own
     name — `proof BinC.Succ_inv { … }`;
   - `impl`, which has no name of its own: the applied form
     `Impl(<op>, <repr>)` — `proof Impl(add, BinNat).refines { … }`. It reads
     as §1.2's `Impl<Rp>(f)` registry type, it needs no minted name, and it
     parses today.

Rejected, with reasons: **plain minted paths** (`Impl_BinNat_add::refines`)
work today but force the author to know the mangling and to depend on a name
`issues/unnameable-generated-names.md` intends to mark as internal — the whole
point of a designed spelling is that the mangling stays the elaborator's
business. **`@`-forms** cost a small postfix production and read acceptably,
but spend the language's one `@` on a second meaning for a form that appears
once per obligation. **`::`-shaped applied paths** need a genuinely new
production for a token that today does not survive the lexer in that position.

**Reference position is deliberately not settled here.** Citing a certificate
inside another proof keeps today's `Impl_BinNat_add::refines()` in v1, and the
pretty spelling belongs to `issues/repr-access-spellings.md`, whose whole
subject is one designed spelling for a repr's legitimate access points; that
issue should take `<owner>.<slot>` as the *shape* to extend, and must dissolve
the value-projection hazard (fix `theorem-field-projection-oom`) before a dot
form can mean projection anywhere.

## 4. The `impl` surface

### 4.1 Grammar

```
impl <op> for <repr> { <clause>, … }          // the form today, unchanged
impl <op> for <repr> := derive();             // pinning: the transfer, at declaration time
impl <op> for <repr> { body := <e>, refines := via derived, … }

clause  ::= <name> := <expr>                  // ANY surface expression (§4.2)
          | <name> := ?                       // an open obligation slot (§1.2)
          | <name> := ?<name>                 // …with a local name
          | refines := via derived            // the §1.2 route (§4.3)

proof <owner>.<slot> { <expr> }
proof <owner>.<slot> : <statement> { <expr> } // checked ascription (§2.2)
```

`proof` is contextual, like every keyword here, and free: probed, `fn
proof(n: Nat) -> Nat { n }` still checks, and nothing in `lib/` uses the word.

### 4.2 Inline expressions: splice the AST, do not widen the printer — FINDING B

Today a clause is turned back into **text** by `spell_expr`
(`datarepr.rs:495-515`), which handles `Var`/`Num`/`App`/`TyApp`/`Dot` and
deliberately declines on everything else rather than fall back to `_` (which
would parse back as a *hole* and let inference invent content). Probed, all
three decline identically: `body := λ …`, `body := match …`, `body := { let … }`.

The blocker is only the round-trip. Probe 2 checked, in the exact shape the
emission uses — a 0-ary declaration whose result type is the synthesized field
type — an annotated λ, an **unannotated** λ, an inline `match`, a `let`-block,
and a term needing implicit-argument inference. All five check.

> **RECOMMENDED: splice the AST.** `elab_impl` already receives the clause as
> an `Expr` in the `ImplDecl`. Instead of `spell_expr` → string → concatenate →
> `parse_file`, generate the skeleton with a placeholder body, parse it, and
> **replace the parsed body with the user's `Expr`** before `elab_decl`. One
> patch point per clause, no printer, and every surface form the parser accepts
> works the day it is added.

Rejected: a **total expression printer**. It would have to cover ~22 `ExprKind`
variants plus patterns, arms and blocks, stay in sync with the surface forever,
and re-derive `spell_expr`'s decline discipline at every new form — all to
reproduce text that is immediately re-parsed into the AST we started with.

Recorded limitation, which the round should log as an issue rather than solve:
`Span` is a bare `(start, end)` with no file identity (`ast.rs:5-8`), so a
spliced subtree's spans index the *user's* file while the enclosing generated
declaration's index the generated text. Today `elab_generated` already discards
inner spans and re-reports at the owner declaration's span, so nothing breaks —
but the round should **improve** it to the *clause's* own span (available as
`cl.span`), and note that pointing at the failing sub-term inside an inline
proof wants span provenance, which is a separate change.

### 4.3 The routes, and what each leaves open

**`derive()`** — the pinning form. `reprgen(op, repr)` is already pure: it
reads the registries and returns source text including the `impl` block itself
(`reprgen.rs:158`, emission at `:468`). The surface form is therefore a
*caller*: elaborate the emission, or fail at declaration with the decline
reason verbatim (§6 on the shape of that failure). It fills **body and every
obligation** — the derived route's slots are never open.

**`via derived`** — probed (probe 6). Written at `refines`, it: requires the
derived `Impl` (deriving it silently if absent and in-fragment, exactly as
reprgen's phase 0 already resolves callees); opens **one** obligation, §1.2's
weak abs-image equation

```
(ra: Bin) -> (rb: Bin) -> (h0: bin_inv(ra)) -> (h1: bin_inv(rb)) ->
    bin_abs(bin_add_fast(ra, rb)) = bin_abs(bin_add_derived(ra, rb))
```

and synthesizes the certificate as `trans(<the obligation>, <derived
refines>)` — **no congruence step**, because the obligation is already stated
under `abs`. The landed hand-written `Bin` route proves *carrier* equality and
pays a `cong_bin_abs`; under the official statement that step disappears, and
carrier equality remains available as the strongest discharge (§1.2's settled
paragraph) since the author may ascribe and prove it by `refl` where `abs` is
injective on `inv`.

**At a repr-typed result, `via derived` does not fill `refines_inv`.**
`inv(body(x̄))` does not follow from an abs-image equation — that is precisely
what non-injective `abs` costs. So the route opens a second slot, and the error
that says so should say why. Probed as a separate theorem in probe 6.

**Plain terms** — inline or named, per §4.2, checked against the synthesized
statement with ordinary bidirectional inference (probed: an inline `trans` with
an uninferable implicit fails with the ordinary message, so clauses are in
checking position as they should be).

### 4.4 What today's form becomes, and byte-stability

**Decided: the named-artifacts block stays valid, unchanged, and stays the
generator emission target.** Every clause form is a widening; `impl add for
BinNat { body := bin_add_derived, refines := … }` means exactly what it means
today. This is not politeness — reprgen emits that text (`reprgen.rs:467-469`),
and the user's ratified motivation for the whole surface is that *tuned impls
will themselves be generated*, so the emission form must remain the plainest
one.

**Decided: reprgen and datarepr emissions are byte-identical after this round.**
No emitted text changes; the new surface adds callers and a slot table. The
`ImplSchema` extraction (§2.1) is behavior-preserving by construction, and
`crates/elab/tests/reprgen.rs` pins emissions by `contains`, so the round has a
cheap check that it stayed so.

One thing this **defers rather than decides**: reprgen names derived artifacts
at top level (`add_derived`, `add_is_rec`, `add_derived_refines`). Reached from
a user-written `impl add for BinNat := derive()`, those land in the user's
namespace. The Q2 verdict asks only that provenance be *distinguishable on
inspection*, which §6's listing satisfies with a registry-side `Provenance`
enum (`Derived | ViaDerived | Inline | Named | Proof`) — recorded, never
consulted by a certificate. Moving derived artifacts under the owner's
namespace is the better answer and belongs with
`issues/unnameable-generated-names.md`, whose marker they should carry; doing
it here would change emission bytes for no v1 benefit.

### 4.5 `runtime_fn`, as an aside only

Nothing here infers an entry to runtime; the verdict stands. The short form the
user allowed — "treat the derived definition as a runtime fn without rewriting
it" — has a natural spelling once slots exist (`runtime_fn f at Rp;`, resolving
the registry and erroring on an open slot per §1.5), and is **not** part of
this design. Recorded so the shape is not re-derived.

## 5. The second customer: `datarepr` clause laws

`datarepr` already has everything: generated statements (`abs_law_ty`,
`inv_law_ty`, `fold_law_ty`), a namespace, and a value assembled last. Slots
are the same three lines of state:

```heather
datarepr BinC for Nat {
    R := Bin, abs := bin_abs, inv := bin_canon,
    mk Zero := BNil, mk Succ := binc,
    Succ_abs := bin_succ_abs_canon,
    Succ_inv := ?,                      // open: proved below
    fold := bin_fold, fold_law := bin_fold_law_canon,
}

proof BinC.Succ_inv {
    λ a0 h0 => trans(j(bin_succ_abs(a0), λ y q => bin_of_nat(bin_abs(binc(a0))) = bin_of_nat(y), refl),
                     j(h0, λ y q => binc(bin_of_nat(bin_abs(a0))) = binc(y), refl))
}
```

**RECOMMENDED: v1, in the same round.** It is the cheapest possible proof that
the mechanism is general rather than an `impl` feature wearing a general hat,
and it is the shape §1.1's "a declaration form decides its slots" is designed
against. Two interactions to hold:

- **`repr-fold-via-abs-default` must land after, or with, this.** The two
  rounds want the same clause-reading code and they disagree about omission
  (FINDING C). If they merge, the rule is one sentence: *omitted takes the
  default, `?` opens a slot, and a clause that is neither is checked as
  today.* If they do not merge, this round must land the `?` marker first so
  the defaults round has an unambiguous omission to define.
- `datarepr`'s clause laws inherit §1.4 note 5's friction (a law clause's
  binder list includes the `inv` hypotheses even when unused). Slots do not fix
  it and do not make it worse; the `proof` form's λ can simply ignore them, as
  the example does.

## 6. Tooling

**The obligations listing.** `heather obligations <file>` (and `--json`, per
`issues/ai-facing-tooling.md`'s serializer), one row per slot:

```
owner                     slot          state   provenance  statement
impl add for BinNat       refines       open    —           (ra: Bin) -> (rb: Bin) -> …
impl add for BinNat       refines_inv   filled  proof       (ra: Bin) -> (rb: Bin) -> …
datarepr BinC             Succ_inv      filled  proof       (a0: Bin) -> (h0: bin_canon(a0)) -> …
datarepr BinC             Succ_abs      filled  named       …
impl length for ListTok   refines       filled  derived     …
```

The statement column prints the **synthesized source text** the slot table
already holds (§2.1). This is worth stating as a design property rather than an
implementation detail: because the schema is built as surface source, the
listing is legible **without** `issues/goal-display-decodes` — probe 8 shows
what the alternative looks like, an unsolved goal today printing
`Id[0](Nat; app(app(u5^{·^1}; …)))`. Any future path that renders a statement
from kernel terms inherits that problem; this one does not.

**Failures return data.** Three shapes, all keyed to a slot:

- *end of file with open slots* — the listing above, filtered to `open`, as the
  error;
- *a consumer of an uncertified owner* — "`length` at `ListTok` has an open
  obligation `refines`; it was declared at line N and nothing discharges it",
  plus the statement;
- *a declined `derive()`* — reprgen's reason verbatim (it already names the op,
  the constructor and the shape it could not read, `reprgen.rs:754`), tagged
  with the owner and slot it was asked to fill, so a tool can distinguish "the
  fragment does not cover this" from "you have not proved it yet".

## 7. Forward: intrinsic style (v2, precluded by nothing here)

`issues/intrinsic-certification-style.md` owns it. What this design owes it is
only that it stay reachable, and it does: an intrinsic definition elaborates by
splitting the recursion skeleton into values and proof components, and the
proof components have to *go* somewhere — the extrinsic artifacts. Slots are
that somewhere. The third route beside `derive()` and `via derived` is a clause
saying "this owner's obligations are filled by the splitter of definition `f`",
and it fits §1.1's state machine with no change: a route fills slots, the
kernel checks the filling, provenance records which route did it. Nothing in
§1–§6 assumes the filler is a human-written `proof` declaration.

## 8. Staging

### v1 — the mechanism, both customers (trigger: this design's acceptance)

In order, each step green before the next:

1. **`ImplSchema` extraction** (§2.1). Behavior-preserving; emissions
   byte-identical; `reprgen.rs` phase 3 rewritten against it. *Acceptance*: the
   existing 31 datarepr+reprgen tests unchanged and green.
2. **AST-splice for clauses** (§4.2), replacing `spell_expr` at the clause
   position in both `elab_impl` and `written_clauses`. *Acceptance*: an inline
   λ body, an inline `match` body, an inline `let`-block, and an inline proof
   term at `refines`, each at `Bin`; plus a negative control that an inline
   term of the wrong statement is still refused by the kernel, not by the
   printer.
3. **The slot table, `?`, and `proof <owner>.<slot>`** (§1, §3), for `impl`
   first. *Acceptance*: probe 5's shape as a test (open `refines`, intervening
   declarations, `proof` filling it, the value assembled); an unfilled slot
   erroring at end of file; a consumer of an uncertified `Impl` erroring by
   slot name; `fn proof(…)` still checking.
4. **Ascription** (§2.2). *Acceptance*: the four probe-4 rows as four tests —
   two accepted (δ, α), two rejected (reorder, orientation) — plus the
   diagnostic of §2.3.
5. **`datarepr` clause slots** (§5). *Acceptance*: `BinC` with `Succ_inv` open
   and proved below, checking; the same file with the proof removed, erroring.
6. **`derive()` and `via derived`** (§4.3). *Acceptance*: `impl length for
   ListTok := derive()` from a `.hthr` file — the first transfer ever requested
   from source; a declined `derive()` reporting reprgen's reason; probe 6's
   `via derived` shape with the abs-image obligation open, and its
   repr-typed-result sibling leaving `refines_inv` open too.
7. **`heather obligations`** (§6), text and `--json`.

Final verification is the full `scripts/test` (this touches the generators) and
`scripts/bench --check`.

### Deferred, with cost recorded

- **Span provenance for spliced ASTs** (§4.2): inline-proof errors locate to
  the clause, not the sub-term. Cost: one wrong-line hunt per failing inline
  proof; fixing it means giving `Span` a file identity, which touches every
  construction site.
- **Reference spelling** (§3): citing a certificate still spells the minted
  namespace path. Cost: minted names stay in hand-written proofs, exactly the
  friction `issues/repr-access-spellings.md` was filed for.
- **Derived artifacts in the owner's namespace** (§4.4): provenance is visible
  in the listing but not in the name. Cost: a `derive()` at the surface adds
  top-level names the user did not write.
- **Obligation-bearing record types written by hand** (§1.1): user classes with
  laws cannot use slots until open-ability is expressible in a hand-written
  `record`. Cost: the mechanism stays generated-only, which is all v1's
  customers need.
- **Cross-file discharge**: out by verdict, not by cost.

## 9. Rejected alternatives (shape claims only)

- **A statement-omitted `theorem`** as the filling form. Dropped pre-charter
  (user: a theorem without a visible statement is a trap). `proof` with
  optional ascription gives the same brevity and can always be made legible.
- **The trailing proof-keyword form** (`impl … { … } proving refines { … }`).
  Dropped in discussion round 2 as redundant with first-class `proof`
  declarations.
- **Omission as the open marker** — FINDING C, §1.2.
- **A total expression printer** to make clauses inline-able — §4.2.
- **Open-ability marked in the record type** — §1.1; revisit for hand-written
  law-carrying records.
- **`Impl(f, Rp)::slot` and `f@Rp::slot`** as *expression* forms: both need new
  grammar for a path that is only ever a key (§3), and the expression reading
  invites exactly the value projection §1.3 forbids.
- **Adjacency-only discharge**: weighed in §1.4, rejected because it costs the
  intervening lemma and saves no state.
- **Provenance consulted by resolution** (e.g. preferring hand impls over
  derived ones at a use site): never. Provenance is recorded for humans and
  tools; the registry has exactly one entry per key and the certificate is the
  same four names whatever produced them (`reprgen.rs:59-63`).

## 10. Probe log

Release CLI at `f42dcce`, every run `(ulimit -v 8388608 -t 120)`, fixture =
`bin_base!()` + `BIN_REPR` + `BIN_ADD` extracted from
`crates/elab/tests/support/mod.rs`.

1. **Today's `impl` block** — the named-artifacts form checks; `body := λ …`,
   `body := match …`, `body := { let … }` all die at ``clause `body` is not a
   shape this round can spell``; a repr-typed result without `refines_inv` dies
   with §1.2's message. → §4.1, §4.2.
2. **The 0-ary emission shape with inline content** — annotated λ, unannotated
   λ, inline `match`, `let`-block, and an implicit-bearing term all check
   against a synthesized Π type. → FINDING B, §4.2.
3. **Slot-path candidates** — the table in §3. `::` after an application is a
   parse error in every arrangement; `.`-chains parse and reach resolution;
   `A::b` is one lexer token with one join; `@` is a claimed prefix. →
   FINDING D, §3.
4. **Ascription equality** — the four-row table in §2.2, by cross-casting the
   generated `refines` into hand-written variants. δ and α accepted; reorder
   and orientation `NotConvertible`. → §2.2.
5. **The open-slot state machine, by hand** — record type with obligation
   statements, `body` filled at declaration, unrelated declarations
   intervening, the two theorems filled later *in the user's vocabulary*, the
   value assembled last: checks. → §1.1, §1.4, §2.2.
6. **`via derived` synthesis** — the abs-image obligation, `refines =
   trans(obligation, derived_refines)` with no congruence step, and
   `refines_inv` as a separate obligation: all check. → §4.3.
7. **`proof` as a keyword** — `fn proof(n: Nat) -> Nat { n }` checks; no
   occurrence of the word in `lib/`. → §4.1.
8. **`?` in clause position** — `refines := ?` and `refines := ?later` parse
   and reach `spell_expr`; a `?` in a *body* prints an undecoded kernel goal.
   → §1.2 (grammar cost zero), §6 (why the listing prints source text).

Nothing probed refuted a settled frame item; the stop-condition did not fire.
Two open items changed under probe evidence (§1.2's marker, §3's spelling) and
one section (§2.1) exists because a probe found a duplication the charter did
not know about.
