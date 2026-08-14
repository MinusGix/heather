# Non-`Nat` embeddings for the certifying generator

Design for `docs/certifying-generator-design.md` §8 item 2 — "other tier-0/1
inductives: per-type `embed_T` (a derived artifact), `CompileTK` records per
signature until bundled records exist". Round pattern as usual: this document
first, the implementation against §9's acceptance list.

This is the **first fragment feature since the Rust transcriber walker was
deleted** (`issues/retire-rust-transcriber.md`, closed), so it is also the
first test of the frozen-walker rule: the analysis — which signatures are in
the fragment, and what a body transcribes to — lands **in-language only**
(`lib/certgen_code.hthr`), and Rust gains nothing but names, rendering and
fixture arithmetic (`docs/certgen-transcriber-in-language-design.md` §5,
`docs/certgen-cert-expression-design.md` §3). Where a check *looks* like
analysis but is really a spelling question, §6 says so out loud rather than
letting it drift back.

The principle inherited from `issues/certifying-generator.md` and protected by
every decision below: **the generator is untrusted.** A wrong embedding, a
mis-numbered tag, a spec spelled against the wrong type — each is a certificate
the kernel refuses, never an unsound theorem. Declining is a supported answer
and negative controls are mandatory.

---

## 1. The finding that sizes the round: `Val` needs nothing

`lib/ir_v1.hthr`'s value domain is

```heather
inductive Val { VNil, VCons(head: Val, tail: Val), VCon(tag: Nat, fields: Val) }
```

— *untyped constructor trees* (doc §4). `embed_nat` is not a privileged
primitive; it is one three-line function that happens to be the only embedding
the library owns:

```heather
fn embed_nat(n: Nat) -> Val {
    match n { Zero => VCon(0, VNil), Succ(k) => VCon(1, VCons(embed_nat(k), VNil)) }
}
```

So "crossing a source inductive's values into the IR's value domain" is, for
any tier-0 or tier-1 source type, **exactly the same shape of function**:
constructor `i` becomes `VCon(i, <its fields, embedded, as a VCons chain>)`.
`simulate` already expresses everything needed to consume such values —
`LetCon` builds one at an arbitrary tag, `LetMatch` scrutinizes one at an
arbitrary tag, and neither ever mentions `Nat`.

**Consequence, and it is the whole reason this stage is affordable: the blast
radius on `lib/ir_v1.hthr` is zero.** No `Val` extension, no re-proof of the
∃-composition kit, no change to `Converges`, `eval`, `fuel_monotone` or any
kit lemma. `embed_T` is a *generated* declaration that lands in the emission
beside the IR, exactly as §8 item 2 said ("a derived artifact"). The one thing
the library gains is nothing.

This was checked before scoping, because the opposite answer (a typed value
domain, or per-type `Val` constructors) would have made this a multi-round
programme with a proof-migration in it.

## 2. Scope: what lands, and why exactly this

**In this round.** A fragment function's **result type** may be a *tier-0
enumeration*: a user `inductive D { c₀, …, c_{n-1} }` that is

- non-recursive (tier 0 — the lowering is sums-of-Σs, not `Wf`),
- unindexed and unparameterized,
- `n ≥ 1` constructors,
- **no constructor fields**.

Parameters stay `Nat`; structural recursion stays on a `Nat` parameter.

**Deferred, with homes** (§8 has the full list): non-`Nat` *parameters*;
constructor *fields*; tier-1 (recursive) source types; parameterized types;
cross-function composition at a non-`Nat` result.

The fields cut is the one this document changed its mind about, and the reason
is recorded rather than smoothed over — §2.2.

### 2.1 Why the result position and not the parameter position

The two positions are not symmetric, and the asymmetry is a *lowering* fact,
checked rather than assumed (probe, 2026-08-12):

- A **`Nat` match** — which is what a fragment body's one `match` is — lowers
  to `Term::ElimNat`, whose motive is the result type spelled **inline**
  (`Σ(Unit).Unit + Σ(Unit).Unit` for `Bool`), with no `El(D#tycode^δ)`
  anywhere. The walker already ignores the motive (`ta_elim` binds it and
  never reads it), so a non-`Nat` result changes *nothing* about the
  eliminator: only the arms' bodies change, from `Zero`/`Succ` spines to
  `Inl`/`Inr`/`Pair`/`Triv` spines.

- A **match on an inductive parameter** lowers to `Term::Case`, and three
  separate things break at once: the motive is `El(u^δ)` — the 2026-08-12
  `GenDef::TyCode` reference — so the walker's type side would have to walk a
  code *term* under a constant motive; the arms bind a Σ-typed variable and
  read their fields by `Fst`/`Snd` projections, which is a second binder
  convention the marker pass does not have; and an enum with more than two
  constructors is a *nested* `Case` whose inner scrutinee is a fresh bound
  variable, which is precisely the "nested eliminator" the fragment declines
  (`lib/certgen_code.hthr` convention 1). Any one of those is a round.

So the smallest honest cut that exercises the general mechanism —
`embed_T`, a per-signature `CompileTK`, a certificate whose goal is
`VCons(embed_T(f(a)), VNil)`, and tags beyond 0/1 — is the result position. It is a real end-to-end `Compile` instance over a
non-`Nat` type, which is the acceptance the charter asks for.

### 2.2 Why constructor fields are OUT — the design's one reversal

The first cut of this document put one `Nat` field in, on the argument that a
nullary-only enum makes `embed_T` a tag table and under-tests the word
"embedding". The implementation refuted that on cost, and the refutation is
worth keeping because it is a size law, not an accident.

A constructor with fields makes the walker's payload state carry a compiled
**prefix** (`Pre`) and a reference list (`PRefs`), because a field is an
arbitrary expression with its own instructions, which have to be merged and
re-based exactly as a call's arguments are. That grows `TA` — the walker's one
constant motive — by three constructors carrying two more `Pre` fields, and
`issues/wf-field-conversion-cost.md`'s law is Θ(arms × |lowered field type|)
*per `match` on the container*, with `Pre` the largest type this file has.
Measured, one fixture at a time against the same session:

| | `lib/certgen_code.hthr` elaboration | generating one fixture |
| --- | --- | --- |
| before the round | 36 s | ~10 s |
| with fields (the first cut) | 75–89 s | 24 s, and **114 s** for the one fixture that had a field |
| nullary only (landed) | 42 s | ~3 s |

At the with-fields numbers the certgen test binaries do not fit inside
`scripts/test`'s **300-second per-process `ulimit -t`** — which is how the
round found out, as a `SIGKILL` rather than a slow run. So fields are deferred
to a stage that can pay for them, and the cut buys back the mechanism's whole
point at a fifth of the cost: `embed_T` is still a per-type derived artifact,
the certificate's goal is still a non-`Nat` embedding, and the tags still run
past 0/1.

*(2026-08-13, second note — **this table is superseded as the reason fields are
out**, and `docs/certgen-ctor-fields-design.md` is the record. The feature round
re-probed as the note below told it to, with the feature implemented rather
than extrapolated: the elaboration cliff this table prices is **gone** (the
widened file costs ~30% more on a file an order of magnitude cheaper than the
one measured here, nowhere near any rail), and what defers the stage instead is
the **in-language evaluation** cost of generating a fixture with a field, which
no elaborator spelling round touches. Read the "generating one fixture" column
as the surviving half of this table and the elaboration column as history; the
numbers, old and new, are in `issues/certgen-harness-cost.md`.)*

*(2026-08-13, third and last note — **fields LANDED**, so the surviving half of
this table is history too. The evaluation cost the note above handed the stage
to was removed at the analyzer seam
(`docs/analyzer-evaluation-design.md`): the elaborator runs the analyzers in
the kernel's value domain instead of its rewriter, and every fixture in that
column — including the two-field one that did not finish at all — now
generates in tens of milliseconds. Neither column of this table describes the
system any more; §8's entry is the current state.)*

*(2026-08-13, [[wf-field-conversion-cost]]'s component-respell round: the
size law this table prices was cut at its constant — statements, `App`
annotations, projection chains, field tuples and injection spines now
reference registered lowerings instead of inlining them, and the lowering's
level joins are canonical. The with-fields configuration was not re-run (the
first-cut walker no longer exists), but the law's cost sites measured 2–5x
cheaper on this file's own successors, so this table's numbers describe the
old elaborator; the feature round that picks fields back up should re-probe
before treating the 300-second rail as binding. See that issue's 2026-08-13
log entry.)*

Two smaller findings from the same measurements, kept because they will be
true again next time:

- **A `match` on `TA` nested inside another `match` on `TA` multiplies the
  law.** The three-level `ta_pair` of the first cut was on its own worth more
  than everything else the round added; flattening it into one-`match`
  functions is now a stated rule in the file.
- **`ta_val` returning `TA` was costing three extra `TA` eliminations.** It now
  returns a two-constructor `VOut`, which is a strict improvement *on the
  pre-round file too* and is why the landed cost is only +17% rather than +40%
  despite two more `TA` constructors.

### 2.3 Why every slot's embedding is decided by position

With a non-`Nat` result `R`, every temporary a fragment body binds is
`R`-typed (a `LetCon` builds an `R`; a self-call returns an `R`), while every
parameter and the `Succ` arm's `gk` is `Nat`. That two-class split is decided
by *position alone* — no inference over the chain — which is what lets the
renderer spell `embed_nat(a)` for a parameter and `embed_R(f(a))` for a
temporary. When `R = Nat` the two classes coincide, so every existing emission
(`add`, `dbl`, `seven`, `third3`, `mul`) is byte-identical.

What would break it is a **foreign call** out of an `R`-result function:
`add(a, a)` binds a `Nat` temporary in a chain whose other temporaries are
`R`s, and the renderer would need a per-slot type it can only get by
inference. With fields deferred there is nowhere for such a temporary to be
*used* — a `Nat` value cannot reach an `R`-result `Ret` — so the shape is
already impossible, and the two boundaries that make it so are honest declines
in their own right: a callee whose result is not `Nat` has no callee marker
(the marker convention is a closed `Nat → … → Nat` chain), and the readback
declines a foreign call from an `R`-result function outright. Cross-function
composition at a non-`Nat` result therefore lands with fields, not before.

## 3. `embed_T`, concretely

Emitted once per result type, into the emission's *support* text (§6), ahead
of the record that mentions it:

```heather
fn Flag_gen_embed(gx: Flag) -> Val {
    match gx {
        Off => VCon(0, VNil),
        On => VCon(1, VNil),
    }
}
```

The name is `{T}_gen_embed`, in the emission's existing `_gen_` namespace, so
it cannot collide with a user's `embed_flag`. The scheme is written for fields
already (`c(a, b) ↦ VCon(i, VCons(embed_nat(a), VCons(embed_nat(b), VNil)))`),
so the deferred stage inherits the emitter unchanged; what it has to build is
the *walker* side. For `T = Nat` the embedding is `embed_nat` and nothing is
emitted — the library's own. That collapse is
deliberate: **`Nat` is not a special case in the emitters, it is the
zero-th instance of the mechanism**, carried as an ordinary "result type
description" (name, embedding function name, constructor table) so that every
format string has exactly one code path.

**Tag order is the lowering's order**, i.e. declaration order: the readback's
pinned reading (`certgen.rs`'s reader block) already says `inr^i(inl(payload))`
picks constructor `i` of a right-nested sum, and the walker mints its tags the
same way (§4). `embed_T`'s `match` is written in declaration order, so
`match x { c_i(…) => VCon(i, …) }` and the walker agree by construction — and
if they ever did not, the emission's exactness fixture (a `refl` on a concrete
run) is what refuses it.

### The equiv/`Converges` statement

Unchanged in shape, changed in one token. The invariant of a generated
function `f : Nat → … → Nat → R` is

```
theorem f_gen_conv(a1: Nat) : (a2: Nat) -> … -> (tail: Val)
    -> Converges(f_gen_prog(),
                 VCons(embed_nat(a1), … VCons(embed_nat(ak), tail)),
                 f_gen_body(),
                 VCons(T_gen_embed(f(a1, …, ak)), VNil))
```

— the environment is embedded parameter-wise (`Nat`), the *output* is embedded
at `R`. Intermediate goals (`letcon_conv`'s `vs`, `letcall_conv`'s `ws`,
`letmatch_conv`'s arm goal) follow the same rule: a slot's embedding is
`embed_nat` if it is a parameter or `gk`, and `T_gen_embed` if it is a
temporary (§2.3). The kit lemmas are used verbatim — they quantify over `Val`
and never mention any embedding.

And the record:

```heather
record CompileNat1Flag(f: Nat -> Flag) {
    prog: Prog,
    entry: Ir,
    cert: (a1: Nat) -> Converges(prog, VCons(embed_nat(a1), VNil),
                       entry, VCons(Flag_gen_embed(f(a1)), VNil)),
}
```

`CompileNat{k}` for a `Nat` result (unchanged, `CompileNat2` still declared in
`lib/ir_v1.hthr`), `CompileNat{k}{T}` otherwise — "`CompileTK` records per
signature until bundled records exist", as §8 item 2 wrote it. The record is
the **checking position** of `docs/testing-generated-terms.md`: a wrong
embedding dies in the `cert` field's type.

## 4. The transcriber's widening (in-language)

`lib/certgen_code.hthr`, four new arms and two new accumulator states. The
motive stays the single constant `TA`, so nothing about the 52-branch shell
changes.

Constructor values arrive, per the tier-0 lowering, as
`inr^i(inl(Pair(<nominal tag>, Triv)))`. The last constructor of an `n`-ary
sum has no trailing `inl`, and a **one**-constructor enum is the bare payload
with no sum at all. The nominal tag (`docs/inductive-tier0-lowering.md` §3.3)
is **not** a bare `Triv`: it is the declaration index's binary digits as a
`Pair`-spine of `Triv`s, which the first implementation got wrong and a
session with more than one declared inductive immediately exposed. So the
recognizer's test is "the first component contains no value", not "the first
component is `Triv`".

New states on `TA`:

```heather
TPure                 -- built from `Triv` and `Pair` alone: a tag spine, and
                      -- (with no fields) a whole constructor payload
TCtor(tag: Nat)       -- that payload with its index
```

Neither carries a prefix, which is the §2.2 decision in one line.

New arms and helpers:

| node | helper | rule |
| --- | --- | --- |
| `tm_triv` | `ta_triv()` | `TPure` |
| `tm_pair(S, T, a, b)` | `ta_pair(a, b)` | pure over pure is pure again; a pair with a *value* in it is a constructor field, and declines |
| `tm_inl(A, B, t)` | `ta_inl(t)` | a payload becomes `TCtor(0)`; an already-indexed value declines |
| `tm_inr(A, B, t)` | `ta_inr(t)` | `TPure ↦ TCtor(1)`, `TCtor(g) ↦ TCtor(Succ(g))` |

so `Red = inl(P)` reads 0, `Green = inr(inl(P))` reads 1, `Blue = inr(inr(P))`
reads 2, and a one-constructor enum's bare `P` reads 0 — the same numbering
`inr^i(inl(·))` gives, derived rather than restated.

Rendering: a `TPure` or `TCtor(g)` used as a value is one more instruction,
`PCon(g, QNil, PEnd)`, whose own value is itself — the same shape
`ta_call_fin` already emits for a saturated call. Both land in `ta_val`, which
this round also **narrowed to a two-constructor result type `VOut`**: its three
consumers used to `match` on `TA` again, and `TA` is the expensive type (§2.2).

**What did not have to change**: `ta_marker`, `ta_elim`, `ta_finish`,
`render_pre`, `self_args`, `dist` — the whole level/distance machinery, which
is about the environment layout and knows nothing about types. And `ta_succ`
keeps its numeral fusion untouched, so every existing emission is
byte-identical.

**The type branches stay in the default arm.** `ty_sum`/`ty_sigma`/`ty_unit`
are *not* written in the transcriber's shell: the only type it ever meets is
the eliminator's motive, which `ta_elim` binds and ignores. Writing them would
buy a `TStuck` that is already there.

## 5. The signature checker's widening (in-language)

`check_sig` walks the fn's type as code (the reflection primitive), and the
fragment rule lives whole in `lib/certgen_code.hthr`. Today it accepts
`Nat → … → Nat` via a two-state `SigOut` used as its own accumulator. That
conflation stops paying: recognizing a tier-0 lowering needs intermediate
states, so the walk gets a proper accumulator and `SigOut` becomes the answer.

```heather
inductive SA {
    SNo, SNat,
    SPure,                    -- built from `Unit` and Σ alone: `Unit` itself,
                              -- a nominal-tag type, a no-field payload
    SEnum(k: Nat),            -- a right-nested sum of k payloads
    SFn(arity: Nat, res: Nat) -- Nat → … → Nat → R
}
inductive SigOut { SigNo, SigYes(arity: Nat, res: Nat) }
```

`res` is a **single `Nat`**: `0` means the result is `Nat`, `k ≥ 1` means it
is an enumeration with `k` constructors. Two reasons, and the second is a size
law rather than taste. It keeps the whole verdict flat — no inductive-typed
field on either type — which matters because
`issues/wf-field-conversion-cost.md`'s law says a `match` on a container pays
Θ(arms × |lowered field type|); every field here is a `Nat`, whose lowering is
one node. And a zero-constructor result (`Empty`) is not a thing a fragment
function can return anyway, so `0` is free to mean `Nat`.

The rules (all total, `SNo` propagating):

- `ty_nat → SNat`, `ty_unit → SPure`;
- `sig_sigma(SPure, SPure) = SPure` and nothing else. A Σ with a `Nat` in it is
  a constructor **field**, deferred by §2.2, so it declines here — which is
  what puts "no fields" in the *library's* rule rather than in Rust's.
- `sig_sum(SPure, SPure) = SEnum(2)`; `sig_sum(SPure, SEnum(k)) = SEnum(Succ(k))`;
  else `SNo`. (Right-nested, and only the last summand is bare.)
- `sig_pi(dom, cod)`: `dom` must be `SNat`; `cod = SNat → SFn(1, 0)`,
  `SPure → SFn(1, 1)` (a one-constructor enumeration has no sum),
  `SEnum(k) → SFn(1, k)`, `SFn(a, r) → SFn(Succ(a), r)`; else `SNo`.
- `sig_finish(SFn(a, r))` with `a ≥ 1` is `SigYes(a, r)`; everything else is
  `SigNo` — which is where "a nullary fn has no calling convention to certify"
  still lives.

So `Flag`'s `Σ(t).Unit + Σ(t).Unit` reads `SEnum(2)` and `Sign3`'s
right-nested sum reads `SEnum(3)`, while `Peek {PNone, PSome(k: Nat)}` declines
at its second payload. A **tier-1** result (`Refs`, `Ir`) lowers to `Wf`, hits
the default arm and declines; a higher-order domain still declines exactly as
before.

Three arms are added to the `check_sig` shell (`ty_sigma`, `ty_sum`,
`ty_unit`); the shell is otherwise untouched and the motive is still one
constant type.

## 6. What stays in Rust, and the line it is on

Unchanged homes (`docs/certgen-transcriber-in-language-design.md` §5): scope
resolution/marking, names, the emitters, the fixture arithmetic. What this
round *adds* to Rust, and why each is a name and not an analysis:

1. **The result type's description** — its surface name (read off the
   declaration's `result` type), its embedding function's name, and its
   constructor table (name and field count each, from the elaborator's
   inductive registry). Every one of those is an identifier: Ψ carries a
   lowering, not the identifiers it was written with, which is the same
   sentence that put `surface_params` in Rust and derived spec strings at the
   rim. `embed_T`'s text, `con_spec`'s `PSome(gk)`, and the record's name are
   all made of exactly this.

2. **The tag→name check** in `chain_from_rir`. It was already there — as
   `matches!(tag, 0 | 1)`, "constructor tag {n} is not a `Nat`" — and it
   generalizes to "tag `t` with `m` arguments must name a constructor of the
   result type". It is the *spelling* boundary: a tag the renderer cannot name
   is a certificate it cannot write.

3. **The agreement property**, §4-of-the-reflection-design style, one line
   wider. In-language `check_sig` answers `(arity, res)`; Rust resolves the
   declaration's result type and computes `(arity, ctor count or 0)`. Both
   accept with equal pairs, or both decline, or it is a loud
   `signature disagreement` — asserted never to fire on any fixture, positive
   or negative.

4. **The fixture evaluator's value model.** `V(u64)` — a `Nat` — becomes
   `V { tag, fields }`, a constructor tree, which is what the IR's `LetCon`
   always built and what `simulate` always evaluated. `Nat` is the two-tag
   instance of it. This is arithmetic for a literal fuel, not analysis.

5. **The marker pass's node whitelist** gains `Inl`/`Inr`/`Pair`/`Triv` (it
   is a structural recursion with an explicit whitelist, and an unlisted node
   is a decline), and the `ElimNat` motive check widens from "`Nat` on the
   nose" to "`Nat`, or a tier-0 lowering shape". The motive is never marked —
   the walker ignores it — so this is a *permission*, not a computation.

Nothing here decides which functions are in the fragment. That decision is
`check_sig` and the walker's decline set, and it stayed where the frozen-walker
rule put it.

## 7. What the generator declines, and why that is the architecture

Declines added by this round, each an honest answer rather than a gap:

- **a non-`Nat` parameter** — unchanged (`sig_pi`'s domain rule), and now the
  *only* signature decline that is about a position rather than a type;
- **a tier-1 result type** — `Wf` is not a shape `sig_*` has a case for;
- **a non-`Nat` field** — `sig_sigma` declines a field chain whose head is not
  `SNat`;
- **a parameterized or indexed result type** — its lowering is not a bare
  sum-of-Σs at the use site, so it declines by the same default arm;
- **a foreign call from a non-`Nat`-result function** — §2.3, at the rim;
- **a constructor tag the result type cannot name**, or with the wrong number
  of arguments — at the rim, where the spelling lives;
- **a returned slot whose class does not match the result type** (a `Ret` of a
  `Nat` parameter from an `R`-result function) — at the rim.

Each of the last three is a *readback/renderer* decline, which is the weaker
kind: the stronger property is that even a decline that failed to fire
produces a certificate the kernel refuses. §9 item 5 pins that with mutations
on a non-`Nat` emission, not only on the `Nat` ones.

## 8. Deferred, with homes

- **Non-`Nat` parameters** (and therefore matching on a non-`Nat` scrutinee) —
  blocked on `Term::Case`: the `El(D#tycode^δ)` motive, the Σ-projection arm
  binders, and the nested-`Case` shape for `n > 2`. It also wants a
  *per-parameter* type list in `SigOut`, which the flat `(arity, res)` verdict
  deliberately does not carry. Home:
  `docs/certifying-generator-design.md` §8 item 2, restated as its own stage;
  the surface work is a `tm_case` arm and a second marker convention, both of
  which want `issues/code-variable-analysis-api.md`'s closed-term substitution
  more than they want this round.
- **Tier-1 (recursive) source types** — **LANDED, 2026-08-14**
  (`docs/certgen-tier1-source-types-design.md`), with two corrections to this
  entry's forecast: the walker reads the *recursor's step*, not `Supf` values
  (fragment inputs arrive as eliminations, with the accessors as markers),
  and the different-`CertOut`-shape cost was one constructor. `embed_T`
  becoming structurally recursive was right.
- **Constructor fields** — **LANDED, 2026-08-13**, in
  `docs/certgen-ctor-fields-design.md`'s second round, at the design that
  document already carried: one new `TA` state, no new arm, and the emitter
  side untouched because it was written for fields one stage early. §2.2's
  price was never paid — the elaboration cliff it measured had been taken by
  two spelling rounds, and the *evaluation* cliff that replaced it was removed
  at the analyzer seam (`docs/analyzer-evaluation-design.md`) rather than
  inside this walker.
- **Fields of another enum**, once fields land — a composition step over §3's
  `embed_T`; no new mechanism, real emitter work. (Confirmed by the fields
  round: the *walker* reads such a field with no change at all; what is missing
  is per-field embeddings at the rim — `docs/certgen-ctor-fields-design.md` §6.)
- **Cross-function composition at a non-`Nat` result** — §2.3; **LANDED with
  fields, 2026-08-13**, exactly as this entry predicted the two would. Cheaper
  than predicted, and now observed rather than designed: it needs no shared
  data structure, only the positional rule of
  `docs/certgen-ctor-fields-design.md` §5, and `viafield` — a foreign call
  feeding a constructor field — generates and kernel-checks end to end.
- **Type-parameterized result types** — monomorphized at each use site
  (`docs/inductive-tier0-lowering.md` §2), so `Option<Nat>` has a lowering the
  walker could read; what it does not have is a *name* the emitter can spell
  for `embed_T`. Home: `issues/datarepr-separation.md`, where representation
  naming lives.

## 9. Acceptance

1. **`lib/certgen_code.hthr` states its own acceptance**, as it does today —
   `refl` theorems for: a two-constructor value at tag 1 and at tag 0, a
   one-constructor enumeration's bare payload, a three-constructor value at
   tag 2, the same constructor at a **non-zero nominal tag** (the finding of
   §4), and the two declines (`ta_inl` over an already-indexed value; a
   payload with a field in it). Plus the signature pins re-spelled onto `SA`:
   `Nat → Nat` is `SigYes(1, 0)`, a two-constructor result is `SigYes(1, 2)`,
   a three-constructor lowering is `SEnum(3)`, a one-constructor result is
   `SigYes(1, 1)`, a tag spine is `SPure`, and a constructor field declines
   both on its own and through the enumeration around it.
2. **The existing five emissions are byte-identical** (`add`, `dbl`, `seven`,
   `third3`, `mul`), and the `IR_*` literals and every existing mutation
   control stay green untouched. This is the round's regression bar: `Nat` is
   the zero-th instance of the mechanism, so it must not move a byte.
3. **End-to-end generated `Compile` instances over non-`Nat` types**, elaborated
   and kernel-checked in `crates/elab/tests/certgen_nonnat.rs`:
   - `is_zero(n: Nat) -> Flag` — the two-constructor case, `CompileNat1Flag`;
   - `sign(n: Nat) -> Sign3` — three constructors, so a tag of 2, which no
     `Nat` emission can produce;
   - `tt(n: Nat) -> Flag` — a **self-call at a non-`Nat` result**, so the
     induction hypothesis is consumed at goal
     `VCons(Flag_gen_embed(tt(gk)), VNil)`.
4. **The four axes** (`docs/testing-generated-terms.md`): literal *and* neutral
   — the exactness fixtures run at literal arguments while every invariant is
   open in its parameter and in `tail`; **open element type** — the emitted
   record is checked at the *declared* spec function, not at a closed value;
   **checking position** — the instance value is checked against
   `CompileNat1Flag(is_zero)`, where a wrong embedding dies; **negative
   controls** — item 5.
5. **Mutation controls on a non-`Nat` emission** (not only on the `Nat` ones):
   a wrong constructor tag in the IR, and a perturbed fixture claim, each
   refused by the kernel.
6. **Decline cases**, each attributed to the in-language checker and each
   asserted *not* to be a signature disagreement: a tier-1 result type, a
   constructor with a field, a non-`Nat` parameter (unchanged), a nullary fn
   (unchanged). Plus the rim decline: a call to a callee whose result is not
   `Nat`.
7. One flip recorded rather than hidden: `fn tocmp(n: Nat) -> Cmp { CLt }`,
   until this round a *decline* fixture in `crates/elab/tests/certgen.rs`, is
   **in the fragment** after it. It is replaced by a decline this round still
   makes (a tier-1 result type), and the flip is noted at the site — the same
   discipline the transcriber round used for the two quotation tests it
   flipped.
8. Full `scripts/test` green, including both whole-library acceptance tests.

## 10. Cost, recorded because it lands on a rail

Not a perf round, and nothing here was measured out of curiosity: every number
in §2.2 was taken because a test binary was being `SIGKILL`ed by
`scripts/test`'s per-process `ulimit -t`. What lands:

- `lib/certgen_code.hthr` elaborates in ~42 s where it took ~36 s, i.e. **+17%**
  for two more `TA` constructors and six more functions — the `VOut` narrowing
  of `ta_val` pays most of the widening back.
- Generating a non-`Nat` fixture costs ~3 s, *less* than a `Nat` one (~10 s),
  because these bodies are two instructions.
- The non-`Nat` acceptance lives in a **binary of its own**
  (`crates/elab/tests/certgen_nonnat.rs`) so that it gets its own 300-second
  rail; its expensive half joins `scripts/test --fast`'s skip list beside
  `emissions_check_and_controls`, which is the same acceptance class.

`issues/certgen-harness-cost.md` is where the levers live, and the two size
findings of §2.2 belong to `issues/wf-field-conversion-cost.md`'s open ledger.
