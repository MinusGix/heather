# Constructor fields for the certifying generator — design, a measured deferral, and the round that landed it

> **Status, 2026-08-13 (second round): LANDED.** §§2–7 are the shipped
> design, unchanged from the deferral round — not one line of the walker or
> the rim was redesigned. What changed is the cost §8 measured, which
> `docs/analyzer-evaluation-design.md` removed at the analyzer seam: the
> fixtures §8 lists at 24–135x, and the one that did not finish at all, now
> generate in tens of milliseconds each. §9's checklist was worked through
> in order and is recorded there with its verdicts, including the two
> §5 predictions — `pack` and `viafield` — which held end to end on the
> first run. The rest of the document is left as it was written, because the
> deferral's reasoning is the reason this round existed.


Design for `docs/certifying-generator-design.md` §8 item 2's **second stage**:
a fragment function's result type may be a tier-0 enumeration whose
constructors take fields. The stage was designed in and cut on cost by the
non-`Nat` embeddings round (`docs/certgen-non-nat-embeddings-design.md` §2.2),
which recorded the cut as a *size law* and told the next round to **re-probe
before trusting the recorded cliff**, because two elaborator spelling rounds
(`issues/wf-field-conversion-cost.md`, `issues/wf-shape-annotation-slots.md`)
had since cut the constant that law was priced under.

**This round re-probed, and the verdict is: the recorded cliff is gone and a
different one is in its way.** The elaboration cost §2.2 measured — the reason
the first cut `SIGKILL`ed at `scripts/test`'s per-process rail — has collapsed
to a rounding error. What has *not* moved, because no spelling round touches
it, is the **in-language evaluation** cost of running the transcriber over a
body that builds a constructor with fields: generating one such fixture is
between one and two orders of magnitude more expensive than generating
anything the fragment ships today, and it grows steeply with the payload's
structure. So the stage is deferred again, on a **different and better
attributed** measurement, with the design below fully worked out and
prototyped rather than sketched.

Everything in §§2–7 was *implemented and checked* during the round, and the
implementation was then reverted rather than landed. What was checked, so that
the next round knows what it is inheriting:

- the walker's five new `refl` pins — one field, two fields with their slot
  order, a computed field, a field that is a cross-function call, and the
  decline for a field that is not a value — **all held on the first run**, as
  did every pre-existing pin (the `Nat` transcriptions and the field-free
  non-`Nat` ones are byte-identical);
- a generated `Compile` instance for a one-field constructor —
  `fn peek(n: Nat) -> Peek { match n { Zero => PNone, Succ(k) => PSome(k) } }`
  — was elaborated and **kernel-checked end to end**, `Peek_gen_embed`,
  exactness fixtures, `letcon_conv` over a field argument, the
  `CompileNat1Peek(peek)` instance and all;
- the transcriptions of a two-field constructor and of a computed field were
  read back through the rim and matched the designed layout exactly. The
  *foreign call in a field* — the cross-function composition of §5 — was
  checked at the walker only (its `refl` pin), because no fixture combining it
  with a field ever finished generating; §5's rim rule is therefore designed
  and implemented but not exercised end to end, and that is the one thing the
  next round should re-check first.

It is recorded here so that the round which pays the evaluation cost — or
removes it — does not re-derive any of it. §8 is the measurement and the
verdict; §9 is what would unblock it.

The principle this round is measured against, as every round on this generator
is: **the generator is untrusted.** Every decision below is a decline or a
spelling, never a soundness argument.

---

## 1. What "constructor fields" means here, and what was already done

`Val` is untyped constructor trees (`docs/certgen-non-nat-embeddings-design.md`
§1), so the *emitter* side of this stage has existed since that round:

- `ResTy::embed_text` writes `c(a, b) ↦ VCon(i, VCons(embed_nat(a),
  VCons(embed_nat(b), VNil)))` at any arity — it was written for fields
  deliberately, one stage early;
- `ResTy::ctor_spec` already renders a constructor spec with arguments, and
  already refuses a field spelled from a non-`Nat` slot;
- the readback's `chain_from_rir` already checks a `LetCon`'s **arity**
  against the named constructor;
- the marker pass already carries `Pair`/`Inl`/`Inr`/`Triv` through its
  whitelist.

So the stage is, as §8 of that document said, **a walker stage** — plus one
question the walker does not answer, which §5 below is about.

## 2. Scope

A fragment function's result type `R` may be a tier-0 enumeration —
non-recursive, unindexed, unparameterized, `n ≥ 1` constructors — whose
constructors take zero or more fields, **each of type `Nat`**. Parameters stay
`Nat`; recursion stays structural on a `Nat` parameter.

A field may be any expression the fragment already compiles: a parameter, the
arm's `gk`, a numeral, a `Succ` chain, or a **cross-function call**. It may not
be a self-call, for a reason that is a type fact rather than a restriction: a
self-call returns `R`, and a field is a `Nat`.

Deferred, unchanged: non-`Nat` parameters, tier-1 result types, parameterized
result types (§6 adds *fields at another inductive* to that list, with its
reason).

## 3. The lowering the walker reads

`docs/inductive-tier0-lowering.md` §§3–4: constructor `i` of `n` is

```
inr^i(inl(Pair(<nominal tag>, Pair(f₁, … Pair(f_k, Triv)))))
```

with the last constructor missing its `inl` and a one-constructor enumeration
missing the sum entirely. The nominal tag is the declaration index's binary
digits as a `Pair`-spine of `Triv`s (§3.3; since 2026-09-26 it is `srefl` at
`sEq(Nat; k; k)`, which the walker's `tm_srefl` arm reads the same way), so it
is recognizable only as *a value with no field in it* — which is what the field-free stage's `TPure`
already is.

**The tag and the fields are told apart by position**, and that is the whole
trick of the design: the second component of a `Pair` is always the rest of the
field chain; the first component is a field unless it is pure, in which case it
is the nominal tag. Nothing has to know which of "a field chain" and "a payload
with fields" it is holding until an `inl`/`inr` — or the function's root —
asks.

## 4. The walker: one new state, no new arm

The consequence of §3 is that the fields stage costs `TA` **one** constructor
and **no** new arm in any existing `match`:

```heather
TPure                                        -- unchanged: a tag spine, a
                                             --   field-free payload
TFlds(pre: Pre, len: Nat, args: PRefs)       -- new: a field chain, and (once
                                             --   its tag is consumed) a
                                             --   payload with fields
TCtor(tag: Nat, pre: Pre, len: Nat, args: PRefs)   -- was TCtor(tag)
```

`TFlds` carries exactly what `TPart` carries for a call's arguments — a merged
prefix, its length, and the references in slot order — because a field is an
arbitrary expression with its own instructions, which have to be merged and
re-based exactly as a call's arguments are. That is §2.2's sentence, and it is
still true; what changed is the price.

The arms, each one `match` per `fn` per the file's size rule (which forbids a
`match` on `TA` inside another):

| node | rule |
| --- | --- |
| `ta_triv` | `TPure` — the empty chain |
| `ta_pair(a, b)` | dispatch on `b`: `TPure` → `ta_pair_end(a)`, `TFlds(…)` → `ta_pair_cons(a, …)`, else decline |
| `ta_pair_end(a)` | `TPure` → `TPure`; otherwise the chain's last field: `ta_flds_cons(ta_val(a), PEnd, 0, QNil)` |
| `ta_pair_cons(a, pre, len, args)` | `TPure` → the payload's tag, chain unchanged; otherwise one more field |
| `ta_flds_cons(v, pre, len, args)` | the merge: `pre_append(shift_pre(pa, len), pre)`, `add(len, la)`, `QCons(shift_ref(ra, len), args)` |
| `ta_inl(t)` / `ta_inr(t)` | carry `(pre, len, args)` through, index as before |
| `ta_val` | `TCtor(tag, pre, len, args)` → `PCon(tag, args, pre)`; `TFlds` → the same at index 0 |

Two things fall out for free and are worth naming, because they are what makes
this design cheap rather than merely correct:

- **`ta_val` becomes uniform.** A constructor value renders as one `LetCon`
  over the fields it collected, which is *the same shape* `ta_call_fin`
  already emits for a saturated call. The field-free case is that at
  `PEnd/0/QNil`, so every existing non-`Nat` emission is byte-identical.
- **A field may be a call**, because the merge is the one `ta_call` already
  performs. See §5.

The signature side mirrors it state for state: `SFlds` is a Σ chain of `Nat`s,
`sig_sigma` dispatches on its second argument exactly as `ta_pair` does on
`b`, `SPure` in a first component is the tag, `SNat` is a field. `SigOut`
stays flat `(arity, res)` — the field *counts* are a declaration fact the rim
already has, so the verdict does not carry them and no elimination pays for an
inductive-typed field.

## 5. Cross-function composition, taken with fields — the §2.3 answer

`docs/certgen-non-nat-embeddings-design.md` §2.3 deferred cross-function
composition at a non-`Nat` result and predicted it "wants a per-slot type on
the renderer's environment, which is the same data structure the fields stage
needs. The two should land together." That is right, and the shared structure
is smaller than predicted — it is not a data structure at all but a **rule**:

> A temporary's type is decided by position. The temporary the region
> *returns* has the function's result type. A **self-call**'s temporary has the
> result type. Every other temporary is a `Nat`.

The last clause is a theorem about the fragment, not a heuristic: a temporary
that is neither returned nor a self-call can only be *used* as a constructor
field or as a call argument, and both are `Nat`s. A foreign callee is
`Nat → … → Nat` by the callee-marker convention, so its temporary is a `Nat`
whatever the caller returns.

Two consequences:

- The renderer needs no inference — `ProofCx::con_res` is a look-ahead for
  "does the rest of this region return the slot I am about to bind", which is
  a walk of the certificate it already has.
- **Cross-function composition lands with fields and not before**, for the
  reason §2.3 gave from the other side: before fields there was nowhere for a
  `Nat` temporary to be *used* in an `R`-result function, so the shape was
  impossible; with fields there is, so the decline `chain_from_rir` used to
  make is retired. `fn viafield(n) -> Peek { … PSome(add(k, k)) … }` would
  generate a two-member program whose callee's invariant is re-derived at
  `embed_nat` and whose constructor is spelled over the call — designed and
  implemented, pinned in the walker, never generated (§8's cost is why).

The same rule is applied twice, one layer apart — on the read-back `Ir` (which
constructor table a `LetCon`'s tag is checked against) and on the certificate
(which embedding a temporary's spec is written at). They agree by
construction, because the certificate fold is a per-instruction map over
exactly that chain.

At an all-`Nat` signature both branches of the rule coincide, which is why the
five `Nat` emissions stay byte-identical: `Nat` is still the zero-th instance.

## 6. What this stage declines, and why each is honest

- **A field at another inductive.** The *term* side reads it perfectly well —
  an enumeration value is a value like any other, and `ta_val` renders it — so
  this is not a walker limit. It is an emitter limit: `embed_T` would have to
  embed the field at *that* type's embedding rather than at `embed_nat`, which
  means emitting a second `embed_T` and threading per-field types through
  `ctor_spec`. Declined at `sig_sigma`'s field rule, and the Rust residue
  declines the same declarations (a non-`Nat` field type) so that the
  agreement property stays a decline rather than a loud disagreement.
- **A field at a tier-1 type** — `Wf` is not a shape `sig_*` has a case for,
  as before.
- **A self-call in a field** — impossible by typing (§2), not refused.
- **A constructor tag or arity the result type cannot name** — at the rim,
  where the spelling lives, unchanged.

One pre-existing degeneracy was found while working out §3 and is recorded
here because it is not this stage's to fix: a field whose type is a
**one-constructor, field-free** enumeration is *indistinguishable* from the
nominal tag, at both the term and the type level (both are built from `Unit`
and Σ / `Triv` and `Pair` alone). Such a declaration is therefore accepted with
that field silently uncounted, and the emitted `embed_T` drops it. Nothing
unsound follows — `embed_T` is a generated artifact and the certificate is
about exactly the embedding that was emitted — but the resulting `Compile`
instance is about a lossy embedding. This is true of the shipped field-free
stage today, not only of this design.

## 7. What the rim gains — names and rendering only

The frozen-walker rule holds: `crates/elab/src/certgen.rs` gains no analysis.

1. `ResTy::of` stops refusing constructors with fields and starts refusing
   constructors with **non-`Nat`** fields (§6) — a declaration-registry read.
2. The positional rule of §5, at two sites, plus the retirement of the
   foreign-call decline.
3. Nothing else. `embed_text`, `ctor_spec`, the arity check, the fixture
   evaluator's `V { tag, fields }` and the marker whitelist were all written
   for fields already.

`lib/certgen/certgen_cert.hthr` needs **zero** edits, verified rather than assumed: a
constructor tag is a `Nat` field of `CCon` and its arguments are a `Refs`, so
the fold is already field-count-agnostic, and the induction is still over the
scrutinized `Nat` parameter. That is the second consecutive fragment feature
the `Cert` expression absorbed untouched — `docs/certgen-cert-expression-design.md`
§8.1 predicted a tier-1 *source* type would be the first to touch it, and this
round is evidence for that prediction rather than against it.

## 8. The measurement, and why the stage is deferred again

Two costs, and the round's finding is that §2.2 measured the one that has since
been fixed. Wall times are in `issues/certgen-harness-cost.md`'s 2026-08-13
log per the shape-claims-in-docs policy; the shapes are:

**(a) Elaborating the widened library: a non-issue now.** The whole point of
re-probing. `lib/certgen/certgen_code.hthr` with the §4 widening — one more `TA`
constructor, three more `Pre`-carrying fields, four more `fn`s, five more
`refl` pins — elaborates about **30% slower** than the file ships at today, on
a file that two spelling rounds made roughly an order of magnitude cheaper than
the one §2.2 measured. In absolute terms the widening costs a fraction of a
second where §2.2's cut cost tens of seconds, and the debug/release ratio on
this file is small enough that the test binaries never come near their rail
from elaboration. §2.2's `SIGKILL` is not reproducible: **that cliff is gone,
and the size law's constant is where the two spelling rounds left it.**

**(b) *Generating* one fixture: the cliff that is in the way.** This is the
in-language *evaluation* of the transcriber shell over a marked body — running
`transcribe` by kernel reduction, plus the spine-directed readback — and no
spelling round touches it, because nothing here is a term the elaborator
emits. Measured in one debug harness, relative to today's fragment:

| fixture | shape | cost, relative to `add` |
| --- | --- | --- |
| `add`, `seven` | the shipped `Nat` fragment | 1x (`seven` below it) |
| `is_zero` | a nullary non-`Nat` constructor | ~1.5x |
| `mul` | the shipped cross-function `Nat` case — today's most expensive fixture | ~18x |
| `peek` | **one** field, a bare arm binder | ~24x |
| `PSome(Succ(k))` | one field, computed | ~100x |
| `BSome(k, k)` | **two** fields, both bare | ~135x |
| `BSome(k, Succ(k))` | two fields, one computed | **beyond the rail** — exceeds `scripts/test`'s address-space limit, and does not finish at any budget this round gave it |

The shape is the point: cost grows steeply with the payload's *structure*, not
with the body's size (a numeral literal body — `seven`, eight instructions — is
the cheapest fixture there is). One bare field is affordable and comparable to
the shipped cross-function case; the smallest two-field constructor costs a
whole test binary's budget by itself; and the first genuinely ordinary
two-field constructor does not finish at all.

**Why that is a stop and not a fixture-selection problem.** The fragment cannot
decline the expensive shapes honestly. `check_sig` accepts a declaration by its
*type*, so a two-field enumeration is in the fragment as soon as one-field
enumerations are; the generator would then accept `BSome(k, Succ(k))` and
consume the whole rail before failing. A cost boundary that the fragment cannot
state is worse than a feature that is not there: declining is supposed to be
cheap, and this would make it expensive.

**The attribution, corrected.** §2.2 named the mechanism right — a payload
state carrying a compiled `Pre`, and `Pre` is the file's largest type — and
attributed the price to the elaboration-time size law. Half of that was the
elaborator's, and it is fixed. The other half is the *evaluation* of matches on
`Pre` (a `Wf`-lowered inductive) inside a shell that the kernel reduces without
sharing, which is precisely the residual `issues/certgen-harness-cost.md`
already owns as "the transcriber's own in-language evaluation, which no verdict
cache can touch". The fields stage is the first feature to make that residual
the *binding* constraint rather than a floor.

### 8.1 What actually cost that, measured one round later

The attribution above says "matches on `Pre` … inside a shell that the kernel
reduces without sharing". The half of that sentence which is about *sharing*
turned out to be wrong, and the correction is worth keeping beside the table
because it is the reason the table's numbers were reachable at all:
`docs/analyzer-evaluation-design.md` §1 counted the reader's work and found
**no repetition to share** — `peek` is ~300 reader steps and ~2000 reduction
steps in total. The cost was *per step*, in the size of the term the
**rewriter** rebuilt at each one, and the largest terms in sight are the `Wf`
shape and arity slots of the very lowerings this table's "structure" reading
pointed at. So the mechanism named here was right about *where* and wrong
about *why*, and the fix was an evaluator rather than a memo.

The table above is therefore a record of the rewriter, not of the fragment.
The same fixtures under the value-domain reader are in
`issues/certgen-analyzer-evaluation-cost.md`'s log; every one of them,
including `BSome(k, Succ(k))`, is tens of milliseconds.

## 9. What would unblock it — worked through, with verdicts

Owned by `issues/certgen-analyzer-evaluation-cost.md`, promoted out of
`issues/certgen-harness-cost.md`'s log by this round's measurement. In the
order they would be worth trying, none of them this round's:

1. **Cheaper meta-layer evaluation.** The transcriber is run by
   `whnf_term_delta` under `Reader`'s spine-directed readback, which re-reduces
   each sub-spine from the top and shares nothing between reductions. A
   memoizing or normalize-once evaluation for analyzer invocation is a single
   change with the whole fragment behind it, and it would also drop
   `certgen.rs`'s standing in-language-evaluation floor. This is the lever the
   measurement points at.
2. **A smaller `TA`.** The walker's states carry `Pre` and `Ir`, both `Wf`
   -lowered, and every `match` on `TA` eliminates over all of them. Splitting
   the payload states out of `TA` into a small companion type (the `VOut`
   move, applied again) is the in-language half of the same problem, worth
   measuring *after* (1) rather than before — the size law's elaboration half
   is no longer what hurts.
3. **Re-probing at that point with §§2–7 unchanged.** The design is
   prototyped: the walker's pins, the positional slot rule, the cross-function
   composition and the byte-identity of the existing emissions were all
   checked during this round before the cost was measured. Nothing about it
   needs redesigning; it needs to become affordable to run.

**Verdicts, 2026-08-13.**

1. **Taken, and it was the whole of it** — `docs/analyzer-evaluation-design.md`.
   Not a memo: the reader is re-instantiated at the kernel's value domain, so
   an eliminator enters its branch instead of copying it and the lowered
   annotations are never traversed. One seam, no kernel line.
2. **Not taken, and no longer worth taking.** A smaller `TA` was to be
   measured after (1); after (1) the widest fixture generates in ~50 ms, so
   there is nothing left to measure it against. It stays described on
   `issues/certgen-analyzer-evaluation-cost.md` as available, unspent.
3. **Re-probed, and §§2–7 needed no change.** In the order §9 asked for:
   - the two things this document said had never been generated —
     `pack` = `BSome(k, Succ(k))` (two fields, one computed) and `viafield`
     (a cross-function call *in* a field, §5's rule) — were generated,
     read back against the designed IR literally, and **kernel-checked end
     to end** through their emissions and support artifacts. Both held on the
     first run, so §5's positional rule is now observed rather than
     predicted, and non-`Nat` §2.3's deferred cross-function composition is
     discharged with it;
   - every pre-existing emission is byte-identical, `Nat` and field-free
     non-`Nat` alike;
   - the third perturbed-library control this document's §8 wanted and could
     not write exists: `certgen_controls.rs`'s
     `a_perturbed_field_merge_is_refused_by_the_kernel` snocs where
     `ta_flds_cons` should cons, so a two-field constructor **renders** with
     its slots swapped — right tag, right arity, wrong value — and its own
     exactness fixture refuses it. A one-field constructor cannot see that
     mutation, which is why the control's fixture has two.

The fragment's constructors therefore take fields, and §2's deferrals —
non-`Nat` parameters, tier-1 result types, parameterized results, and §6's
field at another inductive — are what is left.
