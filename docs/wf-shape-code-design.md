# Naming a `Wf`'s shape and arity — design

Deliberate perf round on `issues/wf-shape-annotation-slots.md`, 2026-08-13.
The predecessor (`docs/annotation-component-respell-design.md`) collapsed every
*nameable type* in an emitted annotation to `El (D#tycode^δ)` and re-homed its
residual here: `Term::Supf`/`Term::ElimWf` carry the `Wf`'s **shape component**
and its **arity term** verbatim, and no whole-type code can stand in either
slot — a shape is not a declared type, and an arity is not a type at all.

The issue had been exonerated twice on *match bodies* — a fraction of a
percent of a lowered body, both times — and re-attributed once, unmeasured, to
*values*. This round measured first, per its charter, and the measurement moved
the design twice before a line of the fix was written.

## 1. What the counters said

Method: a throwaway exact node counter (`fmt::count_exact`, a tick in the
`write_exact` path plus a scoped slot category at the three formers), run at
the elaborator's two kernel-gate sites per declaration. Workloads: the
`lib/ir_v1.hthr` declarations prefix, prefix + `lib/certgen_cert.hthr`,
prefix + `lib/certgen_code.hthr`. Numbers live in the issue log; the shapes:

1. **The slots are the workload.** Roughly three quarters of every emitted
   node — statements and bodies alike, on all three workloads — sat inside a
   `shape` or an `arity` slot of `Supf`, `ElimWf` or `Type::Wf`. The issue's
   own two exonerations were not wrong; they were taken before the
   component-respell round removed everything else.
2. **The arity is the bigger half, by several times.** Every prior sentence about this
   issue says "shape slot". A `Supf`'s arity — the constant-motive case tree
   that counts a label's children — is consistently three to four times its
   shape, and the arity occurs in *more* places than the shape does: the step
   telescope writes it into a `Vec` length, a `Fin` length and an `nth` length,
   each instantiated once per arm.
3. **`Type::Wf` outweighed both formers.** The largest single category was
   inline `Type::Wf` occurrences in ordinary annotations — thousands of them in
   the declarations prefix alone, more than half its body mass. Reading them
   back against the registry's own copies (byte-comparison of the rendered
   types) showed they were not exotic: **they were whole registered lowerings, emitted verbatim at sites
   that call no respell at all**. That is a different defect from this issue's,
   at the same slots, and §3.4–§3.5 are its fix.
4. **Half of a value-heavy statement was in the kernel's *decode* spelling.**
   `El (D#tycode^δ)` whnfs to `Wf(El ⌜S⌝). n` — the lazy decode leaves every
   component `El`-wrapped (`reduce.rs`'s `TmWf` rule) — and *that* is what a
   constructor value built at a respelled expected type carries into all of its
   annotations. Every guard in the elaborator compares against the registry's
   **inline** copy, so every one of them declined. The predecessor's value-side
   respells were, at those sites, dead. §3.3 is its fix, and it is the single
   largest number in the round.

So the charter's question — "does conversion then pay repeated δ+decode per
unfold?" — was answered before it was asked in the only place it could have
bitten: the reason to *avoid* the decode spelling is not conversion cost, it is
that the decode is a look-alike no guard accepts. §5 records the measured
answer for conversion itself.

## 2. The definitions

### 2.1 Two, not one

Per **recursive** declaration whose lowering is `Wf(x : S). n`, registered off
`register_ty_code`'s own lowering so the two registrations can never disagree
about what `⟦D⟧` is, and inheriting that function's boundary verbatim
(unparameterized, unindexed, `tag_of` routes back):

```text
D#shape : Trm_c(· ⊢ Ty l)            := ⌜S⌝
D#arity : Π(x : El (D#shape^δ)). Nat := λ(x : El (D#shape^δ)). n
```

The shape is a **code**, exactly like `D#tycode`: a shape slot holds a `Type`,
and `El (D#shape^δ)` is the type occurrence of a code.

The arity is a **function**, and that asymmetry is forced. An arity slot holds
a `Term` of type `Nat` *in the context extended by the shape's binder*, so the
only closed thing that can stand there and reduce back to `n` is an application
to that binder:

```text
shape slot ↦ El (D#shape^δ)
arity slot ↦ app(D#arity^δ; [l,0] El (D#shape^δ) → Nat; x₀)
```

A code `⌜n⌝` would be a term of `Trm_c`, not a term of `Nat`; there is no
splice at layer c that would put it back. This is why the issue's one-line fix
sketch ("a shape code, spelled in the slots") only ever covered a quarter of
the mass.

### 2.2 The definitions are closed, and the pair is all-or-nothing

Closedness is `register_ty_code`'s argument unchanged: a parameterized
declaration's lowering is monomorphized per instantiation, so there is no one
`S` to name. Registration is best-effort like every other `GenDef`, and
additionally **paired**: the guard entry is written only when *both* definitions
passed the kernel gate, so no use site can ever see half a spelling.

### 2.3 The guard takes two spellings of the shape

`Elaborator::wf_slot_refs(cx, shape, arity)` hands out the pair only when the
slots in front of it *are* the ones the definitions were minted from — the same
"can only decline" structural comparison `ty_type_ref` has always made, and for
the same reason: the tag alone would be a nominal claim about slots the emission
site read from somewhere else.

It keeps **two** copies of the shape: the inline `S`, and `El ⌜S⌝` — the decode
spelling of §1.4. A constructor value built at a respelled expected type arrives
with the second and no other, so with one copy the whole value site declines
silently. Measured: statements did not move at all until the second copy was
added. The arity needs no second copy (`code_of` keeps a term slot verbatim, and
the decode hands it back unchanged).

## 3. The five site families

The line held throughout is the predecessor's §3.1, unchanged: **structural
reads keep the inline spelling; only emitted terms take a reference.** What
changed is that this round had to *restore* that line as well as follow it
(§3.3).

### 3.1 Constructor values — `build_ctor`'s `Supf`

The site the 2026-08-13 re-attribution named. A constructor value carries one
whole shape and one whole arity; a nullary value of a large declaration is tens
of thousands of nodes of almost nothing else. `build_children` and the container
projection keep reading the inline `expected`.

### 3.2 The `match` lowering — `build_elim_wf`'s `ElimWf`, and the telescope

The `ElimWf`'s own two slots, and — through `wf_step_telescope_at`'s new
`slots` parameter — every arity the step telescope writes: the `cs` `Vec`
length, the `ih` `Fin` length, `nth`'s length, and the `Supf` the step's type is
stated at. That parameter is the edit the issue predicted, widened by
measurement from one `Supf` to the whole telescope.

Spelling *both* sides alike is not only smaller but cheaper: the kernel rebuilds
this telescope from the `ElimWf`'s own slots, so a respelled term against an
inline telescope would pay a δ-unfold per branch, where two identical spellings
compare syntactically.

The kernel's own callers (`typing.rs`, `conv.rs`, `rec.rs`, `reduce.rs`) pass
`None` and get today's behavior exactly: they build the telescope *from* the
term in front of them, and re-spelling there would be inventing a term the
checker never saw.

### 3.3 `whnf` of a reference gives the registry's copy, not the decode

`Elaborator::whnf` now maps `El (D#tycode^δ)` to the registry's inline `⟦D⟧`
before reducing anything. The two are the same type; the decode's spelling is
the look-alike of §1.4, and the whole elaborator — every structural reader and
every use-site guard — is written against the inline identity.

This is the opaque-globals doctrine (*unfolding-for-analysis happens at the
boundary*) applied one step earlier than `unspell_ty_deep` applies it: at the
one choke point every structural read of a type goes through. It is what makes
the predecessor's four respell families work again at values, and it is the
reason the numbers in §5 are what they are.

### 3.4 Both `match` lowerings' spines

`Tel` grows a `spine_emit` beside `spine`, and tier 0's `case_tree` takes the
same pair as an argument: the emission copy (`respell_spine`, already written
for values) is used for the `Case` component types, the `Inl`/`Inr` annotations
and the branch injections, while the binder types pushed into the elaborator's
own context and everything `projection`/`elab_arm` reads a field out of keep the
inline spine.

This is [[wf-field-conversion-cost]]'s residual, left out of its round by
charter ("the match lowerings' own spine uses stay inline") and taken here
because this round's counters put it above this issue's own slot. A `match` on a
declaration carrying a `Wf`-lowered field wrote that field type verbatim into
every `Case`, every `Inr` and every injection; the tier-0 half of it was the
largest single term left in `lib/certgen_code.hthr` after the tier-1 half
landed.

### 3.5 The motive, component-wise

`build_elim_wf`'s motive respell was whole-type only, and declined on every
motive whose head is not a declaration — `pick_arm(arms: Ir) -> Nat -> Ir` has
the motive `Π(Nat). ⟦Ir⟧`, so the largest type in the file was written out at
every instantiation of it. It is `respell_ty_deep` at depth 1 now (the motive's
own `z` binder), which shifts the *references* rather than the result.

## 4. What is deliberately not touched

- **`respell_ty_deep` keeps its `Type::Wf` arm as it was.** It feeds Ψ
  statements, and a statement is read structurally by every later call site;
  slot references there would reach `tag_of`/`spine` through a path §3.3's
  unspell does not cover (the head is a `Wf`, not a reference). The slot
  references are emitted only where the emission is final.
- **Structural readers learn nothing.** No reader of `Type::Wf`'s shape slot
  was taught the new spelling, and none needs to be: `decoded` leaves an `El` of
  a *neutral* code exactly as it is, which is the correct answer for a reader
  that must not see through a reference. The predecessor's §6 finding 4 is the
  cautionary tale, and the discipline that avoids it is that nothing structural
  is ever handed a slot reference in the first place.
- **The reflection boundary is unchanged.** `fn_type_code` and `sig_peel`
  unspell `TyCode` references out of *statements*; slot references never enter a
  statement (they enter emitted terms), so the inverse walk has nothing new to
  see. Pinned by the certgen suite rather than argued.
- **`forded.rs`'s `zj` `sup_f`** — the issue's original Θ(n) site — takes the
  same helper where its declaration has the pair registered, but the forded
  fixtures were not this round's measured workloads and no claim is made about
  their exponent.

## 5. Measurement and A/B

Per the inherited protocol: release build, wall best-of-3 under the CLAUDE.md
ulimits, one session for both columns, exact node counts from a throwaway
counter reverted before the final verification, and an env kill-switch
(`HEATHER_NO_WFSLOT`) on the slot references so both columns are one binary.
Numbers live in `issues/wf-shape-annotation-slots.md`'s log; this document keeps
shape claims only.

The charter's second measurement — whether conversion then pays repeated
δ+decode per unfold, the alternative reading of the unmoved forded slope — is
what the kill-switch column answered: it isolated exactly the slot references
against a binary that kept every other change, and every workload was
**faster** with them on, by a factor in the same range as the node reduction.
The alternative reading is refuted for these workloads: δ is one unfold against
a term whose case tree had to reduce either way, and §3.2's
spell-both-sides-alike removes the only place a mismatch could have been paid
per branch.

## 5.1 Rejected shapes, with reasons

- **A code for the arity (`D#arity := ⌜n⌝`).** The slot holds a `Term` of type
  `Nat` in the shape-extended context; a code is a term of `Trm_c`, and layer c
  has no splice that would put it back. §2.1.
- **Teaching `decoded`/`tag_of`/`spine` to see through `El (D#shape^δ)`.** It
  would let slot references stand anywhere, including in Ψ statements — and it
  would make every structural reader spelling-sensitive, which is exactly the
  credulous read the fingerprint discipline exists to prevent. The round goes
  the other way instead (§3.3): nothing structural is ever handed a reference.
- **Respelling the slots inside `lower_instance`.** Unchanged rejection from the
  predecessor: the inline lowering is the identity every reader and both
  recognizer fingerprints anchor on, and the guards compare against it.
- **Leaving the telescope's arity occurrences inline while respelling the
  `ElimWf`'s own slots.** Measured worse on both axes: twice the nodes, and a
  δ-unfold per branch where the two spellings meet.
- **Naming a *tier-0* declaration's spine components** (a `GenDef` per
  constructor payload type). The predecessor rejected this once on measurement
  and it stays rejected: the payload types' mass is the embedded field types,
  which `TyCode` already names, and §3.4 collects it with no new key.
  *(2026-09-06: the rejection was measured on **recursive** declarations,
  whose `Wf` has a `D#shape`. A **flat** declaration has no shape code, so
  the whole type was its only name and every `inl`/`inr` level below it
  spelled its suffix sum out; `issues/inductive-spelling-codes-nonrecursive.md`
  names flat declarations' payloads and suffix sums — `GenDef::PayloadCode`/
  `SuffixCode` — and spells the whole-type code over those names. Recursive
  declarations are unchanged.)*

## 6. Correctness, and the tests

Every reference is convertible to what it replaces by construction (the shape
code is `code_of` of the registry's shape; the arity function's body *is* the
registry's arity), and every position it stands in is one the kernel checks by
conversion — the `Supf`/`ElimWf` slots are the former's own components, from
which typing rebuilds `Wf(shape). arity` and hands agreement to conversion, and
the ι-rule only clones them. So the round is a spelling change end to end, the
same conservativity argument as the two rounds before it.

Tests (`wf.rs mod tycode`, extending the existing module), on
`docs/testing-generated-terms.md`'s axes: the registration boundary (recursive
yes, non-recursive and parameterized no); a constructor value's `Supf` and a
`match`'s `ElimWf` pinned *structurally* at the reference spelling; the decode
look-alike (a value built at a respelled expected type respells too — the §2.3
copy, which is the one a naive guard misses); the four axes crossed with the new
spelling (literal and neutral scrutinee, an open element type that respells
nothing and still elaborates beside coded declarations, a checking position, a
computation pinned by `refl`); a false-equation negative control; and a
look-alike negative in the landed discipline — a `Wf` whose shape `tag_of`
routes to `D` but whose arity is not `D`'s must decline.

---

## 7. Landed (2026-08-13)

Everything above shipped as designed, with §3.3–§3.5 being the three site
families the measurement added to the charter's one. What the round did *not*
do, deliberately: it did not touch `respell_ty_deep`'s statement path, did not
teach any structural reader the new spelling, and did not chase the two
remaining emitted families the counters name — `Type::Wf` occurrences that are
not any declaration's registered lowering (a monomorphized instantiation; a copy
inside a code quote), and an `App`'s `dom`/`cod` for a **function-typed
parameter**, where the predecessor's statement cascade cannot reach because the
annotation is copied from the binder's type during elaboration rather than from
a callee's Ψ statement. Both are recorded on the issue.

The residual that no spelling reaches is unchanged and still unowned:
conversion's own cost on large values, which is what `lib/ir_v1.hthr`'s
theorems pay and why that file moves least of the measured workloads.
