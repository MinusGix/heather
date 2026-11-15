# A closed type argument spelled two ways, and the `Pi`/`Pi` row — design

Design pass on `issues/elaborator-canonical-type-spelling.md`, 2026-09-15,
answering the two triggers its entry of that date names: (1) a declaration's
function-typed value-parameter domain has no name, and `Pi`/`Pi` is the top
head-pair row on `docs/showcase/calc_parser.hthr` after the
telescoped-dependent-projection round; (2) a **closed** type argument is
spelled two ways inside one lowering, so `instance_match`'s positional matcher
recovers two disagreeing codes for one hole and declines.

Every claim below was hand-run before it was written: a throwaway spike on the
`51f5e59` tree, one furnace box, release with `--features value-metrics`,
`--kernel-workers 1`, base and spike built in the same job and run back to
back. No source change survives this pass; the seconds live in the round
report and on the issue.

**The two triggers are one defect, and the second is a consequence of the
first.** Nobody had read the first difference between the two `Π`s. It is not
a level tree and it is not a genuinely different `Π`: it is a component —
`Cursor<T>(source)` inline on one side and the per-instantiation reference on
the other, and the `A` argument spelled `Nat` against `El («Nat»)`. Both are
the *same* disagreement the decline listing reports as
`hole-match-type-hole/two-occurrences-disagree`, seen from the kernel's end
instead of the elaborator's. Fixing the matcher removes the `Pi`/`Pi` row
without anything being named.

---

## 1. The datum, from the trace and not from the hypothesis

`HEATHER_CONV_MISS_TRACE=close_body` on the current tree puts essentially all
of that item's misses on one head pair, `Pi`/`Pi`, and
`first_difference_excerpt` splits them into **two groups of almost exactly
equal count**. Trimmed, with the rendering positions as the sampler prints
them:

```text
group A   expected len=695  inferred len=706  first difference at 685
expected: …; u55^{·^9})) → Ty 0; x1))). Π[0,1](Nat). Ty 0…
inferred: …; u55^{·^9})) → Ty 0; x1))). Π[0,1](El[0](«Nat»)). Ty 0…

group B   expected len=1323 inferred len=561  first difference at 117
expected: … Π[0,(0 ⊔ (0 ⊔ 1))](Σ[0,0](Σ[0,0](Σ[0,0](Unit 0). Unit 0). …
inferred: … Π[0,(0 ⊔ (0 ⊔ 1))](El[0](app(app(u289^{·^7}; [1,1] Ty 0 →
          Π[0,1](El[0](app(u763^{·^8}; …; x0))). Ty 0; u55^{·^7}); …
```

Read off it, in the order the charter asked the candidates to be checked:

1. **Level trees are not the first difference.** They are there — every
   rendering above carries `(1 ⊔ ((0 ⊔ 0) ⊔ (0 ⊔ (0 ⊔ (0 ⊔ (0 ⊔ 1))))))` in a
   fn statement's `Π` — but they are *identical on both sides*: the first
   difference is 685 bytes in on a 695-byte rendering (group A) and 117 bytes
   in (group B), and every level in the agreeing prefix agrees. They are a
   real defect at a real site (§5.3) and they are not this one.
2. **A component spelled two ways** is what both groups are. Group B is
   `Cursor<T>(source)` written out on the expected side and
   `El (app(Cursor#tycode_fn^δ; ā))` on the inferred side — the expected
   rendering is more than twice the size of the inferred one, which is the
   reference doing its job on one side only. Group A is the `A` argument of
   the same `Π`: the primitive `Nat` against `El («Nat»)`, the kernel's own
   substitution result at a code argument (the 2026-09-10 entry's third
   spelling).
3. **Genuinely different but convertible `Π`s** is refuted. Outside the one
   differing component the two renderings agree byte for byte, including
   every level, every `·^k` tail and every binder.

So slice 2 is candidate 2, and the answer is that it **collapses into slice
1**: no new definition kind, no name for the domain.

### 1.1 Why the expected side is the inline one

`Certified<T,A>(source, begin, relation)` declares its third value parameter
as `(source: List<T>) -> Cursor<T>(source) -> Cursor<T>(source) -> A -> Type`.
At a use site `valparam_args` (`inductive.rs`) re-elaborates that declared
type with the type parameters bound as `Cx::tyvars` **at the argument's inline
type**, and the result is what the argument is checked against and what
`lower_ctor` then writes into the field types. The argument's own type comes
off the callee's Ψ statement, which
`docs/elaborator/annotation-component-respell-design.md` §2.1's cascade respelled. So one `Π` is
built out of inline components and the other out of references — and the
emission chokepoint is supposed to reconcile them: `annotation_type` on that
`Π` walks the domains and asks `respell_ty_at` to name `Cursor<PTok>(source)`.

**It asks, and it is refused, by slice 1's defect.** The decline listing says
so by name: `instance_match Cursor hole-match-type-hole/two-occurrences-
disagree` is the largest parser-side row, and `Cursor` is exactly the
component the group-B excerpt shows unnamed. The `Pi`/`Pi` row is the kernel
being handed the decline.

---

## 2. Slice 1 — what disagrees, and where

At a **closed** type argument the subject spells one argument two ways
(`docs/elaborator/telescoped-record-projections-design.md` §2.3 as amended). A binder's
type is a *structural read* and keeps the inline lowering
(`docs/elaborator/annotation-component-respell-design.md`'s standing line); the same type
as an application's **type argument** is an annotation, went through the
chokepoint, and is `El (D#tycode^δ)` — so `code_of` of the first is `TmSum(…)`
and of the second is `D#tycode^δ`. `Holes::place_ty` sees two codes for one
hole and stops. `wf.rs mod dependent_telescope`'s
`a_type_parameter_occurring_as_a_code_in_a_term_slot_is_placed` states the
boundary as a to-be-flipped assertion; `Cursor`, `Certified` and `Failure` are
the parser-side payers and the dictionary records the rest.

Three further facts fix the shape of the fix.

- **No choice of recovered argument helps.** Step 2 compares the template at
  whichever code was chosen against a subject that contains *both* spellings,
  so it refuses either way. The matcher is not choosing wrongly; the
  comparison is spelling-sensitive.
- **The second residue is the same disagreement from the other side.**
  `hole-match-Wf/El` is a stored template that is inline at a node meeting a
  subject that arrived *already emitted* and carries a reference there.
- **There is a third, and the trace found it before the listing did.**
  `El («Nat»)` against `Nat` is neither of the above: it is a **quote**, not a
  name — a code literal substituted into an `El` slot against the type it
  quotes. It looks like an independent row and is not: §5.2 measures it as a
  symptom of the first two, and the arm that would have addressed it directly
  is refused there.

---

## 3. The mechanism: the recognizers see through **names**

The issue's own Direction, taken literally and no further. Seeing through
*quotes* as well looks like the same sentence and is not (§5.2).

```text
see_through(T) = the registry's inline copy, if T is El(D#tycode^δ) or
                 El(app(D#tycode_fn^δ; ā))          — Elaborator::unspell_here
               = None otherwise
```

Both comparisons `instance_match` performs learn it, at one node each:

- **`Holes::ty` and `Holes::tm`, on the former-mismatch arm.** When the two
  sides are not syntactically equal and no structural arm applies, try
  `see_through` on the subject, then on the template, and recurse. Every arm
  above it is untouched, so nothing that matches today matches differently.
- **`Holes::place_ty`.** Two codes for one hole agree when their inline normal
  forms agree. The **reference** copy is the one kept, because that is what
  the reference carries and what the emitted argument becomes anyway — and
  because keeping it is free: `instance_match` already re-derives the emitted
  argument as `code_of(emit_ty(decode_deep(El l c)))`, which gives the
  reference from either input.
- **Step 2 is the same walk with no holes.** Rather than a second congruence
  kept in step with the first, the identity check runs `Holes` with an empty
  telescope (`total = 0`, so no hole arm can fire) and a `strict` flag that
  makes a global's substitution tail count — the lax tail reading exists for
  the *match*, whose two sides are read in different frames, and step 2's
  whole job is to catch a wrongly-framed copy. One walk, two uses, and the
  see-through arms the match needed are exactly the ones the proof is allowed.

> **Amended 2026-11-09, §3.** The `strict` flag is gone. A closed global's
> empty substitution records nothing, so there is no frame for a copy to be
> wrongly in and no tail for the two readings to differ on; step 2 is the
> same walk with no holes and nothing else
> (`issues/empty-substitution-tail-decoration.md`).

> **Amended 2026-09-15 (implementation), §3.** `see_through` is
> `Elaborator::unspell_here_in(T, g)` and not `unspell_here(T)` — the same
> function with the scratch anchor carried rather than assumed.
> `unspell_here` bakes `gen_def_of`'s `g = 0` numbering, while
> `instance_match` also runs `g` scratch globals deep (`apply_implicit`'s
> world, `respell_ty_deep_in`'s `scratch`), and a reference read at the wrong
> anchor names a *different* generated definition rather than none — which the
> see-through relation, unlike everything else that reads that anchor, would
> then propagate into step 2's own walk. `unspell_here(T) =
> unspell_here_in(T, 0)` verbatim, so nothing outside the matcher moves.
> The term-slot arm sees through a **code** (`code_of` of the copy the
> reference names); `unspell_here_in` reads the `El`'s code and never its
> level, so the `El` that arm builds around a code carries a placeholder
> level.

Termination: `unspell_here` replaces a reference by the registry's copy of a
declaration declared *earlier*, so each step is by a well-founded measure and
the recursion cannot cycle. That the measure exists is not by itself enough —
§5.2 is the round where the neighbouring relation had one and still ran out of
stack.

Soundness is unchanged and is still step 2's: the matcher may be as incomplete
or as generous as convenient, because the template at the recovered arguments
must still *be* the subject — now up to the same see-through relation, which
is `δ`-unfolding a generated definition to the very copy it was minted from.
It relates no two declarations.
The look-alike negatives (`ByCodeLk`, `ByAppLk`) still decline for the reason
they always did: their templates differ at a node where neither side is a
reference or a quote, and the tag Σ is compared positionally.

### 3.1 Why the second residue falls to it

`hole-match-Wf/El` is a `Wf`-headed template node against an `El`-headed
subject node. It reaches the former-mismatch arm, `see_through` unspells the
subject's reference into the registry's `Wf`, and the walk continues. No arm
is needed per residue: the residues are one relation seen at different
formers, which is why `Sigma/El`, `Sum/El` and `Wf/El` all leave the listing
together.

### 3.2 What is *not* changed

- **`lower_instance` stays the identity.** Respelling inside the registry is
  the credulous read the fingerprint rounds exist to prevent
  (`docs/elaborator/annotation-component-respell-design.md` §3), and it is now doubly
  unnecessary: the recognizer sees through the difference instead.
- **No structural reader learns a new spelling.** The change is confined to
  the matcher and its proof; `whnf`, `unify_ty`, `resolve_goal_from` and
  `display_shape` keep their existing unspelling.
- **The emitted argument's spelling is unchanged**, which is what makes this a
  pure decline-removal: sites that named a type before name the same type,
  sites that declined now name the one the subject already meant.

---

## 4. Rejected shapes, with reasons

- **Spell the subject one way — respell binder types too.** The structural-read
  line exists for a reason: the inline lowering is the identity every
  structural reader and both recognizer fingerprints anchor on, `whnf` is
  written against it, and every reader that looks at a binder's type would pay
  a δ (and `unify_ty` would lose the structure an implicit is solved from,
  which is the 63-declaration failure the 2026-09-10 pass already paid for
  once). It also does not reach the quote half at all, since the kernel's
  substitution result is not the elaborator's to spell. One paragraph is all
  it deserves.
- **Normalizing the subject once, deeply, before matching.** The clean-looking
  version of the same idea, and it needs a walk the elaborator does not have:
  `unspell_ty_deep` does not descend into terms, and the disagreeing
  occurrences live in `App` type arguments inside `Id` endpoints. A
  term-descending inverse is a round of its own, would materialize the whole
  inline copy at every emission, and buys nothing over seeing through one node
  when the two sides actually differ there.
- **Naming the function-typed value-parameter domain** (`D#dom_i := λΘ. ⌜Π…⌝`,
  design §5's own follow-up). This is the hypothesis the charter said not to
  start from, and the trace refutes it: naming one side buys one δ and then
  the *same* `Π`/`Π` compare, because the argument's type is not the domain's
  name — and once the component is spelled alike the two `Π`s are
  syntactically equal and the conversion shortcut fires with nothing named.
  The trigger on §5 is answered, not deferred: it was never a naming problem.
  Should a later table put a `Pi`/`Pi` row on top again whose first difference
  is *not* a component, this is where to start.
- **A kernel rule that sees through a code reference.** Unchanged from §6 of
  the telescoped design and refused on this round's own evidence too: the
  kernel would pay per conversion for a decision the elaborator now makes once
  per emission, and both sides of every row here are ours.
- **Making the matcher complete.** Still not wanted. Each unhandled former is
  a decline that costs today's spelling and never a wrong answer; the
  see-through arm is not a new former but a relation on the nodes that are
  already walked.

---

## 5. What the spike showed, and what it did not fix

The spike is the mechanism of §3 and nothing else.

- **The decline listing loses exactly the predicted rows** —
  `two-occurrences-disagree` and `Wf/El` for `Cursor`, `Certified` and
  `Failure`, and the `project_field … instance-args` rows for `Cursor` — and
  the flip assertion in `wf.rs mod dependent_telescope` flips.
- **`Pi`/`Pi` leaves the head-pair table.** It is the top row before and is
  not in the top eight after; the showcase's whole-file wall, kernel gate,
  resident memory, conversion misses and evaluator steps all fall, with
  `close_body` — the item the trace was taken on — losing most of its time,
  the overwhelming majority of its misses and most of its evaluator steps.
  The spike compared the top rows only, so the telescoped design's §9 item 6
  (*no head-pair count may rise*) is still open and is the implementer's:
  compare the **whole** summed table, not its head.

  > **Amended 2026-09-15 (implementation), §5.** The whole summed table was
  > compared. 53 rows both sides; total misses 370 654 → 319 716 and total
  > seconds 40.361 → 25.850. Four counts rose and all four are noise in
  > seconds: `El(?)/El(?)` 827 → 1 284 (0.770 → 0.739 s), `Sum/El⌜⌝` 16 581 →
  > 16 769 (0.980 → 0.975 s), `El⌜⌝/El^δ` 425 → 449 (0.041 → 0.051 s),
  > `El⌜⌝/Wf` 182 → 188 (0.019 → 0.020 s). No pair exists in the changed run
  > that did not exist in the parent's. Strict head-pair monotonicity is
  > therefore **not** met, which the telescoped design's own §9 item 1 had
  > already superseded in favour of totals; the four rows are the see-through
  > arm carrying a walk past a former mismatch to a *later* stop, and the same
  > thing is visible in the decline listing, where `RecognizedHead
  > hole-match-Sum/El` (26) becomes `hole-match-other-tm/other-tm` (28).
  > `Pi`/`Pi` itself: row 2 → row 9, 47 010 / 4.947 s → 8 421 / 0.739 s.
- **The full suite is green except the flip assertion itself.** One test
  fails, and it is `mod dependent_telescope`'s
  `a_type_parameter_occurring_as_a_code_in_a_term_slot_is_placed`,
  at the line whose message is *"if this now recovers, the two spellings of a
  closed type argument have been reconciled — flip the assertion and
  re-measure"*. Nothing else moves: not the x86 rails, not
  `record_projection_size`, not the `psi().bindings.len()` fixtures, not the
  whole-library acceptance load or the emission walker's residue list. This
  is the whole suite and not the fast lane, because the change is in a
  generator and the fast lane replays images an earlier build wrote.
- **`complete_post` does not move.** Its misses are `El(?)`/`Wf`,
  `El⌜⌝`/`El(?)` and `Vec`/`Sigma`, which are other declarations' rows and the
  next round's.
- **The reproducer improves without collapsing.** `probes/t_pcr3.hthr`'s
  `qchain1..3` and `qev3` stay at **zero** misses and zero steps and get
  materially cheaper, but the per-receiver growth factor is still large: what
  the charter predicted (`t_pc1..4`'s collapse) does not arrive from the
  matcher alone, because `Certified`'s remaining declines keep some reads on
  the fallback walk. Those declines are named in §5.1 and are the implementer's
  first measurement, not a design question.

### 5.1 The residues this leaves, named

- `instance_match List hole-match-Wf/Sigma` is by a wide margin the largest
  remaining `instance_match` row on the showcase and is **not** a spelling
  pair of this kind: a `Wf`-headed template against a genuinely `Σ`-headed
  subject. It is untouched here and wants its own attribution.
- `Or`, `Result` and `Option` decline with `hole-match-Sum/Sigma`, the same
  shape at the sum spine.
- `project_field Parser receiver-gate-0` is the gate, not a spelling.

### 5.2 The quote half: built, refuted, and left as a residue

Seeing through names alone leaves step 2 failing with a new and precise
reason — `identity-match-El/Nat` on `Certified` and on `Exists`, a small
count — which is the group-A excerpt arriving in the elaborator: a code
literal substituted into an `El` slot against the type it quotes. Adding
`decoded` to `see_through` is one line and looks like the same sentence.

**It was built and it is refused.** With the quote arm in, the showcase
aborts with `fatal runtime error: stack overflow` at every width, and so does
the reproducer and the decline listing. The measure that makes the relation
well-founded is not the one that bounds it: a quote can be a multi-megabyte
literal — the same run's sampler shows single conversion operands over seven
million characters — and decoding one on a mismatch arm turns a matcher walk
into a walk of the decoded copy at every node it disagrees at. The name arm
never does this, because a reference unspells to the registry's *copy*, which
is the type the walk was already going to compare.

So the quote half is **not** in this slice, and the measurements say it costs
nothing to leave out: with names alone, `Pi`/`Pi` leaves the head-pair table
anyway — the group-A rows go with the group-B ones. The *reading* of that,
offered as an inference and not as a measurement, is that once `Cursor` is
named the expected side of the comparison stops being `valparam_args`'
re-elaborated inline domain and becomes the device's own statement at the
recovered arguments, so the `A` argument is then spelled on both sides by the
same substitution: group A is a symptom of group B rather than an independent
row. Confirming that is a one-line trace re-read on the changed tree (§7
item 3) and is cheap enough that the implementer should do it rather than
believe this paragraph.

> **Amended 2026-09-15 (implementation), §5.2 — the reading above is
> REFUTED.** The implementer did the re-read, and group A is **not** a symptom
> of group B. On part A's tree the `close_body` trace's `Pi`/`Pi` records are
> 7 058 where the parent had 44 339, and **7 052 of the 7 058 are group A**:
> the `(len=695, len=706, first difference at 685)` signature and its
> neighbours, every one of them `Π[0,1](Nat)` against
> `Π[0,1](El[0](«Nat»))`. Group B — the `(len=1323, len=561, at 117)`
> signature, `Cursor<T>(source)` inline against its reference — is gone
> entirely, exactly as designed. So the two groups had the same count because
> they sat on the same comparisons, not because one caused the other: naming
> the component fixed the component and left the quote beside it.
>
> What that costs, and does not: the row's seconds fall 4 400 ms → 480 ms
> inside a `close_body` that falls 29 939 ms → 6 861 ms, so it is still that
> item's top row, at 7 % of the item rather than 15 %. On the **whole-file**
> head-pair table it goes from row 2 (47 010 / 4.947 s) to row 9 (8 421 /
> 0.739 s), which is §5's "not in the top eight" met with one row to spare.
> The elaborator-side name for the same thing is the
> `instance_match Certified identity-match-El/Nat` row, 92 declines, and §7
> item 2's "a **small** row is expected; one on a record whose reads dominate
> an item is a re-attribution" is what fired: `Certified` *is* that record.
>
> The owner is unchanged and is not this slice: the bounded arm of
> `issues/quote-see-through-bounded-arm`, never an unbounded `decode`, and
> **not** §4's rejected naming slice — the first difference is still a
> component of the `Π` and not the `Π`, so nothing here re-opens naming the
> function-typed parameter domain. `Nat` is a primitive: it has no name to
> take, so seeing through names cannot reach it in principle, which is the
> same wall `wf.rs`'s `a_type_argument_arriving_as_a_quote_still_declines`
> pins at `ByCode<Nat>`.

> **Amended 2026-09-15 (implementation), §5.2.** The pinned negative
> (§7 item 7) is `wf.rs mod dependent_telescope`'s
> `a_type_argument_arriving_as_a_quote_still_declines`, and it pins **two**
> instantiations rather than one, because the second was a surprise: a type
> argument written as an outright code literal (`ByCode<El «Nat»>`) declines
> as predicted, and so does `ByCode<`**`Nat`**`>` — the bare primitive. `Nat`
> has no name to take, so its type-argument occurrence is the kernel's own
> substitution result `El «Nat»` against the `Nat` the binder spells, and the
> decline is step 2's on the `El`/`Nat` former pair. That is the design's
> group A reproduced in twelve lines of unit test rather than read off a
> trace, and it is a second reason the bounded arm is the only route: seeing
> through names cannot reach an argument that never had one. The control in
> the same test is `ByCode<Flat>`, which *is* reconciled.

If a later table puts the quote pair back on top, the shape to try is a
**bounded** arm — decode only against a small former (a primitive, a `Ty`),
or under an explicit node budget — and never an unbounded `decode` on a
mismatch.

### 5.3 The level trees are a separate, filed defect

`crates/elab/src/lib.rs`'s statement closing loop accumulates
`Level::max(dom_lvl, stmt_lvl)` raw, where `lower_shape`, `wrap_tel` and
`register_ty_code_fn` all end with `.normalize().canonical()` and
`Level::join` exists as the smart constructor for exactly this. Every fn
statement's `Π` therefore carries a quadratic `⊔` tree that is copied into
every `App` annotation read off it. The trace says it is not what makes these
comparisons miss — both sides carry the same tree — but the same trace says
it is a large fraction of what the kernel *renders*, and `Level::join`'s own
comment records a previous round where an un-normalized inferred level cost
tens of thousands of value-domain queries. It is a two-line change at a site
the charter already named, it is `equiv`-preserving by construction, and it
should be filed and landed on its own evidence rather than smuggled into this
round: measuring one change with another moving is what §5 of the telescoped
design was criticised for.

---

## 6. Cost, and the boundaries not moved

**Cost of the mechanism.** `see_through` is called only where the two sides
already differ at a node — never on the fast path, where equality decides
first — and what it materializes is the copy step 2 was going to build
anyway. The observed direction on every workload measured was down, including
`decl_emit_ns`, which is where a matcher that did more work would show first.

**Persistence.** Nothing is registered, stored or serialized differently. No
`GenDef` key, no image byte, no `psi().bindings.len()` fixture moves. What
changes is how many sites *use* the definitions that already exist.

**The receiver gate, the dependency test and the three devices** are untouched
in shape; more records reach them, which is the point.

---

## 7. Verification items for the implementer's first hour

Stop and report if any of these fires; each would refute part of the design.

1. **The flip assertion flips, and its look-alike does not.**
   `wf.rs mod tycode > tycode_fn > dependent_telescope`'s
   `a_type_parameter_occurring_as_a_code_in_a_term_slot_is_placed` currently
   asserts that `ByCode<Flat>` does *not* recover; it must now recover, with
   the recovered argument the **reference** code, while `ByCodeLk` and
   `ByApp`'s wrong-value-argument negative still decline. A look-alike that
   starts matching is the one failure mode that is not a performance
   question.
2. **The decline listing, before the seconds.**
   `HEATHER_GENDEF_DECLINES=1` on `docs/showcase/calc_parser.hthr`: the
   `two-occurrences-disagree` and `Wf/El` rows for `Cursor`, `Certified` and
   `Failure` are gone and `project_field … instance-args` for `Cursor` is
   gone. A **small** `identity-match-El/Nat` row on `Certified` and `Exists`
   is expected (§5.2) and is not a reason to add the quote arm; a large one,
   or one on a record whose reads dominate an item, is a re-attribution.
3. **The trace, re-read.** `HEATHER_CONV_MISS_TRACE=close_body` on the
   changed tree: `Pi`/`Pi` must be out of the head-pair table's top rows. If
   it is still there, re-read the excerpt before changing anything — a
   `Pi`/`Pi` whose first difference is *not* a component is a different
   finding and §4's rejected naming slice comes back into scope.
4. **The showcase's totals, serially and at the default width**, with
   `close_body` and `parser_primitives::complete_post` named in the table:
   whole-file wall, kernel gate, misses, steps and maxrss. `complete_post` is
   expected not to move; if it does, attribute before claiming it.
5. **The x86 rails do not move.** `crates/elab/tests/function_ir_x86_scaling.rs`
   and the native certificate gates, `caller_native_memory_same_27/28` inside
   the default fuel. The matcher now names instantiations it used to decline,
   and the certificate's records are where a reference that is cheap to
   compare and dear to compute through has been refused twice before. A
   regression here is a *design* refutation, not a tuning problem, and the
   report is the per-item scaling at two sizes — never a raised budget.
6. **Existing tests stay green**, and two of them have to be re-read rather
   than re-run: `wf.rs mod dependent_telescope` (item 1) and
   `crates/elab/tests/record_projection_size.rs` (whose parameterized-record
   fallback case may now take the reference route). Also `wf.rs mod
   stale_template`, `wf.rs mod tycode`, `annotation_cost.rs`,
   `parser_library.rs`, `showcase_calculator.rs`, and the whole-library
   acceptance load, whose emission-walker residue list may only shrink.
7. **The new tests vary the four axes and carry their controls**
   (`docs/testing-generated-terms.md`):
   - a **closed** type argument recovered from a subject that spells it both
     ways — the binder-type occurrence and the type-argument occurrence in
     one lowering — and an **open** one, which must still recover exactly as
     it does today (the open case is the one the current test covers and the
     regression risk of the new arm);
   - a **literal** receiver (an assembled record value) and a **neutral** one
     (a parameter and a bare binder), both reading a field off a record whose
     registration now succeeds;
   - a **checking** position: the projected field as the proof of a stated
     theorem, so a wrong type is a rejection and not a different term;
   - the quote pair as a **negative**: a type argument that arrives as a code
     literal (`El («Nat»)`) against the same type written out still declines,
     with `identity-match-El/Nat` as the reason — pinned so that the day
     someone adds the bounded arm of §5.2, this test is the one that changes;
   - negative controls: a false equation refused; a look-alike declaration
     whose lowering coincides shape-for-shape refused; a wrong-instance
     application refused **by the kernel rather than by a guard**; and a
     subject whose two occurrences disagree about a *genuinely different*
     argument still declining rather than picking one.
> **Amended 2026-09-15 (implementation), §7 item 7.** The **literal** receiver
> is an assembled record value returned by a `fn` and read through
> (`c_lit().a`), the idiom `mod dependent_telescope`'s own axis test already
> uses — *not* a constructor written inline at an argument position. The
> inline form was tried first and the emission walker rightly reports two
> findings on it, an `App`'s `dom`/`cod` carrying the boxed `El ⌜⟦Flat⟧⌝`
> literal. That is the quote layer's standing residue
> (`issues/emission-walker-residual-sites`), it is on the parent too, and it
> is not this slice's to fix; asserting an empty walker against it would have
> pinned someone else's defect to this test.

8. **Landing order: one commit, because slice 2 has no edit of its own.**
   Slice 1 is the whole change; slice 2's verification — `Pi`/`Pi` out of the
   head-pair table's top rows and the showcase totals down — is a
   *consequence* of it and is read off the same run. There is no green
   intermediate state to split on and nothing to sequence. Two things must
   **not** ride along: the level-tree normalization of §5.3 (a separate
   commit with its own before/after, or the round cannot say which change
   moved the gate) and the quote arm of §5.2 (built, refuted, and owned by a
   follow-up). The commit message should name the trace read, not the
   matcher: the finding is that the top `Pi`/`Pi` row was a decline, and that
   is what a later reader will want.

---

## 8. Status

Design only. No source change lands in this pass; the spike that measured
every claim above was reverted, and `probes/s3_*.sh` plus the trace excerpts
are what a reader needs to reproduce it.
