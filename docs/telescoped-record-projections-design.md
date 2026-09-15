# Named projections for telescoped dependent records — design

Deliberate perf round on `issues/parser-certified-composition-cost.md`,
2026-09-15. Boundary 1 of `issues/per-instantiation-projection-boundaries.md`
— "a dependent telescoped spine keeps the inline walk" — with the checked
parser library as its first customer and
`docs/per-instantiation-type-codes-design.md` §13 as the mechanism this
extends.

Every claim below was hand-run before it was written: a throwaway spike on the
2026-09-15 tree, one furnace E5 box, release with `--features value-metrics`,
`--kernel-workers 1`, before and after in the same session. The spike is not
part of this pass; what it showed is quoted where it decided something, and
the seconds live on the issue.

**The headline is not the device.** The device is four lines. Three separate
silent declines stand between it and every field read in
`lib/std/parser`, and each had to be found by instrumenting a decline
listing rather than by reading the code — §13.10's own lesson, paid twice more.

---

## 1. The datum

`issues/parser-certified-composition-cost.md` carries the attribution; this
section only says what it costs *shape*-wise, so the design can be read
without it.

Every record the parser library composes is **telescoped and dependent**:
`Cursor<T>(source)` (`within` mentions `offset`), `Success<T,A>(source,begin)`
(`forward` mentions `end`), `Certified<T,A>(source,begin,relation)` (`evidence`
mentions `end` and `value`), `CachedCursor`, `SelectedHead`, `RecognizedHead`,
`Counted<A>(count)`, `Dep<A>(B)`. `register_rec_projs` declines exactly that
combination, so every `op.end`, every `s.value`, every `c.evidence` is
`project_field`'s inline `fst(sndʲ v)` walk, whose tail substitution is the
exponent `issues/theorem-field-projection-oom.md` diagnosed and named away for
*closed* dependent records.

The reproducer is seventeen lines (`probes/t_pc1.hthr` … `t_pc4.hthr`): a
`Cert<T>(source, begin)` record with `Certified`'s four fields, read through
one, two, three and four **chained** receivers (`b: Cert(source, a.end)`, …).
Its shape claim is the whole issue:

- per chained receiver the item's total, its kernel gate and its emission time
  each grow by more than an order of magnitude — the fourth exhausts a
  multi-gigabyte address-space rail and dies on the allocator;
- **zero** conversion misses and **zero** evaluator steps at every depth.

Nothing is being computed and nothing is being compared. The cost is the
*size of the emitted term* and the kernel's well-formedness check of it, which
is the signature of the tail-substitution exponent and of nothing else. A
conversion-side fix — a kernel rule, a shortcut, a spelling — cannot touch a
number whose miss count is zero.

---

## 2. What actually declines, measured

§13.7 item 1 says to run registration as a **listing of what registered and
what declined, with the reason**, because a silent decline looks exactly like a
device that fired and lost. Run that way on the reproducer, the device declines
three times before the dependency gate is ever reached, and each decline is its
own defect.

### 2.1 The stored template is one Ψ binding stale

`register_rec_projs` types the record binder with the **reference**
`El (app(D#tycode_fn^δ; θ̄))`, obtained by `respell_ty` of the declaration's own
template — §4.1's hole-match at the identity spine, which proves the reference
means the template. That match fails for `Cursor`, `Certified`, `Decide`,
`Exists` and `ListElim`, and the dump says why in one glance: every global
reference in the subject is spelled **exactly one higher** than in the
template, and everything else is identical character for character.

`register_ty_code_fn` computes the template, then pushes `D#tycode_fn` into Ψ,
then commits the template *as computed*. `GlobalVar`s number from the end of Ψ,
so from the moment of its own push the stored `template` — and the stored
`stmt` with it — refers to every global one binding too far in. Any
declaration whose lowering mentions a global (`List`, `Nat`'s `Le`,
`list_len`) therefore fails its own identity match. A declaration whose
lowering mentions none (`Pair<A,B>`, `And<P,Q>`, `Iff`, `ListAlg`,
`CollectionLiteral<A>(n)`) matches, which is why the boundary looked like a
dependency boundary and was never in doubt.

**The fix is the precedent already in the file.** `rec_proj_ref_at` reads a
projection's `Π` back out of Ψ rather than remembering it, and rescopes with
`shift_global(var.0 + 1)` off the reference's own variable, because "a stored
copy would carry the global indices of the Ψ it was built in, and every
declaration since has moved them". `TyCodeFn.template` and `TyCodeFn.stmt` sit
in exactly that position — the Ψ prefix *before* the `D#tycode_fn` binding,
which is where a binding's declared type sits — so they take exactly that
rescoping, computed on every read from the current reference. The entry itself
does not change, nothing about the image codec changes (`module_image.rs`
byte 17 round-trips both types verbatim), and the shift self-corrects when an
image is replayed into a different Ψ prefix.

> **Amended 2026-09-15 (implementation), §2.1.** The rescoping is *half* the
> defect, and landing it alone is a regression — measured, in pass 1, as a
> kernel `SubstMismatch` on `lib/x86_64`'s `decode_mov_ri` and a 3.4 % rise in
> the showcase wall. A template global also carries the **telescope's own
> substitution tail**: `u^{·^{|Θ|+d}}` where the subject at a use site carries
> `u^{·^{outer+d}}`. `Holes::tm` compared a `GlobalTm` syntactically, tail
> included, so with the indices repaired the match still compared the two
> *contexts' lengths* and succeeded only where they agree — the identity spine,
> which is exactly what `register_rec_projs` asks at and why pass 1 saw
> registration declines disappear and use-site declines stay. Two edits, both
> in `gendefs.rs`: a **closed** global (a `GlobalTm` substituting nothing) is
> compared by its index alone, since its tail records the frame and nothing
> about the constant; and `instance_of_template` takes the **subject's frame**
> as its substitution tail instead of hard-coding `·^{|Θ|}`, so the copy step 2
> compares — and the copy the *inverse* (`unspell_here`, `unspell_ty_deep`)
> hands a structural reader — is spelled in the context it is read in. Without
> the second, a repaired index produces a wrongly-tailed emitted term rather
> than a decline, which is where the `SubstMismatch` came from. The frame the
> inverse needs is read off the spine head's own substitution tail
> (`spine_frame`), which `gen_ref_deeper` writes and nothing else touches, so
> no caller of the inverse has to supply one. `gen_spine`'s weakening of the
> closed statement moved from `shift_local` to the same composition for the
> same reason: `shift_local` keeps the stored `·` base where the frame may end
> in a context variable.
>
> **And §2.1's attribution of the `List`/`Or`/`Option` rows to this defect is
> wrong.** Those lowerings mention no global at all, and their decline counts
> are byte-identical before and after the rescoping. They are `tag_of`'s
> documented structural over-reach (`closed_type_ref`'s own note) — the same
> mechanism behind the `respell_ty_at … no-closed-code` rows — and not this
> defect. Do not chase them here.

**This is not this round's device; it is a defect this round uncovered.** Its
reach is much wider than records: `instance_match` is §4.1's only route from an
inline instantiation to its reference, and on the reproducer its declines are
dominated — by three orders of magnitude over the record rows — by `List`, `Or`
and `Option`, the library's most-used parameterized declarations. The type-code
device has been declining silently wherever a lowering mentions a global since
it landed. It should be its own
issue and it must land **before** anything below, because everything below is
measured on top of it.

### 2.2 A value parameter is placed only where it occurs bare

With §2.1 fixed, `Cursor` and `Decide` register and `Certified`, `Exists` and
`ListElim` still do not. `Holes::tm` places a value parameter only where the
template spells it as a bare `Var`; anywhere else it demands syntactic equality
with the subject. `Certified`'s `begin` occurs only as `begin.offset` — a
`Fst`/`Snd` chain — and its `relation` only applied; `Exists`'s `P` occurs only
as `P(witness)`. None is ever bare, so none is ever placed.

The matcher may be as incomplete as convenient and can never be wrong: step 2
requires the template *at the recovered arguments* to be the subject
syntactically. So the extension is free of proof obligation — descend into the
term formers a parameter hides behind. Two suffice for every declaration in
`lib/std` and `lib/std/parser`: an **application** (`fun`, `dom`, `cod`, `arg`,
levels compared) and a **projection** (`fst_ty`, `snd_ty`, `pair`, levels
compared), with the type slots handed to `Holes::ty` at the right depth. With
those two, every record in the reproducer registers and the decline listing is
empty.

### 2.3 A type parameter occurs as a *code*, in a term slot

Registration is then complete and **every use site still walks**, declining at
`instance_args`. The dump again: the template spells the type parameter `T` as
`El (Var …)` in a type slot and as the bare `Var` — its *code* — inside the
`app(list_len; …)` and `app(Le; …)` spines it inherits from `Cursor<T>`, and
the subject has the argument's code (`«Nat»`) there. `Holes::tm` places only
value parameters (`i ≥ np`), so a type parameter in a term slot falls through
to equality and the match dies.

The fix decides a small representation question the design should state rather
than discover: **a hole is recovered as a code, not as a type.** A type slot's
hit is `code_of` of the strengthened subject type, a term slot's hit is the
strengthened subject term, and the two agree by construction — where recovering
one as `Type::Nat` and the other as `El ⌜Nat⌝` would disagree syntactically and
decline for spelling. `instance_match`'s step 2 then substitutes the codes
directly (it quoted them anyway) and the recovered *types*, which only the
emission of the arguments needs, are `decode_deep (El l c)`.

> **Amended 2026-09-15 (implementation), §2.3.** "The two agree by
> construction" is true of the *matcher* and not of the **subject**, and the
> difference is measurable: `Cursor` still declines 926 times on the showcase
> with `hole-match-type-hole/two-occurrences-disagree`. At an **open**
> argument both slots carry the parameter's own variable and the recovery is
> exactly as described. At a **closed** one the subject spells the same
> argument two ways: a binder's type is a *structural read* and keeps the
> inline lowering (`docs/annotation-component-respell-design.md` §2.5's own
> rule), while the type argument of an application is an *annotation* and went
> through the chokepoint, so it is `El (D#tycode^δ)`. `code_of` of the two is
> `TmSum(…)` against `D#tycode^δ`. **No recovery can fix this**, because step 2
> then compares the template at whichever was chosen against a subject that
> contains both — so the matcher is not the place: this is §3.2's "spell both
> sides alike" at the *elaborator's own* type-argument/binder-type boundary, and
> it is the next slice. `wf.rs mod dependent_telescope` states it as a
> to-be-flipped assertion. The unreached cases on the showcase are
> `Cursor` (926), `Certified` (196), `Failure` (105) and the dictionary
> records; what still reaches a **field read** through it is small
> (`project_field … instance-args`, ~350 rows over the whole file) because
> most `instance_match` calls are emission-time, where a decline only keeps a
> spelling.
>
> The second residue the listing now names is `hole-match-Wf/El`: the stored
> template is inline by construction and a subject that arrives *already
> emitted* carries a reference at the same node. That is the same disagreement
> from the other side and the same next slice.

### 2.4 What that leaves

The three above are prerequisites, not alternatives: with any one of them
missing the device registers for some declarations and not for others, and a
half-landed slice is a **regression**, not a small win —
`docs/per-instantiation-type-codes-design.md` §3.1's ~1000× reference-vs-inline
pairing is the whole reason. The spike measured that too: with `Cursor` named
and `Certified` not, the reproducer's two-receiver item is *slower* than with
neither named, and gains conversion misses and evaluator steps where it had
none. Spell both sides alike or neither.

---

## 3. The device

With §2 in place, the device itself is the closed triple with the
declaration's own telescope `Θ` in front — `tycode_fn_telescope`'s `Θ` and
`ā`, the same ones `register_ty_code_fn` and the simple telescoped `D#projⱼ`
use:

```text
D#recfamⱼ : Π Θ. Π(v : R). Π(x : Fⱼ). Ty l'          := λΘ. λv. λx. ⌜Sⱼ⌝
D#projⱼ   : Π Θ. Π(v : R). Fⱼ                         := λΘ. λv. fst(sndʲ v)
D#tailⱼ   : Π Θ. Π(v : R). El (D#recfamⱼ^δ Θ v πⱼ)    := λΘ. λv. snd(sndʲ v)
```

with `R = El l (app(D#tycode_fn^δ; θ̄))` — **the reference, not the template**,
§13.2's load-bearing choice, unchanged and for the unchanged reason: the
domain at a use site's `ā` *is* the receiver's own type, so the kernel's `App`
rule matches it syntactically instead of decoding it once per field read.

The tails stay **codes**. §13.2 rejected the named tails at a telescope on the
ground that a telescope registers only non-dependent spines, where nothing is
substituted into a tail and the code costs δ per entry per read at evaluation.
That argument does not survive the dependent case: here a written-out tail *is*
the exponent, which is what `RecFam`/`RecTail` exist to bound, and what §1's
zero-miss zero-step table says is the entire cost.

### 3.1 What changes in the code

Remarkably little, because the 2026-09-10 fix pass already wrote both builders
over a telescope and then gated one of them off.

- **The gate** (`gendefs.rs`, `register_rec_projs`). Today
  `let simple = telescoped;` and `if record_spine_is_dependent(…) == telescoped
  { return; }`. It becomes: compute `dependent` once; decline only the closed
  non-dependent case (§13.6's own deliberate omission, unchanged); and
  `simple = telescoped && !dependent`. Four combinations, three devices, one
  predicate — the *dependency* test chooses the shape and the *telescope*
  chooses whether there is a `Θ` in front, which is what the two axes were
  always about.
- **The three builders** (`push_tail_fam`, the two `push_proj_def` calls).
  Unchanged. Both already take `tel`, wrap the statement with `wrap_tel`, the
  body with `wrap_tel_lam`, and saturate the occurrence with
  `tel_self_args(tel.len(), 1 | 2)`. `shift_tel` already moves the telescope
  across every push, and `instantiate_fam` already instantiates the family at
  the projection in `Γ = ·, θ̄, v`. The spike changed none of them and they
  register for a four-field dependent telescoped record on the first attempt.
- **`saturate`'s arity.** Unchanged, and must stay `<` rather than `!=`
  (§13.10): a `D#projⱼ : Π Θ. Π(v : R). Fⱼ` whose field type is itself an
  arrow has more `Π`s than arguments, and the parser's records are full of
  them (`relation`, `Parser`'s `run`).
- **`rec_proj_ref_at`.** Unchanged. It reads the `Π` out of Ψ and rescopes off
  the reference's own variable — which is, note, the discipline §2.1 says the
  `TyCodeFn` entry is missing.
- **`project_field`'s use site** (`inductive.rs`). One condition, §4.

### 3.2 What the spike measured, including what it did not fix

With §2's three layers and this gate, every record in the reproducer registers
(the decline listing is empty) and every field read takes the reference. The
shape of the result, at `--kernel-workers 1` on one box in one session:

- **The exponent is gone from where §1 found it.** Emission time and resident
  memory both *fall* at every depth — at three chained receivers the emitted
  term is small enough that peak RSS drops by more than half — and the
  four-receiver item, which used to abort the allocator, **checks**.
- **It is not yet linear.** The per-receiver growth factor falls, but it is
  still large, and the four-receiver item that now passes is slow. What moved
  is *which* cost: misses and evaluator steps rise from exactly zero to tens of
  thousands, while emission and RSS fall. The device converted a term-size
  problem into a conversion problem, and won on the trade but did not end it.
- **The residue has one name.** The conversion-miss table's top row for the
  three-receiver item is `El(?)` against `Wf` — a reference meeting an inline
  lowering — for about a quarter of the item. That is §3.1's "spell both sides
  alike" at the *new* device's own slots, the same finding §13.8 made about the
  first telescoped device (its components were inline and every use site read
  its annotations back out of them). The definitions' statements, the
  recovered **value** arguments (only the type arguments go through
  `emit_ty`/`code_of` today) and the `App` annotations `saturate` reads off the
  `Π` are the three places to look.

So the implementation round is the device **and** a spelling pass over its own
slots, gated together by §9 item 3. Landing the device alone reaches a pass
where there was an abort and is worth having; leaving the spelling row
unaddressed leaves most of the win on the table.

> **Amended 2026-09-15 (implementation), §3.2.** Of the three places named
> above, **one** carried it and it is the first: the declaration's own
> **telescope domains**. A `Π` domain is an annotation slot like any other,
> and this one is read back at more `App` nodes than most — `gen_spine` writes
> it into every argument of a code-function spine and `saturate` into every
> argument of a `D#projⱼ` spine — so left inline it meets, at each of them, the
> reference the argument's own type carries. That is the `El(?)`/`Wf` row.
> `Elaborator::emitted_tel` (`gendefs.rs`) puts the domains through
> `annotation_type`, once, and both `register_ty_code_fn`'s statement and
> `register_rec_projs`'s `tel` read that one list. `shift_tel`, which was a
> no-op while the domains were inline, becomes load-bearing and was already
> right. Only the domains: `tycode_fn_telescope`'s `cx`, `targs` and `vargs`
> stay structural, because `lower_instance` builds the **template** from them
> and the template is the inline identity §4's inverse re-lowers against.
>
> It was not found by the trace. The **emission walker** found it first, as
> `App.dom`/`App.cod` findings on a telescoped dependent record's field read
> (`wf.rs`'s `a_record_field_type_and_its_use_site_spell_a_computed_receiver_alike`,
> which fires the moment the device registers for `Pack<A,B>(seed)`) — a
> sampler row and a walker finding being the same disagreement seen from the
> kernel's end and the elaborator's, exactly as
> `docs/annotation-component-respell-design.md` §2.5 says.
>
> The other two are **not** this round's, and one of them has no machinery to
> be done with. The `App` annotations `saturate` reads off the `Π` are the same
> slots as the statements', so they are fixed by the same edit. The recovered
> **value** arguments are *terms*, and the chokepoint is a type-slot
> chokepoint: `emit_ty`/`annotation_type` have no term-side twin, and inventing
> one to respell the types buried inside a recovered term is a round of its
> own. No measured row was attributed to it here.

### 3.3 What is deliberately *not* unified

The closed device and the simple telescoped device stay as they are. The
unification is not free: the closed device's domain is the inline `⟦D⟧` and a
closed receiver's type is `El (D#tycode^δ)` (§13.6's third bullet, an
untouched boundary with its own argument), and the simple telescoped device's
whole point is that a non-dependent spine's `D#projⱼ` body is one
`fst(sndʲ v)` the kernel walks in `j + 1` steps with no δ at evaluation. Both
are measured into place. This round adds a fourth cell to the table and moves
neither of the other two.

---

## 4. The receiver gate

`receiver_admits_reference` (neutral, and not a bare `Var`) stays **exactly as
it is for a non-dependent telescoped record**, and the dependent device is
**exempt from it, at every receiver, exactly as the closed device is**.

The argument is the one §13.10 already made for the closed device, with the
evidence now on the other record shape. The gate exists because a projection
reference is cheap to *compare* and dear to *compute through*: δ + β per read
per level, which is what `caller_native_memory_same_27/28` could not afford and
what the bare-`Var` narrowing of 2026-09-13 was for. That trade is a real one
only when the alternative is linear. For a **dependent** spine the alternative
is the exponent — which is why the closed device has never had a receiver gate
and why a literal receiver is the case that needs it most — so the dependent
telescoped device inherits the closed device's exemption rather than the
telescoped device's gate.

Two facts make this safe to say rather than hope.

- **The payers are on the other side of the same predicate.** Every record the
  fuel evidence is about — `MachineState<M>`, `StackAccess<M>`, `And<P, Q>`,
  and the twenty-eight-state chain of `reused_callee`'s certificate — has a
  **non-dependent** spine and keeps today's gate untouched. The dependent
  telescoped declarations on the x86 side are `CollectionLiteral<A>(n)` and
  `Monoid<A>`, neither of which a certificate computes a chain through.
- **The gate would make the round pointless anyway.** `close_body`'s reads are
  `op.end`, `op.value`, `op.evidence`, `inner.end`, `close.forward` — every one
  off a **bare** binder, which is precisely what `receiver_admits_reference`
  declines. Keeping the gate for dependent records would register `3·nfields+1`
  definitions per parser record and use none of them.

The stability property the 2026-09-13 narrowing was defending is *stronger*
here, not weaker: firing at every receiver is the spelling that survives
substitution unconditionally, because there is no receiver shape at which the
two sides disagree. The one-sidedness that broke the 20-node rail cannot
recur within the dependent cell.

Verification items 3 and 4 of §9 are the ones that would refuse this.

---

## 5. The repeated closed `Pi/Pi` comparison

This section is the one below that was *not* probed on its own shape — the
reproducer's record has no function-typed value parameter, so what follows is
reasoning from the attribution plus a probe (`probes/t_pcr3.hthr`) written
against the real `Certified` and left for the implementation round to run.

`HEATHER_CONV_MISS_TRACE=close_body` puts all of that item's misses on one
closed `Pi/Pi` comparison — the type of a partially applied
`Recognized<…>` relation against `Certified`'s `relation` parameter domain —
repeated inside `Fst`/`Snd` chain annotations at up to twenty-one binder
depths — and, summed, for barely a tenth of that item. The count is the
striking thing about it; the seconds are not.

**Expect the device to remove most of the occurrences without addressing the
comparison.** The comparison is dear because it is repeated per node of a
chain per binder depth; a named projection replaces the whole chain with one
application spine whose `dom` annotations are read off `D#projⱼ`'s own
statement, so the same `Π` is written once per read instead of once per node
per depth. The count should fall by the depth factor; the per-comparison cost
should not move at all.

> **Amended 2026-09-15 (implementation), §5.** The prediction is **wrong in
> sign and right in kind**, and the trigger has fired. On the showcase the
> `Pi`/`Pi` row goes 23 711 / 4.23 s → 47 010 / 4.87 s and is the **top row on
> the changed side** — not because the comparison got dearer (it got cheaper
> per occurrence) but because there are twice as many. The reasoning above had
> the replacement backwards: the device does not only delete `Fst`/`Snd` chain
> nodes, it makes `D#projⱼ`'s statement carry that `Π` explicitly and
> `saturate` writes it into the `App` annotations of **every** field read.
> Against it, the row the device exists to remove halves (`Sigma`/`El⌜⌝`
> 33 757 / 3.64 s → 16 744 / 1.62 s) and every total falls, so the reshape is a
> trade taken and not a regression. §5's own trigger — "`Pi`/`Pi` a top row
> **after** the device has landed" — is therefore met, and the follow-up it
> names stands unchanged: name a declaration's function-typed value-parameter
> domain. That is a new definition kind rather than a spelling change, so it
> is still not this round's.

What remains is a spelling question and **not this round's**: a value
parameter of function type has no name today, so `annotation_type`/`emit_ty`
can respell the `Π`'s components (they bottom out in `Cursor<T>` references
already) but not the `Π` itself, and the emission chokepoint has nothing
shorter to write. File it as a follow-up on
`issues/elaborator-canonical-type-spelling.md`'s line — *name a declaration's
function-typed value-parameter domain* — triggered on the next run where
`Pi`/`Pi` is a top row **after** the device has landed. Doing it in this round
would be measuring one change with another moving.

---

## 6. Kernel work: rejected, and why in one paragraph

The user opened the door to a kernel change if the elaborator device could not
reach linear. It does not reach linear (§3.2) — and the kernel is still the
wrong place, for two measured reasons in sequence rather than one.

**Before the device**, §1's table is zero misses and zero evaluator steps at
every depth. The kernel is neither converting nor computing; it is *checking a
term that is exponentially large*, and no conversion rule, shortcut or
`Fst`/`Snd` amendment makes a large term small. The size is created in
`crates/elab` by substituting an annotated projection node into a tail, and the
only thing that removes it is not writing it.

**After the device**, misses are real and are the residue — but the top row is
`El(?)` against `Wf`: an elaborator-minted reference meeting an elaborator-emitted
inline lowering. Both sides are ours. A kernel taught to see through one
spelling into the other would be paying, per conversion, for a decision the
emission chokepoint makes once — which is exactly the trade
`docs/per-instantiation-type-codes-design.md` §3.1 quantifies at ~1000× and
§13.6's last bullet already refuses. The fix is to stop writing two spellings
(§3.2), and the measurement to justify a kernel rule does not exist until that
is done.

So the standing line (§8/§9 of the type-codes design, and the project's
"verified fancy kernel later" rule) is kept, and kept on this round's own
evidence rather than by citation. If a kernel slice is ever opened for this
family, the shape to open it on is the third route of
`issues/record-projection-defs-declaration-cost.md` — deciding
`D#projᵢ^δ ā v ≡ D#projᵢ^δ ā v` on the spine without unfolding either side —
and the prerequisite for even proposing it is a post-spelling-pass table in
which that comparison, and not a spelling row, is on top.

---

## 7. Declaration-time cost, and persistence

**Cost.** A telescoped dependent record moves from 0 Ψ bindings to
`3·nfields + 1`, and its declaration item's time moves with it — on the
reproducer, from roughly the noise floor to a substantial fraction of a second
for a four-field record whose fields are equalities over `Cursor` projections.
That is `issues/record-projection-defs-declaration-cost.md`'s cost, arriving at
a second family of records, and it is paid **once per declaration** against a
per-read exponent. The three routes that issue lists (lazy registration at the
first projection, a cheaper unfold, a conversion that decides
`D#projᵢ^δ v ≡ D#projᵢ^δ v` on the spine) all stay its own; this round adds a
customer to it and no new argument. The implementation round should add the
reproducer's declaration items to that issue's table.

Two consequences worth stating before they are discovered:

- the cost lands on *library* declarations, so it is paid once per module image
  and replayed thereafter, not once per client;
- a record that is telescoped, dependent and **large** is the shape where the
  cost is worst and the benefit is largest; there is no size at which the
  ordering flips, because one side is linear in the spine and the other is
  exponential in it.

**Persistence.** Nothing changes. `GenDef::RecProj/RecTail/RecFam(tag, j)` are
keyed per *declaration*, and a declaration is either telescoped or it is not,
so the same key carries the parametric definitions with no ambiguity — image
bytes 9/10/11 unchanged, nothing persisted per instantiation (§13.5). What
moves is the **count**: every fixture asserting `psi().bindings.len()` over a
module that declares a telescoped dependent record moves by `3·nfields + 1`
per record, and the prelude's own `CollectionLiteral<A>(n)`, which §13.5
recorded as declining, now registers. §2.1's rescoping changes no bytes either:
the entry is serialized as it is and rescoped on read, so an image replayed
into a different Ψ prefix self-corrects.

---

## 8. Rejected shapes, with reasons

- **A kernel rule for `Fst`/`Snd` through a code reference.** §6. Before the
  device, zero misses is the refutation; after it, the residue is a spelling
  disagreement between two elaborator-chosen spellings. §13.6's last bullet is
  the standing rejection and it still holds.
- **Landing the device without the spelling pass over its own slots.** §3.2.
  It is a real improvement — an abort becomes a pass — but it leaves the
  larger part of the win unclaimed and leaves a `El(?)`/`Wf` row that reads,
  from outside, exactly like a device that fired and lost.
- **Keeping `receiver_admits_reference` for the dependent device.** §4. It
  would register every definition the parser needs and use none of them, since
  every read in `close_body` is off a bare binder.
- **Minting the reference at every receiver for the *non-dependent*
  telescoped device too.** Not retried. Re-measured twice (2026-09-10 and
  2026-09-13) and refused both times by
  `caller_native_memory_same_27/28`; the dependency test is what keeps this
  round out of that cell.
- **A separate, simpler definition for a dependent telescoped spine** — the
  simple `λΘ. λv. fst(sndʲ v)` with the tail written out. It *is* the
  exponent: the tail at entry `j` is the whole rest of the record with the
  earlier projections substituted in, which is the thing §1 measures.
- **Registering lazily, at the first projection.** `issues/record-projection-
  defs-declaration-cost.md`'s own first route, and still blocked by the
  expression path being `&self` throughout. Not this round's; naming it here
  only because §7 makes it more attractive, not less.
- **Fixing the stale template by shifting at commit time** (storing
  `template.shift_global(1)`). Wrong for the general case and right only for
  the next instant: every later push moves it again. The rescoping belongs on
  the read, off the reference's own variable, which is the discipline
  `rec_proj_ref_at` already documents.
- **Recovering a type-parameter hole as a `Type`.** §2.3. The same parameter is
  hit in a type slot and in a term slot, and the two spellings (`Nat` and
  `El ⌜Nat⌝`) disagree syntactically; recovering the **code** makes them one
  by construction.
- **Making the matcher complete.** Not attempted and not wanted. Two formers —
  application and projection — cover every declaration in `lib/std` and
  `lib/std/parser`, and each further former is a decline that costs today's
  spelling, never a wrong answer.

---

## 9. Verification items for the implementer's first hour

Stop and report if any of these fires; each would refute part of the design.

1. ~~**The rescoping lands first, and on its own.**~~ **Superseded 2026-09-15
   (implementation), §9 item 1.** Pass 1 ran this item and it refuted itself.
   With the rescoping alone in the tree the decline listing keeps its
   `List`/`Or`/`Option` rows (they were never this defect — see the amendment
   on §2.1), the showcase wall rises 3.4 %, `Wf/El(?)` goes 1 374 → 46 159,
   and the full suite goes **red**: the kernel refuses `lib/x86_64`'s
   `decode_mov_ri` with `SubstMismatch`. That is §2.4's own prediction arriving
   as a measurement — with `Cursor`/`Decide`/`Failure` named and
   `Certified`/`Success`/`Exists`/`ListElim` not, a reference meets an inline
   lowering at one side of every comparison — so the isolation this item asks
   for is not available: the slice has no green intermediate state. **The whole
   stack lands together and is gated on totals, not on head-pair
   monotonicity** (which item 6 asks for and which §2.4 says the intermediate
   states cannot have). The pass's own discipline instead: each step verified
   by the decline listing before the next, and the totals of items 3–5 as the
   bar.
2. **A decline listing, not an assertion.** Instrument `register_rec_projs`
   and `project_field` to print declaration, field and reason, and run it on
   `probes/t_pc1.hthr` and on `docs/showcase/calc_parser.hthr`. The expected
   listing is: no `#projdecline` at all, and no `#projwalk` for `Cursor`,
   `Success`, `Certified`, `CachedCursor`, `RecognizedHead`. A decline among
   those means one of §2's three layers is still missing — and a silent
   decline looks exactly like a device that fired and lost (§13.10).
3. **The reproducer, before and after, on one box in one job.** `probes/t_pc1`
   … `t_pc4` and `t_pcev3` at `--kernel-workers 1`, reporting per item
   `total_ns`, `kernel_gate_ns`, `decl_emit_ns`, `eval_steps`, `conv_misses`
   and `/usr/bin/time` maxrss. The expected **shape** is the point, not the
   seconds: the per-receiver growth factor collapses from more than an order of
   magnitude to a small constant, `t_pc4` checks instead of aborting, and the
   declaration items rise by a bounded amount that does not grow with chain
   depth. Misses and steps rise from zero — that is the reference being
   compared and computed through, and it is only acceptable while the totals
   fall.

   **Expect the device alone not to clear this item.** §3.2: the spike reached
   a pass at four receivers and a large fall in emission and RSS, with the
   growth factor reduced rather than removed. The gate for the round is the
   device *plus* its spelling pass, and the discriminator between "still
   working" and "wrong" is the conversion-miss table: if `El(?)`/`Wf` is the
   top row, the spelling pass is unfinished; if something else is, re-attribute
   before changing anything.
4. **The x86 rails do not move.** `crates/elab/tests/function_ir_x86_scaling.rs`
   and the native certificate gates, whose records are **non-dependent** and
   must be untouched. `caller_native_memory_same_27/28` inside the default
   fuel. A regression here means the dependency test is not partitioning what
   §4 says it partitions.
5. **The showcase checks, serially, inside the default fuel.** The paren-path
   refl theorems of `docs/showcase/calc_parser.hthr` (`parentheses`,
   `nested_parentheses`, `missing_close`) must still check, and
   `calc_parser`'s whole-file serial time and RSS are the round's bar.
   `close_body` and `parser_primitives::complete_post` are the two items to
   name in the table.
6. **Spelled alike, or not at all.** No head-pair count may rise on the
   showcase run. §2.4: a half-landed slice is a regression, and the observable
   signature is conversion misses and evaluator steps appearing on an item that
   had none.
7. **The suite's `psi().bindings.len()` fixtures.** §7. They move by
   `3·nfields + 1` per telescoped dependent record, the prelude's
   `CollectionLiteral<A>(n)` included. A fixture that moves by a *different*
   amount means a spine registered under the wrong shape.
8. **Existing tests stay green.** `crates/elab/tests/record_projection_size.rs`
   (the closed device — its parameterized-record fallback test now exercises
   the *new* route and its assertion has to be re-read, not just re-run),
   `annotation_cost.rs`, `records.rs`, `parser_library.rs`,
   `showcase_calculator.rs`, and the x86 rails of item 4.
9. **The new tests vary the four axes and carry their controls**
   (`docs/testing-generated-terms.md`): a **literal** receiver (an assembled
   record value) and a **neutral** one (a parameter, *and* a bare binder, which
   §4 newly admits); an **open** element type, so nothing is fixed by the
   declaration; a **checking** position — the projected field used as the proof
   of a stated theorem, so a wrong type is a rejection and not a different
   term; and, as negative controls, a false equation refused, a neighbouring
   field refused for this field's statement, and a **wrong-instance**
   application refused **by the kernel rather than by a guard**. The last is
   the one that says the reference means what it claims: `D#projⱼ` applied to
   the wrong `ā` must not typecheck.

---

## 10. Status

Design only. No source change lands in this pass; the spike that measured
every claim above was reverted, and `probes/t_pc*.hthr` plus the decline
listing are what the implementation round starts from.
