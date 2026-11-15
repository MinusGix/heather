# Naming a parameterized declaration's lowering at each instantiation — design

Deliberate perf round on `issues/per-instantiation-type-codes.md`, 2026-09-10.
The fourth slice of `issues/elaborator-canonical-type-spelling.md`. The three
before it made every emission site *spell one type alike*; this one gives a
name to a type that has none, so that the kernel's own substitution produces
the same spelling the elaborator emits.

Every mechanism below was hand-run before it was written (`tycodefn_probe.rs`,
a throwaway child module of `gendefs.rs`, and `t_infer.hthr`, both in this
round's scratch); what each probe showed is quoted where it decided something.

## 1. The datum

`register_ty_code`'s `params`/`valparams` guard names `⟦D⟧` only for an
unparameterized, unindexed declaration, so every instantiation of a
parameterized or value-indexed one is a monomorphized inline `Type` no
reference can stand for. The issue body lists three measured consequences and
owns their numbers; the one chartered here:

an implicit type argument solved as a code literal (`M := List<BitVec(8)>`) is
written by `apply_implicit`'s discharge into the whole spine's annotations as
`El ⌜Wf…⌝`, and **the kernel's own instantiation of the callee's codomain at
that argument yields the same literal** — so re-emitting the spine decoded only
moves the miss to the Π check (issue log 2026-09-10: measured a net loss and
reverted). Only a reference removes it.

The shape reproduces at twenty lines: `t_infer.hthr` is a record `Holder<M>(k)`
whose implicit type parameter inference solves to `Box<Flat>`, applied in a
two-deep chain. Under `HEATHER_VALUE_METRICS` its `chain` item's top miss is
`Sigma`/`Sigma`, and `HEATHER_CONV_MISS_TRACE=chain` puts it at
`Var < Case < Case < TmWf < TmWf < App < App < App < App < Lam` — inside a
`TmWf` code payload, in the application spine's annotations. That is
`FetchedFrom<M>(…)`/`static_elf64_access()` with the library removed.

## 2. The definition (one per declaration, not one per instance)

Per **parameterized or value-indexed**, unindexed declaration, registered off
`register_ty_code`'s own lowering machinery in the branch its guard currently
returns from, through the unchanged `push_gen_def` gate — a closed λ in
`LocalCtx::nil()`, the `GenDef::ArityFn` precedent:

```text
D#tycode_fn : Π(A₁ : Ty l₁)…(Aₙ : Ty lₙ)(v₁ : T₁)…(v_m : T_m). Ty l
           := λ(A₁ : Ty l₁)…(v_m : T_m). ⌜⟦D<El A₁,…,El Aₙ>(v̄)⟧⌝
```

The body is `code_of` of `lower_instance` run with each type parameter bound to
`El lᵢ (Aᵢ)` and each value parameter to its own binder — exactly the
`Cx::tyvars` shape a `(A : Type<l>)` binder already installs (`expr.rs`'s
`extend_lambda_context`). Nothing new lowers.

**Probe (A).** Registration passes the kernel gate for `Box<A>`, `Two<A, B>`,
`BV(n)` and `Mixed<A>(n)`. The Π is dependent in general — a value parameter's
type may mention an earlier parameter — so the reference's application spine
carries the *remaining* Π as its `cod`, not a constant.

**Amended (2026-09-13).** The body quotes `emit_ty` of the template, not the
template: the raw lowering behind the reference met the chokepoint's respelled
annotations component by component at every projection out of a global-headed
receiver, and the components' own δ was the whole `Sigma`/`El(?)` bucket of
the x86 call certificates (`docs/record-projection-reference-design.md` §9.8).
The stored `TyCodeFn.template` stays inline: it is what §4's inverse
re-lowers against, and the elaborator's `whnf` of a reference never sees the
kernel's decode.

A value parameter is abstracted by an ordinary Π over its type — a value index
is a `Term`, not a code, the same asymmetry `ArityFn` established. Unlike
`ShapeCode`/`ArityFn` there is no pair: one function names the whole type.

### 2.1 Levels: one level profile per definition

The elaborator mints no level variables — `Level::Var` occurs in
`crates/elab` only inside `module_image`'s codec — so a type parameter's level
is whatever its instantiation's is, and one closed λ fixes one profile.
Registration is therefore at the **all-parameters-`Ty 0`** profile, and that is
the boundary.

Enforcing it costs nothing: §4's guard compares level slots with everything
else, so a higher-level instantiation fails to match and keeps today's inline
spelling. Probe A confirms the kernel is not the obstacle — the same
construction registers with `A : Ty 1` — so widening later is a *key* change
(intern the profile to a `u16` beside the tag; `GenDef` stays `Copy`), not a
scheme change. §12 item 4 counts rather than guesses.

### 2.2 The boundary, otherwise

Inherited verbatim from `register_ty_code`: unindexed (an indexed family's
use-site type mentions its index — `GenDef::Fam`'s business; this is reached
only off `register_gen_defs`' unindexed branch), `code_of` of the open lowering
succeeds, and `tag_of` of it routes back to *this* declaration — the
recognizer's own precondition checked rather than assumed. Best-effort like
every other `GenDef`: nothing registered means every occurrence stays inline.

Registration also commits, for §4's guard, the **open template** (the very type
quoted into the body) with its parameter levels, its value parameters' types
and the instance level. One entry per declaration, and the guard needs nothing
else — which is what keeps §7 small.

### 2.3 The rejected alternative, costed

A closed memo per *instantiation*, keyed like `Representations::monomorphs`
and minted at a Ψ-safe point, loses on four counts and wins on one.

Loses: the key carries the argument vector, so `GenDef` stops being
`Copy + Hash` on a bare `u32` and the image codec grows a term serializer in
its key encoding (§7); minting mid-declaration is unsound because `GlobalVar`s
number from the end of Ψ (issue log, 2026-09-06), so it must be a pre-pass; a
pre-pass cannot see the instantiations inference discovers, and the chartered
row is exactly one (`M := List<BitVec(8)>` is born in `unification.rs`); and N
instantiations pay N gate checks of a large closed type where one function
pays one.

Wins, honestly: its reference is `El (u^δ)` with no β — one δ to a value the
kernel's glued globals share — where the code function pays δ then β and
materializes the substituted code. §12 turns that into a measured verification
item instead of an argument.

## 3. The reference, and what the kernel does with it

A use spells `El l (app(D#tycode_fn^δ; ā))`, the head from `gen_ref_deeper`
(the substitution tail's length is `cx.gamma.entries.len() + depth`; the
definition is closed and its Ψ index is context-independent) and one
`gen_app`-shaped `App` node per argument. (Amended 2026-11-09: the empty
substitution records nothing, so the head is `gen_ref` at every depth and
`gen_ref_deeper` is gone; the depth paragraph of §4.1 describes a tail that
no longer exists. `issues/empty-substitution-tail-decoration.md`.)

**Probe (B).** `El (app(Box#tycode_fn^δ; ⌜⟦Flat⟧⌝))` passes
`kernel_check_type` at the instance level, converts with the inline
`⟦Box<Flat>⟧` in both directions, converts with itself, and the *wrong*
argument's application does not convert with the instance (the negative
control). The same holds with the argument itself reference-spelled
(`Flat#tycode^δ`), with `Box<Box<Flat>>` (nesting), with `BV(8)` and with
`Mixed<Flat>(8)`.

Arguments compose for free: `code.rs`'s `El` arm is the identity
(`code_of(El t) = t`), so a nested instance's argument is the inner reference
and nothing is ever quoted twice.

**Probe (B3) — the point of the round.** A callee codomain annotation
`El (app(Box#tycode_fn^δ; x₀))`, substituted at `M := Flat#tycode^δ`, is
*syntactically*

```text
El[0](app(u0^{·^0}; [1,1] Ty 0 → Ty 0; u6^{·^0}))
```

— the same term the use site mints. That is the property the 2026-09-10 revert
could not have and cannot be given by any spelling of a literal: substitution
into a reference is a reference.

### 3.1 The cost, and the standing warning from 2026-08-25

The issue records four measured negatives for representations that hide a
structural head behind a global. They apply here as a warning about
*consistency*, not about the shape, and the probe quantifies it — 200
conversions of `⟦Box<Box<Box<Flat>>>⟧`:

| pairing | 200 conversions |
| --- | --- |
| inline vs inline | 42 µs |
| reference vs reference | 42 µs |
| reference vs inline | 44.5 ms |

Reference against reference is syntactic, exactly like inline against inline;
reference against inline is ~1000× either (δ + β + decode, then a walk of the
whole instance in the decode spelling). So `docs/wf-shape-code-design.md`
§3.2's **spell both sides alike** is not an optimization here but the whole
difference between a win and a loss: a half-landed slice is a *regression*
(§12 item 2).

The 2026-08-25 negatives are not repeated because their premise is absent:
there the reference stood where structural readers had to look through it, per
projection. Here it stands only in **emitted** annotations (§8), every
structural read goes through `Elaborator::whnf`, and §4.2 restores the inline
copy there.

## 4. The guard, and the inverse

### 4.1 Minting: recovery is a guess, re-lowering is the proof

`respell_ty` gains a second route, taken only after `ty_type_ref` declines.
Prefilter: `tag_of(ty)` names a declaration `D` that has a `TyCodeFn` entry.
Then

1. recover the arguments by **positional hole-matching** against the
   registered open template. Parameter `i` occurs in the template as
   `El (Var (n−1−i + d))` at walk depth `d`; a value parameter occurs as
   `Var(…)` at the small set of term slots the type walk already passes
   (`Vec`/`Fin` length, `Id`/`SEq` endpoints, an `El`'s code). Every
   occurrence of a hole must agree; everything outside a hole must be
   syntactically identical, levels included.
2. re-lower with the recovered arguments and require `==` with the subject.

Step 2 makes step 1 sound, and that is the design's load-bearing sentence:
**the matcher may be as incomplete as convenient and can never be wrong.** It
declines on a value parameter it could not place, on the `Wf` arity (a term
under the shape's binder, compared by step 2 anyway), on an
unfamiliar former — each decline is today's inline spelling.

**Amended (2026-09-10), implementation pass.** Step 2 is the **template at the
recovered arguments**, not a second lowering. What has to be true is that the
reference's own meaning is the subject, and the reference's meaning *is*
`template[ā]` — so that is what is compared, and the `Wf` arity the matcher
declines to walk is compared with everything else. Re-lowering was tried
first and is both weaker and far dearer: it re-elaborates the declaration's
field syntax at every emission (the mutual-recursion fixtures went from
seconds to 204 s and blew the suite's 4 GB cap), and it needs an ambient
context the emission walk does not carry — `lower_instance` builds
substitutions off the context's *length*, so running it under the walk's
`cx` is a kernel assertion rather than a decline. §12 item 5's memo is
therefore not needed: the guard is now two structural walks. `ty_type_ref`'s
"can only decline" discipline unchanged, at its cost order (one structural
walk of the subject).

Positional, never a scan, which is `issues/tag-types-collide-with-lowerings.md`
answered by construction: a declaration's tag Σ is compared for *equality*
against the template's own tag Σ at the position the template puts it, so no
payload can be mistaken for a tag digit and no tag digit for a payload. It
also settles a second collision the probe surfaced: in `⟦Mixed<A>(n)⟧` the
type parameter and the value parameter are both spelled `x2` at their own
depths (`Σ(El[0](x2)). Σ(Vec[0](Nat; x2)). Unit`). They are never confused
because they live in different *sorts* of slot, and matching is by position
in the template rather than by index anywhere in the subject.

**Probe (C).** The template recovers `⟦Flat⟧` from `⟦Box<Flat>⟧` and both
arguments from `⟦Two<Flat, Flat2>⟧`; `tag_of(⟦Box<Flat>⟧)` routes back to
`Box`; `⟦Flat⟧` does not match `Box`'s template; and re-lowering with the
recovered argument reproduces the subject exactly.

The recovered arguments are then themselves put through `emit_ty` and
`code_of` before the application is built, so `List<BitVec(8)>` becomes
`app(List#tycode_fn^δ; app(BitVec#tycode_fn^δ; 8))` with no literal at any
level.

**Depth.** `respell_deep_at`'s standing argument — "a type equal to the
registry's *closed* copy is closed, so only the tail's length moves" — fails
for an open instance, whose recovered arguments mention binders inside the
walk. So this route mints at depth (`gen_ref_deeper`, tail
`cx.gamma.entries.len() + d`) with the arguments verbatim, instead of minting
closed and shifting after; `gen_ref_deeper` stops having one caller, and that
is its only change. Probe F: an open `El (app(Box#tycode_fn^δ; x₀))` under a
`Ty 0` binder typechecks in that context, converts with `⟦Box<A>⟧` both ways,
and `shift_local(1)` moves tail and argument together (`u0^{·^2} … x1`).

### 4.2 The inverse is mandatory, not optional

**Probe (D).** On `El (app(D#tycode_fn^δ; ā))` today: `unspell_here` returns
`None` (it matches `El { tm: GlobalTm }` and the head is an `App`),
`is_gen_ref` is false (`gen_def_of` cannot be reached through the `App`), and
`Elaborator::whnf` therefore hands a structural reader

```text
Wf[0](El[0](«…»)). case(…)
```

— the kernel's lazy **decode** spelling, `docs/wf-shape-code-design.md` §1.4's
look-alike, which every use-site guard declines. `whnf == inline` is false.
Re-lowering the decoded arguments *does* give the inline copy.

Three edits, load-bearing rather than tidy:

- `gen_app_of(t) -> Option<(GenDef, Vec<Term>)>` — peel an `App` spine to its
  `GlobalTm` head, returning key and arguments. The application-aware sibling
  of `is_gen_ref`/`gen_def_of`; everything below goes through it.
- `unspell_here` gains an arm: on a `TyCodeFn` head, decode each argument
  (`decode_deep` of `El lᵢ argᵢ`; a value argument stands as it is) and
  re-lower. That restores `docs/wf-shape-code-design.md` §3.3's invariant —
  *the elaborator's `whnf` of a reference is the registry's copy, never the
  kernel's decode* — and with it every structural reader and use-site guard.
- `unspell_ty_deep` (the reflection boundary, `len_at`-anchored) gains the same
  arm, so `fn_type_code` and certgen's `sig_peel` still hand a `meta` analyzer
  the inline type. Statements will carry `El (app …)` where they carried
  `El ⌜Wf…⌝` — the same kind of thing they already carry for closed
  declarations; the certgen suite pins it.

Idempotence is free: `tag_of` goes through `decoded`, which leaves an `El` of a
neutral alone — probe D confirms `tag_of(reference) = None` while
`tag_of(whnf(reference)) = Some(Box)`.

**Amended (2026-09-10), implementation pass.** Three corrections, each forced
by the tree.

- *The inverse is a substitution, not a re-lowering.* `unspell_here` has no
  `Cx` and its callers' types may be open, so it instantiates the registered
  **template** at the arguments and `decode_deep`s the result — context-free,
  and exactly what re-lowering would give, since the template *is* the
  lowering with `El (Var i)` in the holes. Type arguments are themselves
  unspelled first, so a nested reference does not survive into the copy a
  structural reader sees. Being context-free is also what lets an instance
  be built once: it is a function of the template and the arguments alone,
  an elaboration asks for the same one many times over at equal arguments on
  other nodes, and the askings come close together, so a small table by
  template and arguments answers them (`gendefs::Instances`, 2026-11-11,
  `issues/template-instance-rebuilt-per-asking.md`).
- *There is a fourth edit, and it is load-bearing.* `unification.rs`'s
  `unify_ty` is a **syntactic congruence**, not a reader that goes through
  `Elaborator::whnf`, so a callee domain arriving off its respelled statement
  as `El (app(D#tycode_fn^δ; ā))` hides the very structure an implicit is
  solved from: `or_pick<P, Q, A>(d: P ∨ Q, …)` stopped inferring `Q` and 63
  library declarations failed with "cannot infer the type argument". Both
  sides are put in the inline spelling before every congruence
  (`unspell_deep_now`, `unify_arg_ty` and `solve_from_expected`) — the
  pattern in the call's scratch world, the subject in the committed one.
  §8's "no structural reader learns the applied spelling" is unchanged; what
  changed is that `whnf` is not the only place it has to be restored.
- *Three more readers had to be told, and they are the same sentence.* A
  structural read that does not go through `Elaborator::whnf` sees the applied
  spelling and must be handed the inline copy where it stands:
  `resolve_goal_from` unspells its goal once at the entry (a class
  instantiation arrives off a respelled binder type, and "the goal type is not
  a class" was 60 library declarations); `display_shape` unspells before it
  takes a `Wf`'s shape (otherwise a diagnostic says `List<…>`); and the `Wf`
  **slot pair** asks its own question — `emit_wf_slots`, the component
  respell — rather than `emit_ty` of the former the two reconstitute, since a
  slot may not hold a name for the whole (§8) and `emit_ty` now offers one.
  `emission_walk`'s slot-pair audit asks the same question, or it reports
  every monomorphized `Wf` in the corpus.
- *A site that shifted after respelling now passes a depth.* `elab_match_data`'s
  tier-0 motive respell was `respell_ty(cx, motive).shift_local(1)` for a
  motive scoped over `(Γ, z : ⟦D⟧)`; the closed route cannot tell the
  difference, the instance route can (§4.1's depth paragraph), and with the
  lie left in place the recovered argument is strengthened against a context
  one entry too short — a kernel assertion, not a decline. It now calls
  `respell_ty_at(cx, motive, 1, 0)`.

## 5. The quote slice — in, and separable

`code_of` itself does not change; it is a pure syntactic quote and the
reflection boundary reads it as such. Its two callers take the respelled type:

- `lib.rs` ~5985, a **written** type argument `f<List<Nat>>`:
  `code_of(emit_ty(a_ty).unwrap_or(a_ty))`.
- `unification.rs` 113–142, `El ?A ≟ T ⇒ ?A := ⌜T⌝`: after `strengthen_ty`,
  `code_of(emit_ty(s))`.

The second is the chartered row's origin — where `M := List<BitVec(8)>` is
born, and the only place a solution can be reference-spelled *before*
`apply_implicit`'s discharge writes it through the whole spine.

**Amended (2026-09-10), implementation pass.** The respell is at the
**discharge**, not inside `unify_ty`: the solver is a free function with no
elaborator, and — since §4.2's fourth edit now unspells both sides before
unifying — a solution read off the inline subject is a literal by
construction. `apply_implicit` puts each solved slot whose declared domain is
`Ty l` through `respell_solution` (`code_of` of `emit_ty` of `El l ⌜T⌝`) as it
builds the discharge substitution. That is one place instead of one per
solving rule, and it is where the world is known: a solution is scoped in the
**committed** Ψ, not the scratch one — `apply_global`'s payloads are the
substitution's target and the identity region below them is renumbered past
the metavariables — so the entry point is `emit_ty` at scratch 0, not
`emit_ty_in`. (The coordinator's note expected the scratch-aware entry point;
the tree says otherwise, and the `t_infer` chain is the test that pins it.) With §3's
substitution property there is then no third spelling for the `Sigma`/`Sigma`
and `El⌜⌝`/`Wf` rows to miss on.

The first is separable, and the measurement says so plainly: **all 578 of the
five-node module's emission-walk findings are the *closed* literal** —
`El ⌜⟦Instruction⟧⌝` where `Instruction#tycode^δ` already exists, dominated by
`Pair.fst_ty`/`Pair.snd_ty` (236 each). That bullet removes them with no
per-instantiation code at all. §2–§4 are the conv-miss fix, §5's first bullet
is the walker fix; they ride together because they are one sentence ("quote
the type you would emit"), not because either needs the other. The reflection
boundary needs §4.2's `unspell_ty_deep` arm for this and nothing more.

## 6. Open instances, nesting, value parameters

All probed (F): `Box<Box<Flat>>` nests by composing applications; the open
instance typechecks, converts and shifts as a unit (§4.1); `BV(8)` and
`Mixed<Flat>(8)` cover the value-parameter and mixed telescopes — the shapes
`CallMemory(file, stack)` and `FetchedFrom<M>(access, memory, span)` actually
instantiate. §4.1's depth paragraph is the only place `respell_ty_deep`'s
closedness argument had to be replaced rather than reused.

## 7. Persistence and layering

- `GenDef::TyCodeFn(u32)` — one more bare-`u32` variant. `Copy + Hash` is
  unchanged and **the derive does not move**, which is §2.3's fourth reason
  against a per-instance key. Image byte `14` in `module_image.rs`'s
  `put_gen_def`/`get_gen_def`.
- `DeltaEvent::GenTyCodeFn { tag, entry }` beside `GenTyCode` (event byte
  `17`), with `semantic_commit_gen_ty_code_fn` and its replay arm; a
  `GenDefLayer::ty_code_fn` map with `ty_code_fn(&tag)`/`has_ty_code_fns()`,
  sealed-then-current like `ty_code`. The codec already serializes `Type` and
  `Level`, so the event is `GenTyCode`'s shape with two more fields.

  **Amended (2026-09-10):** the entry carries the definition's own **statement**
  (the whole `Π`) rather than a `valparam_tys` list. It is the same
  information and one walk answers both questions a use site asks: the `Π`
  domains *are* the arguments' types, in order and already dependent, so the
  spine's `dom`/`cod` annotations and the re-lowering's `(Term, Type, Level)`
  triples come out of walking it — no second syntax for a telescope.
- Nothing is persisted **per instantiation** — the layering payoff of inverting
  rather than remembering: a type read back from another module's Ψ, or rebuilt
  by substitution, is recognized by the same template as one this module
  lowered.

**Amended (2026-09-10).** One consequence worth stating plainly, because it
is visible in every count: a parameterized or value-indexed declaration now
costs **one more Ψ binding**, the prelude's `CollectionLiteral` included, so
the fixtures that assert `psi().bindings.len()` moved by one.

## 8. Deliberately not touched

- **`lower_instance`.** Unchanged, and still the identity both recognizer
  fingerprints and every structural read anchor on. Not relitigated.
- **`respell_ty_deep`'s `Wf` arm.** Stays exactly as it is, as the *fallback*
  when §4.1 declines (a level profile ≠ 0, an unplaceable value parameter):
  shape and arity respelled together or not at all.
- **Indexed families.** `GenDef::Fam` owns route 1's family function.
- **No structural reader learns the applied spelling.** The line of
  `docs/wf-shape-code-design.md` §4 stands unchanged; §4.2 is what makes it
  affordable.
- **No kernel change.** Nothing in `crates/kernel` moves; every probe above
  ran against the kernel as it is.
- **The `Sum`/`El⌜⌝` row** (925/item on the fetch family, a lowered `match`
  binder against its quoted type) is `issues/elaborator-canonical-type-spelling.md`'s
  quote layer, not this round's.

## 9. Rejected shapes, with reasons

- **A closed definition per instantiation.** §2.3.
- **A contextual code `D#tycode : Trm_c(Δ ⊢ Ty l)` referenced by a checked
  `LocalSubst`.** Measured negative twice on 2026-08-25, and the gate-local
  caching meant to rescue it a third time. Not retried: this design differs in
  *where* the reference may stand (§8), which is the premise those experiments
  violated.
- **Carrying the arguments from the lowering sites to emission by a side
  channel.** `Type` derives `Clone, PartialEq, Eq` and not `Hash`, so no memo
  can be keyed by the type; `Rc` identity does not survive `apply_local`; and a
  session table would need per-instantiation serialization *and* would still
  miss every type rebuilt by substitution or read back from another module —
  most of the x86 workload. Inversion needs no channel and no persistence.
- **Respelling the slots inside `lower_instance`.** Unchanged rejection from
  the two rounds before.
- **Teaching `tag_of`/`decoded` to see through the application.** Same
  rejection as the shape-code round's: it would let references stand anywhere
  and make every structural reader spelling-sensitive.
- **A `Vec`-keyed level profile in the `GenDef` key.** Changes the derive for
  a case §12 has not yet shown to exist.

## 10. Measurement — before and after

One furnace box, release, `-p heather-cli --features value-metrics`,
rev `bc07438`. **The implementation pass re-took the before column on its own
box** (same counts to the digit, seconds ~15 % higher than the design pass's),
so both columns below are that box's; the after column is the finished tree's,
same invocations.

**`heather build-x86 examples/x86-native/mix.hthr mix --arg 0x14 --arg 0b10110
-o … --item-timings out/mix.tsv`** — the `mix_native_loaded_byte` rows and the
`Sigma`/`Sigma` and `El⌜⌝`/`Wf` counts from `out/mix.conv-miss.txt`:

| | before | after |
| --- | --- | --- |
| whole run | wall 186.7 s, RSS 499 MB, 943 rows, 37.36 s item / 28.53 s kernel | wall 193.4 s, RSS 371 MB, 943 rows, **43.84 s item / 37.34 s kernel** |
| `mix_native_loaded_byte_*` | 10 items, 9.17 s / 8.00 s kernel | 10 items, **4.38 s / 3.56 s kernel** |
| per **heavy** byte item (×4) | 1.68–1.87 s total, 1.47–1.66 s kernel; conv-miss 1.09–1.27 s | 0.77–0.83 s total, 0.63–0.69 s kernel; conv-miss 0.42–0.45 s |
| per **light** byte item (×6) | 0.21–0.43 s total; conv-miss 0.22–0.25 s | 0.12–0.23 s total; conv-miss 0.06–0.10 s |
| `Sigma`/`Sigma` (this round's row) | **195 / 0.33–0.39 s** per heavy item, 48 / 0.06 s per light | **gone from every byte item** |
| `El⌜⌝`/`Wf` (this round's row) | **185 / 0.15–0.18 s** per heavy item; 5,751 / 2.42 s over the run | **gone from every byte item**; 0 over the run |
| `Sum`/`El⌜⌝` (the quote layer, §8) | 925 / 0.24–0.28 s per heavy item; 22,211 / 3.02 s over the run | gone from the byte items; 183 / 0.08 s over the run |
| `Vec`/`Sigma` | 8,764 / 0.17 s per item; 79,600 / 5.47 s over the run | 8,764 / 0.20 s per item; 79,982 / 5.00 s |
| `El^δ`/`Sigma` | 8,280 / 0.15 s per item; 81,007 / 2.20 s over the run | 82,933 / 3.67 s over the run |
| `Sigma`/`El(?)` — **the round's own regression** | 1,050 / 9.54 s over the run | **15,998 / 65.1 s over the run** |

The two rows in bold are the acceptance criterion's, and they are met: the
chartered family is **2.1× faster** and neither row survives anywhere in it.

**The regression is real and is §12 item 2's shape, one level up (2026-09-10).**
`Sigma`/`El(?)` is an inline `Σ` meeting an *applied reference*, and it is
what a **projection** costs once the record it projects has a name: the
kernel's `Fst`/`Snd` rule reconstitutes `Σ(fst_ty). snd_ty` from the slot
components and converts the pair's own type against it, and that type is now
`El (app(D#tycode_fn^δ; ā))` — δ then β then a decode of the whole
instantiation, where before it was a syntactic match. The same row exists for
*closed* codes (`Sigma`/`El^δ`, 6.2 k / 6.9 s, unmoved) and has been accepted
since the whole-type codes landed; this is that shape at ten times the count
and ten times the price, concentrated in the certificate's value-heavy items
(`mix_native_source_artifact` 18.4 s, `stack_word_agrees` 11.2 s,
`stack_word_matches` 6.7 s). It is *not* the annotations disagreeing —
`project_field`'s chain and the constructor tuple both take the chokepoint's
spelling (the emission walker's residue on the five-node module went
578 → 260, and every remaining slot is a pre-existing one, dominated by the
`Pair` quote family §5's first bullet halved from 236 to 120 per side).

**The fix is not more spelling but a name for the projection.**
`register_rec_projs` declines for a parameterized record on the same
closedness boundary this round just removed for the type; with `D#projⱼ`
abstracted over the declaration's telescope, a field read is an application of
a definition and no `Σ` is ever reconstituted against the reference. That is
`issues/theorem-field-projection-oom.md`'s device at this round's telescope,
and it is the natural next slice. **It was taken in the same round: §13**,
which attributes the row before designing anything and records what it did and
did not recover.

The rest of the rows are recorded so that a *rise* anywhere is visible.

**`scripts/measure-x86-conv-miss`** (five-node FunctionIR/x86 module, dev):
**578 emission-walk findings**, every one an `El ⌜⟦Instruction⟧⌝` quote that
the chokepoint would write as `El (Instruction#tycode^δ)`; the two largest
slots are `Pair.fst_ty` at depth 0 (236) and `Pair.snd_ty` at depth 1 (236),
with `Supf.shape/arity`, `Lam.dom`, `Inl.rhs`/`Inr.rhs` and `Snd.*` making up
the rest. Test wall 55.65 s. **After: 260 findings** — `Pair.fst_ty`/`snd_ty`
120 each and 20 `App.cod`/`App.dom`/`ElimNat.motive`, all of them slots the
before column already listed; the `Supf.shape/arity` and the whole `Fst`/`Snd`
chain are gone (test wall 61.0 s).

`compile-x86` on the same file has no `loaded_byte` family at all (no ELF
loading): 132 items, 3.28 s item / 2.06 s kernel. Recorded only as the cheap
sanity run — the acceptance measurement is `build-x86`.

## 11. Correctness, and the tests

Every reference is convertible to what it replaces by construction — the
body *is* `code_of` of the very lowering the guard re-derives and compares —
and every position it stands in is one the kernel checks by conversion. A
spelling change end to end, the same conservativity argument as the three
rounds before it.

Tests extend `crates/elab/src/wf.rs mod tycode`, on
`docs/testing-generated-terms.md`'s axes:

- `a_parameterized_declaration_gets_a_code_function_and_a_closed_one_does_not`
  — the registration boundary, mirroring the existing closed-side test.
- `a_value_indexed_declaration_gets_a_code_function` — `BV(n)`, `Mixed<A>(n)`.
- `an_instantiation_is_spelled_as_the_code_functions_application` — structural,
  convertible both directions, idempotent.
- `a_wrong_argument_application_is_not_the_instance` — negative control (axis 4).
- `an_inferred_type_argument_discharges_the_reference` — the chartered row,
  `t_infer.hthr` as source: the spine's annotations carry `El (app …)` and the
  emission walker is empty on it.
- `a_nested_instantiation_composes_the_references` — `Box<BV(8)>`.
- `an_open_instance_under_a_binder_shifts_as_a_unit` — axis 2; the one that
  catches a depth error.
- `a_higher_level_instantiation_declines_and_stays_inline` — §2.1's boundary.
- `a_lookalike_declaration_does_not_match_the_template` — the `mod fingerprint`
  pair, plus a fieldless tag-0 declaration beside them
  (`issues/tag-types-collide-with-lowerings.md` item 3).
- `the_reflection_boundary_unspells_an_applied_reference` — `fn_type_code` over
  a statement carrying one; certgen green is the rest.
- The four axes crossed with the new spelling on a monomorphized constructor
  value and `match`: literal and neutral scrutinee, an open element type, a
  *checking* position, a false equation refused.

## 12. Verification items for the implementer's first hour

Stop and report if any of these fires; each would refute part of the design.

1. **Registration on the real library.** `D#tycode_fn` passes `push_gen_def`
   for `List<A>`, `BitVec(n)` and `MachineState<M>`, not only the fixture. A
   failure means §2's Π/λ shape is wrong for a telescope the fixture lacks.
2. **Spelled alike, or not at all.** After the first site is routed, re-run
   `t_infer.hthr` under `HEATHER_VALUE_METRICS`. If any head-pair count
   *rises*, a site respells one side only — §3.1 says that is a ~1000×
   pairing; the fix is the sibling site, never more fuel.
3. **The inverse lands first.** §4.2's `gen_app_of` + `unspell_here` arm
   **before** any minting site. The other order gives `Elaborator::whnf` the
   decode spelling (probe D) and a scatter of silent guard declines instead of
   a clean error.
4. **The level profile is not a fiction.** Instrument `lower_instance` to count
   instantiations whose parameter levels are not all `0` over `lib/` and
   `examples/x86-native/`. Nonzero and material means the key needs an interned
   profile before the round is worth finishing.

   **Measured (2026-09-10): 0 of 1,544.** Every parameterized instantiation
   `heather check` reaches over `lib/std`, `lib/` and `examples/x86-native/`
   is at the all-`Ty 0` profile. §2.1's boundary costs nothing today.
5. **The guard's re-lowering is affordable.** Count and time the `respell_ty`
   calls reaching step 2 of §4.1 on the five-node module. If re-lowering
   dominates, memoize by `(tag, recovered spelling)` per declaration — a
   session-local cache, not a persisted one.

   **Fired, and answered by removing the re-lowering (2026-09-10).** With
   `lower_instance` as step 2 the mutual-recursion fixtures took 204 s and the
   suite's 4 GB cap killed the target; step 2 is now the template at the
   recovered arguments (§4.1's amendment), two structural walks, and the fast
   lane's test wall is 178–181 s against 184 s before the round. No memo.
6. **`scripts/bench --check`, and the walker's recorded residue shrinks.** A
   slot that *appears* in `ir_v1`'s listing is a site this round taught to
   write a spelling the chokepoint would not — report it, do not add it to the
   list.

   **Held (2026-09-10):** 578 → 260 findings, no new slot; three sites did
   have to be taught (§4.2's amendment) and one of them —
   `project_field`'s walk, which fell to its inline branch because `emit_ty`
   is idempotent and the receiver's type was *already* the reference — was
   worth 87 findings and the whole `Fst`/`Snd` chain.

## 13. Projections at an instantiation

§10 named its own next slice and this is it, written after the measurement it
answers rather than before. Every mechanism was hand-run before it was written
here; the tests in `crates/elab/src/wf.rs mod tycode::tycode_fn` are those
probes kept.

### 13.1 The datum, attributed

`HEATHER_PROJ_PAY` (a throwaway instrument in `project_field`) names every
record whose field read reaches the walk, over the whole `build-x86 mix` run:
**2,250 reads**, against 15,998 `Sigma`/`El(?)` misses — one per `Fst`/`Snd`
node of the chains they build. Grouped by declaration, the payers are:

| declaration | reads | telescope | spine |
| --- | --- | --- | --- |
| `MachineState<M>` | 623 | 1 param, 4 fields | **not** dependent |
| `StackAccess<M>` | 198 | 1 param, 4 fields | **not** dependent |
| `CollectionLiteral<A>(n)` | 166 | 1 + 1, 2 fields | dependent |
| `And<P, Q>` | 151 | 2 params, 2 fields | **not** dependent |
| `Location<A, B>`, `Exists<A>(p)`, `Group<A>(n)`, `Pair<A, B>`, … | 59, 59, 28, 24 | telescoped | mixed |

and the trace agrees: the `Sigma`/`El(?)` sites are `Var < Snd^k < Fst < Fst <
App…` with `El (app(u877; [1,1] Ty 0 → Ty 0; x9))` innermost — a one-parameter
record's chain, at an **open** instance.

That settles the question §10 left open. The closed device declines a
non-dependent spine (`record_spine_is_dependent`) because there the reason to
name is the walk's *exponent*: the payload is substituted into the tails, so a
spine nothing depends on is linear already and the definitions would be all
cost. At a telescope the reason is a different one — the receiver's **type** is
a reference, and the `Fst`/`Snd` rule reconstitutes `Σ(fst_ty). snd_ty` and
converts that reference against it at every node, dependent spine or not. The
measured payers are the non-dependent ones. So the dependency gate is a
property of the closed case and stops being a gate at a telescope.

### 13.2 The definitions

The closed triple with the declaration's own telescope `Θ` in front —
`register_ty_code_fn`'s `Θ`, so that both definitions take the same `ā`:

```text
D#recfamⱼ : Π Θ. Π(v : R). Π(x : Fⱼ). Ty l'  := λΘ. λv. λx. ⌜Sⱼ⌝
D#projⱼ   : Π Θ. Π(v : R). Fⱼ                := λΘ. λv. fst(sndʲ v)
D#tailⱼ   : Π Θ. Π(v : R). El(D#recfamⱼ^δ Θ v πⱼ) := λΘ. λv. snd(sndʲ v)
```

with `R = El l (app(D#tycode_fn^δ; θ̄))` — **the reference, not the template.**
That is the load-bearing choice. Were `v`'s domain the template, then at `ā` it
is an inline `Σ`, and the kernel's `App` rule would convert the receiver's
`El (app(…))` against it once per field read: the very δ + β + decode §10
measured, moved from `Fst` to `App`. With the reference the two are one term —
`dom[ā]` *is* the receiver's type — and the decode is paid once, at the
definition's own gate, where the body's `fst` node meets `Σ(fst). snd`.

**The non-dependent case gets no second shape,** decided rather than inherited.
A tail family is not needed for *correctness* there (nothing later mentions the
field), but it is what bounds the annotation each node carries: written out,
`snd_ty` is the whole rest of the record at every entry, quadratic in the
spine. One shape and one argument, at the price of one Ψ binding per spine
entry.

**Amended (2026-09-10), fix pass: at a telescope there are no companions.**
`D#recfamⱼ`/`D#tailⱼ` are the *closed* device's, and the closed device is
gated to a **dependent** spine, which is the only spine whose tails a payload
is substituted into. The telescoped device is gated the other way (§13.3), so
its definitions are the simple ones — `D#projⱼ := λΘ. λv. fst(sndʲ v)`, the
tail written out, `nfields` definitions and not `3·nfields + 1`. That is the
shape "rejected rather than inherited" above, revisited with the evidence:
the quadratic annotation it was rejected for is a property of a dependent
spine, and it is δ per entry per read *at evaluation* that a certificate
computing through a field read cannot afford (§13.10).

**Probe (G).** Registration passes `push_gen_def` for `Cell<A, B>`,
`Mixed<A>(n)`, `BV(n)` and `Dep<A>(n)` (a dependent telescoped spine); the
applied projection typechecks in its context, converts with the inline walk's
result in both directions, and a **wrong-instance** application is refused by
the kernel rather than by a guard. An open instance's projection shifts as a
unit, arguments and receiver together.

### 13.3 Registration, and where it declines

In `register_rec_projs`, off `tycode_fn_telescope` — the same best-effort gate,
the same all-or-nothing per field (a failure at field `j` leaves `< j`
registered and inlines the rest). The record binder's type comes from
`respell_ty(cx, template)`, which recovers the telescope's own binders as its
arguments — the identity spine — and *proves* the reference means the template
by §4.1's step 2. A decline there is a declaration with no name to use, and it
keeps the inline walk: the case is a value parameter that occurs nowhere in the
lowering (`record Dep<A>(n: Nat) { k: Nat, a: A }` — the matcher cannot place
`n`), which §4.1 already declines for the type.

**Amended (2026-09-10), fix pass: the gate was never the problem.** The
telescoped boundary above is what ships — a telescope registers whatever its
spine does — and the two test binaries that aborted on the allocator
(§13.10) were a defect one layer down, not evidence against it. `saturate`
refused every statement whose `Π` count was not exactly the spine it was
handed, and a `D#projⱼ : Π Θ. Π(v : R). Fⱼ` whose field type is itself an
arrow has more: **every function-typed field declined at registration**.
Declining sent records whose fields are laws — `repr`'s `abs`, `Rp`,
`Repr_ListTok`, `Monoid<A>`'s `op` — back to `project_field`'s exponential
walk, which is the 4 GiB abort `issues/theorem-field-projection-oom.md`
records and the device exists to replace. The check is now `<` (the loop
already refuses a spine the statement cannot take), and with it both targets
are green under *either* telescoped boundary; the inverse gate that was
drafted here was measured, found unnecessary, and removed. The lesson is
§13.7's own: a decline is silent, so a device that declines where it was
measured to fire looks exactly like a device that fired and lost.

### 13.4 The use site

`project_field` asks `instance_args` once, and there are two routes to one
answer: the receiver's type is already `El (app(D#tycode_fn^δ; ā))` and its own
spine *is* the arguments, or it is the inline instantiation and §4.1's
hole-match with its proof recovers them. The second is `instance_ref`'s own
arguments **exposed** (`instance_match`) rather than re-matched — one matcher,
two definitions. `rec_proj_ref_at` then saturates the definition's `Π`,
reading each `App`'s annotations off it (`saturate`), which is where a
dependent telescope's later domains come from. A closed record takes the same
path with an empty `ā`, and `saturate` refuses a spine the statement has no
`Π` for — `<`, not `!=`, since a field type may itself be an arrow (§13.10).

**Amended (2026-09-10), fix pass: the telescoped route asks about the
receiver first.** `project_field` mints the reference only where `value`
bottoms out in a **local** (`receiver_is_neutral`: through `Fst`/`Snd`/`App`
spines to a `Var`). That is the shape §13.1's trace attributes the misses to,
and the shape a reference is *compared* in; a receiver the kernel will reduce
anyway is one it has to compute the projection through, at δ + β per read
per level, which is what `reused_callee`'s certificate could not afford
(§13.10). The **closed** device is exempt and fires whatever the receiver is:
there the definitions exist to remove the walk's exponent, and a literal
receiver is the case that needs them most.

### 13.5 The inverse, and persistence

A projection is a **term**, not a type, so no type-level reader moves:
`Elaborator::whnf`, `unspell_here`, `unspell_ty_deep` and `unify_ty` see
exactly the types they saw. The one structural reader of `rec_proj_ref_at`'s
output is `display.rs`'s `call`, which matched the single-receiver form; it now takes the receiver as the **last** argument of a
spine whose length is the declaration's telescope plus one, and drops the
instantiation as it already drops a call's implicits. Nothing else
pattern-matches a `RecProj` head.

**No new key variants**, and this is worth stating rather than assuming:
`RecProj/RecTail/RecFam(tag, j)` are keyed per *declaration*, and a declaration
is either telescoped or it is not — so the same key carries the parametric
definitions with no ambiguity, image bytes 9/10/11 unchanged, and nothing is
persisted per instantiation (§7's layering payoff again). What does move is the
count: a telescoped record that registers costs `nfields` more Ψ bindings
(§13.2's amendment — no family, no tail), so the fixtures that assert
`psi().bindings.len()` move by that much. The prelude's
`CollectionLiteral<A>(n)` is *not* one of them: its spine is dependent and
§13.3's gate declines it, so the prelude's only new binding is its
`#tycode_fn` and those fixtures move by one.

### 13.6 Rejected shapes

- **A separate, simpler definition for a non-dependent spine.** §13.2 —
  **reversed by the fix pass**: it is not a separate definition but *the*
  telescoped one, and the dependency gate is what keeps the two apart
  (§13.2's and §13.3's amendments).
- **Minting the reference at every receiver.** Tried, and it is what
  `caller_native_memory_same_28` rejected with `OutOfFuel` (§13.10). The
  boundary is the receiver's own head. **Re-measured 2026-09-13** on a tree
  three spelling rounds newer, because the rejection was dated: still refused,
  one item earlier (`…_27`). So is the weaker "one layer of computation"
  bound — `reused_callee`'s own receivers are a single global over three
  neutrals, with the twenty-eight levels inside the definitions.
- **Widening the *closed* device's dependency gate in the same round.** The
  measurement says it would pay — `Sigma`/`El^δ` is 6.2 k / 6.6 s and the
  closed non-dependent payers (`InstructionBytes`, `Region`,
  `ConditionalJoinRegion`, `LinkedConditionalBlock`) are its shape — but it is
  a different boundary with a different argument (a closed receiver's type is
  `El (D#tycode^δ)` while the closed device's domain is the inline `⟦D⟧`), and
  this round's bar is §10's row. Its own slice.
- **A definition per instantiation.** §2.3, verbatim.
- **Teaching the kernel's `Fst`/`Snd` rule to see through a code reference.**
  §9's last bullet's rejection, plus §8's: no kernel change.

### 13.7 Verification items

1. **Registration on the real library.** `MachineState<M>`, `StackAccess<M>`
   and `And<P, Q>` — the three non-dependent payers — all get `#proj₀`;
   `CollectionLiteral<A>(n)` declines, and §13.3 says why. A decline among
   the first three means §13.3's boundary is not the one the payers sit on.
   **Run it as a listing of what registered and what declined, with the
   reason**: the fix pass found that a silent decline had sent three closed
   records back to the exponential walk and looked, from outside, exactly
   like a device that had fired (§13.10).
2. **Spelled alike, or not at all** (§12 item 2 at this layer). No head-pair
   count may *rise*; in particular `Sigma`/`El^δ` must not grow, which is what
   a parametric receiver falling back to the closed device's shape would look
   like.
3. **The walker's residue does not grow** past §10's 260, and no new slot
   appears.
4. **The bar.** `Sigma`/`El(?)` back to ≤ 1,050 (its before count) and the
   whole run's item and kernel totals at or below the `bc07438` column.

### 13.8 Amended during implementation (2026-09-10): the definitions' own components

One correction, forced by the walker. The definitions are built off
`lower_instance`'s components, which are **inline**, and every use site reads
its `App.dom`/`App.cod` annotations back out of those statements — so a
monomorphized component in a definition is a monomorphized annotation at every
field read. The emission walker's residue rose 578 → 260 → **328** before this
was seen. `register_rec_projs` now puts `fst` and `snd` through `emit_ty`
before they enter a statement, exactly as `project_field`'s fallback walk
already respells the components its own `Fst`/`Snd` nodes carry, and keeps the
un-respelled tail for the structural walk (`cur`) — the same split as the use
site's. Residue back to 260, and the run's item total fell a further 9.4 s: the
line is worth more than the walker finding that found it.

### 13.9 Measurement — three columns, one box

Same box, release, `-p heather-cli --features value-metrics`, one invocation:
`heather build-x86 examples/x86-native/mix.hthr mix --arg 0x14 --arg 0b10110
-o … --item-timings …`. Seconds are same-box; counts are the datum. **Re-taken
by the fix pass on the green tree** (both columns on one box, the before one
from a `bc07438` worktree built beside it); the middle column is the
type-codes-only tree's, kept from the earlier box for its counts.

| | before (`bc07438`) | type-codes only (§10) | with projections (green tree) |
| --- | --- | --- | --- |
| whole run | wall 167.1 s, RSS 500 MB, 943 rows, **34.07 s item / 26.15 s kernel** | 44.05 s / 37.61 s | wall 117.9 s, RSS 366 MB, 943 rows, **18.25 s item / 12.36 s kernel** |
| `mix_native_loaded_byte_*` | 10 items, 7.92 s / 6.86 s kernel | 10 items, 4.36 s / 3.54 s | 10 items, **3.94 s / 3.18 s** |
| `Sigma`/`El(?)` — §10's regression | **1,050 / 8.02 s** | **15,998 / 65.74 s** | **2,651 / 8.03 s** |
| `Sigma`/`Sigma` | 19,301 / 10.38 s | 6,013 / 5.45 s | 5,971 / 4.66 s |
| `El⌜⌝`/`Sigma` | 16,712 / 10.24 s | gone | gone |
| `Wf`/`Wf` | 8,748 / 6.47 s | gone | gone |
| `Sigma`/`El^δ` (the closed row, §13.6) | 6,205 / 6.13 s | 6,212 / 6.61 s | 6,247 / 5.82 s |
| `El(?)`/`Sigma` | not in the top 16 | 8,080 / 3.97 s | 8,170 / 3.62 s |
| `Vec`/`Sigma` | 79,600 / 4.57 s | 79,982 / 4.92 s | 79,982 / 4.55 s |
| `El^δ`/`Sigma` | 81,007 / 1.99 s | 82,433 / 3.05 s | 82,437 / 1.99 s |
| emission-walk findings (`scripts/measure-x86-conv-miss`) | 578 | 260 | **260**, same slots |

**The bar is met and the boundary that was paid for it is recorded rather
than papered over.**

- The whole-run bar — item and kernel totals at or below the `bc07438`
  column — is met by a wide margin: **34.07 → 18.25 s item, 26.15 → 12.36 s
  kernel**, 46 % and 53 % below the before column and well below the tree §10
  measured. RSS falls 500 → 366 MB.
- The **`Sigma`/`El(?)` row is back to its before *time*** (8.03 s against
  8.02 s) at 2.5× its before count — 15,998 → 2,651 — where §13's first
  implementation left it at 5,370 / 26.45 s. What remains is the closed
  non-dependent records §13.6 deliberately left out, the dependent
  telescoped ones the gate now declines, and every field read whose receiver
  is not a local.
- The walker's residue is **260 with no new slot** (§13.7 item 3), the same
  slots the type-codes-only column listed.
- §13.7 item 2's "no head-pair count rises" holds for every row above except
  two that move by tenths of a percent — `Sigma`/`El^δ` 6,212 → 6,247 and
  `El(?)`/`Sigma` 8,080 → 8,170 — both cheaper in seconds than the column
  they rose against, and both the closed device's own rows.

**The boundaries, with what each leaves unnamed.** Three, and each was
measured into place by the fix pass rather than argued:

1. **A dependent telescoped spine keeps the inline walk** (§13.3, §13.6).
   `CollectionLiteral<A>(n)` (166 reads) and `Monoid<A>` are the
   measured ones. Its definitions would have to write the tail out.
2. **A field read whose receiver is not a local keeps the inline walk**
   (§13.6). What that costs is not separated from boundary 1 in the counts
   above; `stack_word_agrees` and `stack_word_matches` remain the two
   `Sigma`/`El(?)` payers.

   **Amended (2026-09-13), [[x86-scaling-rail-out-of-fuel]]: and neither does
   a read off the *bare binder*.** This boundary was one-sided and therefore
   not stable under substitution: a reference minted at a local is a reference
   over a **computed** receiver the moment the local is instantiated, which is
   the side this boundary declines — so a record's field type and every
   statement written against the same computed state spelled one read two
   ways, the shortcut could not fire, and the kernel converted by evaluation.
   That is the 20-node x86 rail's `OutOfFuel`, refused since this round
   landed. The gate is now `receiver_admits_reference`: neutral **and not a
   bare `Var`**. A chain (`Sndᵏ v`, an applied local) is §13.1's measured
   payer and keeps the reference; a bare binder's read is one `Fst`/`Snd`
   node, which is what the walk costs anyway. The two alternatives — minting
   at every receiver, and minting at one layer of computation — were both
   hand-run on the 2026-09-13 tree and both re-broke
   `caller_native_memory_same_27/28`, so §13.6's rejection of the first has
   *not* expired. `docs/archive/x86-scaling-rail-out-of-fuel-design.md` carries the
   attribution, the table and the argument.
3. **The closed non-dependent records** (`InstructionBytes`, `Region`,
   `ConditionalJoinRegion`, `LinkedConditionalBlock`) are §13.6's own
   deliberate omission, unchanged.

An issue can own all three; none of them is a defect in this slice.

### 13.10 Status (2026-09-10, fix pass): green

The suite is green and the three targets §13.10 recorded are fixed. What
fixed them, because two of the three were not what the evidence had been read
to say:

- **`record_projection_size` and `repr_access` (SIGABRT).** Not the
  telescoped registration at all: `saturate`'s arity check compared
  `pi_arity(stmt)` with the spine it was handed, and a projection whose field
  type is itself an arrow has more `Π`s than arguments. **Every
  function-typed field declined**, closed records included, which sent `Rp`,
  `Repr_ListTok` and `Impl_ListTok_length` back to `project_field`'s
  exponential walk — `issues/theorem-field-projection-oom.md`'s blow-up, on
  the allocator. The check is now `<`; the loop's own non-`Π` refusal is the
  guard that was meant. Both targets green under *either* telescoped
  boundary, which is what retired the inverted gate drafted for them.
- **`native_summary` (`OutOfFuel`).** Real, and a shape this design had not
  considered: a projection *reference* is cheap to **compare** and dear to
  **compute through**. `reused_callee`'s certificate chains twenty-eight
  machine states through `state.memory`, and with the reference
  `caller_native_memory_same_28` needs between 8× and 64× `DEFAULT_FUEL`
  (measured by multiplying the elaborator's budget; 488 exhausted evaluator
  budgets at 8×, none at 64×) where the inline `fst(sndʲ v)` checks inside
  the default. The fix is §13.6's use-site boundary — the reference is
  minted only where the receiver bottoms out in a **local**, which is the
  shape §13.1 attributes the misses to (`Var < Sndᵏ < Fst < …`) — and it is
  a spelling boundary, not more fuel. The closed device is exempt: there the
  definitions exist to remove the walk's exponent, and a literal receiver is
  exactly the case that needs them.

Two lessons worth keeping. A decline is silent, so a device that declines
where it was measured to fire looks exactly like a device that fired and
lost — §13.7 item 1 should have been run as a *listing*, not an assertion on
four names. And the round's whole argument was about conversion **misses**;
nothing in it asked what a reference costs the evaluator, which is the
question the certificates ask.
