# Exporting Heather to Lean and Rocq: the shared fragment

Status: **exploration**, 2026-10-20, with a prototype (`crates/export`) and
probe files that were run against Lean 4.20.0 and Coq 8.18.0. Owner issue:
`issues/heather-proof-export.md` (the `export-fragment` milestone in
`docs/roadmap.md`). Follow-up rounds are the issues listed in §10.

The question: how should checked Heather declarations be translated into Lean
and Rocq so that each target rechecks them? We want one translation general
enough to serve both, and a translation simple enough that "if it is exported
then it checks, relative to our model of Lean" could later be a theorem. This
document answers with a design, a former-by-former account of what each target
can carry, and the evidence for each claim.

---

## 0. The answer in brief

1. **Export from kernel declarations (Ψ), never from surface syntax.** The
   kernel term is what Heather checked, and it is far smaller than the
   surface: one fully annotated calculus with a few dozen formers, and no
   elaborator behaviour to reproduce.
2. **Use one intermediate language and two printers.** The intermediate
   language, **HX** (§4), is a pure type system with constants: sorts, Π, λ,
   application, variables, numerals, and one *prelude constant* per kernel
   former (`Hx.pair`, `Hx.J`, `Hx.transp`, …) applied to all of that
   former's annotations. A printer per target is mechanical. The only trusted
   text per target is a hand-written prelude of about a hundred lines, which
   implements each constant with the target's own inductives and records
   (`crates/export/prelude/Hx.lean`, `Hx.v`).
3. **The common fragment is the layer-free, Wf-free kernel.** It covers Nat,
   Id, Σ, Unit, Empty, sums, W, Vec and Fin, strict equality (`sEq`),
   squash, codes (`El` disappears under Russell universes), and global
   definitions, at closed universe levels. Heather's definitional rules on it
   are all present in Lean. Rocq has all of them except **unit η** and **η
   for a record whose only field is irrelevant**, and Heather's tier-0 enums
   lean on both (§3, §5.3).
4. **`Wf` is the hard former in both targets, for opposite reasons** (§5.1).
   Rocq can declare it exactly, with its positivity and guard checks
   bypassed, but then misses the unit η that `Wf`'s whole point depends on.
   Lean cannot declare it at all. What Lean can do instead is realise each
   lowered inductive as a native Lean inductive. That realisation is exact
   except for β at an *open* tag, which the elaborator's generated code does
   not seem to use.
5. **Recommendation: Lean is the first target.** Lean has unit η, Σ η, the
   K-like reduction that is Heather's strip rule, proof irrelevance, GMP
   numerals and algebraic universe levels. Minus's other projects are in Lean,
   and an exported `List` that is a real Lean inductive can be used from Lean.
   Rocq stays a second printer over the same HX, for the fragment it can
   carry. Its draw is the proof side: heather-coq and MetaCoq are both in Coq
   (§8).
6. **The prototype works on a first slice.** Over the elaborated prelude plus
   `Nat::add`, three addition lemmas, an enum with `not` and `not_not`, and a
   proof by `refl` at a 22-digit literal, the export refuses nothing. **Lean
   checks all 22 declarations. Coq checks 20**, and stops at `not_not` (unit
   and irrelevant-record η) and at the 22-digit literal (unary `nat`). That
   is exactly where §3 predicts.

## 1. What export proves, and what it trusts

An exported declaration that the target checks shows that the target's kernel
accepts the translated proof of the translated statement. Three things stand
between that and "Heather's theorem is true":

- **The statement translation** is trusted. If ⟦·⟧ mistranslates a
  statement, the target checks a different theorem. This is the same hazard
  class as the inductive lowerings (`docs/inductive-tier0-lowering.md`: a bug
  "produces a checked theorem about a type the user did not write"). So
  statements must translate by a translation simple enough to review, and
  §8's theorem is what eventually removes the trust.
- **The proof translation** is *not* trusted. A wrong proof translation
  produces a term the target rejects, which is a failed export, never a false
  theorem. This is why the printers may lean on the target's elaborator for
  now (§5.6). It is also why the exporter, like the elaborator, is untrusted
  plumbing. It can be clever, but it must not be needed for soundness.
- **The prelude** is trusted per target: one constant per former, at the
  kernel's argument order. It is small and it is not generated.

Axioms carry over as axioms. The library has none today
(`docs/axiom-provenance-design.md`; `rg '^axiom' lib` is empty). Theorems
whose proofs Ψ did not keep also export as axioms for now, and the target's
own report lists them: Lean's `#print axioms g15` (`Nat::add_assoc`) names
`g10`, which is the prelude's `Nat::cong_succ`, exported as an axiom
(`issues/export-keeps-proofs.md`).

## 2. The source: what a kernel declaration looks like

From the elaborated Ψ (`crates/export/tests/nat_fragment.rs`):

- Every declaration is a `GlobalBinding::Tm` at `Layer::Code` with an empty
  Δ, so its type and body are closed kernel terms over earlier globals. Type
  parameters are ordinary Π-binders over `Ty 0` used through `El`
  (`docs/surface-polymorphism.md` §2). Inductive types are bodied
  type-code definitions: `B` is `u1 + u0` over two payload codes
  `Σ(sEq(Nat; k; k)). Unit`.
- **No universe polymorphism.** `UPi`/`ULam`/`UApp` are layer m, and no
  declaration uses them, so every level is closed. The exporter normalises
  each level to a number (§5.5).
- **No modal structure.** `box`, `letbox`, the code recursors and the
  context and type meta-functions appear only in `meta fn`s and the certgen
  machinery. Those are not candidates for export: their meaning *is* the
  code layer.
- **Theorems keep no proof** unless their statement carries data
  (`crates/elab/src/lib.rs:4150`, `sealing::carries_data`). A `fn` keeps its
  body, so the prototype writes its lemmas as `fn`s.
- **Checked spellings** (`pair@`, `inl@`, `inr@`, `fst@`, `snd@`, `app@`;
  `docs/intro-by-type-design.md`) omit components that the type they were
  checked at determines. They are common: every enum constructor value is an
  `inr@(pair@(srefl, ⟨⟩))`.

## 3. Former by former

Each row says what Heather's kernel does definitionally and how the target
carries it. "Probe" names the file in `crates/export/probes/` that checks the
claim. Every probe in that column was run against the stated versions.

| Former | Heather rule | Lean 4 | Rocq / Coq | Probe |
|---|---|---|---|---|
| `Ty l`, `El`, codes | Tarski, non-cumulative, one level per type | `Type l`, Russell: `El c ↦ ⟦c⟧` | `Type@{u_l}`, Russell | prototype |
| `Π`, `λ`, app | β, η | native | native | prototype |
| `Nat`, `elim_Nat`, literals | ι; literals of any size | builtin `Nat`, `Nat.rec`; GMP literals | unary `nat`: a large literal is a large term | prototype (`big`) |
| `Id`, `refl`, `J` | Paulin-Mohring J, **no K** | Type-valued inductive | Type-valued inductive | `Definitional.lean` |
| `sEq`, `srefl`, `transp` | irrelevance; **strip**: `transp` at convertible endpoints is its payload, even at a neutral proof | structure over `Eq`; the strip is `Eq.rec`'s K-like reduction ✓; irrelevance only **eta-long** (§5.2) | record over an SProp `sEq` with `Definitional UIP`; strip ✓; irrelevance only eta-long | both `Definitional.*` |
| `sEmpty`, `Squash` | irrelevant | structure over `False` / `Nonempty` | record over SProp; `elimSquash` stated eta-long | prelude |
| `Σ`, `pair`, `fst`, `snd` | projections with η | structure; η against a constructor | primitive record; η against a constructor | both |
| `Unit^l`, `⟨⟩` | η: any two terms convert | unit-like structure, η between neutrals ✓ | **no unit η**, and a record without a relevant field cannot be primitive ✗ | `Definitional.v` |
| `Empty^l`, `elim_Empty` | no β | inductive | inductive | prelude |
| `+`, `inl`, `inr`, `case` | positive, ι | inductive | inductive | prelude |
| `W`, `sup`, `elim_W` | ι with a synthesized ih λ | inductive (`W.rec` has exactly that ι) | inductive + `fix` | prelude |
| `Vec`, `Fin` | computed by `Nat` recursion; neutral at a neutral length | `Nat.rec` into `Type` | `Fixpoint` into `Type` | prototype |
| `Wf`, `sup_f`, `elim_Wf` | finitary fixed point; children a `Vec`; ι at any tag | **not declarable** (positivity) | declarable with `bypass_check(positivity, guard)` | `WfPositivity.lean`, `WfBypass.v` |
| `DVec`, `IWf` | as `Vec`/`Wf`, indexed | as `Wf` | as `Wf` | not probed (no code yet; layer p/m only) |
| global definitions | δ, lazy | `def` (`@[reducible]` for the elaborator) | `Definition` | prototype |
| sealed theorem proofs | unfold at a stuck elimination | `def`/`theorem`: Lean's kernel may unfold either | must be `Defined`, never `Qed` | design |
| `box`, `letbox`, code recursors, `CtxPi`, `TyPi`, `GlobalTy` | the modal layers | refused | refused | prototype |
| `ΠΠ`, `Λ`, `$` | first-class level quantification | prenex only (constants' level params) | prenex only | design |

Two corrections to the roadmap's framing follow from the table. First, "no K"
holds for `Id`, but `sEq` has definitional UIP and the strip rule, which is K
behaviour. Both targets supply it, Lean natively for `Eq` and Rocq behind the
`Definitional UIP` flag. Second, "a layer-free proof asks less of its target"
is true for the logic but not for conversion. Heather's η for `Unit`, `Σ` and
irrelevant types is *more* than Rocq's kernel decides, and its `Wf` is more
than either target's positivity checker admits.

## 4. HX: the intermediate language

```
t ::= x                     de Bruijn variable
    | Type ℓ                ℓ a closed level (a number) today
    | Π(x : t). t  |  λ(x : t). t  |  t t
    | c.{ℓ⃗}                 prelude constant at explicit levels
    | g                     an exported declaration
    | n                     natural-number literal
    | _                     a component the kernel term does not spell
```

A declaration is `g : T := t`, or `g : T` for an assumption. Every kernel
former maps to a prelude constant applied to its annotations, in the kernel's
own field order, with the former's binders turned into λs
(`crates/export/src/lib.rs`, `Tr::tm`). For example:

```
elim_Nat^l(z. M; b; k ih. s; n)  ↦  Hx.elimNat.{l} (λz. ⟦M⟧) ⟦b⟧ (λk. λih. ⟦s⟧) ⟦n⟧
transp^{l,l'}(I; x.P; a; b; e; t) ↦ Hx.transp.{l,l'} ⟦I⟧ (λx. ⟦P⟧) ⟦a⟧ ⟦b⟧ ⟦e⟧ ⟦t⟧
El(c) ↦ ⟦c⟧      TmPi(s; x. t) ↦ Π(x : ⟦s⟧). ⟦t⟧      Ty l ↦ Type l
```

Why this shape:

- **The printers carry no logic.** They spell binders, applications and
  universe instances, so a third target (Agda, Dedukti, a model of Lean
  written in Heather) costs one printer and one prelude.
- **HX's conversion is the target's**, restricted to what the prelude
  defines: β, δ, ι for each prelude inductive, Π η, η against a constructor
  for the records, irrelevance for the `Prop`/`SProp` fields, and the K-like
  reduction of the prelude's strict equality. Unit η is in Lean's HX, not
  Rocq's. This small, explicit relation is what §8's theorem would be stated
  against.
- **It is λΠ-modulo in all but name**, the shape Dedukti and Logipedia use
  for proof interchange, and close to the Lean kernel's export format. Either
  would be a natural serialised form later (§10).

Holes (`_`) are the one escape. They come only from checked spellings, and the
target's elaborator fills them from the expected or inferred type. §5.6 says
how a typed exporter removes them.

## 5. The hard parts

### 5.1 `Wf` (and later `IWf`)

`Wf^l(x:S). n` stores its children in `Vec(Wf; n[a/x])`, which is a `Σ`-tuple
computed from the arity. That is the whole point of the former
(`crates/kernel/DESIGN.md`): `sup_f(tag; cs)` at a neutral `cs` *converts* with
the concrete `node(nth cs 0, nth cs 1)`, through Σ η and unit η, where `W`
would need funext. Every tier-1 inductive lowers through it, `List<A>`
included (`docs/inductive-tier1-wf-lowering.md`).

**Rocq: exact declaration, missing η.** With `#[bypass_check(positivity)]`
on the inductive and `#[bypass_check(guard)]` on its eliminator, `Wf` and
`elim_Wf` are the kernel's rules verbatim. β at an *open* tag holds, and
`Print Assumptions` lists exactly the two bypasses (`WfBypass.v`). The bypass
is semantically sound: `Vec(X; k)` is a finite product of `X`, so the type is
strictly positive, and only the syntactic checker cannot see it. That makes a
small meta-theorem §8 could carry. However, the property `Wf` exists for fails
in Rocq. Comparing `cs` with `pair(nth cs 0, pair(nth cs 1, tt))` ends in
`snd (snd cs) ≡ tt`, which is unit η. It passes only when the exporter writes
`cs` eta-long, and §5.3 shows that eta-long cannot reach the neutrals that
reduction creates.

**Lean: no declaration, but a per-declaration realisation.** Lean's kernel
rejects `Wf` outright (`WfPositivity.lean`) and has no bypass for checked
declarations. Two generic encodings fail. As a `W`-type with `Fin`-indexed
children, `elim_Wf` cannot even be typed, because `nth (tabulate f)` is not
`f`. As a nested inductive over an indexed vector, `toH (ofH h) ≢ h` at a
neutral `h`. What works is to realise each lowered inductive as a native Lean
inductive, with one constructor per summand of the shape, carrying the
summand's payload and its children as fields. Then:

- `⟦Wf(S; n)⟧ := D` (the native type, over the declaration's parameters);
- `⟦sup_f(a; cs)⟧ := case a of k ↦ D.c_k payload (fst cs) … ` (stuck at an
  open tag);
- `⟦elim_Wf(M; step; t)⟧ := D.rec`, one minor premise per constructor,
  calling `step` at the canonical tag with the children re-tupled and the ih
  as a case over the index.

`WfNative.lean` checks this for `List<A>`. The `Wf` property holds (1), and β
at a canonical tag holds (2). β at an **open** tag fails (3), and so would a
comparison of two ihs at an open index. Heather's own notes say the generated
code never does either. The step cases on the tag before touching `cs`, and
the ih is "applied at literal indices … never stored and never compared"
(`crates/kernel/DESIGN.md`, the `Wf` paragraph). So the conjecture is that the
realisation is exact on every term the elaborator generates. The library
sweep (`issues/export-library-sweep.md`) tests that, and the fragment's
definition (§6) states it as a side condition until then. Which `Wf`
instance is which declaration should come from the elaborator's inductive
table, not from matching spellings (`issues/export-wf-native-inductives.md`).
A side benefit: an exported `List` is then a real Lean inductive, which is
what makes exported results *usable* from Lean, and not only checked there.

**As implemented (2026-10-21, `crates/export/src/wf.rs`).** The exporter
meets a tier-1 declaration as its whole-type code (`D#tycode`, or
`D#tycode_fn` over its type parameters) and emits there the inductive `D`,
its constructors named from the elaborator's table, and `D::supf#`. Before
the first declaration that eliminates at motive level `l'` it emits
`D::elim#l'`, which is `D.rec` with one minor premise per constructor. The
premise calls the step at the canonical tag, passes the children re-tupled,
and passes the ih as a case over the `Fin` index. The step's binder types
are the kernel's own telescope (`wf_step_telescope`, its `nth` included), so
the two sides of every comparison are spelled alike.

An instance is recognised by the **nominal tag** its first payload carries
(`sEq(Nat; t; t)`), which identifies the declaration however the shape is
spelled. Its type arguments come from walking the instance's payload types
beside the declaration's own, after evaluation: where the declaration has
`El(A_i)`, the instance has `A_i`'s argument. The walk compares nothing,
because Lean does: a wrong argument is a rejected declaration.

The conjecture holds on the sweep. Lean's kernel accepts every exported
`List` lemma, so nothing in the closure uses β at an open tag. The negative
control in `crates/export/tests/library_sweep.rs` builds a declaration that
does use it, `elim_Wf(_. Nat; _ _ _. 0; sup_f(a; cs)) = 0` at an open `a`.
Heather's kernel accepts it, Lean rejects it, and `scripts/export-recheck`
fails unless that declaration is exactly the one Lean rejects. Not covered
yet: indexed families (`IWf`, refused by name) and declarations whose arity
depends on the payload (refused by name).

### 5.2 Irrelevance needs eta-long terms

Heather's `sEq`, `sEmpty` and `Squash` are irrelevant: any two terms convert.
Neither target can say that of a *type in a universe* `Type l`. Lean's proof
irrelevance is for `Prop`, Rocq's for `SProp`, and a code `TmSEq : Ty l` must
decode to something in `Type l`, because `El` is the identity under Russell
universes. So the prelude wraps the proposition in a one-field structure
(`Hx.SEq.pf : a = b`). Lean's structure η fires only when one side is a
constructor, so `⟨p.pf⟩ ≡ ⟨q.pf⟩` holds but `p ≡ q` does not
(`Definitional.lean`). Rocq is the same, and its wrapper cannot even be a
primitive record. The fix is a translation invariant: **write every term at a
type whose whnf is `sEq`, `sEmpty` or `Squash` eta-long**, as the constructor
applied to the projected proof, and do the same through `Σ`s whose
components need it. The strip rule needs no help. It is `Eq.rec`'s K-like
reduction in Lean and the special reduction of an SProp equality under
Definitional UIP in Rocq, and both fire at a neutral proof (both
`Definitional.*`).

**What the prototype does (2026-10-21).** A *closed singleton* is a closed
type whose whnf is `Unit`, an `sEq` between whnf-equal endpoints, or a
non-dependent `Σ` of singletons; Heather's η makes any two of its terms
convertible, neutrals included. Wherever the exporter can read a term's type
without inference (a binder's domain, a global's statement, an application's
codomain, a projection's component, an intro's own annotation) and that type
is a closed singleton, it prints the type's **canonical element** (`tt`,
`srefl`, or a pair of them) instead of the term. Two canonical elements are
syntactically equal, and a neutral the exporter could not type meets one
through structure η, which fires against a constructor. The *types* are
printed as written. An earlier version collapsed singleton types themselves
to `Hx.Unit`, so that Lean's unit η would cover neutrals; that disagreed with
the δ-unfolding of an open definition that reaches the same type only by
substitution (`Or<Unit, Not<Unit>>`'s `inl` in `bool::True::Decide`), and
Lean rejected it.

The invariant is what the typed exporter maintains (§5.6), and it has a known
gap. A neutral whose type becomes irrelevant only after a substitution (a
`f n : Vec(sEq…; n)` at `n := 1`) is not expanded. The target then rejects a
conversion Heather accepts. That is a failed export, never a wrong theorem.

### 5.3 Unit η in Rocq

Lean has unit η natively. In Rocq, `Unit` cannot be a primitive record (no
relevant field), and an SProp field does not count. Eta-long translation
covers the `⟨⟩`-typed terms that are written in the source, but not those that
reduction creates. The prelude's own `case` hands its branch the type
`M (inl x)` at the *bound* `x`, which no translation of the branch can
expand. That was the prototype's `B::not_not` failure: `not(not(inl x)) ⇝
inl(pair(srefl, ⟨⟩))` must convert with `inl x` for a neutral payload `x`.
Every tier-0 enum's case analysis has this shape.

The routes, as weighed on 2026-10-21:

- **Wait for unit η in Rocq, or patch it.** Neither is on offer.
- **Put `Unit` and `sEq` in SProp**, where irrelevance is definitional η.
  That needs sort polymorphism (Rocq ≥ 8.19) for `Σ` over a mix, and breaks
  where Heather needs `Unit` relevant: `Vec A 0` is a `Fixpoint` into one
  sort.
- **Native enums with no payload.** They work, but make `B` a different
  type from the `Sum` it unfolds to.
- **Conversion certificates** (the ETT-to-ITT direction): the exporter
  replays Heather's conversions and inserts rewrites. This is far heavier than
  anything else here.
- **Singleton-aware `case` (taken).** When a summand's payload is a closed
  singleton, the exporter emits `caseL`/`caseR`/`caseLR` instead of `case`.
  The branch is stated at the canonical element `c` (`M (inl c)`, under no
  binder). The prelude reaches it by `J` along an η *lemma* `∀x. c = x`
  (`etaUnit`, `etaSEq`, `etaSig`), which Rocq proves by `destruct`. That
  reduces whenever the payload is a constructor, and the exporter already
  prints a payload of a closed singleton type as its canonical element (§5.2).
  Lean's lemmas are `refl` by its own η, so there the case also computes at
  a neutral payload. The same rule removes singleton payload fields from
  realised `Wf` constructors (§5.1): a bound payload would meet the same wall
  in the recursor's minor premises.

Two neighbours needed the same treatment in the library sweep:

- A term at a squash type prints eta-long (`squashEta`). Rocq's `Squash` is a
  record over an SProp field, so it has no η, but two eta-long terms convert
  by irrelevance.
- A binder domain that becomes a closed singleton only once an enclosing
  payload is its canonical element (`IsTrue(inr x)` in a branch) is closed
  over those canonical elements before the singleton test.

What is left is the honest core: a theorem whose statement *is* unit η.
`Bool::is_true_unique` proves `p = q` at `IsTrue(True)` by `refl`. Rocq
needs a propositional proof there, which the η lemmas give
(`trans(sym(eta p), eta q)`), but the exporter can only write it if it knows
the endpoints the `refl` is checked against. That is the typed exporter of
§5.6, so the sweep stays informational in Rocq until it exists.

### 5.4 Numerals and acceleration

Lean's `Nat` literals are GMP numbers, and `Nat.rec` on a literal peels one
`succ` lazily, so the prototype's `add(10^21, 1) = 10^21 + 1` checks
instantly. Rocq's `nat` is unary: the same declaration ran past a 120-second
limit, and the recheck script runs Rocq under a CPU and address-space rail
for this reason. More generally, Heather's run-accelerated folds and native
bitvector values are *representation and strategy* changes with no semantic
content (`crates/kernel/DESIGN.md`, acceleration policy). That is exactly why
export soundness ignores them, and exactly why their speed does not come
along. A Heather proof by evaluation that leans on them (an x86 certificate, a
`ten_pow` at a large exponent) is in the fragment logically but may be out of
reach for the target's checker in cost. The first fragment therefore excludes
the native certificates. Mapping Heather's `Nat::add` to Lean's accelerated
`Nat.add` would change δ-behaviour at open arguments, so it is not a free
optimisation. Rocq's binary `N` is no way out either: Heather's `elimNat`
computes on `succ n` for a symbolic `n`, and `N.peano_rect` does not. So
the Rocq printer refuses a declaration spelling a numeral of more than five
digits, and what mentions it (`65536` appears in every collection literal's
tag and checks; `10^21` does not finish).

### 5.5 Universes

Heather's levels are closed in every exported declaration. Lean takes them
as numbers (`Type 2`, `Hx.pair.{0, 1}`), and algebraic levels in instances
are fine there. Coq 8.18 refuses algebraic universe instances
(`Sig@{max(a,b) b}` is a syntax error). Closed levels avoid the question,
because the Rocq prelude declares a chain of global universes `Set < u1 <
u2 < …` and level `k` prints as `Hx.u_k`. Rocq's cumulativity is harmless:
it can only accept more. When declarations become level-polymorphic (layer m
today), only **prenex** `ΠΠ` maps to either target, as a constant's level
parameters. A `ΠΠ` under a binder, or a `Λ` passed as an argument, needs
`Setω`-style quantification that neither has. Each Heather type's level is
`l` and its Lean sort is `Type l`. Nothing exported lands in `Prop`, which
keeps Lean's impredicativity out of the translation entirely.

### 5.6 Checked spellings and the typed exporter

The prototype prints a checked spelling as the prelude constant with holes
for its components (`@Hx.pair _ _ a b`), plus an ascription when the kernel
term carries its checked type. The target elaborator fills the holes, and the
kernel then checks the result. That is sound, because the holes are in proof
terms and statements are fully spelled. It is fragile, though: in
`WfNative.lean` Lean's elaborator needed `with_unfolding_all` to see a
conversion its kernel accepts. The intended exporter is **typed**. It walks
each declaration with the kernel's own inference, recovers each checked
spelling's components from the whnf the derivation contains (the `⌊·⌋`
translation of `docs/intro-by-type-design.md` §2.4), and in the same pass
writes eta-long terms at irrelevant types (§5.2). Its output has no holes, so
it can go to the target's kernel directly: Lean through `addDecl` from a small
import program, bypassing the elaborator, or through the kernel export
format.

Half of that landed on 2026-10-21 without a new walker: the exporter erases
checked spellings by calling the kernel's own `⌊·⌋`
(`typing::spell_checked_in_code`, `spell_checked_in_code_ty`) on each
statement and body before translating. A body whose spelling fails falls
back to the hole-printing route. Two in the sweep did, both
`NotConvertible`, and the cause was in `⌊·⌋` itself: its record of what
each checked spelling was viewed at is keyed by the node's address, and
both bodies share one `@` node between a `case` motive and a branch
annotation, where the scrutinee is a variable in one and a constructor in
the other. The second view overwrote the first. The record now marks such a
node ambiguous and the rebuild gives each occurrence its own copy, which
the next pass records apart (`crates/kernel/tests/typing.rs`,
`spelling_a_shared_node_viewed_at_two_formers`). No body in the sweep keeps
a hole since. The fix also reaches the elaborator's own uses of `⌊·⌋` at
the quote boundary, where the same sharing would have refused a payload.

Heather's terms are DAGs, and printing them as trees is exponential in the
worst case. That is the reason the checked spellings exist. Lean's export
format is hash-consed and keeps the sharing, and so does the kernel route's
node table. The text route gets it back by hoisting
(`crates/export/src/share.rs`): every subterm of some size that occurs twice
becomes a reducible definition, abstracted over the variables it uses and
those their types need, keyed by its closed body, and declared just before
its first user. The definitions are δ-equal to what they replace and Lean
checks them, so hoisting adds nothing to trust. Abstracting over the whole
context prefix instead was tried first: the binder prefixes were nine
tenths of the text. Rocq would take the same hoisting, or `let`s, or a
MetaCoq quotation.

### 5.7 Opacity

Heather unseals a theorem's proof at a stuck elimination
(`issues/theorem-witness-unfolding.md`). A target must be able to unfold
whatever Heather unfolded. Lean's kernel can unfold a `theorem`'s value as it
does a `def`'s (worth re-checking per Lean version; the prototype prints
`def` regardless). Rocq never unfolds `Qed`, so data-carrying
theorems print as `Defined`, and the prototype prints everything as a
transparent definition. Extra transparency can only make a conversion
cheaper or costlier, never wrong.

## 6. The fragment, stated

- **F (common):** declarations whose types and proofs are closed kernel
  terms over Nat, Id, Σ, Unit, Empty, sums, W, Vec, Fin, sEq, sEmpty, Squash,
  codes and global definitions, at closed levels, with no modal former, no
  `ΠΠ`/`Λ`/`$`, and no `DVec`/`IWf`; `Wf` only in Lean (below). The exporter refuses everything
  else by name (`Refusal` in `crates/export/src/lib.rs`), and a declaration
  that mentions a refused one is itself refused.
- **F_Lean = F + Wf**, through per-declaration native inductives, under the
  side condition of §5.1 (no β at an open tag, no ih compared at an open
  index). The side condition is checked by Lean itself: a violation is a
  rejected export.
- **F_Rocq = F minus what needs unit η or irrelevant-record η after reduction,
  minus large literals; + Wf through the two bypasses.** In practice that is
  the Nat-and-Id part, not the enum part.

The refusal list *is* the milestone's step 3, the list of kernel features
that stopped the translation:

1. modal formers (box, letbox, code recursors, context/type meta-functions,
   global type variables);
2. non-prenex level polymorphism;
3. `Wf`/`IWf` in Lean beyond the side condition; unit and irrelevant-record
   η in Rocq;
4. irrelevance that only appears after a substitution (§5.2's gap);
5. cost: accelerated evaluation (§5.4).

## 7. The prototype

`crates/export` translates Ψ to HX and prints Lean and Rocq. `scripts/export-recheck`
runs its acceptance test with `HEATHER_EXPORT_OUT` set, copies the preludes
beside the output, and hands both files to `lean` and `coqc` (from `LEAN` /
`COQC` or `PATH`) under CPU and memory rails. On 2026-10-20, over the prelude
and the test's source (`crates/export/tests/nat_fragment.rs`), it gave:

| | declarations | result |
|---|---|---|
| export | 22, of which 4 are prelude theorems without kept proofs (axioms) | no refusal |
| Lean 4.20.0 | 22 | all check; `#print axioms` on `not_not` and the literal proof: none |
| Coq 8.18.0 | 20 of 22 | stops at `B::not_not` (§5.3); the literal proof does not finish (§5.4) |

On 2026-10-21 the exporter gained kept proofs, qualified names, spelling
erasure, canonical elements (§5.2) and the **kernel route**:
`print_kernel` writes a hash-consed node table (`.hxk`, one line per
distinct subterm), and `prelude/Import.lean` rebuilds each declaration as a
Lean `Expr` and hands it to `addDecl`. No parser and no elaborator sees an
exported term. The library sweep (`crates/export/tests/library_sweep.rs`,
the closure of `lib/std/list.hthr`) gave:

| | declarations | result |
|---|---|---|
| export | 387 bindings | 293 exported; 90 refused for `Wf`, 4 for mentioning a refused one |
| slice, Lean kernel route | 22 | all accepted, no axioms; a corrupted literal is rejected |
| sweep, Lean kernel route | 292 | all accepted in about two seconds; `bool::is_true_dec_yes` skipped (its body keeps a hole, §5.6) |
| sweep, Lean source text | 293 | all accepted, but parsing takes nearly the whole run: minutes, against a fraction of a second of type checking |

Later the same day, with `Wf` realised as native inductives (§5.1) and a
binary tree added to the slice:

| | declarations | result |
|---|---|---|
| export | 387 bindings | all 387 exported, `List` as a native inductive |
| sweep, Lean kernel route | 385 + 3 added (`List::supf#`, `List::elim#0`, `#1`) | all accepted in a few seconds; `bool::is_true_dec_yes` and `List::filter_map` skipped for holes |
| negative control, Lean kernel route | the sweep + 1 | exactly the open-tag β declaration rejected |
| slice, Lean kernel route and text | 34 | all accepted, no axioms |
| sweep, Lean source text | 7 MB of text | no error, but Lean has not finished parsing when a 20-minute CPU rail stops it |
| slice, Coq 8.18 | 20 of 22 | unchanged: stops at `B::not_not` (§5.3) |

Lean's parser is superlinear in one declaration's size (a synthetic tree of
applications or `fun`s quadruples when it doubles), and Heather's largest
proofs print to hundreds of kilobytes as trees. Then, with the two hole
bodies' spellings fixed and the text route's sharing restored (§5.6):

| | declarations | result |
|---|---|---|
| sweep, Lean kernel route | 387 + 3 added | all accepted, none skipped, in a few seconds |
| sweep, Lean source text, one file | 1 MB of text (from 7 MB) | all accepted in about half a minute, no error |
| sweep, Lean source text, one file per module | 7 files | all accepted; `list` dominates, then `nat` |

Then Rocq, after the singleton-aware `case` (§5.3), the literal bound for
Rocq (§5.4) and native `Wf` inductives for Rocq (§5.1):

| | declarations | result |
|---|---|---|
| slice, Coq 8.18 | 33 (`big` refused for Rocq) | all accepted; the only assumption reported is the prelude's Definitional UIP |
| sweep, Coq 8.18 | 6.5k lines | stops at `Bool::is_true_unique`, a theorem that is unit η itself (§5.3) |
| slice and sweep, Lean, both routes | unchanged | all accepted |

So the text route checks the whole sweep again. The kernel route stays the
one to measure (no elaborator in it); the text is for reading and for the
elaborator's opinion on the same declarations.

The probes (`crates/export/probes/`) are the evidence behind §3 and §5.1. They
are not part of `scripts/test`, because the suite does not assume Lean or
Rocq is installed. The design keeps that so: rechecking in a target is an
opt-in script, not a gate.

## 8. Toward "if it is exported then it checks"

The theorem, relative to a model of a target's kernel:

> If `Ψ ⊢ t : T` in Heather and `t`, `T` are in fragment F, then
> `⟦Ψ⟧ ⊢_HX ⟦t⟧ : ⟦T⟧`, and `⊢_HX` embeds into the target's typing.

It splits into three lemmas, and HX is chosen to make the last two small:

1. **Heather → HX preserves typing and conversion** on F. The work is
   conversion: each Heather conversion rule (β, each ι, Π/Σ/Unit η, the
   irrelevance arms, the strip rule, δ) has to map to an HX rule, under the
   eta-long invariant of §5.2. This lemma lives with the kernel's
   metatheory in **heather-coq**, which already states every one of those
   rules. The acceleration policy's discipline that every fast path
   decides *the same relation* is what keeps the kernel's evaluator out of
   this theorem.
2. **HX → Rocq**: a near-identity embedding into PCUIC, plus the prelude's
   typing. Stated against **MetaCoq**'s formal PCUIC and proved in Coq. This
   is the strongest single argument for Rocq: lemmas 1 and 2 would live in
   the same proof assistant, and MetaCoq's verified checker could even run
   on the output.
3. **HX → Lean**: the same embedding against a formal model of Lean's
   kernel. Lean4Lean is one such model, written in Lean. The roadmap's
   `lean-in-heather` area wants a model of Lean anyway (`lean-fragment`),
   and if that model is written in Heather, lemma 3 is a Heather theorem.
   So could lemma 1 be, with the exporter itself written over Heather's own
   codes: the code recursors are an intensional analysis of exactly this
   syntax. That is the "logic in Heather" route, and it needs the meta layer
   `hih-passes` is building. It is not a first step.

Nothing here is needed for the next rounds. What the design does now to keep
the theorem reachable: HX has no elaborator semantics (holes are a prototype
crutch the typed exporter removes), the per-target prelude is explicit, and
every translation step is syntax-directed except the eta-long pass, which is
type-directed and stated as an invariant.

## 9. Related work (cited from memory; links not checked in this round)

- Lean 4's kernel export format, and the independent checkers that read it
  (lean4checker's replay, nanoda), which are the model for a kernel-level
  Lean import.
- Lean4Lean (Carneiro): Lean's kernel typing formalised in Lean (§8, lemma 3).
- MetaCoq (Sozeau et al.): PCUIC, its metatheory and a verified checker
  (§8, lemma 2).
- Gilbert, Cockx, Sozeau, Tabareau, *Definitional proof-irrelevance without
  K* (POPL 2019): SProp, and the origin of Rocq's `Definitional UIP` rule
  used for `sEq`.
- Dedukti and Logipedia: λΠ-modulo as an interchange format exported to
  several provers, the closest prior art to HX.
- rocq-lean-import (Gilbert): Lean export files into Rocq, the reverse
  composition worth knowing about if both targets are wanted.
- Winterhalter, Sozeau, Tabareau, *Eliminating reflection from type theory*
  (CPP 2019): the conversion-certificate route §5.3 sets aside.

## 10. Next rounds

Each item is an issue (area `heather-in-lean-coq` unless noted), in the order
they pay off:

1. [export-keeps-proofs](../issues/export-keeps-proofs.md) (`language`):
   theorems keep their proofs for export (an elaborator mode, or read them
   from module images), so a sweep does not export every theorem as an axiom.
2. [export-typed-translation](../issues/export-typed-translation.md): the
   typed exporter of §5.6 (checked-spelling erasure, the eta-long invariant,
   names, no holes), with output to Lean's kernel rather than its elaborator.
3. [export-library-sweep](../issues/export-library-sweep.md): run the export
   over `lib/std/nat.hthr`, `bool`, `logic`, `list` through the loader, and
   record every refusal and every target rejection by cause. This is the
   milestone's "done when", and it tests §5.1's conjecture.
4. [export-wf-native-inductives](../issues/export-wf-native-inductives.md):
   realise tier-1 `Wf` instances as native Lean inductives from the
   elaborator's inductive table.
5. [export-checks-theorem](../issues/export-checks-theorem.md): §8's
   statement over HX, lemma 1 first in heather-coq. This is design until
   the sweep says which fragment matters.

Rocq as a full second target is parked inside
[heather-proof-export](../issues/heather-proof-export.md) until unit η is
answered (§5.3). The printer and prelude stay, and the probes record exactly
what Rocq lacks.

## 11. Decisions (Minus, 2026-10-21)

1. **Lean is the first target.** Rocq stays a second printer over HX for
   the fragment it can carry (§6).
2. **Exported names are module-qualified Heather names**, not `g<index>`
   (`issues/export-typed-translation.md`, item 4).
3. **The open-tag β condition** (§5.1) stays an exporter-side condition:
   the realisation is accepted and the library sweep counts violations,
   rather than making it an elaborator invariant now.
   The exporter is untrusted and a violation is loud (Lean rejects the
   declaration). An invariant on the elaborator's *output* would not cover
   the redexes that conversion creates by substitution anyway. Syntactic
   open-tag redexes, if the sweep finds any, can be pre-reduced by the
   exporter. Only conversion-created ones would need a change on the Heather
   side.
