# Conditions whose proofs are interchangeable

Status: **prototype, 2026-11-14.** The elaborator half is built (§3, §5);
the kernel half it would want next (§4.2) is a proposal for Minus and is not
built. Brief: section 1 of the 2026-11-14 language-feature threads ("Proofs a
search finds are interchangeable"). Related: `docs/sprop-design.md` (the
strict formers), `issues/sprop-squash.md` (the squash former as landed),
`issues/sprop-inductives-and-squash-bridges.md` (the deferred bridges),
`issues/found-proof-differs-across-recursion-companions.md` (the hazard).

## 1. What was bent

Heather's proofs are relevant: two calls that differ only in a proof
argument are equal only if the two proofs are. A search (`bv_omega`,
`omega`) finds a different term each time it runs in a different context,
so the same source elaborated twice gives two terms that do not convert.
PR #607 met this in `decreases` bodies, whose companions (`f#ext`, the
unfolding equation) elaborate the body again: `c1#ext` compared
`vector_put(…, p₁)` with `vector_put(…, p₂)`, spent the kernel's budget
comparing two certificates, and was refused. The workarounds it took:

- `measure::lift_found` lifts every proof a search finds in a `decreases`
  body into a theorem `f#found_N`, so every elaboration names one term;
- `Vec::at` is defined as the total function (`vector_get` at a pad), so
  unfolding it drops the proof;
- the `When` design (`/mnt/project-files/design/when-design.md` §7) keeps
  values that hold proofs transient.

Each works around one place where a proof is compared. The general fix is
to say, at the parameter, that its proof is never compared.

## 2. What the kernel already has

**No kernel change is needed for the equality itself.** The kernel has
propositional truncation `∥A∥` (`Type::Squash`, landed 2026-08-25), and
its conversion has an irrelevance arm for it (`conv.rs`, `tm_nf`:
`TyView::Squash { .. } => Ok(())`, after both sides reach weak head
form). Two neutral applications with the same head compare their
arguments at the head's inferred domain (`Conv::tm_ne_app`), so an
argument at a squash domain is accepted without being looked at. Hence

```heather
theorem opaque_same({n: Nat}, f: (i: u64) → ∥i.toNat() < n∥ → u32, i: u64, p, q: i.toNat() < n):
    f(i, squash(p)) = f(i, squash(q)) { refl }
```

checks with `f` a variable (opaque: nothing to unfold), and the same
statement over `i.toNat() < n` is refused (`NotConvertible`). The
argument's whnf is a `squash(…)` constructor, so the arm costs one
discriminant read; the certificate under it is never reduced.

`Nat::Le` and friends compute to `True`/`False` by recursion, and both are
irrelevant (Unit η, Empty η), so at canonical numbers two proofs already
convert. The hazard is at a neutral index (`i.toNat()` with `i` a
variable), where the condition is a stuck `match` and its proofs compare
structurally. That is every loop.

## 3. Surface: the condition's type is `∥P∥`

A parameter or field whose proofs are interchangeable is written with the
type `∥P∥` (or `Squash<P>`). Nothing new is spelled:

```heather
fn Vec::at({w, n: Nat}, self v: [BitVec(w); n], i: u64,
    inside: ∥i.toNat() < n∥ := bv_omega) → BitVec(w) { … }
```

What the elaborator adds (`Checking::check_condition_squashed`,
`crates/elab/src/checking.rs`) is that **a proof of `P` is accepted where
`∥P∥` is expected**, wrapped in `squash`:

- a search, a tactic, `refl` or a hole runs at `P` (none of them can prove
  a squash), so `:= bv_omega` is the default it was;
- anything else is inferred in a probe; if what it proves is not itself a
  squash it is checked at `P` and wrapped, so `inside := h` with
  `h: i.toNat() < n` works, and a condition passed on (`inside := inside`
  with `inside: ∥…∥`) stays as it is.

The rule is introduction only and cannot lose information (`squash` is the
constructor). It fires when the expected type is syntactically
`Type::Squash`; a definition that unfolds to a squash does not get it.

**Alternatives considered.** A marker on the binder (`inside: irrelevant
P`, a `{{ }}` binder) would say the same thing with new syntax and lower to
this; it can be added as sugar if `∥P∥` reads badly in signatures. A `Prop`
sort or an SProp classifier is the judgmental sort `docs/sprop-design.md`
§1 declined, and nothing here needs it: the irrelevance is the squash
former's.

## 4. What a body can do with `inside: ∥P∥`

### 4.1 Today

- Pass it on to another squashed condition, as is.
- Eliminate into any `∥B∥` (`squash_ind`, `squash_map`, `squash_bind`,
  `lib/std/core/logic.hthr`).
- Eliminate into `Unit`, and into Π and Σ of irrelevant types, by the
  compositional constructions in `issues/sprop-squash.md`.
- Ignore it, as `Vec::at` does: the body is the total function, and the
  condition is the caller's obligation.

### 4.2 Missing: absurdity, and with it every decidable condition

From `inside: ∥i < 0∥` a body cannot reach `False`: `squash_map` gives
`∥Empty∥`, and nothing releases `∥Empty∥` into `Empty`. So a function that
uses its condition to rule a case out (`vector_index`'s `Zero` arm,
`false_elim(inside)`) cannot take it squashed.

**Proposal (kernel; for Minus):** the release bridge
`issues/sprop-inductives-and-squash-bridges.md` names as scope point (b),
at `Empty`, which has been irrelevant since Empty η
(`docs/metatheory-ch07-extensions.md` §28):

```
Γ ⊢ q : ∥Empty^l∥
-----------------------------
Γ ⊢ unsquash_empty(q) : Empty^l
```

A fixed former whose result shape the kernel checks; no classifier, no
sort. No β is needed (a closed `∥Empty∥` has no canonical inhabitant), and
neutral congruence skips the argument as `elim_Empty`'s does. Its
metatheory cost is the one real question: the squash relation is
"normalizing-total" (§27 there), which ignores payloads, so it does not
know a `squash(t)` at `∥Empty∥` has a `t` in `Empty`'s relation. The
relation at `∥A∥` would have to carry that the payload is related at `A`
(still ignoring which payload), and §27's case be re-read for it. That is
the abort criterion's place: if the relation cannot carry it without
relevance marks, the bridge does not land.

With the bridge, **every decidable condition is recoverable**, as a
library theorem:

```heather
theorem Squash::recover<P>(q: ∥P∥) requires Decide<P>: P
    // decide P; on ¬P, squash_map(q, ¬P) : ∥Empty∥, released
```

and a condition defined by recursion into `True`/`False` (`Nat::Le`)
recovers by the same recursion. Then `vector_index` can take
`inside: ∥i < n∥` and `Vec::at` can be defined as it (the proof-taking
primitive) instead of as the padded total read.

### 4.3 Not offered

Computing from the proof relevantly. A condition whose proof carries data
a caller reads (a witness, a certificate a function inspects) is not a
condition and stays relevant.

## 5. The lifting, and what retires it

The lifting (`measure::lift_found`) now skips a default whose parameter is
squashed (`MeasureContext::measure_default_goals`): the found proof stays
in the call, each companion has its own, and they convert. The probes in
`lib/_tests/std/core/strict_conditions_tests.hthr` show the trio on the
issue's reproduction (`c1` over `[u32; 64]`, a store at `j + 16` of a read
at `j + 14`, both found):

| condition | lifting | `c1_unfold` |
|---|---|---|
| `i.toNat() < n` | off (`:= { bv_omega }`, not a context search) | refused: `c1#ext` OutOfFuel |
| `i.toNat() < n` | on (`:= bv_omega`) | ok (`c1#found_N`) |
| `∥i.toNat() < n∥` | skipped | ok |

`Vec::at`, `Vec::put` and `Vec::put_byte_be` take their conditions
squashed. After that **no library function whose result is data has a
relevant parameter defaulted to a context search**; the remaining
context-search defaults are evidence theorems (`CReal::…_by_nlinarith`,
`Span::disjoint_by_ends`, …), whose results are proofs. So the lifting has
no library customer left. It retires (a separate PR: delete
`lift_found`, `FoundGoal`, the `#searched` member bases) once Minus agrees
that a relevant condition defaulted to a search is a declaration to
refuse or to warn about ("write it `∥P∥`") rather than to support.

## 6. Cost

- **Conversion:** nothing added, and cheaper where it fires: a squashed
  argument is accepted at its weak head form, where today two certificates
  are compared.
- **Elaboration:** a non-search expression checked against a `∥P∥` is
  inferred once more in a probe. Squash positions are rare (conditions,
  `BoundedList`'s `fit`), so this is not on a hot path.
- **Kernel trust base:** unchanged by §3 and §5. §4.2 would add one former.

## 7. Native code and `When`

A squashed condition is erased like any proof: the reflector reads `v.at`'s
receiver and index, not its condition, and the linked SHA-256's assembly is
unchanged (`scripts/linked --check`). For `When<T, P>`, a `Present(t, h:
∥P∥)` makes two values with different proofs convertible, which retires
the hazard `when-design.md` §7.1 probes for: values holding conditions need
not stay transient.

## 8. Open, for Minus

1. The surface: the type `∥P∥` alone, or a binder marker as sugar.
2. The bridge of §4.2 (kernel, with its metatheory re-read).
3. Retiring the lifting (§5), and what to say about a relevant condition
   defaulted to a search.
