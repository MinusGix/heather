# Casting: what a cast is in Heather, and how it is written

Date: 2026-10-30. Status: **decided 2026-10-30** (§8: option B, `↑`, and the
recommended answer to every other question); §6.4 is the open design.
Owner: [casting-standard](../issues/casting-standard.md). Consumer:
[push-cast-through-embeddings](../issues/push-cast-through-embeddings.md).

Heather has avoided a coercion story so far, deliberately: every past round
that met one declined it (the `Expr`/`Ty` bridge coercion was built and
retired, `docs/surface-polymorphism.md` §5; implicit `Ok`-wrapping was
refused, `issues/prelude-option-and-friends.md` 2026-08-13; `Pos` chose
search over insertion, `docs/positivity-evidence-design.md` §4). Meanwhile
the library grew a numeric tower whose casts are written five different ways
and recognized by four tactics, each by its own spelling. This note proposes
the standard: what counts as a cast, how one is written, what it elaborates
to, and how tactics move casts around.

**The proposal in one paragraph.** A cast is an *explicit mark with an
inferred target*: `↑x` says "a cast happens here", and the elaborator decides
which one from the expected carrier, by the same bounded bidirectional
protocol numerals already use. Only lossless embeddings, declared as edges of
one cast graph, can be written `↑`; every lossy conversion stays a named
function. A cast elaborates to the edge functions themselves, composed along
the one path the graph allows, so `↑n` at `Rat` *is* `Rat::ofInt(OfNat(n))`,
the term the numeral `3` already has the shape of. Each edge carries its law
table, and one tactic family (`push_cast`, `norm_cast`) reads it, so `ring`,
`linarith`, `mono` and `intervals` stop recognizing casts by hand. Nothing is
ever inserted where the source did not write `↑`, and a mismatch that a cast
would fix gets a diagnostic that says so.

## 1. What the library does today

Counts are over `lib/` at `f61b59d`.

### 1.1 Five spellings for one idea

| Edge | Spelled | Uses | Laws named |
|---|---|---|---|
| `Nat → Int` | `OfNat(n)` (constructor), `n.int()` (method, `int.hthr:658`, unfolds to `OfNat(n)`) | 1325 / 731 | `Int::ofNat_add`, `ofNat_mul`, `ofNat_le_iff` |
| `Int → Rat` | `Rat::ofInt(i)` | 127 | `Rat::ofInt_add`, `ofInt_mul`, `ofInt_le`, `ofInt_inj` |
| `Rat → CReal` | `CReal::ofRat(q)` | 268 | `CReal::ofRat_add`, `_mul`, `_neg`, `_inv`, `_le`, `_lt`, … |
| `Int → Dyadic` | `Dyadic::ofInt(i)` | 11 | `Dyadic::ofInt_le`, `ofInt_lt` |
| `Dyadic → Rat` | `d.rat()` (method) | 464 | `Dyadic::rat_add`, `rat_mul`, `rat_ofInt`, … |
| `Nat → Rat` | no function: `Rat::ofInt(OfNat(n))` | 76 | `Rat::ofNat_nonneg` |
| `Dyadic → CReal` | no function: `CReal::ofRat(d.rat())` | — | `Dyadic::real_add`, `real_mul`, `real_neg` |
| `Finite(F) → Rat` | `x.val()` | 6 | — |
| `BitVec(n) → Nat` | `x.toNat()` | 1006 | `BitVec::toNat_ofNat`, `toNat_lt_pow`, … |
| `Char → Nat` | `c.toNat()` | 1 | — |

and the lossy direction, which is a different kind of thing:
`BitVec::ofNat` (wraps mod `2^n`, 966 uses), `Int::toNat` (truncates at 0),
`Interval::of_rat(q, p)` (rounds outward at precision `p`).

Three conventions are mixed: `Target::ofSource(x)` (static), `x.target()`
(method on the source) and a bare constructor. Composite casts have no name
and are written as the composition, and lemma names follow whichever
spelling the edge has (`Rat::ofInt_add` vs `Dyadic::rat_add`), with the
composite's laws named for a function that does not exist
(`Dyadic::real_add`).

### 1.2 One cast that is already implicit: numerals

`docs/carrier-directed-numerals-design.md` is the one place the language
already inserts an embedding: a numeral checked at `A` resolves
`Numeral<A>` and applies its `ofNat`, so `3 : Rat` elaborates to
`Rat::ofInt(OfNat(3))` and `3 : CReal` to `CReal::ofRat(Rat::ofInt(OfNat(3)))`.
It is narrow on purpose: checking position only, a bounded search for an
anchor leaf in an operator spine (`operator_carrier_leaf`,
`crates/elab/src/surface.rs:19`), no delayed metavariables, `Nat` by default.
Characters, strings and decimal literals follow the same ladder
(`crates/elab/src/literals.rs`). It works and nobody has wanted to retire it.
It is also the precedent this proposal builds on: a literal is notation for a
value at a carrier, not a conversion of a value someone already has.

### 1.3 Tactics recognize casts by spelling, each its own way

- `omega` reads `OfNat(e)` / `int::OfNat(e)` through the Nat side
  (`crates/elab/src/omega_cert.rs:822`, `:1031`).
- `ring` at `Rat`/`CReal` reads a cast of a Nat sum, product or successor as
  an atom with a definition, by recognizing `…OfNat(e)…` with only closing
  parentheses after it (`docs/ring-normalization-design.md` §8, "Casts"),
  with its own push lemmas `RingExpr::of_nat_add`/`of_nat_mul`/`of_nat_succ`.
- `bv_omega` reads `toNat`/`ofNat` of words (`crates/elab/src/bv_omega.rs`).
- `intervals` has an `OEmbed` operation for `CReal::ofRat`
  (`lib/std/tactic/interval_tactic.hthr:146`).
- `mono` knows no casts, which is why `interval.hthr` names `rat_add` at
  every bound (`docs/interval-proof-shapes.md` §2) — the trigger issue.

And the classes carry embeddings with laws already: `CommRingOfInt.of_int`
with its four homomorphism laws (`lib/std/algebra/semiring.hthr:162`) and
`OrderedField.of_nat` with two (`docs/constructive-ordered-field-design.md`).

### 1.4 Where it hurts

- **Spelling is identity.** Evidence search, `rel_cong` and the tactics
  compare spellings (the note on `Numeral<Rat>`, `rat.hthr:80`), so
  `n.int()` and `OfNat(n)` are two atoms to `ring` though they convert, and
  `Dyadic::ofInt(n).rat()` and `Rat::ofInt(n)` are two values related only by
  `Dyadic::rat_ofInt` (a diamond, bridged by hand at
  `lib/std/num/float/error.hthr:346`).
- **Image laws by hand.** Every arithmetic step on bounds owes a
  homomorphism law on the side it happens on (the issue's example).
- **Noise in statements.** `x * CReal::ofRat(Rat::ofInt(OfNat(n + 1)))`
  (`ring_field_tests.hthr:37`) says "`n + 1` as a real" in 40 characters.

## 2. How other systems do it

From the systems' documentation and long use, not re-measured here.

**Lean 4 / Mathlib.** Coercions are inserted when unification fails at a
known expected type: `Coe`, `CoeTail`, `CoeHead`, `CoeOut`, `CoeDep`
(value-dependent), `CoeFun`, `CoeSort`, chained through `CoeT`. Instances
are unfolded at elaboration, and `@[coe]` heads (`Nat.cast`, `Int.cast`,
`Subtype.val`) are displayed as `↑x`. The numeric tower runs through classes
(`NatCast`, `IntCast`, `RatCast`), so `((n : ℤ) : ℚ)` and `(n : ℚ)` are
different terms, related by simp lemmas (`Int.cast_natCast`). Inside
arithmetic, `binop%` computes the "maximal" carrier of an operator tree and
casts at the *leaves*: `(a + b : ℤ)` with `a b : ℕ` is `↑a + ↑b` (Lean 3 cast
at the root; the change moved where truncated subtraction bites). The cast
tactics are a tagged simp set: `@[norm_cast]` lemmas are classified as
*move* (`↑(a + b) = ↑a + ↑b`), *elim* (`↑a = ↑b ↔ a = b`) and *squash*
(`↑↑a = ↑a`); `push_cast` moves casts to the leaves, `norm_cast` moves them
up and eliminates them, `exact_mod_cast`/`assumption_mod_cast` compare up to
that normal form, and `zify`/`qify`/`rify` lift a goal into a bigger
carrier. What users fight: the target of `↑x` is invisible in goals; where a
cast landed depends on elaboration order and unification failure; diamonds
between composite casts need squash lemmas; and `↑(n - 1)` vs `↑n - 1` is
the classic Nat-subtraction trap, made worse by not seeing which was
inserted.

**Coq / Rocq.** `Coercion f : A >-> B` declares an edge of a global
coercion graph; paths are composed, inserted on mismatch, and Coq reports
"ambiguous paths" when two paths join the same classes (newer versions
accept them only if the paths are convertible). `Funclass`/`Sortclass`
coercions too. The standard library writes the numeric tower *explicitly*
(`Z.of_nat`, `IZR`, `inject_Z`) with numerals resolved by notation scope
(`%Z`, `%R`), and `lia`'s preprocessing `zify` pushes `Z.of_nat` inward.
**Mathematical Components** is the interesting middle: subtype projections
(`val`) and structure projections are coercions, but numeric casts are
explicit *postfix notations*: `n%:R` (Nat into any ring), `n%:Z`, `x%:num`,
with laws named by cast and operation (`natrD : (m + n)%:R = m%:R + n%:R`,
`natrM`, `ler_nat`). A cast is two characters, always visible, and its
target is inferred.

**Agda.** No coercions at all. The standard library writes `+ n` (the
constructor `+_`), `toℕ`, `fromℕ`, `ℤ→ℚ`, explicitly. Literals are
overloaded through the `Number` record (`fromNat` with a `Constraint`, which
is how `Fin` literals check their bound) — Heather's `Numeral` plus its `Fin`
rule is the same design. The cost is noise: casts are full names.

**Idris 2.** Idris 1 had `implicit` conversion functions; Idris 2 does not.
What remains is the `Cast from to` interface: `cast x` is explicit, and its
target comes from the expected type. Literals go through `fromInteger`,
`fromString`, `fromDouble`. One lesson to not copy: `Cast` covers lossy
conversions (`Double → Int`) under the same name as lossless ones.

**Rust** (the surface Heather's syntax resembles). No implicit numeric
widening. `From`/`Into` are lossless by convention and `x.into()` takes its
target from the expected type; `TryFrom` is the partial one; `as` covers
primitive casts *including truncating ones*, which is widely regretted
(Clippy's `cast_possible_truncation` and friends exist to flag it).

What the survey says, in one line each:

1. Every system that keeps implicit insertion pays in diagnostics (which
   cast? where?) and in coherence lemmas between paths.
2. The systems people praise for numeric code (MathComp, and Lean *with*
   its cast tactics) win on the *tactic* side and on short visible notation,
   not on insertion.
3. "Explicit mark, inferred target" (MathComp's `%:R`, Idris's `cast`,
   Rust's `into`) is the stable middle ground.
4. Lossless and lossy conversions must not share a spelling.

## 3. What a cast is: three kinds of conversion

The standard sorts every conversion into one of three kinds, and only the
first is a cast.

1. **Embeddings** — total, injective, and the source is a substructure of
   the target: `Nat → Int → Rat → CReal`, `Int → Dyadic`, `Dyadic → Rat`,
   `Finite(F) → Rat`; later a subtype's projection to its ambient type
   (`Pos<Nat> → Nat`), `Fin(n) → Nat`, `Char → Nat`, and `BitVec(n) → Nat`
   (injective, but its laws are conditional, §6.3). These are written `↑`.
2. **Lossy conversions** — not injective or not total: `BitVec::ofNat`
   (wraps), `Int::toNat` (truncates), floor/round from `Rat`, a float's
   `round(mode)`. **Always a named function, never `↑`.** Their name should
   say what is lost (`wrap`, `truncate`, `floor`); renaming the existing ones
   is a separate, optional tidy (§7.4).
3. **Structural adaptations** — `Prop → Bool` by `decide`, `T → Result<T, E>`
   by `Ok`, `Nat → Pos<Nat>` with a searched proof, a record used as a
   function. These are not casts and do not go through `↑`; each keeps its
   own recorded decision (`issues/bool-from-decidable-prop.md`,
   `issues/prelude-option-and-friends.md`,
   `docs/positivity-evidence-design.md`).

## 4. The options

**A. Status quo plus a cast tactic.** Casts stay named functions, written in
full. Add the edge registry and `push_cast`/`norm_cast` (§6) only. Smallest
change; fixes the trigger issue; leaves the five spellings and the noise.

**B. Explicit mark, inferred target (recommended).** `↑x` is a cast whose
target comes from the checking position or an operator anchor; `cast<B>(x)`
names the target where none is known. Only declared embedding edges qualify;
the result is the composed edge functions. Plus everything in A. Nothing is
inserted that was not written.

**C. B, plus leaf insertion inside anchored operator spines.** In an
operator tree whose carrier is decided (by the expected type or an anchor
leaf, the numeral protocol), a leaf whose own type has an embedding edge
into that carrier is cast without a mark: `n + x` with `n: Nat, x: Rat`
elaborates to `↑n + x`. This is Lean 4's `binop%` restricted to lossless
edges and to operator notation. "Smart", bounded, but implicit: the source
`n + 1 - x` hides which subtraction ran.

**D. General coercion on mismatch** (Lean `Coe`, Coq `Coercion`) at every
checking position, including function arguments. Rejected: it is the
mechanism every past Heather round declined, for the reasons recorded there
(the elaborated term diverges from the written one, which is what `refl`
unfolds, diagnostics print and theorems are stated over), and it is where
the survey's costs live.

| | A | B | C | D |
|---|---|---|---|---|
| Source shows where a cast is | yes (full name) | yes (`↑`) | no, inside arithmetic | no |
| Source shows which cast | yes | no, inferred | no | no |
| `Rat::ofInt(OfNat(n + 1))` reads | as is | `↑(n + 1)` | `↑(n + 1)`; bare `n + 1` at `Rat` means `↑n + 1` | `n + 1`, at the root or the leaves by elaboration order |
| New elaborator machinery | none | a checking-only leaf in the numeral protocol | B + leaf search per operator node | coercion insertion everywhere |
| Diagnostics | unchanged | name the edge on a `↑` failure; suggest `↑` on a mismatch | must explain insertions | must explain insertions |
| Reversible later | — | to C, cheaply | to B, costly (source loses marks) | — |

## 5. The recommendation: B, in detail

### 5.1 The cast graph

An edge is a registered map. The sketch below shows only the map, as a
one-field class the way `Numeral` is; §5.6 refines it so that an edge is a
*morphism value* (the map and its laws as a record), which is the form that
also replaces the combined classes (`CommRingOfInt`, `OrderedFieldOfInt`, the
proposed `OrderedFieldOfRat`):

```heather
class Cast<A, B> { cast: A → B }

instance Cast<Nat, Int>      { cast := OfNat }
instance Cast<Int, Rat>      { cast := Rat::ofInt }
instance Cast<Rat, CReal>    { cast := CReal::ofRat }
instance Cast<Int, Dyadic>   { cast := Dyadic::ofInt }
instance Cast<Dyadic, Rat>   { cast := Dyadic::rat }
```

declared beside the target type (an edge into `Rat` lives in `rat.hthr`,
where `Numeral<Rat>` is), and visible exactly when both types are. Only
*primitive* edges are declared. A composite cast is the composition of the
edges along a path, found by the elaborator, never declared as its own
instance — so `Nat → Rat` is `Rat::ofInt(OfNat(n))` and needs no
`Rat::ofNat`.

**Paths are unique by the shortest-path rule.** Between two types the
elaborator takes the shortest path; two shortest paths of the same length is
a refusal *at the edge declaration that created the second one*, naming both
paths. `Int → Rat` directly (length 1) beats `Int → Dyadic → Rat`
(length 2), so `↑i : Rat` is always `Rat::ofInt(i)`, and
`Dyadic::rat_ofInt` becomes the one coherence law the cast tactics use to
normalize the long path to the short one (a *squash* law, §6.1). Why
shortest: it is the spelling the numerals already produce (`Numeral<Rat>` is
`Rat::ofInt(OfNat(n))`, the `Nat → Int → Rat` path), so `↑n` and `3` have the
same shape and `ring`'s existing reading serves both.

**One spelling per edge.** `↑n : Int` is `OfNat(n)`, not `n.int()`. The
method stays (it is convenient in code that wants no `↑`), but the cast
tactics normalize `n.int()` to `OfNat(n)` by its δ-step, and new library
statements use `↑`.

### 5.2 Writing a cast

- **`↑e`** is a prefix operator at the precedence of `-` and `¬`. It is a
  *checking-only* form, exactly as `one<A: Numeral>()` is to the numeral
  protocol's classifier: it supplies no carrier and needs one.
  - At a checking position expecting `B`: infer `e : A`, find the path
    `A ⇝ B`, emit the composed edge functions applied to `e`.
  - As a leaf of an operator spine: the spine's carrier comes from its
    expected type or from an anchor leaf (`operator_carrier_leaf`, unchanged:
    `↑` leaves are skipped as anchors, like numerals and `one()`). So
    `↑n * x` with `x: Rat` reads `↑n` at `Rat`.
  - Nowhere else. `let y = ↑n;` is refused: "a cast needs a target here;
    write `cast<Rat>(n)` or annotate `let y: Rat = ↑n`". No delayed
    metavariables, by the numeral design's rule.
  - `A = B` is allowed and elaborates to `e` (so generic code can write `↑`
    where the carrier may already be the target), and is linted when both
    are concrete and equal.
- **`cast<B>(e)`** is the same with the target named, usable anywhere,
  including inference position. It is an ordinary generic function whose
  elaboration is special-cased to unfold to the path, so it never appears in
  a term.
- **Precedence settles the subtraction trap visibly**: `↑(n - 1)` casts the
  truncated Nat difference, `↑n - 1` subtracts at the target. The source
  always says which.

Glyph: `↑` matches the library's existing Unicode operators (`≈`, `¬`,
`⁻¹`, `∑`) and Lean's display, which readers of exported proofs know. The
lexer needs the symbol and the editor grammar its inventory entry
(`tree-sitter` drift, `issues/tree-sitter-grammar-drift.md`). If an ASCII
form is wanted, `cast<_>(e)` is it; no second operator.

### 5.3 What a cast elaborates to, and how it is printed

The term is the edge functions applied, β-reduced through the instance as
the numeral's `ofNat` is: `↑n : CReal` is
`CReal::ofRat(Rat::ofInt(OfNat(n)))`, byte-identical to what is written
today. So nothing downstream changes: `refl`, conversion, module images,
export to Lean/Rocq, and every tactic see the term they see now. The
change is surface-only, and the library can migrate statement by statement.

The speller prints an application of a declared edge (or a path of them)
back as `↑e`, so goals and diagnostics show what was written. In a type
mismatch whose two sides differ under a cast, the speller names the target,
`cast<Rat>(n)`, because there the target is the information the reader
lacks — the Lean complaint (§2) fixed where it matters, without cluttering
every goal.

### 5.4 Smart without implicit: the diagnostic

When a checking position expecting `B` receives `e : A`, and the cast graph
has a path `A ⇝ B`, the mismatch error says so and offers the fix:

```
error: expected `Rat`, found `n: Nat`
  help: `Nat` embeds in `Rat` (Nat → Int → Rat); write `↑n`
```

This is the "smart" half of the user's lean: the elaborator knows the cast
and says which one, at the place it is needed, and the source still records
it. Lossy conversions get the same help naming their function, worded as a
choice (`BitVec::ofNat(n)` wraps mod 2^64; is that intended?).

### 5.5 Why not C now

C is cheap to add later (the leaf search already exists for numerals) and
expensive to take back (sources written under C have lost their marks). B
also produces the data that decides C: once the library is migrated, count
the `↑` per statement. If it is dense in exactly the arithmetic spines C
would cover — e.g. `interval.hthr` bounds — C can be turned on per module
(an attribute, like the lint profile) rather than language-wide.

### 5.6 An edge is a morphism, not a combined class

Added 2026-10-30, after Minus's objection (on
[interval-containment-once-over-ordered-field](../issues/interval-containment-once-over-ordered-field.md))
to classes like `CommRingOfInt`, `OrderedFieldOfInt` and `OrderedFieldOfRat`,
which fuse a structure with one particular map into it. The cast graph wants
the same split, so the standard is:

- **A morphism is data.** A record per kind of structure-preserving map,
  indexed by the two carriers' relations and operations the way the layers
  are (`docs/constructive-ordered-field-design.md`):

  ```heather
  record OrderedRingHom<A, B>(…A's ≈ < <= + *…, …B's…) {
      map: A → B,
      map_respects, map_zero, map_one, map_add, map_mul,
      map_le_iff, map_lt_iff,     // order-embedding: preserves and reflects
  }
  ```

  with weaker records (`RingHom`, `OrderEmbedding`) for edges that are not
  ordered-ring maps. The structures stay plain `OrderedField`, `CommRing`.
- **A cast edge is a registered morphism value**, not an instance of a
  combined class: `Rat::ofInt_hom: OrderedRingHom<Int, Rat>(…)`, with
  `map := Rat::ofInt` and the existing `Rat::ofInt_*` lemmas as its fields.
  `↑` elaborates to the `map` field unfolded, so §5.3's terms are unchanged.
  The §6.1 law table *is* the record's fields (typed, not lemma names), plus
  any extra laws listed beside it (`↑(a⁻¹)`, `↑(a ^ n)`).
- **Generic code takes the morphism as a parameter**, not a bigger class:
  `section<K: OrderedField(≈, <, <=, +, *)>(φ: OrderedRingHom<Rat, K>(…))`
  for interval containment. At `Rat`, `φ` is the identity morphism and at
  `CReal` it is `CReal::ofRat_hom`, the same values the cast graph holds. One
  definition of "the embedding" serves `↑`, `push_cast` and the generic
  lemmas.
- **The more fundamental constraint, for `Int`.** `Int` is initial among
  rings: any `CommRing` already has a map from `Int` (by `0`, `1`, `+`,
  negation), and any two ring morphisms out of `Int` agree up to `≈`. So
  generic code needs no `of_int` field at all: it can define the map, and a
  carrier's own spelling (`Rat::ofInt`) is related to it by the uniqueness
  theorem, which is exactly a *squash* law (§6.1). The open question is only
  whether `ring`/`linarith` can read coefficients through the generic map at
  acceptable cost, or need the carrier's spelling handed to them (then as a
  morphism parameter, not a class field). The same holds for `Nat` among
  semirings. `Rat` is initial among fields of characteristic zero, but its
  map needs inverses and apartness, so `Rat → K` stays a parameter.

## 6. The cast tactics

Independent of the syntax choice (A, B and C all need it), and the part
that closes [push-cast-through-embeddings](../issues/push-cast-through-embeddings.md).

### 6.1 One law table per edge

Beside each edge, a table of its laws. Under §5.6 the table is the
morphism record's fields plus extras; the first cut can be lemma names in
`mono`'s style
(`lib/std/tactic/mono.hthr`: records of lemma names, skipped when the name
does not resolve), sorted by Lean's three classes because the three are used
differently:

- **move**: `↑(a + b) ≈ ↑a + ↑b`, `↑(a * b)`, `↑(-a)`, `↑(a⁻¹)`, `↑(a ^ n)`,
  `↑0 ≈ 0`, `↑1 ≈ 1` — the existing `Rat::ofInt_add`, `CReal::ofRat_mul`,
  `Dyadic::rat_add`, … under their names.
- **elim**: `↑a ≤ ↑b ↔ a ≤ b`, `↑a < ↑b ↔ a < b`, `↑a ≈ ↑b ↔ a = b`
  (`CReal::ofRat_le`, `Rat::ofInt_inj`, `Int::ofNat_le_iff`, …).
- **squash**: coherence of a long path with the short one
  (`Dyadic::rat_ofInt`), and `↑(numeral) ≈ numeral`.

Laws are along the target's relation (`≈` at `Rat`/`CReal`, `=` at `Int`),
which is what setoid `rewrite` already takes. For a class carrier the table
can name class laws (`CommRingOfInt::of_int_add`), so generic sections get
the cast tactics too. Naming standard for new laws: `<edge function>_<op>`
in the edge function's namespace, as most already are (`Rat::ofInt_add`,
`Dyadic::rat_add`); a composite's laws are not stated (they follow by
composing), so `Dyadic::real_add` and friends become derivable and can be
retired.

### 6.2 `push_cast`, `norm_cast`, `exact_mod_cast`

- **`push_cast`** rewrites bottom-up along the target relation with the
  move and squash laws, images outward to images at the leaves, through
  `rewrite`'s `Respects2` crossing (`docs/equation-rewrite-design.md` §9). It
  is a Heather-side tactic over the host interface, like `mono`.
- **`norm_cast`** is `push_cast` on both sides, then the elim laws: when
  both sides of a comparison are images of one source along one path, the
  goal is lifted back to the source (a `Rat` comparison of two Int casts
  becomes an Int goal that `omega` decides). This is Lean's `zify` read the
  other way, and it is what lets the strong solvers at the small carriers
  close goals stated at the big ones.
- **`exact_mod_cast(h)`** normalizes `h` and the goal and compares.
- **Consumers.** `mono` runs `push_cast` on both sides before comparing
  (the issue's sketch); `ring`'s spelling-based cast reading
  (`RingExpr::of_nat_add`, …) becomes a `push_cast` preprocessing step, and
  `intervals`' `OEmbed` reads the table. `omega` and `bv_omega` keep their
  own readers: their casts are the solvers' atoms, not rewrites.

### 6.3 Conditional laws

`BitVec(n) → Nat` is injective, but `↑(a + b) = ↑a + ↑b` holds only without
overflow. The table admits a law with premises (`toNat_add_of_lt`), each
discharged by `omega` over the context, and a failed premise is reported by
name, as `bv_omega` does (`docs/bv-omega-design.md`). Until that lands,
`BitVec → Nat` stays out of `↑` and `bv_omega` owns it.

### 6.4 Doing better than Lean's cast pushing

Added 2026-10-30. Minus's verdict on `push_cast`/`norm_cast` from use: hard
to direct, and troublesome. Where the trouble comes from, and what Heather
does instead:

| Lean's trouble | Its cause | Heather's answer |
|---|---|---|
| The goal comes back in a shape nobody asked for | a simp set rewrites everywhere to *its* normal form, with lemma priorities and other simp lemmas deciding the outcome | the user says the shape (*state, don't steer*, below); the tactic only checks it |
| Hard to aim at one subterm | simp has no location short of `conv` | a located move takes a pattern (`push_cast(at: ↑(n + 1))`), the way `rewrite` does |
| A missing lemma silently does nothing | `@[norm_cast]` tagging, and the elim/move/squash class is guessed from the lemma's shape | an edge is a morphism record (§5.6): its laws are its fields, so coverage is fixed by the type and a missing law is a named refusal, not a silent stop |
| Partial progress, then an opaque "failed to simplify" | the simp loop has no notion of what was owed | a refusal names the subterm that blocked and why: no law for `↑(a / b)` on `Int → Rat`, or a side condition `b <= a` that `omega` could not prove from the context |
| Numerals need special splitting (`(2 : ℝ)` as `((2 : ℕ) : ℝ)`) | numerals and casts are different terms | free: a numeral at `Rat` *is* `↑` of a `Nat` numeral (§1.2) |
| Diamonds of composite casts need squash lemmas | many spellings of one composite | one spelling per path (§5.1); squash laws are only the declared second paths |
| Nat subtraction and division need hand-applied lemmas | conditional laws are not simp lemmas | conditional laws are part of the table, discharged by `omega` against the context and reported by name when they fail (§6.3) |

The two ideas that do most of the work:

**1. Cast-transparent tactics, so cast pushing is rarely a step at all.**
In Lean you push casts *so that* `ring`, `linarith` or `omega` can see the
goal. In Heather the arithmetic tactics read casts themselves. Their reifiers
already build an expression tree; each node also records the carrier it is
computed at, and the casts are edges between carriers. The tactic then
*chooses* where to decide: the lowest carrier every atom lives in (two
`Int` images compared at `Rat` are decided at `Int` by `omega`), or the
target carrier with every image pushed to the leaves (for `ring` and
`linarith` over mixed atoms). It emits the morphism laws as part of its own
certificate. No intermediate goal is shown, so there is no normal form to be
surprised by. `ring` already does a fragment of this by hand (§1.3), and
`mono` gets it by reading both sides through the same tree.

**2. State, don't steer, when the user does want a different goal.**
Instead of a sequence of moves whose result you discover, you write the goal
you want:

```heather
// goal: ↑(n + 1) * x <= ↑m * x   at Rat, with n, m: Nat
cast_to(↑n * x + x <= ↑m * x);    // a goal stated at the shape wanted
cast_to(n + 1 <= m);              // or at the carrier wanted: decided by omega
```

`cast_to(S)` reads both the goal and `S` through the carrier tree, checks
that they agree modulo the edges' laws (and the context, for conditional
ones), and replaces the goal by `S`. When they do not agree, it reports the
first subterm where the two readings differ, the way `ring` names what
clearing leaves. `have h: S := cast_from(h0)` is the same for a hypothesis.
This replaces `norm_cast`, `push_cast`, `exact_mod_cast`, `zify`, `qify`
and `rify` with one directed form, where the direction is whatever the user
wrote. The located `push_cast(at: pattern)` stays for the case where writing
the whole goal out is longer than naming the one subterm.

What it costs: the carrier-annotated reader is shared by `ring`,
`linarith`, `mono`, `omega` and `cast_to`, so it is one piece of work with
five consumers, built on the existing reifiers. `cast_to`'s check is a
normalization of both sides with the move laws, then a syntactic comparison,
so it is as predictable as the morphism tables are complete.

## 7. What changes, in order

1. **Decide** (§8). This note and its issue only.
2. **Law tables + `push_cast`** for `Nat → Int → Rat → CReal`,
   `Int → Dyadic → Rat`; `mono` preprocesses with it; `interval.hthr`'s
   `rat_add` calls go away. Needed under every option.
3. **Under B: `Cast` edges, `↑` and `cast<B>`**, the speller's `↑`, the
   mismatch help. Tests along the four axes of
   `docs/testing-generated-terms.md` (literal and neutral operand, open
   carrier, checking position, a negative control: `↑` with no target, a
   lossy edge, an ambiguous second path).
4. **`norm_cast`/`exact_mod_cast`**, and `ring` reads casts through
   `push_cast`.
5. **Optional tidy**: migrate statements to `↑` where it shortens them;
   rename lossy functions for what they lose; retire composite-law lemmas.
   Never a bulk rewrite in one PR.

## 8. Decisions (Minus, 2026-10-30)

1. **Option B.** C stays available as a per-module opt-in if `↑` proves
   dense (§5.5); D is rejected.
2. **Glyph `↑e`**, with `cast<B>(e)` as the named form.
3. **Edges**: the numeric tower and `Dyadic`/`Finite` now; subtype
   projections next; `BitVec → Nat` only with conditional laws (§6.3).
4. **Diamonds**: shortest path wins, with a squash law for the other path.
5. **Edges are morphism values** (§5.6), replacing the combined
   `…OfInt`/`…OfRat` classes over time.
6. **`↑` produces `OfNat(n)`**, and the tactics normalize `.int()` to it.

7. **The cast tactics are §6.4's**: cast-transparent tactics through a
   shared reader, and `cast_to(S)` for stating the goal wanted (Minus:
   stating the goal is what a model writing mathematics does most easily).

## 9. Slice 1: the edges, and `mono` reading them (2026-10-30)

What landed, against §7's step 2:

- **`OrderedRingHom<A, B>`** (`lib/std/algebra/morphism.hthr`), with the
  map and both sides' relations and operations as indices and the ten laws
  as fields, and a theorem per field (`OrderedRingHom::add_law`, …) taking
  the morphism explicitly. A call names the carriers
  (`OrderedRingHom::add_law<Dyadic, Rat>(Dyadic::rat_hom(), a, c)`): the
  record is structural, so `B` occurs in a morphism's type only through its
  indices' types, and nothing infers it from the morphism.
- **Three edges**: `Dyadic::rat_hom`, `CReal::ofRat_hom`, `Rat::ofInt_hom`,
  each beside its target type and built from the existing image lemmas.
  Every index is a named global: `Int`'s `≈` is the new `Int::Same` (`=`),
  because a λ there is β-reduced out of the field types and then cannot be
  inferred back.
- **`lib/std/tactic/cast.hthr`**: `cast_move(h, depth)` reads an image one
  layer in (`(a + c).rat()` to `a.rat() + c.rat()`, and an image of an image
  through `respects_law` on the outer edge), returning the moved term and its
  `≈` proof without touching the goal. The law is applied to fresh holes, one
  per index, with the target carrier's hole set to the image's type first
  (the structural record again).
- **`mono` reads casts** where a goal's sides do not split by a law: an
  order between two images of one edge becomes the source order
  (`le_law`/`lt_law`), else a side that an edge moves is moved and the goal
  continues on the moved side (`Rat::le_of_same_of_le` and its three
  siblings per carrier, `MonoCarrier.pushes`). Probes in
  `lib/_tests/std/tactic/cast_tests.hthr`.
- **Customers**: `interval.hthr`'s negation, sum, positive-product and
  corner bounds, and `creal_interval.hthr`'s, are `by mono_with([…])` over
  the bounds' facts; `Dyadic::real_neg`/`real_add`/`real_mul` (the
  two-edge composites) are retired, as §6.1 predicted.

What it does not do yet, each for a reason:

- **Not a normal form.** `mono` moves an image only where its own split
  stops, layer by layer; a hypothesis stated at the fully pushed form is not
  matched against an unpushed goal. (Slice 2, §10, adds that.)
- **No `0`, `1` or subtraction moves** in `mono` yet (the fields exist), and
  `Nat → Int` is not an edge yet: it needs an `OrderedSemiringHom` (`Nat`
  has no negation), with its laws stated at `Int::Same`.
- **A client imports `morphism`.** The tactic looks the field theorems up by
  name where the `by` is, so a module using `mono` across casts imports
  `morphism` (and the edges' modules, which it already does for the types).
- **Host gaps found on the way.** The tactic side cannot project a record
  field (no projection globals; a record value views as `HOther`), so the
  laws are read through the field theorems. `apply` of a generic class lemma
  at a concrete carrier fails to infer the relation's carrier, so the push
  lemmas are per carrier. Two open types compared by the host are now the
  same when they are the same syntax (`same_ty`'s `(None, None)` case, which
  answered `false`): a hole whose type mentions earlier holes,
  `map: ?A → ?B`, needs it.

## 10. Slice 2: the normal form, `cast_from` and `cast_to` (2026-10-30)

- **The normal form** (`cast_push`, `lib/std/tactic/cast.hthr`): a side
  read with every image pushed to the leaves. An operation of the carrier
  has its operands read and is rebuilt by its `respects` lemma; an image an
  edge moves is moved (`cast_move`) and read again; anything else is a leaf.
  The proof `h ≈ normal` is built as it goes, `None` where nothing moved. The
  carriers it is read at are a table of names (`cast_carriers`: `Rat` and
  `CReal`, their relations, `≈` laws and the `+`, `*`, `-` congruences).
- **`cast_from(h)`** proves the goal from `h` when the two are one relation
  whose sides agree in normal form, carrying `h` along the four `≈` proofs
  (`le_respects`/`lt_respects`, or `trans` for `≈`). It accepts `h` pushed
  in, pulled out, or stated at a carrier an edge maps into the goal's:
  `h: a <= b` at `Dyadic` proves `CReal::ofRat(a.rat()) <= CReal::ofRat(b.rat())`
  through two edges, and `h: m + 1 <= n` at `Int` proves
  `Rat::ofInt(m) + 1 <= Rat::ofInt(n)` (a `Rat` numeral is `Rat::ofInt`'s image
  of an `Int` one, §1.2). Lifting is lazy and uses only the goal relation's
  law (`le_law`, `lt_law`, `respects_law`), straight into the goal's carrier
  first and through another carrier second: an eager lift of every fact
  through every edge and law ran out of tactic fuel.
- **`cast_to(S, prove)`** is §6.4's "state, don't steer": `S` proved by
  `prove`, then carried by `cast_from`. `S` is any statement the goal agrees
  with through casts, including one at the source carrier
  (`cast_to(a <= b, assumption())`).
- **`mono` consumes it**: where its split and the cast moves stop, a given
  term or local whose statement agrees with the goal through casts closes
  it (`cast_from` without lifting; orders between images are already
  `le_law`'s). So `h: a.rat() + b.rat() * c.rat() <= x` closes
  `(a + b * c).rat() <= x`, which slice 1 could not.
- **A disagreement is not diagnosed yet**: `cast_from` reports that the
  two differ, not the first subterm where they do (§6.4 asks for that).

Next ([[cast-carrier-reader]]): `ring`, `linarith` and `omega` reading
through the same normal form, the located diagnostic, `0`/`1`/subtraction,
and `Nat → Int`; `↑` and `cast<B>` after (§7 step 3).
