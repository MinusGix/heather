# What is awkward in the math and tactics libraries, and what would fix it

Minus asked (2026-11-08) for a look over the mathematical and tactics parts
of the standard library for things that are fundamentally awkward and would
benefit from better language features, theorem and function APIs, or
tactics, linked to existing issues so the tracker's priorities can be read
against them. This note answers from master at `5df757c`: lib/std/algebra,
analysis, num (with float), tactic, relation and core, about 47,000 lines.

It is a survey. It files issues and changes no library or compiler code.

## Method

Three passes. First, counting idioms across the libraries (the numbers below
are `grep -o` counts over lib/std/algebra, analysis, num and tactic unless
a line says otherwise). Second, reading the files where those idioms
concentrate: real_fn, sequence, real_log, float_real, round_real, eft,
creal, ordered_field, linarith, ring, mono. Third, a small probe for every
suspected gap, checked with `heather check --cache` on the release binary,
so each claim that something "cannot be written" was tried. Probes are
quoted in the issues they support.

The prior reviews this builds on: `notes/rat-style-review.md` (October;
most of its items landed, which is why `Rat` and `CReal` now read well),
docs/elaborator/elaborator-principles-survey.md (the unifier's rules), and
docs/proof-patterns.md (rules for writing proofs today).

## 0. Summary

The concrete carriers read well now. `Rat` and `CReal` have numerals,
`-`, `/` with searched apartness, implicit endpoints, dot calls and calc.
The awkwardness is concentrated in three places:

1. **Generic code**: anything stated once over a class
   (`section<K: OrderedField(…)>`). It has no numerals and no minus, and
   its theorems cannot infer their points. So it is written through the
   dictionary (`K.multiplicative.unit`, `K.inv(e)`), with every endpoint
   restated, and the concrete carriers keep a second copy of the class
   theory to avoid calling it. This is the biggest finding, because the
   project's direction (prove once over the class, read at `Rat` and
   `CReal`) is exactly what it penalises.
2. **Equality up to `≈`**: about 3,100 occurrences of
   `same_sym`/`same_trans`/`rel_trans`/`…_respects`. The tools that would
   absorb them (`grind`, setoid `rewrite`) reach `≈` only partly.
3. **Automation that cannot be used where it is most needed**: `omega`
   cannot be used in nat/int, `linarith` cannot be used in ordered_field,
   and `omega` does not read `max`/`min`. Casts are pushed by hand because
   `linarith` does not read them.

The rest is smaller: destructuring, threshold and ε bookkeeping, symmetric
case splits, tactic lemma tables as strings, and features that landed but
were not swept back through older files.

| § | Finding | Kind | Size in the library | Issues |
|---|---|---|---|---|
| 1 | Generic theorems cannot infer their points | language | 1,571 class-theorem calls with explicit points; 17+ dummy points; ~65 duplicated theorems per carrier | **new** [generic-theorem-implicit-points](../../issues/generic-theorem-implicit-points.md); [elab-unifier-completeness](../../issues/elab-unifier-completeness.md), [method-call-on-constrained-carrier](../../issues/method-call-on-constrained-carrier.md), [type-owned-namespaces](../../issues/type-owned-namespaces.md) |
| 2 | No `0`, `1`, `-x`, `x - y` at a class carrier | library + language | `.multiplicative.unit` 656, `K.unit` 353, `K.inv(` 489 | **new** [class-carrier-arithmetic-surface](../../issues/class-carrier-arithmetic-surface.md); [class-carrier-division-gaps](../../issues/class-carrier-division-gaps.md), [infix-subtraction-notation](../../issues/infix-subtraction-notation.md) |
| 3 | `≈` is plumbed by hand | library + tactic | ~3,100 setoid-plumbing occurrences | **new** [carrier-respects-as-rewrite-evidence](../../issues/carrier-respects-as-rewrite-evidence.md); [egraph-setoid-path-algebra](../../issues/egraph-setoid-path-algebra.md), [setoid-surface-kernel-cost](../../issues/setoid-surface-kernel-cost.md), [one-sided-respects-sweep](../../issues/one-sided-respects-sweep.md) |
| 4 | Theories are proved without the tactics that import them | library layering | nat ~2.5k, int ~2k, ordered_field ~1.2k lines; misplaced lemmas | **new** [theory-modules-after-their-tactics](../../issues/theory-modules-after-their-tactics.md) |
| 5 | Casts are pushed by hand | tactic | `ofRat_*` lemma uses 376, `of_int`/`of_nat` 126, `hom.map_*` 56 | [cast-carrier-reader](../../issues/cast-carrier-reader.md), [cast-from-at-class-carrier](../../issues/cast-from-at-class-carrier.md) |
| 6 | A section's symbols capture other carriers | language | 66 prefix-spelled `Rat::` operations in two float files; 18-index hom headers | **new** [section-symbols-capture-other-carriers](../../issues/section-symbols-capture-other-carriers.md); [class-default-operators](../../issues/class-default-operators.md) |
| 7 | Evidence is taken apart by counting | language | 59 `.x.y.z` chains, 60 nested `Exists` matches, 904 `.witness`/`.proof` | [conjunction-facts-read-by-counting](../../issues/conjunction-facts-read-by-counting.md), [nested-exists-match-cost](../../issues/nested-exists-match-cost.md) |
| 8 | Thresholds and ε-splitting by hand | tactic + library | `le_max_*` 75, `half`-family 135, `below_both`/`shrink` 34 | **new** [omega-reads-min-max](../../issues/omega-reads-min-max.md); [asymptotic-relations](../../issues/asymptotic-relations.md) |
| 9 | Symmetric case splits proved twice | library | ~245 order case splits, some mirrored | **new** [wlog-symmetric-cases](../../issues/wlog-symmetric-cases.md) |
| 10 | Tactic lemma tables are strings in tactic source | tactic design | mono 99 names, cast 17, norm_num 16, interval 13 | [automation-lemma-registries](../../issues/automation-lemma-registries.md) |
| 11 | Landed features not swept back | lint | `j(` with a motive 340, `let k: T = tac; k` ~80, … | [lint-roadmap](../../issues/lint-roadmap.md), the sweep issues |
| 12 | Long import lists | modules | 19–21 imports per analysis/float file | [feature-implicit-module-dependencies](../../issues/feature-implicit-module-dependencies.md), [std-prelude-facade](../../issues/std-prelude-facade.md) |

§13 gives the recommended order of work, which is not the table's order:
some small items are cheap enough to go first.

## 1. Generic theorems cannot infer their points

A theorem over `K: OrderedField(≈, <, <=, +, *)` with implicit endpoints is
refused at its call, even inside the same section:

```heather
theorem p_lt_tr({x, y, z: K}, a: x < y, b: y < z): x <= z { … }
theorem p_use(a, b, c: K, h1: a < b, h2: b < c): a <= c { p_lt_tr(h1, h2) }
// cannot infer the implicit arguments needed for `OrderedField<K>(≈, <, <=, +, *)`
```

A theorem with no point of its own fails the same way against an expected
type that mentions only dictionary fields. docs/library/constructive-ordered-field-design.md
records the cause (`?lt(?x, ?y)` is not solvable before the carrier is
known) and the decision that follows from it: generic theorems take explicit
points. What that decision costs:

- **Restated endpoints.** lib/std has 1,571 calls to a class theorem
  (`StrictOrder::`, `PseudoOrder::`, `OrderedAddMonoid::`, …,
  `OrderedField::`), each with its points written out. float_real.hthr's
  `affine_up` calls `PseudoOrder::le_trans(map(R), A * map(lo) + map(b), A *
  x + map(b), …)`, where the two hypotheses already fix all three points.
- **Dummy points.** These take an argument only so a caller's carrier pins
  `A`, and their comments say so: `OrderedField::two_pos(x: K)`,
  `of_nat_nonneg(x: K, n)`, `Bisection::quarter(x: K)`,
  `OrderedAddGroup::neg_zero(x: A)`, `lin_one_pos(x: A)`,
  `RingExpr::of_nat_add(xs: List<A>, …)`.
- **A second copy of the theory at each carrier.** 65 `CReal::` and 68
  `Rat::` theorem names coincide with a generic class theorem's
  (`add_le_mono`, `le_of_same_l`, `mul_pos`, `neg_lt`, `npow_add`, …), and
  `Rat`∩`CReal` share 101. Most of these are re-proved, not read off the
  instance. For example, `CReal::add_le_mono` is the same two-step proof as
  `LocatedAddMonoid::add_le_mono`. Each copy exists because it can be
  written `x.add_le_mono_r(…)` with implicit points. `mono` then has to list
  the carrier copies as well as the class laws.

This is the most fundamental item. The project's mathematics direction is
"state it once over the class, read it at every carrier" (real_fn,
sequence, closed_interval, field_division, ordered_sign all follow it), and
this is the tax on every line of that. Fixing it would let the carrier
copies go, which is also what [type-owned-namespaces](../../issues/type-owned-namespaces.md) would need before
`x.add_le_mono(…)` could reach the class theorem through the instance.

The issue proposes two routes. One is to retry the index-filling rungs
after the explicit arguments are unified, instead of refusing at the first
attempt. The other is a ranked first-order solution of `?lt(?x, ?y) ≟
lt(a, b)` when the head is a section local or a dictionary field, which is
P2 of the elaborator survey. The cause is the design note's statement; the
issue asks the round to re-trace it in `apply_implicit` first.

## 2. A class carrier has no numerals and no minus

Inside a section over `OrderedField`, `x⁻¹` and `a / b` work (designations
at the class since 2026-11-06), but `0`, `1`, `-x` and `x - y` do not (three
probes in the issue). So `0 < e → 0 < e/2` is written

```heather
theorem OrderedField::half_pos(e: K, he: K.unit < e): K.unit < OrderedField::half(e)
```

with `half(e)` defined as `e * K.recip(K.multiplicative.unit +
K.multiplicative.unit, Inr(OrderedField::two_pos(e)))`. Over the
libraries, `.multiplicative.unit` appears 656 times, `K.unit` 353 and
`K.inv(` 489. This is the most visible difference between a generic
analysis file and the same mathematics at `CReal` (compare real_fn.hthr
with real_log.hthr).

Most of the fix is cheap. Prefix and infix `-` are two designation lines at
the class, beside the two in field_division.hthr. Numerals need the
carrier-directed numeral route to fall back to the integers the dictionary
in scope names. `linarith` at a class carrier also has to read `e / 2`:
today it refuses `e / (1 + 1) < e` from `0 < e` at `K`, and proves the same
statement at `Rat`. [class-carrier-division-gaps](../../issues/class-carrier-division-gaps.md) keeps its other two
bullets.

## 3. Equality up to `≈` is plumbed by hand

`same_sym`, `same_trans`, `rel_sym`, `rel_trans`, `same_refl`, `rel_refl`
and `…_respects` together appear about 3,100 times. The densest files are
creal (236 lines), rat (191), float/round (175), ordered_field (127) and
real_log (101). real_log.hthr's `half_r_pow` ends in
`CReal::same_trans(k, CReal::same_trans(m2, CReal::same_trans(CReal::same_sym(…), …)))`.

What exists, and why it does not absorb this:

- **calc over `≈`** exists and is used (398 calc blocks), but calc ≈ and
  `rel_cong` cost far more kernel steps than the terms they stand for
  ([setoid-surface-kernel-cost](../../issues/setoid-surface-kernel-cost.md)). That is a reason to avoid them in hot
  files.
- **Setoid `rewrite`** crosses an operation only with registered evidence,
  and at `Rat`/`CReal` only `+` and `*` have it. The other 35 respects
  theorems (`abs`, `neg`, `sub`, `div`, `npow`, `exp`, `log`, `sqrt`, …)
  are plain theorems. Rewriting `a ≈ b` under `abs` leaves
  `?compatibility : PreservesRelation(Same, Same, abs)` open. Fixing that is
  mechanical: [carrier-respects-as-rewrite-evidence](../../issues/carrier-respects-as-rewrite-evidence.md) asks for it, plus a
  form that makes a respects theorem register itself.
- **`grind`** reads `a ≈ b` at `Rat` by unfolding it to its
  cross-multiplication equation, so it cannot close `|a| + 1 ≈ |c| + 1`
  from `a ≈ b ≈ c` (probed). A setoid-aware e-graph is
  [egraph-setoid-path-algebra](../../issues/egraph-setoid-path-algebra.md). That is the expensive half and the one
  that would remove most of the chains.

Also seen in that probe: the unsolved-goal display prints `≈` hypotheses at
`Rat` as their unfolding (`h1 : a.num * int(b.den) = b.num * int(a.den)`).
It is a display gap of the kind [diagnostic-operator-resugaring](../../issues/diagnostic-operator-resugaring.md) closed
for operators, noted here and not filed separately.

## 4. Theories are proved without the tactics that import them

`omega` imports nat and int, `linarith` imports ordered_field, and `ring`
imports semiring. So the ~2,500 lines of nat.hthr, the ~2,000 of int.hthr
and the ~1,200 of ordered_field.hthr are proved without the tactics every
client uses on the same facts. The hand chains in §1 and §3 are
concentrated in exactly these files.

When a fact is wanted with automation, it leaves its home. real_fn.hthr
says of its opening lemmas: "facts about an ordered field [that] would live
in `ordered_field.hthr`, but their proofs are `linarith` and `nlinarith`
calls and the `linarith` kit imports `ordered_field`; they live here …
until that edge is cut". That works against the project rule that a type's
facts live in its own file.

The fix is a layering change that the module system already supports. Split
each module into a core (what the tactic's certificate cites) and a theory
that imports the tactic, and `export` the core so `import nat;` means what
it did. parser.hthr already re-exports its parts this way. Cost to watch:
small clients of `nat` would replay `omega`'s closure, which is why the issue
asks for a `perf ab --source-patch` measurement before landing.
[theory-modules-after-their-tactics](../../issues/theory-modules-after-their-tactics.md).

## 5. Casts are pushed by hand

`CReal::ofRat_add`, `ofRat_mul`, `ofRat_le`, `ofRat_lt`, `ofRat_respects`
and kin are used 376 times. `of_int`/`of_nat` push lemmas account for 126
more, and homomorphism laws (`hom.map_add`, `map_le`, …) for 56. The shape
is always the same: a fact proved at `Rat` (often by `omega`) is lifted to
`CReal` and joined with a chain of `same_trans`:

```heather
let hf0: (Rat::inv_succ(1) + Rat::inv_succ(1) ≈ 1) = omega;
CReal::same_trans(CReal::same_sym(CReal::ofRat_add(Rat::inv_succ(1), Rat::inv_succ(1))), CReal::ofRat_respects(hf0))
```

`linarith` at `CReal` refuses a `Rat` fact about the cast's arguments
(probed: `h: a <= b` for a goal over `CReal::ofRat(a + b)`). The tracker
already owns the fix: [cast-carrier-reader](../../issues/cast-carrier-reader.md) reads casts once for every
arithmetic tactic, and [cast-from-at-class-carrier](../../issues/cast-from-at-class-carrier.md) covers the class
carrier, which float_real/round_real's `map` needs. This survey's
contribution is the count, which ranks it fifth. It also partly overlaps
§2: `CReal::half_r()` (`CReal::ofRat(Rat::inv_succ(1))`) could be `1 / 2`
at `CReal` today.

## 6. A section's operator symbols capture every carrier

A constraint binder's symbols resolve at rung 1, before any type is looked
at (docs/language/classes/operators-onto-classes-design.md §4). So inside a section over `K`,
`a + 0 <= b` at `Rat` is refused, with a message about `Numeral<the expected
type>`. Proofs that relate `Rat` to `K` through a homomorphism therefore
spell the `Rat` side by name:

```heather
theorem Rat::affine_up(x: K, lo, R, a, b: Rat, a_nn: Rat::Le(0, a), l: map(lo) <= x,
    at: Rat::Le(R, Rat::add(Rat::mul(a, lo), b))): map(R) <= map(a) * x + map(b)
```

The section header restates all eighteen indices of `OrderedRingHom<Rat,
K>`. The proposal is to make rung 1 apply only when the operand is at the
binder's carrier (or its type is unknown) and fall to the designation at the
operand's own head otherwise.
[section-symbols-capture-other-carriers](../../issues/section-symbols-capture-other-carriers.md).

## 7. Evidence is taken apart by counting

`match h { ⟨n, ⟨a, b⟩⟩ => … }` works, but `let ⟨n, a, b⟩ = h;` is a parse
error (probed). So an existential's parts are read as `.witness`/`.proof`
(904 reads), conjunctions as `.right.right.left` (59 chains of three or
more), and two existentials as nested matches (60; 36 in creal.hthr).
float_real's `err_in_nonneg` has `let pl = w.right.right.left; let ph =
w.right.right.right;` and then `pl.right.left`, `pl.right.right`. The
destructuring `let` and flat right-nested patterns are already the
language direction of [conjunction-facts-read-by-counting](../../issues/conjunction-facts-read-by-counting.md). This survey
adds the math-library counts and moves it up: it is small, self-contained
language work with a reader on every page. [nested-exists-match-cost](../../issues/nested-exists-match-cost.md)
owns the cost side.

## 8. Thresholds and ε-splitting by hand

Two recurring bookkeeping shapes in analysis:

- **"Past both thresholds."** `let n = p.witness.max(q.witness)`, then
  `p.witness.le_max_l(q.witness)`, `le_trans` to the later index: 75
  `le_max_*` calls in analysis and creal, 80 max/min lemma calls in
  lib/std. `omega` cannot do it because it reads `max` as an atom (probed:
  it gets stuck on `a <= c → b <= c → a.max(b) <= c` with a model that
  sets `max(a, b) = 1`). Lean's `omega` adds the two defining facts per
  `min`/`max` atom, and so can ours: [omega-reads-min-max](../../issues/omega-reads-min-max.md). It is a small,
  sharp tactic fix. *Landed 2026-11-09* as a case split per read
  (omega design §20); the library sweep is
  [omega-max-min-sweep](../../issues/omega-max-min-sweep.md).
- **"ε/2 each."** `OrderedField::half`, `half_pos` and `half_add` are
  threaded through 135 uses, and `below_both`/`shrink` through 34. Part of
  this goes with §2 (`e / 2` and `linarith` reading it). The rest is the
  missing `Eventually` layer: [asymptotic-relations](../../issues/asymptotic-relations.md) owns `Eventually` and
  `Tendsto` with the threshold as data, scheduled behind the Landau
  relations. This survey suggests pulling the `Eventually` slice with its
  `and`/`mono` lemmas forward, since sequence.hthr and real_fn_limit.hthr
  would use it now.

The constructive choices behind these shapes are deliberate and not
awkwardness: no `abs`, no `min` and no sign test at a generic carrier,
`AbsLe` as a predicate, and moduli as data (real_fn.hthr's header). What
§8 asks for is bookkeeping, not decisions.

## 9. Symmetric case splits proved twice

About 245 order case splits (`le_total`, `lt_total`, `le_dec`, `lt_dec`,
`trichotomy`) appear in the libraries. Where the goal is symmetric, both
arms are written. `CReal::atanh_regular` has two eleven-line arms with `m`
and `n` exchanged. `Rat::err_in_nonneg` and `Rat::err_in_nonpos` are twin
theorems. A `wlog_le` lemma per totally ordered carrier (and one through
negation for signs) removes the copy without any language work. A `wlog`
tactic that infers the predicate is the follow-up.
[wlog-symmetric-cases](../../issues/wlog-symmetric-cases.md).

## 10. Tactic lemma tables are strings in tactic source

`mono` names 99 lemmas by string (`"OrderedAddMonoid::add_le_mono_l"`),
`cast` 17, `norm_num` 16 and `interval` 13. `ring` and `linarith` read
carriers through Rust (`crates/elab/src/linarith.rs`) plus a fixed lemma
kit. A new carrier or operation gets automation by editing the tactic.
`evidence theorem` already shows the alternative: a declaration that
registers itself with a search. [automation-lemma-registries](../../issues/automation-lemma-registries.md) owns the
design. §3's respects registration is the first concrete customer, and
`mono` laws the second.

The tactics' own code has a smaller version of §11: 28 functions in
lib/std/tactic recurse by hand over a list in `Tac`
(`mono_class_laws`, `mono_class_signs`, …) where `List::traverse` and
`List::for_m` exist and `Tac` has `Bind`/`Pointed` instances. This is
noted, not filed. Check the tier-2 `Tac` cost
([tier2-constructor-value-cost](../../issues/tier2-constructor-value-cost.md)) before sweeping it.

## 11. Features that landed but were not swept back

Several of the idioms above are older than the feature that removes them:

| Idiom | Count | Replaced by |
|---|---|---|
| `j(e, λ v _ => …, h)` transport with a written motive | 340 | `rewrite(e, in := h)` ([equation-rewrite-in-goal](../../issues/equation-rewrite-in-goal.md), closed) |
| `let k: (T) = linarith(…); k` / `ring` at a tail whose type is `T` | ~80 | the bare tail call (probed: checks) |
| `.left`/`.right` split into ascribed lets before `linarith` | common in sequence.hthr | `linarith(h)` reads `∧` and `AbsLe` (probed) |
| `le_respects(…, same_refl(…), …)` for a one-sided step | ~120 | [one-sided-respects-sweep](../../issues/one-sided-respects-sweep.md) |
| `K.zero_lt_one` passed to `linarith` for `+ 1` goals | 54 sites mention it | not needed (probed at `K`) |
| `CReal::ofRat(Rat::inv_succ(1))` for ½ | — | `1 / 2` at `CReal` |

Sweeps one at a time do not keep up, and the tracker has several open
([one-sided-respects-sweep](../../issues/one-sided-respects-sweep.md), [grind-library-sweep](../../issues/grind-library-sweep.md),
[uncurried-recursions-library-sweep](../../issues/uncurried-recursions-library-sweep.md), [pos-sugar-library-adoption](../../issues/pos-sugar-library-adoption.md)).
The better tool is the lint tier: each row is a mechanical rewrite that
[lint-mechanical-fix-mode](../../issues/lint-mechanical-fix-mode.md) could apply and [lint-unnecessary-explicit-elaboration](../../issues/lint-unnecessary-explicit-elaboration.md)
partly covers. The recommendation is that the round landing a feature also
lands its lint, rather than filing a sweep.

## 12. Long import lists

Analysis and float modules import 19–21 modules each, and real_log.hthr
imports 27. `by` asks for `import tactic` by name. This belongs to
[feature-implicit-module-dependencies](../../issues/feature-implicit-module-dependencies.md) and [std-prelude-facade](../../issues/std-prelude-facade.md). It is
ranked last because it is boilerplate at the top of a file, not friction
inside proofs.

## 13. Order of work

Ranked by value for cost, not by size:

1. **§2's library half** (designations for `-` at the class) and **§3's
   respects registration**. Mechanical library rounds that each remove
   hundreds of occurrences from new code.
2. **[omega-reads-min-max](../../issues/omega-reads-min-max.md)**. Small, contained in the reifier, with a
   clear customer.
3. **§7's destructuring `let`**. Small language work, a reader on every
   page.
4. **[generic-theorem-implicit-points](../../issues/generic-theorem-implicit-points.md)**. The largest payoff and the
   only item here that needs real elaborator design. After it, a round can
   move one generic file to implicit points and start deleting carrier
   copies (§1).
5. **§2's numerals at a class carrier**, with `linarith` reading `/ 2`.
   After that the generic analysis files can be restated.
6. **[theory-modules-after-their-tactics](../../issues/theory-modules-after-their-tactics.md)**, measured first.
7. **[cast-carrier-reader](../../issues/cast-carrier-reader.md)**, **[section-symbols-capture-other-carriers](../../issues/section-symbols-capture-other-carriers.md)**,
   the `Eventually` slice of [asymptotic-relations](../../issues/asymptotic-relations.md), and
   [wlog-symmetric-cases](../../issues/wlog-symmetric-cases.md), in any order.
8. The expensive structural pieces: a setoid-aware `grind`
   ([egraph-setoid-path-algebra](../../issues/egraph-setoid-path-algebra.md)) and lemma registries
   ([automation-lemma-registries](../../issues/automation-lemma-registries.md)).

Item 4 is the one to schedule deliberately. The rest can be picked up as
fillers. Since §1 and §2 both change how generic statements are written,
restating the analysis files should wait until both have landed, so they
are rewritten once.

## Issues filed

- [generic-theorem-implicit-points](../../issues/generic-theorem-implicit-points.md) (language, math-classes)
- [class-carrier-arithmetic-surface](../../issues/class-carrier-arithmetic-surface.md) (mathematics, math-classes)
- [carrier-respects-as-rewrite-evidence](../../issues/carrier-respects-as-rewrite-evidence.md) (mathematics, tac-general)
- [theory-modules-after-their-tactics](../../issues/theory-modules-after-their-tactics.md) (mathematics)
- [section-symbols-capture-other-carriers](../../issues/section-symbols-capture-other-carriers.md) (language, math-classes)
- [omega-reads-min-max](../../issues/omega-reads-min-max.md) (tactics, tac-arith)
- [wlog-symmetric-cases](../../issues/wlog-symmetric-cases.md) (mathematics)

Log entries with this survey's probes and counts went to
[class-carrier-division-gaps](../../issues/class-carrier-division-gaps.md), [elab-unifier-completeness](../../issues/elab-unifier-completeness.md),
[egraph-setoid-path-algebra](../../issues/egraph-setoid-path-algebra.md), [feature-implicit-module-dependencies](../../issues/feature-implicit-module-dependencies.md),
[asymptotic-relations](../../issues/asymptotic-relations.md), [conjunction-facts-read-by-counting](../../issues/conjunction-facts-read-by-counting.md),
[class-default-operators](../../issues/class-default-operators.md), [cutsat-first-class-relations](../../issues/cutsat-first-class-relations.md) and
[std-api-waves](../../issues/std-api-waves.md).
