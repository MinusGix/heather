# Interval proofs: the repeated shapes, and what removes each

Round of 2026-10-30 (`issues/interval-proof-shapes.md`), on
`lib/std/num/float/interval.hthr`. The question was which APIs or tactic
automation would make the file's proofs read as the arguments they are,
rather than as the plumbing around them. The file's proofs were made of
six shapes; this note names each, what the round did about it, and what is
left with its owner.

## 1. Moving one side of `≤` along `≈`

The largest share of the old `le_respects` calls had the shape "the bound
is a dyadic image, the inequality was proved about its rational value":

```heather
// before
let low: ((a + c).rat() <= x + y) = Rat::le_respects(Rat::same_sym(a.rat_add(c)), (x + y).same_refl(), Rat::add_le_mono(hx.left, hy.left));
// one side, no reflexivity on the other, no `same_sym` to undo the law's direction
Rat::le_of_same_of_le(a.rat_add(c), Rat::add_le_mono(hx.left, hy.left))
```

`Rat::le_of_same_of_le` and `Rat::le_of_le_of_same` (`rat.hthr`) are the
`calc` step `≈ … <=` as one call. About 120 one-sided `le_respects` calls
remain elsewhere in `lib/` ([[one-sided-respects-sweep]]).

## 2. A box's two bounds, then rounded outward

Every operation proved the same four-line tail: a lower and an upper bound
through image laws, then a `le_trans` with `down_le` and one with `le_up`,
each with its implicits named because `Dyadic::Le` facts do not fill `Rat`
implicits. Two lemmas own that now:

```heather
theorem Interval::bnd_has_of({lo, hi: Dyadic}, {L, H, x: Rat}, el: lo.rat() ≈ L, eh: hi.rat() ≈ H, hl: L <= x, hh: x <= H): Bnd(lo, hi).Has(x)
theorem Interval::round_out_has({lo, hi: Dyadic}, p: Nat, {x: Rat}, h: Bnd(lo, hi).Has(x)): Bnd(lo.down(p), hi.up(p)).Has(x)
```

so a sum's containment is the sentence it is:

```heather
Interval::round_out_has(p, Interval::bnd_has_of(a.rat_add(c), b.rat_add(d), Rat::add_le_mono(hx.left, hy.left), Rat::add_le_mono(hx.right, hy.right)))
```

`add_bnd_has` (a four-line body → one line), `mul_pos_has` (six → four), `neg_has`'s arm and
`mul_box_has`'s tail use them. What the caller still names is the image law
(`rat_add`); a cast-pushing step would infer it and let `mono` prove the
bound outright ([[push-cast-through-embeddings]]).

## 3. Match motives that restate the function

`mul_bnd_has`, `recip_bnd_has`, `pow_step_has` and `pow_sq_has` wrote
motives that copied the function body they were splitting
(`match a.nonneg_dec() as λ s => (match s { …the body of mul_bnd… }).Has(x * y)`).
Motive synthesis has found these since `goal-motive-by-scrutinee-abstraction`
(it reduces the goal and abstracts what it is stuck on), so they are plain
`match a.nonneg_dec() { … }` now. Nothing new was needed; the written
motives predated or ignored the synthesis.

## 4. The convoy over `Whole`

`has_respects`, `neg_has`, `add_has`, `mul_has`, `recip_has`, `lt_of_below`
and `le_of_below_eq` each lifted a box lemma to intervals with

```heather
match I as λ K => K.Has(x) → K.add(J, p).Has(x + y) { Bnd(a, b) => λ kx => …, Whole => λ _ => trivial }(hx)
```

The motive was there only to refine the hypothesis `hx` along with the goal.
That is the elaborator's job now
([[elab-match-refines-hypothesis-kernel-rejects]], closed 2026-10-30: a
`match` on a local generalizes the hypotheses that mention it), so each is

```heather
match I { Bnd(a, b) => match J { Bnd(c, d) => Interval::add_bnd_has(a, b, c, d, p, hx, hy), Whole => trivial }, Whole => trivial }
```

7 sites here and 9 in `creal_interval.hthr`. What remains is a convoy on a
computed scrutinee (`Interval::of_rat(lo, p)` in `span_has_real`,
`Dyadic::lt_bool(0, lo)` in `apart_of_excludes`), which refines no
hypothesis because it is not a local.

## 5. Two copies of the search

`lt_search`/`le_search` and their soundness theorems differed only in the
verdict (`below`, `below_eq`) and the relation. `IntervalExpr::search` takes
the verdict, `IntervalExpr::of_search` takes the relation and the verdict's
soundness, and the four names the tactic uses are each one call into them. The
soundness proof uses `match e : verdict(…)` and `Bool::is_true_of_eq`
(`bool.hthr`) in place of the hand convoy `as λ v => … = v → …` and
`j(sym(e), λ w _ => w.IsTrue(), trivial)`, which `creal_interval.hthr` also
now spells with the lemma (11 sites).

## 6. A `≈` chain written inside-out

`of_rat_same` was four nested `same_trans`/`same_sym`. It is a `calc` of
four `≈` steps, read top to bottom.

## Smaller facts that were missing

`Rat::mul_le_mono_l_nonpos` (so `between_l` is `between_r`'s proof, not
four commutations of it), `Dyadic::rat_nonneg` beside `rat_pos`,
`Dyadic::neg_pos`, `Dyadic::lt_of_not_le`.

## What is left, ranked

1. ~~[[elab-match-refines-hypothesis-kernel-rejects]]~~ — the convoys
   (§4); closed 2026-10-30.
2. [[interval-containment-once-over-ordered-field]] — `creal_interval.hthr`
   restates 26 of these lemmas at `CReal`; proving them once over an
   ordered field folds half that file into instances, and every shape
   cleanup above would then happen once.
3. [[push-cast-through-embeddings]] — §2's remaining image laws, and the
   step that lets `mono` close containment bounds directly.
4. [[one-sided-respects-sweep]] — mechanical, file by file.

Found on the way: an `And` passed for a match-defined predicate at an
inferred implicit is refused by the kernel with `LevelMismatch`
([[and-at-match-predicate-implicit-level-mismatch]]); fixed 2026-10-31 (the
unifier paired the arguments of two applications with different heads), and
`mul_box_has_in` now passes the pair directly.
