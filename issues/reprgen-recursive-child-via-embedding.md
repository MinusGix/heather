---
title: "reprgen: transfer arms that use the recursive child, through the embedding"
status: open
labels: [compiler,datarepr,design]
area: heather-in-heather
created: 2026-10-28
updated: 2026-10-28
---

`reprgen` declines a structural arm that uses its recursive child anywhere
except as a self-call's argument: `pred` (`Succ(k) => k`), `tail_of`
(`Cons(h, t) => t`), `uses_child` (`Cons(h, t) => length(t)`). The reason,
recorded at the decline in `crates/elab/src/reprgen.rs` and in
`docs/native/datarepr-design.md` §3.3's as-landed notes, is that the arm's algebra
is spelled once and typed twice. The child is at the carrier in the fold and
at `S` in the anchor law, and no single spelling is well-typed under both.

`docs/surveys/proof-repair-algebra-survey.md` §6 takes the way through from
Plante et al.'s Proposition 3.15 remark: an occurrence of the source type in
the defining data is a further use of the repair map. Here the repair map is
the embedding `emb : S → R`, the spec recursor over the images.

## The rule

In the spec-side algebra, a recursive child `k` used outside a self-call is
spelled `emb(k)`. The anchor law's repr-side step is `s1(abs(a0), b0)`, so
on the carrier the same position reads `emb(abs(a0))`. Each such site adds
one law to the certificate:

- in the `abs` walk, `emb_abs` (`abs(emb(k)) = k`);
- where `inv` is owed, at a repr-typed result or a callee argument,
  `emb_inv` (`inv(emb(k))`);
- for a site handed to a resolved callee, that callee's `refines` at
  `emb(k)`, closed by `emb_abs`.

No new `Repr` field is needed. The defaulted fold already generates
`N_emb`, `N_emb_abs` and `N_emb_inv`. A repr with a written fold either
names its embedding, or the embedding is always generated, since v1 images
are total. Choosing between the two is part of this round.

## Acceptance

- `pred`, `tail_of` and `uses_child` transfer at the naive repr, at `BinMin`
  and at `BinC`, with `refines` and, at a repr-typed result, `refines_inv`.
- `UnC` (fold not through `abs`) is among the fixtures, so the transport
  direction stays observable (design §3.3 as-landed note 5).
- Negative controls per `docs/testing-generated-terms.md`:
  - the raw-child emission is refused (the probe below has one);
  - a mutated `emb_abs` site is refused;
  - an arm that uses the child *and* recurses on it still transfers.
- The decline message for the shapes this does not cover stays named. The
  scrutinee itself and non-structural recursion are unchanged.

## Hand-run (2026-10-28, master `0db0151`)

Run with `heather check --expectations` against the `BIN_CANON` fixture
(`crates/elab/tests/support/mod.rs`: `bin_base!()` plus the `BinC`
declaration). Every declaration checks. The negative control is refused for
the typed-twice reason.

```heather
fn pred(n: Nat) -> Nat { match n { Zero => Zero, Succ(k) => k } }
fn bump(n: Nat) -> Nat { match n { Zero => Zero, Succ(k) => Succ(Succ(k)) } }

// The child crosses as `emb(abs(a0))`: the spec-side algebra holds `emb(k)`,
// and the anchor law's `s1(abs(a0), b0)` is that arm at the carrier.
fn pred_derived(r: Bin) -> Bin {
    bin_fold(Bin, BNil, λ a0 b0 => bin_of_nat(bin_abs(a0)), r)
}
fn bump_derived(r: Bin) -> Bin {
    bin_fold(Bin, BNil, λ a0 b0 => binc(binc(bin_of_nat(bin_abs(a0)))), r)
}

theorem pred_abs_alg(x: Nat):
    bin_abs(nat_rec_(Bin, BNil, λ k b => bin_of_nat(k), x)) = pred(x)
{ match x { Zero => refl, Succ(k) => bin_roundtrip(k) } }

theorem bump_abs_alg(x: Nat):
    bin_abs(nat_rec_(Bin, BNil, λ k b => binc(binc(bin_of_nat(k))), x)) = bump(x)
{
    match x {
        Zero => refl,
        Succ(k) => trans(bin_succ_abs(binc(bin_of_nat(k))),
            Nat::cong_succ(trans(bin_succ_abs(bin_of_nat(k)), Nat::cong_succ(bin_roundtrip(k))))),
    }
}

theorem pred_refines(r: Bin, h: bin_canon(r)): bin_abs(pred_derived(r)) = pred(bin_abs(r)) {
    trans(cong_bin_abs(bin_fold_law_canon(Bin, BNil, λ k b => bin_of_nat(k), r, h)),
          pred_abs_alg(bin_abs(r)))
}

theorem bump_refines(r: Bin, h: bin_canon(r)): bin_abs(bump_derived(r)) = bump(bin_abs(r)) {
    trans(cong_bin_abs(bin_fold_law_canon(Bin, BNil, λ k b => binc(binc(bin_of_nat(k))), r, h)),
          bump_abs_alg(bin_abs(r)))
}

// `inv` of the result: the embedding is canonical by the round trip, and the
// images preserve canonicity by their closure law.
theorem emb_canon(k: Nat): bin_canon(bin_of_nat(k)) {
    j(bin_roundtrip(k), λ y q => bin_of_nat(bin_abs(bin_of_nat(k))) = bin_of_nat(y), refl)
}

theorem pred_inv_alg(x: Nat): bin_canon(nat_rec_(Bin, BNil, λ k b => bin_of_nat(k), x)) {
    match x { Zero => refl, Succ(k) => emb_canon(k) }
}

theorem pred_refines_inv(r: Bin, h: bin_canon(r)): bin_canon(pred_derived(r)) {
    j(sym(bin_fold_law_canon(Bin, BNil, λ k b => bin_of_nat(k), r, h)),
      λ y q => bin_canon(y), pred_inv_alg(bin_abs(r)))
}

// …and it computes: pred of three (B1(B1(BNil))) is two.
theorem pred_at_three(): bin_abs(pred_derived(B1(B1(BNil)))) = Succ(Succ(Zero)) { refl }

// Negative control: the arm WITHOUT the embedding — the child handed back at
// the carrier — is what reprgen declines today, and its refines does not check.
fn pred_raw(r: Bin) -> Bin { bin_fold(Bin, BNil, λ a0 b0 => a0, r) }
// expect-error: this has type `Nat`, but `Bin` is expected here
theorem pred_raw_refines(r: Bin, h: bin_canon(r)): bin_abs(pred_raw(r)) = pred(bin_abs(r)) {
    trans(cong_bin_abs(bin_fold_law_canon(Bin, BNil, λ k b => k, r, h)),
          pred_abs_alg(bin_abs(r)))
}
```

## What it assumes from elsewhere

- **[[datarepr-separation]]** owns the repr model. Assumed here: only that
  v1 images are total, so the embedding exists.
- **[[repr-fold-via-abs-default]]** generated `N_emb`/`N_emb_abs`/`N_emb_inv`.
  Assumed here: only that they exist, under those names, at a defaulted fold.

## Log

- 2026-11-05: gardener: cites a file it shares with [[datatype-container-algebras]] (`docs/surveys/proof-repair-algebra-survey.md`); [[parallel-checking-and-caching]] (`crates/elab/tests/support/mod.rs`); [[suite-tests-reelaborate-library-modules]] (`crates/elab/tests/support/mod.rs`).
