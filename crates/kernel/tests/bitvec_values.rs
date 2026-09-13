//! Native bitvector words: the criterion, the conversion fast path, and the
//! run's one-step view (`docs/native-bitvector-values-design.md`, round 2).
//!
//! A `Vec^l(T; n)` whose element type has exactly two canonical inhabitants
//! with proof-irrelevant payloads is a machine word, and this file is the
//! standing evidence that *reading it as one decides the same relation*. The
//! shape under test is the one the elaborator actually emits for a
//! two-constructor nullary inductive (`docs/inductive-tier0-lowering.md` §3):
//! a sum of `Tag_D`-prefixed field spines, so `False = inl ⟨tag, ⟨⟩⟩` and
//! `True = inr ⟨tag, ⟨⟩⟩` with `tag` a Σ-nest of `Unit`s. `bool_like` below
//! is that shape by construction rather than by import, so the file stays a
//! kernel test with no library in it — §11.2 is the same criterion met by
//! the real `Bool`, which the certificate measures.
//!
//! Coverage, and why each row is here:
//!
//! - the criterion's positive and negative sides, including the element type
//!   whose payload is *not* proof-irrelevant (`Nat + Nat`), which must keep
//!   deciding by η;
//! - widths 0, 1, 2, `WIDTH_CAP - 1`, `WIDTH_CAP`, `WIDTH_CAP + 1` — the
//!   last is the one that cannot fit in one word, and it must still decide;
//! - a difference at every interesting position (first bit, last bit, the
//!   bit just past the cap), since a fast path that compares the wrong bits
//!   is a fast path that accepts the wrong terms;
//! - a **neutral tail**, where only a prefix packs and the residual has to
//!   go back to the ordinary comparison;
//! - non-canonical payloads, which must not pack and must still decide.
//!
//! A wrong answer here is a soundness bug, so every row asserts a verdict in
//! both directions: convertible pairs are accepted, and the corresponding
//! perturbation is refused.

use std::sync::Arc as Rc;

use heather_kernel::conv::{conv_term, ConvError};
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{CtxEntry, GlobalCtx, LocalCtx, LocalVar, Term, Type};
use heather_kernel::typing::check_term;
use heather_kernel::value::BIT_RUN_WIDTH_CAP;

const FUEL: u64 = 4_000_000;

fn rt(t: Term) -> Rc<Term> {
    Rc::new(t)
}

fn rty(t: Type) -> Rc<Type> {
    Rc::new(t)
}

fn nat(n: u64) -> Term {
    let mut t = Term::Zero;
    for _ in 0..n {
        t = Term::Succ(rt(t));
    }
    t
}

fn unit() -> Type {
    Type::Unit { level: Level::Zero }
}

fn triv() -> Term {
    Term::Triv { level: Level::Zero }
}

fn sigma(fst: Type, snd: Type) -> Type {
    Type::Sigma {
        fst_level: Level::Zero,
        snd_level: Level::Zero,
        fst: rty(fst),
        snd: rty(snd),
    }
}

fn pair(fst_ty: Type, snd_ty: Type, fst: Term, snd: Term) -> Term {
    Term::Pair {
        fst_level: Level::Zero,
        snd_level: Level::Zero,
        fst_ty: rty(fst_ty),
        snd_ty: rty(snd_ty),
        fst: rt(fst),
        snd: rt(snd),
    }
}

fn sum(lhs: Type, rhs: Type) -> Type {
    Type::Sum {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        lhs: rty(lhs),
        rhs: rty(rhs),
    }
}

fn inj(right: bool, lhs: Type, rhs: Type, val: Term) -> Term {
    let (lhs, rhs, val) = (rty(lhs), rty(rhs), rt(val));
    if right {
        Term::Inr { lhs_level: Level::Zero, rhs_level: Level::Zero, lhs, rhs, val }
    } else {
        Term::Inl { lhs_level: Level::Zero, rhs_level: Level::Zero, lhs, rhs, val }
    }
}

fn vec(elem: Type, len: Term) -> Type {
    Type::Vec { level: Level::Zero, elem: rty(elem), len: rt(len) }
}

// -------------------------------------------------------------------------
// The element type: one constructor spine of `inductive Bool { False, True }`
// -------------------------------------------------------------------------

/// `Tag_D` as §3.3 of the lowering builds it: the binary digits of a
/// declaration id as a right-nested Σ of `Unit`s. Depth 3 is an ordinary id;
/// the point is that it is *not* `Unit` itself, so the criterion has a nest
/// to walk and the payload check has one to verify.
fn tag() -> Type {
    sigma(unit(), sigma(unit(), unit()))
}

fn tag_value() -> Term {
    pair(unit(), sigma(unit(), unit()), triv(), pair(unit(), unit(), triv(), triv()))
}

/// A nullary constructor's field spine: `Σ(_ : Tag_D). Unit`.
fn arm() -> Type {
    sigma(tag(), unit())
}

fn arm_value() -> Term {
    pair(tag(), unit(), tag_value(), triv())
}

/// The element type under test: exactly two canonical inhabitants, both
/// payloads proof-irrelevant.
fn bool_like() -> Type {
    sum(arm(), arm())
}

fn bit(b: bool) -> Term {
    inj(b, arm(), arm(), arm_value())
}

/// The same bit with a payload that is *not* the canonical inhabitant: the
/// tag nest is replaced by a variable of the same type. Proof-irrelevant, so
/// conversion still accepts it — but it must not pack.
fn opaque_bit(b: bool, var: u32) -> Term {
    inj(b, arm(), arm(), pair(tag(), unit(), Term::Var(LocalVar(var)), triv()))
}

/// A closed `Vec` literal over `bool_like`, LSB first: element `i` is bit
/// `i` of `bits`, and the chain terminates in `⟨⟩` at length `width`.
fn word(width: u32, bits: u128) -> Term {
    word_over(width, bits, triv(), nat(0))
}

/// The same over an arbitrary tail of length `tail_len`.
fn word_over(width: u32, bits: u128, tail: Term, tail_len: Term) -> Term {
    let mut out = tail;
    let mut len = tail_len;
    for i in (0..width).rev() {
        let rest_ty = vec(bool_like(), len.clone());
        out = pair(bool_like(), rest_ty, bit(bits >> i & 1 == 1), out);
        len = Term::Succ(rt(len));
    }
    out
}

fn word_ty(width: u32) -> Type {
    vec(bool_like(), nat(u64::from(width)))
}

// -------------------------------------------------------------------------
// Verdicts
// -------------------------------------------------------------------------

fn gamma_with(tys: &[Type]) -> LocalCtx {
    let mut g = LocalCtx::nil();
    for ty in tys {
        g.entries.push(CtxEntry { ty: rty(ty.clone()), level: Level::Zero });
    }
    g
}

fn check(gamma: &LocalCtx, t: &Term, ty: &Type) {
    check_term(&GlobalCtx::default(), 0, Layer::Prog, gamma, t, ty, &Level::Zero, FUEL)
        .unwrap_or_else(|e| panic!("not well typed: {e:?}"));
}

fn conv(gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type) -> Result<(), ConvError> {
    conv_term(&GlobalCtx::default(), gamma, Layer::Prog, a, b, ty, &Level::Zero, FUEL)
        .map(drop)
}

fn accepts(gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type) {
    conv(gamma, a, b, ty).unwrap_or_else(|e| panic!("not convertible: {e:?}"));
}

fn refuses(gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type) {
    match conv(gamma, a, b, ty) {
        Err(ConvError::NotConvertible) => {}
        other => panic!("expected a refusal, got {other:?}"),
    }
}

// -------------------------------------------------------------------------
// The shape itself
// -------------------------------------------------------------------------

#[test]
fn the_element_type_is_the_lowering_of_a_two_constructor_nullary_inductive() {
    // §11.2's premise, stated as a typing obligation rather than as prose:
    // both bits inhabit the element type, and its two halves are unit-like,
    // so they are proof-irrelevant — which is what makes the *tag* of an
    // injection the only thing a comparison can observe about a bit.
    let g = gamma_with(&[]);
    check(&g, &bit(false), &bool_like());
    check(&g, &bit(true), &bool_like());
    accepts(&g, &arm_value(), &pair(tag(), unit(), tag_value(), triv()), &arm());
    // The two bits are not each other: a bit comparison is a tag comparison.
    refuses(&g, &bit(false), &bit(true), &bool_like());
}

#[test]
fn a_closed_word_is_well_typed_at_every_width_that_matters() {
    let g = gamma_with(&[]);
    for width in widths() {
        let w = word(width, 0x5555_5555_5555_5555_5555_5555_5555_5555);
        check(&g, &w, &word_ty(width));
    }
}

/// 0, 1, 2, cap − 1, cap, cap + 1 (design §8).
fn widths() -> Vec<u32> {
    vec![0, 1, 2, BIT_RUN_WIDTH_CAP - 1, BIT_RUN_WIDTH_CAP, BIT_RUN_WIDTH_CAP + 1]
}

// -------------------------------------------------------------------------
// The fast path decides what η decides
// -------------------------------------------------------------------------

#[test]
fn equal_words_are_convertible_at_every_width() {
    let g = gamma_with(&[]);
    for width in widths() {
        let bits = 0xdead_beef_cafe_f00d_0123_4567_89ab_cdef;
        accepts(&g, &word(width, bits), &word(width, bits), &word_ty(width));
    }
}

#[test]
fn a_difference_at_any_position_is_refused() {
    let g = gamma_with(&[]);
    for width in widths() {
        if width == 0 {
            // The empty vector is `Unit`: every two of them are convertible,
            // and there is no position to differ at.
            continue;
        }
        let ty = word_ty(width);
        for position in [0, width / 2, width - 1] {
            let a = word(width, 0);
            let b = word(width, 1u128 << position);
            refuses(&g, &a, &b, &ty);
            refuses(&g, &b, &a, &ty);
        }
    }
}

#[test]
fn a_difference_past_the_cap_is_still_refused() {
    // The bit that cannot fit in the first word: the residual has to go back
    // through the comparison, and the fast path must not answer for it.
    let width = BIT_RUN_WIDTH_CAP + 1;
    let g = gamma_with(&[]);
    let a = word(width, 0);
    let b = word(width, 1u128 << (width - 1));
    refuses(&g, &a, &b, &word_ty(width));
    accepts(&g, &a, &word(width, 0), &word_ty(width));
}

#[test]
fn only_the_prefix_packs_over_a_neutral_tail() {
    // `x : Vec(Bool; 3)` is a neutral tail: the first eight components pack,
    // and the residual is decided the way two neutrals are decided.
    let tail_ty = vec(bool_like(), nat(3));
    let g = gamma_with(&[tail_ty]);
    let ty = vec(bool_like(), nat(11));
    let x = || Term::Var(LocalVar(0));
    let a = word_over(8, 0xa5, x(), nat(3));
    check(&g, &a, &ty);
    accepts(&g, &a, &word_over(8, 0xa5, x(), nat(3)), &ty);
    refuses(&g, &a, &word_over(8, 0xa4, x(), nat(3)), &ty);
    // A differing *tail* under an equal prefix is refused too: the residual
    // is not answered for by the word.
    let y = || Term::Var(LocalVar(1));
    let g2 = gamma_with(&[vec(bool_like(), nat(3)), vec(bool_like(), nat(3))]);
    let over_x = word_over(8, 0xa5, y(), nat(3));
    let over_y = word_over(8, 0xa5, x(), nat(3));
    refuses(&g2, &over_x, &over_y, &ty);
}

#[test]
fn a_non_canonical_payload_does_not_pack_and_still_decides() {
    // The payload is proof-irrelevant, so the verdicts are the same as for
    // canonical bits; what must not happen is a *wrong* verdict because a
    // neutral payload was read as a canonical one.
    let g = gamma_with(&[tag()]);
    let ty = vec(bool_like(), nat(3));
    let mixed = pair(
        bool_like(),
        vec(bool_like(), nat(2)),
        opaque_bit(true, 0),
        pair(
            bool_like(),
            vec(bool_like(), nat(1)),
            bit(false),
            pair(bool_like(), vec(bool_like(), nat(0)), bit(true), triv()),
        ),
    );
    check(&g, &mixed, &ty);
    accepts(&g, &mixed, &word_over(3, 0b101, triv(), nat(0)), &ty);
    refuses(&g, &mixed, &word_over(3, 0b100, triv(), nat(0)), &ty);
}

#[test]
fn an_element_type_that_is_not_two_valued_is_untouched() {
    // `Nat + Nat` passes the *sum* half of the criterion and fails the
    // unit-like half, so nothing packs and the chain is compared by η. The
    // row exists because a criterion that accepted it would compare two
    // `inl 3` and `inl 4` as the same bit.
    let elem = sum(Type::Nat, Type::Nat);
    let g = gamma_with(&[]);
    let ty = vec(elem.clone(), nat(2));
    let mk = |x: u64, y: u64| {
        pair(
            elem.clone(),
            vec(elem.clone(), nat(1)),
            inj(false, Type::Nat, Type::Nat, nat(x)),
            pair(
                elem.clone(),
                vec(elem.clone(), nat(0)),
                inj(true, Type::Nat, Type::Nat, nat(y)),
                triv(),
            ),
        )
    };
    check(&g, &mk(3, 4), &ty);
    accepts(&g, &mk(3, 4), &mk(3, 4), &ty);
    refuses(&g, &mk(3, 4), &mk(4, 4), &ty);
}

#[test]
fn projections_out_of_a_word_agree_with_the_chain() {
    // η is what puts a word back together, so the fast path must not change
    // what `fst`/`snd` of a vector are. Compare a literal against its own
    // component-wise rebuild at width 4.
    let g = gamma_with(&[]);
    let ty = word_ty(4);
    let w = word(4, 0b1011);
    let proj = |k: u32| {
        let mut t = w.clone();
        let mut len = 4u64;
        for _ in 0..k {
            t = Term::Snd {
                fst_level: Level::Zero,
                snd_level: Level::Zero,
                fst_ty: rty(bool_like()),
                snd_ty: rty(vec(bool_like(), nat(len - 1))),
                pair: rt(t),
            };
            len -= 1;
        }
        t
    };
    let rebuilt = {
        let mut out = triv();
        for i in (0..4u32).rev() {
            let head = Term::Fst {
                fst_level: Level::Zero,
                snd_level: Level::Zero,
                fst_ty: rty(bool_like()),
                snd_ty: rty(vec(bool_like(), nat(u64::from(3 - i)))),
                pair: rt(proj(i)),
            };
            out = pair(bool_like(), vec(bool_like(), nat(u64::from(3 - i))), head, out);
        }
        out
    };
    check(&g, &rebuilt, &ty);
    accepts(&g, &rebuilt, &w, &ty);
    refuses(&g, &rebuilt, &word(4, 0b1111), &ty);
}
