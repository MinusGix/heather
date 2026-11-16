//! Native bitvector words: the criterion, the conversion fast path, and the
//! run's one-step view (`docs/kernel/native-bitvector-values-design.md`, round 2).
//!
//! A `Vec^l(T; n)` whose element type has exactly two canonical inhabitants
//! with proof-irrelevant payloads is a machine word, and this file is the
//! standing evidence that *reading it as one decides the same relation*. The
//! shape under test is the one the elaborator actually emits for a
//! two-constructor nullary inductive (`docs/inductives/inductive-tier0-lowering.md` §3):
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

use heather_kernel::rc::Rc;

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

// -------------------------------------------------------------------------
// The packed literal `Term::VecLit` (issues/kernel-native-bitvector-values.md)
// -------------------------------------------------------------------------
//
// A packed literal is a compact spelling of the pair chain above, so every
// row compares it against that chain: the evidence that the literal *is*
// its chain, at the widths, element orders and positions where a wrong
// reading would show. Its typing obligations are the chain's, and its
// refusals (range, payload, `box`) are pinned by their errors.

use heather_kernel::reduce::whnf_term;
use heather_kernel::term::{vec_lit_chain, VEC_LIT_WIDTH_CAP};
use heather_kernel::typing::{spell_checked_in_code, TypeError};

fn lit_over(zero: Term, one: Term, elem: Type, width: u32, bits: u64) -> Term {
    Term::VecLit { level: Level::Zero, elem: rty(elem), zero: rt(zero), one: rt(one), width, bits }
}

/// A packed word over `bool_like`, element 0 `False`, element 1 `True`.
fn lit(width: u32, bits: u64) -> Term {
    lit_over(bit(false), bit(true), bool_like(), width, bits)
}

fn mask(width: u32) -> u64 {
    if width == 64 { u64::MAX } else { (1u64 << width) - 1 }
}

fn lit_widths() -> [u32; 4] {
    [1, 2, VEC_LIT_WIDTH_CAP - 1, VEC_LIT_WIDTH_CAP]
}

#[test]
fn a_packed_literal_is_its_chain_at_every_width() {
    let g = gamma_with(&[]);
    for width in lit_widths() {
        let bits = 0x9e37_79b9_7f4a_7c15 & mask(width);
        let ty = word_ty(width);
        let l = lit(width, bits);
        check(&g, &l, &ty);
        accepts(&g, &l, &word(width, u128::from(bits)), &ty);
        accepts(&g, &word(width, u128::from(bits)), &l, &ty);
        accepts(&g, &l, &lit(width, bits), &ty);
        for position in [0, width - 1] {
            let flipped = bits ^ 1 << position;
            refuses(&g, &l, &word(width, u128::from(flipped)), &ty);
            refuses(&g, &word(width, u128::from(flipped)), &l, &ty);
            refuses(&g, &l, &lit(width, flipped), &ty);
        }
    }
}

#[test]
fn which_element_is_one_is_the_literal_s_not_the_type_s() {
    // The swapped literal: `zero` is `True`. Its bits read as the
    // complement — what a reader that assumed `zero` was the type's first
    // constructor would get wrong.
    let g = gamma_with(&[]);
    for width in lit_widths() {
        let ty = word_ty(width);
        let bits = 0x0123_4567_89ab_cdef & mask(width);
        let swapped = lit_over(bit(true), bit(false), bool_like(), width, bits);
        check(&g, &swapped, &ty);
        accepts(&g, &swapped, &word(width, u128::from(!bits & mask(width))), &ty);
        accepts(&g, &swapped, &lit(width, !bits & mask(width)), &ty);
        refuses(&g, &swapped, &lit(width, bits), &ty);
        // A constant literal: both elements the same, so the bits are
        // irrelevant to what it denotes.
        let ones = lit_over(bit(true), bit(true), bool_like(), width, bits);
        accepts(&g, &ones, &word(width, u128::from(mask(width))), &ty);
        refuses(&g, &ones, &word(width, 0), &ty);
    }
}

#[test]
fn a_packed_tail_under_a_structural_prefix() {
    // The elaborator packs a long literal's last 64 elements and keeps the
    // rest as pairs: the chain must still meet the all-structural word,
    // through the run's prefix-and-residual comparison.
    let g = gamma_with(&[]);
    let ty = word_ty(8);
    let tail = lit(5, 0b10110);
    let mixed = word_over(3, 0b101, tail, nat(5));
    check(&g, &mixed, &ty);
    accepts(&g, &mixed, &word(8, 0b10110 << 3 | 0b101), &ty);
    refuses(&g, &mixed, &word(8, 0b10111 << 3 | 0b101), &ty);
    refuses(&g, &mixed, &word(8, 0b10110 << 3 | 0b100), &ty);
}

#[test]
fn open_elements_and_an_open_element_type_fall_back_to_the_chain() {
    // Γ = (A : Ty 0, x : El A, y : El A): neither the element type nor its
    // elements are closed, so nothing packs into a word; the literal must
    // still be its chain, and still tell `x` from `y`.
    let mut g = LocalCtx::nil();
    g.entries.push(CtxEntry { ty: rty(Type::Ty(Level::Zero)), level: Level::constant(1) });
    let el = |a: u32| Type::El { level: Level::Zero, tm: rt(Term::Var(LocalVar(a))) };
    g.entries.push(CtxEntry { ty: rty(el(0)), level: Level::Zero });
    g.entries.push(CtxEntry { ty: rty(el(1)), level: Level::Zero });
    let a = el(2);
    let (x, y) = (Term::Var(LocalVar(1)), Term::Var(LocalVar(0)));
    let l = lit_over(x.clone(), y.clone(), a.clone(), 3, 0b010);
    let ty = vec(a.clone(), nat(3));
    check(&g, &l, &ty);
    let chain = |e: [&Term; 3]| {
        let mut out = triv();
        for (i, e) in e.iter().enumerate().rev() {
            let rest = vec(a.shift_local(1), nat(2 - i as u64));
            out = pair(a.clone(), rest, (*e).clone(), out);
        }
        out
    };
    accepts(&g, &l, &chain([&x, &y, &x]), &ty);
    refuses(&g, &l, &chain([&x, &x, &x]), &ty);
    refuses(&g, &l, &chain([&x, &y, &y]), &ty);
}

#[test]
fn a_literal_checks_against_a_computed_length() {
    // The literal's type spells its length as a numeral; a checking position
    // that computes the same length must accept it, and a different one
    // must not.
    let g = gamma_with(&[]);
    let computed = vec(bool_like(), Term::Succ(rt(Term::Succ(rt(nat(2))))));
    check(&g, &lit(4, 0b1001), &computed);
    let wrong = vec(bool_like(), Term::Succ(rt(nat(2))));
    assert!(check_term(&GlobalCtx::default(), 0, Layer::Prog, &g, &lit(4, 0b1001), &wrong, &Level::Zero, FUEL)
        .is_err());
}

fn infer_err(t: &Term) -> TypeError {
    heather_kernel::typing::infer_term(&GlobalCtx::default(), 0, Layer::Prog, &LocalCtx::nil(), t, FUEL)
        .expect_err("should be refused")
}

#[test]
fn an_out_of_range_or_ill_typed_literal_is_refused() {
    assert_eq!(infer_err(&lit(0, 0)), TypeError::HeadMismatch);
    assert_eq!(infer_err(&lit(VEC_LIT_WIDTH_CAP + 1, 0)), TypeError::HeadMismatch);
    assert_eq!(infer_err(&lit(3, 0b1000)), TypeError::HeadMismatch);
    // An element that is not of the element type is a refusal, even at a
    // position no bit selects.
    let bad = lit_over(bit(false), nat(1), bool_like(), 3, 0);
    infer_err(&bad);
    // The controls.
    heather_kernel::typing::infer_term(&GlobalCtx::default(), 0, Layer::Prog, &LocalCtx::nil(), &lit(3, 0b111), FUEL)
        .unwrap();
}

#[test]
fn projections_of_a_literal_reduce_to_its_chain_s() {
    let g = LocalCtx::nil();
    let l = lit(3, 0b110);
    let proj = |second: bool, of: Term, len: u64| {
        let (fst_ty, snd_ty, pair) = (rty(bool_like()), rty(vec(bool_like(), nat(len - 1))), rt(of));
        if second {
            Term::Snd { fst_level: Level::Zero, snd_level: Level::Zero, fst_ty, snd_ty, pair }
        } else {
            Term::Fst { fst_level: Level::Zero, snd_level: Level::Zero, fst_ty, snd_ty, pair }
        }
    };
    assert!(whnf_term(&proj(false, l.clone(), 3), &g, FUEL).unwrap() == bit(false));
    assert!(whnf_term(&proj(true, l.clone(), 3), &g, FUEL).unwrap() == lit(2, 0b11));
    let second = proj(false, proj(true, l, 3), 2);
    assert!(whnf_term(&second, &g, FUEL).unwrap() == bit(true));
    // The last element's tail is `⟨⟩`, not a width-zero literal.
    assert!(whnf_term(&proj(true, lit(1, 1), 1), &g, FUEL).unwrap() == triv());
}

#[test]
fn a_box_payload_sees_the_chain() {
    // The code recursors range over component forms, so a literal under
    // `box` is refused, and the quote boundary spells it as its chain.
    let l = lit(3, 0b101);
    let ty = word_ty(3);
    let code_ty = Type::CodeTm { ctx: LocalCtx::nil(), ty: rty(ty.clone()), level: Level::Zero };
    let in_box = |t: Term| {
        check_term(&GlobalCtx::default(), 0, Layer::Meta, &LocalCtx::nil(), &Term::BoxTm(rt(t)), &code_ty, &Level::Zero, FUEL)
    };
    assert_eq!(in_box(l.clone()).unwrap_err(), TypeError::UnderBox);
    let spelled =
        spell_checked_in_code(&GlobalCtx::default(), 0, Layer::Code, &LocalCtx::nil(), rt(l.clone()), &ty, &Level::Zero, FUEL)
            .unwrap();
    let elem = rty(bool_like());
    assert!(*spelled == vec_lit_chain(&Level::Zero, &elem, &rt(bit(false)), &rt(bit(true)), 3, 0b101));
    in_box((*spelled).clone()).unwrap();
    accepts(&LocalCtx::nil(), &spelled, &l, &ty);
}

// -------------------------------------------------------------------------
// The items node `Term::VecItems` (issues/long-string-literal-stack-overflow.md)
// -------------------------------------------------------------------------
//
// The packed literal's sibling for any elements: an array, one level deep at
// any length, read through the same one-step view. The rows mirror the
// packed literal's — it *is* its chain, element by element, at an open
// element type too — and add the two things only it has: a live window
// (`from`) and a length past what any recursive walk survives.

use heather_kernel::term::vec_items_chain;

fn items_over(elem: Type, items: &[Term], from: u32) -> Term {
    Term::VecItems {
        level: Level::Zero,
        elem: rty(elem),
        items: items.iter().cloned().map(rt).collect::<Vec<_>>().into(),
        from,
    }
}

fn chain_over(elem: Type, items: &[Term]) -> Term {
    let items: Vec<_> = items.iter().cloned().map(rt).collect();
    vec_items_chain(&Level::Zero, &rty(elem), &items)
}

fn nats(n: u64) -> Vec<Term> {
    (0..n).map(|i| nat(i % 3)).collect()
}

#[test]
fn an_items_node_is_its_chain() {
    let g = gamma_with(&[]);
    for n in [1u64, 2, 7] {
        let xs = nats(n);
        let ty = vec(Type::Nat, nat(n));
        let node = items_over(Type::Nat, &xs, 0);
        check(&g, &node, &ty);
        accepts(&g, &node, &chain_over(Type::Nat, &xs), &ty);
        accepts(&g, &chain_over(Type::Nat, &xs), &node, &ty);
        for position in [0, n as usize - 1] {
            let mut ys = xs.clone();
            ys[position] = nat(5);
            refuses(&g, &node, &chain_over(Type::Nat, &ys), &ty);
            refuses(&g, &node, &items_over(Type::Nat, &ys, 0), &ty);
        }
    }
}

#[test]
fn an_items_node_means_its_live_window() {
    // `from` skips a prefix: the node is the shorter vector, equal (as
    // syntax and as a value) to the node of the window alone.
    let g = gamma_with(&[]);
    let xs = nats(6);
    let window = items_over(Type::Nat, &xs, 2);
    let alone = items_over(Type::Nat, &xs[2..], 0);
    let ty = vec(Type::Nat, nat(4));
    check(&g, &window, &ty);
    assert!(window == alone);
    accepts(&g, &window, &chain_over(Type::Nat, &xs[2..]), &ty);
    assert!(window != items_over(Type::Nat, &xs, 1));
    // At the wrong length the type itself refuses.
    assert!(check_term(&GlobalCtx::default(), 0, Layer::Prog, &g, &window, &vec(Type::Nat, nat(6)), &Level::Zero, FUEL)
        .is_err());
}

#[test]
fn open_items_at_an_open_element_type_are_their_chain() {
    // Γ = (A : Ty 0, x : El A, y : El A), as for the packed literal: and,
    // past it, substitution maps the items like any other subterm.
    let mut g = LocalCtx::nil();
    g.entries.push(CtxEntry { ty: rty(Type::Ty(Level::Zero)), level: Level::constant(1) });
    let el = |a: u32| Type::El { level: Level::Zero, tm: rt(Term::Var(LocalVar(a))) };
    g.entries.push(CtxEntry { ty: rty(el(0)), level: Level::Zero });
    g.entries.push(CtxEntry { ty: rty(el(1)), level: Level::Zero });
    let a = el(2);
    let (x, y) = (Term::Var(LocalVar(1)), Term::Var(LocalVar(0)));
    let node = items_over(a.clone(), &[x.clone(), y.clone(), x.clone()], 0);
    let ty = vec(a.clone(), nat(3));
    check(&g, &node, &ty);
    accepts(&g, &node, &chain_over(a.clone(), &[x.clone(), y.clone(), x.clone()]), &ty);
    refuses(&g, &node, &chain_over(a.clone(), &[x.clone(), x.clone(), x.clone()]), &ty);
    refuses(&g, &node, &chain_over(a.clone(), &[x.clone(), y.clone(), y.clone()]), &ty);
    // Weakened under one more binder of the element type, every item moves.
    let mut g2 = g.clone();
    g2.entries.push(CtxEntry { ty: rty(el(2)), level: Level::Zero });
    let shifted = node.shift_local(1);
    let ty2 = vec(el(3), nat(3));
    check(&g2, &shifted, &ty2);
    let (x2, y2) = (Term::Var(LocalVar(2)), Term::Var(LocalVar(1)));
    accepts(&g2, &shifted, &chain_over(el(3), &[x2.clone(), y2, x2]), &ty2);
}

#[test]
fn an_out_of_range_or_ill_typed_items_node_is_refused() {
    assert_eq!(infer_err(&items_over(Type::Nat, &nats(3), 3)), TypeError::HeadMismatch);
    assert_eq!(infer_err(&items_over(Type::Nat, &[], 0)), TypeError::HeadMismatch);
    // An item of another type, anywhere, is a refusal.
    infer_err(&items_over(Type::Nat, &[nat(1), triv(), nat(2)], 0));
    infer_err(&items_over(Type::Nat, &[nat(1), nat(1), triv()], 0));
    heather_kernel::typing::infer_term(&GlobalCtx::default(), 0, Layer::Prog, &LocalCtx::nil(), &items_over(Type::Nat, &nats(3), 0), FUEL)
        .unwrap();
}

#[test]
fn projections_of_an_items_node_reduce_to_its_chain_s() {
    let g = LocalCtx::nil();
    let xs = [nat(4), nat(5), nat(6)];
    let node = items_over(Type::Nat, &xs, 0);
    let proj = |second: bool, of: Term, len: u64| {
        let (fst_ty, snd_ty, pair) = (rty(Type::Nat), rty(vec(Type::Nat, nat(len - 1))), rt(of));
        if second {
            Term::Snd { fst_level: Level::Zero, snd_level: Level::Zero, fst_ty, snd_ty, pair }
        } else {
            Term::Fst { fst_level: Level::Zero, snd_level: Level::Zero, fst_ty, snd_ty, pair }
        }
    };
    assert!(whnf_term(&proj(false, node.clone(), 3), &g, FUEL).unwrap() == nat(4));
    assert!(whnf_term(&proj(true, node.clone(), 3), &g, FUEL).unwrap() == items_over(Type::Nat, &xs, 1));
    let second = proj(false, proj(true, node, 3), 2);
    assert!(whnf_term(&second, &g, FUEL).unwrap() == nat(5));
    // The last element's tail is `⟨⟩`.
    assert!(whnf_term(&proj(true, items_over(Type::Nat, &xs, 2), 1), &g, FUEL).unwrap() == triv());
}

#[test]
fn a_box_payload_sees_the_items_chain() {
    let xs = nats(3);
    let node = items_over(Type::Nat, &xs, 0);
    let ty = vec(Type::Nat, nat(3));
    let code_ty = Type::CodeTm { ctx: LocalCtx::nil(), ty: rty(ty.clone()), level: Level::Zero };
    let in_box = |t: Term| {
        check_term(&GlobalCtx::default(), 0, Layer::Meta, &LocalCtx::nil(), &Term::BoxTm(rt(t)), &code_ty, &Level::Zero, FUEL)
    };
    assert_eq!(in_box(node.clone()).unwrap_err(), TypeError::UnderBox);
    let spelled =
        spell_checked_in_code(&GlobalCtx::default(), 0, Layer::Code, &LocalCtx::nil(), rt(node.clone()), &ty, &Level::Zero, FUEL)
            .unwrap();
    assert!(*spelled == chain_over(Type::Nat, &xs));
    in_box((*spelled).clone()).unwrap();
    accepts(&LocalCtx::nil(), &spelled, &node, &ty);
}

#[test]
fn a_node_longer_than_any_chain_the_stack_holds_checks() {
    // The point of the node: a chain this long overflowed the checker's
    // stack (a few thousand elements did), the node is one level deep. This
    // runs on the test thread's own stack, with no `RUST_MIN_STACK` help
    // assumed; its elements share one `Rc`, as a literal's repeated
    // character does. Typing, substitution and syntactic equality walk the
    // node; comparing two separately built nodes *by value* unfolds them into
    // a chain as long as the node, which conversion walks by deferring its
    // deep tail comparisons (docs/kernel/deep-term-walks-design.md), at the full
    // length: each unfolded tail is a fresh node, whose bounds the array's
    // suffix joins answer in a stride's work, so the comparison is linear in
    // the length (it was quadratic, and this was pinned at a tenth of it:
    // issues/vec-items-window-bounds.md).
    let node_of = |n: usize| Term::VecItems {
        level: Level::Zero,
        elem: rty(Type::Nat),
        items: vec![rt(nat(1)); n].into(),
        from: 0,
    };
    let g = gamma_with(&[]);
    let n = 200_000u64;
    let node = node_of(n as usize);
    check(&g, &node, &vec(Type::Nat, Term::NatLit(n.into())));
    let shifted = node.shift_local(1);
    assert!(shifted == node);
    assert!(node_of(n as usize) == node);
    accepts(&g, &node_of(n as usize), &node_of(n as usize), &vec(Type::Nat, Term::NatLit(n.into())));
}
