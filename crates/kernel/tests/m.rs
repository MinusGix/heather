//! `M`, `corec` and `out`: the kernel round of the coinduction design
//! (`docs/kernel-coinduction-design.md` §1, §2, §10 step 3;
//! `issues/kernel-coinductive-types.md`).
//!
//! `M^{l,l',li}(I; i. S; i s. P; i s p. o)(j)` is the indexed negative
//! coinductive type in Petersson–Synek form: a node at index `j` has a shape
//! `s : S[j]` and a child at the index `o[j, s, p]` for each position `p`.
//! `out` is its only eliminator, `corec` (an apomorphism: each child is a new
//! seed or an existing tree) its only introduction, and β fires only under
//! `out`. There is no η and no rule unfolds a `corec` anywhere else, so two
//! descriptions of one tree are different values.
//!
//! The families: `Stream` (streams of `Nat`, unindexed: `I := Unit`), `From`
//! (indexed: a node at `i` carries a head with a proof that it is `i`, and
//! its child is at `S i`), and a `Stream` whose shapes sit at level one.
//!
//! Every conversion verdict is asked of both checkers (the value machine and
//! the rewriter, `conv::oracle`), every typing of both the gate and
//! `typing::oracle`. The four axes of `docs/testing-generated-terms.md`: a
//! literal and a neutral seed and index, an open carrier (a type variable of
//! Γ, with its step built from functions of Γ), checking positions (a tree
//! at a convertibly spelled index), and negative controls: two `corec`s of
//! one tree, a `corec` against a neutral, `t` against `in(out t)`.

use std::sync::Arc as Rc;

use heather_kernel::conv::{conv_term, conv_type, oracle};
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::reduce::{is_neutral_term, whnf_term};
use heather_kernel::term::{m_out_ty, m_step_ty, CtxEntry, GlobalCtx, LocalCtx, LocalVar, MSig, Term, Type};
use heather_kernel::typing::{self, check_term, check_type, infer_term, TypeError};

const FUEL: u64 = 200_000;

// -------------------------------------------------------------------------
// Syntax helpers
// -------------------------------------------------------------------------

fn rt(t: Term) -> Rc<Term> {
    Rc::new(t)
}

fn rty(t: Type) -> Rc<Type> {
    Rc::new(t)
}

fn c(n: u64) -> Level {
    Level::constant(n)
}

fn v(i: u32) -> Term {
    Term::Var(LocalVar(i))
}

fn nil_ctx() -> LocalCtx {
    LocalCtx::nil()
}

fn ext(gamma: &LocalCtx, ty: Type, level: Level) -> LocalCtx {
    let mut g = gamma.clone();
    g.entries.push(CtxEntry { ty: rty(ty), level });
    g
}

fn nat(n: u64) -> Term {
    let mut t = Term::Zero;
    for _ in 0..n {
        t = Term::Succ(rt(t));
    }
    t
}

fn succ(t: Term) -> Term {
    Term::Succ(rt(t))
}

fn unit_at(l: Level) -> Type {
    Type::Unit { level: l }
}

fn unit0() -> Type {
    unit_at(c(0))
}

fn triv() -> Term {
    Term::Triv { level: c(0) }
}

/// `a + b` by `elim_Nat` on `a`.
fn plus(a: Term, b: Term) -> Term {
    Term::ElimNat {
        level: c(0),
        motive: rty(Type::Nat),
        base: rt(b),
        step: rt(succ(v(0))),
        scrut: rt(a),
    }
}

fn app(fun: Term, dom: Type, cod: Type, arg: Term) -> Term {
    Term::App { fun: rt(fun), dom_level: c(0), cod_level: c(0), dom: rty(dom), cod: rty(cod), arg: rt(arg) }
}

/// `El^0 A` for a type variable `A`.
fn el(a: Term) -> Type {
    Type::El { level: c(0), tm: rt(a) }
}

// -------------------------------------------------------------------------
// The former's helpers, every annotation from the kernel's own schemas
// -------------------------------------------------------------------------

fn at(sig: &Rc<MSig>, j: Term) -> Type {
    sig.at(rt(j))
}

fn out(sig: &Rc<MSig>, j: Term, m: Term) -> Term {
    Term::Out { sig: Rc::clone(sig), index: rt(j), scrut: rt(m) }
}

fn corec(sig: &Rc<MSig>, carrier: Type, step: Term, j: Term, seed: Term) -> Term {
    Term::Corec {
        sig: Rc::clone(sig),
        carrier_level: c(0),
        carrier: rty(carrier),
        step: rt(step),
        index: rt(j),
        seed: rt(seed),
    }
}

/// `out`'s Σ at `j`, taken apart.
fn out_parts(sig: &Rc<MSig>, j: &Term) -> (Level, Level, Rc<Type>, Rc<Type>) {
    match m_out_ty(sig, j) {
        Type::Sigma { fst_level, snd_level, fst, snd } => (fst_level, snd_level, fst, snd),
        _ => unreachable!("m_out_ty builds a Σ"),
    }
}

/// `fst(out(m))`: the shape of `m`'s root.
fn shape_of(sig: &Rc<MSig>, j: Term, m: Term) -> Term {
    let (fst_level, snd_level, fst_ty, snd_ty) = out_parts(sig, &j);
    Term::Fst { fst_level, snd_level, fst_ty, snd_ty, pair: rt(out(sig, j, m)) }
}

/// `snd(out(m))`: the children of `m`'s root, as a function.
fn kids_of(sig: &Rc<MSig>, j: Term, m: Term) -> Term {
    let (fst_level, snd_level, fst_ty, snd_ty) = out_parts(sig, &j);
    Term::Snd { fst_level, snd_level, fst_ty, snd_ty, pair: rt(out(sig, j, m)) }
}

/// `snd(out(m)) p`: the child of `m`'s root at position `p`.
fn child(sig: &Rc<MSig>, j: Term, m: Term, p: Term) -> Term {
    let (_, _, _, snd) = out_parts(sig, &j);
    let Type::Pi { dom_level, cod_level, dom, cod } = snd.inst_top(0, &shape_of(sig, j.clone(), m.clone())) else {
        unreachable!("m_out_ty's second component is a Π")
    };
    Term::App { fun: rt(kids_of(sig, j, m)), dom_level, cod_level, dom, cod, arg: rt(p) }
}

/// What a step hands back at a position: a new seed, or an existing tree.
enum Kid {
    Seed(Term),
    Tree(Term),
}

/// A step `pair(head; λp. kid)` in `(Γ, i, x)` at `m_step_ty`'s
/// annotations: `head` in `(Γ, i, x)`, the kid in `(Γ, i, x, p)`.
fn step(sig: &Rc<MSig>, carrier: &Type, head: Term, kid: Kid) -> Term {
    let Type::Sigma { fst_level, snd_level, fst: fst_ty, snd: snd_ty } =
        m_step_ty(sig, &c(0), carrier).shift_local(1)
    else {
        unreachable!("m_step_ty builds a Σ")
    };
    let Type::Pi { dom_level, cod_level, dom, cod } = snd_ty.inst_top(0, &head) else {
        unreachable!("the step's second component is a Π")
    };
    let Type::Sum { lhs_level, rhs_level, lhs, rhs } = (*cod).clone() else {
        unreachable!("a child is a sum")
    };
    let kid = match kid {
        Kid::Seed(y) => Term::Inl { lhs_level, rhs_level, lhs, rhs, val: rt(y) },
        Kid::Tree(t) => Term::Inr { lhs_level, rhs_level, lhs, rhs, val: rt(t) },
    };
    Term::Pair {
        fst_level,
        snd_level,
        fst_ty,
        snd_ty,
        fst: rt(head),
        snd: rt(Term::Lam { dom_level, cod_level, dom, body: rt(kid) }),
    }
}

/// `pair(s; f)` at `out`'s Σ at `j`.
fn node(sig: &Rc<MSig>, j: &Term, s: Term, f: Term) -> Term {
    let (fst_level, snd_level, fst_ty, snd_ty) = out_parts(sig, j);
    Term::Pair { fst_level, snd_level, fst_ty, snd_ty, fst: rt(s), snd: rt(f) }
}

// -------------------------------------------------------------------------
// Families
// -------------------------------------------------------------------------

/// Streams of `Nat`: `M(Unit; _. Nat; _ _. Unit; _ _ _. ⟨⟩)`, closed.
fn stream() -> Rc<MSig> {
    Rc::new(MSig {
        level: c(0),
        pos_level: c(0),
        idx_level: c(0),
        idx: rty(unit0()),
        shape: rty(Type::Nat),
        pos: rty(unit0()),
        next: rt(triv()),
    })
}

fn stream_ty() -> Type {
    at(&stream(), triv())
}

fn hd(m: Term) -> Term {
    shape_of(&stream(), triv(), m)
}

fn tl(m: Term) -> Term {
    child(&stream(), triv(), m, triv())
}

/// `0, 0, 0, …` over the carrier `Unit`.
fn zeros() -> Term {
    let sig = stream();
    corec(&sig, unit0(), step(&sig, &unit0(), nat(0), Kid::Seed(triv())), triv(), triv())
}

/// `0, 0, 0, …` again, over the carrier `Nat`: the seed is carried along
/// and never read.
fn zeros_by_nat() -> Term {
    let sig = stream();
    corec(&sig, Type::Nat, step(&sig, &Type::Nat, nat(0), Kid::Seed(v(1))), triv(), nat(0))
}

/// `n, S n, S S n, …`: the seed is the head, its successor the next seed.
fn nats(n: Term) -> Term {
    let sig = stream();
    corec(&sig, Type::Nat, step(&sig, &Type::Nat, v(0), Kid::Seed(succ(v(1)))), triv(), n)
}

/// The constructor `in(s, f)`: a `corec` at carrier `Unit` whose every child
/// exits (design §1.4). `s` and `f : Unit → Stream` are in Γ.
fn cons(s: Term, f: Term) -> Term {
    let sig = stream();
    let kid = Kid::Tree(app(f.shift_local(3), unit0(), stream_ty(), v(0)));
    corec(&sig, unit0(), step(&sig, &unit0(), s.shift_local(2), kid), triv(), triv())
}

/// `From`: `M(Nat; i. Σ(h : Nat). Id(Nat; h; i); _ _. Unit; i _ _. S i)`.
/// A node at index `i` holds `i` itself (with the proof), and its child is
/// at `S i`: the shapes depend on the index, and the child index computes.
fn from_sig() -> Rc<MSig> {
    let shape = Type::Sigma {
        fst_level: c(0),
        snd_level: c(0),
        fst: rty(Type::Nat),
        snd: rty(Type::Id { level: c(0), ty: rty(Type::Nat), lhs: rt(v(0)), rhs: rt(v(1)) }),
    };
    Rc::new(MSig {
        level: c(0),
        pos_level: c(0),
        idx_level: c(0),
        idx: rty(Type::Nat),
        shape: rty(shape),
        pos: rty(unit0()),
        next: rt(succ(v(2))),
    })
}

/// The head `(i, refl i)` at index `i` (a term of `S[i]`), for `i` in any Γ.
fn from_head(i: Term) -> Term {
    let snd_ty = Type::Id { level: c(0), ty: rty(Type::Nat), lhs: rt(v(0)), rhs: rt(i.shift_local(1)) };
    Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(Type::Nat),
        snd_ty: rty(snd_ty),
        fst: rt(i.clone()),
        snd: rt(Term::Refl { level: c(0), ty: rty(Type::Nat), tm: rt(i) }),
    }
}

/// `from(j) : From(j)`, at carrier `Unit`: the step reads only the index.
fn from(j: Term) -> Term {
    let sig = from_sig();
    corec(&sig, unit0(), step(&sig, &unit0(), from_head(v(1)), Kid::Seed(triv())), j, triv())
}

/// The value at the root of a `From` tree at index `j`: `fst(fst(out m))`.
fn from_value(j: Term, m: Term) -> Term {
    let sig = from_sig();
    let Type::Sigma { fst_level, snd_level, fst, snd } = sig.shape_at(&j) else { unreachable!() };
    Term::Fst { fst_level, snd_level, fst_ty: fst, snd_ty: snd, pair: rt(shape_of(&sig, j, m)) }
}

// -------------------------------------------------------------------------
// Judgment helpers
// -------------------------------------------------------------------------

fn psi() -> GlobalCtx {
    GlobalCtx::default()
}

fn ck_ty_at(layer: Layer, gamma: &LocalCtx, t: &Type, level: &Level) -> Result<(), TypeError> {
    check_type(&psi(), 0, layer, gamma, t, level, FUEL)
}

fn ck_ty(gamma: &LocalCtx, t: &Type, level: Level) {
    ck_ty_at(Layer::Prog, gamma, t, &level).unwrap_or_else(|e| panic!("type does not check: {e:?}"));
    typing::oracle::check_type(&psi(), 0, Layer::Prog, gamma, t, &level, FUEL)
        .unwrap_or_else(|e| panic!("type does not check (oracle): {e:?}"));
}

/// Checked by the gate and by `typing::oracle`.
fn ck(gamma: &LocalCtx, t: &Term, ty: &Type, level: Level) {
    ck_ty(gamma, ty, level.clone());
    check_term(&psi(), 0, Layer::Prog, gamma, t, ty, &level, FUEL)
        .unwrap_or_else(|e| panic!("term does not check: {e:?}"));
    typing::oracle::check_term(&psi(), 0, Layer::Prog, gamma, t, ty, &level, FUEL)
        .unwrap_or_else(|e| panic!("term does not check (oracle): {e:?}"));
}

fn not_ck(gamma: &LocalCtx, t: &Term, ty: &Type, level: Level) {
    check_term(&psi(), 0, Layer::Prog, gamma, t, ty, &level, FUEL).expect_err("expected ill-typed");
    typing::oracle::check_term(&psi(), 0, Layer::Prog, gamma, t, ty, &level, FUEL)
        .expect_err("expected ill-typed (oracle)");
}

fn conv_ty_both(gamma: &LocalCtx, a: &Type, b: &Type, level: &Level) -> [bool; 2] {
    [
        conv_type(&psi(), gamma, Layer::Prog, a, b, level, FUEL).is_ok(),
        oracle::conv_type(&psi(), gamma, Layer::Prog, a, b, level, FUEL).is_ok(),
    ]
}

fn conv_tm_both(gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type, level: &Level) -> [bool; 2] {
    [
        conv_term(&psi(), gamma, Layer::Prog, a, b, ty, level, FUEL).is_ok(),
        oracle::conv_term(&psi(), gamma, Layer::Prog, a, b, ty, level, FUEL).is_ok(),
    ]
}

fn conv_ty(gamma: &LocalCtx, a: &Type, b: &Type, level: Level) {
    assert_eq!(conv_ty_both(gamma, a, b, &level), [true, true], "types not convertible (values, rewriter)");
}

fn not_conv_ty(gamma: &LocalCtx, a: &Type, b: &Type, level: Level) {
    assert_eq!(conv_ty_both(gamma, a, b, &level), [false, false], "types convertible (values, rewriter)");
}

/// Both terms are checked first, so a verdict is never about ill-typed input.
fn conv_tm(gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type, level: Level) {
    ck(gamma, a, ty, level.clone());
    ck(gamma, b, ty, level.clone());
    assert_eq!(conv_tm_both(gamma, a, b, ty, &level), [true, true], "terms not convertible (values, rewriter)");
}

fn not_conv_tm(gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type, level: Level) {
    ck(gamma, a, ty, level.clone());
    ck(gamma, b, ty, level.clone());
    assert_eq!(conv_tm_both(gamma, a, b, ty, &level), [false, false], "terms convertible (values, rewriter)");
}

/// Γ = (m : Stream).
fn one_stream() -> LocalCtx {
    ext(&nil_ctx(), stream_ty(), c(0))
}

// -------------------------------------------------------------------------
// Formation, introduction, elimination, the layer gate
// -------------------------------------------------------------------------

#[test]
fn the_families_and_their_terms_are_well_formed() {
    ck_ty(&nil_ctx(), &stream_ty(), c(0));
    ck(&nil_ctx(), &zeros(), &stream_ty(), c(0));
    ck(&nil_ctx(), &zeros_by_nat(), &stream_ty(), c(0));
    ck(&nil_ctx(), &nats(nat(3)), &stream_ty(), c(0));
    ck(&nil_ctx(), &hd(zeros()), &Type::Nat, c(0));
    ck(&nil_ctx(), &tl(zeros()), &stream_ty(), c(0));
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    ck_ty(&g, &at(&from_sig(), v(0)), c(0));
    ck(&g, &from(v(0)), &at(&from_sig(), v(0)), c(0));
    // corec synthesizes its type, out its Σ.
    let (ty, level) = infer_term(&psi(), 0, Layer::Prog, &g, &from(v(0)), FUEL).expect("corec infers");
    assert_eq!((ty, level), (at(&from_sig(), v(0)), c(0)));
    let o = out(&from_sig(), v(0), from(v(0)));
    let (ty, level) = infer_term(&psi(), 0, Layer::Prog, &g, &o, FUEL).expect("out infers");
    assert_eq!((ty, level), (m_out_ty(&from_sig(), &v(0)), c(0)));
}

#[test]
fn the_level_is_the_join_of_the_three() {
    // Positions at level one: the family is at 0 ⊔ 1 ⊔ 0 = 1, and a stream
    // at it is not a type of level zero.
    let sig = Rc::new(MSig { pos_level: c(1), pos: rty(unit_at(c(1))), ..(*stream()).clone() });
    let ty = at(&sig, triv());
    ck_ty(&nil_ctx(), &ty, c(1));
    assert!(ck_ty_at(Layer::Prog, &nil_ctx(), &ty, &c(0)).is_err());
}

#[test]
fn m_and_its_terms_are_admitted_at_layer_c() {
    // docs/kernel-m-codes-design.md §0: `TmM` is M's code, so the former and
    // its terms check at c as at p and m (`tests/m_codes.rs` has the rest).
    let ty = stream_ty();
    for layer in [Layer::Code, Layer::Prog, Layer::Meta] {
        assert_eq!(ck_ty_at(layer, &nil_ctx(), &ty, &c(0)), Ok(()));
        assert!(check_term(&psi(), 0, layer, &nil_ctx(), &zeros(), &ty, &c(0), FUEL).is_ok());
        let g = one_stream();
        assert!(check_term(&psi(), 0, layer, &g, &hd(v(0)), &Type::Nat, &c(0), FUEL).is_ok());
    }
}

#[test]
fn ill_typed_coalgebras_and_observations_are_refused() {
    let sig = from_sig();
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    // A corec at index j is not a tree at S j.
    not_ck(&g, &from(v(0)), &at(&sig, succ(v(0))), c(0));
    // A step whose head is at the wrong index: (S i, refl (S i)) : S[S i].
    let bad = corec(&sig, unit0(), step(&sig, &unit0(), from_head(succ(v(1))), Kid::Seed(triv())), v(0), triv());
    not_ck(&g, &bad, &at(&sig, v(0)), c(0));
    // A seed of the wrong carrier.
    let s = stream();
    let bad_seed = corec(&s, Type::Nat, step(&s, &Type::Nat, v(0), Kid::Seed(v(1))), triv(), triv());
    not_ck(&nil_ctx(), &bad_seed, &stream_ty(), c(0));
    // A child that is a seed where the carrier is Unit, given as a Nat.
    let bad_kid = corec(&s, unit0(), step(&s, &unit0(), nat(0), Kid::Seed(nat(0))), triv(), triv());
    not_ck(&nil_ctx(), &bad_kid, &stream_ty(), c(0));
    // out of a tree at index j, claimed at index S j.
    let gm = ext(&g, at(&sig, v(0)), c(0));
    let o = out(&sig, succ(v(1)), v(0));
    not_ck(&gm, &o, &m_out_ty(&sig, &succ(v(1))), c(0));
    // A tree is not a Nat stream.
    not_ck(&g, &from(v(0)), &stream_ty(), c(0));
}

// -------------------------------------------------------------------------
// β: one step, only under out
// -------------------------------------------------------------------------

#[test]
fn beta_on_a_literal_seed() {
    let g = nil_ctx();
    conv_tm(&g, &hd(nats(nat(2))), &nat(2), &Type::Nat, c(0));
    conv_tm(&g, &hd(tl(nats(nat(2)))), &nat(3), &Type::Nat, c(0));
    conv_tm(&g, &hd(tl(tl(zeros()))), &nat(0), &Type::Nat, c(0));
    not_conv_tm(&g, &hd(tl(nats(nat(2)))), &nat(2), &Type::Nat, c(0));
    // The rewriter's weak head of out(corec …) is a pair.
    let w = whnf_term(&out(&stream(), triv(), nats(nat(2))), &g, FUEL).expect("enough fuel");
    assert!(matches!(w, Term::Pair { .. }), "expected a pair, got {w:?}");
}

#[test]
fn beta_on_a_neutral_seed() {
    // Γ = (n : Nat): the seed is a variable, and so is every head.
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    conv_tm(&g, &hd(nats(v(0))), &v(0), &Type::Nat, c(0));
    conv_tm(&g, &hd(tl(tl(nats(v(0))))), &succ(succ(v(0))), &Type::Nat, c(0));
    not_conv_tm(&g, &hd(tl(nats(v(0)))), &v(0), &Type::Nat, c(0));
    // The tail is the corec at the next seed, exactly.
    conv_tm(&g, &tl(nats(v(0))), &nats(succ(v(0))), &stream_ty(), c(0));
    not_conv_tm(&g, &tl(nats(v(0))), &nats(v(0)), &stream_ty(), c(0));
}

/// Γ = (A : Ty 0, h : El A → Nat, t : El A → El A, a : El A).
fn open_carrier_ctx() -> LocalCtx {
    let g = ext(&nil_ctx(), Type::Ty(c(0)), c(1));
    let g = ext(&g, Type::Pi { dom_level: c(0), cod_level: c(0), dom: rty(el(v(0))), cod: rty(Type::Nat) }, c(0));
    let g = ext(&g, Type::Pi { dom_level: c(0), cod_level: c(0), dom: rty(el(v(1))), cod: rty(el(v(2))) }, c(0));
    ext(&g, el(v(2)), c(0))
}

/// `unfold(h, t, a)`: the stream `h a, h (t a), h (t (t a)), …` over the
/// carrier `El A` of [`open_carrier_ctx`].
fn unfold_open(seed: Term) -> Term {
    let sig = stream();
    // The carrier in (Γ, i): A is 4.
    let carrier = el(v(4));
    // In (Γ, i, x): A 5, h 4, t 3, x 0. In (Γ, i, x, p): A 6, t 4, x 1.
    let head = app(v(4), el(v(5)), Type::Nat, v(0));
    let next = app(v(4), el(v(6)), el(v(7)), v(1));
    corec(&sig, carrier.clone(), step(&sig, &carrier, head, Kid::Seed(next)), triv(), seed)
}

#[test]
fn beta_over_an_open_carrier() {
    let g = open_carrier_ctx();
    let h = |x: Term| app(v(2), el(v(3)), Type::Nat, x);
    let t = |x: Term| app(v(1), el(v(3)), el(v(4)), x);
    let s = unfold_open(v(0));
    ck(&g, &s, &stream_ty(), c(0));
    conv_tm(&g, &hd(s.clone()), &h(v(0)), &Type::Nat, c(0));
    conv_tm(&g, &hd(tl(s.clone())), &h(t(v(0))), &Type::Nat, c(0));
    conv_tm(&g, &tl(s.clone()), &unfold_open(t(v(0))), &stream_ty(), c(0));
    not_conv_tm(&g, &hd(tl(s.clone())), &h(v(0)), &Type::Nat, c(0));
    not_conv_tm(&g, &hd(tl(tl(s))), &h(t(v(0))), &Type::Nat, c(0));
}

#[test]
fn beta_at_a_neutral_index() {
    // Γ = (j : Nat): the root of from(j) holds j, its child is at S j and
    // holds S j; the child's index is computed by `o`.
    let sig = from_sig();
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    conv_tm(&g, &from_value(v(0), from(v(0))), &v(0), &Type::Nat, c(0));
    let kid = child(&sig, v(0), from(v(0)), triv());
    ck(&g, &kid, &at(&sig, succ(v(0))), c(0));
    conv_tm(&g, &from_value(succ(v(0)), kid.clone()), &succ(v(0)), &Type::Nat, c(0));
    conv_tm(&g, &kid, &from(succ(v(0))), &at(&sig, succ(v(0))), c(0));
    not_conv_tm(&g, &from_value(succ(v(0)), kid), &v(0), &Type::Nat, c(0));
    // At a literal index too.
    conv_tm(&nil_ctx(), &from_value(nat(4), from(nat(4))), &nat(4), &Type::Nat, c(0));
}

#[test]
fn trees_check_at_a_convertibly_spelled_index() {
    // The checking position: from(j) at From(0 + j), its child at
    // From(1 + j); M's index compares by conversion.
    let sig = from_sig();
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    conv_ty(&g, &at(&sig, v(0)), &at(&sig, plus(nat(0), v(0))), c(0));
    conv_ty(&g, &at(&sig, succ(v(0))), &at(&sig, plus(nat(1), v(0))), c(0));
    not_conv_ty(&g, &at(&sig, v(0)), &at(&sig, succ(v(0))), c(0));
    ck(&g, &from(v(0)), &at(&sig, plus(nat(0), v(0))), c(0));
    ck(&g, &child(&sig, v(0), from(v(0)), triv()), &at(&sig, plus(nat(1), v(0))), c(0));
    // out at the other spelling of the index observes the same tree.
    let o1 = out(&sig, v(0), from(v(0)));
    let o2 = out(&sig, plus(nat(0), v(0)), from(v(0)));
    conv_tm(&g, &o1, &o2, &m_out_ty(&sig, &v(0)), c(0));
}

#[test]
fn m_types_compare_structurally() {
    let g = nil_ctx();
    not_conv_ty(&g, &stream_ty(), &at(&from_sig(), nat(0)), c(0));
    let other = Rc::new(MSig { shape: rty(unit0()), ..(*stream()).clone() });
    not_conv_ty(&g, &stream_ty(), &at(&other, triv()), c(0));
    // The child index compares at `I`: `i` itself is `⟨⟩` by Unit η.
    let spelled = Rc::new(MSig { next: rt(v(2)), ..(*stream()).clone() });
    conv_ty(&g, &stream_ty(), &at(&spelled, triv()), c(0));
}

// -------------------------------------------------------------------------
// Constructors are exact under out
// -------------------------------------------------------------------------

#[test]
fn a_constructor_gives_back_its_children() {
    // Γ = (s : Nat, f : Unit → Stream): out(in(s, f)) ≡ (s, f), with f a
    // variable — no bisimilarity in between (design §1.4, §2.2).
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let fty = Type::Pi { dom_level: c(0), cod_level: c(0), dom: rty(unit0()), cod: rty(stream_ty()) };
    let g = ext(&g, fty.clone(), c(0));
    let t = cons(v(1), v(0));
    ck(&g, &t, &stream_ty(), c(0));
    conv_tm(&g, &hd(t.clone()), &v(1), &Type::Nat, c(0));
    conv_tm(&g, &kids_of(&stream(), triv(), t.clone()), &v(0), &fty, c(0));
    conv_tm(&g, &tl(t.clone()), &app(v(0), unit0(), stream_ty(), triv()), &stream_ty(), c(0));
    let o = out(&stream(), triv(), t);
    conv_tm(&g, &o, &node(&stream(), &triv(), v(1), v(0)), &m_out_ty(&stream(), &triv()), c(0));
}

// -------------------------------------------------------------------------
// No η: the negative controls
// -------------------------------------------------------------------------

#[test]
fn two_corecs_of_one_tree_are_distinct() {
    let g = nil_ctx();
    // The same observations at every depth tried...
    conv_tm(&g, &hd(zeros()), &hd(zeros_by_nat()), &Type::Nat, c(0));
    conv_tm(&g, &hd(tl(tl(zeros()))), &hd(tl(tl(zeros_by_nat()))), &Type::Nat, c(0));
    // ...and still two values.
    not_conv_tm(&g, &zeros(), &zeros_by_nat(), &stream_ty(), c(0));
    not_conv_tm(&g, &tl(zeros()), &tl(zeros_by_nat()), &stream_ty(), c(0));
}

#[test]
fn corec_congruence_compares_the_coalgebras() {
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let sig = stream();
    // A step spelled differently but convertible, and a seed likewise.
    let zeros_plus =
        corec(&sig, unit0(), step(&sig, &unit0(), plus(nat(0), nat(0)), Kid::Seed(triv())), triv(), triv());
    conv_tm(&g, &zeros(), &zeros_plus, &stream_ty(), c(0));
    conv_tm(&g, &nats(v(0)), &nats(plus(nat(0), v(0))), &stream_ty(), c(0));
    // Different seeds, a different step.
    not_conv_tm(&g, &nats(v(0)), &nats(succ(v(0))), &stream_ty(), c(0));
    let ones = corec(&sig, unit0(), step(&sig, &unit0(), nat(1), Kid::Seed(triv())), triv(), triv());
    not_conv_tm(&g, &zeros(), &ones, &stream_ty(), c(0));
    // The carrier is compared (with its level): zeros over Unit and over a
    // Unit at level one.
    let k1 = Term::Corec {
        sig: Rc::clone(&sig),
        carrier_level: c(1),
        carrier: rty(unit_at(c(1))),
        step: rt(m_step_pair_at_level_one(&sig)),
        index: rt(triv()),
        seed: rt(Term::Triv { level: c(1) }),
    };
    not_conv_tm(&g, &zeros(), &k1, &stream_ty(), c(0));
}

/// `zeros`' step over the carrier `Unit^1`, at `m_step_ty`'s annotations
/// for `k := 1`.
fn m_step_pair_at_level_one(sig: &Rc<MSig>) -> Term {
    let carrier = unit_at(c(1));
    let Type::Sigma { fst_level, snd_level, fst: fst_ty, snd: snd_ty } =
        m_step_ty(sig, &c(1), &carrier).shift_local(1)
    else {
        unreachable!()
    };
    let Type::Pi { dom_level, cod_level, dom, cod } = snd_ty.inst_top(0, &nat(0)) else { unreachable!() };
    let Type::Sum { lhs_level, rhs_level, lhs, rhs } = (*cod).clone() else { unreachable!() };
    let kid = Term::Inl { lhs_level, rhs_level, lhs, rhs, val: rt(Term::Triv { level: c(1) }) };
    Term::Pair {
        fst_level,
        snd_level,
        fst_ty,
        snd_ty,
        fst: rt(nat(0)),
        snd: rt(Term::Lam { dom_level, cod_level, dom, body: rt(kid) }),
    }
}

#[test]
fn corec_against_a_neutral_is_not_convertible() {
    let g = one_stream();
    not_conv_tm(&g, &zeros(), &v(0), &stream_ty(), c(0));
    not_conv_tm(&g, &v(0), &zeros(), &stream_ty(), c(0));
    not_conv_tm(&g, &tl(v(0)), &zeros(), &stream_ty(), c(0));
}

#[test]
fn a_tree_is_not_its_own_reconstruction() {
    // Γ = (t : Stream): in(fst(out t), snd(out t)) is a corec, t a
    // variable, so the two are distinct; their observations agree, by Σ η.
    let g = one_stream();
    let rebuilt = cons(hd(v(0)), kids_of(&stream(), triv(), v(0)));
    not_conv_tm(&g, &v(0), &rebuilt, &stream_ty(), c(0));
    let o = |m: Term| out(&stream(), triv(), m);
    conv_tm(&g, &o(v(0)), &o(rebuilt.clone()), &m_out_ty(&stream(), &triv()), c(0));
    conv_tm(&g, &tl(rebuilt), &tl(v(0)), &stream_ty(), c(0));
    // The copying coalgebra at carrier Stream: bisimilar to t, not t.
    let sig = stream();
    let copy_step = step(&sig, &stream_ty(), hd(v(0)), Kid::Seed(tl(v(1))));
    let copy = corec(&sig, stream_ty(), copy_step, triv(), v(0));
    not_conv_tm(&g, &v(0), &copy, &stream_ty(), c(0));
    conv_tm(&g, &hd(copy.clone()), &hd(v(0)), &Type::Nat, c(0));
    conv_tm(&g, &hd(tl(copy)), &hd(tl(v(0))), &Type::Nat, c(0));
}

// -------------------------------------------------------------------------
// out is neutral on a neutral
// -------------------------------------------------------------------------

#[test]
fn out_is_neutral_on_a_neutral_tree() {
    let g = ext(&one_stream(), stream_ty(), c(0));
    let o = out(&stream(), triv(), v(1));
    assert!(is_neutral_term(&o));
    assert_eq!(whnf_term(&o, &g, FUEL).expect("enough fuel"), o);
    let ty = m_out_ty(&stream(), &triv());
    conv_tm(&g, &o, &o.clone(), &ty, c(0));
    not_conv_tm(&g, &o, &out(&stream(), triv(), v(0)), &ty, c(0));
    not_conv_tm(&g, &hd(v(1)), &hd(v(0)), &Type::Nat, c(0));
    conv_tm(&g, &hd(tl(v(1))), &hd(tl(v(1))), &Type::Nat, c(0));
}

#[test]
fn the_neutral_congruence_reads_no_forced_annotation() {
    // Γ = (j : Nat, m : From(j)): out at two spellings of the index of one
    // neutral tree, compared without the index (ELIM_CONGRUENCE.md).
    let sig = from_sig();
    let g = ext(&ext(&nil_ctx(), Type::Nat, c(0)), at(&sig, v(0)), c(0));
    let o1 = out(&sig, v(1), v(0));
    let o2 = out(&sig, plus(nat(0), v(1)), v(0));
    conv_tm(&g, &o1, &o2, &m_out_ty(&sig, &v(1)), c(0));
    conv_tm(&g, &from_value(v(1), v(0)), &from_value(plus(nat(0), v(1)), v(0)), &Type::Nat, c(0));
}
