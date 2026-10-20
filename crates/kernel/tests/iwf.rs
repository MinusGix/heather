//! `IWf`, `sup_i` and `elim_IWf`: step 3 of the `IWf` landing
//! (`docs/iwf-former-design.md` §1.2, §2, §4, §5, §13; `issues/iwf-former.md`).
//!
//! `IWf^{l,li}(I; x:S. n; x. o; x i. c)(m)` is `Wf` with an index: the
//! constructor `sup_i(a; cs)` is at its output index `o[a/x]`, its `k`th child
//! at the child index `c[a/x, k/i]`, and nothing else is stored. The rules
//! are the Coq formalization's (heather-coq `M17_DESIGN.md`, "M17b: syntax and
//! rules", "M17b outcome"; `Typing/Declarative.v`'s `wft_iwf`, `wf_supi`,
//! `wf_elimIWf`, `ReductionBase.v`'s `red_elimIWf_supi`), and the neutral
//! congruence is its typed one (`ELIM_CONGRUENCE.md`, `actmne_elimIWf`).
//!
//! The families are hand-built lowerings in design §8.1's shape: a shape that
//! is a sum of constructor payloads, the arity, output index and child index
//! by `case` on the shape (the child index through a "convoy" `case` whose
//! motive abstracts the position, since a `case` branch does not refine the
//! position's type). `Tm` (`Lit : Tm(1)`, `App(n, m, f : Tm(n), a : Tm(m)) :
//! Tm(S(n + m))`) is design §4's example and the headline: β on open data at
//! a computed index. design §8.2's F1–F3, which route 2b rejects, are built
//! and type-checked; a `Vec` over a type variable of Γ is the open family.
//!
//! Every conversion verdict is asked of both checkers (the value machine and
//! the rewriter, `conv::oracle`), every typing of both the gate and
//! `typing::oracle`. The four axes of `docs/testing-generated-terms.md`: a
//! literal and a neutral scrutinee, an open family, checking positions (a
//! value at a convertibly spelled index), and negative controls throughout.

use std::sync::Arc as Rc;

use heather_kernel::conv::{conv_term, conv_type, oracle};
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::reduce::{is_neutral_term, is_whnf_type, whnf_term};
use heather_kernel::term::{
    fin_first, fin_next, iwf_children_ty, CtxEntry, GlobalCtx, IWfSig, LocalCtx, LocalVar, Term,
    Type,
};
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

fn unit0() -> Type {
    Type::Unit { level: c(0) }
}

fn triv() -> Term {
    Term::Triv { level: c(0) }
}

fn fin(len: Term) -> Type {
    Type::Fin { len: rt(len) }
}

fn sum(lhs: Type, rhs: Type) -> Type {
    Type::Sum { lhs_level: c(0), rhs_level: c(0), lhs: rty(lhs), rhs: rty(rhs) }
}

/// `Σ^{0,0}(_ : fst). snd`, `snd` under the binder.
fn sigma(fst: Type, snd: Type) -> Type {
    Type::Sigma { fst_level: c(0), snd_level: c(0), fst: rty(fst), snd: rty(snd) }
}

fn pair(fst_ty: Type, snd_ty: Type, fst: Term, snd: Term) -> Term {
    Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(fst_ty),
        snd_ty: rty(snd_ty),
        fst: rt(fst),
        snd: rt(snd),
    }
}

fn fst_of(fst_ty: Type, snd_ty: Type, p: Term) -> Term {
    Term::Fst { fst_level: c(0), snd_level: c(0), fst_ty: rty(fst_ty), snd_ty: rty(snd_ty), pair: rt(p) }
}

fn snd_of(fst_ty: Type, snd_ty: Type, p: Term) -> Term {
    Term::Snd { fst_level: c(0), snd_level: c(0), fst_ty: rty(fst_ty), snd_ty: rty(snd_ty), pair: rt(p) }
}

fn inl(lhs: Type, rhs: Type, val: Term) -> Term {
    Term::Inl { lhs_level: c(0), rhs_level: c(0), lhs: rty(lhs), rhs: rty(rhs), val: rt(val) }
}

fn inr(lhs: Type, rhs: Type, val: Term) -> Term {
    Term::Inr { lhs_level: c(0), rhs_level: c(0), lhs: rty(lhs), rhs: rty(rhs), val: rt(val) }
}

/// `case^{0,0,ml}(z. M; A; B; x. l; y. r; t)`.
fn case(ml: Level, lhs: Type, rhs: Type, motive: Type, l: Term, r: Term, scrut: Term) -> Term {
    Term::Case {
        lhs_level: c(0),
        rhs_level: c(0),
        motive_level: ml,
        lhs: rty(lhs),
        rhs: rty(rhs),
        motive: rty(motive),
        case_l: rt(l),
        case_r: rt(r),
        scrut: rt(scrut),
    }
}

fn pi(dom: Type, cod: Type, cl: Level) -> Type {
    Type::Pi { dom_level: c(0), cod_level: cl, dom: rty(dom), cod: rty(cod) }
}

fn lam(dom: Type, cl: Level, body: Term) -> Term {
    Term::Lam { dom_level: c(0), cod_level: cl, dom: rty(dom), body: rt(body) }
}

fn app(fun: Term, dom: Type, cod: Type, cl: Level, arg: Term) -> Term {
    Term::App { fun: rt(fun), dom_level: c(0), cod_level: cl, dom: rty(dom), cod: rty(cod), arg: rt(arg) }
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

fn refl_nat(t: Term) -> Term {
    Term::Refl { level: c(0), ty: rty(Type::Nat), tm: rt(t) }
}

/// Position `p` of `Fin(n)`: `inr^p (inl ⟨⟩)`.
fn pos(n: u64, p: u64) -> Term {
    assert!(p < n);
    let mut t = fin_first(rt(nat(n - p - 1)));
    for q in (0..p).rev() {
        t = fin_next(rt(nat(n - q - 1)), rt(t));
    }
    t
}

/// `Σ(_ : t₀). Σ(_ : t₁). … Unit` — the explicit spelling of a children
/// tuple's type, each tail under the binders before it.
fn tuple_ty(tys: &[Type]) -> Type {
    match tys.split_first() {
        None => unit0(),
        Some((t, rest)) => sigma(t.clone(), tuple_ty(rest).shift_local(1)),
    }
}

/// The children tuple `(c₀, (c₁, … ⟨⟩))` at those types.
fn tuple(tys: &[Type], vals: &[Term]) -> Term {
    assert_eq!(tys.len(), vals.len());
    match (tys.split_first(), vals.split_first()) {
        (Some((t, trest)), Some((x, vrest))) => {
            pair(t.clone(), tuple_ty(trest).shift_local(1), x.clone(), tuple(trest, vrest))
        }
        _ => triv(),
    }
}

// -------------------------------------------------------------------------
// Families: design §8.1's lowering of a two-constructor declaration
// -------------------------------------------------------------------------

/// `inductive D : I → Type { C₀(p : L) : D(o₀), C₁(p : R, k children) :
/// D(o₁) }`, the first constructor nullary. All components are scoped in the
/// family's own Γ (empty unless the family is open); `out_l`/`out_r` under
/// the payload `p`, `child_r` under `p, i : Fin k`.
#[derive(Clone)]
struct Fam {
    idx: Type,
    left: Type,
    right: Type,
    arity_r: u64,
    out_l: Term,
    out_r: Term,
    child_r: Term,
}

impl Fam {
    /// The signature `IWf^{0,0}(I; x : L + R. n; x. o; x i. c)`, in Γ.
    fn sig(&self) -> IWfSig {
        let (l1, r1) = (self.left.shift_local(1), self.right.shift_local(1));
        // n, in (Γ, x): case x { inl _ ⇒ 0 | inr _ ⇒ k }.
        let arity = case(c(0), l1.clone(), r1.clone(), Type::Nat, nat(0), nat(self.arity_r), v(0));
        // o, in (Γ, x): case x { inl p ⇒ o₀ | inr p ⇒ o₁ }.
        let out = case(
            c(0),
            l1,
            r1,
            self.idx.shift_local(2),
            self.out_l.shift_local_above(1, 1),
            self.out_r.shift_local_above(1, 1),
            v(0),
        );
        // c, in (Γ, x, i): the convoy (case x { … } : Π(i : Fin(n[x])). I) i.
        let (l2, r2) = (self.left.shift_local(2), self.right.shift_local(2));
        let motive = pi(fin(arity.inst_top(3, &v(0))), self.idx.shift_local(4), c(0));
        // In (Γ, x, i, p): `Fin 0` is `Empty`, so the nullary arm is absurd.
        let absurd = lam(
            fin(nat(0)),
            c(0),
            Term::ElimEmpty {
                level: c(0),
                scrut_level: c(0),
                motive: rty(self.idx.shift_local(5)),
                scrut: rt(v(0)),
            },
        );
        let at_r = lam(fin(nat(self.arity_r)), c(0), self.child_r.shift_local_above(2, 2));
        let convoy = case(c(0), l2, r2, motive, absurd, at_r, v(1));
        let child = app(convoy, fin(arity.shift_local(1)), self.idx.shift_local(3), c(0), v(0));
        IWfSig {
            level: c(0),
            idx_level: c(0),
            idx: rty(self.idx.clone()),
            shape: rty(sum(self.left.clone(), self.right.clone())),
            arity: rt(arity),
            out: rt(out),
            child: rt(child),
        }
    }
}

fn at(sig: &IWfSig, m: Term) -> Type {
    sig.at(rt(m))
}

fn elim(sig: &IWfSig, ml: Level, motive: Type, step: Term, index: Term, scrut: Term) -> Term {
    Term::ElimIWf {
        level: sig.level.clone(),
        idx_level: sig.idx_level.clone(),
        motive_level: ml,
        idx: Rc::clone(&sig.idx),
        shape: Rc::clone(&sig.shape),
        arity: Rc::clone(&sig.arity),
        out: Rc::clone(&sig.out),
        child: Rc::clone(&sig.child),
        motive: rty(motive),
        step: rt(step),
        index: rt(index),
        scrut: rt(scrut),
    }
}

/// `Tm`: `Lit : Tm(1)`, `App(n, m, f : Tm(n), a : Tm(m)) : Tm(S(n + m))`
/// (design §4, §11). Closed.
fn tm_fam() -> Fam {
    let nn = sigma(Type::Nat, Type::Nat);
    let fst_p = |p: Term| fst_of(Type::Nat, Type::Nat, p);
    let snd_p = |p: Term| snd_of(Type::Nat, Type::Nat, p);
    Fam {
        idx: Type::Nat,
        left: unit0(),
        right: nn,
        arity_r: 2,
        out_l: nat(1),
        out_r: succ(plus(fst_p(v(0)), snd_p(v(0)))),
        // In (p, i): case i { inl _ ⇒ fst p | inr _ ⇒ snd p }.
        child_r: case(c(0), unit0(), fin(nat(1)), Type::Nat, fst_p(v(2)), snd_p(v(2)), v(0)),
    }
}

/// The `App` label `inr (n, m)`.
fn tm_app_label(n: Term, m: Term) -> Term {
    inr(unit0(), sigma(Type::Nat, Type::Nat), pair(Type::Nat, Type::Nat, n, m))
}

fn tm_lit_label() -> Term {
    inl(unit0(), sigma(Type::Nat, Type::Nat), triv())
}

/// `Lit`, in any Γ (the family is closed).
fn tm_lit() -> Term {
    tm_fam().sig().supi(rt(tm_lit_label()), rt(triv()))
}

/// `App(n, m, f, a)`, at the explicit children tuple type.
fn tm_app(n: Term, m: Term, f: Term, a: Term) -> Term {
    let sig = tm_fam().sig();
    let tys = [at(&sig, n.clone()), at(&sig, m.clone())];
    sig.supi(rt(tm_app_label(n, m)), rt(tuple(&tys, &[f, a])))
}

/// `size : Π(n). Tm(n) → Nat`'s step, `size Lit = 1`,
/// `size (App f a) = S(size f + size a)`, in (Γ, a, cs, ih), Γ closed for
/// the family: `case a` with the ih convoyed, as its type `Π(i : Fin(n[a])).
/// Nat` only reduces under the branch.
fn size_step(lit: Term) -> Term {
    let sig = tm_fam().sig();
    let ih_ty = |arity: Term| pi(fin(arity), Type::Nat, c(0));
    // In (Γ, a, cs, ih, z).
    let motive = pi(ih_ty(sig.arity.inst_top(4, &v(0))), Type::Nat, c(0));
    let lit_arm = lam(ih_ty(nat(0)), c(0), lit.shift_local(5));
    // In (Γ, a, cs, ih, p, ih'): S(ih' 0 + ih' 1).
    let call = |p: u64| app(v(0), fin(nat(2)), Type::Nat, c(0), pos(2, p));
    let app_arm = lam(ih_ty(nat(2)), c(0), succ(plus(call(0), call(1))));
    let convoy = case(
        c(0),
        unit0(),
        sigma(Type::Nat, Type::Nat),
        motive,
        lit_arm,
        app_arm,
        v(2),
    );
    app(convoy, ih_ty(sig.arity.inst_top(3, &v(2))), Type::Nat, c(0), v(0))
}

/// `size(m; t)`, the family's signature read `k` binders below its Γ.
fn size_at(k: u32, m: Term, t: Term) -> Term {
    let sig = tm_fam().sig().shift_local(k);
    elim(&sig, c(0), Type::Nat, size_step(nat(1)).shift_local_above(k, 3), m, t)
}

/// The dependent motive `j z. Σ(k : Nat). Id(Nat; j; S k)` — every `Tm`
/// index is a successor — in (Γ, j, z).
fn pos_motive() -> Type {
    sigma(Type::Nat, Type::Id { level: c(0), ty: rty(Type::Nat), lhs: rt(v(2)), rhs: rt(succ(v(0))) })
}

/// Its step, in (Γ, a, cs, ih): `case a { Lit ⇒ (0, refl) | App(n, m) ⇒
/// (n + m, refl) }` at `Σ(k). Id(Nat; o[a]; S k)` — the motive mentions the
/// index, so each arm is typed at its constructor's output index.
fn pos_step() -> Term {
    let sig = tm_fam().sig();
    let at_out = |out: Term| sigma(Type::Nat, Type::Id {
        level: c(0),
        ty: rty(Type::Nat),
        lhs: rt(out.shift_local(1)),
        rhs: rt(succ(v(0))),
    });
    // In (Γ, a, cs, ih, w).
    let motive = at_out(sig.out.inst_top(4, &v(0)));
    let lit_arm = pair(
        Type::Nat,
        Type::Id { level: c(0), ty: rty(Type::Nat), lhs: rt(nat(1)), rhs: rt(succ(v(0))) },
        nat(0),
        refl_nat(nat(1)),
    );
    // In (Γ, a, cs, ih, p).
    let fst_p = fst_of(Type::Nat, Type::Nat, v(0));
    let snd_p = snd_of(Type::Nat, Type::Nat, v(0));
    let sum_p = plus(fst_p, snd_p);
    let app_arm = pair(
        Type::Nat,
        Type::Id {
            level: c(0),
            ty: rty(Type::Nat),
            lhs: rt(succ(sum_p.shift_local(1))),
            rhs: rt(succ(v(0))),
        },
        sum_p.clone(),
        refl_nat(succ(sum_p)),
    );
    case(c(0), unit0(), sigma(Type::Nat, Type::Nat), motive, lit_arm, app_arm, v(2))
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

fn conv_tm(gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type, level: Level) {
    assert_eq!(conv_tm_both(gamma, a, b, ty, &level), [true, true], "terms not convertible (values, rewriter)");
}

fn not_conv_tm(gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type, level: Level) {
    assert_eq!(conv_tm_both(gamma, a, b, ty, &level), [false, false], "terms convertible (values, rewriter)");
}

/// Γ = (n : Nat, m : Nat, f : Tm(n), a : Tm(m)): open data, the children
/// at variable indices. `n` = 3, `m` = 2, `f` = 1, `a` = 0.
fn open_app_ctx() -> LocalCtx {
    let sig = tm_fam().sig();
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let g = ext(&g, Type::Nat, c(0));
    let g = ext(&g, at(&sig, v(1)), c(0));
    ext(&g, at(&sig, v(1)), c(0))
}

// -------------------------------------------------------------------------
// Formation, introduction, the layer gate
// -------------------------------------------------------------------------

#[test]
fn the_families_are_well_formed() {
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let sig = tm_fam().sig();
    // IWf^{l,li}(…)(m) @ l ⊔ li, at a variable, a literal and a computed index.
    ck_ty(&g, &at(&sig, v(0)), c(0));
    ck_ty(&g, &at(&sig, nat(3)), c(0));
    ck_ty(&g, &at(&sig, plus(v(0), nat(2))), c(0));
    assert!(is_whnf_type(&at(&sig, v(0))));
    // Not one level above, and the index must be in `I`.
    assert_eq!(ck_ty_at(Layer::Prog, &g, &at(&sig, v(0)), &c(1)), Err(TypeError::LevelMismatch));
    assert!(ck_ty_at(Layer::Prog, &g, &at(&sig, triv()), &c(0)).is_err());
    // A child index outside `I` (here a `Fin` position, not a `Nat`) is
    // rejected: the signature's own premises are checked.
    let bad = IWfSig { child: rt(v(0)), ..sig.clone() };
    assert!(ck_ty_at(Layer::Prog, &g, &at(&bad, v(0)), &c(0)).is_err());
    // So is an output index outside `I`.
    let bad = IWfSig { out: rt(v(0)), ..sig };
    assert!(ck_ty_at(Layer::Prog, &g, &at(&bad, v(0)), &c(0)).is_err());
}

#[test]
fn the_level_is_the_join_of_the_shape_and_index_levels() {
    // Design §1.2: l ⊔ li. An index type at level 1 (`Ty 0`) and shapes at 0.
    let g = nil_ctx();
    let sig = IWfSig {
        level: c(0),
        idx_level: c(1),
        idx: rty(Type::Ty(c(0))),
        shape: rty(unit0()),
        arity: rt(nat(0)),
        out: rt(Term::TmNat),
        child: rt(Term::TmNat),
    };
    let ty = at(&sig, Term::TmNat);
    ck_ty(&g, &ty, c(1));
    assert_eq!(ck_ty_at(Layer::Prog, &g, &ty, &c(0)), Err(TypeError::LevelMismatch));
    // The one constructor is at «Nat», its children a `DVec^1(0; …) ⇝ Unit^1`.
    let leaf = sig.supi(rt(triv()), rt(Term::Triv { level: c(1) }));
    ck(&g, &leaf, &ty, c(1));
    not_ck(&g, &leaf, &at(&sig, Term::TmTy(c(0))), c(1));
}

#[test]
fn iwf_and_its_terms_are_gated_out_of_layer_c() {
    // Design §1: no code yet, so not at layer c until the rec.rs round;
    // admitted at p and m (Coq's `compt i`).
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let sig = tm_fam().sig();
    let ty = at(&sig, v(0));
    assert_eq!(ck_ty_at(Layer::Code, &g, &ty, &c(0)), Err(TypeError::LayerMismatch));
    assert_eq!(ck_ty_at(Layer::Prog, &g, &ty, &c(0)), Ok(()));
    assert_eq!(ck_ty_at(Layer::Meta, &g, &ty, &c(0)), Ok(()));
    let lit_ty = at(&sig, nat(1));
    assert!(check_term(&psi(), 0, Layer::Code, &nil_ctx(), &tm_lit(), &lit_ty, &c(0), FUEL).is_err());
    assert!(check_term(&psi(), 0, Layer::Meta, &nil_ctx(), &tm_lit(), &lit_ty, &c(0), FUEL).is_ok());
    let gt = ext(&g, ty, c(0));
    let s = size_at(2, v(1), v(0));
    assert!(check_term(&psi(), 0, Layer::Code, &gt, &s, &Type::Nat, &c(0), FUEL).is_err());
    assert!(check_term(&psi(), 0, Layer::Prog, &gt, &s, &Type::Nat, &c(0), FUEL).is_ok());
}

#[test]
fn a_constructor_is_at_its_output_index() {
    let sig = tm_fam().sig();
    // Lit : Tm(1), and only Tm(1).
    ck(&nil_ctx(), &tm_lit(), &at(&sig, nat(1)), c(0));
    not_ck(&nil_ctx(), &tm_lit(), &at(&sig, nat(0)), c(0));
    // It synthesizes Tm(o[a]), not a reduced index.
    let (ty, l) = infer_term(&psi(), 0, Layer::Prog, &nil_ctx(), &tm_lit(), FUEL).expect("infers");
    assert_eq!(l, Level::join(c(0), c(0)));
    let out_at = sig.out.inst_top(0, &tm_lit_label());
    assert_eq!(ty, at(&sig, out_at));
    // App(n, m, f, a) on open data: its type is the computed index
    // S(n + m), and a convertible spelling of it checks by conversion
    // (design §2, "pass it bare"): S n + m.
    let g = open_app_ctx();
    let t = tm_app(v(3), v(2), v(1), v(0));
    ck(&g, &t, &at(&sig, succ(plus(v(3), v(2)))), c(0));
    ck(&g, &t, &at(&sig, plus(succ(v(3)), v(2))), c(0));
    // Negative controls: a different index, and the children swapped (f is
    // at index n, the second child's index is m).
    not_ck(&g, &t, &at(&sig, plus(v(3), v(2))), c(0));
    not_ck(&g, &t, &at(&sig, succ(plus(v(2), v(3)))), c(0));
    let swapped = tm_app(v(3), v(2), v(0), v(1));
    not_ck(&g, &swapped, &at(&sig, succ(plus(v(3), v(2)))), c(0));
    // The children's type is the DVec of the design, which reduces to the
    // explicit tuple of the children's types.
    let cs_ty = iwf_children_ty(&sig, &tm_app_label(v(3), v(2)));
    conv_ty(&g, &cs_ty, &tuple_ty(&[at(&sig, v(3)), at(&sig, v(2))]), c(0));
    not_conv_ty(&g, &cs_ty, &tuple_ty(&[at(&sig, v(2)), at(&sig, v(3))]), c(0));
}

#[test]
fn a_closed_tree_at_a_literal_index() {
    // App(1, 1, Lit, Lit) : Tm(3).
    let sig = tm_fam().sig();
    let t = tm_app(nat(1), nat(1), tm_lit(), tm_lit());
    ck(&nil_ctx(), &t, &at(&sig, nat(3)), c(0));
    not_ck(&nil_ctx(), &t, &at(&sig, nat(2)), c(0));
    // A literal-scrutinee elimination computes all the way: size = 3.
    let s = size_at(0, nat(3), t);
    ck(&nil_ctx(), &s, &Type::Nat, c(0));
    conv_tm(&nil_ctx(), &s, &nat(3), &Type::Nat, c(0));
    not_conv_tm(&nil_ctx(), &s, &nat(2), &Type::Nat, c(0));
}

// -------------------------------------------------------------------------
// Elimination and β
// -------------------------------------------------------------------------

#[test]
fn elim_types_at_an_open_index() {
    // size : Π(n : Nat). Tm(n) → Nat, as λn t. elim_IWf(…; n; t).
    let sig = tm_fam().sig();
    let body = size_at(2, v(1), v(0));
    let size = lam(Type::Nat, c(0), lam(at(&sig, v(0)), c(0), body));
    let size_ty = pi(Type::Nat, pi(at(&sig, v(0)), Type::Nat, c(0)), c(0));
    ck(&nil_ctx(), &size, &size_ty, c(0));
    // The scrutinee must be at the elimination's index.
    let g = ext(&ext(&ext(&nil_ctx(), Type::Nat, c(0)), Type::Nat, c(0)), at(&sig, v(1)), c(0));
    not_ck(&g, &size_at(3, v(1), v(0)), &Type::Nat, c(0));
    ck(&g, &size_at(3, v(2), v(0)), &Type::Nat, c(0));
    // A step at the wrong type is rejected: a `Lit` arm returning `⟨⟩`.
    let bad = elim(&sig.shift_local(3), c(0), Type::Nat, size_step(triv()), v(2), v(0));
    not_ck(&g, &bad, &Type::Nat, c(0));
}

#[test]
fn beta_on_open_data_at_a_computed_index() {
    // The headline (design §4, §13 step 3; heather-coq `red_elimIWf_supi`):
    // size(App(n, m, f, a)) ≡ S(size f + size a) with n, m, f, a variables
    // and the scrutinee at the computed index S(n + m). There is no form B:
    // the constructor computes whatever its index.
    let g = open_app_ctx();
    let t = tm_app(v(3), v(2), v(1), v(0));
    let lhs = size_at(4, succ(plus(v(3), v(2))), t.clone());
    ck(&g, &lhs, &Type::Nat, c(0));
    let rhs = succ(plus(size_at(4, v(3), v(1)), size_at(4, v(2), v(0))));
    ck(&g, &rhs, &Type::Nat, c(0));
    conv_tm(&g, &lhs, &rhs, &Type::Nat, c(0));
    // At the index's other spelling too: β does not read the index.
    let lhs2 = size_at(4, plus(succ(v(3)), v(2)), t);
    ck(&g, &lhs2, &Type::Nat, c(0));
    conv_tm(&g, &lhs2, &rhs, &Type::Nat, c(0));
    // Negative controls: the children's order, and a missing successor.
    let swapped = succ(plus(size_at(4, v(2), v(0)), size_at(4, v(3), v(1))));
    not_conv_tm(&g, &lhs, &swapped, &Type::Nat, c(0));
    not_conv_tm(&g, &lhs, &plus(size_at(4, v(3), v(1)), size_at(4, v(2), v(0))), &Type::Nat, c(0));
    // The rewriter's weak head is the successor itself.
    let w = whnf_term(&lhs, &g, FUEL).expect("enough fuel");
    assert!(matches!(w, Term::Succ(_)), "expected S(…), got {w:?}");
}

#[test]
fn beta_fires_at_any_index_untyped() {
    // `red_elimIWf_supi` fires at a `sup_i` of any annotations and any
    // index: reduction is untyped, and an index that is not `o[a]` (here
    // 0, where `Lit` is at 1) does not stop it. Typing is what rules it out.
    let s = size_at(0, nat(0), tm_lit());
    not_ck(&nil_ctx(), &s, &Type::Nat, c(0));
    let w = whnf_term(&s, &nil_ctx(), FUEL).expect("enough fuel");
    assert_eq!(w, nat(1));
}

#[test]
fn beta_with_a_motive_that_mentions_the_index() {
    // Motive j z. Σ(k). Id(Nat; j; S k): the step is typed at each
    // constructor's output index, and β at App(n, m, f, a) : Tm(S(n + m))
    // gives the pair (n + m, refl), at the elimination's type
    // Σ(k). Id(Nat; S(n + m); S k).
    let g = open_app_ctx();
    let sig = tm_fam().sig().shift_local(4);
    let idx = succ(plus(v(3), v(2)));
    let t = tm_app(v(3), v(2), v(1), v(0));
    let e = elim(&sig, c(0), pos_motive().shift_local_above(4, 2), pos_step().shift_local_above(4, 3), idx.clone(), t);
    let res_ty = sigma(Type::Nat, Type::Id {
        level: c(0),
        ty: rty(Type::Nat),
        lhs: rt(idx.shift_local(1)),
        rhs: rt(succ(v(0))),
    });
    ck(&g, &e, &res_ty, c(0));
    let snd_ty = Type::Id { level: c(0), ty: rty(Type::Nat), lhs: rt(idx.shift_local(1)), rhs: rt(succ(v(0))) };
    let expected = pair(Type::Nat, snd_ty.clone(), plus(v(3), v(2)), refl_nat(idx.clone()));
    ck(&g, &expected, &res_ty, c(0));
    conv_tm(&g, &e, &expected, &res_ty, c(0));
    // The first component is n + m, not m + n.
    let first = fst_of(Type::Nat, snd_ty.clone(), e);
    conv_tm(&g, &first, &plus(v(3), v(2)), &Type::Nat, c(0));
    not_conv_tm(&g, &first, &plus(v(2), v(3)), &Type::Nat, c(0));
    // The motive is checked at every index: a step that claims the
    // successor witness of `Lit` is 1 does not type.
    let bad_step = {
        let mut s = pos_step();
        if let Term::Case { case_l, motive, lhs, rhs, case_r, scrut, .. } = &s {
            let Term::Pair { fst_ty, snd_ty, snd, .. } = &**case_l else { unreachable!() };
            let wrong = Term::Pair {
                fst_level: c(0),
                snd_level: c(0),
                fst_ty: Rc::clone(fst_ty),
                snd_ty: Rc::clone(snd_ty),
                fst: rt(nat(1)),
                snd: Rc::clone(snd),
            };
            s = case(c(0), (**lhs).clone(), (**rhs).clone(), (**motive).clone(), wrong, (**case_r).clone(), (**scrut).clone());
        }
        s
    };
    let gk = ext(&ext(&nil_ctx(), Type::Nat, c(0)), at(&tm_fam().sig(), v(0)), c(0));
    let bad = elim(&tm_fam().sig().shift_local(2), c(0), pos_motive().shift_local_above(2, 2), bad_step.shift_local_above(2, 3), v(1), v(0));
    let bad_ty = sigma(Type::Nat, Type::Id { level: c(0), ty: rty(Type::Nat), lhs: rt(v(2)), rhs: rt(succ(v(0))) });
    not_ck(&gk, &bad, &bad_ty, c(0));
}

// -------------------------------------------------------------------------
// Neutral elimination: the typed congruence
// -------------------------------------------------------------------------

/// Γ = (k : Nat, t : Tm(k), u : Tm(k)): neutral scrutinees.
fn neutral_ctx() -> LocalCtx {
    let sig = tm_fam().sig();
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let g = ext(&g, at(&sig, v(0)), c(0));
    ext(&g, at(&sig, v(1)), c(0))
}

#[test]
fn elim_is_neutral_on_a_neutral_scrutinee() {
    let g = neutral_ctx();
    let s = size_at(3, v(2), v(1));
    ck(&g, &s, &Type::Nat, c(0));
    assert!(is_neutral_term(&s));
    assert_eq!(whnf_term(&s, &g, FUEL).expect("enough fuel"), s);
    conv_tm(&g, &s, &s.clone(), &Type::Nat, c(0));
    // A different scrutinee is a different neutral.
    not_conv_tm(&g, &s, &size_at(3, v(2), v(0)), &Type::Nat, c(0));
    // A different step is not convertible: `Lit ↦ 1` against `Lit ↦ 2`.
    let sig = tm_fam().sig().shift_local(3);
    let other = elim(&sig, c(0), Type::Nat, size_step(nat(2)).shift_local_above(3, 3), v(2), v(1));
    ck(&g, &other, &Type::Nat, c(0));
    not_conv_tm(&g, &s, &other, &Type::Nat, c(0));
    // A different motive is not convertible either: at `Nat` against `Ty 0`
    // would not type, so the two compared are `j z. Nat` and the motive
    // that names the index, read at the scrutinee's own type.
    let dep = elim(&sig, c(0), pos_motive(), pos_step().shift_local_above(3, 3), v(2), v(1));
    let dep_ty = sigma(Type::Nat, Type::Id { level: c(0), ty: rty(Type::Nat), lhs: rt(v(3)), rhs: rt(succ(v(0))) });
    ck(&g, &dep, &dep_ty, c(0));
    conv_tm(&g, &dep, &dep.clone(), &dep_ty, c(0));
}

#[test]
fn the_neutral_congruence_reads_no_forced_annotation() {
    // heather-coq ELIM_CONGRUENCE.md: the scrutinees, the motive's level,
    // the motive and the step are compared; the signature and the index are
    // forced by the scrutinee's type. Two eliminations of one neutral `t`
    // whose signatures, indices and motives are spelled differently but
    // convertibly are convertible.
    let g = neutral_ctx();
    let s = size_at(3, v(2), v(1));
    // The signature respelled: `Lit`'s output index as `0 + 1`, and the
    // index `k` as `0 + k`. The motive as El(«Nat»).
    let mut fam = tm_fam();
    fam.out_l = plus(nat(0), nat(1));
    let sig2 = fam.sig().shift_local(3);
    ck_ty(&g, &at(&sig2, v(2)), c(0));
    conv_ty(&g, &at(&sig2, v(2)), &at(&tm_fam().sig().shift_local(3), v(2)), c(0));
    let el_nat = Type::El { level: c(0), tm: rt(Term::TmNat) };
    let respelled = elim(&sig2, c(0), el_nat, size_step(nat(1)).shift_local_above(3, 3), plus(nat(0), v(2)), v(1));
    ck(&g, &respelled, &Type::Nat, c(0));
    conv_tm(&g, &s, &respelled, &Type::Nat, c(0));
    // Negative control: the same respelling with the other scrutinee.
    let other = elim(&sig2, c(0), Type::Nat, size_step(nat(1)).shift_local_above(3, 3), v(2), v(0));
    not_conv_tm(&g, &s, &other, &Type::Nat, c(0));
}

// -------------------------------------------------------------------------
// Values: equality of the visible data, no η, no irrelevance arm
// -------------------------------------------------------------------------

#[test]
fn value_equality_is_equality_of_the_visible_data() {
    // Design §5/§8.4: a `sup_i` stores its shape and its children and
    // nothing else, so two values are equal exactly when those are.
    let sig = tm_fam().sig();
    // Γ = (n, m, f : Tm(n), a : Tm(m), f' : Tm(n)).
    let g = ext(&open_app_ctx(), at(&sig, v(3)), c(0));
    let ty = at(&sig, succ(plus(v(4), v(3))));
    let t1 = tm_app(v(4), v(3), v(2), v(1));
    conv_tm(&g, &t1, &t1.clone(), &ty, c(0));
    // A different child: not equal, and no irrelevance arm hides it.
    let t2 = tm_app(v(4), v(3), v(0), v(1));
    ck(&g, &t2, &ty, c(0));
    not_conv_tm(&g, &t1, &t2, &ty, c(0));
    // Two distinct variables of one family type are not equal (no
    // irrelevance: this is not `sEq`), and a variable is not a constructor
    // form (no η).
    let g1 = ext(&ext(&nil_ctx(), at(&sig, nat(1)), c(0)), at(&sig, nat(1)), c(0));
    not_conv_tm(&g1, &v(0), &v(1), &at(&sig, nat(1)), c(0));
    not_conv_tm(&g1, &v(0), &tm_lit(), &at(&sig, nat(1)), c(0));
    // Closed values at Tm(1) and Tm(3) compare by their data.
    conv_tm(&nil_ctx(), &tm_lit(), &tm_lit(), &at(&sig, nat(1)), c(0));
    let big = tm_app(nat(1), nat(1), tm_lit(), tm_lit());
    conv_tm(&nil_ctx(), &big, &big.clone(), &at(&sig, nat(3)), c(0));
}

#[test]
fn the_children_compare_through_sigma_and_unit_eta() {
    // A children tuple held as a variable `cs` against its projections: the
    // comparison descends at the children's `DVec` type, which reduces to
    // Σ/Unit and takes their η. No `IWf`-specific rule is involved.
    let sig = tm_fam().sig();
    let tys = [at(&sig, v(1)), at(&sig, v(0))];
    let cs_ty = tuple_ty(&tys);
    // Γ = (n, m, cs : Σ(Tm(n)). Σ(Tm(m)). Unit).
    let g = ext(&ext(&ext(&nil_ctx(), Type::Nat, c(0)), Type::Nat, c(0)), cs_ty.clone(), c(0));
    let (n, m) = (v(2), v(1));
    let label = tm_app_label(n.clone(), m.clone());
    let sig3 = sig.shift_local(3);
    let whole = sig3.supi(rt(label.clone()), rt(v(0)));
    let tys3 = [at(&sig3, n.clone()), at(&sig3, m.clone())];
    let tail_ty = tuple_ty(&tys3[1..]).shift_local(1);
    let first = fst_of(tys3[0].clone(), tail_ty.clone(), v(0));
    let rest = snd_of(tys3[0].clone(), tail_ty, v(0));
    let second = fst_of(tys3[1].clone(), unit0(), rest);
    let spelled = sig3.supi(rt(label), rt(tuple(&tys3, &[first, second])));
    let ty = at(&sig3, succ(plus(n, m)));
    ck(&g, &whole, &ty, c(0));
    ck(&g, &spelled, &ty, c(0));
    conv_tm(&g, &whole, &spelled, &ty, c(0));
}

#[test]
fn the_annotations_of_a_constructor_are_forced() {
    // A `sup_i` whose signature is spelled differently (but convertibly) is
    // the same value: the annotations are the type's (heather-coq
    // `actmnf_supi`), at the left's type.
    let mut fam = tm_fam();
    fam.out_l = plus(nat(0), nat(1));
    let sig2 = fam.sig();
    let sig = tm_fam().sig();
    let lit2 = sig2.supi(rt(tm_lit_label()), rt(triv()));
    ck(&nil_ctx(), &lit2, &at(&sig, nat(1)), c(0));
    conv_tm(&nil_ctx(), &tm_lit(), &lit2, &at(&sig, nat(1)), c(0));
}

// -------------------------------------------------------------------------
// Type conversion
// -------------------------------------------------------------------------

#[test]
fn type_conversion_is_structural_with_the_index() {
    let g = ext(&ext(&nil_ctx(), Type::Nat, c(0)), Type::Nat, c(0));
    let sig = tm_fam().sig().shift_local(2);
    // Convertible indices: S(n + m) and S n + m.
    conv_ty(&g, &at(&sig, succ(plus(v(1), v(0)))), &at(&sig, plus(succ(v(1)), v(0))), c(0));
    // Different indices: distinguished.
    not_conv_ty(&g, &at(&sig, v(1)), &at(&sig, v(0)), c(0));
    not_conv_ty(&g, &at(&sig, nat(1)), &at(&sig, nat(2)), c(0));
    // A different signature at the same index: distinguished (the child
    // indices swapped, so `App`'s children would be at m and n).
    let mut fam = tm_fam();
    let fst_p = fst_of(Type::Nat, Type::Nat, v(2));
    let snd_p = snd_of(Type::Nat, Type::Nat, v(2));
    fam.child_r = case(c(0), unit0(), fin(nat(1)), Type::Nat, snd_p, fst_p, v(0));
    let swapped = fam.sig().shift_local(2);
    not_conv_ty(&g, &at(&sig, v(0)), &at(&swapped, v(0)), c(0));
    // Different levels: distinguished.
    let up = IWfSig { level: c(1), shape: rty(Type::Sum {
        lhs_level: c(1),
        rhs_level: c(1),
        lhs: rty(Type::Unit { level: c(1) }),
        rhs: rty(Type::Unit { level: c(1) }),
    }), ..sig.clone() };
    not_conv_ty(&g, &at(&sig, v(0)), &at(&up, v(0)), c(0));
}

// -------------------------------------------------------------------------
// Design §8.2: what route 2b rejects (F1–F3), as hand-built IWf terms
// -------------------------------------------------------------------------

fn leaf(sig: &IWfSig, left: &Type, right: &Type) -> Term {
    sig.supi(rt(inl(left.clone(), right.clone(), triv())), rt(triv()))
}

fn node(sig: &IWfSig, left: &Type, right: &Type, payload: Term, tys: &[Type], kids: &[Term]) -> Term {
    sig.supi(rt(inr(left.clone(), right.clone(), payload)), rt(tuple(tys, kids)))
}

#[test]
fn f1_a_child_at_a_non_variable_index() {
    // Leaf : T(0), Node(n, l : T(0), r : T(n)) : T(S n) — `c(a, 0) := 0`.
    let fam = Fam {
        idx: Type::Nat,
        left: unit0(),
        right: Type::Nat,
        arity_r: 2,
        out_l: nat(0),
        out_r: succ(v(0)),
        child_r: case(c(0), unit0(), fin(nat(1)), Type::Nat, nat(0), v(2), v(0)),
    };
    let sig = fam.sig();
    let (l, r) = (fam.left.clone(), fam.right.clone());
    let lf = leaf(&sig, &l, &r);
    ck(&nil_ctx(), &lf, &at(&sig, nat(0)), c(0));
    // Node(0, Leaf, Leaf) : T(1); Node(1, Leaf, Node(0, Leaf, Leaf)) : T(2).
    let n1 = node(&sig, &l, &r, nat(0), &[at(&sig, nat(0)), at(&sig, nat(0))], &[lf.clone(), lf.clone()]);
    ck(&nil_ctx(), &n1, &at(&sig, nat(1)), c(0));
    let n2 = node(&sig, &l, &r, nat(1), &[at(&sig, nat(0)), at(&sig, nat(1))], &[lf.clone(), n1.clone()]);
    ck(&nil_ctx(), &n2, &at(&sig, nat(2)), c(0));
    // Open data: Γ = (n, r : T(n)) ⊢ Node(n, Leaf, r) : T(S n).
    let g = ext(&ext(&nil_ctx(), Type::Nat, c(0)), at(&sig, v(0)), c(0));
    let open = node(&sig, &l, &r, v(1), &[at(&sig, nat(0)), at(&sig, v(1))], &[lf.clone(), v(0)]);
    ck(&g, &open, &at(&sig, succ(v(1))), c(0));
    // Negative control: the left child must be at 0, not at n.
    let bad = node(&sig, &l, &r, v(1), &[at(&sig, v(1)), at(&sig, v(1))], &[v(0), v(0)]);
    not_ck(&g, &bad, &at(&sig, succ(v(1))), c(0));
}

#[test]
fn f2_two_children_at_one_index() {
    // Leaf : T(1), Node(n, l : T(n), r : T(n)) : T(n + n) — `c(a, _) := n`,
    // no coherence predicate.
    let fam = Fam {
        idx: Type::Nat,
        left: unit0(),
        right: Type::Nat,
        arity_r: 2,
        out_l: nat(1),
        out_r: plus(v(0), v(0)),
        child_r: v(1),
    };
    let sig = fam.sig();
    let (l, r) = (fam.left.clone(), fam.right.clone());
    // Γ = (n, x : T(n), y : T(n), z : T(S n)).
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let g = ext(&g, at(&sig, v(0)), c(0));
    let g = ext(&g, at(&sig, v(1)), c(0));
    let g = ext(&g, at(&sig, succ(v(2))), c(0));
    let n = v(3);
    let tys = [at(&sig, n.clone()), at(&sig, n.clone())];
    let xy = node(&sig, &l, &r, n.clone(), &tys, &[v(2), v(1)]);
    let xx = node(&sig, &l, &r, n.clone(), &tys, &[v(2), v(2)]);
    ck(&g, &xy, &at(&sig, plus(n.clone(), n.clone())), c(0));
    ck(&g, &xx, &at(&sig, plus(n.clone(), n.clone())), c(0));
    not_conv_tm(&g, &xy, &xx, &at(&sig, plus(n.clone(), n.clone())), c(0));
    // Negative control: a child at another index.
    let bad = node(&sig, &l, &r, n.clone(), &[at(&sig, n.clone()), at(&sig, succ(n.clone()))], &[v(2), v(0)]);
    not_ck(&g, &bad, &at(&sig, plus(n.clone(), n)), c(0));
    // Closed: Node(1, Leaf, Leaf) : T(2).
    let lf = leaf(&sig, &l, &r);
    let n1 = node(&sig, &l, &r, nat(1), &[at(&sig, nat(1)), at(&sig, nat(1))], &[lf.clone(), lf]);
    ck(&nil_ctx(), &n1, &at(&sig, nat(2)), c(0));
}

#[test]
fn f3_a_payload_that_mentions_a_child_index() {
    // Nil : V(0), Cons(n, x : Fin(n), xs : V(n)) : V(S n) — `n` is stored, so
    // `x : Fin(n)` is an ordinary dependent field.
    let payload = sigma(Type::Nat, fin(v(0)));
    let fst_p = |p: Term| fst_of(Type::Nat, fin(v(0)), p);
    let fam = Fam {
        idx: Type::Nat,
        left: unit0(),
        right: payload.clone(),
        arity_r: 1,
        out_l: nat(0),
        out_r: succ(fst_p(v(0))),
        child_r: fst_p(v(1)),
    };
    let sig = fam.sig();
    let (l, r) = (fam.left.clone(), fam.right.clone());
    // Γ = (n, x : Fin(n), xs : V(n)).
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let g = ext(&g, fin(v(0)), c(0));
    let g = ext(&g, at(&sig, v(1)), c(0));
    let cons = |x: Term, xs: Term, n: Term| {
        let lbl = pair(Type::Nat, fin(v(0)), n.clone(), x);
        node(&sig, &l, &r, lbl, &[at(&sig, n)], &[xs])
    };
    ck(&g, &cons(v(1), v(0), v(2)), &at(&sig, succ(v(2))), c(0));
    // Negative control: a tail at the wrong index.
    not_ck(&g, &cons(v(1), v(0), v(2)), &at(&sig, v(2)), c(0));
    // Closed: Nil : V(0), but nothing is at V(1) — Cons(0, x, Nil) needs an
    // `x : Fin 0` — so a `Fin 1` head over Nil is rejected.
    let nil = leaf(&sig, &l, &r);
    ck(&nil_ctx(), &nil, &at(&sig, nat(0)), c(0));
    let one = cons(pos(1, 0), nil.clone(), nat(0));
    not_ck(&nil_ctx(), &one, &at(&sig, nat(1)), c(0));
}

// -------------------------------------------------------------------------
// An open family: Vec over a type variable of Γ
// -------------------------------------------------------------------------

#[test]
fn an_open_family_vec_over_a_type_variable() {
    // Γ_A = (A : Ty 0): Nil : V(0), Cons(n, x : El A, xs : V(n)) : V(S n).
    // The family mentions A, so every use below Γ_A shifts it.
    let el_a = |depth: u32| Type::El { level: c(0), tm: rt(v(depth)) };
    let payload = sigma(Type::Nat, el_a(1));
    let fst_p = |p: Term, depth: u32| fst_of(Type::Nat, el_a(depth), p);
    let fam = Fam {
        idx: Type::Nat,
        left: unit0(),
        right: payload,
        arity_r: 1,
        out_l: nat(0),
        out_r: succ(fst_p(v(0), 2)),
        child_r: fst_p(v(1), 3),
    };
    let sig_a = fam.sig();
    let ga = ext(&nil_ctx(), Type::Ty(c(0)), c(1));
    ck_ty(&ga, &at(&sig_a, nat(0)), c(0));
    // Γ = (A, n, x : El A, y : El A, xs : V(n)).
    let g = ext(&ga, Type::Nat, c(0));
    let g = ext(&g, el_a(1), c(0));
    let g = ext(&g, el_a(2), c(0));
    let sig = sig_a.shift_local(3);
    let g = ext(&g, at(&sig, v(2)), c(0));
    let sig = sig_a.shift_local(4);
    let (l, r) = (unit0(), sigma(Type::Nat, el_a(5)));
    let cons = |x: Term| {
        let lbl = pair(Type::Nat, el_a(5), v(3), x);
        node(&sig, &l, &r, lbl, &[at(&sig, v(3))], &[v(0)])
    };
    let ty = at(&sig, succ(v(3)));
    ck(&g, &cons(v(2)), &ty, c(0));
    ck(&g, &cons(v(1)), &ty, c(0));
    // Equal heads, equal values; different heads, different values.
    conv_tm(&g, &cons(v(2)), &cons(v(2)), &ty, c(0));
    not_conv_tm(&g, &cons(v(2)), &cons(v(1)), &ty, c(0));
    // length : V(n) → Nat by elim_IWf, β on the open cons: length(cons x xs)
    // ≡ S(length xs).
    let len_step = {
        // In (Γ', a, cs, ih), Γ' = Γ (sig at depth 4): case a with ih convoyed.
        let ih_ty = |arity: Term| pi(fin(arity), Type::Nat, c(0));
        let motive = pi(ih_ty(sig.arity.inst_top(4, &v(0))), Type::Nat, c(0));
        let r_s = r.shift_local(3);
        let nil_arm = lam(ih_ty(nat(0)), c(0), nat(0));
        let cons_arm = lam(ih_ty(nat(1)), c(0), succ(app(v(0), fin(nat(1)), Type::Nat, c(0), pos(1, 0))));
        let convoy = case(c(0), unit0(), r_s, motive, nil_arm, cons_arm, v(2));
        app(convoy, ih_ty(sig.arity.inst_top(3, &v(2))), Type::Nat, c(0), v(0))
    };
    let len = |idx: Term, t: Term| elim(&sig, c(0), Type::Nat, len_step.clone(), idx, t);
    let lhs = len(succ(v(3)), cons(v(2)));
    ck(&g, &lhs, &Type::Nat, c(0));
    let rhs = succ(len(v(3), v(0)));
    ck(&g, &rhs, &Type::Nat, c(0));
    conv_tm(&g, &lhs, &rhs, &Type::Nat, c(0));
    not_conv_tm(&g, &lhs, &len(v(3), v(0)), &Type::Nat, c(0));
}
