//! Declared-index families hand prototype: §8.2 of
//! `docs/inductive-indexed-lowering.md`, the claim that route 1 at a
//! *declared* index type is an instantiation of the landed `Nat` scheme, not
//! a redesign. The scheme reads "one family branch per index constructor,
//! `rec` at each recursive argument of the index constructor" — this file
//! builds that by hand, kernel terms against the real kernel, for the three
//! index shapes the generalization has to cover:
//!
//! - **an enum index** (`Parity`): the family is `Case` at motive `Ty 0` —
//!   no recursion is *possible* (no recursive argument of the index
//!   constructor to draw a `rec` from), and the scheme says so by shape;
//! - **a linear recursive index** (`MyNat`, a declared `Nat`-clone lowered
//!   onto `Wf` exactly as tier 1 declares it): the family is `elim_Wf` at
//!   motive `Ty 0`, and the recursive field's code is `ih` at a literal
//!   `Fin` index;
//! - **a branching recursive index** (`Shape`, with `SNode(l, r)`): two
//!   pattern variables, two recursive fields, each drawing from `ih` at a
//!   *different* `Fin` literal — the subject-recursive-judgment shape
//!   (`issues/indexed-families.md`, the 2026-07-28 conjecture) in miniature.
//!
//! The device the `Nat` case never needed: inside `elim_Wf`'s step, `ih` has
//! domain `Fin(arity a)` with `a` the *open* step binder, so a branch cannot
//! apply it at a literal until the arity is refined — `cs` and `ih` are
//! threaded **through the `Case` motive**, so each branch receives them at
//! the constructor-refined arity (wf.rs's own recursor device, §6.2 there).
//! Where the `Nat` scheme's arms leaned on `Case` β + Σ-η, the index side
//! here additionally leans on **Unit η**: an index constructor rebuilt from
//! a branch is `sup_f(inl u; cs')` with `u : Unit` and the children-vector
//! tail at `Vec(–; 0) ⇝ Unit`, and its identity with the declared
//! constructor is exactly η at `Unit`.
//!
//! Elisions, as in `indexed_route1.rs`: nominal tags and `Unit` spine
//! terminators for the *family's* constructors (single-constructor classes
//! have no sum, one-field spines are the field). The **index** declarations
//! are NOT elided: their tag sum (`Unit + Unit`) and children vectors are
//! spelled in full, because they are what the tier-1 lowering actually
//! emits and the composition with it is the thing under test.

use std::sync::Arc as Rc;

use heather_kernel::conv::conv_term;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{
    nth, CtxBase, CtxEntry, GlobalCtx, LocalCtx, LocalSubst, LocalVar, Term, Type,
};
use heather_kernel::typing::{check_term, check_type};

const FUEL: u64 = 1_000_000;

// ---------------------------------------------------------------------------
// Construction helpers (shared idiom with indexed_route1.rs)
// ---------------------------------------------------------------------------

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

/// A context of `n` entries for building substitutions: `LocalSubst::id`
/// reads only the length and the base.
fn scope(n: u32) -> LocalCtx {
    LocalCtx {
        base: CtxBase::Nil,
        entries: ((0..n).map(|_| CtxEntry { ty: rty(Type::Nat), level: c(0) }).collect::<Vec<_>>()).into(),
    }
}

fn el(t: Term) -> Type {
    Type::El { level: c(0), tm: rt(t) }
}

fn unit0() -> Type {
    Type::Unit { level: Level::Zero }
}

fn triv() -> Term {
    Term::Triv { level: Level::Zero }
}

fn ty0() -> Type {
    Type::Ty(c(0))
}

/// `M[h, z]` for a motive scoped in `(Γ, h, z)`, with `h` and `z` scoped in
/// Γ extended by `extra` binders.
fn mot_at(depth: u32, motive: &Type, h: Term, z: Term, extra: u32) -> Type {
    motive.apply_local(
        &LocalSubst::id(&scope(depth)).shift_local(extra).extended(rt(h)).extended(rt(z)),
    )
}

// ---------------------------------------------------------------------------
// Checking helpers
// ---------------------------------------------------------------------------

fn ck(gamma: &LocalCtx, t: &Term, ty: &Type, level: Level) {
    check_type(&GlobalCtx::default(), 0, Layer::Prog, gamma, ty, &level, FUEL)
        .expect("the type is well-formed");
    check_term(&GlobalCtx::default(), 0, Layer::Prog, gamma, t, ty, &level, FUEL)
        .unwrap_or_else(|e| panic!("term does not check: {e:?}"));
}

fn ck_fails(gamma: &LocalCtx, t: &Term, ty: &Type, level: Level) {
    check_term(&GlobalCtx::default(), 0, Layer::Prog, gamma, t, ty, &level, FUEL)
        .expect_err("the kernel gate must reject this");
}

fn ty_fails(gamma: &LocalCtx, ty: &Type, level: Level) {
    check_type(&GlobalCtx::default(), 0, Layer::Prog, gamma, ty, &level, FUEL)
        .expect_err("the type must be ill-formed");
}

fn conv(gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type, level: Level) {
    conv_term(&GlobalCtx::default(), gamma, Layer::Prog, a, b, ty, &level, FUEL)
        .unwrap_or_else(|e| panic!("not convertible: {e:?}"));
}

fn not_conv(gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type, level: Level) {
    conv_term(&GlobalCtx::default(), gamma, Layer::Prog, a, b, ty, &level, FUEL)
        .expect_err("expected inconvertible");
}

// ---------------------------------------------------------------------------
// The two-constructor tag sum, shared by every declared index here: both
// `Parity` (as the whole enum) and the Wf shapes (as the label type) are
// `Unit + Unit`, first constructor `inl ⟨⟩`, second `inr ⟨⟩`.
// ---------------------------------------------------------------------------

fn tag2_ty() -> Type {
    Type::Sum {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        lhs: rty(unit0()),
        rhs: rty(unit0()),
    }
}

fn inl_u(val: Term) -> Term {
    Term::Inl {
        lhs_level: c(0),
        rhs_level: c(0),
        lhs: rty(unit0()),
        rhs: rty(unit0()),
        val: rt(val),
    }
}

fn inr_u(val: Term) -> Term {
    Term::Inr {
        lhs_level: c(0),
        rhs_level: c(0),
        lhs: rty(unit0()),
        rhs: rty(unit0()),
        val: rt(val),
    }
}

// ---------------------------------------------------------------------------
// Part A — enum index. `Parity ≅ El ⌜Unit + Unit⌝`, `Even = inl ⟨⟩`,
// `Odd = inr ⟨⟩`; the family
//
//   AB<E> : (p : Parity) -> Type { A(x: E, y: E) : AB(Even), B : AB(Odd) }
//
// is one `Case` at motive `Ty 0` — no `elim_Wf`, no `ih`, because an enum's
// constructors have no recursive arguments for a recursive field to recurse
// on. The A-spine (tag and terminator elided) is `⌜Σ(x : El e). El e⌝`; the
// B-spine is `⌜Unit⌝`.
// ---------------------------------------------------------------------------

fn even() -> Term {
    inl_u(triv())
}

fn odd() -> Term {
    inr_u(triv())
}

/// `famAB e p : Ty 0`. `e` scoped in the ambient Γ; `case_l` binds the
/// `Unit` payload (shift 1), the Σ-code's `snd` binds one more (shift 2).
fn ab_fam(e: Term, p: Term) -> Term {
    Term::Case {
        lhs_level: c(0),
        rhs_level: c(0),
        motive_level: c(1),
        lhs: rty(unit0()),
        rhs: rty(unit0()),
        motive: rty(ty0()),
        case_l: rt(Term::TmSigma {
            fst_level: c(0),
            snd_level: c(0),
            fst: rt(e.shift_local(1)),
            snd: rt(e.shift_local(2)),
        }),
        case_r: rt(Term::TmUnit { level: Level::Zero }),
        scrut: rt(p),
    }
}

fn ab_ty(e: Term, p: Term) -> Type {
    el(ab_fam(e, p))
}

/// `A(x, y) = pair(x; y)` at `AB(Even)`.
fn a_val(e: Term, x: Term, y: Term) -> Term {
    Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(el(e.clone())),
        snd_ty: rty(el(e.shift_local(1))),
        fst: rt(x),
        snd: rt(y),
    }
}

/// The enum-indexed eliminator: `Case` on the index at motive
/// `Mot(p) = Π(v : El (famAB p)). M[p, v]`, applied to the scrutinee.
/// `a_case` is scoped `(Γ, x : El e, y : El e)`; `b_case` in Γ.
fn ab_elim(
    depth: u32,
    ml: &Level,
    e: Term,
    motive: &Type,
    a_case: Term,
    b_case: Term,
    p: Term,
    s: Term,
) -> Term {
    // case_l, scoped (Γ, u : Unit): λ(v : El (famAB (inl u))). a_case[fst v, snd v].
    let fst_ann = || rty(el(e.clone().shift_local(2)));
    let snd_ann = || rty(el(e.clone().shift_local(3)));
    let x_proj = Term::Fst {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: fst_ann(),
        snd_ty: snd_ann(),
        pair: rt(v(0)),
    };
    let y_proj = Term::Snd {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: fst_ann(),
        snd_ty: snd_ann(),
        pair: rt(v(0)),
    };
    let case_l = Term::Lam {
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(ab_ty(e.clone().shift_local(1), inl_u(v(0)))),
        body: rt(a_case.apply_local(
            &LocalSubst::id(&scope(depth))
                .shift_local(2)
                .extended(rt(x_proj))
                .extended(rt(y_proj)),
        )),
    };
    // case_r, scoped (Γ, u : Unit): λ(v : El (famAB (inr u))). b_case.
    let case_r = Term::Lam {
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(ab_ty(e.clone().shift_local(1), inr_u(v(0)))),
        body: rt(b_case.shift_local(2)),
    };
    // Mot, scoped (Γ, z : Parity): Π(v : El (famAB z)). M[z, v] — the Π's
    // binder is the motive's own `z`-slot, so `cod` is the motive verbatim.
    let mot = Type::Pi {
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(ab_ty(e.clone().shift_local(1), v(0))),
        cod: rty(motive.clone()),
    };
    Term::App {
        fun: rt(Term::Case {
            lhs_level: c(0),
            rhs_level: c(0),
            motive_level: ml.clone(),
            lhs: rty(unit0()),
            rhs: rty(unit0()),
            motive: rty(mot),
            case_l: rt(case_l),
            case_r: rt(case_r),
            scrut: rt(p.clone()),
        }),
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(ab_ty(e, p.clone())),
        cod: rty(mot_at(depth, motive, p.shift_local(1), v(0), 1)),
        arg: rt(s),
    }
}

// ---------------------------------------------------------------------------
// Tests — Part A
// ---------------------------------------------------------------------------

/// `[e : Ty 0, x : El e, y : El e]` — `e = Var 2, x = Var 1, y = Var 0`.
fn ab_ctx() -> LocalCtx {
    let g = ext(&nil_ctx(), ty0(), c(1));
    let g = ext(&g, el(v(0)), c(0));
    ext(&g, el(v(1)), c(0))
}

#[test]
fn enum_index_type_and_ctors_check() {
    // Open element code and fields: A(x, y) at AB(Even), B at AB(Odd).
    let g = ab_ctx();
    let (e, x, y) = (v(2), v(1), v(0));
    ck(&g, &a_val(e.clone(), x.clone(), y.clone()), &ab_ty(e.clone(), even()), c(0));
    ck(&g, &triv(), &ab_ty(e.clone(), odd()), c(0));

    // Mismatched index: each constructor at the other's index rejects.
    ck_fails(&g, &a_val(e.clone(), x, y), &ab_ty(e.clone(), odd()), c(0));
    // (B at Even: famAB(Even) is a Σ-code, and ⟨⟩ is not a pair.)
    ck_fails(&g, &triv(), &ab_ty(e, even()), c(0));
}

#[test]
fn enum_index_match_beta_fires() {
    // match (A(x, y)) { A(x', y') ⇒ x' } ≡ x, everything open — Case β on
    // the *index* value, then projections against the pair.
    let g = ab_ctx();
    let (e, x, y) = (v(2), v(1), v(0));
    let elim = ab_elim(
        3,
        &c(0),
        e.clone(),
        &el(v(4)), // M[p, z] = El e, constant (e under p, z)
        v(1),      // (Γ, x', y') ⊢ x'
        x.clone(), // B-arm: irrelevant here, any El e will do
        even(),
        a_val(e.clone(), x.clone(), y),
    );
    conv(&g, &elim, &x, &el(e), c(0));
}

// ---------------------------------------------------------------------------
// Part B — linear recursive declared index. The index is `MyNat`, a declared
// `Nat`-clone lowered exactly as tier 1 lowers it:
//
//   shape = Unit + Unit (tags: inl = Z, inr = S)
//   arity = case(x; z. Nat; 0; 1)
//   MyNat = Wf⁰(x : Unit+Unit). arity
//   mz    = sup_f(inl ⟨⟩; ⟨⟩)          ms(n) = sup_f(inr ⟨⟩; ⟨n, ⟨⟩⟩)
//
// and the family is
//
//   VecF<E> : (n : MyNat) -> Type { NilF : VecF(mz),
//                                   ConsF(n, x: E, xs: VecF(n)) : VecF(ms n) }
//
// famV = elim_Wf at motive `Ty 0`; the S-class branch code is
// `⌜Σ(x : El e). El (ih' fz)⌝` — the recursive field's code is the index
// eliminator's ih at the literal `Fin` position of the pattern variable.
// ---------------------------------------------------------------------------

/// The arity of the shared two-constructor index shape: first constructor
/// nullary, second with `r` recursive arguments. Scoped anywhere; `t` is the
/// scrutinee (the arity's own binder when used as an annotation).
fn arity_at(r: u64, t: Term) -> Term {
    Term::Case {
        lhs_level: c(0),
        rhs_level: c(0),
        motive_level: c(0),
        lhs: rty(unit0()),
        rhs: rty(unit0()),
        motive: rty(Type::Nat),
        case_l: rt(Term::Zero),
        case_r: rt(nat(r)),
        scrut: rt(t),
    }
}

fn arity2(r: u64) -> Term {
    arity_at(r, v(0))
}

/// The declared index type: `Wf⁰(x : Unit+Unit). arity2(r)`. Closed, which
/// keeps every scope computation below honest by construction.
fn wf_idx(r: u64) -> Type {
    Type::Wf { level: c(0), shape: rty(tag2_ty()), arity: rt(arity2(r)) }
}

fn supf_of(r: u64, label: Term, children: Term) -> Term {
    Term::Supf {
        level: c(0),
        shape: rty(tag2_ty()),
        arity: rt(arity2(r)),
        label: rt(label),
        children: rt(children),
    }
}

/// The nullary index constructor: `sup_f(inl ⟨⟩; ⟨⟩)`.
fn widx_c0(r: u64) -> Term {
    supf_of(r, inl_u(triv()), triv())
}

fn mz() -> Term {
    widx_c0(1)
}

/// `ms(n) = sup_f(inr ⟨⟩; ⟨n, ⟨⟩⟩)` — one child in the children vector.
fn ms(n: Term) -> Term {
    supf_of(
        1,
        inr_u(triv()),
        Term::Pair {
            fst_level: c(0),
            snd_level: c(0),
            fst_ty: rty(wf_idx(1)),
            snd_ty: rty(Type::Vec { level: c(0), elem: rty(wf_idx(1)), len: rt(Term::Zero) }),
            fst: rt(n),
            snd: rt(triv()),
        },
    )
}

/// `fz` / `fs` at `Fin(rest+1)` — `Fin(S k) ⇝ Unit + Fin(k)`.
fn fz(rest: u64) -> Term {
    Term::Inl {
        lhs_level: c(0),
        rhs_level: c(0),
        lhs: rty(unit0()),
        rhs: rty(Type::Fin { len: rt(nat(rest)) }),
        val: rt(triv()),
    }
}

fn fs(rest: u64, i: Term) -> Term {
    Term::Inr {
        lhs_level: c(0),
        rhs_level: c(0),
        lhs: rty(unit0()),
        rhs: rty(Type::Fin { len: rt(nat(rest)) }),
        val: rt(i),
    }
}

/// `Π(i : Fin(n̂)). Ty 0` — the refined family-ih type at a literal arity.
fn fam_ih_pi_lit(len: u64) -> Type {
    Type::Pi {
        dom_level: c(0),
        cod_level: c(1),
        dom: rty(Type::Fin { len: rt(nat(len)) }),
        cod: rty(ty0()),
    }
}

/// `Π(i : Fin(arity[t])). Ty 0` for `t` in the current scope.
fn fam_ih_pi_at(r: u64, t: Term) -> Type {
    Type::Pi {
        dom_level: c(0),
        cod_level: c(1),
        dom: rty(Type::Fin { len: rt(arity_at(r, t)) }),
        cod: rty(ty0()),
    }
}

/// The family for a two-class Wf index: `elim_Wf` at motive `Ty 0`. The step
/// cannot use `ih` directly in a branch — its domain `Fin(arity a)` is
/// neutral in `a` — so the `Case` motive is `Π(ih' : Π(i : Fin(arity t)).
/// Ty 0). Ty 0` and each branch receives `ih` at its own constructor-refined
/// arity. Branch codes are scoped `(Γ, a, cs, ih, u, ih')`, `ih' = Var 0`.
fn wf_fam(r: u64, branch_l: Term, branch_r: Term, idx: Term) -> Term {
    // Case motive, scoped (Γ, a, cs, ih, t).
    let case_motive = Type::Pi {
        dom_level: c(1),
        cod_level: c(1),
        dom: rty(fam_ih_pi_at(r, v(0))),
        cod: rty(ty0()),
    };
    let lam = |arity_lit: u64, body: Term| Term::Lam {
        dom_level: c(1),
        cod_level: c(1),
        dom: rty(fam_ih_pi_lit(arity_lit)),
        body: rt(body),
    };
    let inner = Term::Case {
        lhs_level: c(0),
        rhs_level: c(0),
        motive_level: c(1),
        lhs: rty(unit0()),
        rhs: rty(unit0()),
        motive: rty(case_motive),
        case_l: rt(lam(0, branch_l)),
        case_r: rt(lam(r, branch_r)),
        scrut: rt(v(2)),
    };
    let step = Term::App {
        fun: rt(inner),
        dom_level: c(1),
        cod_level: c(1),
        dom: rty(fam_ih_pi_at(r, v(2))),
        cod: rty(ty0()),
        arg: rt(v(0)),
    };
    Term::ElimWf {
        level: c(0),
        motive_level: c(1),
        shape: rty(tag2_ty()),
        arity: rt(arity2(r)),
        motive: rty(ty0()),
        step: rt(step),
        scrut: rt(idx),
    }
}

/// `famV e n : Ty 0`. In the S-branch's Σ-code, `fst` sees `ih' = Var 0`
/// and `snd` binds one more, so there `ih' = Var 1`; `e` sits under
/// `(a, cs, ih, u, ih')` = 5 binders (6 in `snd`).
fn vecf_fam(e: Term, idx: Term) -> Term {
    let ih_at_fz = Term::App {
        fun: rt(v(1)),
        dom_level: c(0),
        cod_level: c(1),
        dom: rty(Type::Fin { len: rt(nat(1)) }),
        cod: rty(ty0()),
        arg: rt(fz(0)),
    };
    wf_fam(
        1,
        Term::TmUnit { level: Level::Zero },
        Term::TmSigma {
            fst_level: c(0),
            snd_level: c(0),
            fst: rt(e.shift_local(5)),
            snd: rt(ih_at_fz),
        },
        idx,
    )
}

fn vecf_ty(e: Term, idx: Term) -> Type {
    el(vecf_fam(e, idx))
}

fn vnilf() -> Term {
    triv()
}

/// `ConsF(n, x, xs) = pair(x; xs)` at `VecF(ms n)` — as in the Nat scheme,
/// the pattern-variable field appears in annotations only.
fn vconsf(e: Term, n: Term, x: Term, xs: Term) -> Term {
    Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(el(e.clone())),
        snd_ty: rty(vecf_ty(e.shift_local(1), n.shift_local(1))),
        fst: rt(x),
        snd: rt(xs),
    }
}

/// §6 instantiated at the declared index: the derived eliminator is
/// `elim_Wf` on the index at motive `Mot(h) = Π(v : El (famV e h)). M[h, v]`,
/// its step the same Case-with-threaded-(cs, ih) device as the family's —
/// here threading both, because the arm needs the pattern variable (a
/// projection of `cs'`) *and* the value-level ih.
///
/// `motive` is scoped `(Γ, h : MyNat, z : El (famV e h))` at level `ml`;
/// `nil_case` in Γ; `cons_case` in `(Γ, n : MyNat, x : El e, xs : VecF(n),
/// ihv : M[n, xs])`. The pattern variable an arm binds is `nth(cs', fz)`
/// ≡ `fst cs'` — recovered by projection, with no inversion machinery.
fn vecf_elim(
    depth: u32,
    ml: &Level,
    e: Term,
    motive: &Type,
    nil_case: Term,
    cons_case: Term,
    idx: Term,
    scrut: Term,
) -> Term {
    let wf = || rty(wf_idx(1));
    let vec_wf = |len: Term| Type::Vec { level: c(0), elem: wf(), len: rt(len) };
    // Mot, scoped (Γ, h): Π(v : El (famV e h)). M[h, v].
    let mot = Type::Pi {
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(vecf_ty(e.clone().shift_local(1), v(0))),
        cod: rty(motive.clone()),
    };
    // Mot at h := w, `extra` binders past Γ.
    let mot_w = |w: Term, extra: u32| {
        mot.apply_local(&LocalSubst::id(&scope(depth)).shift_local(extra).extended(rt(w)))
    };
    let nth_w = |len: Term, cs: Term, i: Term| nth(&c(0), &wf(), &rt(len), rt(cs), rt(i));

    // ---- the step's Case motive, scoped (Γ, a, cs, ih, t) ----
    // Π(cs' : Vec(Wf; arity t)). Π(ih' : Π(i : Fin(arity t)). Mot(nth cs' i)).
    //   Mot(sup_f(t; cs'))
    let case_motive = Type::Pi {
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(vec_wf(arity_at(1, v(0)))),
        cod: rty(Type::Pi {
            // scope (Γ, a, cs, ih, t, cs')
            dom_level: ml.clone(),
            cod_level: ml.clone(),
            dom: rty(Type::Pi {
                dom_level: c(0),
                cod_level: ml.clone(),
                dom: rty(Type::Fin { len: rt(arity_at(1, v(1))) }),
                // scope (Γ, a, cs, ih, t, cs', i)
                cod: rty(mot_w(nth_w(arity_at(1, v(2)), v(1), v(0)), 6)),
            }),
            // scope (Γ, a, cs, ih, t, cs', ih')
            cod: rty(mot_w(supf_of(1, v(2), v(1)), 6)),
        }),
    };

    // ---- case_l, scoped (Γ, a, cs, ih, u) ----
    // λ(cs₀ : Vec(Wf; 0)). λ(ih₀ : …). λ(vz : El (famV (sup_f(inl u; cs₀)))).
    //   nil_case
    // The body's obligation is M[sup_f(inl u; cs₀), vz]; nil_case pays
    // M[mz, ⟨⟩] — convertible by Unit η at u, cs₀ and vz. The index side of
    // the Nat scheme's "Unit η is load-bearing for nullary spines".
    let ih0_ty = Type::Pi {
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(Type::Fin { len: rt(Term::Zero) }),
        // scope (Γ, a, cs, ih, u, cs₀, i)
        cod: rty(mot_w(nth_w(Term::Zero, v(1), v(0)), 6)),
    };
    let case_l = Term::Lam {
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(vec_wf(Term::Zero)),
        body: rt(Term::Lam {
            dom_level: ml.clone(),
            cod_level: ml.clone(),
            dom: rty(ih0_ty),
            body: rt(Term::Lam {
                dom_level: c(0),
                cod_level: ml.clone(),
                // scope (Γ, a, cs, ih, u, cs₀, ih₀): u = 2, cs₀ = 1
                dom: rty(vecf_ty(e.clone().shift_local(6), supf_of(1, inl_u(v(2)), v(1)))),
                body: rt(nil_case.shift_local(7)),
            }),
        }),
    };

    // ---- case_r, scoped (Γ, a, cs, ih, u) ----
    let ih1_ty = Type::Pi {
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(Type::Fin { len: rt(nat(1)) }),
        // scope (Γ, a, cs, ih, u, cs₁, i)
        cod: rty(mot_w(nth_w(nat(1), v(1), v(0)), 6)),
    };
    // Body scope (Γ, a, cs, ih, u, cs₁, ih₁, vc): cs₁ = 2, ih₁ = 1, vc = 0.
    let n_pat = Term::Fst {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: wf(),
        snd_ty: rty(vec_wf(Term::Zero)),
        pair: rt(v(2)),
    };
    let payload_fst_ann = || rty(el(e.clone().shift_local(7)));
    let payload_snd_ann =
        || rty(vecf_ty(e.clone().shift_local(8), n_pat.shift_local(1)));
    let x_proj = Term::Fst {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: payload_fst_ann(),
        snd_ty: payload_snd_ann(),
        pair: rt(v(0)),
    };
    let xs_proj = Term::Snd {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: payload_fst_ann(),
        snd_ty: payload_snd_ann(),
        pair: rt(v(0)),
    };
    // ihv = ih₁ fz xs' : M[nth(cs₁, fz), xs'].
    let ih_fun = Term::App {
        fun: rt(v(1)),
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(Type::Fin { len: rt(nat(1)) }),
        // cod binds i: scope (…, cs₁ = 3, ih₁ = 2, vc = 1, i = 0)
        cod: rty(mot_w(nth_w(nat(1), v(3), v(0)), 8)),
        arg: rt(fz(0)),
    };
    let ihv = Term::App {
        fun: rt(ih_fun),
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(vecf_ty(e.clone().shift_local(7), nth_w(nat(1), v(2), fz(0)))),
        // cod binds the value: scope (…, cs₁ = 3, …, varg = 0)
        cod: rty(mot_at(
            depth,
            motive,
            nth_w(nat(1), v(3), fz(0)),
            v(0),
            8,
        )),
        arg: rt(xs_proj.clone()),
    };
    let case_r_body = cons_case.apply_local(
        &LocalSubst::id(&scope(depth))
            .shift_local(7)
            .extended(rt(n_pat.clone()))
            .extended(rt(x_proj))
            .extended(rt(xs_proj))
            .extended(rt(ihv)),
    );
    let case_r = Term::Lam {
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(vec_wf(nat(1))),
        body: rt(Term::Lam {
            dom_level: ml.clone(),
            cod_level: ml.clone(),
            dom: rty(ih1_ty),
            body: rt(Term::Lam {
                dom_level: c(0),
                cod_level: ml.clone(),
                // scope (Γ, a, cs, ih, u, cs₁, ih₁): u = 2, cs₁ = 1
                dom: rty(vecf_ty(e.clone().shift_local(6), supf_of(1, inr_u(v(2)), v(1)))),
                body: rt(case_r_body),
            }),
        }),
    };

    // ---- the step: Case applied to cs, then ih. Scoped (Γ, a, cs, ih). ----
    let inner = Term::Case {
        lhs_level: c(0),
        rhs_level: c(0),
        motive_level: ml.clone(),
        lhs: rty(unit0()),
        rhs: rty(unit0()),
        motive: rty(case_motive),
        case_l: rt(case_l),
        case_r: rt(case_r),
        scrut: rt(v(2)),
    };
    let app_cs = Term::App {
        fun: rt(inner),
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(vec_wf(arity_at(1, v(2)))),
        // cod binds cs': scope (Γ, a, cs, ih, cs'), a = 3.
        cod: rty(Type::Pi {
            dom_level: ml.clone(),
            cod_level: ml.clone(),
            dom: rty(Type::Pi {
                dom_level: c(0),
                cod_level: ml.clone(),
                dom: rty(Type::Fin { len: rt(arity_at(1, v(3))) }),
                // scope (Γ, a, cs, ih, cs', i)
                cod: rty(mot_w(nth_w(arity_at(1, v(4)), v(1), v(0)), 5)),
            }),
            // scope (Γ, a, cs, ih, cs', ih')
            cod: rty(mot_w(supf_of(1, v(4), v(1)), 5)),
        }),
        arg: rt(v(1)),
    };
    let step = Term::App {
        fun: rt(app_cs),
        dom_level: ml.clone(),
        cod_level: ml.clone(),
        // ih's own type, scoped (Γ, a, cs, ih): Π(i : Fin(arity a)). Mot(nth cs i).
        dom: rty(Type::Pi {
            dom_level: c(0),
            cod_level: ml.clone(),
            dom: rty(Type::Fin { len: rt(arity_at(1, v(2))) }),
            // scope (Γ, a, cs, ih, i)
            cod: rty(mot_w(nth_w(arity_at(1, v(3)), v(2), v(0)), 4)),
        }),
        // cod binds the ih argument: scope (Γ, a, cs, ih, arg), a = 3, cs = 2.
        cod: rty(mot_w(supf_of(1, v(3), v(2)), 4)),
        arg: rt(v(0)),
    };

    // ---- the recursion applied to the scrutinee ----
    Term::App {
        fun: rt(Term::ElimWf {
            level: c(0),
            motive_level: ml.clone(),
            shape: rty(tag2_ty()),
            arity: rt(arity2(1)),
            motive: rty(mot),
            step: rt(step),
            scrut: rt(idx.clone()),
        }),
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(vecf_ty(e, idx.clone())),
        cod: rty(mot_at(depth, motive, idx.shift_local(1), v(0), 1)),
        arg: rt(scrut),
    }
}

// ---------------------------------------------------------------------------
// Tests — Part B
// ---------------------------------------------------------------------------

/// `[e : Ty 0, n : MyNat, x : El e, xs : VecF<e>(n)]` — everything open.
fn vecf_ctx() -> LocalCtx {
    let g = ext(&nil_ctx(), ty0(), c(1));
    let g = ext(&g, wf_idx(1), c(0));
    let g = ext(&g, el(v(1)), c(0));
    ext(&g, vecf_ty(v(2), v(1)), c(0))
}

/// A closed `MyNat` literal.
fn mnat(n: u64) -> Term {
    let mut t = mz();
    for _ in 0..n {
        t = ms(t);
    }
    t
}

#[test]
fn wf_index_type_and_ctors_check() {
    // The index declaration itself checks: mz and ms(n) at MyNat, n open.
    let g = ext(&nil_ctx(), wf_idx(1), c(0));
    ck(&g, &mz(), &wf_idx(1), c(0));
    ck(&g, &ms(v(0)), &wf_idx(1), c(0));

    // Closed family values at their exact indices.
    ck(&nil_ctx(), &vnilf(), &vecf_ty(Term::TmNat, mz()), c(0));
    let two = vconsf(
        Term::TmNat,
        mnat(1),
        nat(4),
        vconsf(Term::TmNat, mnat(0), nat(5), vnilf()),
    );
    ck(&nil_ctx(), &two, &vecf_ty(Term::TmNat, mnat(2)), c(0));

    // The §5 claim at a declared index: ConsF checks with element code,
    // index, element and tail all open — famV (ms n) unfolds whatever n is,
    // because ms(n) is sup_f-headed and elim_Wf β fires.
    let g = vecf_ctx();
    let (e, n, x, xs) = (v(3), v(2), v(1), v(0));
    ck(&g, &vconsf(e.clone(), n.clone(), x, xs), &vecf_ty(e, ms(n)), c(0));
}

#[test]
fn wf_index_beta_fires_on_fully_open_data() {
    // §6.2 at a declared index: match (ConsF(n, x, xs)) { ConsF(n', x', xs')
    // ⇒ x' } ≡ x with n, x, xs (and e) all variables.
    let g = vecf_ctx();
    let (e, n, x, xs) = (v(3), v(2), v(1), v(0));
    let elim = vecf_elim(
        4,
        &c(0),
        e.clone(),
        &el(v(5)), // M[h, z] = El e, constant
        x.clone(), // nil arm: irrelevant, any El e will do
        v(2),      // (Γ, n', x', xs', ihv) ⊢ x'
        ms(n.clone()),
        vconsf(e.clone(), n.clone(), x.clone(), xs),
    );
    conv(&g, &elim, &x, &el(e), c(0));
}

#[test]
fn wf_index_arm_recovers_the_pattern_variable() {
    // The pattern variable is nth(cs', fz) ≡ fst cs' — recovered by
    // projection out of the index constructor's children, no inversion.
    let g = vecf_ctx();
    let (e, n, x, xs) = (v(3), v(2), v(1), v(0));
    let elim = |arm: Term| {
        vecf_elim(
            4,
            &c(0),
            e.clone(),
            &wf_idx(1), // M[h, z] = MyNat, constant
            mz(),
            arm,
            ms(n.clone()),
            vconsf(e.clone(), n.clone(), x.clone(), xs.clone()),
        )
    };
    // (Γ, n', x', xs', ihv) ⊢ n' ≡ n.
    conv(&g, &elim(v(3)), &n, &wf_idx(1), c(0));
    // Negative: the recovered variable is the index, not its successor.
    not_conv(&g, &elim(v(3)), &ms(n.clone()), &wf_idx(1), c(0));

    // lenF computes on closed data: arm = S ihv, into kernel Nat.
    let two = vconsf(
        Term::TmNat,
        mnat(1),
        nat(4),
        vconsf(Term::TmNat, mnat(0), nat(5), vnilf()),
    );
    let len = vecf_elim(
        0,
        &c(0),
        Term::TmNat,
        &Type::Nat,
        Term::Zero,
        Term::Succ(rt(v(0))),
        mnat(2),
        two,
    );
    conv(&nil_ctx(), &len, &nat(2), &Type::Nat, c(0));
}

#[test]
fn wf_index_gate_rejects_the_near_misses() {
    let g = vecf_ctx();
    let (e, n, x, xs) = (v(3), v(2), v(1), v(0));

    // ConsF at index mz: famV unfolds to ⌜Unit⌝, a pair is rejected.
    ck_fails(&g, &vconsf(e.clone(), n.clone(), x.clone(), xs.clone()), &vecf_ty(e.clone(), mz()), c(0));
    // ConsF at the neutral index n: the family is stuck, a canonical pair
    // does not inhabit it.
    ck_fails(&g, &vconsf(e.clone(), n.clone(), x.clone(), xs.clone()), &vecf_ty(e.clone(), n.clone()), c(0));
    // NilF at a successor index.
    ck_fails(&g, &vnilf(), &vecf_ty(e.clone(), ms(n.clone())), c(0));

    // Cross-class equations fail to state (§7 at a declared index).
    ty_fails(
        &g,
        &Type::Id {
            level: c(0),
            ty: rty(vecf_ty(e.clone(), mz())),
            lhs: rt(vnilf()),
            rhs: rt(vconsf(e, n, x, xs)),
        },
        c(0),
    );
}

// ---------------------------------------------------------------------------
// Part C — branching recursive declared index. The index is
//
//   Shape { SLeaf, SNode(l: Shape, r: Shape) }        (arity 2)
//
// and the family is the derivation-shaped
//
//   Bal : (s : Shape) -> Type { BLeaf : Bal(SLeaf),
//                               BNode(l, r, dl: Bal(l), dr: Bal(r)) :
//                                 Bal(SNode(l, r)) }
//
// — two pattern variables, two recursive fields, each at a *different*
// pattern variable, so each draws its code from `ih` at a different `Fin`
// literal. This is "rec at each recursive argument of the index
// constructor" (§8.2) in full, and the miniature of a typing judgment
// recursing on subterms of its subject.
// ---------------------------------------------------------------------------

fn sleaf() -> Term {
    widx_c0(2)
}

/// `SNode(l, r) = sup_f(inr ⟨⟩; ⟨l, ⟨r, ⟨⟩⟩⟩)` — two children.
fn snode(l: Term, r: Term) -> Term {
    let wf2 = || rty(wf_idx(2));
    supf_of(
        2,
        inr_u(triv()),
        Term::Pair {
            fst_level: c(0),
            snd_level: c(0),
            fst_ty: wf2(),
            snd_ty: rty(Type::Vec { level: c(0), elem: wf2(), len: rt(nat(1)) }),
            fst: rt(l),
            snd: rt(Term::Pair {
                fst_level: c(0),
                snd_level: c(0),
                fst_ty: wf2(),
                snd_ty: rty(Type::Vec { level: c(0), elem: wf2(), len: rt(Term::Zero) }),
                fst: rt(r),
                snd: rt(triv()),
            }),
        },
    )
}

/// `famBal s : Ty 0`. The SNode-class branch is
/// `⌜Σ(dl : El (ih' fz)). El (ih' (fs fz))⌝` — in the Σ-code's `fst` the
/// refined ih is `Var 0`, in its `snd` it is `Var 1`.
fn bal_fam(idx: Term) -> Term {
    let ih_at = |ih_var: u32, i: Term| Term::App {
        fun: rt(v(ih_var)),
        dom_level: c(0),
        cod_level: c(1),
        dom: rty(Type::Fin { len: rt(nat(2)) }),
        cod: rty(ty0()),
        arg: rt(i),
    };
    wf_fam(
        2,
        Term::TmUnit { level: Level::Zero },
        Term::TmSigma {
            fst_level: c(0),
            snd_level: c(0),
            fst: rt(ih_at(0, fz(1))),
            snd: rt(ih_at(1, fs(1, fz(0)))),
        },
        idx,
    )
}

fn bal_ty(idx: Term) -> Type {
    el(bal_fam(idx))
}

fn bleaf() -> Term {
    triv()
}

/// `BNode(l, r, dl, dr) = pair(dl; dr)` at `Bal(SNode(l, r))` — both
/// pattern-variable fields erased, both children open.
fn bnode(l: Term, r: Term, dl: Term, dr: Term) -> Term {
    Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(bal_ty(l)),
        snd_ty: rty(bal_ty(r.shift_local(1))),
        fst: rt(dl),
        snd: rt(dr),
    }
}

/// The `Bal` eliminator — `vecf_elim`'s shape at arity 2. `node_case` is
/// scoped `(Γ, l, r, dl, dr, ihl, ihr)`: two pattern variables (`nth(cs',
/// fz)` and `nth(cs', fs fz)`, i.e. the two projections of the index
/// constructor's children), two value ihs, each from the *same* threaded
/// `ih` at its own `Fin` literal.
fn bal_elim(
    depth: u32,
    ml: &Level,
    motive: &Type,
    leaf_case: Term,
    node_case: Term,
    idx: Term,
    scrut: Term,
) -> Term {
    let wf = || rty(wf_idx(2));
    let vec_wf = |len: Term| Type::Vec { level: c(0), elem: wf(), len: rt(len) };
    let mot = Type::Pi {
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(bal_ty(v(0))),
        cod: rty(motive.clone()),
    };
    let mot_w = |w: Term, extra: u32| {
        mot.apply_local(&LocalSubst::id(&scope(depth)).shift_local(extra).extended(rt(w)))
    };
    let nth_w = |len: Term, cs: Term, i: Term| nth(&c(0), &wf(), &rt(len), rt(cs), rt(i));

    // Case motive, scoped (Γ, a, cs, ih, t).
    let case_motive = Type::Pi {
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(vec_wf(arity_at(2, v(0)))),
        cod: rty(Type::Pi {
            dom_level: ml.clone(),
            cod_level: ml.clone(),
            dom: rty(Type::Pi {
                dom_level: c(0),
                cod_level: ml.clone(),
                dom: rty(Type::Fin { len: rt(arity_at(2, v(1))) }),
                cod: rty(mot_w(nth_w(arity_at(2, v(2)), v(1), v(0)), 6)),
            }),
            cod: rty(mot_w(supf_of(2, v(2), v(1)), 6)),
        }),
    };

    // case_l, scoped (Γ, a, cs, ih, u) — Unit η pays the index identity.
    let ih0_ty = Type::Pi {
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(Type::Fin { len: rt(Term::Zero) }),
        cod: rty(mot_w(nth_w(Term::Zero, v(1), v(0)), 6)),
    };
    let case_l = Term::Lam {
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(vec_wf(Term::Zero)),
        body: rt(Term::Lam {
            dom_level: ml.clone(),
            cod_level: ml.clone(),
            dom: rty(ih0_ty),
            body: rt(Term::Lam {
                dom_level: c(0),
                cod_level: ml.clone(),
                dom: rty(bal_ty(supf_of(2, inl_u(v(2)), v(1)))),
                body: rt(leaf_case.shift_local(7)),
            }),
        }),
    };

    // case_r, scoped (Γ, a, cs, ih, u).
    let ih1_ty = Type::Pi {
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(Type::Fin { len: rt(nat(2)) }),
        cod: rty(mot_w(nth_w(nat(2), v(1), v(0)), 6)),
    };
    // Body scope (Γ, a, cs, ih, u, cs₁, ih₁, vc): cs₁ = 2, ih₁ = 1, vc = 0.
    let l_pat = Term::Fst {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: wf(),
        snd_ty: rty(vec_wf(nat(1))),
        pair: rt(v(2)),
    };
    let r_pat = Term::Fst {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: wf(),
        snd_ty: rty(vec_wf(Term::Zero)),
        pair: rt(Term::Snd {
            fst_level: c(0),
            snd_level: c(0),
            fst_ty: wf(),
            snd_ty: rty(vec_wf(nat(1))),
            pair: rt(v(2)),
        }),
    };
    let payload_fst_ann = || rty(bal_ty(l_pat.clone()));
    let payload_snd_ann = || rty(bal_ty(r_pat.shift_local(1)));
    let dl_proj = Term::Fst {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: payload_fst_ann(),
        snd_ty: payload_snd_ann(),
        pair: rt(v(0)),
    };
    let dr_proj = Term::Snd {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: payload_fst_ann(),
        snd_ty: payload_snd_ann(),
        pair: rt(v(0)),
    };
    // One value ih per recursive field: the same threaded ih₁ at a
    // different Fin literal, applied to that field's stored derivation.
    let ih_at = |i: Term, deriv: &Term| {
        let fun = Term::App {
            fun: rt(v(1)),
            dom_level: c(0),
            cod_level: ml.clone(),
            dom: rty(Type::Fin { len: rt(nat(2)) }),
            cod: rty(mot_w(nth_w(nat(2), v(3), v(0)), 8)),
            arg: rt(i.clone()),
        };
        Term::App {
            fun: rt(fun),
            dom_level: c(0),
            cod_level: ml.clone(),
            dom: rty(bal_ty(nth_w(nat(2), v(2), i.clone()))),
            cod: rty(mot_at(depth, motive, nth_w(nat(2), v(3), i), v(0), 8)),
            arg: rt(deriv.clone()),
        }
    };
    let ihl = ih_at(fz(1), &dl_proj);
    let ihr = ih_at(fs(1, fz(0)), &dr_proj);
    let case_r_body = node_case.apply_local(
        &LocalSubst::id(&scope(depth))
            .shift_local(7)
            .extended(rt(l_pat.clone()))
            .extended(rt(r_pat.clone()))
            .extended(rt(dl_proj))
            .extended(rt(dr_proj))
            .extended(rt(ihl))
            .extended(rt(ihr)),
    );
    let case_r = Term::Lam {
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(vec_wf(nat(1))),
        body: rt(Term::Lam {
            dom_level: ml.clone(),
            cod_level: ml.clone(),
            dom: rty(ih1_ty),
            body: rt(Term::Lam {
                dom_level: c(0),
                cod_level: ml.clone(),
                dom: rty(bal_ty(supf_of(2, inr_u(v(2)), v(1)))),
                body: rt(case_r_body),
            }),
        }),
    };

    // The step: Case applied to cs, then ih. Scoped (Γ, a, cs, ih).
    let inner = Term::Case {
        lhs_level: c(0),
        rhs_level: c(0),
        motive_level: ml.clone(),
        lhs: rty(unit0()),
        rhs: rty(unit0()),
        motive: rty(case_motive),
        case_l: rt(case_l),
        case_r: rt(case_r),
        scrut: rt(v(2)),
    };
    let app_cs = Term::App {
        fun: rt(inner),
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(vec_wf(arity_at(2, v(2)))),
        cod: rty(Type::Pi {
            dom_level: ml.clone(),
            cod_level: ml.clone(),
            dom: rty(Type::Pi {
                dom_level: c(0),
                cod_level: ml.clone(),
                dom: rty(Type::Fin { len: rt(arity_at(2, v(3))) }),
                cod: rty(mot_w(nth_w(arity_at(2, v(4)), v(1), v(0)), 5)),
            }),
            cod: rty(mot_w(supf_of(2, v(4), v(1)), 5)),
        }),
        arg: rt(v(1)),
    };
    let step = Term::App {
        fun: rt(app_cs),
        dom_level: ml.clone(),
        cod_level: ml.clone(),
        dom: rty(Type::Pi {
            dom_level: c(0),
            cod_level: ml.clone(),
            dom: rty(Type::Fin { len: rt(arity_at(2, v(2))) }),
            cod: rty(mot_w(nth_w(arity_at(2, v(3)), v(2), v(0)), 4)),
        }),
        cod: rty(mot_w(supf_of(2, v(3), v(2)), 4)),
        arg: rt(v(0)),
    };

    Term::App {
        fun: rt(Term::ElimWf {
            level: c(0),
            motive_level: ml.clone(),
            shape: rty(tag2_ty()),
            arity: rt(arity2(2)),
            motive: rty(mot),
            step: rt(step),
            scrut: rt(idx.clone()),
        }),
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(bal_ty(idx.clone())),
        cod: rty(mot_at(depth, motive, idx.shift_local(1), v(0), 1)),
        arg: rt(scrut),
    }
}

/// `plus`, recursing on its first argument (as in `indexed_route1.rs`).
fn plus(a: Term, b: Term) -> Term {
    Term::ElimNat {
        level: c(0),
        motive: rty(Type::Nat),
        base: rt(b),
        step: rt(Term::Succ(rt(v(0)))),
        scrut: rt(a),
    }
}

// ---------------------------------------------------------------------------
// Tests — Part C
// ---------------------------------------------------------------------------

/// `[l : Shape, r : Shape, dl : Bal(l), dr : Bal(r)]` — everything open.
fn bal_ctx() -> LocalCtx {
    let g = ext(&nil_ctx(), wf_idx(2), c(0));
    let g = ext(&g, wf_idx(2), c(0));
    let g = ext(&g, bal_ty(v(1)), c(0));
    ext(&g, bal_ty(v(1)), c(0))
}

#[test]
fn branching_index_type_and_ctors_check() {
    // The index itself: SNode(l, r) at Shape with both children open.
    let g = ext(&nil_ctx(), wf_idx(2), c(0));
    let g2 = ext(&g, wf_idx(2), c(0));
    ck(&g2, &snode(v(1), v(0)), &wf_idx(2), c(0));

    // Closed derivation at its exact index.
    let d1 = bnode(sleaf(), sleaf(), bleaf(), bleaf());
    ck(&nil_ctx(), &d1, &bal_ty(snode(sleaf(), sleaf())), c(0));

    // Open everything: two pattern variables, two recursive fields —
    // famBal (SNode(l, r)) unfolds whatever l and r are, and both stored
    // derivations check at their own pattern variable's family instance.
    let g = bal_ctx();
    let (l, r, dl, dr) = (v(3), v(2), v(1), v(0));
    ck(
        &g,
        &bnode(l.clone(), r.clone(), dl.clone(), dr.clone()),
        &bal_ty(snode(l.clone(), r.clone())),
        c(0),
    );

    // Near misses: BNode at the leaf index; BLeaf at a node index; and a
    // derivation stored under the *wrong* pattern variable (dr at dl's
    // position, distinct open subjects).
    ck_fails(&g, &bnode(l.clone(), r.clone(), dl.clone(), dr.clone()), &bal_ty(sleaf()), c(0));
    ck_fails(&g, &bleaf(), &bal_ty(snode(l.clone(), r.clone())), c(0));
    ck_fails(&g, &bnode(l.clone(), r.clone(), dr.clone(), dl.clone()), &bal_ty(snode(l, r)), c(0));
}

#[test]
fn branching_index_both_ihs_engage_and_beta_fires() {
    // count : Bal(s) → Nat, leaf ↦ 1, node ↦ ihl + ihr — an arm that uses
    // both value ihs, drawn from the same threaded ih at two Fin literals.
    let count = |depth: u32, idx: Term, d: Term| {
        bal_elim(
            depth,
            &c(0),
            &Type::Nat,
            nat(1),
            plus(v(1), v(0)), // (Γ, l', r', dl', dr', ihl, ihr) ⊢ ihl + ihr
            idx,
            d,
        )
    };

    // Closed: the two-leaf derivation counts 2.
    let d1 = bnode(sleaf(), sleaf(), bleaf(), bleaf());
    let closed = count(0, snode(sleaf(), sleaf()), d1);
    conv(&nil_ctx(), &closed, &nat(2), &Type::Nat, c(0));

    // Open: count (BNode(l, r, dl, dr)) ≡ count dl + count dr with the
    // subjects and both derivations all variables — β through a branching
    // *index* constructor, both ihs synthesized.
    let g = bal_ctx();
    let (l, r, dl, dr) = (v(3), v(2), v(1), v(0));
    let lhs = count(4, snode(l.clone(), r.clone()), bnode(l.clone(), r.clone(), dl.clone(), dr.clone()));
    let rhs = plus(count(4, l, dl), count(4, r, dr));
    conv(&g, &lhs, &rhs, &Type::Nat, c(0));
}

#[test]
fn enum_index_cross_class_equations_fail_to_state() {
    // A and B live at different indices, so no common type states their
    // equation — at either index one side fails to check.
    let g = ab_ctx();
    let (e, x, y) = (v(2), v(1), v(0));
    ty_fails(
        &g,
        &Type::Id {
            level: c(0),
            ty: rty(ab_ty(e.clone(), even())),
            lhs: rt(a_val(e, x, y)),
            rhs: rt(triv()),
        },
        c(0),
    );
}
