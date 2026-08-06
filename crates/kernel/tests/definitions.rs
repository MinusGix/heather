//! Bodied global definitions and δ-reduction (extension,
//! issues/simulate-conversion-cost.md): `u : Trm_c(Δ ⊢ T @ l) := t`.
//!
//! The property under test is not "δ works" but **layer-indexed
//! transparency**, so every positive here has its opacity twin:
//!
//! - the body unfolds at the computing layers p/m — closed *and* under a
//!   neutral argument, in a *type* through `El`, and in a **checking**
//!   position (`check_term`), not only in a conversion query;
//! - it never unfolds at c, where a global is syntax: `box(u^δ)` compares
//!   syntactically, unequal to `box(body)`, and the code recursors stay
//!   blocked on it exactly as on a declaration;
//! - the Ψ-free entry points (`whnf_term`, `step_term`) are what layer c
//!   uses and unfold nothing at all.
//!
//! Negative controls throughout: a *declaration* of the same type never
//! converts with the value a definition would, and two definitions with
//! different bodies stay apart.

use std::rc::Rc;

use heather_kernel::conv::{conv_term, conv_type, ConvError};
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::reduce::{
    is_neutral_term, step_term, whnf_term, whnf_term_delta, whnf_type_delta, Defs,
};
use heather_kernel::term::{
    Branches, CtxBase, CtxEntry, GlobalBinding, GlobalCtx, GlobalVar, LocalCtx, LocalSubst,
    LocalVar, Motives, SubstTail, Term, Type,
};
use heather_kernel::typing::{check_global_ctx, check_term, TypeError};

const FUEL: u64 = 100_000;

// -------------------------------------------------------------------------
// Construction helpers (mirroring tests/conv.rs)
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

fn nil_ctx(n: u32) -> LocalCtx {
    LocalCtx {
        base: CtxBase::Nil,
        entries: ((0..n)
            .map(|_| CtxEntry { ty: rty(Type::Nat), level: Level::Zero })
            .collect::<Vec<_>>()).into(),
    }
}

fn num(n: u32) -> Term {
    let mut t = Term::Zero;
    for _ in 0..n {
        t = Term::Succ(rt(t));
    }
    t
}

/// `Π^{0,0}(x : Nat). Nat`.
fn nat_to_nat() -> Type {
    Type::Pi {
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: rty(Type::Nat),
        cod: rty(Type::Nat),
    }
}

fn lam(body: Term) -> Term {
    Term::Lam {
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: rty(Type::Nat),
        body: rt(body),
    }
}

fn app(f: Term, a: Term) -> Term {
    Term::App {
        fun: rt(f),
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: rty(Type::Nat),
        cod: rty(Type::Nat),
        arg: rt(a),
    }
}

/// `u_var^{·^k}` out of a Γ of `k` entries — every binding here is closed.
fn glob(var: u32, k: u32) -> Term {
    Term::GlobalTm {
        var: GlobalVar(var),
        subst: LocalSubst {
            tail: SubstTail::Empty { len: k, base: CtxBase::Nil },
            terms: vec![],
        },
    }
}

/// `u : Trm_c(· ⊢ ty @ 0) := body`, or a declaration when `body` is `None`.
fn binding(ty: Type, body: Option<Term>) -> GlobalBinding {
    GlobalBinding::Tm {
        ctx: nil_ctx(0),
        layer: Layer::Code,
        ty: rty(ty),
        level: Level::Zero,
        body: body.map(rt),
    }
}

fn psi(bindings: Vec<GlobalBinding>) -> GlobalCtx {
    GlobalCtx::new(bindings)
}

/// `two := 2 : Nat` and `succ2 := λx. Succ (Succ x) : Nat → Nat`; index 1 is
/// `two`, index 0 is `succ2`.
fn defs_psi() -> GlobalCtx {
    psi(vec![
        binding(Type::Nat, Some(num(2))),
        binding(nat_to_nat(), Some(lam(Term::Succ(rt(Term::Succ(rt(v(0)))))))),
    ])
}

/// The same shapes, declared and not defined — the negative control for
/// every unfolding test below.
fn opaque_psi() -> GlobalCtx {
    psi(vec![binding(Type::Nat, None), binding(nat_to_nat(), None)])
}

fn ok_tm(p: &GlobalCtx, g: &LocalCtx, a: &Term, b: &Term, ty: &Type) {
    assert_eq!(conv_term(p, g, Layer::Prog, a, b, ty, &c(0), FUEL), Ok(()));
}

fn no_tm(p: &GlobalCtx, g: &LocalCtx, a: &Term, b: &Term, ty: &Type) {
    assert_eq!(
        conv_term(p, g, Layer::Prog, a, b, ty, &c(0), FUEL),
        Err(ConvError::NotConvertible)
    );
}

// -------------------------------------------------------------------------
// (a) δ at the computing layers
// -------------------------------------------------------------------------

#[test]
fn a_definition_converts_with_its_body_at_p() {
    let p = defs_psi();
    let g = nil_ctx(0);
    // Closed: `two^· ≈ 2`, and by transitivity through β `succ2^· 0 ≈ 2`.
    ok_tm(&p, &g, &glob(1, 0), &num(2), &Type::Nat);
    ok_tm(&p, &g, &num(2), &glob(1, 0), &Type::Nat);
    ok_tm(&p, &g, &app(glob(0, 0), Term::Zero), &num(2), &Type::Nat);
    // …and the two definitions agree with each other, which needs *both*
    // unfolded.
    ok_tm(&p, &g, &app(glob(0, 0), Term::Zero), &glob(1, 0), &Type::Nat);
    // Negative control: the wrong numeral is still wrong.
    no_tm(&p, &g, &glob(1, 0), &num(3), &Type::Nat);
}

#[test]
fn a_declaration_of_the_same_type_does_not_unfold() {
    // The control that makes the test above about *bodies* and not about
    // globals: identical Ψ shapes, no bodies, nothing converts.
    let p = opaque_psi();
    let g = nil_ctx(0);
    no_tm(&p, &g, &glob(1, 0), &num(2), &Type::Nat);
    no_tm(&p, &g, &app(glob(0, 0), Term::Zero), &num(2), &Type::Nat);
    // A declaration is still convertible with *itself*.
    ok_tm(&p, &g, &glob(1, 0), &glob(1, 0), &Type::Nat);
}

#[test]
fn a_definition_unfolds_under_a_neutral_argument() {
    // The open axis (docs/testing-generated-terms.md): the argument is a
    // *variable*, so nothing computes to a literal and the equation is only
    // available through δ plus β.
    let p = defs_psi();
    let g = nil_ctx(1);
    let expect = Term::Succ(rt(Term::Succ(rt(v(0)))));
    ok_tm(&p, &g, &app(glob(0, 1), v(0)), &expect, &Type::Nat);
    // Negative control at the same neutral: one Succ short.
    no_tm(&p, &g, &app(glob(0, 1), v(0)), &Term::Succ(rt(v(0))), &Type::Nat);
    // And with no body, the application is a neutral that converts only
    // with itself.
    let q = opaque_psi();
    no_tm(&q, &g, &app(glob(0, 1), v(0)), &expect, &Type::Nat);
    ok_tm(&q, &g, &app(glob(0, 1), v(0)), &app(glob(0, 1), v(0)), &Type::Nat);
}

#[test]
fn a_definition_unfolds_inside_a_type() {
    // A type reaches a definition through `El` only — `U^δ` has no body.
    // `code := Nat : Ty 0`, so `El^0 (code^·) ≈ Nat @ 1`.
    let p = psi(vec![GlobalBinding::Tm {
        ctx: nil_ctx(0),
        layer: Layer::Code,
        ty: rty(Type::Ty(Level::Zero)),
        level: Level::constant(1),
        body: Some(rt(Term::TmNat)),
    }]);
    let g = nil_ctx(0);
    let el = Type::El { level: Level::Zero, tm: rt(glob(0, 0)) };
    assert_eq!(conv_type(&p, &g, Layer::Prog, &el, &Type::Nat, &c(0), FUEL), Ok(()));
    // whnf agrees, and only with δ.
    assert_eq!(
        whnf_type_delta(&el, &g, Defs::transparent(&p), FUEL),
        Ok(Type::Nat)
    );
    assert_eq!(whnf_type_delta(&el, &g, Defs::opaque(), FUEL), Ok(el.clone()));
    // Negative control: without the body the `El` is a neutral type.
    let q = psi(vec![GlobalBinding::Tm {
        ctx: nil_ctx(0),
        layer: Layer::Code,
        ty: rty(Type::Ty(Level::Zero)),
        level: Level::constant(1),
        body: None,
    }]);
    assert_eq!(
        conv_type(&q, &g, Layer::Prog, &el, &Type::Nat, &c(0), FUEL),
        Err(ConvError::NotConvertible)
    );
}

#[test]
fn a_definition_unfolds_in_checking_position() {
    // Not a conversion query but the *checker*: `refl` at `Id(Nat; two^·; 2)`
    // synthesizes `Id(Nat; two^·; two^·)` and is accepted only because
    // checking it goes through conversion on the endpoints.
    let p = defs_psi();
    let g = nil_ctx(0);
    let id_ty = |lhs: Term, rhs: Term| Type::Id {
        level: Level::Zero,
        ty: rty(Type::Nat),
        lhs: rt(lhs),
        rhs: rt(rhs),
    };
    let refl = Term::Refl { level: Level::Zero, ty: rty(Type::Nat), tm: rt(glob(1, 0)) };
    assert_eq!(
        check_term(&p, 0, Layer::Prog, &g, &refl, &id_ty(glob(1, 0), num(2)), &c(0), FUEL),
        Ok(())
    );
    // Negative control: a false endpoint is rejected, and the *same* claim
    // over a declaration is rejected too.
    assert_eq!(
        check_term(&p, 0, Layer::Prog, &g, &refl, &id_ty(glob(1, 0), num(3)), &c(0), FUEL),
        Err(TypeError::NotConvertible)
    );
    let q = opaque_psi();
    let refl_q = Term::Refl { level: Level::Zero, ty: rty(Type::Nat), tm: rt(glob(1, 0)) };
    assert_eq!(
        check_term(&q, 0, Layer::Prog, &g, &refl_q, &id_ty(glob(1, 0), num(2)), &c(0), FUEL),
        Err(TypeError::NotConvertible)
    );
}

// -------------------------------------------------------------------------
// The δ-lazy order: spines before bodies
// -------------------------------------------------------------------------

/// `slow := λx. (λa.a) ((λa.a) (… 40 deep … x))` — a body whose whnf costs
/// forty head steps, so "did we unfold?" is legible in the fuel.
fn slow_psi() -> GlobalCtx {
    let mut e = v(0);
    for _ in 0..40 {
        e = app(lam(v(0)), e);
    }
    psi(vec![binding(nat_to_nat(), Some(lam(e)))])
}

#[test]
fn a_shared_definition_head_settles_on_its_spine() {
    // `slow^· x ≈ slow^· x` at a neutral `x` is decided by comparing the
    // spines. Unfolding would answer too, so the observable is the budget:
    // with 40 fuel the spine comparison succeeds while the query that has
    // no choice but to unfold — the same head against its own body — runs
    // out. That is the δ-lazy order, and nothing else explains the split.
    let p = slow_psi();
    let g = nil_ctx(2);
    let q = |a: Term, b: Term, fuel: u64| {
        conv_term(&p, &g, Layer::Prog, &a, &b, &Type::Nat, &c(0), fuel)
    };
    assert_eq!(q(app(glob(0, 2), v(0)), app(glob(0, 2), v(0)), 40), Ok(()));
    assert_eq!(q(app(glob(0, 2), v(0)), v(0), 40), Err(ConvError::OutOfFuel));
    // With a real budget the unfolding answer is the right one, and the
    // δ-lazy attempt that failed first did not corrupt it.
    assert_eq!(q(app(glob(0, 2), v(0)), v(0), FUEL), Ok(()));
    // Different arguments: the spine comparison fails, δ fires on both
    // sides, and two distinct variables are still distinct.
    assert_eq!(
        q(app(glob(0, 2), v(0)), app(glob(0, 2), v(1)), FUEL),
        Err(ConvError::NotConvertible)
    );
}

// -------------------------------------------------------------------------
// (b) layer c: a global is syntax
// -------------------------------------------------------------------------

#[test]
fn a_boxed_definition_is_not_its_boxed_body() {
    // The coherence invariant (ch. 06 compares boxed globals syntactically;
    // DESIGN.md's "boxed types/terms compare syntactically"). If δ reached
    // through `□`, these two would convert — and the code recursor below
    // would still tell them apart.
    let p = defs_psi();
    let g = nil_ctx(0);
    let code_ty = Type::CodeTm {
        ctx: nil_ctx(0),
        level: Level::Zero,
        ty: rty(Type::Nat),
    };
    let boxed_u = Term::BoxTm(rt(glob(1, 0)));
    let boxed_body = Term::BoxTm(rt(num(2)));
    assert_eq!(
        conv_term(&p, &g, Layer::Meta, &boxed_u, &boxed_body, &code_ty, &c(0), FUEL),
        Err(ConvError::NotConvertible)
    );
    // …while each is convertible with itself, so the rejection is about δ
    // and not about `box` comparison being broken.
    assert_eq!(
        conv_term(&p, &g, Layer::Meta, &boxed_u, &boxed_u, &code_ty, &c(0), FUEL),
        Ok(())
    );
    assert_eq!(
        conv_term(&p, &g, Layer::Meta, &boxed_body, &boxed_body, &code_ty, &c(0), FUEL),
        Ok(())
    );
    // And the definition *outside* the box does convert with its body —
    // the same two terms, one layer down.
    ok_tm(&p, &g, &glob(1, 0), &num(2), &Type::Nat);
}

#[test]
fn the_code_recursor_still_sees_a_definition_as_a_global() {
    // ch. 06 blocks the recursion principles on global variables. A body
    // must not unblock them: `elim^Trm (box (u^·))` is neutral, steps
    // nowhere, and two of them are told apart by *which* global they carry.
    let p = defs_psi();
    let g = nil_ctx(0);
    let elim = |var: u32| Term::ElimCodeTm {
        ty_motive_level: Level::Zero,
        tm_motive_level: Level::Zero,
        motives: Rc::new(Motives { ty_motive: rty(Type::Nat), tm_motive: rty(Type::Nat) }),
        branches: const_branches(Term::Zero),
        code_level: Level::Zero,
        ctx: nil_ctx(0),
        ty: rty(Type::Nat),
        scrut: rt(Term::BoxTm(rt(glob(var, 0)))),
    };
    assert_eq!(step_term(&elim(1), &g), None);
    assert_eq!(
        whnf_term_delta(&elim(1), &g, Defs::transparent(&p), FUEL),
        Ok(elim(1))
    );
    assert!(is_neutral_term(&elim(1)));
    assert_eq!(
        conv_term(&p, &g, Layer::Meta, &elim(1), &elim(1), &Type::Nat, &c(0), FUEL),
        Ok(())
    );
    // Both globals are defined, and their bodies have different types — so
    // if δ reached the scrutinee at all, this would not be a clean
    // "different global" rejection.
    assert_eq!(
        conv_term(&p, &g, Layer::Meta, &elim(1), &elim(0), &Type::Nat, &c(0), FUEL),
        Err(ConvError::NotConvertible)
    );
}

#[test]
fn the_psi_free_reduction_unfolds_nothing() {
    // `step_term`/`whnf_term` are ch. 06's relation, and the only one layer
    // c ever uses. Same term, two δ-environments, two answers.
    let p = defs_psi();
    let g = nil_ctx(0);
    let t = app(glob(0, 0), Term::Zero);
    assert_eq!(step_term(&glob(1, 0), &g), None);
    assert_eq!(whnf_term(&t, &g, FUEL), Ok(t.clone()));
    assert_eq!(whnf_term_delta(&t, &g, Defs::opaque(), FUEL), Ok(t.clone()));
    assert_eq!(whnf_term_delta(&t, &g, Defs::transparent(&p), FUEL), Ok(num(2)));
}

// -------------------------------------------------------------------------
// (c) the binding's own well-formedness
// -------------------------------------------------------------------------

#[test]
fn a_body_is_checked_against_the_declared_type() {
    assert_eq!(check_global_ctx(&defs_psi(), 0, FUEL), Ok(()));
    assert_eq!(check_global_ctx(&opaque_psi(), 0, FUEL), Ok(()));
    // A body at the wrong type is rejected where it is bound, not where it
    // is used.
    let bad = psi(vec![binding(nat_to_nat(), Some(Term::Zero))]);
    assert!(check_global_ctx(&bad, 0, FUEL).is_err());
    // Layer v admits no term but a variable, so it admits no definition.
    let at_v = psi(vec![GlobalBinding::Tm {
        ctx: nil_ctx(0),
        layer: Layer::Var,
        ty: rty(Type::Nat),
        level: Level::Zero,
        body: Some(rt(num(2))),
    }]);
    assert_eq!(check_global_ctx(&at_v, 0, FUEL), Err(TypeError::LayerMismatch));
}

#[test]
fn a_body_may_mention_earlier_definitions() {
    // Ψ is a telescope: `later := Succ (two^·)` is scoped in the prefix, so
    // its own occurrence of `two` is one index further out than a use site's.
    // Getting that shift wrong is the classic δ bug; `3` is the witness.
    let p = psi(vec![
        binding(Type::Nat, Some(num(2))),
        binding(Type::Nat, Some(Term::Succ(rt(glob(0, 0))))),
    ]);
    assert_eq!(check_global_ctx(&p, 0, FUEL), Ok(()));
    let g = nil_ctx(0);
    ok_tm(&p, &g, &glob(0, 0), &num(3), &Type::Nat);
    no_tm(&p, &g, &glob(0, 0), &num(2), &Type::Nat);
    // And the shift is visible in the reduct: the body's `u₀` (its own
    // prefix's `two`) comes out as `u₁` at the use site. Weak head, so the
    // inner definition stays folded under the `Succ`.
    assert_eq!(
        whnf_term_delta(&glob(0, 0), &g, Defs::transparent(&p), FUEL),
        Ok(Term::Succ(rt(glob(1, 0))))
    );
}

// -------------------------------------------------------------------------
// Branch table (as in tests/conv.rs)
// -------------------------------------------------------------------------

fn const_branches(t: Term) -> Rc<Branches> {
    let z = || rt(t.clone());
    Rc::new(Branches {
        ty_nat: z(),
        ty_pi: z(),
        ty_ty: z(),
        ty_el: z(),
        tm_var: z(),
        tm_nat: z(),
        tm_pi: z(),
        tm_ty: z(),
        tm_zero: z(),
        tm_succ: z(),
        tm_elim_nat: z(),
        tm_lam: z(),
        tm_app: z(),
        ty_id: z(),
        ty_sigma: z(),
        tm_id: z(),
        tm_refl: z(),
        tm_j: z(),
        tm_sigma: z(),
        tm_pair: z(),
        tm_fst: z(),
        tm_snd: z(),
        ty_unit: z(),
        ty_empty: z(),
        tm_unit: z(),
        tm_empty: z(),
        tm_triv: z(),
        tm_elim_empty: z(),
        ty_sum: z(),
        tm_sum: z(),
        tm_inl: z(),
        tm_inr: z(),
        tm_case: z(),
        ty_w: z(),
        tm_w: z(),
        tm_sup: z(),
        tm_elim_w: z(),
        ty_vec: z(),
        tm_vec: z(),
        ty_fin: z(),
        tm_fin: z(),
        ty_wf: z(),
        tm_wf: z(),
        tm_supf: z(),
        tm_elim_wf: z(),
        ty_seq: z(),
        tm_seq: z(),
        ty_sempty: z(),
        tm_sempty: z(),
        tm_srefl: z(),
        tm_transp: z(),
        tm_elim_sempty: z(),
    })
}

