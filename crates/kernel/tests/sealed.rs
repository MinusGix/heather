//! Sealed proofs (`issues/theorem-witness-unfolding.md`, option D): an opaque
//! binding whose proof Ψ keeps beside it is unsealed exactly where an
//! elimination is stuck on it, and every unsealing is recorded.
//!
//! The axes of `docs/testing-generated-terms.md`: a literal (closed) and a
//! neutral argument, a **checking** position as well as a conversion query,
//! both reduction machines (the value machine behind `conv_term` and the
//! syntax reducer behind `whnf_term_delta`), and a negative control for each
//! positive — the same Ψ without the sealed proof, a bare application with no
//! elimination waiting on it, and layer c.

use std::sync::Arc as Rc;

use heather_kernel::conv::{conv_term, ConvError};
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::reduce::{whnf_term, whnf_term_delta, Defs};
use heather_kernel::term::{
    CtxBase, CtxEntry, GlobalBinding, GlobalCtx, GlobalVar, LocalCtx, LocalSubst, LocalVar,
    SubstTail, Term, Type,
};
use heather_kernel::typing::{check_term, TypeError};
use heather_kernel::unseal;

const FUEL: u64 = 100_000;

fn rt(t: Term) -> Rc<Term> {
    Rc::new(t)
}

fn rty(t: Type) -> Rc<Type> {
    Rc::new(t)
}

fn z() -> Level {
    Level::Zero
}

fn v(i: u32) -> Term {
    Term::Var(LocalVar(i))
}

fn nats(n: u32) -> LocalCtx {
    LocalCtx {
        base: CtxBase::Nil,
        entries: ((0..n).map(|_| CtxEntry { ty: rty(Type::Nat), level: z() }).collect::<Vec<_>>()).into(),
    }
}

fn num(n: u32) -> Term {
    (0..n).fold(Term::Zero, |t, _| Term::Succ(rt(t)))
}

/// `Σ(x : Nat). Nat` — the shape of an `∃` whose witness a client reads.
fn sigma() -> Type {
    Type::Sigma { fst_level: z(), snd_level: z(), fst: rty(Type::Nat), snd: rty(Type::Nat) }
}

fn pair(a: Term, b: Term) -> Term {
    Term::Pair {
        fst_level: z(),
        snd_level: z(),
        fst_ty: rty(Type::Nat),
        snd_ty: rty(Type::Nat),
        fst: rt(a),
        snd: rt(b),
    }
}

fn fst(p: Term) -> Term {
    Term::Fst { fst_level: z(), snd_level: z(), fst_ty: rty(Type::Nat), snd_ty: rty(Type::Nat), pair: rt(p) }
}

fn glob(var: u32, k: u32) -> Term {
    Term::GlobalTm {
        var: GlobalVar(var),
        subst: LocalSubst { tail: SubstTail::Empty { len: k, base: CtxBase::Nil }, terms: vec![] },
    }
}

fn app(f: Term, a: Term) -> Term {
    Term::App { fun: rt(f), dom_level: z(), cod_level: z(), dom: rty(Type::Nat), cod: rty(sigma()), arg: rt(a) }
}

fn decl(ty: Type) -> GlobalBinding {
    GlobalBinding::Tm { ctx: nats(0), layer: Layer::Code, ty: rty(ty), level: z(), body: None }
}

/// Index 1: `w : Σ(x:Nat). Nat`, sealed proof `(3, 0)`. Index 0:
/// `f : Π(n:Nat). Σ(x:Nat). Nat`, sealed proof `λn. (S n, n)`. With
/// `sealed == false`, the same two declarations and no proofs: the control.
fn world(sealed: bool) -> GlobalCtx {
    let pi = Type::Pi { dom_level: z(), cod_level: z(), dom: rty(Type::Nat), cod: rty(sigma()) };
    let mut p = GlobalCtx::new(vec![decl(sigma()), decl(pi)]);
    if sealed {
        p.seal(0, rt(pair(num(3), num(0))));
        let body = Term::Lam { dom_level: z(), cod_level: z(), dom: rty(Type::Nat), body: rt(pair(Term::Succ(rt(v(0))), v(0))) };
        p.seal(1, rt(body));
    }
    p
}

fn conv(p: &GlobalCtx, g: &LocalCtx, a: &Term, b: &Term, ty: &Type) -> Result<(), ConvError> {
    conv_term(p, g, Layer::Prog, a, b, ty, &z(), FUEL)
}

#[test]
fn a_projection_unseals_and_is_recorded() {
    let p = world(true);
    let g = nats(0);
    let (r, opened) = unseal::record(|| conv(&p, &g, &fst(glob(1, 0)), &num(3), &Type::Nat));
    assert_eq!(r, Ok(()));
    // `w` sits at absolute index 0.
    assert_eq!(opened, vec![0]);
    // Negative control: the witness is 3, not 4.
    assert_eq!(conv(&p, &g, &fst(glob(1, 0)), &num(4), &Type::Nat), Err(ConvError::NotConvertible));
}

#[test]
fn without_the_proof_the_theorem_stays_opaque() {
    let p = world(false);
    let g = nats(0);
    let (r, opened) = unseal::record(|| conv(&p, &g, &fst(glob(1, 0)), &num(3), &Type::Nat));
    assert_eq!(r, Err(ConvError::NotConvertible));
    assert!(opened.is_empty());
}

#[test]
fn a_bare_application_is_never_opened() {
    // `f 2 ≡ f 2` is decided on the spine, and `f 2 ≡ f 3` must not be
    // decided by running two proofs: with no elimination waiting on them,
    // both stay neutral.
    let p = world(true);
    let g = nats(0);
    let (r, opened) = unseal::record(|| conv(&p, &g, &app(glob(0, 0), num(2)), &app(glob(0, 0), num(2)), &sigma()));
    assert_eq!(r, Ok(()));
    assert!(opened.is_empty(), "comparing equal spines opened {opened:?}");
    let (r, opened) = unseal::record(|| whnf_term_delta(&app(glob(0, 0), num(2)), &g, Defs::transparent(&p), FUEL));
    assert_eq!(r.ok(), Some(app(glob(0, 0), num(2))));
    assert!(opened.is_empty());
}

#[test]
fn a_projection_decided_on_its_spine_opens_nothing() {
    // `fst w ≡ fst w` and `fst (f n) ≡ fst (f n)`: an elimination stuck on a
    // sealed theorem glues its proof, but the comparison is decided on the
    // spine and never forces the glue, so nothing was opened.
    let p = world(true);
    let (r, opened) = unseal::record(|| conv(&p, &nats(0), &fst(glob(1, 0)), &fst(glob(1, 0)), &Type::Nat));
    assert_eq!(r, Ok(()));
    assert!(opened.is_empty(), "{opened:?}");
    let g = nats(1);
    let t = fst(app(glob(0, 1), v(0)));
    let (r, opened) = unseal::record(|| conv(&p, &g, &t, &t, &Type::Nat));
    assert_eq!(r, Ok(()));
    assert!(opened.is_empty(), "{opened:?}");
}

#[test]
fn a_projection_unseals_under_a_neutral_argument() {
    // The open axis: `fst (f n) ≡ S n` holds only by unsealing `f` and β.
    let p = world(true);
    let g = nats(1);
    let (r, opened) = unseal::record(|| conv(&p, &g, &fst(app(glob(0, 1), v(0))), &Term::Succ(rt(v(0))), &Type::Nat));
    assert_eq!(r, Ok(()));
    assert_eq!(opened, vec![1]);
    assert_eq!(
        conv(&p, &g, &fst(app(glob(0, 1), v(0))), &v(0), &Type::Nat),
        Err(ConvError::NotConvertible)
    );
    assert_eq!(
        conv(&world(false), &g, &fst(app(glob(0, 1), v(0))), &Term::Succ(rt(v(0))), &Type::Nat),
        Err(ConvError::NotConvertible)
    );
}

#[test]
fn the_syntax_reducer_unseals_at_the_same_place() {
    let p = world(true);
    let g = nats(0);
    let (r, opened) = unseal::record(|| whnf_term_delta(&fst(app(glob(0, 0), num(2))), &g, Defs::transparent(&p), FUEL));
    assert_eq!(r.ok(), Some(num(3)));
    assert_eq!(opened, vec![1]);
    // Layer c and the Ψ-free entry point never unseal.
    let (r, opened) = unseal::record(|| whnf_term(&fst(app(glob(0, 0), num(2))), &g, FUEL));
    assert_eq!(r.ok(), Some(fst(app(glob(0, 0), num(2)))));
    assert!(opened.is_empty());
    let r = whnf_term_delta(&fst(glob(1, 0)), &g, Defs::opaque(), FUEL);
    assert_eq!(r.ok(), Some(fst(glob(1, 0))));
}

#[test]
fn a_checking_position_computes_with_the_witness() {
    // `refl : Id(Nat; fst w; 3)` — the shape of `zero_below_one().witness =
    // 1 { refl }`, checked rather than merely converted.
    let p = world(true);
    let g = nats(0);
    let id_ty = |lhs: Term, rhs: Term| Type::Id { level: z(), ty: rty(Type::Nat), lhs: rt(lhs), rhs: rt(rhs) };
    let refl = Term::Refl { level: z(), ty: rty(Type::Nat), tm: rt(fst(glob(1, 0))) };
    let (r, opened) =
        unseal::record(|| check_term(&p, 0, Layer::Prog, &g, &refl, &id_ty(fst(glob(1, 0)), num(3)), &z(), FUEL));
    assert_eq!(r, Ok(()));
    assert_eq!(opened, vec![0]);
    assert_eq!(
        check_term(&p, 0, Layer::Prog, &g, &refl, &id_ty(fst(glob(1, 0)), num(2)), &z(), FUEL),
        Err(TypeError::NotConvertible)
    );
    assert_eq!(
        check_term(&world(false), 0, Layer::Prog, &g, &refl, &id_ty(fst(glob(1, 0)), num(3)), &z(), FUEL),
        Err(TypeError::NotConvertible)
    );
}

#[test]
fn sealing_keeps_the_binding_and_its_prefix() {
    let p = world(true);
    // The bindings are the declarations, unchanged: a sealed proof is beside
    // Ψ's bindings, never in one.
    assert_eq!(p.bindings, world(false).bindings);
    assert_eq!(p.sealed.len(), 2);
    assert_eq!(p.prefix(1).sealed.len(), 1);
    assert!(p.prefix(1).sealed_proof(0).is_some());
    assert!(p.prefix(1).sealed_proof(1).is_none());
    // A definition is not sealed: there is nothing to seal.
    let mut q = GlobalCtx::new(vec![GlobalBinding::Tm {
        ctx: nats(0),
        layer: Layer::Code,
        ty: rty(Type::Nat),
        level: z(),
        body: Some(rt(num(1))),
    }]);
    q.seal(0, rt(num(2)));
    assert!(q.sealed.is_empty());
}
