//! The two spellings of a reference into Ψ (`crates/kernel/DESIGN.md`,
//! "Constants are addressed from the start of Ψ"): a constant of the
//! signature by position, a variable by de Bruijn index.
//!
//! Two kinds of test.
//!
//! - **Adequacy, as laws.** Erasing a term's constants to the indices the
//!   paper would write commutes with every operation on the global
//!   namespace: weakening, substitution, and the local substitution that
//!   carries terms across them. The corpus is `subst_laws.rs`'s generated
//!   well-scoped terms, respelled at a random split of their scope, so every
//!   term former that carries a reference or binds a global is exercised.
//! - **The reference rule**, on hand-built contexts: what typing accepts and
//!   refuses, that a constant's statement is read as stored (unchanged when Ψ
//!   grows by constants or by variables, under a binder of globals too), and
//!   that δ and conversion see through a constant as through a variable.
//!   Each acceptance has its refusal beside it.

mod common;

use std::sync::Arc as Rc;

use common::*;
use heather_kernel::conv::{conv_term, ConvError};
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::reduce::{whnf_term_delta, Defs};
use heather_kernel::subst::{global_var_bound_tm, global_var_bound_ty, GlobalEntry, GlobalSubst};
use heather_kernel::term::{
    CtxBase, GlobalBinding, GlobalCtx, GlobalRef, GlobalVar, LocalCtx, LocalSubst, SubstTail, Term, Type,
};
use heather_kernel::typing::{check_global_ctx, check_signature_extension, check_term, infer_term, TypeError};

const CASES: u64 = 300;
const BUDGET: u32 = 12;
const FUEL: u64 = 100_000;

// -------------------------------------------------------------------------
// Respelling
// -------------------------------------------------------------------------

/// The paper's reading of a reference in a Ψ of `len` bindings: a constant
/// at position `p` is the index `len − 1 − p`.
fn erase_ref(len: u32) -> impl FnMut(GlobalRef) -> Option<GlobalRef> {
    move |r| match r {
        GlobalRef::Var(i) => Some(GlobalRef::Var(i)),
        GlobalRef::Const(p) => Some(GlobalRef::Var(len.checked_sub(1 + p)?)),
    }
}

/// The spelling a Ψ of `len` bindings, the first `consts` of them the
/// signature, gives a free index.
fn spell_ref(len: u32, consts: u32) -> impl FnMut(GlobalRef) -> Option<GlobalRef> {
    move |r| match r {
        GlobalRef::Var(i) if i < len && len - 1 - i < consts => Some(GlobalRef::Const(len - 1 - i)),
        r => Some(r),
    }
}

fn spell(t: &Rc<Term>, len: u32, consts: u32) -> Rc<Term> {
    Rc::new(t.reindex_global(&mut spell_ref(len, consts)).expect("total"))
}

fn erase(t: &Term, len: u32) -> Term {
    t.reindex_global(&mut erase_ref(len)).expect("every constant is in scope")
}

fn spell_ty(t: &Type, len: u32, consts: u32) -> Type {
    t.reindex_global(&mut spell_ref(len, consts)).expect("total")
}

/// A context has no `reindex_global` of its own: through the contextual
/// type that holds one.
fn spell_ctx(c: &LocalCtx, len: u32, consts: u32) -> LocalCtx {
    let Type::CodeTy { ctx, .. } = spell_ty(&Type::CodeTy { ctx: c.clone(), level: Level::Zero }, len, consts) else {
        unreachable!("a respelling keeps the former")
    };
    ctx
}

fn spell_var(v: GlobalVar, len: u32, consts: u32) -> GlobalVar {
    spell_ref(len, consts)(v.view()).expect("total").into()
}

fn spell_subst(d: &LocalSubst, len: u32, consts: u32) -> LocalSubst {
    LocalSubst {
        tail: match d.tail {
            SubstTail::Empty => SubstTail::Empty,
            SubstTail::Wk { len: k, ctx_var } => SubstTail::Wk { len: k, ctx_var: spell_var(ctx_var, len, consts) },
        },
        terms: d.terms.iter().map(|t| spell(t, len, consts)).collect(),
    }
}

fn spell_sigma(s: &GlobalSubst, len: u32, consts: u32) -> GlobalSubst {
    GlobalSubst {
        entries: s
            .entries
            .iter()
            .map(|e| match e {
                GlobalEntry::Ctx(c) => GlobalEntry::Ctx(spell_ctx(c, len, consts)),
                GlobalEntry::Ty(t) => GlobalEntry::Ty(Rc::new(spell_ty(t, len, consts))),
                GlobalEntry::Tm(t) => GlobalEntry::Tm(spell(t, len, consts)),
            })
            .collect(),
    }
}

/// Whether any reference in `t` is a constant: the laws below are vacuous
/// on a corpus the respelling never touched.
fn mentions_constant(t: &Term) -> bool {
    let mut seen = false;
    t.reindex_global(&mut |r| {
        seen |= matches!(r, GlobalRef::Const(_));
        Some(r)
    });
    seen
}

// -------------------------------------------------------------------------
// Adequacy
// -------------------------------------------------------------------------

#[test]
fn respelling_is_inverted_by_erasure() {
    heather_kernel::checks::set_skip_verification(heather_kernel::checks::SkipVerification::Full);
    let mut respelled = 0;
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x2545f4914f6cdd1d);
        let sc = gen_scope(&mut r);
        let len = sc.globals.len() as u32;
        let t = gen_term(&sc, &mut r, BUDGET);
        for consts in 0..=len {
            let c = spell(&t, len, consts);
            respelled += u32::from(mentions_constant(&c));
            law!(seed, erase(&c, len), *t);
            // Respelling what is already spelled changes nothing.
            law!(seed, *spell(&c, len, consts), *c);
        }
        // With no signature the term is the paper's, node for node.
        assert!(Rc::ptr_eq(&spell(&t, len, 0), &t) || *spell(&t, len, 0) == *t);
    }
    assert!(respelled > CASES as u32 / 4, "the corpus barely mentions a constant ({respelled})");
}

#[test]
fn weakening_is_the_identity_on_constants() {
    heather_kernel::checks::set_skip_verification(heather_kernel::checks::SkipVerification::Full);
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x6a09e667f3bcc908);
        let sc = gen_scope(&mut r);
        let len = sc.globals.len() as u32;
        let t = gen_term(&sc, &mut r, BUDGET);
        let by = 1 + r.below(3);
        let consts = r.below(len + 1);
        let c = spell(&t, len, consts);
        // erase ∘ shift = shift ∘ erase: the constants did not move, and
        // read at the longer length they are the indices the shift made.
        law!(seed, erase(&c.shift_global(by), len + by), t.shift_global(by));
        // A term of the signature alone is not touched at all.
        let closed = spell(&t, len, len);
        law!(seed, closed.shift_global(by), *closed);
        // …and above a cutoff likewise, while the cutoff is among the
        // variables, which is where a binder puts it.
        for cutoff in 0..=(len - consts).min(2) {
            law!(seed, erase(&c.shift_global_above(by, cutoff), len + by), t.shift_global_above(by, cutoff));
        }
    }
}

#[test]
fn substitution_is_the_identity_on_constants() {
    heather_kernel::checks::set_skip_verification(heather_kernel::checks::SkipVerification::Full);
    // erase(t[σ]) = erase(t)[erase(σ)], for a σ that instantiates variables:
    // the signature is a prefix of what σ leaves alone.
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0xbb67ae8584caa73b);
        let sc = gen_scope(&mut r);
        let len = sc.globals.len() as u32;
        let t = gen_term(&sc, &mut r, BUDGET);
        let (sigma, prefix) = gen_sigma(&sc, &mut r, BUDGET);
        let rest = prefix.globals.len() as u32;
        let consts = r.below(rest + 1);
        let c = spell(&t, len, consts);
        let csigma = spell_sigma(&sigma, rest, consts);
        law!(seed, erase(&c.apply_global(&csigma), rest), t.apply_global(&sigma));
    }
}

#[test]
fn local_substitution_commutes_with_respelling() {
    heather_kernel::checks::set_skip_verification(heather_kernel::checks::SkipVerification::Full);
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x3c6ef372fe94f82b);
        let mut sc = gen_scope(&mut r);
        let len = sc.globals.len() as u32;
        let base = sc.local.base;
        let target = Shape { base, len: r.below(4) };
        let source = sc.local;
        sc.local = target;
        let t = gen_term(&sc, &mut r, BUDGET);
        sc.local = source;
        let delta = gen_subst(&sc, &mut r, BUDGET, target);
        let consts = r.below(len + 1);
        law!(seed,
            erase(&spell(&t, len, consts).apply_local(&spell_subst(&delta, len, consts)), len),
            t.apply_local(&delta));
    }
}

// -------------------------------------------------------------------------
// The free-variable bound the global operations skip on
// -------------------------------------------------------------------------

/// `1 +` the largest global variable free in `t`, read off the one operation
/// that hands every free reference to a caller.
fn largest_free_variable(t: &Term) -> u32 {
    let mut bound = 0;
    t.reindex_global(&mut |r| {
        if let GlobalRef::Var(i) = r {
            bound = bound.max(i + 1);
        }
        Some(r)
    });
    bound
}

/// The bound `shift_global` and `apply_global` skip on is the largest free
/// variable, at every split of the scope into signature and variables: a
/// constant is never one, a variable a binder inside the term binds is not
/// free, and the boxed code the global operations read through is read.
#[test]
fn the_global_bound_is_the_largest_free_variable() {
    let mut closed = 0;
    let mut open = 0;
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x510e527fade682d1);
        let sc = gen_scope(&mut r);
        let len = sc.globals.len() as u32;
        let t = gen_term(&sc, &mut r, BUDGET);
        for consts in 0..=len {
            let c = spell(&t, len, consts);
            let want = largest_free_variable(&c);
            law!(seed, global_var_bound_tm(&c), want);
            // A second answer is the memo's.
            law!(seed, global_var_bound_tm(&c), want);
            assert!(want <= len - consts, "seed {seed}: a variable past the variables");
            closed += u32::from(want == 0 && mentions_constant(&c));
            open += u32::from(want > 0);
        }
        let ty = Rc::new(spell_ty(&gen_type(&sc, &mut r, BUDGET), len, r.below(len + 1)));
        let mut want = 0;
        ty.reindex_global(&mut |r| {
            if let GlobalRef::Var(i) = r {
                want = want.max(i + 1);
            }
            Some(r)
        });
        law!(seed, global_var_bound_ty(&ty), want);
    }
    assert!(closed > CASES as u32 / 8 && open > CASES as u32 / 8, "a one-sided corpus ({closed} closed, {open} open)");
}

/// The skips themselves. An operation asks about a subtree the second time
/// it meets it, so each is run twice; at full verification every skip the
/// second run takes is walked anyway and compared, and the two results must
/// be one.
#[test]
fn the_global_operations_skip_what_they_would_not_change() {
    heather_kernel::checks::set_skip_verification(heather_kernel::checks::SkipVerification::Full);
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x9b05688c2b3e6c1f);
        let sc = gen_scope(&mut r);
        let len = sc.globals.len() as u32;
        let t = gen_term(&sc, &mut r, BUDGET);
        let (sigma, prefix) = gen_sigma(&sc, &mut r, BUDGET);
        let rest = prefix.globals.len() as u32;
        for consts in [0, r.below(rest + 1), rest] {
            let c = spell(&t, len, consts);
            let by = 1 + r.below(3);
            for cutoff in 0..=(len - consts).min(3) {
                let once = c.shift_global_above(by, cutoff);
                law!(seed, c.shift_global_above(by, cutoff), once);
                law!(seed, erase(&once, len + by), t.shift_global_above(by, cutoff));
            }
            let csigma = spell_sigma(&sigma, rest, consts);
            let once = c.apply_global(&csigma);
            law!(seed, c.apply_global(&csigma), once);
            law!(seed, erase(&once, rest), t.apply_global(&sigma));
        }
    }
}

/// A numeral as deep as the stack is not: the bound of a long data spine is
/// computed from the bottom up (`docs/deep-term-walks-design.md`).
#[test]
fn the_global_bound_of_a_deep_spine_does_not_recurse_its_length() {
    let head = Rc::new(Term::GlobalTm {
        var: GlobalVar::index(3),
        subst: LocalSubst { tail: SubstTail::Wk { len: 0, ctx_var: GlobalVar::constant(0) }, terms: vec![] },
    });
    let mut t = head;
    for _ in 0..200_000 {
        t = Rc::new(Term::Succ(t));
    }
    assert_eq!(global_var_bound_tm(&t), 4);
    // Shifted twice, so the second walk skips nothing it should not: the
    // variable at the bottom is free, and moves.
    let once = t.shift_global(1);
    assert!(t.shift_global(1) == once);
    assert_eq!(global_var_bound_tm(&Rc::new(once)), 5);
}

// -------------------------------------------------------------------------
// The reference rule
// -------------------------------------------------------------------------

fn rt(t: Term) -> Rc<Term> {
    Rc::new(t)
}

fn rty(t: Type) -> Rc<Type> {
    Rc::new(t)
}

fn num(n: u32) -> Term {
    let mut t = Term::Zero;
    for _ in 0..n {
        t = Term::Succ(rt(t));
    }
    t
}

/// A reference at the empty substitution: every binding here is closed.
fn at(var: GlobalVar) -> Term {
    Term::GlobalTm { var, subst: LocalSubst { tail: SubstTail::Empty, terms: vec![] } }
}

fn konst(p: u32) -> Term {
    at(GlobalVar::constant(p))
}

fn var(i: u32) -> Term {
    at(GlobalVar::index(i))
}

fn def(ty: Type, body: Option<Term>) -> GlobalBinding {
    GlobalBinding::Tm { ctx: LocalCtx::nil(), layer: Layer::Code, ty: rty(ty), level: Level::Zero, body: body.map(rt) }
}

fn id_ty(a: Term, b: Term) -> Type {
    Type::Id { level: Level::Zero, ty: rty(Type::Nat), lhs: rt(a), rhs: rt(b) }
}

/// `two := 2`, `also := two` (by position), and `p : two = 2` declared: a
/// signature whose later bindings mention its earlier ones.
fn signature() -> GlobalCtx {
    let mut psi = GlobalCtx::default();
    psi.commit(def(Type::Nat, Some(num(2))));
    psi.commit(def(Type::Nat, Some(konst(0))));
    psi.commit(def(id_ty(konst(0), num(2)), None));
    psi
}

fn infer(psi: &GlobalCtx, t: &Term) -> Result<(Type, Level), TypeError> {
    infer_term(psi, 0, Layer::Prog, &LocalCtx::nil(), t, FUEL)
}

#[test]
fn a_signature_is_well_formed_binding_by_binding() {
    let psi = signature();
    assert_eq!(psi.consts(), 3);
    assert_eq!(check_global_ctx(&psi, 0, FUEL), Ok(()));
    // The same bindings read with no signature: `also`'s body is then a
    // position where the paper's Ψ has only indices.
    let flat = GlobalCtx::new(psi.bindings.to_vec());
    assert_eq!(check_global_ctx(&flat, 0, FUEL), Err(TypeError::MisspelledGlobal(GlobalVar::constant(0))));
    // An extension of the signature is checked as constants…
    let more = [def(Type::Nat, Some(konst(1)))];
    assert_eq!(check_signature_extension(&psi, &more, 0, FUEL), Ok(()));
    // …and a constant may not name itself or anything later.
    let ahead = [def(Type::Nat, Some(konst(3)))];
    assert_eq!(
        check_signature_extension(&psi, &ahead, 0, FUEL),
        Err(TypeError::UnboundGlobalVar(GlobalVar::constant(3)))
    );
}

#[test]
fn each_binding_has_one_spelling() {
    let mut psi = signature();
    // Constants by position.
    assert_eq!(infer(&psi, &konst(0)).map(|(t, _)| t), Ok(Type::Nat));
    assert_eq!(infer(&psi, &konst(2)).map(|(t, _)| t), Ok(id_ty(konst(0), num(2))));
    // An index that reaches the signature is refused, though it names a
    // binding: it is not that binding's spelling.
    assert_eq!(infer(&psi, &var(0)), Err(TypeError::MisspelledGlobal(GlobalVar::index(0))));
    assert_eq!(infer(&psi, &var(2)), Err(TypeError::MisspelledGlobal(GlobalVar::index(2))));
    // Out of scope, either way.
    assert_eq!(infer(&psi, &konst(3)), Err(TypeError::UnboundGlobalVar(GlobalVar::constant(3))));
    assert_eq!(infer(&psi, &var(3)), Err(TypeError::UnboundGlobalVar(GlobalVar::index(3))));

    // A variable over the signature: by index, and not by position.
    psi.push(def(Type::Nat, None));
    assert_eq!(psi.consts(), 3);
    assert_eq!(infer(&psi, &var(0)).map(|(t, _)| t), Ok(Type::Nat));
    assert_eq!(infer(&psi, &konst(3)), Err(TypeError::MisspelledGlobal(GlobalVar::constant(3))));
    assert_eq!(infer(&psi, &var(1)), Err(TypeError::MisspelledGlobal(GlobalVar::index(1))));
    // The constants are what they were.
    assert_eq!(infer(&psi, &konst(2)).map(|(t, _)| t), Ok(id_ty(konst(0), num(2))));
    assert_eq!(psi.reference(1), Some(GlobalVar::constant(1)));
    assert_eq!(psi.reference(3), Some(GlobalVar::index(0)));
}

#[test]
#[should_panic(expected = "a constant committed under global variables")]
fn the_signature_grows_only_under_no_variable() {
    let mut psi = signature();
    psi.push(def(Type::Nat, None));
    psi.commit(def(Type::Nat, None));
}

#[test]
fn a_constant_reads_the_same_in_every_extension() {
    // One term, checked in the signature, then with more constants after
    // it, then under variables: never respelled.
    let t = Term::Refl { level: Level::Zero, ty: rty(Type::Nat), tm: rt(konst(1)) };
    let ty = id_ty(konst(1), num(2));
    let check = |psi: &GlobalCtx| check_term(psi, 0, Layer::Prog, &LocalCtx::nil(), &t, &ty, &Level::Zero, FUEL);
    let mut psi = signature();
    assert_eq!(check(&psi), Ok(()));
    for _ in 0..3 {
        psi.commit(def(Type::Nat, Some(num(7))));
        assert_eq!(check(&psi), Ok(()));
    }
    for _ in 0..3 {
        psi.push(def(Type::Nat, None));
        assert_eq!(check(&psi), Ok(()));
    }
    // The index spelling of the same binding is a different index in each
    // of those worlds; in the flat reading of the first it is `u_1`.
    let flat = GlobalCtx::new(vec![def(Type::Nat, Some(num(2))), def(Type::Nat, Some(var(0)))]);
    let by_index = Term::Refl { level: Level::Zero, ty: rty(Type::Nat), tm: rt(var(0)) };
    assert_eq!(
        check_term(&flat, 0, Layer::Prog, &LocalCtx::nil(), &by_index, &id_ty(var(0), num(2)), &Level::Zero, FUEL),
        Ok(())
    );
    // Negative control: the wrong numeral, in the last world.
    assert!(check_term(&psi, 0, Layer::Prog, &LocalCtx::nil(), &t, &id_ty(konst(1), num(3)), &Level::Zero, FUEL).is_err());
}

#[test]
fn delta_reads_a_constant_as_stored() {
    let mut psi = signature();
    let nil = LocalCtx::nil();
    let conv = |psi: &GlobalCtx, a: &Term, b: &Term| conv_term(psi, &nil, Layer::Prog, a, b, &Type::Nat, &Level::Zero, FUEL);
    // `also ≈ two ≈ 2`: two unfoldings, the second of a constant found
    // inside the first's stored body.
    assert_eq!(conv(&psi, &konst(1), &num(2)), Ok(()));
    assert_eq!(conv(&psi, &konst(1), &konst(0)), Ok(()));
    assert_eq!(conv(&psi, &konst(1), &num(3)), Err(ConvError::NotConvertible));
    assert_eq!(whnf_term_delta(&konst(1), &nil, Defs::transparent(&psi), FUEL).ok(), Some(num(2)));
    // The same under variables, where an index-spelled body would have had
    // to be weakened: a variable defined as a constant, and compared to it.
    psi.push(def(Type::Nat, Some(konst(1))));
    psi.push(def(Type::Nat, None));
    assert_eq!(conv(&psi, &var(1), &konst(0)), Ok(()));
    assert_eq!(conv(&psi, &var(1), &num(2)), Ok(()));
    assert_eq!(whnf_term_delta(&var(1), &nil, Defs::transparent(&psi), FUEL).ok(), Some(num(2)));
    // A declared variable is no definition, and no constant.
    assert_eq!(conv(&psi, &var(0), &konst(0)), Err(ConvError::NotConvertible));
    // Opaque worlds unfold neither spelling.
    assert_eq!(whnf_term_delta(&konst(1), &nil, Defs::opaque(), FUEL).ok(), Some(konst(1)));
}

#[test]
fn a_bound_global_is_a_variable_and_its_body_keeps_its_constants() {
    // letbox u = box 0 in (u, checked against the constant `two`'s type):
    // the body mentions the bound code by index 0 and, beside it, nothing
    // moved in the signature.
    let letbox = |body: Term| Term::LetBoxTm {
        motive_level: Level::Zero,
        code_level: Level::Zero,
        ctx: LocalCtx::nil(),
        ty: rty(Type::Nat),
        motive: rty(Type::Nat),
        body: rt(body),
        scrut: rt(Term::BoxTm(rt(Term::Zero))),
    };
    let psi = signature();
    let meta = |t: &Term| infer_term(&psi, 0, Layer::Meta, &LocalCtx::nil(), t, FUEL).map(|(t, _)| t);
    assert_eq!(meta(&letbox(var(0))), Ok(Type::Nat));
    assert_eq!(meta(&letbox(konst(0))), Ok(Type::Nat));
    // The bound global has no position: it is not in the signature.
    assert_eq!(meta(&letbox(konst(3))), Err(TypeError::MisspelledGlobal(GlobalVar::constant(3))));
    // And an index past the binder reaches the signature, which is refused.
    assert_eq!(meta(&letbox(var(1))), Err(TypeError::MisspelledGlobal(GlobalVar::index(1))));
    // β: the body's constant survives the substitution of the bound code
    // unrenumbered, and the bound occurrence is replaced.
    let nil = LocalCtx::nil();
    let whnf = |t: &Term| whnf_term_delta(t, &nil, Defs::transparent(&psi), FUEL).ok();
    assert_eq!(whnf(&letbox(var(0))), Some(Term::Zero));
    assert_eq!(whnf(&letbox(konst(1))), Some(num(2)));
}

#[test]
fn a_context_variable_is_never_a_constant_of_an_empty_signature() {
    // `CtxBase::Var` and a weakening's context variable are references
    // too, and are held to the same rule.
    let mut psi = GlobalCtx::default();
    psi.push(GlobalBinding::Ctx);
    let boxed = |g: GlobalVar| Type::CodeTy { ctx: LocalCtx { base: CtxBase::Var(g), entries: Default::default() }, level: Level::Zero };
    let ok = |psi: &GlobalCtx, t: &Type| {
        heather_kernel::typing::check_type(psi, 0, Layer::Meta, &LocalCtx::nil(), t, &Level::Zero, FUEL)
    };
    assert_eq!(ok(&psi, &boxed(GlobalVar::index(0))), Ok(()));
    assert_eq!(ok(&psi, &boxed(GlobalVar::constant(0))), Err(TypeError::MisspelledGlobal(GlobalVar::constant(0))));
    let mut sig = GlobalCtx::default();
    sig.commit(GlobalBinding::Ctx);
    assert_eq!(ok(&sig, &boxed(GlobalVar::constant(0))), Ok(()));
    assert_eq!(ok(&sig, &boxed(GlobalVar::index(0))), Err(TypeError::MisspelledGlobal(GlobalVar::index(0))));
}
