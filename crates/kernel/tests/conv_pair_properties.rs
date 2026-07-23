//! Property tests for conversion on **distinct pairs**
//! (issues/kernel-conv-pair-properties.md). `conv_properties.rs` only
//! relates a term to itself or its own reducts, so a checker that answers
//! yes too eagerly would pass all of it; these tests pit conversion against
//! pairs that are distinct-but-convertible (perturbed positives) and
//! distinct-and-inconvertible (mutated negatives).
//!
//! 1. root-level β/η/letbox/elim_Nat expansions of a well-typed term stay
//!    convertible, in both orientations;
//! 2. two independent perturbations of the same term are convertible to
//!    each other — the transitivity face of the PER;
//! 3. `El^l e` is convertible to the hand-decoded type of the encoding `e`;
//! 4. value-changing mutations yield `NotConvertible` (never `OutOfFuel`):
//!    `t ≉ su t` at `Nat`, shape-mutated encodings at `Ty l`, and box
//!    bodies differing by a value — or by a mere *redex*: code is
//!    intensional, so `box (β-redex of t) ≉ box t`;
//! 5. neutral code recursors (Γ-variable scrutinee) compare branchwise:
//!    a β-wrapped branch stays convertible while a bumped or swapped branch
//!    does not — `rec_ca`'s pairwise C_A comparison with genuinely
//!    differing sides, which β-firing recursors never reach.
//! 6. the **Σ algebraic laws** over generated well-typed pairs: β
//!    (`fst (pair a b) ≈ a`, `snd … ≈ b`) and η — a neutral `p ≈ (fst p,
//!    snd p)` definitionally — while two *distinct* neutral inhabitants of
//!    the same Σ stay `NotConvertible`, so η is surjective-pairing, not
//!    blind acceptance.
//!
//! Failures report seeds only; never Debug-format terms here.

mod common;

use std::rc::Rc;

use common::wt::{
    gen_encoding, gen_nat_rec, gen_wt_ctx, gen_wt_env, gen_wt_term, gen_wt_term_at,
    gen_wt_type, perturb_conv, FUEL,
};
use common::Rng;
use heather_kernel::conv::{conv_term, conv_type, ConvError};
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{LocalSubst, LocalVar, Term, Type};
use heather_kernel::typing::check_term;

const CASES: u64 = 300;
const BUDGET: u32 = 8;
const NC: ConvError = ConvError::NotConvertible;

fn rt(t: Term) -> Rc<Term> {
    Rc::new(t)
}

fn rty(t: Type) -> Rc<Type> {
    Rc::new(t)
}

#[test]
fn perturbed_term_stays_convertible() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x517cc1b727220a95);
        let env = gen_wt_env(&mut r);
        let (t, ty, l) = gen_wt_term(&env, &mut r, BUDGET);
        let p = perturb_conv(&env, &mut r, &t, &ty, &l)
            .unwrap_or_else(|| panic!("seed {seed}: no perturbation applicable"));
        assert!(p != t, "seed {seed}: perturbation returned the term unchanged");
        let res = check_term(&env.psi, env.univs, env.layer, &env.gamma, &p, &ty, &l, FUEL);
        assert!(res.is_ok(), "seed {seed}: perturbed term ill-typed: {res:?}");
        let at = env.layer.type_layer();
        let lr = conv_term(&env.psi, &env.gamma, at, &t, &p, &ty, &l, FUEL);
        assert!(lr.is_ok(), "seed {seed}: t ≉ perturb(t): {lr:?}");
        let rl = conv_term(&env.psi, &env.gamma, at, &p, &t, &ty, &l, FUEL);
        assert!(rl.is_ok(), "seed {seed}: perturb(t) ≉ t: {rl:?}");
    }
}

#[test]
fn two_perturbations_are_convertible_to_each_other() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x2545f4914f6cdd1d);
        let env = gen_wt_env(&mut r);
        let (t, ty, l) = gen_wt_term(&env, &mut r, BUDGET);
        let p1 = perturb_conv(&env, &mut r, &t, &ty, &l)
            .unwrap_or_else(|| panic!("seed {seed}: no perturbation applicable"));
        let p2 = perturb_conv(&env, &mut r, &t, &ty, &l)
            .unwrap_or_else(|| panic!("seed {seed}: no perturbation applicable"));
        let at = env.layer.type_layer();
        let res = conv_term(&env.psi, &env.gamma, at, &p1, &p2, &ty, &l, FUEL);
        assert!(res.is_ok(), "seed {seed}: perturb₁(t) ≉ perturb₂(t): {res:?}");
    }
}

/// One decoding step of an encoding, by hand (the checker's is `whnf_type`;
/// this is the independent transcription).
fn decode(e: &Term) -> Type {
    match e {
        Term::TmNat => Type::Nat,
        Term::TmTy(l) => Type::Ty(l.clone()),
        Term::TmPi { dom_level, cod_level, dom, cod } => Type::Pi {
            dom_level: dom_level.clone(),
            cod_level: cod_level.clone(),
            dom: rty(Type::El { level: dom_level.clone(), tm: Rc::clone(dom) }),
            cod: rty(Type::El { level: cod_level.clone(), tm: Rc::clone(cod) }),
        },
        Term::TmId { level, ty, lhs, rhs } => Type::Id {
            level: level.clone(),
            ty: rty(Type::El { level: level.clone(), tm: Rc::clone(ty) }),
            lhs: Rc::clone(lhs),
            rhs: Rc::clone(rhs),
        },
        Term::TmSigma { fst_level, snd_level, fst, snd } => Type::Sigma {
            fst_level: fst_level.clone(),
            snd_level: snd_level.clone(),
            fst: rty(Type::El { level: fst_level.clone(), tm: Rc::clone(fst) }),
            snd: rty(Type::El { level: snd_level.clone(), tm: Rc::clone(snd) }),
        },
        Term::TmSum { lhs_level, rhs_level, lhs, rhs } => Type::Sum {
            lhs_level: lhs_level.clone(),
            rhs_level: rhs_level.clone(),
            lhs: rty(Type::El { level: lhs_level.clone(), tm: Rc::clone(lhs) }),
            rhs: rty(Type::El { level: rhs_level.clone(), tm: Rc::clone(rhs) }),
        },
        _ => unreachable!("gen_encoding only produces TmNat/TmTy/TmPi/TmId/TmSigma/TmSum"),
    }
}

#[test]
fn el_of_encoding_converts_to_its_decoding() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x9e3779b97f4a7c15);
        let env = gen_wt_env(&mut r);
        let (e, l) = gen_encoding(&env, &mut r, BUDGET);
        let el = Type::El { level: l.clone(), tm: Rc::clone(&e) };
        let d = decode(&e);
        let at = env.layer.type_layer();
        let lr = conv_type(&env.psi, &env.gamma, at, &el, &d, &l, FUEL);
        assert!(lr.is_ok(), "seed {seed}: El e ≉ decode(e): {lr:?}");
        let rl = conv_type(&env.psi, &env.gamma, at, &d, &el, &l, FUEL);
        assert!(rl.is_ok(), "seed {seed}: decode(e) ≉ El e: {rl:?}");
    }
}

#[test]
fn succ_wrap_is_not_convertible() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0xd6e8feb86659fd93);
        let env = gen_wt_env(&mut r);
        let t = gen_wt_term_at(&env, &mut r, BUDGET, &Type::Nat, &Level::Zero)
            .unwrap_or_else(|| panic!("seed {seed}: Nat is always inhabitable"));
        let s = Term::Succ(Rc::clone(&t));
        let at = env.layer.type_layer();
        let lr = conv_term(&env.psi, &env.gamma, at, &t, &s, &Type::Nat, &Level::Zero, FUEL);
        assert_eq!(lr, Err(NC), "seed {seed}: t vs su t");
        let rl = conv_term(&env.psi, &env.gamma, at, &s, &t, &Type::Nat, &Level::Zero, FUEL);
        assert_eq!(rl, Err(NC), "seed {seed}: su t vs t");
    }
}

/// A type-preserving, shape-changing mutation of an encoding: the root (or,
/// for `TmPi`/`TmSigma`, the codomain, recursively) is replaced by an
/// encoding of a different head constructor at the same level. Only roots are
/// replaced — never a binder's type — because `TmId` endpoints (and a
/// `TmSigma` codomain) may reference enclosing binders, so changing a domain
/// is not type-preserving.
fn mutate_encoding(e: &Term) -> Term {
    match e {
        // Ty 0 = Ty (0 ⊔ 0).
        Term::TmNat => Term::TmPi {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: rt(Term::TmNat),
            cod: rt(Term::TmNat),
        },
        // Ty (1+l) = Ty ((1+l) ⊔ 0).
        Term::TmTy(l) => Term::TmPi {
            dom_level: Level::succ(l.clone()),
            cod_level: Level::Zero,
            dom: rt(Term::TmTy(l.clone())),
            cod: rt(Term::TmNat),
        },
        Term::TmPi { dom_level, cod_level, dom, cod } => Term::TmPi {
            dom_level: dom_level.clone(),
            cod_level: cod_level.clone(),
            dom: Rc::clone(dom),
            cod: rt(mutate_encoding(cod)),
        },
        // Id^l(s; t; u) : Ty l and s : Ty l — dropping to the carrier is
        // type-preserving and changes the head.
        Term::TmId { ty, .. } => (**ty).clone(),
        // Σ: mutate the codomain (a binder's type is off-limits, as for TmPi).
        Term::TmSigma { fst_level, snd_level, fst, snd } => Term::TmSigma {
            fst_level: fst_level.clone(),
            snd_level: snd_level.clone(),
            fst: Rc::clone(fst),
            snd: rt(mutate_encoding(snd)),
        },
        // Sum: non-dependent, so mutating either component is type-preserving;
        // change the lhs head.
        Term::TmSum { lhs_level, rhs_level, lhs, rhs } => Term::TmSum {
            lhs_level: lhs_level.clone(),
            rhs_level: rhs_level.clone(),
            lhs: rt(mutate_encoding(lhs)),
            rhs: Rc::clone(rhs),
        },
        _ => unreachable!("gen_encoding only produces TmNat/TmTy/TmPi/TmId/TmSigma/TmSum"),
    }
}

#[test]
fn mutated_encoding_is_not_convertible() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0xa0761d6478bd642f);
        let env = gen_wt_env(&mut r);
        let (e, l) = gen_encoding(&env, &mut r, BUDGET);
        let m = mutate_encoding(&e);
        let ty = Type::Ty(l.clone());
        let lv = Level::succ(l);
        let res = check_term(&env.psi, env.univs, env.layer, &env.gamma, &m, &ty, &lv, FUEL);
        assert!(res.is_ok(), "seed {seed}: mutated encoding ill-typed: {res:?}");
        let at = env.layer.type_layer();
        let lr = conv_term(&env.psi, &env.gamma, at, &e, &m, &ty, &lv, FUEL);
        assert_eq!(lr, Err(NC), "seed {seed}: e vs mutate(e)");
        let rl = conv_term(&env.psi, &env.gamma, at, &m, &e, &ty, &lv, FUEL);
        assert_eq!(rl, Err(NC), "seed {seed}: mutate(e) vs e");
    }
}

/// `app(λ(x : Nat). t↑; ze)` — closed one-β wrap of a `Nat`-typed term.
fn beta_wrap(t: &Rc<Term>) -> Rc<Term> {
    rt(Term::App {
        fun: rt(Term::Lam {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: rty(Type::Nat),
            body: rt(t.shift_local(1)),
        }),
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: rty(Type::Nat),
        cod: rty(Type::Nat),
        arg: rt(Term::Zero),
    })
}

#[test]
fn box_is_intensional() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0xe7037ed1a0b428db);
        let mut env = gen_wt_env(&mut r);
        env.layer = Layer::Meta; // box is a layer-m form
        let delta = gen_wt_ctx(&env, &mut r, 2, Layer::Prog);
        let ce = env.in_ctx(delta.clone(), Layer::Code);
        let code = gen_wt_term_at(&ce, &mut r, 2, &Type::Nat, &Level::Zero)
            .unwrap_or_else(|| panic!("seed {seed}: Nat is always inhabitable"));
        let ty = Type::CodeTm { ctx: delta, ty: rty(Type::Nat), level: Level::Zero };
        let a = Term::BoxTm(Rc::clone(&code));
        // A different value: not convertible.
        let b = Term::BoxTm(rt(Term::Succ(Rc::clone(&code))));
        // The *same* value behind a β-redex: still not convertible — code
        // compares syntactically, layer c does not compute.
        let c = Term::BoxTm(beta_wrap(&code));
        for (tag, other) in [("su", &b), ("β", &c)] {
            let res =
                check_term(&env.psi, env.univs, env.layer, &env.gamma, other, &ty, &Level::Zero, FUEL);
            assert!(res.is_ok(), "seed {seed}: {tag}-twin ill-typed: {res:?}");
            let lr = conv_term(
                &env.psi, &env.gamma, Layer::Meta, &a, other, &ty, &Level::Zero, FUEL,
            );
            assert_eq!(lr, Err(NC), "seed {seed}: box t vs {tag}-twin");
            let rl = conv_term(
                &env.psi, &env.gamma, Layer::Meta, other, &a, &ty, &Level::Zero, FUEL,
            );
            assert_eq!(rl, Err(NC), "seed {seed}: {tag}-twin vs box t");
        }
    }
}

fn numeral(n: u32) -> Rc<Term> {
    let mut t = Term::Zero;
    for _ in 0..n {
        t = Term::Succ(rt(t));
    }
    rt(t)
}

#[test]
fn neutral_recursor_compares_branches() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x8b72e64c032c9d17);
        let base_env = gen_wt_env(&mut r);
        let tm_variant = r.below(2) == 1;
        let nr = gen_nat_rec(&base_env, &mut r, tm_variant);
        let env = &nr.env;
        // Branch i holds the numeral i: all 33 pairwise distinct, so any
        // swap or bump must be caught by the branchwise comparison.
        let base: [Rc<Term>; 33] = std::array::from_fn(|i| numeral(i as u32));
        let t = nr.build(&base);
        let res =
            check_term(&env.psi, env.univs, env.layer, &env.gamma, &t, &Type::Nat, &Level::Zero, FUEL);
        assert!(res.is_ok(), "seed {seed}: neutral recursor ill-typed: {res:?}");
        let conv = |a: &Term, b: &Term| {
            conv_term(&env.psi, &env.gamma, Layer::Meta, a, b, &Type::Nat, &Level::Zero, FUEL)
        };
        let k = r.below(33) as usize;
        // β-wrapped branch: differing sides that are still convertible.
        let mut pos = base.clone();
        pos[k] = beta_wrap(&base[k]);
        let tp = nr.build(&pos);
        let res =
            check_term(&env.psi, env.univs, env.layer, &env.gamma, &tp, &Type::Nat, &Level::Zero, FUEL);
        assert!(res.is_ok(), "seed {seed}: β-branch twin ill-typed: {res:?}");
        assert!(conv(&t, &tp).is_ok(), "seed {seed}: rec ≉ rec with β-wrapped branch");
        assert!(conv(&tp, &t).is_ok(), "seed {seed}: rec with β-wrapped branch ≉ rec");
        // Bumped branch: NotConvertible.
        let mut neg = base.clone();
        neg[k] = rt(Term::Succ(Rc::clone(&base[k])));
        let tn = nr.build(&neg);
        assert_eq!(conv(&t, &tn), Err(NC), "seed {seed}: bumped branch {k}");
        // Two distinct branches swapped: NotConvertible.
        let j = (k + 1 + r.below(32) as usize) % 33;
        let mut sw = base.clone();
        sw.swap(j, k);
        let ts = nr.build(&sw);
        assert_eq!(conv(&t, &ts), Err(NC), "seed {seed}: swapped branches {j},{k}");
    }
}

/// β for the projections: `fst (pair a b) ≈ a`, `snd (pair a b) ≈ b`, over
/// generated well-typed (possibly dependent) Σ inhabitants.
#[test]
fn sigma_projection_beta_laws() {
    let mut ran = 0u64;
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x27d4eb2f165667c5);
        let env = gen_wt_env(&mut r);
        let (fst_ty, fl) = gen_wt_type(&env, &mut r, BUDGET / 2);
        let Some(a) = gen_wt_term_at(&env, &mut r, BUDGET / 2, &fst_ty, &fl) else { continue };
        let e = env.push_entry(Rc::clone(&fst_ty), fl.clone());
        let (snd_ty, sl) = gen_wt_type(&e, &mut r, BUDGET / 2);
        // b : T[a/x].
        let snd_at = snd_ty.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(&a)));
        let Some(b) = gen_wt_term_at(&env, &mut r, BUDGET / 2, &snd_at, &sl) else { continue };
        let sig = Type::Sigma {
            fst_level: fl.clone(),
            snd_level: sl.clone(),
            fst: Rc::clone(&fst_ty),
            snd: Rc::clone(&snd_ty),
        };
        let pair = rt(Term::Pair {
            fst_level: fl.clone(),
            snd_level: sl.clone(),
            fst_ty: Rc::clone(&fst_ty),
            snd_ty: Rc::clone(&snd_ty),
            fst: Rc::clone(&a),
            snd: Rc::clone(&b),
        });
        let lmax = Level::max(fl.clone(), sl.clone());
        // Sanity: the constructed pair is genuinely well-typed at Σ.
        let ck = check_term(&env.psi, env.univs, env.layer, &env.gamma, &pair, &sig, &lmax, FUEL);
        assert!(ck.is_ok(), "seed {seed}: generated pair ill-typed: {ck:?}");
        let fst = Term::Fst {
            fst_level: fl.clone(),
            snd_level: sl.clone(),
            fst_ty: Rc::clone(&fst_ty),
            snd_ty: Rc::clone(&snd_ty),
            pair: Rc::clone(&pair),
        };
        let snd = Term::Snd {
            fst_level: fl.clone(),
            snd_level: sl.clone(),
            fst_ty: Rc::clone(&fst_ty),
            snd_ty: Rc::clone(&snd_ty),
            pair: Rc::clone(&pair),
        };
        let at = env.layer.type_layer();
        // fst (pair a b) ≈ a : S, both orientations.
        assert!(
            conv_term(&env.psi, &env.gamma, at, &fst, &a, &fst_ty, &fl, FUEL).is_ok(),
            "seed {seed}: fst (pair a b) ≉ a"
        );
        assert!(
            conv_term(&env.psi, &env.gamma, at, &a, &fst, &fst_ty, &fl, FUEL).is_ok(),
            "seed {seed}: a ≉ fst (pair a b)"
        );
        // snd (pair a b) ≈ b : T[a/x], both orientations.
        assert!(
            conv_term(&env.psi, &env.gamma, at, &snd, &b, &snd_at, &sl, FUEL).is_ok(),
            "seed {seed}: snd (pair a b) ≉ b"
        );
        assert!(
            conv_term(&env.psi, &env.gamma, at, &b, &snd, &snd_at, &sl, FUEL).is_ok(),
            "seed {seed}: b ≉ snd (pair a b)"
        );
        ran += 1;
    }
    assert!(ran > 0, "no inhabited Σ was generated across {CASES} seeds");
}

/// η for pairs: a neutral `p ≈ (fst p, snd p)` definitionally, over generated
/// Σ types — and the sharpening negative that two *distinct* neutral
/// inhabitants of the same Σ are not convertible (η is not blind).
#[test]
fn sigma_eta_and_neutral_distinctness() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x94d049bb133111eb);
        let env = gen_wt_env(&mut r);
        // A well-formed Σ type (always constructible — no inhabitant needed).
        let (fst_ty, fl) = gen_wt_type(&env, &mut r, BUDGET / 2);
        let e = env.push_entry(Rc::clone(&fst_ty), fl.clone());
        let (snd_ty, sl) = gen_wt_type(&e, &mut r, BUDGET / 2);
        let lmax = Level::max(fl.clone(), sl.clone());
        let sig = Type::Sigma {
            fst_level: fl.clone(),
            snd_level: sl.clone(),
            fst: Rc::clone(&fst_ty),
            snd: Rc::clone(&snd_ty),
        };
        // Two Γ-variables of the *same* Σ type: after two pushes, both
        // Var(0) and Var(1) have type sig↑².
        let e1 = env.push_entry(rty(sig.clone()), lmax.clone());
        let e2 = e1.push_entry(rty(sig.shift_local(1)), lmax.clone());
        let sig2 = sig.shift_local(2);
        let Type::Sigma { fst_level, snd_level, fst, snd } = &sig2 else {
            unreachable!("shift preserves the Σ head")
        };
        let proj = |first: bool, idx: u32| {
            let pair = rt(Term::Var(LocalVar(idx)));
            if first {
                Term::Fst {
                    fst_level: fst_level.clone(),
                    snd_level: snd_level.clone(),
                    fst_ty: Rc::clone(fst),
                    snd_ty: Rc::clone(snd),
                    pair,
                }
            } else {
                Term::Snd {
                    fst_level: fst_level.clone(),
                    snd_level: snd_level.clone(),
                    fst_ty: Rc::clone(fst),
                    snd_ty: Rc::clone(snd),
                    pair,
                }
            }
        };
        let eta = |idx| Term::Pair {
            fst_level: fst_level.clone(),
            snd_level: snd_level.clone(),
            fst_ty: Rc::clone(fst),
            snd_ty: Rc::clone(snd),
            fst: rt(proj(true, idx)),
            snd: rt(proj(false, idx)),
        };
        let at = e2.layer.type_layer();
        let p0 = Term::Var(LocalVar(0));
        // η: p ≈ (fst p, snd p), both orientations.
        assert!(
            conv_term(&e2.psi, &e2.gamma, at, &p0, &eta(0), &sig2, &lmax, FUEL).is_ok(),
            "seed {seed}: p ≉ (fst p, snd p)"
        );
        assert!(
            conv_term(&e2.psi, &e2.gamma, at, &eta(0), &p0, &sig2, &lmax, FUEL).is_ok(),
            "seed {seed}: (fst p, snd p) ≉ p"
        );
        // Not blind: distinct neutral inhabitants of the same Σ differ.
        assert_eq!(
            conv_term(&e2.psi, &e2.gamma, at, &p0, &Term::Var(LocalVar(1)), &sig2, &lmax, FUEL),
            Err(NC),
            "seed {seed}: distinct Σ variables wrongly convertible"
        );
    }
}
