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
//!
//! Failures report seeds only; never Debug-format terms here.

mod common;

use std::rc::Rc;

use common::wt::{
    gen_encoding, gen_nat_rec, gen_wt_ctx, gen_wt_env, gen_wt_term, gen_wt_term_at,
    perturb_conv, FUEL,
};
use common::Rng;
use heather_kernel::conv::{conv_term, conv_type, ConvError};
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{Term, Type};
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
        _ => unreachable!("gen_encoding only produces TmNat/TmTy/TmPi"),
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
/// for `TmPi`, the domain, recursively) is replaced by an encoding of a
/// different head constructor at the same level.
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
            dom: rt(mutate_encoding(dom)),
            cod: Rc::clone(cod),
        },
        _ => unreachable!("gen_encoding only produces TmNat/TmTy/TmPi"),
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
        // Branch i holds the numeral i: all 13 pairwise distinct, so any
        // swap or bump must be caught by the branchwise comparison.
        let base: [Rc<Term>; 13] = std::array::from_fn(|i| numeral(i as u32));
        let t = nr.build(&base);
        let res =
            check_term(&env.psi, env.univs, env.layer, &env.gamma, &t, &Type::Nat, &Level::Zero, FUEL);
        assert!(res.is_ok(), "seed {seed}: neutral recursor ill-typed: {res:?}");
        let conv = |a: &Term, b: &Term| {
            conv_term(&env.psi, &env.gamma, Layer::Meta, a, b, &Type::Nat, &Level::Zero, FUEL)
        };
        let k = r.below(13) as usize;
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
        let j = (k + 1 + r.below(12) as usize) % 13;
        let mut sw = base.clone();
        sw.swap(j, k);
        let ts = nr.build(&sw);
        assert_eq!(conv(&t, &ts), Err(NC), "seed {seed}: swapped branches {j},{k}");
    }
}
