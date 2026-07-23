//! Property tests for the ch. 05 substitution algebra, on randomly generated
//! well-scoped (not necessarily well-typed) terms (see `common/mod.rs` for
//! the generators). The laws:
//!
//! - identity:       t[id_Γ] = t,  t[id_φ] = t
//! - composition:    t[δ'][δ] = t[δ'∘δ]  (and associativity of ∘)
//! - universe:       t[φ'][φ] = t[φ'∘φ]
//! - φ/δ commute:    t[δ][φ] = t[φ][δ[φ]]
//! - σ/δ commute:    t[δ][σ] = t[σ][δ[σ]]

mod common;

use std::rc::Rc;

use common::*;
use heather_kernel::level::{Level, UnivVar};
use heather_kernel::subst::{GlobalEntry, GlobalSubst};
use heather_kernel::term::{CtxBase, CtxEntry, LocalCtx, LocalSubst, LocalVar, Term, Type};

const CASES: u64 = 300;
const BUDGET: u32 = 12;

#[test]
fn local_identity() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed);
        let sc = gen_scope(&mut r);
        let t = gen_term(&sc, &mut r, BUDGET);
        let id = LocalSubst::id(&materialize(&sc, sc.local));
        assert_eq!(t.apply_local(&id), *t);
    }
}

#[test]
fn local_composition() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x9e3779b97f4a7c15);
        let mut sc = gen_scope(&mut r);
        // Three shapes over a common base so all tails are constructible.
        let base = sc.local.base;
        let sh2 = Shape { base, len: r.below(4) };
        let sh1 = Shape { base, len: r.below(4) };
        let sh0 = Shape { base, len: r.below(4) };

        sc.local = sh2;
        let t = gen_term(&sc, &mut r, BUDGET);

        sc.local = sh1;
        let d2 = gen_subst(&sc, &mut r, BUDGET, sh2); // sh1 ⊢ sh2
        sc.local = sh0;
        let d1 = gen_subst(&sc, &mut r, BUDGET, sh1); // sh0 ⊢ sh1

        law!(seed,
            t.apply_local(&d2).apply_local(&d1),
            t.apply_local(&d2.compose(&d1)));
    }
}

#[test]
fn local_composition_associative() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x517cc1b727220a95);
        let mut sc = gen_scope(&mut r);
        let base = sc.local.base;
        let shapes: Vec<Shape> = (0..4).map(|_| Shape { base, len: r.below(4) }).collect();

        sc.local = shapes[1];
        let d3 = gen_subst(&sc, &mut r, BUDGET / 2, shapes[0]); // sh1 ⊢ sh0
        sc.local = shapes[2];
        let d2 = gen_subst(&sc, &mut r, BUDGET / 2, shapes[1]); // sh2 ⊢ sh1
        sc.local = shapes[3];
        let d1 = gen_subst(&sc, &mut r, BUDGET / 2, shapes[2]); // sh3 ⊢ sh2

        law!(seed,
            d3.compose(&d2).compose(&d1),
            d3.compose(&d2.compose(&d1)));
    }
}

#[test]
fn universe_identity_and_composition() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x2545f4914f6cdd1d);
        let sc = gen_scope(&mut r);
        let t = gen_term(&sc, &mut r, BUDGET);

        let id: Vec<Level> = (0..sc.univ).map(|i| Level::Var(UnivVar(i))).collect();
        law!(seed, t.apply_univ(&id), *t);

        // φ₂ : sc.univ levels over u1 variables; φ₁ : u1 levels over u0.
        let u1 = r.below(3);
        let u0 = r.below(3);
        let sc1 = Sc { univ: u1, globals: vec![], local: Shape { base: BaseRef::Nil, len: 0 } };
        let sc0 = Sc { univ: u0, globals: vec![], local: Shape { base: BaseRef::Nil, len: 0 } };
        let phi2: Vec<Level> = (0..sc.univ).map(|_| gen_level(&sc1, &mut r, 2)).collect();
        let phi1: Vec<Level> = (0..u1).map(|_| gen_level(&sc0, &mut r, 2)).collect();
        let composed: Vec<Level> = phi2.iter().map(|l| l.subst(&phi1)).collect();

        law!(seed,
            t.apply_univ(&phi2).apply_univ(&phi1),
            t.apply_univ(&composed));
    }
}

#[test]
fn universe_local_commute() {
    // t[δ][φ] = t[φ][δ[φ]]
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0xd6e8feb86659fd93);
        let mut sc = gen_scope(&mut r);
        let base = sc.local.base;
        let target = Shape { base, len: r.below(4) };

        let source = sc.local;
        sc.local = target;
        let t = gen_term(&sc, &mut r, BUDGET);
        sc.local = source;
        let delta = gen_subst(&sc, &mut r, BUDGET, target);

        let u0 = r.below(3);
        let sc0 = Sc { univ: u0, globals: vec![], local: Shape { base: BaseRef::Nil, len: 0 } };
        let phi: Vec<Level> = (0..sc.univ).map(|_| gen_level(&sc0, &mut r, 2)).collect();

        law!(seed,
            t.apply_local(&delta).apply_univ(&phi),
            t.apply_univ(&phi).apply_local(&delta.apply_univ(&phi)));
    }
}

#[test]
fn global_local_commute() {
    // t[δ][σ] = t[σ][δ[σ]]
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0xa0761d6478bd642f);
        let mut sc = gen_scope(&mut r);
        let base = sc.local.base;
        let target = Shape { base, len: r.below(4) };

        let source = sc.local;
        sc.local = target;
        let t = gen_term(&sc, &mut r, BUDGET);
        sc.local = source;
        let delta = gen_subst(&sc, &mut r, BUDGET, target);

        let (sigma, _) = gen_sigma(&sc, &mut r, BUDGET);

        law!(seed,
            t.apply_local(&delta).apply_global(&sigma),
            t.apply_global(&sigma).apply_local(&delta.apply_global(&sigma)));
    }
}

#[test]
fn global_empty_is_identity() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0xe7037ed1a0b428db);
        let sc = gen_scope(&mut r);
        let t = gen_term(&sc, &mut r, BUDGET);
        let sigma = GlobalSubst::default();
        law!(seed, t.apply_global(&sigma), *t);
    }
}

#[test]
fn shift_composition() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x8ebc6af09c88c6e3);
        let sc = gen_scope(&mut r);
        let t = gen_term(&sc, &mut r, BUDGET);
        law!(seed, t.shift_local(0), *t);
        law!(seed, t.shift_global(0), *t);
        law!(seed, t.shift_univ(0), *t);
        law!(seed, t.shift_local(2).shift_local(3), t.shift_local(5));
        law!(seed, t.shift_global(2).shift_global(3), t.shift_global(5));
        law!(seed, t.shift_univ(2).shift_univ(3), t.shift_univ(5));
    }
}


#[test]
fn global_local_commute_weakening_focus() {
    // Directly constructs the adversarial configuration for σ's tail
    // expansion: Ψ = (g : Ctx, u : Trm(g, k_u entries ⊢ …)), local contexts
    // based on g, t containing u^{wk-tailed δ'}, and σ replacing g by an
    // m'-entry context and u by a payload that reads the spliced region.
    for seed in 0..300u64 {
        let mut r = Rng::new(seed ^ 0x1f83d9abfb41bd6b);
        let k_u = r.below(3); // entries of u's index context Δ_u = (g, k_u)
        let m_p = 1 + r.below(3); // entries of the context replacing g
        let sc = Sc {
            univ: r.below(2),
            globals: vec![GK::Ctx, GK::Tm(sh(0, k_u))],
            local: Shape { base: BaseRef::Abs(0), len: r.below(3) },
        };

        // t contains a reference u^δ' under a binder.
        let t = {
            let mut inner = sc.clone();
            inner.local.len += 1;
            Rc::new(Term::Lam {
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom: gen_type(&sc, &mut r, 4),
                body: Rc::new(Term::GlobalTm {
                    var: inner.db(1),
                    subst: gen_subst(&inner, &mut r, 4, sh(0, k_u)),
                }),
            })
        };

        // δ : source ⊢ sc.local, both over base g.
        let src = Sc {
            local: Shape { base: BaseRef::Abs(0), len: r.below(4) },
            ..sc.clone()
        };
        let delta = gen_subst(&src, &mut r, 4, sc.local);

        // σ: g ↦ Γ' (m' entries, empty base), u ↦ payload reading a random
        // variable of its context (with g spliced, deep indices reachable).
        let gamma_p = LocalCtx {
            base: CtxBase::Nil,
            entries: (0..m_p)
                .map(|_| CtxEntry { ty: Rc::new(Type::Nat), level: Level::Zero })
                .collect(),
        };
        let payload = Rc::new(Term::Succ(Rc::new(Term::Var(LocalVar(
            r.below(m_p + k_u),
        )))));
        let sigma = GlobalSubst {
            entries: vec![GlobalEntry::Ctx(gamma_p), GlobalEntry::Tm(payload)],
        };

        law!(seed,
            t.apply_local(&delta).apply_global(&sigma),
            t.apply_global(&sigma)
                .apply_local(&delta.apply_global(&sigma)));
    }
}
