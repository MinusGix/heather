//! Property tests for the ch. 05 substitution algebra, on randomly generated
//! well-scoped (not necessarily well-typed) terms (see `common/mod.rs` for
//! the generators). The laws:
//!
//! - identity:       t[id_Γ] = t,  t[id_φ] = t
//! - composition:    t[δ'][δ] = t[δ'∘δ]  (and associativity of ∘)
//! - universe:       t[φ'][φ] = t[φ'∘φ]
//! - φ/δ commute:    t[δ][φ] = t[φ][δ[φ]]
//! - σ/δ commute:    t[δ][σ] = t[σ][δ[σ]]
//!
//! Every case runs with `checks::SkipVerification::Full`: the bounds'
//! skips (`bounds.rs`) are re-walked and compared on every occasion, so these
//! random terms are also the corpus that law is exhaustive over. Elsewhere the
//! default samples one skip in sixteen (`crates/kernel/src/checks.rs`).

mod common;

use heather_kernel::rc::Rc;

use common::*;
use heather_kernel::level::{Level, UnivVar};
use heather_kernel::subst::{GlobalEntry, GlobalSubst};
use heather_kernel::term::{CtxBase, CtxEntry, GlobalVar, LocalCtx, LocalSubst, LocalVar, Term, Type};

const CASES: u64 = 300;
const BUDGET: u32 = 12;

#[test]
fn local_identity() {
    heather_kernel::checks::set_skip_verification(heather_kernel::checks::SkipVerification::Full);
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
    heather_kernel::checks::set_skip_verification(heather_kernel::checks::SkipVerification::Full);
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
    heather_kernel::checks::set_skip_verification(heather_kernel::checks::SkipVerification::Full);
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
    heather_kernel::checks::set_skip_verification(heather_kernel::checks::SkipVerification::Full);
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
    heather_kernel::checks::set_skip_verification(heather_kernel::checks::SkipVerification::Full);
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
    heather_kernel::checks::set_skip_verification(heather_kernel::checks::SkipVerification::Full);
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
    heather_kernel::checks::set_skip_verification(heather_kernel::checks::SkipVerification::Full);
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
    heather_kernel::checks::set_skip_verification(heather_kernel::checks::SkipVerification::Full);
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
        // The cutoff variants at zero, which `subst.rs` §Shifting by zero
        // also short-circuits: a cutoff narrows which variables move, so it
        // cannot make a zero shift do something.
        for cutoff in 0..3 {
            law!(seed, t.shift_global_above(0, cutoff), *t);
            law!(seed, t.shift_univ_above(0, cutoff), *t);
        }
    }
}

/// The two operations the derived `DVec` schemas are built from
/// (`term::dvec_succ_parts`, `term::dnth`), against the substitution they
/// abbreviate: `t.inst_top(k, s)` is `t[id_Γ↑ᵏ, s/x]`, for `t` in `Γ, x` and
/// `s` in `Γ, Δ` with `|Δ| = k`; `shift_local_above(k, 0)` is
/// `shift_local(k)`, and above one binder it is `inst_top(k + 1, x)`.
#[test]
fn instantiation_at_the_top_is_a_substitution() {
    heather_kernel::checks::set_skip_verification(heather_kernel::checks::SkipVerification::Full);
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0xd6e8feb86659fd93);
        let sc = gen_scope(&mut r);
        let gamma = materialize(&sc, sc.local);
        let mut sc_x = sc.clone();
        sc_x.local.len += 1;
        let t = gen_term(&sc_x, &mut r, BUDGET);
        let ty = gen_type(&sc_x, &mut r, BUDGET);
        for by in 0..4 {
            let mut sc_d = sc.clone();
            sc_d.local.len += by;
            let s = gen_term(&sc_d, &mut r, BUDGET);
            let delta = LocalSubst::id(&gamma).shift_local(by).extended(Rc::clone(&s));
            law!(seed, t.inst_top(by, &s), t.apply_local(&delta));
            law!(seed, ty.inst_top(by, &s), ty.apply_local(&delta));
            let x = Term::Var(LocalVar(0));
            law!(seed, t.shift_local_above(by, 0), t.shift_local(by));
            law!(seed, t.shift_local_above(by, 1), t.inst_top(by + 1, &x));
            law!(seed, ty.shift_local_above(by, 1), ty.inst_top(by + 1, &x));
        }
    }
}

/// `IWf`'s schemas (`term::iwf_fam`, `term::iwf_ih`) instantiate the child
/// index at a shape under its position binder: `t.inst_top_above(k, c, s)`
/// is `inst_top(k, s)` lifted under `c` binders, for `t` in `Γ, x, Θ` with
/// `|Θ| = c` and `s` in `Γ, Δ`, `|Δ| = k`; the result is in `Γ, Δ, Θ`.
#[test]
fn instantiation_above_binders_is_a_lifted_substitution() {
    heather_kernel::checks::set_skip_verification(heather_kernel::checks::SkipVerification::Full);
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x4f1bbcdcbfa53e0a);
        let sc = gen_scope(&mut r);
        let gamma = materialize(&sc, sc.local);
        for cutoff in 0..3 {
            let mut sc_xt = sc.clone();
            sc_xt.local.len += 1 + cutoff;
            let t = gen_term(&sc_xt, &mut r, BUDGET);
            let ty = gen_type(&sc_xt, &mut r, BUDGET);
            for by in 0..3 {
                let mut sc_d = sc.clone();
                sc_d.local.len += by;
                let s = gen_term(&sc_d, &mut r, BUDGET);
                let mut delta = LocalSubst::id(&gamma).shift_local(by).extended(Rc::clone(&s));
                for _ in 0..cutoff {
                    delta = delta.shift_local(1).extended(Rc::new(Term::Var(LocalVar(0))));
                }
                law!(seed, t.inst_top_above(by, cutoff, &s), t.apply_local(&delta));
                law!(seed, ty.inst_top_above(by, cutoff, &s), ty.apply_local(&delta));
            }
            if cutoff == 0 {
                let s = gen_term(&sc, &mut r, BUDGET);
                law!(seed, t.inst_top_above(0, 0, &s), t.inst_top(0, &s));
            }
        }
    }
}

/// Shifting by zero must not just *equal* the input, it must **share** it:
/// that is the point of the fast path, and equality alone would pass just as
/// well against the deep-copying traversal it replaced
/// (issues/subst-copies-payloads-at-depth-zero.md).
///
/// Stated on subterm pointers rather than on the root, because the root is a
/// returned value and is necessarily a fresh `Term` either way.
#[test]
fn shifting_by_zero_preserves_sharing() {
    heather_kernel::checks::set_skip_verification(heather_kernel::checks::SkipVerification::Full);
    let inner = Rc::new(Term::Succ(Rc::new(Term::Zero)));
    let t = Term::Succ(Rc::clone(&inner));

    let shared = |out: &Term| match out {
        Term::Succ(got) => Rc::ptr_eq(got, &inner),
        _ => false,
    };
    assert!(shared(&t.shift_local(0)), "shift_local(0) rebuilt the subterm");
    assert!(shared(&t.shift_global(0)), "shift_global(0) rebuilt the subterm");
    assert!(shared(&t.shift_univ(0)), "shift_univ(0) rebuilt the subterm");
    assert!(shared(&t.shift_global_above(0, 1)), "shift_global_above(0, _) rebuilt the subterm");
    assert!(shared(&t.shift_univ_above(0, 1)), "shift_univ_above(0, _) rebuilt the subterm");

    // And the payload path that motivated all of this: substituting into
    // `Var 0` at depth zero must hand back the payload's own subterms, not
    // copies of them. `[t/x]` applied to `x` is where a β-step lands.
    let gamma = LocalCtx::nil();
    let delta = LocalSubst::id(&gamma).extended(Rc::new(t.clone()));
    assert!(
        shared(&Term::Var(LocalVar(0)).apply_local(&delta)),
        "substituting a payload at depth zero copied it"
    );

    // A *nonzero* shift must still do the work where there is work: a subterm
    // that mentions a free variable has to be rebuilt. (A *closed* one is
    // shared even at `by = 1` — that is the subtree sharing tested below, not
    // a fast path being too eager.)
    let open_inner = Rc::new(Term::Succ(Rc::new(Term::Var(LocalVar(0)))));
    let open = Term::Succ(Rc::clone(&open_inner));
    match open.shift_local(1) {
        Term::Succ(got) => assert!(
            !Rc::ptr_eq(&got, &open_inner),
            "shift_local(1) shared a subterm it had to renumber"
        ),
        _ => panic!("shift changed the head shape"),
    }
}

/// A substitution must share the subterms it cannot change — the point of
/// issues/subst-rebuilds-unchanged-subterms.md. Again on pointers: equality
/// holds against the copying traversal too, so equality proves nothing here.
#[test]
fn substitution_shares_subterms_it_cannot_change() {
    heather_kernel::checks::set_skip_verification(heather_kernel::checks::SkipVerification::Full);
    let closed_arg = Rc::new(Term::Succ(Rc::new(Term::Succ(Rc::new(Term::Zero)))));
    let closed_dom = Rc::new(Type::Nat);
    let closed_cod = Rc::new(Type::Pi {
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: Rc::new(Type::Nat),
        cod: Rc::new(Type::Nat),
    });
    // app(x; Nat. (Nat → Nat); 2) — the head mentions x, everything else is
    // closed, which is the shape of a generated recursor arm in miniature.
    let t = Term::App {
        fun: Rc::new(Term::Var(LocalVar(0))),
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: Rc::clone(&closed_dom),
        cod: Rc::clone(&closed_cod),
        arg: Rc::clone(&closed_arg),
    };

    let gamma = LocalCtx::nil();
    let delta = LocalSubst::id(&gamma).extended(Rc::new(Term::Zero));
    match t.apply_local(&delta) {
        Term::App { fun, dom, cod, arg, .. } => {
            assert!(*fun == Term::Zero, "the substituted head is wrong");
            assert!(Rc::ptr_eq(&arg, &closed_arg), "rebuilt a closed argument");
            assert!(Rc::ptr_eq(&dom, &closed_dom), "rebuilt a closed domain annotation");
            assert!(Rc::ptr_eq(&cod, &closed_cod), "rebuilt a closed codomain annotation");
        }
        _ => panic!("substitution changed the head shape"),
    }

    // The identity substitution changes nothing at all, so it must share the
    // *whole* term — including the branch that does mention the variable.
    let id = LocalSubst::id(&LocalCtx {
        base: CtxBase::Nil,
        entries: (vec![CtxEntry { ty: Rc::new(Type::Nat), level: Level::Zero }]).into(),
    });
    match t.apply_local(&id) {
        Term::App { arg, .. } => {
            assert!(Rc::ptr_eq(&arg, &closed_arg), "t[id] rebuilt a subterm")
        }
        _ => panic!("t[id] changed the head shape"),
    }
}

/// Relocating a module image (`ModuleDelta::relocate`, which renumbers its
/// globals through `reindex_global`) must keep a DAG a DAG: a node shared in
/// the input is moved once and shared in the output. Before 2026-11-06 it was
/// moved once per occurrence, so an image loaded at another position than
/// its canonical one came back as a tree. `tactic`/`grind` spelled Tac values
/// as `W` encodings, which share heavily; moved by an unrelated import
/// (`itree`, `coitree`), they made every grind call cost seconds more
/// (issues/grind-scope-size-cost.md). Stated on pointers, as above: equality
/// holds for the copying walk too.
#[test]
fn relocation_keeps_shared_nodes_shared() {
    heather_kernel::checks::set_skip_verification(heather_kernel::checks::SkipVerification::Full);
    // A node that has to move (it names global 0), written twice.
    let moved = Rc::new(Term::GlobalTm { var: GlobalVar::index(0), subst: LocalSubst::id(&LocalCtx::nil()) });
    let t = Term::App {
        fun: Rc::clone(&moved),
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: Rc::new(Type::Nat),
        cod: Rc::new(Type::Nat),
        arg: Rc::clone(&moved),
    };
    let out = t.reindex_global(&mut |r| r.map_var(|i| Some(i + 3))).expect("the map refuses nothing");
    match out {
        Term::App { fun, arg, .. } => {
            assert!(matches!(&*fun, Term::GlobalTm { var, .. } if *var == GlobalVar::index(3)), "the global did not move");
            assert!(Rc::ptr_eq(&fun, &arg), "relocation copied a shared node once per occurrence");
        }
        _ => panic!("relocation changed the head shape"),
    }
}

#[test]
fn global_local_commute_weakening_focus() {
    heather_kernel::checks::set_skip_verification(heather_kernel::checks::SkipVerification::Full);
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
            entries: ((0..m_p)
                .map(|_| CtxEntry { ty: Rc::new(Type::Nat), level: Level::Zero })
                .collect::<Vec<_>>()).into(),
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

/// Abstraction inverts substitution: `T.abstract_local(p)[p/z] = T`, whatever
/// subset of the occurrences the walk found
/// (`docs/goal-motive-synthesis-design.md` §3). This is the whole soundness
/// argument for motive synthesis — the eliminator's obligation `M[e/z] ≡ T` —
/// so it is a law and not a unit test, and it is checked at a *random* pattern
/// as well as at a variable, since the operation's point is that the pattern
/// need not be one.
#[test]
fn abstraction_inverts_substitution() {
    heather_kernel::checks::set_skip_verification(heather_kernel::checks::SkipVerification::Full);
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x94d049bb133111eb);
        let sc = gen_scope(&mut r);
        if sc.local.len == 0 {
            continue;
        }
        let t = gen_term(&sc, &mut r, BUDGET);
        // An `Id` over the same term twice: two positions, so a walk that
        // replaces one and not the other still has to round-trip.
        let ty = Type::Id {
            level: Level::Zero,
            ty: Rc::new(Type::Nat),
            lhs: Rc::clone(&t),
            rhs: Rc::clone(&t),
        };
        let gamma = materialize(&sc, sc.local);
        let pats = [
            Rc::new(Term::Var(LocalVar(r.below(sc.local.len)))),
            gen_term(&sc, &mut r, BUDGET),
        ];
        for p in pats {
            let Some(m) = ty.abstract_local(&p) else { continue };
            law!(seed, m.apply_local(&LocalSubst::id(&gamma).extended(Rc::clone(&p))), ty);
            // And it found every occurrence: none is left under `z`. With the
            // law above that says which type the motive is, so the walk may
            // skip and share what it likes and still have one answer.
            assert!(
                m.abstract_local(&p.shift_local(1)).is_none(),
                "seed {seed}: an occurrence was left in the motive"
            );
        }
    }
}

/// What abstraction leaves alone it does not rebuild: a subtree that mentions
/// no variable of the scope holds no occurrence of a pattern that does, and
/// needs no room made for `z`, so the motive shares it with the goal.
#[test]
fn abstraction_shares_what_it_cannot_change() {
    let closed = Rc::new(Term::Succ(Rc::new(Term::Succ(Rc::new(Term::Zero)))));
    let x = Rc::new(Term::Var(LocalVar(0)));
    let goal = Type::Id {
        level: Level::Zero,
        ty: Rc::new(Type::Nat),
        lhs: Rc::clone(&closed),
        rhs: Rc::clone(&x),
    };
    let Some(Type::Id { lhs, rhs, .. }) = goal.abstract_local(&x) else {
        panic!("the pattern occurs")
    };
    assert!(Rc::ptr_eq(&lhs, &closed));
    assert_eq!(*rhs, Term::Var(LocalVar(0)));
    // A pattern that mentions no variable can sit in such a subtree, and is
    // still found there.
    let Some(Type::Id { lhs, rhs, .. }) = goal.abstract_local(&closed) else {
        panic!("the closed pattern occurs")
    };
    assert_eq!(*lhs, Term::Var(LocalVar(0)));
    assert_eq!(*rhs, Term::Var(LocalVar(1)));
}
