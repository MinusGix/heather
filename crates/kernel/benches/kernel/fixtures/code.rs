//! The code recursors and the checker at large: the heaviest single
//! operations in the kernel.
//!
//! `elim^Typ`/`elim^Trm` carry a **45-branch** table, each branch under its
//! own telescope, so one such term is by far the largest thing the checker
//! sees — `scripts/test` raises `RUST_MIN_STACK` because of it. Two families
//! separate the fixed cost (checking the table) from the marginal cost
//! (recursing over the scrutinee's code), because they regress for different
//! reasons: the first with a change to the branch specs in `rec.rs`, the
//! second with a change to how branches are instantiated in `reduce.rs`.
//!
//! The suite's remaining checker fixture is a throughput number over the
//! generated well-typed corpus. What it is *not* is a measurement of
//! checking the declarations the tier-1 lowering emits: those come from
//! `elab`, which sits above the kernel and cannot be reached from here —
//! `issues/frontend-benchmarks.md` owns that number.

use std::rc::Rc;

use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::reduce::whnf_term;
use heather_kernel::term::{GlobalCtx, Term, Type};
use heather_kernel::typing::check_term;

use super::terms::{nil_ctx, pi_chain, rty};
use super::FUEL;
use crate::common::wt::{gen_wt_env, gen_wt_term, identity_branches, identity_motives};
use crate::common::{count_type, Rng};
use crate::harness::{Case, Family};

const CODE_DEPTHS: [u32; 5] = [1, 2, 4, 8, 16];

pub fn families() -> Vec<Family> {
    vec![check_identity_recursor(), whnf_identity_recursor(), check_generated()]
}

/// `elim^Typ` with the identity motives and branches over `box (Π-chain)`.
fn identity_recursor(code: &Rc<Type>) -> Term {
    Term::ElimCodeTy {
        ty_motive_level: Level::Zero,
        tm_motive_level: Level::Zero,
        motives: identity_motives(),
        branches: identity_branches(),
        code_level: Level::Zero,
        ctx: nil_ctx(),
        scrut: Rc::new(Term::BoxTy(Rc::clone(code))),
    }
}

/// Checking the recursor. The 45 branches are a **fixed** cost, so this
/// family measures a constant plus a small marginal term, and declares no
/// slope band: an exponent fitted through a dominant constant says nothing.
/// The number that matters is the absolute one at the smallest size — "what
/// does one code recursor cost to check" — and the baseline gates exactly
/// that.
fn check_identity_recursor() -> Family {
    let cases = CODE_DEPTHS
        .iter()
        .map(|&n| {
            let gamma = nil_ctx();
            let code = rty(pi_chain(n));
            let size = count_type(&code);
            let t = identity_recursor(&code);
            let expect = Type::CodeTy { ctx: nil_ctx(), level: Level::Zero };
            let go = move || {
                check_term(
                    &GlobalCtx::default(),
                    0,
                    Layer::Meta,
                    &gamma,
                    &t,
                    &expect,
                    &Level::Zero,
                    FUEL,
                )
                .is_ok() as u64
            };
            assert!(go() == 1, "the identity elim^Typ over a Π-chain of {n} does not check");
            Case::new(size, 1, go)
        })
        .collect();
    Family {
        name: "code/check-identity-recursor",
        what: "check_term of elim^Typ — the 45-branch table, a fixed cost",
        unit: "code nodes",
        expect_slope: None,
        cases,
    }
}

/// Reducing the recursor. Here the code size *is* the work: the identity
/// recursor re-boxes its scrutinee node by node, instantiating branch bodies
/// under their telescopes as it goes, so this is the marginal cost of
/// recursion over code — the operation every meta-program pays for.
fn whnf_identity_recursor() -> Family {
    let cases = CODE_DEPTHS
        .iter()
        .map(|&n| {
            let gamma = nil_ctx();
            let code = rty(pi_chain(n));
            let size = count_type(&code);
            let t = identity_recursor(&code);
            let w = whnf_term(&t, &gamma, FUEL).expect("identity elim^Typ exhausted fuel");
            assert!(
                w == Term::BoxTy(Rc::clone(&code)),
                "the identity elim^Typ is not the identity at Π-chain {n}"
            );
            // Checksum is the head shape, not the whole term: a structural
            // comparison would cost as much as the reduction it validates.
            Case::new(size, 1, move || {
                let w = whnf_term(&t, &gamma, FUEL).expect("exhausted fuel");
                matches!(w, Term::BoxTy(_)) as u64
            })
        })
        .collect();
    Family {
        name: "code/whnf-identity-recursor",
        what: "whnf of elim^Typ over code — branch instantiation per code node",
        unit: "code nodes",
        // A loose band on purpose, and the loosest in the suite. Cost here is
        // a per-recursor fixed part plus a per-node part, and at 3–33 code
        // nodes the fixed part dilutes the fit: the slope was 0.86 while
        // branch instantiation copied its payloads, 0.43 once it did not
        // ([[subst-copies-payloads-at-depth-zero]]), and ~0.02 now that the
        // closed branch bodies are skipped outright
        // ([[subst-visits-closed-subtrees]]) — the marginal cost keeps
        // falling, so the constant dominates more. Neither number is an
        // exponent worth defending; what this family gates is the absolute
        // per-node cost against the baseline. The band is here only to catch
        // a return to superlinear.
        expect_slope: Some((-0.20, 1.20)),
        cases,
    }
}

/// `check_term` over the generated well-typed corpus — the checker's
/// throughput on the widest spread of term shapes available. Prefix sizes, so
/// the reported number is ns/term; no slope band, for the reason given on
/// `conv/perturbed-pairs`.
fn check_generated() -> Family {
    const BUDGET: u32 = 6;
    struct Item {
        psi: GlobalCtx,
        gamma: heather_kernel::term::LocalCtx,
        layer: Layer,
        univs: u32,
        t: Rc<Term>,
        ty: Rc<Type>,
        l: Level,
    }
    let mut items = vec![];
    for seed in 0..200u64 {
        let mut r = Rng::new(seed ^ 0xff51afd7ed558ccd);
        let env = gen_wt_env(&mut r);
        let (t, ty, l) = gen_wt_term(&env, &mut r, BUDGET);
        let ok = check_term(&env.psi, env.univs, env.layer, &env.gamma, &t, &ty, &l, FUEL);
        assert!(ok.is_ok(), "seed {seed}: generated term is ill-typed");
        items.push(Item {
            psi: env.psi,
            gamma: env.gamma,
            layer: env.layer,
            univs: env.univs,
            t,
            ty,
            l,
        });
    }
    let items = Rc::new(items);
    let cases = [25u64, 50, 100, 200]
        .iter()
        .map(|&n| {
            let items = Rc::clone(&items);
            Case::new(n, n, move || {
                let mut ok = 0;
                for i in &items[..n as usize] {
                    ok += check_term(
                        &i.psi, i.univs, i.layer, &i.gamma, &i.t, &i.ty, &i.l, FUEL,
                    )
                    .is_ok() as u64;
                }
                ok
            })
        })
        .collect();
    Family {
        name: "check/generated-terms",
        what: "check_term over the generated corpus — checker throughput",
        unit: "terms",
        expect_slope: None,
        cases,
    }
}
