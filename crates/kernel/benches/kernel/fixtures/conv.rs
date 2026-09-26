//! Conversion — the operation the whole *certifying* story is a bet on. A
//! `Compile` equiv proof is meant to discharge because a concrete IR value
//! makes `simulate ir` unfold, i.e. because `conv_term` is willing to run a
//! program. These two families measure both halves of that: conversion
//! against a computation of known length, and conversion over the widest
//! available spread of term shapes.

use std::sync::Arc as Rc;

use heather_kernel::conv::conv_term;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{CtxEntry, GlobalCtx, LocalCtx, LocalVar, Term, Type};
use heather_kernel::typing::check_term;

use super::terms::{add, nil_ctx, num};
use super::FUEL;
use crate::common::wt::{gen_wt_env, gen_wt_term, perturb_conv};
use crate::common::Rng;
use crate::harness::{Case, Family};

pub fn families() -> Vec<Family> {
    vec![computed_numeral(), perturbed_pairs(), vec_literal()]
}

/// `add n n ≡ 2n` at `Nat` — an equation discharged purely by computation,
/// which is the thesis-shaped benchmark in miniature. Conversion has to run
/// the `elim_Nat` to completion and then compare `2n` `Succ` nodes.
///
/// This family is the stand-in for the fixture this suite actually wants —
/// `simulate ir fuel` converted against its result — which cannot be
/// written until [[ir-simulate-design]] fixes simulate's shape. The proxy
/// shares the load-bearing property: cost is set by the length of a
/// computation the checker is asked to replay, and unary fuel makes that at
/// least linear.
///
/// Linear (slope 1.01, ~300 ns per level — about 1.7× the cost of reducing
/// the same computation, the difference being the `2n` result nodes it also
/// compares). It was quadratic (2.20) until
/// [[subst-copies-payloads-at-depth-zero]] landed on 2026-07-28, and 512
/// levels went from 92 ms to 154 µs, which is the single clearest statement of
/// what that defect was costing the certifying story.
fn computed_numeral() -> Family {
    let cases = [32u64, 64, 128, 256, 512]
        .iter()
        .map(|&n| {
            let gamma = nil_ctx();
            let lhs = add(num(n), num(n));
            let rhs = num(2 * n);
            let go = move || {
                conv_term(
                    &GlobalCtx::default(),
                    &gamma,
                    Layer::Prog,
                    &lhs,
                    &rhs,
                    &Type::Nat,
                    &Level::Zero,
                    FUEL,
                )
                .is_ok() as u64
            };
            assert!(go() == 1, "add {n} {n} ≢ {}", 2 * n);
            Case::new(n, 1, go)
        })
        .collect();
    Family {
        name: "conv/computed-numeral",
        what: "conv(add n n, 2n) at Nat — an equation discharged by computation",
        unit: "Succ levels",
        expect_slope: Some((0.85, 1.35)),
        cases,
    }
}

/// One prepared distinct-but-convertible pair from the property-test
/// generators.
struct Pair {
    psi: GlobalCtx,
    gamma: LocalCtx,
    at: Layer,
    t: Rc<Term>,
    p: Rc<Term>,
    ty: Rc<Type>,
    l: Level,
}

/// The generated corpus: for each seed, a well-typed term and a root-level
/// β/η/letbox/elim_Nat expansion of it (`common::wt::perturb_conv`, the
/// generator behind `tests/conv_pair_properties.rs`). Converting the pair is
/// the closest thing the suite has to a *representative* workload: the shapes
/// are whatever the type-directed generator reaches, not what a human would
/// have thought to write.
///
/// Sizes are seed *prefixes*, so case `2n` is case `n` plus more of the same
/// distribution. That makes the family a throughput measurement (ns/pair)
/// rather than a scaling one, and no slope band is declared: the size axis
/// is a case count, so a slope of 1 would be arithmetic rather than a claim
/// about the kernel. What it does gate is the per-pair cost against the
/// baseline.
fn perturbed_pairs() -> Family {
    // Term budget: same order as the property tests (8), trimmed to 6 so
    // that preparing 200 seeds stays under a second — setup is untimed but
    // not free.
    const BUDGET: u32 = 6;
    let mut pairs: Vec<Pair> = vec![];
    for seed in 0.. {
        if pairs.len() == 200 {
            break;
        }
        let mut r = Rng::new(seed ^ 0x517cc1b727220a95);
        let env = gen_wt_env(&mut r);
        let (t, ty, l) = gen_wt_term(&env, &mut r, BUDGET);
        // `perturb_conv` declines on an ω-level term at a non-ΠΠ type; skip
        // that seed rather than counting a pair that does not exist.
        let Some(p) = perturb_conv(&env, &mut r, &t, &ty, &l) else { continue };
        let at = env.layer.type_layer();
        // Validate the pair the way the property test does: both sides
        // well-typed, and convertible. A pair that fails to convert would
        // make this family measure an *error path*.
        for side in [&t, &p] {
            let r = check_term(&env.psi, env.univs, env.layer, &env.gamma, side, &ty, &l, FUEL);
            assert!(r.is_ok(), "seed {seed}: generated pair is ill-typed");
        }
        let ok = conv_term(&env.psi, &env.gamma, at, &t, &p, &ty, &l, FUEL);
        assert!(ok.is_ok(), "seed {seed}: generated pair is not convertible");
        pairs.push(Pair { psi: env.psi, gamma: env.gamma, at, t, p, ty, l });
    }
    let pairs = Rc::new(pairs);

    let cases = [25u64, 50, 100, 200]
        .iter()
        .map(|&n| {
            let pairs = Rc::clone(&pairs);
            Case::new(n, n, move || {
                let mut ok = 0;
                for q in &pairs[..n as usize] {
                    ok += conv_term(
                        &q.psi, &q.gamma, q.at, &q.t, &q.p, &q.ty, &q.l, FUEL,
                    )
                    .is_ok() as u64;
                }
                ok
            })
        })
        .collect();
    Family {
        name: "conv/perturbed-pairs",
        what: "conv over generated well-typed pairs (the property-test corpus)",
        unit: "pairs",
        expect_slope: None,
        cases,
    }
}

/// `[x₀, …, xₙ₋₁] : [T; n]` as the elaborator emits it — a right-nested pair
/// whose every level is annotated with its tail's `Vec` type — checked
/// against the vector type, with an element type whose comparison is not
/// free (a decoded record code's shape: a right-nested `Σ` of units).
///
/// The literal the ELF certificate tests state their 176-byte header with
/// (`issues/elf-mutation-test-shape.md`). Linear since `Conv::vec_ty`
/// (2026-09-11) compares two spelled `Vec` types by length and element once;
/// through the encodings each level compared the element once per remaining
/// level, and the family was quadratic.
fn vec_literal() -> Family {
    fn unit() -> Type {
        Type::Unit { level: Level::Zero }
    }
    fn sigma(fst: Type, snd: Type) -> Type {
        Type::Sigma {
            fst_level: Level::Zero,
            snd_level: Level::Zero,
            fst: Rc::new(fst),
            snd: Rc::new(snd),
        }
    }
    fn vec(elem: Type, len: u64) -> Type {
        let len = if len == 0 { Term::Zero } else { Term::NatLit(len.into()) };
        Type::Vec { level: Level::Zero, elem: Rc::new(elem), len: Rc::new(len) }
    }
    let mut elem = unit();
    for _ in 0..8 {
        elem = sigma(unit(), elem);
    }
    let cases = [32u64, 64, 128, 256, 512]
        .iter()
        .map(|&n| {
            let mut acc = Term::Triv { level: Level::Zero };
            for j in (0..n).rev() {
                acc = Term::Pair {
                    fst_level: Level::Zero,
                    snd_level: Level::Zero,
                    fst_ty: Rc::new(elem.clone()),
                    snd_ty: Rc::new(vec(elem.shift_local(1), n - 1 - j)),
                    fst: Rc::new(Term::Var(LocalVar(0))),
                    snd: Rc::new(acc),
                };
            }
            let ty = vec(elem.clone(), n);
            // Γ = (x : T); the literal is `[x, …, x]`.
            let mut gamma = nil_ctx();
            gamma.entries.push(CtxEntry { ty: Rc::new(elem.clone()), level: Level::Zero });
            let go = move || {
                check_term(&GlobalCtx::default(), 0, Layer::Prog, &gamma, &acc, &ty, &Level::Zero, FUEL)
                    .is_ok() as u64
            };
            assert!(go() == 1, "the {n}-element literal does not check");
            Case::new(n, 1, go)
        })
        .collect();
    Family {
        name: "conv/vec-literal",
        what: "check([x₀…xₙ₋₁] : [T; n]) — a nested-pair literal against its vector type",
        unit: "elements",
        expect_slope: Some((0.85, 1.35)),
        cases,
    }
}
