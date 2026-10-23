//! The simulate-shaped fixture ([[ir-simulate-design]] §11 item 5): what a
//! `Compile` equiv certificate costs to discharge, isolated to its two axes.
//!
//! The real object — `lib/certgen/ir_v1.hthr`'s `eval` run by conversion — cannot
//! live in this suite: it exists only as elaborator output, and the kernel
//! (dev-dependencies included) stays at zero dependencies. What CAN live
//! here is the cost mechanism, hand-built: a fuel-indexed evaluator is an
//! `elim_Nat` whose step branch is a large term (the whole interpreter,
//! inlined at every use — the elaborator has no other way to reference a
//! `fn`), and every fuel step substitutes into that branch. So the model is
//!
//!   evalish(fuel, s) = elim_Nat^0 (_. Nat) 0 (x, y. fst⟨Succ y, num s⟩) fuel
//!
//! — per step, the `num s` payload stands in for the inlined interpreter
//! body: substitution must walk it ([[subst-visits-closed-subtrees]]), the
//! `fst` then discards it, and the surviving `Succ` chain is the answer the
//! conversion compares. Two families, one per axis:
//!
//! - `conv/simulate-payload`: fuel fixed, payload size is the unit. This
//!   slope was 0.91 while substitution walked the closed payload per step,
//!   and is ~0 since the bounds round ([[subst-visits-closed-subtrees]])
//!   made the walk an O(1) skip — this family was that round's acceptance
//!   instrument. What the metadata cannot buy is what the definitions round
//!   ([[simulate-conversion-cost]]) still owns: the *size* of the term
//!   (statements, ih copies) and `.code` stability, via a step body that
//!   *references* its interpreter instead of containing it. When kernel
//!   definitions land, add the third family (payload behind a Ψ-definition)
//!   and the win is the gap between them.
//! - `conv/simulate-depth`: payload fixed, fuel is the unit. Expected ~1
//!   (per-step work is constant here by construction); ir_v1's measured
//!   superlinearity in depth came from state that *grows* along the run
//!   (environments, result chains), which this shape deliberately excludes
//!   so the two effects don't confound.
//!
//! **Amendment, 2026-07-31** ([[nbe-conversion-round]]). `ir_v1`'s
//! superlinearity is gone: conversion evaluates into a value domain, so an
//! eliminator's β extends an environment instead of copying its branch, and
//! the growing state that this shape excludes no longer costs anything to
//! carry. Both families kept their slopes across that change (payload flat,
//! depth ~1) and both got ~2.3–2.5× slower in constant — a lazy
//! sub-structure is an allocation where the rewriter had an `Rc::clone`,
//! and this is a workload with no sharing to buy it back
//! ([[value-domain-allocation-constant]]). §11 item 5's later re-aim, a
//! depth-of-*nesting* family, is retired rather than owed: four hand-built
//! kernel families failed to reproduce that axis at all
//! (`docs/nbe-conversion-design.md` §12), its instrument is
//! `scripts/probe-whnf-sharing` at the CLI, and its subject no longer
//! exists.

use heather_kernel::conv::conv_term;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{GlobalCtx, Term, Type};

use super::terms::{nil_ctx, num, rt, rty, v};
use super::FUEL;
use crate::harness::{Case, Family};

pub fn families() -> Vec<Family> {
    vec![payload(), depth()]
}

/// `elim_Nat^0 (_. Nat) 0 (x, y. fst⟨Succ y, num s⟩) (num fuel)` — reduces
/// to `num fuel`, paying one payload walk per step.
fn evalish(fuel: u64, s: u64) -> Term {
    let step = Term::Fst {
        fst_level: Level::Zero,
        snd_level: Level::Zero,
        fst_ty: rty(Type::Nat),
        snd_ty: rty(Type::Nat),
        pair: rt(Term::Pair {
            fst_level: Level::Zero,
            snd_level: Level::Zero,
            fst_ty: rty(Type::Nat),
            snd_ty: rty(Type::Nat),
            fst: rt(Term::Succ(rt(v(0)))),
            snd: rt(num(s)),
        }),
    };
    Term::ElimNat {
        level: Level::Zero,
        motive: rty(Type::Nat),
        base: rt(Term::Zero),
        step: rt(step),
        scrut: rt(num(fuel)),
    }
}

fn case(fuel: u64, s: u64, unit: u64) -> Case {
    let gamma = nil_ctx();
    let lhs = evalish(fuel, s);
    let rhs = num(fuel);
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
    assert!(go() == 1, "evalish({fuel}, {s}) ≢ {fuel}");
    Case::new(unit, 1, go)
}

/// Per-step cost against step-body size, the inlining axis.
fn payload() -> Family {
    const STEPS: u64 = 64;
    let cases = [32u64, 64, 128, 256, 512, 1024].iter().map(|&s| case(STEPS, s, s)).collect();
    Family {
        name: "conv/simulate-payload",
        what: "evalish at fixed fuel — cost of the step branch's dead weight, skipped per step",
        unit: "payload nodes",
        // Flat since [[subst-visits-closed-subtrees]]; a slope climbing back
        // toward 1 means per-step cost depends on the body's size again.
        expect_slope: Some((-0.20, 0.35)),
        cases,
    }
}

/// Total cost against fuel at a fixed step body, the run-length axis.
fn depth() -> Family {
    const PAYLOAD: u64 = 256;
    let cases = [16u64, 32, 64, 128, 256].iter().map(|&f| case(f, PAYLOAD, f)).collect();
    Family {
        name: "conv/simulate-depth",
        what: "evalish at fixed payload — cost of running longer at constant per-step work",
        unit: "fuel steps",
        expect_slope: Some((0.85, 1.35)),
        cases,
    }
}
