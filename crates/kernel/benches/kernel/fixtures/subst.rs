//! Substitution on deep terms — the walk under every other kernel
//! operation. Nothing here reduces or checks anything, so a regression in
//! these two families localizes to `subst.rs` alone.

use heather_kernel::level::Level;
use heather_kernel::rc::Rc;
use heather_kernel::term::{LocalSubst, Term, Type};

use super::terms::{lam_chain, lam_depth, nat_ctx, num, rt, rty, v};
use crate::common::count_term;
use crate::harness::{Case, Family};

const DEPTHS: [u32; 5] = [32, 64, 128, 256, 512];

pub fn families() -> Vec<Family> {
    vec![shift(), single(), shared_dag()]
}

/// `shift_local` over a λ-chain: renumbers the ambient reference at every
/// level and rebuilds the spine. The cheapest possible traversal — every
/// node is visited, none is replaced — so this family is the suite's
/// baseline for "what does one pass over a term cost".
fn shift() -> Family {
    let cases = DEPTHS
        .iter()
        .map(|&n| {
            let t = lam_chain(n);
            let size = count_term(&t);
            // Structural check at setup: the shift must preserve the spine
            // and change the term (a shift that returned its input would be
            // both wrong and fast).
            let shifted = t.shift_local(1);
            assert!(shifted != t, "shift_local(1) was a no-op at depth {n}");
            assert!(lam_depth(&shifted) == n as u64, "shift lost binders at depth {n}");
            Case::new(size, n as u64, move || lam_depth(&t.shift_local(1)))
        })
        .collect();
    Family {
        name: "subst/shift-local",
        what: "shift_local(1) over a λ-chain — one full pass, no replacement",
        unit: "nodes",
        // One pass, one allocation per node: linear or the walk is wrong.
        expect_slope: Some((0.85, 1.25)),
        cases,
    }
}

/// β-substitution `[s/x]` into a λ-chain body: the same walk, but with a
/// replacement at the leaves, so it also pays for the substituted term's
/// shifts under `n` binders. The interesting comparison is against
/// `shift-local` at equal node count: the gap is what replacement costs.
fn single() -> Family {
    let cases = DEPTHS
        .iter()
        .map(|&n| {
            // Γ = x₀ : Nat, plus the target entry the body was scoped in.
            let gamma = nat_ctx(1);
            let body = lam_chain(n);
            let size = count_term(&body);
            let delta = LocalSubst::id(&gamma).extended(rt(num(3)));
            let out = body.apply_local(&delta);
            assert!(out != body, "[3/x] was a no-op at depth {n}");
            assert!(lam_depth(&out) == n as u64, "[3/x] lost binders at depth {n}");
            Case::new(size, n as u64, move || lam_depth(&body.apply_local(&delta)))
        })
        .collect();
    Family {
        name: "subst/apply-local",
        what: "β-substitution [3/x] into a λ-chain — a pass with replacement",
        unit: "nodes",
        expect_slope: Some((0.85, 1.35)),
        cases,
    }
}

/// `[3/x]` into `tₙ` for `t₀ := x`, `tᵢ := elim_Nat(tᵢ₋₁; Nat; tᵢ₋₁; _ ih.
/// Succ ih)` with **both** occurrences of `tᵢ₋₁` the same `Rc`: a term whose
/// tree is 2ⁿ nodes and whose DAG is n. The elaborator's terms are shaped
/// like this (a `let`'s value read twice, a type annotation repeated down a
/// spine), and the substitution memo (`subst.rs` §Keeping a shared DAG
/// shared) is what keeps a pass over them linear in the DAG. The checksum is
/// the depth of the result's scrutinee chain.
fn shared_dag() -> Family {
    fn depth(t: &Term) -> u64 {
        let mut n = 0;
        let mut cur = t;
        while let Term::ElimNat { scrut, .. } = cur {
            n += 1;
            cur = scrut;
        }
        n
    }
    let cases = [8u64, 16, 32, 64, 128]
        .iter()
        .map(|&n| {
            let mut t = rt(v(0));
            for _ in 0..n {
                t = rt(Term::ElimNat {
                    level: Level::Zero,
                    motive: rty(Type::Nat),
                    base: Rc::clone(&t),
                    step: rt(Term::Succ(rt(v(0)))),
                    scrut: t,
                });
            }
            let gamma = nat_ctx(1);
            let delta = LocalSubst::id(&gamma).extended(rt(num(3)));
            let out = t.apply_local(&delta);
            assert!(out != *t, "[3/x] was a no-op at depth {n}");
            Case::new(n, n, move || depth(&t.apply_local(&delta)))
        })
        .collect();
    Family {
        name: "subst/shared-dag",
        what: "[3/x] into a term 2ⁿ nodes as a tree, n as a DAG — the substitution memo",
        unit: "DAG levels",
        expect_slope: Some((0.80, 1.35)),
        cases,
    }
}
