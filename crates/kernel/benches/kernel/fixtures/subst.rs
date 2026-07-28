//! Substitution on deep terms — the walk under every other kernel
//! operation. Nothing here reduces or checks anything, so a regression in
//! these two families localizes to `subst.rs` alone.

use heather_kernel::term::LocalSubst;

use super::terms::{lam_chain, lam_depth, nat_ctx, num, rt};
use crate::common::count_term;
use crate::harness::{Case, Family};

const DEPTHS: [u32; 5] = [32, 64, 128, 256, 512];

pub fn families() -> Vec<Family> {
    vec![shift(), single()]
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
