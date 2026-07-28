//! Numeral arithmetic: the kernel *executing* a program. This is the area
//! the design leans on twice — ordinary `fn`s compute by kernel reduction,
//! and `Compile` equiv proofs are meant to discharge by conversion — so the
//! numbers here are the cost model of "run it in the kernel".
//!
//! Sizes deliberately run past 150, the largest numeral the
//! *elaborate-then-check* path currently admits (`issues/numeral-stack-depth`
//! owns that limit). Nothing caps numerals in the kernel itself, and these
//! families are what will show whether lifting the cap costs anything.

use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{GlobalCtx, Type};
use heather_kernel::typing::check_term;

use super::terms::{add, mul, nat_ctx, nat_value, nil_ctx, num};
use super::FUEL;
use crate::harness::{Case, Family};

pub fn families() -> Vec<Family> {
    vec![step_once(), add_family(), mul_family(), check_family()]
}

/// **One** β-step of `elim_Nat`, against the size of the eliminator's own
/// annotations. The reduction rule is
/// `elim … (su t) ⇝ s'[t/x, elim … t/y]`, and the step body here is two
/// nodes, so the rule is O(1) *if* substituting a payload does not copy it.
/// This family measures whether that holds, by growing the `base` annotation
/// — which the rule never inspects — and watching the cost of a single step.
///
/// It is the sharpest fixture in the suite, in the sense that its expected
/// exponent is **zero**: a flat line is the claim, and any slope is a bug
/// with a name.
///
/// It earned that description on its first run, when the line was not flat.
/// `SubstLocal::local_var` weakened each payload in all three namespaces at
/// insertion with no no-op fast path, so the substituted recursive occurrence
/// — annotations and all — was rebuilt three times per step even at depth
/// zero: 154 µs for one step at 1024 base nodes. Fixed 2026-07-28
/// (`subst.rs` §Shifting by zero); the same step is now **98 ns and flat**,
/// and this band is what holds it flat.
fn step_once() -> Family {
    let cases = [64u64, 128, 256, 512, 1024]
        .iter()
        .map(|&m| {
            let gamma = nil_ctx();
            // scrut = su 0, so exactly one step fires; base = m nodes the
            // rule has no reason to touch.
            let t = add(num(1), num(m));
            let go = move || {
                heather_kernel::reduce::step_term(&t, &gamma).is_some() as u64
            };
            assert!(go() == 1, "elim_Nat on su 0 did not step");
            Case::new(m, 1, go)
        })
        .collect();
    Family {
        name: "nat/step-once",
        what: "one elim_Nat β-step vs. the size of annotations it never reads",
        unit: "base nodes",
        expect_slope: Some((-0.15, 0.15)),
        cases,
    }
}

/// `add n n` normalized to a numeral: linear in `n` — `n` β-steps of
/// `elim_Nat`, each substituting a two-node step body, then `2n` weak-head
/// peels to read the answer off. ~170 ns per level.
///
/// It was **quadratic** when first measured (slope 2.02, 232 ms at n = 1024),
/// for the reason `nat/step-once` isolates; both went right together on
/// 2026-07-28 ([[subst-copies-payloads-at-depth-zero]]), and n = 1024 now
/// costs 171 µs. This family is the reason to keep believing that.
///
/// It is the number the `Compile` story cares about most: unary fuel makes a
/// fuel-indexed evaluator at least linear in fuel by construction, and a
/// quadratic per-step cost on top of that is the difference between "the
/// checker replays the program" and "the checker cannot".
fn add_family() -> Family {
    let cases = [64u64, 128, 256, 512, 1024]
        .iter()
        .map(|&n| {
            let gamma = nil_ctx();
            let t = add(num(n), num(n));
            assert!(nat_value(&t, &gamma, FUEL) == 2 * n, "add {n} {n} ≠ {}", 2 * n);
            Case::new(n, 2 * n, move || nat_value(&t, &gamma, FUEL))
        })
        .collect();
    Family {
        name: "nat/add-normalize",
        what: "normalize `add n n` to a numeral — n β-steps of elim_Nat",
        unit: "Succ levels",
        expect_slope: Some((0.85, 1.30)),
        cases,
    }
}

/// `mul n n` normalized: `n` additions of `n`, so quadratic **by
/// construction** (slope 1.98). It was cubic (2.77) while `add` was
/// quadratic, which is how a composite fixture reports a defect in its
/// component.
///
/// It earns its place twice. As a fixture it is the closest proxy available
/// for a fuel-indexed evaluator (a linear driver over a linear step), and as
/// a control it is the family that proves the scaling fit can tell one
/// exponent from another — a suite that reports slopes should contain at
/// least one case whose true exponent is known not to be 1.
fn mul_family() -> Family {
    let cases = [8u64, 12, 16, 24, 32, 48]
        .iter()
        .map(|&n| {
            let gamma = nil_ctx();
            let t = mul(num(n), num(n));
            assert!(nat_value(&t, &gamma, FUEL) == n * n, "mul {n} {n} ≠ {}", n * n);
            Case::new(n, n * n, move || nat_value(&t, &gamma, FUEL))
        })
        .collect();
    Family {
        name: "nat/mul-normalize",
        what: "normalize `mul n n` — quadratic by construction (fit control)",
        unit: "Succ levels",
        expect_slope: Some((1.75, 2.30)),
        cases,
    }
}

/// `check_term(Succ^n Zero : Nat)`. Pure checking, no reduction: the walk
/// [[numeral-stack-depth]] found by accident. `stack/check-numeral` measures
/// the same path's *stack*; this one measures its time, and the two together
/// are what a fix to that issue has to move without regressing.
fn check_family() -> Family {
    let cases = [64u64, 128, 256, 512]
        .iter()
        .map(|&n| {
            // A one-entry Γ so the walk is not the empty-context special
            // case, though the numeral is closed.
            let gamma = nat_ctx(1);
            let t = num(n);
            let ck = move || {
                let r = check_term(
                    &GlobalCtx::default(),
                    0,
                    Layer::Prog,
                    &gamma,
                    &t,
                    &Type::Nat,
                    &Level::Zero,
                    FUEL,
                );
                r.is_ok() as u64
            };
            assert!(ck() == 1, "numeral {n} does not check at Nat");
            Case::new(n, 1, ck)
        })
        .collect();
    Family {
        name: "nat/check-numeral",
        what: "check_term(Succ^n Zero : Nat) — the numeral-stack-depth path",
        unit: "Succ levels",
        expect_slope: Some((0.85, 1.30)),
        cases,
    }
}
