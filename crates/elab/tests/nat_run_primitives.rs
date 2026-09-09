//! Closed `Nat` arithmetic is run arithmetic
//! (`issues/nat-run-algebra-primitives.md`): the library's structural
//! `mul`, `sub`, `leb`, `half`, `min`, `max` fold algebras the kernel
//! classifies by evaluating them, and a fold over a literal is then one
//! iteration over the literal's run, whatever the magnitude. Nothing here is
//! keyed on a name or a spelling: the same theorems are checked through a
//! locally *respelled* subtraction, which the old syntactic recognizer did
//! not match.
//!
//! The negatives beside each positive are what say the arithmetic is exact
//! and not merely fast: one off in the answer is `NotConvertible`.

use heather_elab::{ElabError, Elaborator};

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");

fn run(extra: &str) -> Result<(), String> {
    let mut e = Elaborator::with_prelude().expect("prelude");
    for (name, src) in [("logic", LOGIC), ("bool", BOOL), ("nat", NAT)] {
        if let Err(err) = e.elab_module_source(name, src) {
            return Err(match err {
                ElabError::Elab { msg, .. } => format!("{name}: {msg}"),
                other => format!("{name}: {other}"),
            });
        }
    }
    let src = format!("import logic;\nimport bool;\nimport nat;\n{extra}");
    e.elab_module_source("probe", &src).map_err(|err| match err {
        ElabError::Elab { msg, .. } => msg,
        other => format!("{other}"),
    })
}

fn ok(src: &str) {
    if let Err(msg) = run(src) {
        panic!("{msg}");
    }
}

fn refused(src: &str) {
    let msg = run(src).expect_err("a wrong closed fact must be refused");
    // A wrong equation is `NotConvertible`; a wrong proposition computes to
    // `False`, which `trivial` reports in its own words.
    assert!(msg.contains("NotConvertible") || msg.contains("`trivial` proves `True`"), "{msg}");
}

const TWO_63: u128 = 1 << 63;
const TWO_64: u128 = 1 << 64;

/// A subtraction the old shape recognizer did not see: the counters are
/// matched in the other order, through a helper.
const RESPELLED_SUB: &str = "\
fn step_down(m2: Nat, rest: Nat → Nat, n: Nat) → Nat {
    match n { Zero => Succ(m2), Succ(n2) => rest(n2) }
}
fn minus(m: Nat) → Nat → Nat {
    match m { Zero => λ n => Zero, Succ(m2) => λ n => step_down(m2, minus(m2), n) }
}
";

#[test]
fn multiplication_of_two_runs_is_one_iteration() {
    ok(&format!(
        "theorem square_of_2_32(): 4294967296 * 4294967296 = pow(2, 64) {{ refl }}\n\
         theorem product_fits(): 4294967296 * 2147483648 = {TWO_63} {{ refl }}\n\
         theorem product_of_powers(): pow(2, 40) * pow(2, 24) = pow(2, 64) {{ refl }}\n\
         theorem factorial(): fact(20) = 2432902008176640000 {{ refl }}\n",
    ));
    refused("theorem wrong(): 4294967296 * 2147483648 = 9223372036854775809 { refl }");
    refused("theorem wrong(): pow(2, 40) * pow(2, 24) = pow(2, 63) { refl }");
}

#[test]
fn subtraction_and_comparison_cancel_runs_by_meaning() {
    ok(&format!(
        "theorem difference_of_powers(): sub(pow(2, 64), pow(2, 63)) = {TWO_63} {{ refl }}\n\
         theorem truncated(): sub(pow(2, 63), pow(2, 64)) = 0 {{ refl }}\n\
         theorem below(): nat::leb(pow(2, 64), pow(2, 63)) = False {{ refl }}\n\
         theorem above(): nat::leb(pow(2, 63), pow(2, 64)) = True {{ refl }}\n\
         theorem minimum(): min(pow(2, 64), {TWO_63}) = pow(2, 63) {{ refl }}\n\
         theorem maximum(): max({TWO_63}, pow(2, 64)) = pow(2, 64) {{ refl }}\n\
         theorem ordered(): {TWO_63} < pow(2, 64) {{ trivial }}\n\
         {RESPELLED_SUB}\
         theorem respelled(): minus(pow(2, 64), pow(2, 63)) = {TWO_63} {{ refl }}\n\
         theorem respelled_truncated(): minus(pow(2, 63), pow(2, 64)) = 0 {{ refl }}\n",
    ));
    refused(&format!("theorem wrong(): sub(pow(2, 64), pow(2, 63)) = {} {{ refl }}", TWO_63 + 1));
    refused("theorem wrong(): nat::leb(pow(2, 64), pow(2, 63)) = True { refl }");
    refused(&format!("{RESPELLED_SUB}theorem wrong(): minus(pow(2, 64), pow(2, 63)) = {} {{ refl }}", TWO_63 - 1));
}

#[test]
fn course_of_values_windows_iterate_as_permutations() {
    ok(&format!(
        "theorem half_of_power(): half(pow(2, 64)) = pow(2, 63) {{ refl }}\n\
         theorem half_of_odd(): half(Succ(pow(2, 64))) = {TWO_63} {{ refl }}\n\
         theorem half_of_max(): half(18446744073709551615) = {} {{ refl }}\n\
         theorem even_power(): Even(pow(2, 64)) {{ trivial }}\n\
         theorem odd_successor(): Odd(Succ(pow(2, 64))) {{ trivial }}\n",
        (TWO_64 - 1) / 2,
    ));
    refused(&format!("theorem wrong(): half(pow(2, 64)) = {} {{ refl }}", TWO_63 + 1));
    refused("theorem wrong(): Odd(pow(2, 64)) { trivial }");
}
