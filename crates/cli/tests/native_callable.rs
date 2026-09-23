//! The outer entry consumes a reusable composed-function ABI/source summary.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
mod native_support;
use native_support::Built;

// One test per input pair, so the two builds run side by side.
#[test]
fn slow_acceptance_entry_consumes_composed_summary() {
    check(["20", "22"], 3);
}

#[test]
fn slow_acceptance_entry_consumes_composed_summary_wrapping_inputs() {
    check(["18446744073709551615", "1"], 255);
}

fn check(inputs: [&str; 2], expected: i32) {
    let built = Built::callee_example_with_options("callable", "composition", inputs, &["--callable-caller"]);
    assert_eq!(built.run(), Some(expected));
    let certificate = built.certificate();
    assert_eq!(certificate.matches("fn caller_native_composed_summary(").count(), 1);
    assert_eq!(certificate.matches("use_call_summary(").count(), 3);
    assert!(certificate.contains("caller_native_caller_contract(gprs, flags, stack).result_correct"));
    assert!(certificate.contains("caller_native_composed_return_word"));
    assert!(certificate.contains("preserved_rbx := caller_native_composed_known_"));
    assert!(certificate.contains("preserved_r15 := caller_native_composed_known_"));
    assert!(!certificate.contains("theorem caller_native_source_result("));
    built.finish();
}
