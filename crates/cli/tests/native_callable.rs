//! The outer entry consumes a reusable composed-function ABI/source summary.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
mod native_support;
use native_support::Built;

#[test]
fn slow_acceptance_entry_consumes_composed_summary() {
    for (inputs, expected) in [(["20", "22"], 3), (["18446744073709551615", "1"], 255)] {
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
}
