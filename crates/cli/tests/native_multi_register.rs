//! Caller values survive a leaf that writes multiple scratch registers.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
mod native_support;
use native_support::Built;

#[test]
fn slow_acceptance_live_values_cross_multi_register_leaf() {
    let built = Built::callee_example_with_options("multi-register", "multi_register", ["20", "22"], &["--callable-caller"]);
    assert_eq!(built.run(), Some(108));
    let certificate = built.certificate();
    assert_eq!(certificate.matches("use_call_summary(").count(), 3);
    assert!(certificate.contains("caller_native_composed_return_word"));
    built.finish();
}
