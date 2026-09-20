//! Shared source values select one definition, including across another call.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
mod native_support;
use native_support::Built;

#[test]
fn slow_acceptance_shared_values_cross_distinct_leaf_calls() {
    let built = Built::callee_example_with_options("sharing", "sharing", ["20", "22"], &["--callable-caller"]);
    assert_eq!(built.run(), Some(50));
    let certificate = built.certificate();
    assert_eq!(certificate.matches("use_call_summary(").count(), 3);
    assert!(certificate.contains("caller_native_composed_summary"));
    built.finish();
}
