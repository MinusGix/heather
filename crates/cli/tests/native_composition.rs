//! Arithmetic and computed/reordered arguments around reusable leaf calls.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
mod native_support;
use native_support::Built;

#[test]
fn slow_acceptance_straight_line_call_composition() {
    for (inputs, expected) in [(["20", "22"], 3), (["18446744073709551615", "1"], 255)] {
        let built = Built::callee_example("composition", "composition", inputs);
        assert_eq!(built.run(), Some(expected)); // (left | right) XOR ((right - left + right) - 3)
        let certificate = built.certificate();
        assert_eq!(certificate.matches("fn caller_native_leaf_summary(").count(), 1);
        assert_eq!(certificate.matches("use_call_summary(").count(), 2);
        assert_eq!(certificate.matches("call_trace_append(").count(), 2);
        assert!(certificate.contains(".preserved_rbx"));
        assert!(certificate.contains("_source_result"));
        assert!(certificate.contains("_stack_restored"));
        built.finish();
    }
}
