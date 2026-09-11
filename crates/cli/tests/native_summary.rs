//! One checked callee summary used with different inputs and placements.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
mod native_support;
use native_support::Built;

#[test]
fn two_placed_calls_share_one_summary() {
    let built = Built::callee_example("summary", "reused_callee", ["21", "1"]);
    assert_eq!(built.run(), Some(3));
    let certificate = built.certificate();
    assert_eq!(certificate.matches("fn caller_native_leaf_summary(").count(), 1);
    assert_eq!(certificate.matches("use_call_summary(").count(), 2);
    assert_eq!(certificate.matches("call_trace_append(").count(), 2);
    assert!(certificate.contains("caller_native_leaf_second_values"));
    assert!(certificate.contains("StoreStack64(Rdi)"));
    assert!(certificate.contains("_dead_frame_byte"));
    assert!(certificate.contains("_callee_preserved_rsi"));
    built.finish();
}
