//! Checked caller saves protect a live word from a multi-register leaf.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
mod native_support;
use native_support::Built;

// One test per input pair, so the two builds run side by side.
#[test]
fn slow_acceptance_checked_stack_save_and_restore() {
    check(["20", "22"], 88);
}

#[test]
fn slow_acceptance_checked_stack_save_and_restore_wrapping_inputs() {
    check(["18446744073709551615", "1"], 4);
}

fn check(inputs: [&str; 2], expected: i32) {
    let built = Built::callee_example_with_options("stack-save", "stack_save", inputs, &["--callable-caller"]);
    assert_eq!(built.run(), Some(expected));
    let certificate = built.certificate();
    assert!(certificate.contains("StoreStack64(R11)"));
    assert!(certificate.contains("LoadStack64(R11)"));
    assert!(certificate.contains("caller_native_composed_saved_roundtrip"));
    assert!(certificate.contains("caller_native_composed_outside_401fe8_401ff0"));
    assert!(certificate.contains("caller_native_composed_outside_401ff0_401ff8"));
    assert_eq!(certificate.matches("use_call_summary(").count(), 3);
    built.finish();
}
