//! Distinct live caller words survive a leaf that clobbers both registers.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
mod native_support;
use native_support::Built;

// One test per input pair, so the two builds run side by side.
#[test]
fn slow_acceptance_multiple_live_stack_slots() {
    check(["20", "22"], 66);
}

#[test]
fn slow_acceptance_multiple_live_stack_slots_wrapping_inputs() {
    check(["18446744073709551615", "1"], 253);
}

fn check(inputs: [&str; 2], expected: i32) {
    let built = Built::callee_example_with_options("multi-stack-save", "multi_stack_save", inputs, &["--callable-caller"]);
    assert_eq!(built.run(), Some(expected));
    let certificate = built.certificate();
    for register in ["R10", "R11"] {
        assert!(certificate.contains(&format!("StoreStack64({register})")));
        assert!(certificate.contains(&format!("LoadStack64({register})")));
    }
    assert!(certificate.contains("caller_native_composed_saved_roundtrip_401fe0"));
    assert!(certificate.contains("caller_native_composed_saved_roundtrip_401fe8"));
    assert!(certificate.contains("caller_native_composed_outside_401fe8_401fe0"));
    assert!(certificate.contains("caller_native_composed_outside_401fd8_401ff8"));
    assert_eq!(certificate.matches("use_call_summary(").count(), 2);
    built.finish();
}
