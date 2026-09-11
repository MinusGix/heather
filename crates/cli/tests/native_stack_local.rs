//! A live caller slot survives a callee that clobbers its scratch register.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
mod native_support;
use native_support::Built;

#[test]
fn caller_reloads_its_live_stack_local() {
    let built = Built::callee_example("stack-local", "stack_local", ["20", "22"]);
    assert_eq!(built.run(), Some(40));
    let bytes = built.bytes();
    for instruction in [&[0x4c, 0x89, 0x1c, 0x24][..], &[0x4c, 0x8b, 0x1c, 0x24][..], &[0x4d, 0x31, 0xdb][..]] {
        assert!(bytes.windows(instruction.len()).any(|window| window == instruction));
    }
    let proof = built.certificate();
    for claim in ["StoreStack64(R11)", "LoadStack64(R11)", "NativeIntegerCallContract", "_callee_memory_effects(gprs, flags, stack)(", "_saved_value", "_stack_restored", "_loaded_execution"] {
        assert!(proof.contains(claim), "missing {claim}");
    }
    built.finish();
}
