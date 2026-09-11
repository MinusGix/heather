//! An actual nested CALL/RET executable, with no host linker or initial-stack dependency.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
mod native_support;
use native_support::Built;

#[test]
fn nested_calls_return_the_source_result() {
    let built = Built::callee_example("calls", "calls", ["20", "22"]);
    let file = built.bytes();
    assert_eq!(u16::from_le_bytes(file[56..58].try_into().unwrap()), 3);
    assert_eq!(u64::from_le_bytes(file[24..32].try_into().unwrap()), 0x4000e8);
    // The additional segment is RW, zero-filled, and disjoint from code.
    assert_eq!(u32::from_le_bytes(file[180..184].try_into().unwrap()), 6);
    assert_eq!(u64::from_le_bytes(file[192..200].try_into().unwrap()), 0x401000);
    assert_eq!(u64::from_le_bytes(file[208..216].try_into().unwrap()), 0);
    assert_eq!(u64::from_le_bytes(file[216..224].try_into().unwrap()), 4096);
    assert_eq!(built.run(), Some(197));
    let certificate = built.certificate();
    for claim in ["_source_call", "_file_correct", "_loaded_execution", "_callee_contract", "_exit_request", "_syscall_fetched", "_stack_restored", "_aligned_call"] {
        assert!(certificate.contains(claim), "missing {claim}");
    }
    built.finish();
}
