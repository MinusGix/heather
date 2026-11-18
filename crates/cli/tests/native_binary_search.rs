//! The binary search example (`examples/binary-search`): its proofs check, it
//! compiles to x86, links with its C driver, and on every sorted input and
//! key it answers what Rust's `slice::partition_point` answers: the first
//! offset whose byte is not below the key.
//!
//! The theorem (`lower_bound_splits`) says the answer splits the span there;
//! this test runs the binary the example's README tells a reader to build.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
use std::io::Write;
use std::process::{Command, Stdio};

fn run(binary: &std::path::Path, bytes: &[u8], key: u8) -> String {
    let mut child = Command::new(binary).arg(key.to_string()).stdin(Stdio::piped()).stdout(Stdio::piped()).spawn().unwrap();
    child.stdin.take().unwrap().write_all(bytes).unwrap();
    let out = child.wait_with_output().unwrap();
    String::from_utf8(out.stdout).unwrap()
}

/// Sorted inputs: empty, one byte, all alike, both ends of the byte range,
/// and deterministic pseudorandom spans of every length up to 70.
fn cases() -> Vec<Vec<u8>> {
    let mut cases: Vec<Vec<u8>> = vec![vec![], vec![0], vec![255], vec![7; 9], vec![0, 255], (0..=255).collect()];
    let mut state: u64 = 0x9E37_79B9_7F4A_7C15;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for len in 0..70 {
        let spread = 1 + next() % 256;
        let mut v: Vec<u8> = (0..len).map(|_| (next() % spread) as u8).collect();
        v.sort_unstable();
        cases.push(v);
    }
    cases
}

#[test]
fn binary_search_agrees_with_partition_point() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let output = root.join(format!("target/native-binary-search-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&output).unwrap();
    let assembly = output.join("search.s");
    let result = Command::new(env!("CARGO_BIN_EXE_heather"))
        .current_dir(&root)
        .args(["compile-x86", "examples/binary-search/search.hthr", "lower_bound", "-o"])
        .arg(&assembly).args(heather_cli::showcase::native_image_args())
        .output().unwrap();
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    let binary = output.join("lowerbound");
    let linked = Command::new("cc").current_dir(&root)
        .args(["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", "examples/binary-search/main.c"])
        .arg(&assembly).arg("-o").arg(&binary).output().unwrap();
    assert!(linked.status.success(), "{}", String::from_utf8_lossy(&linked.stderr));
    for bytes in &cases() {
        let mut keys: Vec<u8> = vec![0, 1, 254, 255];
        keys.extend(bytes.iter().copied());
        keys.extend(bytes.iter().map(|b| b.wrapping_add(1)));
        keys.sort_unstable();
        keys.dedup();
        for key in keys {
            let expected = format!("{}\n", bytes.partition_point(|&b| b < key));
            assert_eq!(run(&binary, bytes, key), expected, "key {key} on {bytes:?}");
        }
    }
    std::fs::remove_dir_all(output).unwrap();
}
