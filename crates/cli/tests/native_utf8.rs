//! The UTF-8 validator example (`examples/utf8`): its proofs check, it
//! compiles to x86, links with its C driver, and on every input it answers
//! what Rust's `std::str::from_utf8` answers: the length of the longest
//! valid prefix (`valid_up_to`), or the whole input.
//!
//! The theorem says the compiled function is the strict decoder's verdict;
//! this test is the outside check that "strict decoder" is the one the world
//! uses, run against the binary the example's README tells a reader to build.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
use std::io::Write;
use std::process::{Command, Stdio};

fn expected(bytes: &[u8]) -> String {
    match std::str::from_utf8(bytes) {
        Ok(_) => "valid\n".to_string(),
        Err(e) => format!("invalid at byte {}\n", e.valid_up_to()),
    }
}

fn run(binary: &std::path::Path, bytes: &[u8]) -> String {
    let mut child = Command::new(binary).stdin(Stdio::piped()).stdout(Stdio::piped()).spawn().unwrap();
    child.stdin.take().unwrap().write_all(bytes).unwrap();
    let out = child.wait_with_output().unwrap();
    String::from_utf8(out.stdout).unwrap()
}

/// Inputs at every boundary the decoder draws: each lead class, overlong
/// forms, the surrogates, the last scalar value and the first past it, and
/// sequences cut short by the end.
fn boundary_cases() -> Vec<Vec<u8>> {
    let mut cases: Vec<Vec<u8>> = vec![
        vec![],
        b"plain ascii".to_vec(),
        "h\u{e9}llo \u{20ac} \u{1f600}".as_bytes().to_vec(),
        vec![0x80],
        vec![0xBF],
        vec![0xC0, 0x80],
        vec![0xC1, 0xBF],
        vec![0xC2, 0x80],
        vec![0xDF, 0xBF],
        vec![0xE0, 0x80, 0x80],
        vec![0xE0, 0x9F, 0xBF],
        vec![0xE0, 0xA0, 0x80],
        vec![0xED, 0x9F, 0xBF],
        vec![0xED, 0xA0, 0x80],
        vec![0xED, 0xBF, 0xBF],
        vec![0xEE, 0x80, 0x80],
        vec![0xEF, 0xBF, 0xBF],
        vec![0xF0, 0x8F, 0xBF, 0xBF],
        vec![0xF0, 0x90, 0x80, 0x80],
        vec![0xF4, 0x8F, 0xBF, 0xBF],
        vec![0xF4, 0x90, 0x80, 0x80],
        vec![0xF5, 0x80, 0x80, 0x80],
        vec![0xF8, 0x80, 0x80, 0x80, 0x80],
        vec![0xFF],
        vec![0xC2],
        vec![0xE2, 0x82],
        vec![0xF0, 0x9F, 0x98],
        vec![b'a', 0xE2, 0x82, b'b'],
        vec![0xC2, 0x41],
    ];
    for lead in [0xC2u8, 0xE2, 0xF0] {
        for cut in 1..4 {
            let mut v = b"ok ".to_vec();
            v.extend(std::iter::repeat(lead).take(1));
            v.extend(std::iter::repeat(0x80).take(cut - 1));
            cases.push(v);
        }
    }
    cases
}

/// Deterministic pseudorandom inputs: valid text with one byte changed, and
/// bytes drawn mostly from the interesting range.
fn random_cases(count: usize) -> Vec<Vec<u8>> {
    let mut state: u64 = 0x9E37_79B9_7F4A_7C15;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let text = "aé€😀zß\u{7ff}\u{800}\u{ffff}\u{10000}\u{10ffff}".as_bytes();
    let mut out = Vec::new();
    for k in 0..count {
        let len = (next() % 24) as usize;
        let v: Vec<u8> = if k % 2 == 0 {
            let mut v: Vec<u8> = (0..len).map(|_| text[(next() % text.len() as u64) as usize]).collect();
            if !v.is_empty() {
                let at = (next() % v.len() as u64) as usize;
                v[at] = next() as u8;
            }
            v
        } else {
            (0..len).map(|_| if next() % 3 == 0 { next() as u8 & 0x7F } else { 0x80 | next() as u8 }).collect()
        };
        out.push(v);
    }
    out
}

#[test]
fn utf8_validator_agrees_with_rust() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let output = root.join(format!("target/native-utf8-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&output).unwrap();
    let assembly = output.join("utf8.s");
    let result = Command::new(env!("CARGO_BIN_EXE_heather"))
        .current_dir(&root)
        .args(["compile-x86", "examples/utf8/utf8_check.hthr", "utf8_valid_up_to", "-o"])
        .arg(&assembly).arg("--cache-dir").arg(heather_cli::showcase::native_test_images())
        .output().unwrap();
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    let binary = output.join("utf8check");
    let linked = Command::new("cc").current_dir(&root)
        .args(["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", "examples/utf8/main.c"])
        .arg(&assembly).arg("-o").arg(&binary).output().unwrap();
    assert!(linked.status.success(), "{}", String::from_utf8_lossy(&linked.stderr));
    let mut cases = boundary_cases();
    cases.extend(random_cases(400));
    for bytes in &cases {
        assert_eq!(run(&binary, bytes), expected(bytes), "on {bytes:02x?}");
    }
    std::fs::remove_dir_all(output).unwrap();
}
