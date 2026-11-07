//! Literals as long as a source file check, at the default stack and worker
//! count, or are refused with a located diagnostic — never a process abort
//! (`issues/long-string-literal-stack-overflow.md`). A long literal's vector
//! is one `Term::VecItems` node and its list spine is bounded, so no term
//! the elaborator builds is as deep as the literal is long; before that, a
//! string of 2,000 characters overflowed the main thread's stack in the
//! kernel's typing walk, and a longer one a kernel worker's.
//!
//! Subprocesses, without `RUST_MIN_STACK`, so the stacks are the ones a user
//! gets; two kernel workers, so a body is checked on a worker's stack while
//! a statement holding a literal is checked on the main thread's.

use std::process::Command;

fn check(tag: &str, source: &str) -> (Option<i32>, String) {
    let dir = std::env::temp_dir().join(format!("heather-long-literals-{tag}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("probe.hthr");
    std::fs::write(&path, source).unwrap();
    let result = Command::new(env!("CARGO_BIN_EXE_heather"))
        .current_dir(concat!(env!("CARGO_MANIFEST_DIR"), "/../.."))
        .args(["check", "--kernel-workers", "2"])
        .arg(&path)
        .env_remove("RUST_MIN_STACK")
        .env_remove("HEATHER_KERNEL_WORKERS")
        .output()
        .expect("run heather");
    std::fs::remove_dir_all(dir).unwrap();
    (result.status.code(), String::from_utf8_lossy(&result.stderr).into_owned())
}

const IMPORTS: &str = "import logic; import nat; import list; import char; import string;\n";

/// `n` copies of `item`, comma-separated: a literal's elements.
fn elems(item: &str, n: usize) -> String {
    vec![item; n].join(", ")
}

#[test]
fn long_literals_check() {
    let text: String = "abcdefghi\\n".repeat(1_600);
    let len = 16_000;
    let source = format!(
        "{IMPORTS}\
         fn s() → String {{ \"{text}\" }}\n\
         theorem s_len(): s().len() = {len} {{ refl }}\n\
         theorem stated(): String::len(\"{text}\") = {len} {{ refl }}\n\
         fn inferred() → Nat {{ let t = \"{text}\"; t.len() }}\n\
         fn open(x: Nat) → List<Nat> {{ [{xs}] }}\n\
         theorem open_len(y: Nat): open(y).len() = 3000 {{ refl }}\n\
         fn rep<A>(x: A) → List<A> {{ [{xs}] }}\n\
         theorem rep_len(): rep(\"a\").len() = 3000 {{ refl }}\n\
         fn vector(x: Nat) → [Nat; 3000] {{ [{xs}] }}\n",
        xs = elems("x", 3_000),
    );
    let (code, stderr) = check("good", &source);
    assert_eq!(code, Some(0), "{stderr}");
}

#[test]
fn a_wrong_claim_about_a_long_literal_is_a_located_refusal() {
    // The negative control: the same shapes, refused by the kernel with the
    // declaration's span, and a short literal's refusal beside it.
    let text = "a".repeat(16_000);
    let source = format!(
        "{IMPORTS}\
         theorem wrong(): String::len(\"{text}\") = 15999 {{ refl }}\n\
         fn open(x: Nat) → List<Nat> {{ [{xs}] }}\n\
         theorem open_wrong(y: Nat): open(y).len() = 2999 {{ refl }}\n\
         theorem short_wrong(): String::len(\"ab\") = 3 {{ refl }}\n",
        xs = elems("x", 3_000),
    );
    let (code, stderr) = check("bad", &source);
    assert_eq!(code, Some(1), "{stderr}");
    for name in ["wrong", "open_wrong", "short_wrong"] {
        assert!(stderr.contains(&format!("the kernel rejected `{name}`")), "{name}: {stderr}");
    }
    assert!(stderr.contains("probe.hthr:2:"), "refusal needs a source span: {stderr}");
}
