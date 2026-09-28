//! A constructor elaboration refusal must survive as an exit status, even
//! when the CLI runs without the suite's RUST_MIN_STACK setting.

use std::process::Command;

fn check(tag: &str, source: &str, code: i32) -> String {
    let dir = std::env::temp_dir().join(format!(
        "heather-nested-constructors-{tag}-{}", std::process::id(),
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("probe.hthr");
    std::fs::write(&path, source).unwrap();
    let result = Command::new(env!("CARGO_BIN_EXE_heather"))
        .args(["check", "--kernel-workers", "1"])
        .arg(&path)
        .env_remove("RUST_MIN_STACK")
        .output()
        .expect("run heather");
    std::fs::remove_dir_all(dir).unwrap();
    let stderr = String::from_utf8_lossy(&result.stderr).into_owned();
    assert_eq!(result.status.code(), Some(code), "{tag}: {stderr}");
    stderr
}

fn spine(depth: usize) -> String {
    format!("{}Nil{}", "Cons(0, ".repeat(depth), ")".repeat(depth))
}

#[test]
fn deep_checking_and_inference_refuse_without_aborting() {
    for (tag, body) in [
        ("checking", spine(1000)),
        ("inference", format!("let xs = {}; xs", spine(1000))),
    ] {
        let source = format!(
            "inductive L {{ Nil, Cons(Nat, L) }}\nfn l() -> L {{ {body} }}",
        );
        let stderr = check(tag, &source, 1);
        assert!(stderr.contains("expression elaboration depth limit exceeded"), "{stderr}");
        assert!(stderr.contains("probe.hthr:"), "refusal needs a source span: {stderr}");
    }
    // Parameter inference descends before build_ctor is entered: a budget on
    // the constructor builder alone would miss this recursive route.
    let source = format!(
        "inductive Box<A> {{ Wrap(A) }}\nfn l() -> Nat {{ let xs = {}0{}; 0 }}",
        "Wrap(".repeat(1000), ")".repeat(1000),
    );
    let stderr = check("parameter_inference", &source, 1);
    assert!(stderr.contains("expression elaboration depth limit exceeded"), "{stderr}");
}

#[test]
fn ordinary_nested_constructors_still_kernel_check() {
    let source = format!(
        "inductive L {{ Nil, Cons(Nat, L) }}\nfn l() -> L {{ {} }}", spine(100),
    );
    check("ordinary", &source, 0);
}
