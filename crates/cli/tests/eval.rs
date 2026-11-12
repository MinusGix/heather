//! `heather eval`: a closed term's value printed, by type, and labelled as
//! an evaluation (`crates/cli/src/eval.rs`). Each case is a subprocess over
//! one small module, without a cache, so what it reads is what this build
//! elaborates.

use std::process::Command;

const SOURCE: &str = "import bool; import nat; import list; import option; import char; import string;\n\
    fn greeting(name: String) → String { \"hello, \" ++ name ++ \"!\" }\n\
    fn squares(n: Nat) → List<Nat> { match n { Zero => [], Succ(k) => squares(k) ++ [n * n] } }\n\
    fn first_positive(xs: List<Nat>) → Option<Nat> { match xs { Nil => None, Cons(x, rest) => match x { Zero => first_positive(rest), Succ(_) => Some(x) } } }\n";

/// `heather eval` over [`SOURCE`] with `args` after the file: the exit
/// code, stdout and stderr.
fn eval(tag: &str, args: &[&str]) -> (Option<i32>, String, String) {
    let dir = std::env::temp_dir().join(format!("heather-eval-{tag}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("eval_probe.hthr");
    std::fs::write(&path, SOURCE).unwrap();
    let result = Command::new(env!("CARGO_BIN_EXE_heather"))
        .current_dir(concat!(env!("CARGO_MANIFEST_DIR"), "/../.."))
        .arg("eval")
        .arg(&path)
        .args(args)
        .output()
        .expect("run heather");
    std::fs::remove_dir_all(dir).unwrap();
    let text = |bytes: &[u8]| String::from_utf8_lossy(bytes).into_owned();
    (result.status.code(), text(&result.stdout), text(&result.stderr))
}

#[test]
fn a_closed_term_prints_its_value_by_type() {
    // A string at the top is its text; a list, an option and a string
    // inside them are written as values.
    let (code, out, err) = eval("values", &["[greeting(\"wörld\")]", "--type", "List<String>"]);
    assert_eq!(code, Some(0), "{err}");
    assert_eq!(out, "[\"hello, wörld!\"]\n");
    assert!(err.contains("an evaluation: untrusted, it proves nothing and is not a check"), "{err}");
    let (code, out, err) = eval("text", &["greeting(\"a \\\"b\\\"\")"]);
    assert_eq!(code, Some(0), "{err}");
    assert_eq!(out, "hello, a \"b\"!\n");
    let (code, out, err) = eval("numbers", &["Some(squares(4))"]);
    assert_eq!(code, Some(0), "{err}");
    assert_eq!(out, "Some([1, 4, 9, 16])\n");
    let (code, out, err) = eval("option", &["first_positive([0, 0])"]);
    assert_eq!(code, Some(0), "{err}");
    assert_eq!(out, "None\n");
}

#[test]
fn a_read_past_the_limit_is_cut_and_says_so() {
    // Each element is a tag and its number: six numbers are three squares.
    let (code, out, err) = eval("cut", &["squares(100)", "--limit", "6"]);
    assert_eq!(code, Some(0), "{err}");
    assert_eq!(out, "[1, 4, 9, …\n");
    assert!(err.contains("cut at 6 encoded numbers"), "{err}");
}

#[test]
fn a_term_eval_cannot_read_or_elaborate_is_refused_with_its_reason() {
    // A function is not a value `eval` reads: refused by its type.
    let (code, out, err) = eval("function", &["squares"]);
    assert_eq!((code, out.as_str()), (Some(1), ""), "{err}");
    assert!(err.contains("reads a `Nat`, `Bool`, `Char`, `String`, and a `List` or `Option` of those; the term is a `Nat"), "{err}");
    // An unbound name, located in the term as written.
    let (code, _, err) = eval("unbound", &["cubes(3)"]);
    assert_eq!(code, Some(1), "{err}");
    assert!(err.contains("unbound name `cubes`") && err.contains("<term>:1:1"), "{err}");
}
