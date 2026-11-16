//! A program's own optimizer rule changes its compiled code
//! (`examples/x86-native/own_rule.hthr`, docs/native/optimizer-rules-design.md
//! §6): a `rule theorem` declared in the program's module is registered by
//! its prefix, the search applies it where its statement fits, and the
//! certificate's replay is over the library's rules and the program's.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
use std::path::Path;
use std::process::Command;

/// The certified bytes of a compiled function, read back from its assembly.
fn bytes(assembly: &Path) -> Vec<u8> {
    let text = std::fs::read_to_string(assembly).unwrap();
    text.lines()
        .filter_map(|line| line.trim().strip_prefix(".byte"))
        .flat_map(|list| list.split(',').map(|b| u8::from_str_radix(b.trim().trim_start_matches("0x"), 16).unwrap()).collect::<Vec<_>>())
        .collect()
}

/// The code, and what the flag `explain` (`--explain-optimizer`, or with
/// `=all`) printed.
fn compile(root: &Path, source: &Path, function: &str, assembly: &Path, explain: &str) -> (Vec<u8>, String) {
    let result = Command::new(env!("CARGO_BIN_EXE_heather")).current_dir(root)
        .args(["compile-x86"]).arg(source).args([function, "-o"]).arg(assembly).arg(explain)
        .arg("--cache-dir").arg(heather_cli::showcase::native_test_images()).args(["--kernel-workers", "1"])
        .output().unwrap();
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    (bytes(assembly), String::from_utf8(result.stdout).unwrap())
}

/// `OR r64, r64` (REX.W 09 /r), which is what `x | 0` lowers to where
/// nothing says it is `x`.
fn has_or(bytes: &[u8]) -> bool { bytes.windows(2).any(|w| w == [0x48, 0x09]) }

#[test]
fn a_programs_own_rule_is_applied() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let dir = root.join(format!("target/native-own-rule-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let source = root.join("examples/x86-native/own_rule.hthr");
    let (with_rule, explained) = compile(&root, &source, "first_or_zero", &dir.join("with.s"), "--explain-optimizer");
    assert!(!has_or(&with_rule), "the program's rule `or_zero` was not applied: {with_rule:02x?}");
    // The report says so in the rule's words, by its name, beside the
    // library's rules the replay used.
    assert!(explained.lines().any(|line| line.contains(" | 0 = ") && line.ends_with("   by or_zero")), "{explained}");
    assert!(explained.contains("   by narrow_back   ("), "{explained}");
    assert!(!explained.contains("not applied"), "{explained}");
    // The certificate's stages are over the registered rules, the
    // program's among them.
    let certificate = std::fs::read_to_string(dir.join("with.certificate.hthr")).unwrap();
    assert!(certificate.contains("registered(RuleEntry)"), "the certificate names the registered rules");

    // The control: the same program without its rule keeps the `or`.
    let text = std::fs::read_to_string(&source).unwrap();
    let from = text.find("rule theorem or_zero").expect("the rule");
    let to = text.find("// The first byte of a span").expect("the function");
    let plain = dir.join("own_rule.hthr");
    std::fs::write(&plain, format!("{}{}", &text[..from], &text[to..])).unwrap();
    let (without_rule, plain_explained) = compile(&root, &plain, "first_or_zero", &dir.join("without.s"), "--explain-optimizer=all");
    assert!(!plain_explained.contains("by or_zero"), "{plain_explained}");
    // With `=all` the report also names the rules whose nodes fit a node
    // and that were not applied there: the test of the length against
    // zero is one no range decides.
    assert!(plain_explained.lines().any(|line| line.starts_with("  not applied at ") && line.ends_with(": below_yes, below_no")), "{plain_explained}");
    assert!(has_or(&without_rule), "without the rule the `or` stays: {without_rule:02x?}");
    assert!(with_rule.len() < without_rule.len());
    std::fs::remove_dir_all(dir).unwrap();
}

/// A program's own learner (`examples/x86-native/own_learner.hthr`,
/// docs/native/optimizer-rules-design.md §7): the rule `mask_low` has a
/// number its statement's nodes do not give, so the search uses it only
/// where the program's registered learner proposes it.
#[test]
fn a_programs_own_learner_is_asked() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let dir = root.join(format!("target/native-own-learner-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let source = root.join("examples/x86-native/own_learner.hthr");
    let (with_learner, explained) = compile(&root, &source, "first_masked", &dir.join("with.s"), "--explain-optimizer");
    assert!(explained.lines().any(|line| line.contains(" & 255 = ") && line.contains("   by mask_low   (")), "{explained}");

    // The control: the rule alone, with no learner, is not applied, and
    // the code keeps its `and`.
    let text = std::fs::read_to_string(&source).unwrap();
    let from = text.find("// At an `and` of a word").expect("the learner");
    let to = text.find("// The first byte of a span").expect("the function");
    let plain = dir.join("own_learner.hthr");
    std::fs::write(&plain, format!("{}{}", &text[..from], &text[to..])).unwrap();
    let (without_learner, plain_explained) = compile(&root, &plain, "first_masked", &dir.join("without.s"), "--explain-optimizer");
    assert!(!plain_explained.contains("by mask_low"), "{plain_explained}");
    assert!(with_learner.len() < without_learner.len(), "{with_learner:02x?} {without_learner:02x?}");
    std::fs::remove_dir_all(dir).unwrap();
}
