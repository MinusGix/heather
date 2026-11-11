//! The assembly `crates/linked` links is what the compiler emits today.
//!
//! `crates/linked/generated/*.s` is checked in, so that building the
//! workspace needs no Heather compiler (docs/native-lexer-crypto-roadmap.md
//! §2, piece 7). A checked-in copy can go stale without anyone noticing: the
//! source module changes, or the lowering does, and the linked bytes are
//! then certified by nothing. This is the gate on that: every export in
//! `generated/EXPORTS.tsv` is compiled again, certificate checked, and its
//! assembly compared byte for byte. A difference is fixed by
//! `scripts/linked`, which writes the files this test reads, and never by
//! editing them.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
use std::process::Command;

#[test]
fn linked_exports_are_what_the_compiler_emits() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let generated = root.join("crates/linked/generated");
    let manifest = std::fs::read_to_string(generated.join("EXPORTS.tsv")).unwrap();
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let output = root.join(format!("target/native-linked-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&output).unwrap();
    let listed = heather_cli::linked::exports(&manifest).unwrap_or_else(|why| panic!("{why}"));
    let rows: Vec<(&str, &str)> = listed.iter().map(|row| (row.module.as_str(), row.function.as_str())).collect();
    for (module, _) in &rows {
        assert!(root.join(module).is_file(), "EXPORTS.tsv names `{module}`, which is not a file");
    }
    // One compiler per export, four at a time as the library gate runs its
    // folders (`library.rs`): an export costs a certificate, and the
    // scanner alone is two dozen of them.
    let queue = std::sync::Mutex::new(std::collections::VecDeque::from(rows.clone()));
    let failures = std::sync::Mutex::new(Vec::new());
    std::thread::scope(|scope| {
        for _ in 0..4 {
            scope.spawn(|| loop {
                let Some((module, function)) = queue.lock().expect("queue").pop_front() else { break };
                let assembly = output.join(format!("{function}.s"));
                let result = Command::new(env!("CARGO_BIN_EXE_heather"))
                    .current_dir(&root)
                    .args(["compile-x86", module, function, "-o"]).arg(&assembly)
                    .arg("--cache-dir").arg(heather_cli::showcase::native_test_images())
                    .output().unwrap();
                if !result.status.success() {
                    failures.lock().expect("failures").push(format!("compile-x86 {module} {function}:\n{}", String::from_utf8_lossy(&result.stderr)));
                    continue;
                }
                let emitted = std::fs::read_to_string(&assembly).unwrap();
                match std::fs::read_to_string(generated.join(format!("{function}.s"))) {
                    Err(_) => failures.lock().expect("failures").push(format!("crates/linked/generated/{function}.s is missing: run scripts/linked")),
                    Ok(linked) if emitted != linked => failures.lock().expect("failures").push(format!(
                        "crates/linked/generated/{function}.s is not what `compile-x86 {module} {function}` emits: run scripts/linked\n\
                         emitted:\n{emitted}\nlinked:\n{linked}")),
                    Ok(_) => {}
                }
            });
        }
    });
    let failures = failures.into_inner().expect("failures");
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
    let exports: Vec<String> = rows.iter().map(|(_, function)| format!("{function}.s")).collect();
    assert!(!exports.is_empty(), "EXPORTS.tsv lists no export");
    // And nothing is linked that the manifest does not account for.
    for entry in std::fs::read_dir(&generated).unwrap() {
        let name = entry.unwrap().file_name().into_string().unwrap();
        assert!(name == "EXPORTS.tsv" || name == "exports.rs" || exports.contains(&name),
            "crates/linked/generated/{name} is in no row of EXPORTS.tsv");
    }
    std::fs::remove_dir_all(output).unwrap();
}

// What the contract does not take is refused by name, and nothing is
// written (docs/native-library-exports-design.md §6, clauses 1 and 4): a
// seventh word, whether the words are the function's own or a span's
// address and length among them; and a function that stores into its span,
// whose contract has a clause more than a reader's (what the span holds
// after) and is the write half's to export.
#[test]
fn what_the_contract_does_not_take_is_refused() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let dir = root.join(format!("target/native-linked-refusals-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let source = "import logic;\nimport bool;\nimport nat;\nimport list;\nimport option;\nimport pair;\nimport char;\n\
        import string;\nimport tactic;\nimport bitvec;\nimport bitvec_nat;\nimport rt;\nimport rt_lower;\n\
        import function_ir;\nimport function_ir_eval;\nimport runtime;\n\
        runtime fn seven(a, b, c, d, e, f, g: BitVec(64)) → BitVec(64) { a.add(g) }\n\
        runtime fn wide_span(span: List<BitVec(8)>, length, a, b, c, d, e: BitVec(64)) → BitVec(64) {\n\
            span.byte_within(length, a).zero_extend(56).add(e)\n}\n";
    std::fs::write(dir.join("wide.hthr"), source).unwrap();
    let wide = dir.join("wide.hthr");
    let spans = root.join("lib/native/native_tool_spans.hthr");
    for (module, function, why) in [
        (&wide, "seven", "takes 7 words: compile-x86 passes at most six"),
        (&wide, "wide_span", "takes 7 words, an address and a length for each span among them"),
        (&spans, "raise_span", "`raise_span` stores into its span"),
    ] {
        let output = dir.join(format!("{function}.s"));
        let result = Command::new(env!("CARGO_BIN_EXE_heather")).current_dir(&root)
            .arg("compile-x86").arg(module).args([function, "-o"]).arg(&output)
            .arg("--cache-dir").arg(heather_cli::showcase::native_test_images()).args(["--kernel-workers", "1"])
            .output().unwrap();
        let stderr = String::from_utf8_lossy(&result.stderr);
        assert!(!result.status.success() && stderr.contains(why), "{function}: {stderr}");
        assert!(!output.exists(), "{function}: a refused function wrote assembly");
    }
    std::fs::remove_dir_all(dir).unwrap();
}
