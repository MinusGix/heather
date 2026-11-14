//! The assembly `crates/linked` links is what the compiler emits today.
//!
//! `crates/linked/generated/*.s` is checked in, so that building the
//! workspace needs no Heather compiler (docs/native-lexer-crypto-roadmap.md
//! §2, piece 7). A checked-in copy can go stale without anyone noticing: the
//! source module changes, or the lowering does, and the linked bytes are
//! then certified by nothing. This is the gate on that: every export in
//! `generated/EXPORTS.tsv` is compiled again, certificate checked, and its
//! assembly compared byte for byte; an export that is a function of another
//! export's program is compiled with it, as an entry of the one file. A difference is fixed by
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
    for row in &listed {
        assert!(root.join(&row.module).is_file(), "EXPORTS.tsv names `{}`, which is not a file", row.module);
    }
    // A program for each row that has a file, its other exported functions
    // with it.
    // A row is compiled under its symbol, the label and the file's stem.
    let rows: Vec<(&str, &str, &str, Vec<String>)> = listed.iter().filter(|row| row.within.is_none()).map(|row| (row.module.as_str(), row.function.as_str(),
        row.symbol.as_str(), listed.iter().filter(|entry| entry.within.as_deref() == Some(row.symbol.as_str())).map(|entry| entry.entry()).collect())).collect();
    // One compiler per export, four at a time as the library gate runs its
    // folders (`library.rs`): an export costs a certificate, and the
    // scanner alone is two dozen of them.
    let queue = std::sync::Mutex::new(std::collections::VecDeque::from(rows.clone()));
    let failures = std::sync::Mutex::new(Vec::new());
    std::thread::scope(|scope| {
        for _ in 0..4 {
            scope.spawn(|| loop {
                let Some((module, function, symbol, entries)) = queue.lock().expect("queue").pop_front() else { break };
                let assembly = output.join(format!("{symbol}.s"));
                let result = Command::new(env!("CARGO_BIN_EXE_heather"))
                    .current_dir(&root)
                    .args(["compile-x86", module, function, "--symbol", symbol, "-o"]).arg(&assembly)
                    .args(entries.iter().flat_map(|entry| ["--entry", entry.as_str()]))
                    .arg("--cache-dir").arg(heather_cli::showcase::native_test_images())
                    .output().unwrap();
                if !result.status.success() {
                    failures.lock().expect("failures").push(format!("compile-x86 {module} {function}:\n{}", String::from_utf8_lossy(&result.stderr)));
                    continue;
                }
                let emitted = std::fs::read_to_string(&assembly).unwrap();
                match std::fs::read_to_string(generated.join(format!("{symbol}.s"))) {
                    Err(_) => failures.lock().expect("failures").push(format!("crates/linked/generated/{symbol}.s is missing: run scripts/linked")),
                    Ok(linked) if emitted != linked => failures.lock().expect("failures").push(format!(
                        "crates/linked/generated/{symbol}.s is not what `compile-x86 {module} {function} --symbol {symbol}` emits: run scripts/linked\n\
                         emitted:\n{emitted}\nlinked:\n{linked}")),
                    Ok(_) => {}
                }
            });
        }
    });
    let failures = failures.into_inner().expect("failures");
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
    let exports: Vec<String> = rows.iter().map(|(_, _, symbol, _)| format!("{symbol}.s")).collect();
    assert!(!exports.is_empty(), "EXPORTS.tsv lists no export");
    // And nothing is linked that the manifest does not account for (the
    // two tables and the Rust generated from them, and `kinds.rs` from the
    // token kinds' table, are held by `linked_exports.rs`).
    for entry in std::fs::read_dir(&generated).unwrap() {
        let name = entry.unwrap().file_name().into_string().unwrap();
        assert!(["EXPORTS.tsv", "exports.rs", "CONSTANTS.tsv", "constants.rs", "kinds.rs"].contains(&name.as_str()) || exports.contains(&name),
            "crates/linked/generated/{name} is in no row of EXPORTS.tsv");
    }
    std::fs::remove_dir_all(output).unwrap();
}

// What the contract does not take is refused by name, and nothing is
// written (docs/native-library-exports-design.md §6, clauses 1 and 4): a
// ninth word (issues/function-call-past-six-words.md), whether the words
// are the function's own or a span's address and length among them, for a function that reads its span and for
// one that stores into it, and an entry of a program that is not one
// `compile-x86` exports yet.
#[test]
fn what_the_contract_does_not_take_is_refused() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let dir = root.join(format!("target/native-linked-refusals-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let source = "import logic;\nimport bool;\nimport nat;\nimport list;\nimport option;\nimport pair;\nimport char;\n\
        import string;\nimport tactic;\nimport bitvec;\nimport bitvec_nat;\nimport rt;\nimport rt_lower;\n\
        import rt_loop;\nimport rt_file;\nimport rt_file_lower;\nimport rt_file_loop;\n\
        import function_ir;\nimport function_ir_eval;\nimport function_ir_state;\nimport function_ir_writes;\n\
        import function_ir_run;\nimport function_ir_link;\nimport function_ir_placeless;\nimport runtime;\nimport runtime_file;\n\
        runtime fn nine(a, b, c, d, e, f, g, h, i: BitVec(64)) → BitVec(64) { a.add(i) }\n\
        runtime fn wide_span(span: List<BitVec(8)>, length, a, b, c, d, e, f, g: BitVec(64)) → BitVec(64) {\n\
            span.byte_within(length, a).zero_extend(56).add(g)\n}\n\
        runtime fn wide_store(span: List<BitVec(8)>, length, a, b, c, d, e, f, g: BitVec(64)) → Mutated<List<BitVec(8)>, BitVec(64)> {\n\
            Mutated(span.with_byte_within(length, a, b.truncate(8, 56)), g)\n}\n";
    std::fs::write(dir.join("wide.hthr"), source).unwrap();
    let wide = dir.join("wide.hthr");
    for (module, function, why) in [
        (&wide, "nine", "takes 9 words: compile-x86 passes at most eight, six in registers and two on the stack"),
        (&wide, "wide_span", "takes 9 words, an address and a length for each span among them"),
        (&wide, "wide_store", "takes 9 words, an address and a length for each span among them"),
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
    // An entry is another function of the program compiled, found by its
    // name; for now a function of words, in a program that stores into no
    // span (§6.3). Anything else is refused by name, and nothing is written.
    let spans = root.join("lib/native/native_tool_spans.hthr");
    for (function, entry, why) in [
        ("count_newlines", "native_tool_spans::newlines_from", "`native_tool_spans::newlines_from` is lent 1 span: compile-x86 exports another function of a program only where it is a function of words"),
        ("count_newlines", "native_tool_spans::raise_word", "`native_tool_spans::raise_word` is no function of `native_tool_spans::count_newlines`'s program, which has: newlines_from, count_newlines"),
        ("count_newlines", "native_tool_spans::count_newlines", "--entry `native_tool_spans::count_newlines` is the function compiled"),
        ("count_newlines", "nowhere::step", "--entry `nowhere::step` is no function `count_newlines`'s module reaches"),
        ("count_newlines", "newlines_from", "--entry `newlines_from` is not `<module>::<function>`"),
        ("raise_span", "native_tool_spans::raise_word", "stores into its span: compile-x86 exports another function of a program only where the program stores into no span"),
    ] {
        let output = dir.join(format!("{function}.s"));
        let result = Command::new(env!("CARGO_BIN_EXE_heather")).current_dir(&root)
            .arg("compile-x86").arg(&spans).args([function, "--entry", entry, "-o"]).arg(&output)
            .arg("--cache-dir").arg(heather_cli::showcase::native_test_images()).args(["--kernel-workers", "1"])
            .output().unwrap();
        let stderr = String::from_utf8_lossy(&result.stderr);
        assert!(!result.status.success() && stderr.contains(why), "{function} --entry {entry}: {stderr}");
        assert!(!output.exists(), "{function} --entry {entry}: a refused entry wrote assembly");
    }
    // A function is a name or a method's path, and a symbol given for it an
    // identifier; neither is read further than that.
    for (args, why) in [
        (&["List::9f"][..], "function must be a name or a method's path (`Type::method`)"),
        (&["List::raise_letters", "--symbol", "9raise"], "--symbol `9raise` is not an ASCII C/assembly identifier"),
        (&["raise::"], "function must be a name or a method's path"),
    ] {
        let output = dir.join("named.s");
        let result = Command::new(env!("CARGO_BIN_EXE_heather")).current_dir(&root)
            .arg("compile-x86").arg(&spans).args(args).arg("-o").arg(&output)
            .output().unwrap();
        let stderr = String::from_utf8_lossy(&result.stderr);
        assert!(!result.status.success() && stderr.contains(why), "{args:?}: {stderr}");
        assert!(!output.exists(), "{args:?}: a refused name wrote assembly");
    }
    std::fs::remove_dir_all(dir).unwrap();
}
