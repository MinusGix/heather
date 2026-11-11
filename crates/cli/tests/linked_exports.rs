//! `crates/linked/generated/exports.rs` is what its generator writes.
//!
//! The file is the linked crate's one `unsafe` module: the `global_asm!` of
//! every export, a `safe fn` for each function of words, and for each
//! function that reads a span a safe wrapper over `&[u8]` whose `SAFETY`
//! comment is the certificate's premises
//! (docs/native-library-exports-design.md §6). It is written by
//! `heather_cli::linked::exports_rs` from `EXPORTS.tsv` and the signature
//! each assembly file states, which `compile-x86` writes from the values
//! its certificate is stated with. This holds the file on disk to that, so
//! a hand edit to a declaration or a `SAFETY` comment fails here; that the
//! assembly is the compiler's is `native_linked.rs`. No compiler runs, so
//! this is in every lane. A difference is fixed by `scripts/linked`.
#[test]
fn the_declarations_are_generated() {
    let generated = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../linked/generated");
    let read = |name: &str| std::fs::read_to_string(generated.join(name)).map_err(|e| format!("crates/linked/generated/{name}: {e}"));
    let manifest = read("EXPORTS.tsv").unwrap();
    let text = heather_cli::linked::exports_rs(&manifest, &|function| read(&format!("{function}.s"))).unwrap_or_else(|why| panic!("{why}"));
    assert!(read("exports.rs").unwrap() == text,
        "crates/linked/generated/exports.rs is not what `heather linked-exports` writes: run scripts/linked\nexpected:\n{text}");
}

// The table's parameters are held to the code's own signature: a row that
// names a span where the checked-in code takes a word is refused, on the
// real files.
#[test]
fn a_row_the_code_does_not_take_is_refused() {
    let generated = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../linked/generated");
    let read = |name: &str| std::fs::read_to_string(generated.join(name)).map_err(|e| format!("crates/linked/generated/{name}: {e}"));
    let rows = heather_cli::linked::exports(&read("EXPORTS.tsv").unwrap()).unwrap();
    let spans: Vec<_> = rows.iter().filter(|row| row.parameters.iter().any(|(_, kind)| *kind == heather_cli::linked::Kind::Span)).collect();
    assert!(!spans.is_empty(), "no export reads a span");
    for row in spans {
        // The span declared as two words, as a hand-written declaration of
        // the same arity would have it.
        let words: Vec<String> = row.parameters.iter().flat_map(|(name, kind)| match kind {
            heather_cli::linked::Kind::Span => vec![name.clone(), format!("{name}_length")],
            heather_cli::linked::Kind::Word => vec![name.clone()],
        }).collect();
        let manifest = format!("{}\t{}\t{}\n", row.module, row.function, words.join(", "));
        let refused = heather_cli::linked::exports_rs(&manifest, &|function| read(&format!("{function}.s"))).unwrap_err();
        assert!(refused.contains("its compiled code takes"), "{refused}");
    }
}
