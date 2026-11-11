//! The Rust side of an export `crates/linked` links: its declaration,
//! generated (docs/native-library-exports-design.md §6).
//!
//! `compile-x86` states what its code takes in the assembly it writes
//! ([`header`]: which arguments are words and which are spans, and the stack
//! the certificate asks for), from the same values its certificate's
//! `_returns` theorem is stated with. `crates/linked/generated/EXPORTS.tsv`
//! names each export's parameters. [`exports_rs`] writes
//! `generated/exports.rs` from the two: the `global_asm!` of every file, a
//! `safe fn` for a function of words, and for a function that reads a span
//! an `unsafe` declaration over a pointer and a length with a safe wrapper
//! over `&[u8]`, its `SAFETY` comment the theorem's premises in order. The
//! crate's one `unsafe` module is that file, written here in full: nothing
//! in it is a hand's (`crates/cli/tests/linked_exports.rs` holds the file to
//! this function, and `tests/native_linked.rs` the assembly to the
//! compiler).
//!
//! A parameter list that disagrees with the code's own signature (a span
//! where the code takes a word, a parameter too few) is refused here, so a
//! declaration cannot pass a pointer where the certificate says a count.

/// What an argument is to the compiled code.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Kind {
    /// A 64-bit word, in one register.
    Word,
    /// A span of bytes the code reads: two words, its address then its
    /// length.
    Span,
}

impl Kind {
    fn name(self) -> &'static str {
        match self { Kind::Word => "word", Kind::Span => "span" }
    }
}

/// What a compiled function takes and needs, as its certificate states it.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Signature {
    pub kinds: Vec<Kind>,
    /// Bytes of stack below the return address the `_returns` theorem asks
    /// for.
    pub stack: u64,
}

/// The lines of an assembly file that state `signature`, as `compile-x86`
/// writes them and [`Signature::read`] reads them.
pub fn header(symbol: &str, signature: &Signature) -> String {
    let kinds: Vec<&str> = signature.kinds.iter().map(|kind| kind.name()).collect();
    format!("# signature: {symbol}({}) -> word\n# stack: {} bytes below the return address\n", kinds.join(", "), signature.stack)
}

impl Signature {
    /// The signature `assembly` states for `symbol`.
    pub fn read(assembly: &str, symbol: &str) -> Result<Signature, String> {
        let missing = |what: &str| format!("{symbol}.s states no {what}: it is not what this compiler writes (run scripts/linked)");
        let line = assembly.lines().find_map(|line| line.strip_prefix("# signature: ")).ok_or_else(|| missing("signature"))?;
        let kinds = line.strip_prefix(symbol).and_then(|rest| rest.strip_prefix('('))
            .and_then(|rest| rest.strip_suffix(") -> word")).ok_or_else(|| missing("signature of its own"))?;
        let kinds = kinds.split(',').map(str::trim).filter(|kind| !kind.is_empty()).map(|kind| match kind {
            "word" => Ok(Kind::Word),
            "span" => Ok(Kind::Span),
            other => Err(format!("{symbol}.s: `{other}` is no kind of argument")),
        }).collect::<Result<Vec<_>, _>>()?;
        let stack = assembly.lines().find_map(|line| line.strip_prefix("# stack: "))
            .and_then(|rest| rest.split(' ').next()).and_then(|bytes| bytes.parse().ok()).ok_or_else(|| missing("stack"))?;
        Ok(Signature { kinds, stack })
    }
}

/// A row of `EXPORTS.tsv`: the source module, the `runtime fn` in it, and
/// its parameters as the Rust declaration names them.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Export {
    pub module: String,
    pub function: String,
    pub parameters: Vec<(String, Kind)>,
}

/// The table's rows. A row is `<module>\t<function>\t<parameters>`, the
/// parameters separated by commas, each a name, a span's followed by
/// `: span`.
pub fn exports(manifest: &str) -> Result<Vec<Export>, String> {
    let mut rows = Vec::new();
    for line in manifest.lines().filter(|line| !line.starts_with('#') && !line.trim().is_empty()) {
        let bad = || format!("EXPORTS.tsv: `{line}` is not `<module>\\t<function>\\t<parameters>`");
        let mut columns = line.split('\t');
        let (Some(module), Some(function), Some(parameters), None) = (columns.next(), columns.next(), columns.next(), columns.next()) else {
            return Err(bad());
        };
        let identifier = |name: &str| !name.is_empty() && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
            && !name.starts_with(|c: char| c.is_ascii_digit());
        if !identifier(function) { return Err(bad()); }
        let mut named = Vec::new();
        for parameter in parameters.split(',').map(str::trim).filter(|parameter| !parameter.is_empty()) {
            let (name, kind) = match parameter.split_once(':') {
                None => (parameter, Kind::Word),
                Some((name, kind)) if kind.trim() == "span" => (name.trim(), Kind::Span),
                Some((_, kind)) => return Err(format!("EXPORTS.tsv: `{function}`: `{}` is no kind of parameter (a word is a bare name, a span `name: span`)", kind.trim())),
            };
            if !identifier(name) || named.iter().any(|(earlier, _)| earlier == name) {
                return Err(format!("EXPORTS.tsv: `{function}`: `{name}` is not a parameter's name, or is one twice"));
            }
            named.push((name.to_string(), kind));
        }
        if rows.iter().any(|row: &Export| row.function == function) { return Err(format!("EXPORTS.tsv lists `{function}` twice")); }
        rows.push(Export { module: module.to_string(), function: function.to_string(), parameters: named });
    }
    Ok(rows)
}

/// `generated/exports.rs`: every export of `manifest` linked and declared,
/// against the signature its assembly file (`assembly(function)`) states.
pub fn exports_rs(manifest: &str, assembly: &dyn Fn(&str) -> Result<String, String>) -> Result<String, String> {
    let rows = exports(manifest)?;
    let mut links = String::new();
    let mut words = String::new();
    let mut raw = String::new();
    let mut wrappers = String::new();
    for row in &rows {
        let function = &row.function;
        let signature = Signature::read(&assembly(function)?, function)?;
        let named: Vec<Kind> = row.parameters.iter().map(|(_, kind)| *kind).collect();
        if named != signature.kinds {
            let list = |kinds: &[Kind]| kinds.iter().map(|kind| kind.name()).collect::<Vec<_>>().join(", ");
            return Err(format!("EXPORTS.tsv declares `{function}({})`, and its compiled code takes `({})`", list(&named), list(&signature.kinds)));
        }
        links.push_str(&format!("linked!(\"{function}.s\");\n"));
        let doc = format!("/// `{function}` of `{}`. STACK: {} bytes.", row.module, signature.stack);
        if named.iter().all(|kind| *kind == Kind::Word) {
            let parameters: Vec<String> = row.parameters.iter().map(|(name, _)| format!("{name}: u64")).collect();
            words.push_str(&format!("    {doc}\n    pub safe fn {function}({}) -> u64;\n", parameters.join(", ")));
            continue;
        }
        let mut declared = Vec::new();
        let mut taken = Vec::new();
        let mut passed = Vec::new();
        let mut spans = Vec::new();
        for (name, kind) in &row.parameters {
            match kind {
                Kind::Word => {
                    declared.push(format!("{name}: u64"));
                    taken.push(format!("{name}: u64"));
                    passed.push(name.clone());
                }
                Kind::Span => {
                    declared.push(format!("{name}: *const u8"));
                    declared.push(format!("{name}_length: u64"));
                    taken.push(format!("{name}: &[u8]"));
                    passed.push(format!("{name}.as_ptr()"));
                    passed.push(format!("{name}.len() as u64"));
                    spans.push(format!("`{name}`"));
                }
            }
        }
        raw.push_str(&format!("        pub unsafe fn {function}({}) -> u64;\n", declared.join(", ")));
        let span = if spans.len() == 1 { format!("the span {}", spans[0]) } else { format!("the spans {}", spans.join(", ")) };
        wrappers.push_str(&format!("
{doc}
pub fn {function}({taken}) -> u64 {{
    // SAFETY (the premises of `{function}_native_returns`, in order):
    // - the arguments are in their registers (`ArgsIn`): the declaration's
    //   order is the table's, which the gate holds to the code's signature.
    // - each span's two words are its address and its length (`ArgsLent`):
    //   `as_ptr()` and `len()`, for {span}.
    // - the bytes are readable there for the whole call (`Stack::InMemory`):
    //   a `&[u8]` is live, initialised memory while it is borrowed, and an
    //   empty one is read nowhere.
    // - no word the callee stores below this call's return address changes
    //   them, and they end below 2^47 (`Loan::under`, `Loan::canonical`):
    //   borrowed memory is never the unused stack below RSP, and Linux maps
    //   nothing of a process above 2^47 unless it asks for that by a hint.
    // The stack's room is the platform's to give, as for a function of
    // words (the crate's comment).
    unsafe {{ raw::{function}({passed}) }}
}}
", taken = taken.join(", "), passed = passed.join(", ")));
    }
    let mut text = String::from("// Generated by `scripts/linked` from `EXPORTS.tsv` and the signature each
// assembly file states. Not edited: `crates/cli/tests/linked_exports.rs`
// holds this file to its generator (`heather_cli::linked::exports_rs`).
//
// The one module the crate's `unsafe_code = \"deny\"` is lifted for: linking
// the compiler's bytes (`global_asm!`) and naming the functions in them.

// Each file is the compiler's output, verbatim (`options(raw)`: the text is
// assembly, not a format string). It selects `.text` itself and ends in a
// `.note.GNU-stack` section, so it is bracketed to leave the assembler
// where it was.
macro_rules! linked {
    ($file:literal) => {
        core::arch::global_asm!(
            \".pushsection .text\",
            include_str!($file),
            \".popsection\",
            options(raw)
        );
    };
}
");
    text.push_str(&links);
    if !words.is_empty() {
        text.push_str(&format!("
// Functions of words, declared `safe` on the strength of their certificates
// (the crate's comment): nothing a caller passes can make the call
// misbehave, and the unproved part is the platform's, not the callee's.
unsafe extern \"sysv64\" {{
{words}}}
"));
    }
    if !raw.is_empty() {
        text.push_str(&format!("
// Functions that read a span, as the code takes them: each span its address
// and its length. `unsafe`, because the certificate holds only where the
// two words are a span of readable bytes; the wrappers below are where
// that is so.
mod raw {{
    unsafe extern \"sysv64\" {{
{raw}    }}
}}
{wrappers}"));
    }
    Ok(text)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn stated(symbol: &str, kinds: &[Kind], stack: u64) -> String {
        format!("# a first line\n{}.text\n", header(symbol, &Signature { kinds: kinds.to_vec(), stack }))
    }

    #[test]
    fn a_header_reads_back() {
        for kinds in [&[][..], &[Kind::Word], &[Kind::Span, Kind::Word], &[Kind::Word, Kind::Span, Kind::Span]] {
            let signature = Signature { kinds: kinds.to_vec(), stack: 216 };
            assert_eq!(Signature::read(&stated("f", kinds, 216), "f"), Ok(signature));
        }
        // Another function's file, or one from before the header, is refused.
        assert!(Signature::read(&stated("g", &[Kind::Word], 72), "f").is_err());
        assert!(Signature::read("# Heather certified program\n.text\n", "f").is_err());
    }

    #[test]
    fn a_declaration_follows_the_code() {
        let manifest = "# comment\nm.hthr\tf\ta, b\nm.hthr\tg\ttext: span, count\n";
        let assembly = |function: &str| Ok(match function {
            "f" => stated("f", &[Kind::Word, Kind::Word], 72),
            _ => stated("g", &[Kind::Span, Kind::Word], 144),
        });
        let text = exports_rs(manifest, &assembly).unwrap();
        assert!(text.contains("    /// `f` of `m.hthr`. STACK: 72 bytes.\n    pub safe fn f(a: u64, b: u64) -> u64;\n"), "{text}");
        assert!(text.contains("        pub unsafe fn g(text: *const u8, text_length: u64, count: u64) -> u64;\n"), "{text}");
        assert!(text.contains("pub fn g(text: &[u8], count: u64) -> u64 {"), "{text}");
        assert!(text.contains("unsafe { raw::g(text.as_ptr(), text.len() as u64, count) }"), "{text}");
    }

    // The table cannot declare what the code does not take: a span's parts
    // swapped with a word, a word passed as a span, a parameter too few.
    #[test]
    fn a_declaration_the_code_does_not_take_is_refused() {
        let assembly = |_: &str| Ok(stated("g", &[Kind::Span, Kind::Word], 144));
        for parameters in ["count, text: span", "text, count", "text: span", "text: span, count, more", "text: span, count: span"] {
            let refused = exports_rs(&format!("m.hthr\tg\t{parameters}\n"), &assembly).unwrap_err();
            assert!(refused.contains("its compiled code takes `(span, word)`"), "{parameters}: {refused}");
        }
        for (row, why) in [("m.hthr\tg\n", "is not `<module>"), ("m.hthr\tg\ttext: bytes\n", "no kind of parameter"),
            ("m.hthr\tg\ta, a\n", "is one twice"), ("m.hthr\tg\ta\nm.hthr\tg\ta\n", "twice")] {
            let refused = exports_rs(row, &assembly).unwrap_err();
            assert!(refused.contains(why), "{row}: {refused}");
        }
    }
}
