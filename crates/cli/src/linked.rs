//! The Rust side of an export `crates/linked` links: its declaration,
//! generated (docs/native-library-exports-design.md §6).
//!
//! `compile-x86` states what its code takes in the assembly it writes
//! ([`header`]: which arguments are words and which are spans, and the stack
//! the certificate asks for), from the same values its certificate's
//! `_returns` theorem is stated with. `crates/linked/generated/EXPORTS.tsv`
//! names each export's parameters. [`exports_rs`] writes
//! `generated/exports.rs` from the two: the `global_asm!` of every file, a
//! `safe fn` for a function of words, and for a function over a span an
//! `unsafe` declaration over a pointer and a length with a safe wrapper
//! over `&[u8]`, or `&mut [u8]` where the code stores into the span, its
//! `SAFETY` comment the theorem's premises in order. The
//! crate's one `unsafe` module is that file, written here in full: nothing
//! in it is a hand's (`crates/cli/tests/linked_exports.rs` holds the file to
//! this function, and `tests/native_linked.rs` the assembly to the
//! compiler).
//!
//! Exports that share callees are one program: a row's fourth column names
//! the export whose program it is a function of, and its code is a second
//! label in that export's file, stated there with a signature of its own
//! (§6.3). Nothing is linked for such a row but the declaration.
//!
//! A row names the function as Heather does, and a method by its path
//! (`List::raise_letters`, `Sha256::update`); its symbol is the label, the
//! file stem and the Rust name. A plain function is its own symbol; a
//! method's is derived ([`symbol_of`]: each segment in snake case, joined by
//! `_`, so `Sha256::update` is `sha256_update`), or written before the path
//! as `<symbol> = <path>`. Two rows with one symbol are refused, naming both.
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
    /// A span of bytes the code may store into as well: the same two words,
    /// under a lending that lets the span be written.
    SpanMut,
}

impl Kind {
    fn name(self) -> &'static str {
        match self { Kind::Word => "word", Kind::Span => "span", Kind::SpanMut => "span mut" }
    }

    fn named(name: &str) -> Option<Kind> {
        [Kind::Word, Kind::Span, Kind::SpanMut].into_iter().find(|kind| kind.name() == name)
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
/// writes them and [`Signature::read`] reads them: two for each symbol the
/// file exports, the stack's after the signature's.
pub fn header(symbol: &str, signature: &Signature) -> String {
    let kinds: Vec<&str> = signature.kinds.iter().map(|kind| kind.name()).collect();
    format!("# signature: {symbol}({}) -> word\n# stack: {} bytes below the return address\n", kinds.join(", "), signature.stack)
}

impl Signature {
    /// The signature `assembly` states for `symbol`, one of the symbols it
    /// exports.
    pub fn read(assembly: &str, symbol: &str) -> Result<Signature, String> {
        let missing = |what: &str| format!("the assembly read for `{symbol}` states no {what}: it is not what this compiler writes (run scripts/linked)");
        let mut lines = assembly.lines().skip_while(|line| line.strip_prefix("# signature: ")
            .and_then(|rest| rest.strip_prefix(symbol)).is_none_or(|rest| !rest.starts_with('(')));
        let line = lines.next().and_then(|line| line.strip_prefix("# signature: ")).ok_or_else(|| missing("signature of its own"))?;
        let kinds = line.strip_prefix(symbol).and_then(|rest| rest.strip_prefix('('))
            .and_then(|rest| rest.strip_suffix(") -> word")).ok_or_else(|| missing("signature of its own"))?;
        let kinds = kinds.split(',').map(str::trim).filter(|kind| !kind.is_empty())
            .map(|kind| Kind::named(kind).ok_or_else(|| format!("`{symbol}`'s signature: `{kind}` is no kind of argument")))
            .collect::<Result<Vec<_>, _>>()?;
        let stack = lines.next().and_then(|line| line.strip_prefix("# stack: "))
            .and_then(|rest| rest.split(' ').next()).and_then(|bytes| bytes.parse().ok()).ok_or_else(|| missing("stack"))?;
        Ok(Signature { kinds, stack })
    }
}

/// Whether `name` is an ASCII C/assembly identifier: what a symbol, a
/// parameter's name and each segment of a function's path must be.
pub fn identifier(name: &str) -> bool {
    !name.is_empty() && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') && !name.starts_with(|c: char| c.is_ascii_digit())
}

/// The symbol a function is exported under when its row writes none: a
/// plain function's own name, a method's path with each segment in snake
/// case and joined by `_` (`Sha256::update` is `sha256_update`,
/// `List::raise_letters` is `list_raise_letters`, `HashMap::get` is
/// `hash_map_get`). `None` where a segment is not an identifier.
pub fn symbol_of(function: &str) -> Option<String> {
    let segments: Vec<&str> = function.split("::").collect();
    if !segments.iter().all(|segment| identifier(segment)) { return None; }
    let snake = |segment: &str| {
        let chars: Vec<char> = segment.chars().collect();
        let mut out = String::new();
        for (i, &c) in chars.iter().enumerate() {
            // A capital starts a word after a lower-case letter or a digit,
            // and ends a run of capitals where a lower-case letter follows:
            // `HTTPServer` is `http_server`.
            let starts = c.is_ascii_uppercase() && i > 0 && (!chars[i - 1].is_ascii_uppercase() && chars[i - 1] != '_'
                || chars[i - 1].is_ascii_uppercase() && chars.get(i + 1).is_some_and(|next| next.is_ascii_lowercase()));
            if starts { out.push('_'); }
            out.push(c.to_ascii_lowercase());
        }
        out
    };
    Some(segments.iter().map(|segment| snake(segment)).collect::<Vec<_>>().join("_"))
}

/// A row of `EXPORTS.tsv`: the source module, the `runtime fn` in it and
/// the symbol it is exported under, its parameters as the Rust declaration
/// names them, and for a function exported from another export's program,
/// that export (by its symbol).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Export {
    pub module: String,
    /// The function as Heather names it in its module: `f`, or a method's
    /// path, `List::raise_letters`.
    pub function: String,
    /// The label, the file stem and the Rust name.
    pub symbol: String,
    pub parameters: Vec<(String, Kind)>,
    /// The export whose program this function is an entry of: its code is a
    /// label in that export's assembly file, and it has no file of its own.
    pub within: Option<String>,
}

impl Export {
    /// The export whose assembly file holds this one's code: itself, or the
    /// one it is an entry of.
    pub fn file(&self) -> &str { self.within.as_deref().unwrap_or(&self.symbol) }

    /// The function as `compile-x86 --entry` names it: its module, which is
    /// its file's stem, and its name.
    pub fn entry(&self) -> String {
        let stem = std::path::Path::new(&self.module).file_stem().and_then(|stem| stem.to_str()).unwrap_or_default();
        format!("{stem}::{}", self.function)
    }
}

/// The table's rows. A row is `<module>\t<function>\t<parameters>`: the
/// function a plain one's name, a method's path, or `<symbol> = <path>`;
/// the parameters separated by commas, each a name, a span's followed by
/// `: span`, or by `: span mut` where the function stores into it (a
/// `mut self` receiver that is a span is one of these); and a fourth column
/// where the function is an entry of another row's program, that row's
/// symbol.
pub fn exports(manifest: &str) -> Result<Vec<Export>, String> {
    let mut rows = Vec::new();
    for line in manifest.lines().filter(|line| !line.starts_with('#') && !line.trim().is_empty()) {
        let bad = || format!("EXPORTS.tsv: `{line}` is not `<module>\\t<function>\\t<parameters>`, with `\\t<export>` after it for an entry of that export's program");
        let mut columns = line.split('\t');
        let (Some(module), Some(function), Some(parameters), within, None) = (columns.next(), columns.next(), columns.next(), columns.next(), columns.next()) else {
            return Err(bad());
        };
        // The symbol written before the path, or the one the path derives.
        let (symbol, function) = match function.split_once('=') {
            Some((symbol, path)) => (Some(symbol.trim()).filter(|symbol| identifier(symbol)).map(str::to_string), path.trim()),
            None => (symbol_of(function), function),
        };
        let Some(symbol) = symbol.filter(|_| symbol_of(function).is_some()) else {
            return Err(format!("EXPORTS.tsv: `{line}`: the function is a name or a method's path (`Type::method`), each segment an \
                ASCII identifier, and a symbol written before it as `<symbol> = <path>` is one"));
        };
        if within.is_some_and(|within| !identifier(within)) { return Err(bad()); }
        if within.is_some() && function.contains("::") {
            return Err(format!("EXPORTS.tsv: `{function}` is a method, and an entry of another export's program is a plain function \
                (`compile-x86 --entry`, issues/linked-program-entries-limits.md)"));
        }
        let mut named = Vec::new();
        for parameter in parameters.split(',').map(str::trim).filter(|parameter| !parameter.is_empty()) {
            let (name, kind) = match parameter.split_once(':') {
                None => (parameter, Kind::Word),
                Some((name, kind)) => match Kind::named(kind.trim()).filter(|kind| *kind != Kind::Word) {
                    Some(kind) => (name.trim(), kind),
                    None => return Err(format!("EXPORTS.tsv: `{function}`: `{}` is no kind of parameter (a word is a bare name, a span \
                        `name: span`, one the function stores into `name: span mut`)", kind.trim())),
                },
            };
            if !identifier(name) || named.iter().any(|(earlier, _)| earlier == name) {
                return Err(format!("EXPORTS.tsv: `{function}`: `{name}` is not a parameter's name, or is one twice"));
            }
            named.push((name.to_string(), kind));
        }
        if let Some(other) = rows.iter().find(|row: &&Export| row.symbol == symbol) {
            return Err(if other.function == function && other.module == module { format!("EXPORTS.tsv lists `{function}` twice") } else {
                format!("EXPORTS.tsv: `{function}` of `{module}` and `{}` of `{}` are both exported as `{symbol}`: write another symbol \
                    before one of them, as `<symbol> = {function}`", other.function, other.module)
            });
        }
        rows.push(Export { module: module.to_string(), function: function.to_string(), symbol, parameters: named, within: within.map(str::to_string) });
    }
    // An entry is of a program that has a file: a row with no fourth column.
    for row in &rows {
        let Some(within) = &row.within else { continue };
        match rows.iter().find(|other| other.symbol == *within) {
            None => return Err(format!("EXPORTS.tsv: `{}` is an entry of `{within}`, which is no row's symbol", row.function)),
            Some(other) if other.within.is_some() => return Err(format!("EXPORTS.tsv: `{}` is an entry of `{within}`, which is itself an entry of `{}`: \
                name the export that has the file", row.function, other.file())),
            Some(_) => {}
        }
    }
    Ok(rows)
}

/// `generated/exports.rs`: every export of `manifest` linked and declared,
/// against the signature its assembly file states (`assembly(function)`,
/// the function the one whose program it is: a row's own, or the export it
/// is an entry of).
pub fn exports_rs(manifest: &str, assembly: &dyn Fn(&str) -> Result<String, String>) -> Result<String, String> {
    let rows = exports(manifest)?;
    let mut links = String::new();
    let mut words = String::new();
    let mut raw = String::new();
    let mut wrappers = String::new();
    for row in &rows {
        // The symbol is the label and the Rust name; the doc names the
        // function as Heather does.
        let function = &row.symbol;
        let signature = Signature::read(&assembly(row.file())?, function)?;
        let named: Vec<Kind> = row.parameters.iter().map(|(_, kind)| *kind).collect();
        if named != signature.kinds {
            let list = |kinds: &[Kind]| kinds.iter().map(|kind| kind.name()).collect::<Vec<_>>().join(", ");
            return Err(format!("EXPORTS.tsv declares `{function}({})`, and its compiled code takes `({})`", list(&named), list(&signature.kinds)));
        }
        // An entry's code is in the file of the export it is an entry of.
        if row.within.is_none() { links.push_str(&format!("linked!(\"{function}.s\");\n")); }
        let doc = match &row.within {
            None => format!("/// `{}` of `{}`. STACK: {} bytes.", row.function, row.module, signature.stack),
            Some(within) => format!("/// `{}` of `{}`, a function of `{within}`'s program. STACK: {} bytes.", row.function, row.module, signature.stack),
        };
        if named.iter().all(|kind| *kind == Kind::Word) {
            let parameters: Vec<String> = row.parameters.iter().map(|(name, _)| format!("{name}: u64")).collect();
            words.push_str(&format!("    {doc}\n    pub safe fn {function}({}) -> u64;\n", parameters.join(", ")));
            continue;
        }
        let mut declared = Vec::new();
        let mut taken = Vec::new();
        let mut passed = Vec::new();
        let mut spans = Vec::new();
        let mut written = Vec::new();
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
                Kind::SpanMut => {
                    declared.push(format!("{name}: *mut u8"));
                    declared.push(format!("{name}_length: u64"));
                    taken.push(format!("{name}: &mut [u8]"));
                    passed.push(format!("{name}.as_mut_ptr()"));
                    passed.push(format!("{name}.len() as u64"));
                    spans.push(format!("`{name}`"));
                    written.push(format!("`{name}`"));
                }
            }
        }
        raw.push_str(&format!("        pub unsafe fn {function}({}) -> u64;\n", declared.join(", ")));
        let span = if spans.len() == 1 { format!("the span {}", spans[0]) } else { format!("the spans {}", spans.join(", ")) };
        // What a lending to write asks besides, where the code stores.
        let writing = if written.is_empty() { String::new() } else { format!("
    // - the bytes of {} may be stored into, and a byte stored there reads
    //   back and changes no other byte of a span, no word of the stack and
    //   none of the code (`Loan::writable`, `stored`, `apart`, `keeps`,
    //   `keeps_code`): a `&mut [u8]` is writable memory nothing else
    //   borrows for the whole call, so it shares no byte with another
    //   argument, with the stack below this call or with the program's
    //   code. The code stores into no other span (the lending's marks).", written.join(", ")) };
        wrappers.push_str(&format!("
{doc}
pub fn {function}({taken}) -> u64 {{
    // SAFETY (the premises of `{function}_native_returns`, in order):
    // - the arguments are in their registers (`ArgsIn`): the declaration's
    //   order is the table's, which the gate holds to the code's signature.
    // - each span's two words are its address and its length (`ArgsLent`):
    //   its pointer and `len()`, for {span}.
    // - the bytes are readable there for the whole call (`Stack::InMemory`):
    //   a slice is live, initialised memory while it is borrowed, and an
    //   empty one is read nowhere.
    // - no word the callee stores below this call's return address changes
    //   them, and they end below 2^47 (`Loan::under`, `Loan::canonical`):
    //   borrowed memory is never the unused stack below RSP, and Linux maps
    //   nothing of a process above 2^47 unless it asks for that by a hint.{writing}
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
// Functions over a span, as the code takes them: each span its address and
// its length. `unsafe`, because the certificate holds only where the two
// words are a span of readable bytes, writable where the code stores; the
// wrappers below are where that is so.
mod raw {{
    unsafe extern \"sysv64\" {{
{raw}    }}
}}
{wrappers}"));
    }
    Ok(text)
}

/// `generated/constants.rs`: each row of `CONSTANTS.tsv` (`<module>\t<def>`)
/// a `pub const` whose value is the module's own: the `def` of that name,
/// read from `module(path)`'s source, which must be `def <name>: Nat =
/// <numeral>;`. A value the Rust that reads the linked code's answers must
/// agree on with that code (`TOKEN_END_BITS`, where a token word's kind
/// starts) is then written once, in Heather, and the code uses the `def`;
/// a `def` that is anything but a numeral is refused here, not evaluated.
/// Read as Rust's shift counts are, a `u32`.
pub fn constants_rs(table: &str, module: &dyn Fn(&str) -> Result<String, String>) -> Result<String, String> {
    let mut text = String::from("// Generated by `scripts/linked` from `CONSTANTS.tsv` and the `def` each row
// names. Not edited: `crates/cli/tests/linked_exports.rs` holds this file to
// its generator (`heather_cli::linked::constants_rs`).
");
    let mut named: Vec<&str> = Vec::new();
    for line in table.lines().filter(|line| !line.starts_with('#') && !line.trim().is_empty()) {
        let (Some((path, name)), false) = (line.split_once('\t'), line.matches('\t').count() > 1) else {
            return Err(format!("CONSTANTS.tsv: `{line}` is not `<module>\\t<def>`"));
        };
        if named.contains(&name) { return Err(format!("CONSTANTS.tsv lists `{name}` twice")); }
        named.push(name);
        let source = module(path)?;
        let file = heather_syntax::parse_file(&source).map_err(|e| format!("{path}: does not parse: {e:?}"))?;
        let not_a_numeral = || format!("CONSTANTS.tsv: `{name}` of `{path}` is not `def {name}: Nat = <numeral>;`");
        let decl = file.items.iter().find_map(|item| match item {
            heather_syntax::ast::Item::Decl(decl) if decl.value && decl.name == name => Some(decl),
            _ => None,
        }).ok_or_else(|| format!("CONSTANTS.tsv: `{path}` defines no `def {name}`"))?;
        let value = match (&decl.result.kind, decl.body.stmts.is_empty(), &decl.body.result.kind) {
            (heather_syntax::ast::TyKind::Nat, true, heather_syntax::ast::ExprKind::Num(value)) => value,
            _ => return Err(not_a_numeral()),
        };
        let value = value.as_u64().filter(|value| *value <= u64::from(u32::MAX))
            .ok_or_else(|| format!("CONSTANTS.tsv: `{name}` of `{path}` is past a `u32`"))?;
        text.push_str(&format!("\n/// `{name}` of `{path}`.\npub const {name}: u32 = {value};\n"));
    }
    Ok(text)
}

#[cfg(test)]
mod tests {
    use super::*;

    // A constant is the module's `def`, a numeral, and nothing else is
    // read as one.
    #[test]
    fn a_constant_is_its_definition() {
        let module = |path: &str| match path {
            "m.hthr" => Ok("import nat;\ndef BITS: Nat = 56;\ndef MORE: Nat = 4294967296;\ndef SUM: Nat = 50 + 6;\nfn F() → Nat { 3 }\n".to_string()),
            other => Err(format!("{other} was read")),
        };
        let text = constants_rs("# comment\nm.hthr\tBITS\n", &module).unwrap();
        assert!(text.contains("\n/// `BITS` of `m.hthr`.\npub const BITS: u32 = 56;\n"), "{text}");
        for (row, why) in [("m.hthr\tSUM\n", "is not `def SUM: Nat = <numeral>;`"), ("m.hthr\tF\n", "defines no `def F`"),
            ("m.hthr\tMORE\n", "past a `u32`"), ("m.hthr\tBITS\nm.hthr\tBITS\n", "twice"), ("m.hthr\n", "is not `<module>"),
            ("m.hthr\tBITS\tmore\n", "is not `<module>"), ("n.hthr\tBITS\n", "n.hthr was read")] {
            let refused = constants_rs(row, &module).unwrap_err();
            assert!(refused.contains(why), "{row}: {refused}");
        }
    }

    fn stated(symbol: &str, kinds: &[Kind], stack: u64) -> String {
        format!("# a first line\n{}.text\n", header(symbol, &Signature { kinds: kinds.to_vec(), stack }))
    }

    // A file that exports several symbols states each one's signature, and
    // each is read as its own: by its whole name, with its own stack.
    #[test]
    fn each_symbol_of_a_file_reads_its_own() {
        let (root, entry, other) = (Signature { kinds: vec![Kind::Span, Kind::Word], stack: 360 }, Signature { kinds: vec![Kind::Word, Kind::Word], stack: 144 },
            Signature { kinds: vec![Kind::Word], stack: 72 });
        let text = format!("# a first line\n{}{}{}.text\n", header("scan", &root), header("scan_step", &entry), header("step", &other));
        assert_eq!(Signature::read(&text, "scan"), Ok(root));
        assert_eq!(Signature::read(&text, "scan_step"), Ok(entry));
        assert_eq!(Signature::read(&text, "step"), Ok(other));
        assert!(Signature::read(&text, "scan_").unwrap_err().contains("states no signature of its own"));
        // A signature with no stack line after it is not this compiler's.
        let cut = format!("# signature: f(word) -> word\n{}", header("g", &Signature { kinds: vec![], stack: 72 }));
        assert!(Signature::read(&cut, "f").unwrap_err().contains("states no stack"));
    }

    // An entry of another export's program is declared from that export's
    // file and links nothing of its own.
    #[test]
    fn an_entry_is_declared_from_its_program() {
        let manifest = "m.hthr\tstep\tstate, byte\tscan\nn.hthr\tscan\ttext: span, at\n";
        let assembly = |function: &str| match function {
            "scan" => Ok(format!("{}{}.text\n", header("scan", &Signature { kinds: vec![Kind::Span, Kind::Word], stack: 216 }),
                header("step", &Signature { kinds: vec![Kind::Word, Kind::Word], stack: 72 }))),
            other => Err(format!("{other}.s was read")),
        };
        let text = exports_rs(manifest, &assembly).unwrap();
        assert!(text.contains("linked!(\"scan.s\");\n") && !text.contains("linked!(\"step.s\")"), "{text}");
        assert!(text.contains("    /// `step` of `m.hthr`, a function of `scan`'s program. STACK: 72 bytes.\n    pub safe fn step(state: u64, byte: u64) -> u64;\n"), "{text}");
        assert!(text.contains("pub fn scan(text: &[u8], at: u64) -> u64 {"), "{text}");
        let rows = exports(manifest).unwrap();
        assert_eq!((rows[0].file(), rows[0].entry().as_str(), rows[1].file()), ("scan", "m::step", "scan"));
        // The entry is held to its own signature in that file.
        let refused = exports_rs("m.hthr\tstep\tstate\tscan\nn.hthr\tscan\ttext: span, at\n", &assembly).unwrap_err();
        assert!(refused.contains("declares `step(word)`, and its compiled code takes `(word, word)`"), "{refused}");
        for (table, why) in [("m.hthr\tstep\ta\tscan\n", "which is no row"),
            ("m.hthr\tstep\ta\tscan\nm.hthr\tscan\ta\tlast\nm.hthr\tlast\ta\n", "which is itself an entry of `last`"),
            ("m.hthr\tstep\ta\tscan\tmore\n", "is not `<module>"), ("m.hthr\tstep\ta\t9\n", "is not `<module>")] {
            let refused = exports_rs(table, &assembly).unwrap_err();
            assert!(refused.contains(why), "{table}: {refused}");
        }
    }

    #[test]
    fn a_header_reads_back() {
        for kinds in [&[][..], &[Kind::Word], &[Kind::Span, Kind::Word], &[Kind::Word, Kind::Span, Kind::Span], &[Kind::SpanMut, Kind::Span, Kind::Word]] {
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

    // A span the code stores into is taken by `&mut`, and the wrapper says
    // what a lending to write asks.
    #[test]
    fn a_written_span_is_borrowed_to_write() {
        let assembly = |_: &str| Ok(stated("w", &[Kind::SpanMut, Kind::Span, Kind::Word], 144));
        let text = exports_rs("m.hthr\tw\tout: span mut, text: span, count\n", &assembly).unwrap();
        assert!(text.contains("        pub unsafe fn w(out: *mut u8, out_length: u64, text: *const u8, text_length: u64, count: u64) -> u64;\n"), "{text}");
        assert!(text.contains("pub fn w(out: &mut [u8], text: &[u8], count: u64) -> u64 {"), "{text}");
        assert!(text.contains("unsafe { raw::w(out.as_mut_ptr(), out.len() as u64, text.as_ptr(), text.len() as u64, count) }"), "{text}");
        assert!(text.contains("// - the bytes of `out` may be stored into"), "{text}");
        // A reader's wrapper says nothing of stores, and the table cannot
        // lend to read what the code writes, nor to write what it reads.
        let reader = exports_rs("m.hthr\tg\ttext: span, count\n", &|_: &str| Ok(stated("g", &[Kind::Span, Kind::Word], 144))).unwrap();
        assert!(!reader.contains("may be stored into"), "{reader}");
        for parameters in ["out: span, text: span, count", "out: span mut, text: span mut, count"] {
            let refused = exports_rs(&format!("m.hthr\tw\t{parameters}\n"), &assembly).unwrap_err();
            assert!(refused.contains("its compiled code takes `(span mut, span, word)`"), "{parameters}: {refused}");
        }
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

    // A method is a row by its path, exported under the symbol its path
    // derives or the one written before it; the symbol is its label, its
    // file and its Rust name, and the doc names the method.
    #[test]
    fn a_method_is_exported_under_its_symbol() {
        for (function, symbol) in [("f", "f"), ("Sha256::update", "sha256_update"), ("List::raise_letters", "list_raise_letters"),
            ("HashMap::get", "hash_map_get"), ("HTTPServer::run", "http_server_run"), ("U8x4::splat", "u8x4_splat"), ("A::B::c", "a_b_c")] {
            assert_eq!(symbol_of(function).as_deref(), Some(symbol), "{function}");
        }
        for function in ["", "List::", "::f", "List::9f", "List:f", "a-b"] { assert_eq!(symbol_of(function), None, "{function}"); }
        let manifest = "m.hthr\tList::raise_letters\ttext: span mut, count, from\nm.hthr\tlift = Sha256::update\tctx: span mut\n";
        let rows = exports(manifest).unwrap();
        assert_eq!((rows[0].function.as_str(), rows[0].symbol.as_str(), rows[0].file()), ("List::raise_letters", "list_raise_letters", "list_raise_letters"));
        assert_eq!((rows[1].function.as_str(), rows[1].symbol.as_str()), ("Sha256::update", "lift"));
        let assembly = |symbol: &str| Ok(match symbol {
            "list_raise_letters" => stated("list_raise_letters", &[Kind::SpanMut, Kind::Word, Kind::Word], 240),
            "lift" => stated("lift", &[Kind::SpanMut], 120),
            other => return Err(format!("{other}.s was read")),
        });
        let text = exports_rs(manifest, &assembly).unwrap();
        assert!(text.contains("linked!(\"list_raise_letters.s\");\nlinked!(\"lift.s\");\n"), "{text}");
        assert!(text.contains("/// `List::raise_letters` of `m.hthr`. STACK: 240 bytes.\npub fn list_raise_letters(text: &mut [u8], count: u64, from: u64) -> u64 {"), "{text}");
        assert!(text.contains("// SAFETY (the premises of `list_raise_letters_native_returns`, in order):"), "{text}");
        assert!(text.contains("unsafe { raw::lift(ctx.as_mut_ptr(), ctx.len() as u64) }"), "{text}");
        // An entry is named by the symbol of the export whose program it is in.
        let entry = exports("m.hthr\tstep\ta\tlist_scan\nm.hthr\tList::scan\ttext: span\n").unwrap();
        assert_eq!(entry[0].file(), "list_scan");
    }

    // Two rows that would be one symbol are refused, naming both and the
    // symbol; so is a path that is no path, and a method as an entry.
    #[test]
    fn a_symbol_two_rows_derive_is_refused() {
        for (table, why) in [
            ("m.hthr\tList::raise_letters\ta\nn.hthr\tlist_raise_letters\tb\n",
                "`list_raise_letters` of `n.hthr` and `List::raise_letters` of `m.hthr` are both exported as `list_raise_letters`"),
            ("m.hthr\tSha256::update\ta\nm.hthr\tsha256_update = List::sha256_update\ta\n",
                "`List::sha256_update` of `m.hthr` and `Sha256::update` of `m.hthr` are both exported as `sha256_update`"),
            ("m.hthr\tList::f\ta\nm.hthr\tList::f\ta\n", "lists `List::f` twice"),
            ("m.hthr\tList::9f\ta\n", "the function is a name or a method's path"),
            ("m.hthr\t9s = List::f\ta\n", "the function is a name or a method's path"),
            ("m.hthr\ts = \ta\n", "the function is a name or a method's path"),
            ("m.hthr\tList::step\ta\tscan\nm.hthr\tscan\ta\n", "`List::step` is a method, and an entry"),
        ] {
            let refused = exports(table).unwrap_err();
            assert!(refused.contains(why), "{table}: {refused}");
        }
    }
}
