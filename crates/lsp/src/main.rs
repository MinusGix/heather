//! A small, synchronous Language Server Protocol frontend for Heather.
//!
//! The compiler remains the source of truth: an opened buffer is overlaid on
//! its on-disk import closure, then every module is checked in dependency
//! order. Diagnostics run on open and save. Changes are retained for symbols
//! immediately but deliberately do not launch a potentially expensive check
//! on every keystroke.

use std::collections::HashMap;
use std::io::{self, BufRead, BufReader, BufWriter, Write};
use std::path::{Path, PathBuf};

use heather_cli::loader;
use heather_elab::{ElabError, Elaborator, LintProfile, Span, Warning};
use heather_syntax::{DatareprBody, Decl, DeclKind, InductiveDecl, InstanceBody, Item, parse_file};
use serde_json::{Value, json};

fn main() {
    if let Err(error) = Server::new().run() {
        eprintln!("heather-lsp: {error}");
        std::process::exit(1);
    }
}

struct Server {
    input: BufReader<io::Stdin>,
    output: BufWriter<io::Stdout>,
    root: Option<PathBuf>,
    documents: HashMap<String, String>,
    shutdown: bool,
}

impl Server {
    fn new() -> Self {
        Self {
            input: BufReader::new(io::stdin()),
            output: BufWriter::new(io::stdout()),
            root: None,
            documents: HashMap::new(),
            shutdown: false,
        }
    }

    fn run(&mut self) -> Result<(), String> {
        while let Some(message) = read_message(&mut self.input)? {
            let method = message.get("method").and_then(Value::as_str).map(str::to_string);
            let id = message.get("id").cloned();
            match (method.as_deref(), id) {
                (Some("initialize"), Some(id)) => {
                    self.initialize(message.get("params").unwrap_or(&Value::Null));
                    self.respond(id, json!({
                        "capabilities": {
                            "textDocumentSync": {
                                "openClose": true,
                                "change": 1,
                                "save": { "includeText": true }
                            },
                            "documentSymbolProvider": true,
                            "workspaceSymbolProvider": true
                        },
                        "serverInfo": { "name": "heather-lsp", "version": env!("CARGO_PKG_VERSION") }
                    }))?;
                }
                (Some("shutdown"), Some(id)) => {
                    self.shutdown = true;
                    self.respond(id, Value::Null)?;
                }
                (Some("textDocument/documentSymbol"), Some(id)) => {
                    let uri = pointer_str(&message, "/params/textDocument/uri");
                    let symbols = uri
                        .and_then(|uri| self.source(uri).map(|source| document_symbols(uri, source)))
                        .unwrap_or_default();
                    self.respond(id, Value::Array(symbols))?;
                }
                (Some("workspace/symbol"), Some(id)) => {
                    let query = pointer_str(&message, "/params/query").unwrap_or_default();
                    self.respond(id, Value::Array(self.workspace_symbols(query)))?;
                }
                (Some(method), Some(id)) => {
                    self.error(id, -32601, &format!("method not found: {method}"))?;
                }
                (Some("initialized"), None) => {}
                (Some("exit"), None) => break,
                (Some("textDocument/didOpen"), None) => self.did_open(&message)?,
                (Some("textDocument/didChange"), None) => self.did_change(&message),
                (Some("textDocument/didSave"), None) => self.did_save(&message)?,
                (Some("textDocument/didClose"), None) => self.did_close(&message)?,
                // Cancellation and configuration changes need no work in the
                // synchronous first version. Unknown notifications are legal.
                (Some(_), None) | (None, _) => {}
            }
        }
        Ok(())
    }

    fn initialize(&mut self, params: &Value) {
        let root_uri = params
            .get("rootUri")
            .and_then(Value::as_str)
            .or_else(|| params.pointer("/workspaceFolders/0/uri").and_then(Value::as_str));
        self.root = root_uri.and_then(path_from_uri);
    }

    fn did_open(&mut self, message: &Value) -> Result<(), String> {
        let Some(uri) = pointer_str(message, "/params/textDocument/uri") else { return Ok(()) };
        let Some(text) = pointer_str(message, "/params/textDocument/text") else { return Ok(()) };
        self.documents.insert(uri.to_string(), text.to_string());
        self.check(uri)
    }

    fn did_change(&mut self, message: &Value) {
        let Some(uri) = pointer_str(message, "/params/textDocument/uri") else { return };
        let Some(text) = message
            .pointer("/params/contentChanges")
            .and_then(Value::as_array)
            .and_then(|changes| changes.last())
            .and_then(|change| change.get("text"))
            .and_then(Value::as_str)
        else { return };
        self.documents.insert(uri.to_string(), text.to_string());
    }

    fn did_save(&mut self, message: &Value) -> Result<(), String> {
        let Some(uri) = pointer_str(message, "/params/textDocument/uri") else { return Ok(()) };
        if let Some(text) = message.pointer("/params/text").and_then(Value::as_str) {
            self.documents.insert(uri.to_string(), text.to_string());
        }
        self.check(uri)
    }

    fn did_close(&mut self, message: &Value) -> Result<(), String> {
        let Some(uri) = pointer_str(message, "/params/textDocument/uri") else { return Ok(()) };
        self.documents.remove(uri);
        self.publish(uri, Vec::new())
    }

    fn source(&self, uri: &str) -> Option<&str> {
        self.documents.get(uri).map(String::as_str)
    }

    fn check(&mut self, uri: &str) -> Result<(), String> {
        let Some(source) = self.documents.get(uri).cloned() else { return Ok(()) };
        let Some(path) = path_from_uri(uri) else {
            return self.publish(uri, vec![plain_diagnostic("Heather only supports file:// documents")]);
        };
        let search = self.search_paths(&path);
        let modules = match loader::load_overlay(&path, &search, &source) {
            Ok(modules) => modules,
            Err(error) => return self.publish(uri, vec![plain_diagnostic(&error.msg)]),
        };
        let target = match path.canonicalize() {
            Ok(path) => path,
            Err(error) => {
                return self.publish(uri, vec![plain_diagnostic(&format!("cannot read `{}`: {error}", path.display()))]);
            }
        };
        let mut elab = match Elaborator::with_prelude() {
            Ok(elab) => elab,
            Err(error) => {
                let message = format!("the Heather prelude failed to check: {error}");
                return self.publish(uri, vec![plain_diagnostic(&message)]);
            }
        };
        elab.set_kernel_workers(1);
        elab.set_lint_profile(self.lint_profile(&target));

        let mut diagnostics = Vec::new();
        for module in &modules {
            let errors = elab.check_module_source(&module.name, &module.src);
            let warnings = elab.take_warnings();
            if module.path == target {
                diagnostics.extend(errors.iter().map(|error| error_diagnostic(error, &module.src)));
                diagnostics.extend(warnings.iter().map(|warning| warning_diagnostic(warning, &module.src)));
            }
        }
        self.publish(uri, diagnostics)
    }

    fn search_paths(&self, path: &Path) -> Vec<PathBuf> {
        let mut paths = Vec::new();
        if let Some(root) = &self.root {
            // Not the root itself: the loader also searches below every
            // search directory, and below a workspace root lie build trees
            // and scratch copies of the library (docs/modules-design.md §3.2).
            for candidate in [root.join("lib/std"), root.join("lib")] {
                if candidate.is_dir() && !paths.contains(&candidate) {
                    paths.push(candidate);
                }
            }
        }
        if let Some(parent) = path.parent()
            && !paths.iter().any(|candidate| candidate == parent)
        {
            paths.push(parent.to_path_buf());
        }
        paths
    }

    fn lint_profile(&self, path: &Path) -> LintProfile {
        let stdlib = self.root.as_ref().map(|root| root.join("lib/std"));
        match stdlib.and_then(|path| path.canonicalize().ok()) {
            Some(stdlib) if path.starts_with(&stdlib) => LintProfile::Stdlib,
            _ => LintProfile::Default,
        }
    }

    fn workspace_symbols(&self, query: &str) -> Vec<Value> {
        let query = query.to_lowercase();
        let mut out = Vec::new();
        for (uri, source) in &self.documents {
            let module = module_name(uri);
            let Ok(file) = parse_file(source) else { continue };
            for symbol in item_symbols(source, &file.items) {
                let name = symbol.get("name").and_then(Value::as_str).unwrap_or_default();
                let qualified = format!("{module}::{name}");
                if !query.is_empty() && !qualified.to_lowercase().contains(&query) {
                    continue;
                }
                out.push(json!({
                    "name": qualified,
                    "kind": symbol.get("kind").cloned().unwrap_or(json!(13)),
                    "location": {
                        "uri": uri,
                        "range": symbol.get("selectionRange").cloned().unwrap_or_else(zero_range)
                    }
                }));
            }
        }
        out.sort_by(|a, b| {
            a.get("name").and_then(Value::as_str).cmp(&b.get("name").and_then(Value::as_str))
        });
        out
    }

    fn respond(&mut self, id: Value, result: Value) -> Result<(), String> {
        self.send(&json!({ "jsonrpc": "2.0", "id": id, "result": result }))
    }

    fn error(&mut self, id: Value, code: i64, message: &str) -> Result<(), String> {
        self.send(&json!({
            "jsonrpc": "2.0",
            "id": id,
            "error": { "code": code, "message": message }
        }))
    }

    fn publish(&mut self, uri: &str, diagnostics: Vec<Value>) -> Result<(), String> {
        self.send(&json!({
            "jsonrpc": "2.0",
            "method": "textDocument/publishDiagnostics",
            "params": { "uri": uri, "diagnostics": diagnostics }
        }))
    }

    fn send(&mut self, value: &Value) -> Result<(), String> {
        let body = serde_json::to_vec(value).map_err(|e| e.to_string())?;
        write!(self.output, "Content-Length: {}\r\n\r\n", body.len()).map_err(|e| e.to_string())?;
        self.output.write_all(&body).map_err(|e| e.to_string())?;
        self.output.flush().map_err(|e| e.to_string())
    }
}

fn read_message(input: &mut impl BufRead) -> Result<Option<Value>, String> {
    let mut length = None;
    loop {
        let mut line = String::new();
        let read = input.read_line(&mut line).map_err(|e| e.to_string())?;
        if read == 0 {
            return Ok(None);
        }
        if line == "\r\n" || line == "\n" {
            break;
        }
        if let Some(value) = line.strip_prefix("Content-Length:") {
            length = Some(value.trim().parse::<usize>().map_err(|e| e.to_string())?);
        }
    }
    let length = length.ok_or("missing Content-Length header")?;
    let mut body = vec![0; length];
    input.read_exact(&mut body).map_err(|e| e.to_string())?;
    serde_json::from_slice(&body).map(Some).map_err(|e| e.to_string())
}

fn pointer_str<'a>(message: &'a Value, pointer: &str) -> Option<&'a str> {
    message.pointer(pointer).and_then(Value::as_str)
}

fn error_span(error: &ElabError) -> Span {
    match error {
        ElabError::Parse(error) => error.span,
        ElabError::Elab { span, .. }
        | ElabError::Kernel { span, .. }
        | ElabError::Resolution { span, .. }
        | ElabError::ArgSlotEscape { span } => *span,
        ElabError::UnsolvedGoals { goals, .. } => {
            goals.first().map(|goal| goal.span).unwrap_or(Span { start: 0, end: 0 })
        }
    }
}

fn error_diagnostic(error: &ElabError, source: &str) -> Value {
    json!({
        "range": range(source, error_span(error)),
        "severity": 1,
        "source": "heather",
        "message": error.to_string().trim_end()
    })
}

fn warning_diagnostic(warning: &Warning, source: &str) -> Value {
    json!({
        "range": range(source, warning.span),
        "severity": 2,
        "code": warning.lint.name(),
        "source": "heather",
        "message": warning.msg
    })
}

fn plain_diagnostic(message: &str) -> Value {
    json!({
        "range": zero_range(),
        "severity": 1,
        "source": "heather",
        "message": message
    })
}

fn zero_range() -> Value {
    json!({
        "start": { "line": 0, "character": 0 },
        "end": { "line": 0, "character": 0 }
    })
}

fn range(source: &str, span: Span) -> Value {
    json!({
        "start": position(source, span.start),
        "end": position(source, span.end.max(span.start + usize::from(span.start < source.len())))
    })
}

/// LSP columns are UTF-16 code units, while compiler spans are UTF-8 bytes.
fn position(source: &str, byte: usize) -> Value {
    let byte = floor_char_boundary(source, byte.min(source.len()));
    let before = &source[..byte];
    let line = before.bytes().filter(|byte| *byte == b'\n').count();
    let line_start = before.rfind('\n').map_or(0, |newline| newline + 1);
    let character = source[line_start..byte].encode_utf16().count();
    json!({ "line": line, "character": character })
}

fn floor_char_boundary(source: &str, mut byte: usize) -> usize {
    while byte > 0 && !source.is_char_boundary(byte) {
        byte -= 1;
    }
    byte
}

fn document_symbols(uri: &str, source: &str) -> Vec<Value> {
    let Ok(file) = parse_file(source) else { return Vec::new() };
    let children = item_symbols(source, &file.items);
    let whole = range(source, Span { start: 0, end: source.len() });
    vec![json!({
        "name": module_name(uri),
        "detail": "Heather module",
        "kind": 3,
        "range": whole,
        "selectionRange": range(source, Span { start: 0, end: source.len().min(1) }),
        "children": children
    })]
}

fn item_symbols(source: &str, items: &[Item]) -> Vec<Value> {
    items.iter().map(|item| match item {
        Item::Decl(decl) => decl_symbol(source, decl),
        Item::Inductive(inductive) => inductive_symbol(source, inductive),
        Item::Class(class) => {
            let children = class.fields.iter().filter_map(|field| {
                field.name.as_ref().map(|name| symbol(source, name, 8, field.span, Vec::new()))
            }).collect();
            symbol(source, &class.name, 5, class.span, children)
        }
        Item::Instance(instance) => {
            let children = match &instance.body {
                InstanceBody::Block(decls) => decls.iter().map(|decl| decl_symbol(source, decl)).collect(),
                InstanceBody::Literal(fields) => fields.iter().map(|field| {
                    symbol(source, &field.name, 8, field.span, Vec::new())
                }).collect(),
            };
            symbol(source, &format!("instance {}", instance.class.name), 11, instance.span, children)
        }
        Item::Designation(designation) => {
            symbol(source, &format!("designation {}", designation.symbol), 14, designation.span, Vec::new())
        }
        Item::Datarepr(datarepr) => {
            let children = match &datarepr.body {
                DatareprBody::Fields(fields) => fields.iter().map(|field| {
                    symbol(source, &field.name, 8, field.span, Vec::new())
                }).collect(),
                DatareprBody::Mint(_) => Vec::new(),
            };
            symbol(source, &datarepr.name, 23, datarepr.span, children)
        }
        Item::Impl(implementation) => {
            let name = format!("impl {} for {}", implementation.op, implementation.repr);
            symbol(source, &name, 12, implementation.span, Vec::new())
        }
        Item::Import(import) => {
            symbol(source, &format!("import {}", import.module), 2, import.span, Vec::new())
        }
        Item::Generate(generate) => {
            let written = source.get(generate.generator.span.start..generate.generator.span.end).unwrap_or("…");
            symbol(source, &format!("generate {written}"), 12, generate.span, Vec::new())
        }
        Item::Prefixed(prefixed) => decl_symbol(source, &prefixed.decl),
        Item::PrefixedRecord(prefixed) => inductive_symbol(source, &prefixed.record),
    }).collect()
}

fn inductive_symbol(source: &str, inductive: &InductiveDecl) -> Value {
    let children = inductive.ctors.iter().map(|ctor| {
        symbol(source, &ctor.name, 9, ctor.span, Vec::new())
    }).collect();
    symbol(source, &inductive.name, if inductive.is_record { 23 } else { 10 }, inductive.span, children)
}

fn decl_symbol(source: &str, decl: &Decl) -> Value {
    let kind = match decl.kind {
        // A `def` is a constant.
        DeclKind::Fn if decl.value => 14,
        DeclKind::Fn | DeclKind::Theorem => 12,
        DeclKind::Axiom => 13,
    };
    symbol(source, &decl.name, kind, decl.span, Vec::new())
}

fn symbol(source: &str, name: &str, kind: u8, span: Span, children: Vec<Value>) -> Value {
    let selection = name_span(source, span, name).unwrap_or(span);
    let mut value = json!({
        "name": name,
        "kind": kind,
        "range": range(source, span),
        "selectionRange": range(source, selection)
    });
    if !children.is_empty() {
        value.as_object_mut().expect("symbol object").insert("children".into(), Value::Array(children));
    }
    value
}

fn name_span(source: &str, span: Span, name: &str) -> Option<Span> {
    let start = floor_char_boundary(source, span.start.min(source.len()));
    let end = floor_char_boundary(source, span.end.min(source.len()));
    let needle = name
        .strip_prefix("instance ")
        .or_else(|| name.strip_prefix("import "))
        .unwrap_or(name);
    source[start..end].find(needle).map(|offset| Span {
        start: start + offset,
        end: start + offset + needle.len(),
    })
}

fn module_name(uri: &str) -> String {
    path_from_uri(uri)
        .and_then(|path| path.file_stem().map(|stem| stem.to_string_lossy().into_owned()))
        .unwrap_or_else(|| "module".into())
}

fn path_from_uri(uri: &str) -> Option<PathBuf> {
    let encoded = uri.strip_prefix("file://")?;
    let bytes = encoded.as_bytes();
    let mut decoded = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'%' && i + 2 < bytes.len() {
            let high = hex(bytes[i + 1])?;
            let low = hex(bytes[i + 2])?;
            decoded.push(high * 16 + low);
            i += 3;
        } else {
            decoded.push(bytes[i]);
            i += 1;
        }
    }
    String::from_utf8(decoded).ok().map(PathBuf::from)
}

fn hex(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn positions_use_utf16_columns() {
        assert_eq!(position("a🙂b", 5), json!({ "line": 0, "character": 3 }));
        assert_eq!(position("x\nλy", 4), json!({ "line": 1, "character": 1 }));
    }

    #[test]
    fn symbols_are_nested_below_the_module() {
        let symbols = document_symbols(
            "file:///tmp/math.hthr",
            "fn zero() -> Nat { 0 }\ninductive Bit { O, I }",
        );
        assert_eq!(symbols[0]["name"], "math");
        assert_eq!(symbols[0]["children"][0]["name"], "zero");
        assert_eq!(symbols[0]["children"][1]["children"][1]["name"], "I");
    }

    #[test]
    fn file_uris_decode_spaces_and_unicode() {
        assert_eq!(path_from_uri("file:///tmp/a%20b/%CE%BB.hthr"), Some(PathBuf::from("/tmp/a b/λ.hthr")));
    }
}
