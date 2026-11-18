//! `heather eval <file.hthr> <term>`: what a closed term evaluates to,
//! printed. An evaluation and not a check: nothing it prints is a theorem,
//! and it says so on every run.
//!
//! The term is elaborated as `def eval_value = <term>;` in a probe module
//! over the file, which imports the file and everything the file imports, so
//! the term reads the file's names as its own declarations do. The value is
//! read with the evaluator `compile-x86` and `write-elf` read their
//! `List<Nat>` answers with (`function_ir_source::Reads`): a second probe
//! encodes it as a `List<Nat>`, one encoder per node of its type, written in
//! Heather over the type's own constructors, and the numbers are decoded
//! here. A list cell is forced only when it is read, so the read stops at the
//! cap (`--limit`) without evaluating the rest, and what was cut is printed
//! as `…`.
//!
//! The types read that way are `Nat`, `Bool`, `Char`, `String`, and `List`
//! and `Option` of those, nested. A `String` at the top is printed as its
//! text, so a report reads as written; inside a list or an option it is
//! quoted. A value of any other type is read a layer at a time by its
//! constructors (`heather_elab::show_global`): `R(f := 1, g := [C(2)])` as
//! the declarations name them, with `--limit` counting the layers read.
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::sync::Arc;

use heather_cache::module_image::ImageFreshness;
use heather_cli::{loader, semantic::SemanticSession};
use heather_elab::{function_ir_source, Elaborator};

/// The modules the probes import besides the file's own: the encoders name
/// these types' constructors.
const IMPORTS: &[&str] = &["bool", "nat", "list", "option", "char", "string"];
const VALUE_MODULE: &str = "heather_eval_value";
const READ_MODULE: &str = "heather_eval_read";
/// Numbers read off the encoding before the read stops, by default: a
/// string's character costs two.
const DEFAULT_LIMIT: usize = 1 << 16;

const USAGE: &str = "usage: heather eval <file.hthr> <term> [--type <type>] [-L <dir>]... [--cache | --cache-dir <dir>] [--accept-stale-images] [--limit <n>] [--kernel-workers <n>]";

pub fn run(args: &[String]) -> ExitCode {
    match eval(args) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) if error.starts_with("error: ") || error.starts_with("usage: ") => {
            eprintln!("{error}");
            ExitCode::from(if error.starts_with("usage: ") { 2 } else { 1 })
        }
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::from(1)
        }
    }
}

fn eval(args: &[String]) -> Result<(), String> {
    let mut positional = Vec::new();
    let mut cache = None;
    let mut freshness = ImageFreshness::Exact;
    let mut limit = DEFAULT_LIMIT;
    let mut kernel_workers = None;
    let mut at_type = None;
    let mut search = vec![PathBuf::from("lib/std"), PathBuf::from("lib")];
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--cache" => { cache.get_or_insert_with(heather_cache::default_dir); }
            "--accept-stale-images" => freshness = ImageFreshness::AcceptStale,
            // The type the term is checked at, for a term that only checks
            // (a list literal, a numeral meant as another type).
            "--type" => at_type = Some(args.next().ok_or("--type needs a type")?.as_str()),
            "-L" | "--cache-dir" => {
                let value = PathBuf::from(args.next().ok_or_else(|| format!("{arg} needs a path"))?);
                if arg == "-L" {
                    if !search.contains(&value) { search.push(value); }
                } else {
                    cache = Some(value);
                }
            }
            "--limit" | "--kernel-workers" => {
                let n = args.next().and_then(|value| value.parse::<usize>().ok()).filter(|&n| n > 0)
                    .ok_or_else(|| format!("{arg} needs a positive integer"))?;
                if arg == "--limit" { limit = n; } else { kernel_workers = Some(n); }
            }
            // A term that starts with `-` follows a `--`.
            "--" => positional.extend(args.by_ref().map(String::as_str)),
            _ if arg.starts_with('-') => return Err(format!("unknown option `{arg}`\n{USAGE}")),
            _ => positional.push(arg.as_str()),
        }
    }
    let [source, term] = positional[..] else { return Err(USAGE.into()) };
    let source = Path::new(source);
    let sources = loader::load_with(source, &search, IMPORTS).map_err(|e| e.msg)?;
    let canonical = source.canonicalize().map_err(|e| format!("{}: {e}", source.display()))?;
    let root = sources.iter().find(|m| m.path == canonical).ok_or("the file is not in its own closure")?;

    let mut elab = Elaborator::with_prelude().map_err(|e| format!("prelude: {e}"))?;
    elab.set_kernel_workers(
        kernel_workers.or_else(heather_elab::kernel_workers_from_env).unwrap_or(heather_elab::DEFAULT_KERNEL_WORKERS),
    );
    let verdicts = cache.as_ref().map(|dir| {
        let (store, rejected) = heather_cache::Cache::open(dir.clone());
        if let Some(msg) = rejected.as_ref().and_then(|r| r.message()) {
            eprintln!("{msg}");
        }
        Arc::new(store)
    });
    let gate = verdicts.clone().unwrap_or_else(|| Arc::new(heather_cache::Cache::in_process()));
    elab.set_gate(gate as Arc<dyn heather_elab::gate::KernelGate>);
    let mut session = SemanticSession::new(cache).with_freshness(freshness);
    let checked = sources.iter().try_for_each(|module| crate::native::check_file(&mut elab, &mut session, module));
    if let Some(store) = verdicts && let Err(err) = store.save() {
        eprintln!("cache: could not write verdicts: {err}");
    }
    checked?;

    // The term, over the file and what the file imports: its imports are
    // the root's own lines, listed names included, so a bare name the file
    // reads one way the term reads the same way.
    let mut imports = format!("import {};\n", root.name);
    for import in heather_syntax::leading_imports(&root.src) {
        let listed = if import.listed.is_empty() { String::new() } else {
            format!("::{{{}}}", import.listed.iter().map(|(name, _)| name.as_str()).collect::<Vec<_>>().join(", "))
        };
        imports.push_str(&format!("import {}{listed};\n", import.module));
    }
    let annotation = at_type.map(|ty| format!(": {ty}")).unwrap_or_default();
    let head = format!("{imports}\ndef eval_value{annotation} = (\n");
    let value_text = format!("{head}{term}\n);\n");
    elab.elab_module_source(VALUE_MODULE, &value_text).map_err(|e| term_error(e, &value_text, head.len(), term))?;
    let value = format!("{VALUE_MODULE}::eval_value");
    let spelled = heather_elab::global_type_source(&elab, &value);
    let label = |ty: &str| eprintln!("evaluating `{}` : {ty} (an evaluation: untrusted, it proves nothing and is not a check)", term.trim());
    // Any other type is read a layer at a time, by its constructors
    // (`heather_elab::show_global`): slower, as each layer is a weak head
    // of its own, but it reads whatever the display can spell.
    let Some(shape) = spelled.as_deref().and_then(Shape::parse) else {
        label(spelled.as_deref().unwrap_or("(a type with no spelling)"));
        let (shown, cut) = heather_elab::show_global(&elab, &value, limit).map_err(|e| format!("evaluation: {e}"))?;
        println!("{shown}");
        if cut {
            eprintln!("cut at {limit} nodes (`--limit`)");
        }
        return Ok(());
    };
    let spelled = spelled.unwrap_or_default();

    let mut read_text = format!("import {VALUE_MODULE};\n");
    for module in IMPORTS { read_text.push_str(&format!("import {module};\n")); }
    let mut encoders = Encoders::default();
    let top = encoders.encoder(&shape);
    read_text.push_str(&encoders.text);
    read_text.push_str(&format!("fn eval_read() → List<Nat> {{ eval_enc_{top}({value}) }}\n"));
    elab.elab_module_source(READ_MODULE, &read_text)
        .map_err(|e| format!("the encoder for `{spelled}` was refused (a defect of `heather eval`):\n{}", e.render(&read_text)))?;

    label(&spelled);
    let (numbers, cut) = function_ir_source::traced(&elab, "eval", || function_ir_source::with_reads(&elab, |reads| reads.numbers_up_to(&format!("{READ_MODULE}::eval_read"), limit)))
        .map_err(|e| format!("evaluation: {e}"))?;
    let mut numbers = numbers.into_iter();
    let shown = shape.show(&mut numbers, true).ok_or("the encoding did not read back (a defect of `heather eval`)")?;
    println!("{shown}");
    if cut {
        eprintln!("cut at {limit} encoded numbers (`--limit`)");
    }
    Ok(())
}

/// An elaboration error in the term, said as one: its position is the
/// term's own (`<term>:1:5`), with the term quoted under it, since the
/// probe's line numbers would point into a file nobody wrote. An error that
/// points elsewhere (in `--type`) is shown in the probe.
fn term_error(mut error: heather_elab::ElabError, probe: &str, at: usize, term: &str) -> String {
    use heather_elab::ElabError;
    let span = match &mut error {
        ElabError::Parse(e) => Some(&mut e.span),
        ElabError::Elab { span, .. } | ElabError::Kernel { span, .. }
        | ElabError::Resolution { span, .. } | ElabError::ArgSlotEscape { span } => Some(span),
        ElabError::UnsolvedGoals { .. } => None,
    };
    match span {
        Some(span) if span.start >= at && span.end <= at + term.len() => {
            span.start -= at;
            span.end -= at;
            error.render_snippet(term, "<term>")
        }
        _ => error.render_snippet(probe, "<eval probe>"),
    }
}

/// A type `eval` reads, by its spelling.
#[derive(Debug, PartialEq)]
enum Shape {
    Nat,
    Bool,
    Char,
    Str,
    List(Box<Shape>, String),
    Option(Box<Shape>, String),
}

impl Shape {
    /// A qualified spelling (`list::List<nat::Nat>`) read as a shape. The
    /// qualifier must be the standard module the type lives in, or none.
    fn parse(spelled: &str) -> Option<Shape> {
        let (shape, rest) = Shape::parse_at(spelled.trim())?;
        rest.trim().is_empty().then_some(shape)
    }

    fn parse_at(text: &str) -> Option<(Shape, &str)> {
        let text = text.trim_start();
        let end = text.find(|c: char| !(c.is_alphanumeric() || c == '_' || c == ':')).unwrap_or(text.len());
        let (path, rest) = text.split_at(end);
        let (module, name) = match path.rsplit_once("::") {
            Some((module, name)) => (Some(module), name),
            None => (None, path),
        };
        let home = match name {
            "Nat" => "nat",
            "Bool" => "bool",
            "Char" => "char",
            "String" => "string",
            "List" => "list",
            "Option" => "option",
            _ => return None,
        };
        if module.is_some_and(|module| module != home) {
            return None;
        }
        let rest = rest.trim_start();
        match name {
            "List" | "Option" => {
                let inner = rest.strip_prefix('<')?;
                let (element, rest) = Shape::parse_at(inner)?;
                let rest = rest.trim_start().strip_prefix('>')?;
                let spelled = text[..text.len() - rest.len()].trim().to_string();
                let element = Box::new(element);
                Some((if name == "List" { Shape::List(element, spelled) } else { Shape::Option(element, spelled) }, rest))
            }
            "Nat" => Some((Shape::Nat, rest)),
            "Bool" => Some((Shape::Bool, rest)),
            "Char" => Some((Shape::Char, rest)),
            _ => Some((Shape::Str, rest)),
        }
    }

    /// The value the next numbers encode ([`Encoders`]), shown; `top` for
    /// the whole value, whose string is printed as its text. Numbers that
    /// run out mid-value (the read's cap) end the show with `…`.
    fn show(&self, numbers: &mut impl Iterator<Item = u64>, top: bool) -> Option<String> {
        let mut out = String::new();
        self.show_into(numbers, top, &mut out)?;
        Some(out)
    }

    /// `Some(false)` once the numbers ran out, `None` for an encoding that
    /// does not read.
    fn show_into(&self, numbers: &mut impl Iterator<Item = u64>, top: bool, out: &mut String) -> Option<bool> {
        let Some(first) = numbers.next() else {
            out.push('…');
            return Some(false);
        };
        match self {
            Shape::Nat => out.push_str(&first.to_string()),
            Shape::Bool => out.push_str(match first { 0 => "False", 1 => "True", _ => return None }),
            Shape::Char => out.push_str(&format!("{:?}", char_of(first))),
            Shape::Str => {
                let mut text = String::new();
                let mut tag = first;
                let whole = loop {
                    match tag {
                        0 => break true,
                        1 => match numbers.next() {
                            Some(code) => text.push(char_of(code)),
                            None => break false,
                        },
                        _ => return None,
                    }
                    match numbers.next() {
                        Some(next) => tag = next,
                        None => break false,
                    }
                };
                if top {
                    out.push_str(&text);
                    if !whole { out.push('…'); }
                } else if whole {
                    out.push_str(&format!("{text:?}"));
                } else {
                    out.push_str(&format!("{:?}…", text));
                }
                return Some(whole);
            }
            Shape::List(element, _) => {
                out.push('[');
                let mut tag = first;
                let mut started = false;
                loop {
                    match tag {
                        0 => break,
                        1 => {
                            if started { out.push_str(", "); }
                            started = true;
                            if !element.show_into(numbers, false, out)? { return Some(false); }
                        }
                        _ => return None,
                    }
                    match numbers.next() {
                        Some(next) => tag = next,
                        None => {
                            out.push_str(", …");
                            return Some(false);
                        }
                    }
                }
                out.push(']');
            }
            Shape::Option(element, _) => match first {
                0 => out.push_str("None"),
                1 => {
                    out.push_str("Some(");
                    if !element.show_into(numbers, false, out)? { return Some(false); }
                    out.push(')');
                }
                _ => return None,
            },
        }
        Some(true)
    }
}

fn char_of(code: u64) -> char {
    u32::try_from(code).ok().and_then(char::from_u32).unwrap_or('\u{FFFD}')
}

/// The encoders of a value's type, a function per node, each from the
/// node's value to the `List<Nat>` [`Shape::show`] reads: a `Nat` is
/// itself, a `Bool` 0 or 1, a `Char` its code; a list (and a string, the
/// list of its characters) is each element after a 1 and then a 0, and an
/// option 0, or 1 and the value.
#[derive(Default)]
struct Encoders {
    text: String,
    count: usize,
}

impl Encoders {
    /// The number of `shape`'s encoder, written with its elements'.
    fn encoder(&mut self, shape: &Shape) -> usize {
        let at = self.count;
        self.count += 1;
        let f = format!("eval_enc_{at}");
        let def = match shape {
            Shape::Nat => format!("fn {f}(x: Nat) → List<Nat> {{ [x] }}\n"),
            Shape::Bool => format!("fn {f}(x: Bool) → List<Nat> {{ match x {{ False => [0], True => [1] }} }}\n"),
            Shape::Char => format!("fn {f}(x: Char) → List<Nat> {{ [x.code] }}\n"),
            Shape::Str => format!("fn {f}_chars(xs: List<Char>) → List<Nat> {{ match xs {{ Nil => [0], Cons(c, rest) => Cons(1, Cons(c.code, {f}_chars(rest))) }} }}\n\
                fn {f}(x: String) → List<Nat> {{ {f}_chars(x.chars) }}\n"),
            Shape::List(element, spelled) => {
                let e = self.encoder(element);
                format!("fn {f}(xs: {spelled}) → List<Nat> {{ match xs {{ Nil => [0], Cons(x, rest) => Cons(1, eval_enc_{e}(x) ++ {f}(rest)) }} }}\n")
            }
            Shape::Option(element, spelled) => {
                let e = self.encoder(element);
                format!("fn {f}(x: {spelled}) → List<Nat> {{ match x {{ None => [0], Some(v) => Cons(1, eval_enc_{e}(v)) }} }}\n")
            }
        };
        self.text.push_str(&def);
        at
    }
}

#[cfg(test)]
mod tests {
    use super::Shape;

    #[test]
    fn shapes_parse_by_their_standard_module() {
        assert_eq!(Shape::parse("nat::Nat"), Some(Shape::Nat));
        assert_eq!(Shape::parse("list::List<string::String>"),
            Some(Shape::List(Box::new(Shape::Str), "list::List<string::String>".into())));
        assert_eq!(Shape::parse("Option<List<Nat>>"), Some(Shape::Option(
            Box::new(Shape::List(Box::new(Shape::Nat), "List<Nat>".into())), "Option<List<Nat>>".into())));
        assert_eq!(Shape::parse("mine::List<Nat>"), None);
        assert_eq!(Shape::parse("Vec<Nat, 3>"), None);
        assert_eq!(Shape::parse("List<Nat> → Nat"), None);
    }

    #[test]
    fn a_cut_encoding_shows_where_it_was_cut() {
        let list = Shape::parse("List<String>").unwrap();
        let whole = [1, 1, 104, 1, 105, 0, 1, 0, 0];
        assert_eq!(list.show(&mut whole.into_iter(), true).as_deref(), Some(r#"["hi", ""]"#));
        assert_eq!(list.show(&mut whole[..4].iter().copied(), true).as_deref(), Some(r#"["h"…"#));
        let text = Shape::Str;
        assert_eq!(text.show(&mut [1, 104, 1, 105, 0].into_iter(), true).as_deref(), Some("hi"));
        assert_eq!(text.show(&mut [1, 104].into_iter(), true).as_deref(), Some("h…"));
        assert_eq!(Shape::parse("Option<Bool>").unwrap().show(&mut [1, 1].into_iter(), true).as_deref(), Some("Some(True)"));
    }
}
