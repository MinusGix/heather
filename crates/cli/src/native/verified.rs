//! `compile-x86` through the verified lowering
//! (issues/function-ir-verified-lowering.md, round 4).
//!
//! The function and the functions it calls are reflected into a FunctionIR
//! program, and the certificate is what `function_ir_compile` says about it:
//! the program lowered by `lower_program` with the heuristic's placement,
//! evaluable (checked by `program_scan_at`, one pass over each function
//! against a table of the functions' arities, and
//! `program_scan_at_evaluable`; issues/function-ir-evaluable-quadratic.md),
//! evaluating to the source function, and so returning the
//! source's value at the function's label. Nothing in it is about this
//! program's code beyond equations the kernel checks by evaluation. The
//! bytes and the entry offset are evaluated here, from the same
//! definitions, and stated in the certificate as literals.
//!
//! Everything is a function at a time: the placement, the emission and the
//! scan are each read and each stated per function, and the layout and the
//! bytes by a table of the labels (`labels.rs`), so what a certificate
//! costs to make and to check follows the program's size and its largest
//! function, never their product
//! (issues/compile-x86-certificate-memory.md).

use std::collections::BTreeSet;

use heather_elab::{Elaborator, function_ir_source};

use super::answers::{Answers, Reading};

pub(super) struct Compiled {
    /// The certificate's source.
    pub text: String,
    /// The whole program's code, every function in it.
    pub bytes: Vec<u8>,
    /// Where the exported function starts.
    pub entry: usize,
    /// Where each of the program's other exported functions starts, as the
    /// shape lists them.
    pub entries: Vec<usize>,
    /// The stack the exported function's theorem asks for below its return
    /// address (its row of the room table, `program_rooms_by`: its frame,
    /// sized by what it saves and whether it calls, and the deepest
    /// callee's room with a call's 24 bytes below it), and each other
    /// exported function's, as `entries` lists them.
    pub room: u64,
    pub rooms: Vec<u64>,
}

const IMPORTS: &[&str] = &["function_ir", "function_ir_eval", "function_ir_lower", "function_ir_lower_structured",
    "function_ir_lower_calls", "function_ir_compile", "x86_64", "x86_64_block", "x86_64_fetch", "x86_64_data_read",
    "x86_64_fetched_code", "x86_64_stack", "x86_64_asm", "x86_64_asm_runs", "x86_64_asm_table", "x86_64_stack_runs", "bitvec", "bool", "list",
    "logic", "nat", "option", "function_ir_correct"];

/// What a program that is lent buffers needs besides: that it stores into
/// none, and the laws its buffers are lent under.
const LENT_IMPORTS: &[&str] = &["function_ir_writes", "function_ir_lower_reads", "x86_64_lending", "function_ir_state"];

/// And what one that stores into them needs: the run of a program over a
/// file, and the ending the generator states it with.
const WRITTEN_IMPORTS: &[&str] = &["function_ir_run", "rt_file_loop", "rt_file_returns"];

/// What a program and its agreement need (`heather reflect`'s module).
pub(super) const PROGRAM_IMPORTS: &[&str] = &["function_ir", "function_ir_eval", "function_ir_compile", "bitvec", "bool", "list", "logic", "nat", "option"];

/// The program for `source` when the verified lowering's fragment covers it.
pub(super) fn reflect(elab: &Elaborator, source: &str) -> Result<function_ir_source::ReflectedProgram, String> {
    function_ir_source::reflect_program(elab, source).map_err(|e| e.to_string())
}

/// What the certificate is about: a FunctionIR program, its functions
/// `{prefix}_fn{k}()` and lists `{prefix}_first_{k}()` defined, its
/// function `root` the exported one, and the theorem `{prefix}_agrees` that
/// it evaluates to the source function (`answer`, over `a0, a1, …`).
pub(super) struct Shape {
    pub functions: usize,
    pub root: usize,
    pub arity: usize,
    /// Imports and the program's definitions.
    pub definitions: String,
    /// `{prefix}_evaluable` and `{prefix}_agrees`.
    pub agreement: String,
    pub answer: String,
    /// For a program that is lent spans (a `runtime fn` reading
    /// `List<BitVec(8)>` parameters): how many buffers each function takes,
    /// by function. The code's arguments are then each span's address and
    /// length, the root's spans first, and its words after them.
    pub lent: Option<Vec<u64>>,
    /// For a program that stores into the spans it is lent (a `runtime fn`
    /// whose type ends in `Mutated`): which of the root's buffers it stores
    /// into, by buffer. The certificate's lending lets exactly those be
    /// written.
    pub marks: Option<Vec<bool>>,
    /// For a program that stores into its spans and calls over views of
    /// them: each function's row of marks, by function, a mark for each
    /// buffer the function is lent (`program_marked`). One list of marks
    /// cannot state such a program, since a callee numbers its views and
    /// not its caller's buffers; the root's row is then `marks`.
    pub tables: Option<Vec<Vec<bool>>>,
    /// The program's other functions exported beside its root
    /// ([`runtime_entries`]).
    pub entries: Vec<Entry>,
    /// Whether the code is lowered from the program the optimizer makes of
    /// this one ([`optimize`]): its definitions are then `{prefix}_cut_…`,
    /// and the checks the lowering needs are stated of them.
    pub optimize: bool,
}

/// Whether `compile-x86` runs the optimizer over a program that is lent
/// spans: it does unless `HEATHER_OPTIMIZE=off`, which is there to measure
/// what the passes buy and to tell a refusal of theirs from the lowering's.
fn optimizing() -> bool { std::env::var("HEATHER_OPTIMIZE").as_deref() != Ok("off") }

/// The stem the lowered program's definitions are named under: the
/// program's own, or `{prefix}_cut` where the optimizer has been over it
/// (`{prefix}_opt_…` is what its stage made, `{prefix}_cut_…` that with the
/// functions nothing reaches emptied).
fn lowered_stem(prefix: &str, optimize: bool) -> String { if optimize { format!("{prefix}_cut") } else { prefix.to_string() } }

/// Another function of a program, exported beside the program's root:
/// `symbol` the name it is linked under, `source` the Heather function,
/// `index` which of the program's functions it is and `arity` how many
/// words it takes.
pub(super) struct Entry {
    pub symbol: String,
    pub source: String,
    pub index: usize,
    pub arity: usize,
}

/// What a `runtime fn` does with spans: takes none, reads them
/// (`f::agrees_over`), or stores into one (`f::runs_over`).
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Spans { None, Read, Written }

impl Shape {
    /// The Rust reflector's program, its agreement generated here.
    pub fn reflected(prefix: &str, program: &function_ir_source::ReflectedProgram) -> Shape {
        let root = &program.functions[program.root];
        let mut definitions = owner_imports(program);
        definitions.push_str(&program_text(prefix, program));
        Shape {
            functions: program.functions.len(),
            root: program.root,
            arity: root.arity,
            definitions,
            agreement: agreement_text(prefix, program),
            answer: root.answer(&arguments(root.arity)),
            lent: None,
            marks: None,
            tables: None,
            entries: Vec::new(),
            optimize: false,
        }
    }

    /// A `runtime fn`'s program, as its generator published it
    /// (`{source}::program`, its last function `source`, the others the
    /// runtime fns it reaches) with its agreement (`{source}::agrees`, from
    /// the functions' `Compile` instances, docs/native/runtime-fn-setups-design.md
    /// §16.9): nothing about the program is proved here.
    pub fn runtime(prefix: &str, owner: &str, source: &str, functions: usize, arity: usize) -> Shape {
        let parameters = arguments(arity);
        let answer = format!("{source}({})", parameters.join(", "));
        let mut definitions = format!("import {owner};\nimport runtime;\n");
        definitions.push_str(&format!("\n// The program `runtime fn {source}` published, callees first: function `k` the one with `k` after it.
fn {prefix}_program() → List<Function> {{ {source}::program }}
"));
        for k in 0..functions {
            definitions.push_str(&format!("fn {prefix}_first_{k}() → List<Function> {{ {prefix}_program().drop({}) }}
fn {prefix}_fn{k}() → Function {{ match {prefix}_first_{k}() {{ Nil => Setup::code_of(None), Cons(function, _) => function }} }}
", functions - 1 - k));
        }
        let typed = typed(&parameters);
        let agreement = format!("{evaluable}

// The program's function {f} evaluates to the source function: the
// generator's theorem, from each function's `Compile` instance.
theorem {prefix}_agrees({typed}): program_eval({prefix}_program(), {f}, [{list}]) = {answer} {{
    {source}::agrees({list})
}}
", evaluable = evaluable_text(prefix, functions, &format!("{source}::arities")), f = functions - 1, list = parameters.join(", "));
        Shape { functions, root: functions - 1, arity, definitions, agreement, answer, lent: None, marks: None, tables: None, entries: Vec::new(), optimize: false }
    }

    /// A `runtime fn` that reads spans: its program is lent buffers
    /// (`counts`, by function), stores into none (`{prefix}_quiet`, by
    /// evaluation), and over any file evaluates to the function at the
    /// file's spans (`{source}::agrees_over`, the generator's theorem).
    /// `arity` counts the code's words: an address and a length for each
    /// span, then the function's own.
    pub fn runtime_lent(prefix: &str, owner: &str, source: &str, functions: usize, arity: usize, counts: Vec<u64>) -> Shape {
        let parameters = arguments(arity);
        let spans = counts[functions - 1] as usize;
        // The function at the file: span `j` where the code takes its
        // address, its length and the words as they are passed.
        let at_file: Vec<String> = parameters.iter().enumerate()
            .map(|(i, a)| if i < 2 * spans && i % 2 == 0 { format!("now.span({})", i / 2) } else { a.clone() }).collect();
        let answer = format!("{source}({})", at_file.join(", "));
        let mut definitions = format!("import {owner};\nimport runtime;\nimport rt;\n");
        for name in LENT_IMPORTS { definitions.push_str(&format!("import {name};\n")); }
        definitions.push_str(&format!("\n// The program `runtime fn {source}` published, callees first: function `k` the one with `k` after it.
fn {prefix}_program() → List<Function> {{ {source}::program }}

// How many buffers each function is lent, by function: the table the
// functions are emitted and called under.
fn {prefix}_counts() → List<Nat> {{ [{}] }}
", counts.iter().map(|c| c.to_string()).collect::<Vec<_>>().join(", ")));
        for k in 0..functions {
            definitions.push_str(&format!("fn {prefix}_first_{k}() → List<Function> {{ {prefix}_program().drop({}) }}
fn {prefix}_fn{k}() → Function {{ match {prefix}_first_{k}() {{ Nil => Setup::code_of(None), Cons(function, _) => function }} }}
", functions - 1 - k));
        }
        let typed = typed(&parameters);
        // Both programs store into no buffer: the source's evaluation is
        // then what it does over the file, and the lowered one needs
        // nothing lent to write.
        let optimize = optimizing();
        let quiet = if optimize { format!("{}\n\n{}", quiet_text(prefix, functions), quiet_text(&lowered_stem(prefix, true), functions)) }
            else { quiet_text(prefix, functions) };
        let agreement = format!("{evaluable}

{quiet}

// Over any file, the program's function {f} evaluates to the source function
// at the file's spans: the generator's theorem, from each function's
// `Compile` instance.
theorem {prefix}_agrees(now: Buffers(), {typed}): program_eval_over(now, {prefix}_program(), {f}, [{list}]) = {answer} {{
    {source}::agrees_over(now, {list})
}}
", evaluable = evaluable_text(prefix, functions, &format!("{source}::arities")), f = functions - 1,
            list = parameters.join(", "));
        Shape { functions, root: functions - 1, arity, definitions, agreement, answer, lent: Some(counts), marks: None, tables: None, entries: Vec::new(), optimize }
    }

    /// A `runtime fn` that stores into the first span it is lent: its
    /// program's every store is into a buffer `marks` marks
    /// (`{prefix}_within`, by evaluation), and over any file whose first
    /// span is `span` it runs to the source function there
    /// (`{source}::runs_over`, the generator's theorem): the word it
    /// answers, and the span as it leaves it. The code's words are the
    /// span's address, then the function's own, its length parameter first;
    /// a span it only reads is the file's, where the code takes its address
    /// (`Setup::span_at(rest, k)` for the function's span `k + 1`).
    ///
    /// A program that calls over views of its spans is given with `tables`,
    /// a row of marks for each function, and what is evaluated of it is
    /// `{prefix}_marked` (`program_marked`): each function's stores are
    /// into buffers its own row marks, and each call over views is of a
    /// callee whose row the views meet.
    ///
    /// `over` is the function over the span the theorem is stated at: the
    /// source function itself, or for a function of a laid record the
    /// function over the span that holds the record (`{source}::bytes`).
    pub fn runtime_written(prefix: &str, owner: &str, source: &str, over: &str, functions: usize, arity: usize, counts: Vec<u64>, marks: Vec<bool>,
        tables: Option<Vec<Vec<bool>>>) -> Shape {
        let parameters = arguments(arity);
        let spans = counts[functions - 1] as usize;
        let own = (1..arity).map(|i| if i % 2 == 0 && i < 2 * spans { format!("Setup::span_at(rest, {})", i / 2 - 1) } else { parameters[i].clone() })
            .collect::<Vec<_>>().join(", ");
        let comma = if own.is_empty() { "" } else { ", " };
        let answer = format!("{over}(span{comma}{own})");
        let mut definitions = format!("import {owner};\nimport runtime;\nimport rt;\n");
        for name in LENT_IMPORTS.iter().chain(WRITTEN_IMPORTS) { definitions.push_str(&format!("import {name};\n")); }
        definitions.push_str(&format!("\n// The program `runtime fn {source}` published, callees first: function `k` the one with `k` after it.
fn {prefix}_program() → List<Function> {{ {source}::program }}

// How many buffers each function is lent, by function: the table the
// functions are emitted and called under.
fn {prefix}_counts() → List<Nat> {{ [{}] }}

// Which buffers the program stores into, by buffer: the ones its caller
// lends it to write.
fn {prefix}_marks() → List<Bool> {{ [{}] }}
", counts.iter().map(|c| c.to_string()).collect::<Vec<_>>().join(", "),
            marks.iter().map(|mark| if *mark { "True" } else { "False" }).collect::<Vec<_>>().join(", ")));
        if let Some(tables) = &tables {
            definitions.push_str(&format!("
// Which buffers each function stores into, by function and then by its own
// buffers: a callee over views numbers its views.
fn {prefix}_tables() → List<List<Bool>> {{ [{}] }}
", tables.iter().map(|row| format!("[{}]", row.iter().map(|mark| if *mark { "True" } else { "False" }).collect::<Vec<_>>().join(", ")))
                .collect::<Vec<_>>().join(", ")));
        }
        for k in 0..functions {
            definitions.push_str(&format!("fn {prefix}_first_{k}() → List<Function> {{ {prefix}_program().drop({}) }}
fn {prefix}_fn{k}() → Function {{ match {prefix}_first_{k}() {{ Nil => Setup::code_of(None), Cons(function, _) => function }} }}
", functions - 1 - k));
        }
        let typed = typed(&parameters);
        // What the program stores into is checked of the functions lowered.
        let optimize = optimizing();
        let stem = lowered_stem(prefix, optimize);
        let agreement = format!("{evaluable}

{within}

// Over any file whose first span is `span`, the program's function {f} run
// on the span's place and its words ends as the source function does at the
// span: its word, and the span as it leaves it, the rest of the file as it
// was. The generator's theorem, from each function's `CompileSpan` instance.
theorem {prefix}_runs(span: List<BitVec(8)>, rest: Buffers(), {typed}):
    program_run({prefix}_program(), Cons(span, rest), {f}, [{list}]) = FTm::end_of(rest, {answer}) {{
    {source}::runs_over(span, rest, {list})
}}
", evaluable = evaluable_text(prefix, functions, &format!("{source}::arities")),
            within = if tables.is_some() { marked_text(prefix, &stem) } else { within_text(prefix, &stem, functions) }, f = functions - 1,
            list = parameters.join(", "));
        Shape { functions, root: functions - 1, arity, definitions, agreement, answer, lent: Some(counts), marks: Some(marks), tables, entries: Vec::new(), optimize }
    }
}

/// A `runtime fn`'s [`Shape`]: how many functions its published program
/// has and how many words the function takes, read off the published
/// values; for one over spans, how many buffers each function of the
/// program is lent as well, and for one that stores into them, which of
/// the root's buffers the program stores into.
pub(super) fn runtime_shape(elab: &Elaborator, prefix: &str, owner: &str, source: &str, spans: Spans) -> Result<Shape, String> {
    let probe = format!("{prefix}_shape");
    let lent = spans != Spans::None;
    // The rows' search is in a writer's scope: `runtime_file`, which every
    // module with a `runtime fn` over a span it writes imports, imports it.
    let (imports, counts) = match spans {
        Spans::None => ("", "[]".to_string()),
        Spans::Read => ("import function_ir_lower_calls;\nimport function_ir_writes;\n", format!("program_counts({source}::program)")),
        Spans::Written => ("import function_ir_lower_calls;\nimport function_ir_writes;\nimport function_ir_rows;\n",
            format!("program_counts({source}::program)")),
    };
    // A writer's marks follow its counts: a one for a buffer some function
    // of the program stores into.
    // Then whether the program calls over views, and where it does, the rows
    // of marks it links under (`program_rows`, a search whose answer the
    // certificate checks), each function's padded to the buffers it is lent.
    let marks = if spans == Spans::Written {
        format!(" ++ (program_marks({source}::program, 0, lent_count(program_counts({source}::program), {source}::program.len() - 1)) ++
        match program_lendless({source}::program) {{
            True => [0],
            False => Cons(1, {prefix}_rows(program_rows({source}::program), program_counts({source}::program), 0, {source}::program.len())),
        }})")
    } else { String::new() };
    let rows = if spans == Spans::Written {
        format!("fn {prefix}_row(row: List<Bool>, at, count: Nat) → List<Nat> {{
    match count {{ Zero => [], Succ(k) => Cons(match marked(row, at) {{ True => 1, False => 0 }}, {prefix}_row(row, Succ(at), k)) }}
}}
fn {prefix}_rows(rows: List<List<Bool>>, counts: List<Nat>, f, functions: Nat) → List<Nat> {{
    match functions {{ Zero => [], Succ(k) => {prefix}_row(marks_row(rows, f), 0, lent_count(counts, f)) ++ {prefix}_rows(rows, counts, Succ(f), k) }}
}}\n")
    } else { String::new() };
    let text = format!("import {owner};\nimport runtime;\nimport rt;\nimport list;\nimport function_ir;\n{imports}
{rows}fn {prefix}_shape() → List<Nat> {{ Cons({source}::program.len(), Cons({source}::rt.params.len(), {counts}{marks})) }}\n");
    let mut fork = elab.fork();
    fork.elab_module_source(&probe, &text).map_err(|e| e.render(&text))?;
    let numbers = function_ir_source::evaluate_numbers(&fork, &format!("{probe}::{prefix}_shape")).map_err(|e| e.to_string())?;
    match numbers[..] {
        [_, arity, ..] if arity > 8 => Err(format!("`{source}` takes {arity} words{}: compile-x86 passes at most eight, six in registers and two on the stack",
            if lent { ", an address and a length for each span among them" } else { "" })),
        [functions, arity] if functions >= 1 && !lent => Ok(Shape::runtime(prefix, owner, source, functions as usize, arity as usize)),
        [functions, arity, ref counts @ ..] if functions >= 1 && spans == Spans::Read && counts.len() == functions as usize =>
            Ok(Shape::runtime_lent(prefix, owner, source, functions as usize, arity as usize, counts.to_vec())),
        [functions, arity, ref rest @ ..] if functions >= 1 && spans == Spans::Written && rest.len() > functions as usize => {
            let (counts, after) = rest.split_at(functions as usize);
            // The generator states a writer's run over a file whose first
            // span is the function's (`f::runs_over`) and whose other spans
            // it leaves: the written span is lent first, and the spans
            // after it are only read.
            let spans = counts[functions as usize - 1];
            if (after.len() as u64) < spans + 1 { return Err(format!("`{source}::program` did not read back")); }
            let (marks, lends) = after.split_at(spans as usize);
            // A program that calls over views has a row for each function,
            // and the root's row is what its caller lends to write.
            let tables = match lends {
                [0] => None,
                [1, rows @ ..] if rows.len() as u64 == counts.iter().sum::<u64>() => {
                    let mut at = 0;
                    Some(counts.iter().map(|count| {
                        let row = rows[at..at + *count as usize].iter().map(|mark| *mark != 0).collect::<Vec<bool>>();
                        at += *count as usize;
                        row
                    }).collect::<Vec<_>>())
                }
                _ => return Err(format!("`{source}::program` did not read back")),
            };
            let marks: Vec<bool> = match &tables {
                Some(tables) => tables[functions as usize - 1].clone(),
                None => marks.iter().map(|mark| *mark != 0).collect(),
            };
            if spans < 1 || arity < 2 * spans || !marks[0] || marks[1..].iter().any(|mark| *mark) {
                return Err(format!("`{source}` stores into its span and its program is lent {spans} buffers, marked {marks:?}: compile-x86 exports a \
                    writer of its first span, which may read the spans after it"));
            }
            // A function of a laid record is compiled as the function
            // over the span that holds the record, which its generator
            // publishes beside the record-level theorem.
            let over = if elab.qualified_global(&format!("{source}::runs_held")).is_some() { format!("{source}::bytes") } else { source.to_string() };
            Ok(Shape::runtime_written(prefix, owner, source, &over, functions as usize, arity as usize, counts.to_vec(), marks, tables))
        }
        _ => Err(format!("`{source}::program` did not read back")),
    }
}

/// The program's other functions to export, `wanted` (each a module and a
/// function in it), found in the program `source`'s generator published and
/// added to `shape` with their agreements: the program's function there
/// evaluates to the Heather function, which is the generator's theorem
/// about every function of the program (`{source}::sourced`) read at that
/// one. Where a function is comes from the names the generator published
/// (`{source}::names`), and a name is only where to look: the agreement is
/// what the kernel checks, so a function found in the wrong place is a
/// refused certificate, never an export of something else.
///
/// What is taken for now, each of the others refused by name
/// (issues/linked-program-entries-limits.md): a program that stores into
/// no span, and of it the functions lent none, which are functions of
/// words whatever the root is lent.
pub(super) fn runtime_entries(elab: &Elaborator, prefix: &str, owner: &str, source: &str, shape: &mut Shape, wanted: &[(String, String)]) -> Result<(), String> {
    if wanted.is_empty() { return Ok(()); }
    if shape.marks.is_some() {
        return Err(format!("`{source}` stores into its span: compile-x86 exports another function of a program only where the program \
            stores into no span (issues/linked-program-entries-limits.md)"));
    }
    let probe = format!("{prefix}_entries");
    let text = format!("import {owner};\nimport runtime;\nimport list;\n
fn {prefix}_names() → List<Nat> {{ {source}::names }}
fn {prefix}_taken() → List<Nat> {{ {source}::arities }}\n");
    let mut fork = elab.fork();
    fork.elab_module_source(&probe, &text).map_err(|e| e.render(&text))?;
    let read = |item: &str| function_ir_source::evaluate_numbers(&fork, &format!("{probe}::{prefix}_{item}")).map_err(|e| e.to_string());
    // Each function's name, a zero after it, the first function's first;
    // and how many words each takes, the last function's first.
    let codes = read("names")?;
    let names: Vec<String> = codes.split(|code| *code == 0).take(shape.functions)
        .map(|name| name.iter().filter_map(|code| u32::try_from(*code).ok().and_then(char::from_u32)).collect()).collect();
    let taken = read("taken")?;
    if names.len() != shape.functions || taken.len() != shape.functions || codes.last() != Some(&0) {
        return Err(format!("`{source}::names` did not read back"));
    }
    let mut imports = String::new();
    for (module, function) in wanted {
        let named = format!("{module}::{function}");
        let found: Vec<usize> = names.iter().enumerate().filter(|(_, name)| *name == function).map(|(index, _)| index).collect();
        let index = match found[..] {
            [index] => index,
            [] => return Err(format!("`{named}` is no function of `{source}`'s program, which has: {}", names.join(", "))),
            _ => return Err(format!("`{function}` names {} functions of `{source}`'s program: an entry is found by its name", found.len())),
        };
        if index == shape.root { return Err(format!("`{named}` is the program's own function: an entry is another of its functions")); }
        if shape.entries.iter().any(|entry| entry.index == index || entry.symbol == *function) {
            return Err(format!("`{named}` is an entry twice"));
        }
        if let Some(spans) = shape.lent.as_ref().map(|counts| counts[index]).filter(|spans| *spans != 0) {
            return Err(format!("`{named}` is lent {spans} span{}: compile-x86 exports another function of a program only where it is a \
                function of words (issues/linked-program-entries-limits.md)", if spans == 1 { "" } else { "s" }));
        }
        let arity = taken[shape.functions - 1 - index] as usize;
        if arity > 8 { return Err(format!("`{named}` takes {arity} words: compile-x86 passes at most eight, six in registers and two on the stack")); }
        let parameters = arguments(arity);
        let list = parameters.join(", ");
        // A program lent nothing is evaluated at no file, which is
        // `program_eval`; one that is lent spans, at the empty file here:
        // the function is lent none of them.
        let evaluated = if shape.lent.is_some() { format!("program_eval_over(Nil, {prefix}_program(), {index}, [{list}])") }
            else { format!("program_eval({prefix}_program(), {index}, [{list}])") };
        shape.agreement.push_str(&format!("
// The program's function {index} evaluates to `{named}`: the generator's
// theorem about every function of the program, read at this one.
theorem {function}_native_agrees({typed}): {evaluated} = {named}({list}) {{
    program_linked_files_sources({prefix}_program(), {source}::arities, link_sources_at({source}::sources), {source}::sourced, Nil, {index},
        [{list}], trivial)
}}
", typed = typed(&parameters)));
        let imported = |text: &str| text.lines().any(|line| line.strip_prefix("import ").and_then(|rest| rest.strip_suffix(';')) == Some(module.as_str()));
        if !IMPORTS.contains(&module.as_str()) && !imported(&shape.definitions) && !imported(&imports) {
            imports.push_str(&format!("import {module};\n"));
        }
        shape.entries.push(Entry { symbol: function.clone(), source: named, index, arity });
    }
    shape.definitions.insert_str(0, &imports);
    Ok(())
}

/// What the optimizer needs besides: its stage, the plans' types, and the
/// search.
const OPTIMIZE_IMPORTS: &[&str] = &["function_ir_stage", "function_ir_inline", "function_ir_replay", "function_ir_rules", "function_ir_tidy",
    "function_ir_guard", "function_ir_learn", "function_ir_prune", "function_ir_optimize", "pair"];

/// The stage a search's answer is a plan of, in the order
/// `optimize_stage()` composes them (`function_ir_optimize`): a test at the
/// function's entry, and then moves, each an inlining or a replay, as
/// often as a search found use for one (reading through copies and
/// repeats, dropping what nothing reads, deciding tests and writing
/// narrowings as moves).
#[derive(Clone, Copy, PartialEq)]
enum Stage {
    Guard,
    Inline,
    Replay,
}

/// A search that changed a function: the stage its plan is of, the plan,
/// the function made as source, and the name the reads know that function
/// by.
#[derive(Clone)]
struct Staged {
    stage: Stage,
    plan: String,
    function: String,
    name: String,
}

/// What the optimizer made of a program: the definitions `{prefix}_opt_…`
/// (each function, the plans that make it, the lists) and `{prefix}_cut_…`
/// (the same with the functions nothing reaches emptied), which the reads
/// and the certificate both take, and the statements that the stage and
/// the emptying make them of the program, which are the certificate's
/// alone.
struct Optimized {
    definitions: String,
    statements: String,
    /// Each function's placement where the optimizer kept a function the
    /// lowering was asked about with it and the function is reached (it is
    /// then the function the code is lowered from); `None` where the
    /// planner is still to be read.
    placements: Vec<Option<Vec<u64>>>,
}

/// The text of a spelling (`lib/native/function_ir/function_ir_spelled.hthr`):
/// a number is an ASCII character's code, or the mark and after it a number
/// written here in decimal. `None` for anything else.
fn spelled_text(spelling: &[u64]) -> Option<String> {
    const MARK: u64 = 256;
    let mut text = String::with_capacity(spelling.len() * 2);
    let mut numbers = spelling.iter();
    while let Some(&n) = numbers.next() {
        match n {
            MARK => text.push_str(&numbers.next()?.to_string()),
            10 | 32..=126 => text.push(n as u8 as char),
            _ => return None,
        }
    }
    Some(text)
}

/// The optimizer over a program that is lent spans
/// (`function_ir_optimize`, docs/native/optimizer-design.md §9): a function at a
/// time, callees first, each over its callees as the stages left them, and
/// a search at a time, each over the function the searches before it
/// made. A search is an evaluation and proves nothing: it answers a
/// plan and the function its stage makes of it, both as source, which are
/// stated here as literals, and the certificate's statement that the stage
/// makes the one from the other is the kernel's to check, a plan of a
/// function a statement; `Stage::many_made` joins those after the test
/// (the moves: an inlining or a replay each) and `optimize_made` makes
/// them the statement `Stage::run_next` takes. A search that has nothing,
/// or answers the function it was given, adds no plan and keeps the
/// function.
///
/// A function is first inlined and tidied with no test, which is where the
/// search sees what a test of its spans' lengths would decide. Where there
/// is such a test, the function is made again with the test first: the arm
/// for a span too short is the function as written, and the searches work
/// in the other arm alone (those named `…_past`). After inlining, a
/// function reads through its copies and repeats before its tests are
/// decided, since that is what makes a word the test computed and the
/// body's own computation of it one id; and once more after, since what
/// is decided writes moves of its own (a narrowing of a value already in
/// range).
///
/// Last, where bytes of a span are joined into a word, a load of the word
/// is put beside them and the join found a move of it (`find_worded`); the
/// byte loads then go with the sweep. And where a word's bytes are stored
/// one at a time at an index and the next three, the word's load is put
/// after the stores (`find_stores`) and a replay pays the four as one
/// store in its place (`find_paid`).
///
/// What the stages made is kept where it is within the search's room
/// (`Function::fits`) and the lowering takes it with the planner's
/// placement (`Function::lowers`, a read of its own: a search and the
/// planner each hold what they evaluate): the function under its test,
/// else the one with no test and its own tests decided, else the one
/// inlined and tidied alone, else the function as it is.
///
/// Then the functions `roots` (the exported ones) no longer reach are
/// emptied (`prune`): inlined everywhere, a small function is called by
/// nothing, and its code would be emitted all the same. The certificate
/// states the list of the functions reached as a literal, and that the
/// program is closed under it (`program_closed`), by evaluation.
/// How many groups of four byte stores a function has written as one store
/// each, a group a round.
const STORES_MOST: usize = 8;

fn optimize(elab: &Elaborator, answers: &Answers, prefix: &str, probe: &str, imports: &str, definitions: &str, m: usize, roots: &[usize]) -> Result<Optimized, String> {
    let mut fork = Reading::new(elab, answers);
    let source = format!("{probe}_opt_source");
    fork.define(&source, definitions);
    let read = |fork: &mut Reading, module: &str, item: &str|
        fork.read(&format!("{module}::{prefix}_opt_{item}")).map_err(|e| format!("`{prefix}_opt_{item}`: {e}"));
    let uses = |modules: &[String]| modules.iter().map(|name| format!("import {name};\n")).collect::<String>();
    // Whether the lowering takes a function with the planner's placement
    // (`Function::lowers`), and the placement where it does: the program's
    // planning of a function the optimizer keeps is this one, so the
    // compile reads it once (issues/compile-x86-address-space-margin.md).
    let placed = format!("{probe}_opt_placed");
    fork.define(&placed, &format!("{imports}import {source};
fn {prefix}_opt_placed(function: Function, k: Nat, places: List<Place>) → List<Nat> {{
    match function.emit_lent(Start, k, places, {prefix}_counts().len(), {prefix}_counts()) {{
        None => [0],
        Some(_) => Cons(1, places.map(λ (place: Place) => place.number())),
    }}
}}
"));
    let mut modules = vec![source, placed];
    let (mut stated, mut statements) = (String::new(), String::new());
    let mut placements = Vec::with_capacity(m);
    for k in 0..m {
        let below = |stem: &str| if k == 0 { "Nil".to_string() } else { format!("{prefix}_{stem}_{}()", k - 1) };
        let earlier = below("opt_first");
        let original = format!("{prefix}_fn{k}()");
        // A yes or no of the function an expression names, read.
        let asks = |fork: &mut Reading, modules: &[String], item: &str, question: &str| -> Result<bool, String> {
            let module = format!("{probe}_opt_{item}");
            let text = format!("{imports}{}
fn {prefix}_opt_{item}() → List<Nat> {{ match {question} {{ True => [1], False => [0] }} }}
", uses(modules));
            fork.define(&module, &text);
            Ok(read(fork, &module, item)? == [1])
        };
        // The stages `searches` name, in turn from the function `from`: each
        // search is asked of the function the one before it made, and what
        // it makes, where that is another function, is defined under a name
        // of its own, `{prefix}_opt_fn{k}_{tag}{stage}`.
        let run = |fork: &mut Reading, modules: &mut Vec<String>, tag: &str, from: &str, mut before: Option<String>, searches: &[(Stage, String)]|
            -> Result<Vec<Staged>, String> {
            let mut made: Vec<Staged> = Vec::new();
            for (at, (stage, search)) in searches.iter().enumerate() {
                let current = made.last().map_or(from.to_string(), |last| format!("{}()", last.name));
                let item = format!("found_{k}_{tag}{at}");
                let find = format!("{probe}_opt_{item}");
                let text = format!("{imports}{}
fn {prefix}_opt_{item}() → List<Nat> {{ found_spelled({current}.{search}) }}
", uses(modules));
                fork.define(&find, &text);
                let unread = || format!("function {k}'s `{search}` did not read back");
                let found = spelled_text(&read(fork, &find, &item)?).ok_or_else(unread)?;
                if found == "None" { continue; }
                let (plan, function) = match found.split_once('\n') {
                    Some((plan, function)) if function.starts_with("Function(") && !function.contains('\n') => (plan, function),
                    _ => return Err(unread()),
                };
                if before.as_deref() == Some(function) { continue; }
                let name = format!("{prefix}_opt_fn{k}_{tag}{at}");
                let module = format!("{probe}_opt_made_{k}_{tag}{at}");
                let text = format!("{imports}{}
fn {name}() → Function {{
    {function}
}}
", uses(modules));
                fork.define(&module, &text);
                modules.push(module);
                before = Some(function.to_string());
                made.push(Staged { stage: *stage, plan: plan.to_string(), function: function.to_string(), name });
            }
            Ok(made)
        };
        let named = |made: &[Staged]| made.last().map_or(original.clone(), |last| format!("{}()", last.name));
        let fits = |fork: &mut Reading, modules: &[String], made: &[Staged], item: &str|
            asks(fork, modules, &format!("fits_{item}{k}"), &format!("{}.fits(Wanted::usual())", named(made)));
        let lowers = |fork: &mut Reading, modules: &[String], made: &[Staged], item: &str| -> Result<Option<Vec<u64>>, String> {
            let item = format!("taken_{item}{k}");
            let module = format!("{probe}_opt_{item}");
            let function = named(made);
            let text = format!("{imports}{}
fn {prefix}_opt_{item}() → List<Nat> {{ {prefix}_opt_placed({function}, {k}, {function}.plan()) }}
", uses(modules));
            fork.define(&module, &text);
            match read(fork, &module, &item)?.split_first() {
                Some((0, [])) => Ok(None),
                Some((1, places)) => Ok(Some(places.to_vec())),
                _ => Err(format!("`{prefix}_opt_{item}` did not read back")),
            }
        };
        // The placement of the function kept, where the lowering was asked.
        let mut placement = None;
        let wanted = format!("{earlier}, Wanted::usual()");
        let replay = |search: &str| (Stage::Replay, search.to_string());
        // With no test: inlined and tidied, within the search's room or
        // not at all.
        let mut tidied = run(&mut fork, &mut modules, "t", &original, None,
            &[(Stage::Inline, format!("find_inlined({wanted})")), replay("find_copied()"), replay("find_swept()")])?;
        if !tidied.is_empty() && !fits(&mut fork, &modules, &tidied, "")? { tidied.clear(); }
        // Under the test that function asks for, where it asks for one: the
        // test is put on the function as written.
        let mut made: Vec<Staged> = Vec::new();
        let mut tested = run(&mut fork, &mut modules, "g", &named(&tidied), None, &[(Stage::Guard, format!("find_guarded({original}, Wanted::usual())"))])?;
        if !tested.is_empty() {
            let last = tested[0].function.clone();
            tested.extend(run(&mut fork, &mut modules, "p", &named(&tested), Some(last),
                &[(Stage::Inline, format!("find_inlined_past({wanted})")), replay("find_copied_past()"), replay("find_swept_past()"),
                    replay("find_learned_past()"), replay("find_copied_past()"), replay("find_swept_past()")])?);
            if fits(&mut fork, &modules, &tested, "tested_")? && let Some(places) = lowers(&mut fork, &modules, &tested, "tested_")? {
                made = tested;
                placement = Some(places);
            }
        }
        // With no test: what the function's own tests and ranges decide,
        // of the function tidied; or that function.
        if made.is_empty() {
            let mut learned = tidied.clone();
            learned.extend(run(&mut fork, &mut modules, "l", &named(&tidied), tidied.last().map(|last| last.function.clone()),
                &[replay("find_learned()")])?);
            if learned.len() > tidied.len() {
                let last = learned.last().map(|last| last.function.clone());
                learned.extend(run(&mut fork, &mut modules, "m", &named(&learned), last, &[replay("find_copied()"), replay("find_swept()")])?);
                if let Some(places) = lowers(&mut fork, &modules, &learned, "learned_")? {
                    made = learned;
                    placement = Some(places);
                }
            }
            if made.is_empty() && !tidied.is_empty() && let Some(places) = lowers(&mut fork, &modules, &tidied, "")? {
                made = tidied;
                placement = Some(places);
            }
        }
        // Bytes joined into a word, read as one load: the load is put
        // after the last of the byte loads, the walk finds the join a
        // move of its word, the byte loads are swept, and a last walk
        // drops the tests no access reads any more. Kept where the
        // lowering takes it, which asks that the load's span is tested.
        {
            let past = if made.iter().any(|staged| staged.stage == Stage::Guard) { "_past" } else { "" };
            let last = made.last().map(|last| last.function.clone());
            let put = run(&mut fork, &mut modules, "w", &named(&made), last, &[(Stage::Inline, format!("find_worded{past}({earlier})"))])?;
            if !put.is_empty() {
                let mut worded = made.clone();
                worded.extend(put);
                let last = worded.last().map(|last| last.function.clone());
                worded.extend(run(&mut fork, &mut modules, "x", &named(&worded), last,
                    &[replay(&format!("find_learned{past}()")), replay(&format!("find_copied{past}()")), replay(&format!("find_swept{past}()")),
                        replay(&format!("find_learned{past}()")), replay(&format!("find_swept{past}()"))])?);
                if let Some(places) = lowers(&mut fork, &modules, &worded, "worded_")? {
                    made = worded;
                    placement = Some(places);
                }
            }
        }
        // A word stored a byte at a time, written as one store: the word's
        // half, swap and a load of four bytes at the first index are put
        // after the fourth store, and the replay holds the four stores back
        // and pays them as one store in the load's place; a group at a time,
        // as long as one is found (`stores_most`). Then the walks drop the
        // shifts, narrowings and tests no access reads any more. Kept where
        // the lowering takes it.
        {
            let past = if made.iter().any(|staged| staged.stage == Stage::Guard) { "_past" } else { "" };
            let mut stored = made.clone();
            for round in 0..STORES_MOST {
                let last = stored.last().map(|last| last.function.clone());
                let put = run(&mut fork, &mut modules, &format!("s{round}_"), &named(&stored), last, &[(Stage::Inline, format!("find_stores{past}({earlier})"))])?;
                if put.is_empty() { break; }
                let mut tried = stored.clone();
                tried.extend(put);
                let last = tried.last().map(|last| last.function.clone());
                let paid = run(&mut fork, &mut modules, &format!("y{round}_"), &named(&tried), last, &[replay(&format!("find_paid{past}()"))])?;
                if paid.is_empty() { break; }
                tried.extend(paid);
                stored = tried;
            }
            if stored.len() > made.len() {
                let last = stored.last().map(|last| last.function.clone());
                stored.extend(run(&mut fork, &mut modules, "z", &named(&stored), last,
                    &[replay(&format!("find_swept{past}()")), replay(&format!("find_learned{past}()")), replay(&format!("find_copied{past}()")),
                        replay(&format!("find_swept{past}()"))])?);
                if let Some(places) = lowers(&mut fork, &modules, &stored, "stored_")? {
                    made = stored;
                    placement = Some(places);
                }
            }
        }
        placements.push(placement);
        // The function after the test and after each move, by name.
        let tested_name = made.iter().find(|staged| staged.stage == Stage::Guard).map_or(original.clone(), |staged| format!("{}()", staged.name));
        let moves: Vec<&Staged> = made.iter().filter(|staged| staged.stage != Stage::Guard).collect();
        let last_made = moves.last().map_or(tested_name.clone(), |staged| format!("{}()", staged.name));
        let lists = format!("fn {prefix}_opt_first_{k}() → List<Function> {{ Cons({prefix}_opt_fn{k}(), {earlier}) }}\n");
        let next = format!("{probe}_opt_{k}");
        let text = format!("{imports}{}
fn {prefix}_opt_fn{k}() → Function {{ {last_made} }}
{lists}", uses(&modules));
        fork.define(&next, &text);
        modules.push(next);
        let plans_before = below("opt_plans");
        if made.is_empty() {
            stated.push_str(&format!("
// Function {k} as the optimizer left it: as it is, with no plan.
fn {prefix}_opt_plan_{k}() → Passes() {{ no_passes() }}
fn {prefix}_opt_fn{k}() → Function {{ {original} }}
{lists}fn {prefix}_opt_plans_{k}() → List<Passes()> {{ Cons({prefix}_opt_plan_{k}(), {plans_before}) }}
"));
            statements.push_str(&format!("
theorem {prefix}_opt_made_{k}(): optimize_stage().rewrite({earlier}, {original}, {prefix}_opt_plan_{k}()) = Some({prefix}_opt_fn{k}()) {{
    refl
}}
"));
        } else {
            stated.push_str(&format!("\n// Function {k} after each plan that changed it, the plans, and the function as the optimizer left it.\n"));
            let found = made.iter().find(|staged| staged.stage == Stage::Guard);
            stated.push_str(&format!("fn {prefix}_opt_plan_{k}_g() → Option<Guard> {{{}}}\n",
                found.map_or(" None ".to_string(), |staged| format!("\n    Some({})\n", staged.plan))));
            if let Some(staged) = found {
                stated.push_str(&format!("fn {}() → Function {{\n    {}\n}}\n", staged.name, staged.function));
            }
            statements.push_str(&format!("
theorem {prefix}_opt_made_{k}_g(): guard_stage().maybe().rewrite({earlier}, {original}, {prefix}_opt_plan_{k}_g()) = Some({tested_name}) {{
    refl
}}
"));
            // The moves, each its own statement, joined from the last:
            // `{prefix}_opt_moves_{k}_{i}` is the moves from the `i`th on,
            // and `{prefix}_opt_joined_{k}_{i}` that they make the last
            // function of the one the `i`th was given.
            let count = moves.len();
            let given = |i: usize| if i == 0 { tested_name.clone() } else { format!("{}()", moves[i - 1].name) };
            let rest = |i: usize| if i == count { "Nil".to_string() } else { format!("{prefix}_opt_moves_{k}_{i}()") };
            for (i, staged) in moves.iter().enumerate() {
                let side = if staged.stage == Stage::Inline { "Inl" } else { "Inr" };
                stated.push_str(&format!("fn {prefix}_opt_plan_{k}_m{i}() → Or<Inlines, Plan> {{\n    {side}({})\n}}\nfn {}() → Function {{\n    {}\n}}\n",
                    staged.plan, staged.name, staged.function));
                statements.push_str(&format!("
theorem {prefix}_opt_made_{k}_m{i}(): move_stage().rewrite({earlier}, {}, {prefix}_opt_plan_{k}_m{i}()) = Some({}) {{
    refl
}}
", given(i), given(i + 1)));
            }
            for i in (0..count).rev() {
                stated.push_str(&format!("fn {prefix}_opt_moves_{k}_{i}() → List<Or<Inlines, Plan>> {{ Cons({prefix}_opt_plan_{k}_m{i}(), {}) }}\n", rest(i + 1)));
                let later = if i + 1 == count { format!("move_stage().many_none({earlier}, {last_made})") } else { format!("{prefix}_opt_joined_{k}_{}()", i + 1) };
                statements.push_str(&format!("
theorem {prefix}_opt_joined_{k}_{i}(): move_stage().many().rewrite({earlier}, {}, {prefix}_opt_moves_{k}_{i}()) = Some({last_made}) {{
    move_stage().many_made({earlier}, {}, {}, {last_made}, {prefix}_opt_plan_{k}_m{i}(), {}, {prefix}_opt_made_{k}_m{i}(), {later})
}}
", given(i), given(i), given(i + 1), rest(i + 1)));
            }
            let joined = if count == 0 { format!("move_stage().many_none({earlier}, {last_made})") } else { format!("{prefix}_opt_joined_{k}_0()") };
            stated.push_str(&format!("fn {prefix}_opt_plan_{k}() → Passes() {{ passes({prefix}_opt_plan_{k}_g(), {}) }}
fn {prefix}_opt_fn{k}() → Function {{ {last_made} }}
{lists}fn {prefix}_opt_plans_{k}() → List<Passes()> {{ Cons({prefix}_opt_plan_{k}(), {plans_before}) }}
", rest(0)));
            statements.push_str(&format!("
theorem {prefix}_opt_made_{k}(): optimize_stage().rewrite({earlier}, {original}, {prefix}_opt_plan_{k}()) = Some({prefix}_opt_fn{k}()) {{
    optimize_made({earlier}, {original}, {tested_name}, {last_made}, {prefix}_opt_plan_{k}_g(), {},
        {prefix}_opt_made_{k}_g(), {joined})
}}
", rest(0)));
        }
        statements.push_str(&format!("
theorem {prefix}_opt_ran_{k}(): optimize_stage().run({prefix}_first_{k}(), {prefix}_opt_plans_{k}()) = Some({prefix}_opt_first_{k}()) {{
    optimize_stage().run_next({prefix}_fn{k}(), {}, {prefix}_opt_plan_{k}(), {}, {prefix}_opt_fn{k}(), {earlier},
        {}, {prefix}_opt_made_{k}())
}}
", below("first"), plans_before, if k == 0 { "refl".to_string() } else { format!("{prefix}_opt_ran_{}()", k - 1) }));
    }
    let last = m - 1;
    let reach = format!("{probe}_opt_reach");
    let text = format!("{imports}{}
fn {prefix}_opt_reached() → List<Nat> {{ program_reached({prefix}_opt_first_{last}(), [{}]) }}
", uses(&modules), roots.iter().map(|root| root.to_string()).collect::<Vec<_>>().join(", "));
    fork.define(&reach, &text);
    // The walk lists a function once for each call it finds; the certificate
    // states each once, in order.
    let mut reached = read(&mut fork, &reach, "reached")?;
    reached.sort_unstable();
    reached.dedup();
    stated.push_str(&format!("
// `{prefix}_program()` as the optimizer's stage left it, and the functions
// the exported ones reach in it.
fn {prefix}_opt_program() → List<Function> {{ {prefix}_opt_first_{last}() }}
fn {prefix}_opt_live() → List<Nat> {{ [{}] }}

// The program the code is lowered from: a function nothing reaches is
// emptied, and keeps its number.
", reached.iter().map(|n| n.to_string()).collect::<Vec<_>>().join(", ")));
    for k in 0..m {
        let earlier = if k == 0 { "Nil".to_string() } else { format!("{prefix}_cut_first_{}()", k - 1) };
        let emptied = if reached.contains(&(k as u64)) { "" } else { ".emptied()" };
        stated.push_str(&format!("fn {prefix}_cut_fn{k}() → Function {{ {prefix}_opt_fn{k}(){emptied} }}
fn {prefix}_cut_first_{k}() → List<Function> {{ Cons({prefix}_cut_fn{k}(), {earlier}) }}
"));
    }
    stated.push_str(&format!("fn {prefix}_cut_program() → List<Function> {{ {prefix}_cut_first_{last}() }}\n"));
    statements.push_str(&format!("
// The program made does at each function whatever the program does: the
// stage's theorem, at the plans above.
theorem {prefix}_opt_keeps(f: Nat): ProgramRewrites({prefix}_program(), {prefix}_opt_program(), f) {{
    optimize_stage().run_rewrites({prefix}_program(), {prefix}_opt_plans_{last}(), {prefix}_opt_program(), {prefix}_opt_ran_{last}(), f)
}}

theorem {prefix}_cut_made(): prune({prefix}_opt_program(), λ (n: Nat) => n.among({prefix}_opt_live())) = {prefix}_cut_program() {{ refl }}

// Every function reached calls only functions reached.
theorem {prefix}_cut_closed(): program_closed({prefix}_opt_program(), λ (n: Nat) => n.among({prefix}_opt_live())) = True {{ refl }}

// So the program the code is lowered from does at a function reached
// whatever the program does.
theorem {prefix}_cut_keeps(f: Nat, alive: f.among({prefix}_opt_live()) = True): ProgramRewrites({prefix}_program(), {prefix}_cut_program(), f) {{
    ProgramRewrites::then({prefix}_program(), {prefix}_opt_program(), {prefix}_cut_program(), f, {prefix}_opt_keeps(f),
        j({prefix}_cut_made(), λ made _ => ProgramRewrites({prefix}_opt_program(), made, f),
            prune_rewrites(λ (n: Nat) => n.among({prefix}_opt_live()), {prefix}_opt_program(), {prefix}_cut_closed(), f, alive)))
}}
"));
    for (k, placement) in placements.iter_mut().enumerate() {
        if !reached.contains(&(k as u64)) { *placement = None; }
    }
    Ok(Optimized { definitions: stated, statements, placements })
}

pub(super) fn compile(elab: &Elaborator, answers: &Answers, prefix: &str, module: &str, program: &Shape) -> Result<Compiled, String> {
    let f = program.root;
    let mut imports = String::new();
    for name in IMPORTS { imports.push_str(&format!("import {name};\n")); }
    if program.optimize { for name in OPTIMIZE_IMPORTS { imports.push_str(&format!("import {name};\n")); } }
    let definitions = format!("{imports}{}", program.definitions);
    let m = program.functions;
    let probe = format!("{module}_probe");
    // The optimizer first: what is planned, emitted and lowered from here on
    // is the program it made, `{prefix}_cut_…`, and the program published
    // is what the theorems are about.
    let stem = lowered_stem(prefix, program.optimize);
    let (definitions, rewriting, placed) = if program.optimize {
        let roots: Vec<usize> = std::iter::once(f).chain(program.entries.iter().map(|entry| entry.index)).collect();
        let made = optimize(elab, answers, prefix, &probe, &imports, &definitions, m, &roots)?;
        (format!("{definitions}{}", made.definitions), made.statements, made.placements)
    } else { (definitions, String::new(), vec![None; m]) };
    // A function's emission after `prog`: under the program's counts of
    // lent buffers where it has them.
    let lent = program.lent.is_some();
    let emit = |prog: &str, k: usize, places: &str, names: u64| if lent {
        format!("{stem}_fn{k}().emit_lent({prog}, {k}, {places}, {names}, {prefix}_counts(), {prefix}_rooms())")
    } else {
        format!("{stem}_fn{k}().emit({prog}, {k}, {places}, {names}, {prefix}_rooms())")
    };
    // Evaluated on a fork, which only defines: the certificate's statements
    // are the session's to check. A function at a time, each read from the
    // literals the reads before it gave: every read is an evaluation of its
    // own, so one that planned or emitted the whole program would hold all
    // of it at once, and each of them again
    // (issues/compile-x86-certificate-memory.md). The planner runs once per
    // function; a function is emitted onto the code before it as a literal.
    let mut plans = String::new();
    for k in 0..m {
        plans.push_str(&format!("fn {prefix}_plan_{k}() → List<Nat> {{ {stem}_fn{k}().plan().map(λ (place: Place) => place.number()) }}\n"));
    }
    // The last `d` items' numbers, as `Prog::numbers` writes them.
    plans.push_str(&format!("fn {prefix}_top(p: Prog, d: Nat, after: List<Nat>) → List<Nat> {{
    match d {{ Zero => after, Succ(j) => match p {{ Start => after, At(before, name, item) => {prefix}_top(before, j, Cons(name, item.numbers() ++ after)) }} }}
}}
"));
    let mut fork = Reading::new(elab, answers);
    let first = format!("{definitions}{plans}");
    fork.define(&probe, &first);
    let read = |fork: &mut Reading, module: &str, item: &str|
        fork.read(&format!("{module}::{prefix}_{item}")).map_err(|e| format!("`{prefix}_{item}`: {e}"));
    let mut placement = Vec::new();
    // What each function's placement asks it to save (`placement_saves`),
    // which its frame is sized by.
    let mut saves = Vec::new();
    for k in 0..m {
        // The optimizer's question already planned a function it kept.
        let planned = match &placed[k] { Some(places) => places.clone(), None => read(&mut fork, &probe, &format!("plan_{k}"))? };
        saves.push(match planned.first() { Some(&n) if (17..32).contains(&n) => n - 17, _ => 0 });
        for n in planned {
            placement.push(match n {
                16 => "Folded".to_string(),
                // What a call saves, a mask, and a function's count of
                // saves (`Place::number`).
                n if n >= 32 => format!("Spilling({})", n - 32),
                n if n >= 17 => format!("Saving({})", n - 17),
                n => GPRS.get(n as usize).map(|gpr| format!("Into({gpr})")).ok_or_else(|| "a malformed placement".to_string())?,
            });
        }
    }
    let rest = |left: usize| format!("[{}]", placement[placement.len() - left..].join(", "));
    // The room table the code is lowered under: each function's frame as
    // its placement sizes it, and its callees' rooms below
    // (`program_rooms_by`). The lowering checks it a function at a time
    // (`Function::roomy`); the certificate states it as a literal.
    let reading_rooms = format!("{probe}_rooms");
    let numbers = |values: &[u64]| values.iter().map(|n| n.to_string()).collect::<Vec<_>>().join(", ");
    fork.define(&reading_rooms, &format!("{imports}import {probe};
fn {prefix}_rooms_read() → List<Nat> {{ program_rooms_by({stem}_program(), λ (f: Nat) => rooms_at([{}], f)) }}
", numbers(&saves)));
    let table_rooms = read(&mut fork, &reading_rooms, "rooms_read")?;
    if table_rooms.len() != m { return Err("the program's room table did not read back".into()); }
    let room = |function: usize| table_rooms[function];
    let rooms_definition = format!("
// The stack each function asks for below its return address: its frame
// and its callees' rooms below it (`program_rooms_by`), checked by the
// lowering a function at a time (`Function::roomy`).
fn {prefix}_rooms() → Nat → Nat {{ λ (f: Nat) => rooms_at([{}], f) }}
", numbers(&table_rooms));
    // Function `k`'s code and what the placement has left after it, as the
    // certificate states them and as the next function's read starts from.
    let stated = |k: usize, items: &[(u64, String)], left: usize| {
        let mut code = if k == 0 { "Start".to_string() } else { format!("{prefix}_code_{}()", k - 1) };
        for (name, item) in items { code = format!("At({code},\n    {name}, {item})"); }
        format!("
fn {prefix}_code_{k}() → Prog {{
    {code}
}}

fn {prefix}_rest_{k}() → List<Place> {{ {} }}
", rest(left))
    };
    let mut items: Vec<(u64, String)> = Vec::new();
    // (items so far, places left, next label) after each function.
    let mut after: Vec<(usize, usize, u64)> = Vec::new();
    let rooms_module = format!("{probe}_table_rooms");
    fork.define(&rooms_module, &format!("{imports}import {probe};\n{rooms_definition}"));
    let mut modules = vec![probe.clone(), rooms_module];
    let uses = |modules: &[String]| modules.iter().map(|name| format!("import {name};\n")).collect::<String>();
    for k in 0..m {
        let (taken, left, names) = after.last().copied().unwrap_or((0, placement.len(), m as u64));
        let before = if k == 0 {
            format!("fn {prefix}_placement() → List<Place> {{ {} }}\n", rest(placement.len()))
        } else {
            stated(k - 1, &items[after.get(k.wrapping_sub(2)).map_or(0, |step| step.0)..taken], left)
        };
        let (prog, places) = if k == 0 { ("Start".to_string(), format!("{prefix}_placement()")) } else { (format!("{prefix}_code_{}()", k - 1), format!("{prefix}_rest_{}()", k - 1)) };
        let step = format!("{probe}_{k}");
        let text = format!("{imports}{}{before}
fn {prefix}_read_{k}() → List<Nat> {{
    match {emitted} {{
        None => [],
        Some(e) => Cons(prog_depth(e.prog), Cons(e.placement.len(), Cons(e.names, {prefix}_top(e.prog, prog_depth(e.prog) - {taken}, [])))),
    }}
}}
", uses(&modules), emitted = emit(&prog, k, &places, names));
        fork.define(&step, &text);
        let numbers = read(&mut fork, &step, &format!("read_{k}"))?;
        match numbers[..] {
            // Which function and where in it: the library's mirror of the
            // emitter's tests says (`function_ir_refusal`,
            // issues/function-ir-planner-register-pressure.md). Each a read
            // of its own, as every read here is.
            [] => {
                let counts = if lent { format!("{prefix}_counts()") } else { "[]".to_string() };
                let why = format!("{probe}_refusal");
                let text = format!("{imports}import function_ir_refusal;\n{}
fn {prefix}_refused() → List<Nat> {{ {stem}_fn{k}().refusal_bytes({k}, {names}, {counts}, {prefix}_rooms()) }}
fn {prefix}_shown() → List<Nat> {{ {stem}_fn{k}().shown_bytes() }}
", uses(&modules));
                let defined = fork.define_now(&why, &text).is_ok();
                let mut said = |item: &str| (if defined { read(&mut fork, &why, item).ok() } else { None })
                    .map(|bytes| String::from_utf8_lossy(&bytes.iter().map(|&b| b as u8).collect::<Vec<u8>>()).into_owned());
                let (at, nodes) = (said("refused"), said("shown"));
                return Err(format!("the verified lowering refused this program with the planner's placement: its function {k} of {m}, callees first{}{}",
                    at.map_or(String::new(), |at| format!(", at {at}")),
                    nodes.map_or(String::new(), |nodes| format!("\n  the function's nodes, values by their ids: {nodes}"))));
            },
            [count, places, names, ..] if count as usize >= taken && places as usize <= left => {
                let read = read_items(&numbers[3..])?;
                // The contract's ground for needing no stack alignment and
                // touching no state the model lacks: a function's code
                // calls only compiled code (docs/native/native-library-exports-design.md
                // §6, clauses 7 and 9). The function compiler emits no
                // system call; one would be refused here, not exported.
                if read.iter().any(|(_, item)| item == "Syscall") {
                    return Err(format!("function {k}'s code makes a system call: an exported function calls only compiled code"));
                }
                items.extend(read);
                if items.len() != count as usize { return Err(format!("function {k}'s emission did not read back")); }
                after.push((count as usize, places as usize, names));
            }
            _ => return Err(format!("function {k}'s emission did not read back")),
        }
        modules.push(step);
    }
    // The whole code as a literal, and what is read off it: each item's
    // length, and then the bytes by a table of the labels written from the
    // lengths, a window at a time (`asm_code_ending_onto`, as `write-elf`
    // reads them). `Prog::laid_out` and `assemble` find a label by walking
    // the program, quadratic in it, so neither is evaluated whole here or
    // in the certificate (issues/native-compile-linear-layout.md).
    let last = m - 1;
    let closing = format!("{probe}_code");
    let text = format!("{imports}{}{}
fn {prefix}_lens() → List<Nat> {{ asm_lens({prefix}_code_{last}()) }}
", uses(&modules), stated(last, &items[after.get(last.wrapping_sub(1)).map_or(0, |step| step.0)..], after[last].1));
    fork.define(&closing, &text);
    modules.push(closing.clone());
    let lens = read(&mut fork, &closing, "lens")?;
    if lens.len() != items.len() { return Err("the items' lengths do not cover the code".into()); }
    let offsets = super::labels::offsets(&lens);
    let length = offsets[items.len()] as usize;
    let pieces = cut_pieces(&lens, PIECE);
    // The literal is cut where a function ends and where a piece's window
    // does, so each is a definition.
    let mut cuts: BTreeSet<usize> = after.iter().map(|step| step.0).collect();
    cuts.extend(super::labels::piece_cuts(&pieces, items.len()));
    let table = super::labels::table(prefix, &items, &offsets);
    let mut windows = String::new();
    let mut earlier = 0;
    for &cut in cuts.iter().filter(|&&cut| cut > 0) {
        windows.push_str(&format!("fn {prefix}_bytes_{cut}() → List<Nat> {{ asm_code_ending_onto(no_fills(), {prefix}_table().labels(), asm_back({prefix}_code_{last}(), {}), {}, {}, Nil).map(λ (b: BitVec(8)) => b.toNat()) }}\n",
            items.len() - cut, cut - earlier, offsets[cut]));
        earlier = cut;
    }
    let reading = format!("{probe}_bytes");
    let text = format!("{imports}{}{table}{windows}", uses(&modules));
    fork.define(&reading, &text);
    let mut bytes = Vec::with_capacity(length);
    for &cut in cuts.iter().filter(|&&cut| cut > 0) {
        for b in read(&mut fork, &reading, &format!("bytes_{cut}"))? {
            bytes.push(u8::try_from(b).map_err(|_| "a byte above 255".to_string())?);
        }
        if bytes.len() as u64 != offsets[cut] { return Err("the items' lengths do not cover the code".into()); }
    }
    drop(fork);
    // Where a function starts: at its label, the one named after it.
    let starts = |function: usize| match items.iter().rposition(|(name, _)| *name == function as u64 + 1) {
        Some(at) if (offsets[at] as usize) < bytes.len() => Ok(offsets[at] as usize),
        Some(_) => Err("the entry is past the code".to_string()),
        None => Err("the exported function's label is not in the code".to_string()),
    };
    let entry = starts(f)?;
    let entries = program.entries.iter().map(|entry| starts(entry.index)).collect::<Result<Vec<_>, _>>()?;

    let agreement = &program.agreement;
    let parameters = arguments(program.arity);
    let typed = typed(&parameters);
    let list = format!("[{}]", parameters.join(", "));
    let call = &program.answer;
    let mut text = definitions;
    text.push_str(&rewriting);
    // The code is stated as the literal the lowering computes, a function at
    // a time, each function's emission its own statement from the literal
    // before it: a declaration's fuel is its own, and the lowering is most
    // of what one could spend.
    text.push_str(&format!("
// The placement the heuristic chose; the theorem holds for any.
fn {prefix}_placement() → List<Place> {{ {} }}
{rooms_definition}", rest(placement.len())));
    // The literal: `{prefix}_at_{c}` its first `c` items at each cut, and
    // each function's code the cut it ends at.
    text.push_str(&super::emission::code(prefix, &items, &cuts));
    let mut before = ("Start".to_string(), format!("{prefix}_placement()"), m as u64);
    for (k, &(count, left, names)) in after.iter().enumerate() {
        text.push_str(&format!("
fn {prefix}_code_{k}() → Prog {{ {prefix}_at_{count}() }}

fn {prefix}_rest_{k}() → List<Place> {{ {} }}
", rest(left)));
        let earlier = if k == 0 { "Nil".to_string() } else { format!("{stem}_first_{}()", k - 1) };
        let (started, functions, next) = if lent {
            (if k == 0 { format!("emit_functions_lent_start({prefix}_placement(), {m}, {prefix}_counts(), {prefix}_rooms())") } else { format!("{prefix}_emitted_{}()", k - 1) },
                format!("emit_functions_after_lent(Start, {stem}_first_{k}(), {prefix}_placement(), {m}, {prefix}_counts(), {prefix}_rooms())"),
                format!("emit_functions_lent_next({stem}_fn{k}(), {earlier}, {prefix}_placement(), {m}, {prefix}_counts(), {prefix}_rooms(), "))
        } else {
            (if k == 0 { format!("emit_functions_start({prefix}_placement(), {m}, {prefix}_rooms())") } else { format!("{prefix}_emitted_{}()", k - 1) },
                format!("emit_functions({stem}_first_{k}(), {prefix}_placement(), {m}, {prefix}_rooms())"),
                format!("emit_functions_next({stem}_fn{k}(), {earlier}, {prefix}_placement(), {m}, {prefix}_rooms(), "))
        };
        text.push_str(&format!("
theorem {prefix}_emits_{k}(): EmitsAs({emitted}, {prefix}_code_{k}(), {prefix}_rest_{k}(), {names}) {{
    refl
}}

theorem {prefix}_emitted_{k}(): EmitsAs({functions}, {prefix}_code_{k}(), {prefix}_rest_{k}(), {names}) {{
    {next}{prog}, {places}, {labels}, {started},
        {prefix}_code_{k}(), {prefix}_rest_{k}(), {names}, {prefix}_emits_{k}())
}}
", emitted = emit(&before.0, k, &before.1, before.2), prog = before.0, places = before.1, labels = before.2));
        before = (format!("{prefix}_code_{k}()"), format!("{prefix}_rest_{k}()"), names);
    }
    let lent_counts = if lent { format!("{prefix}_counts()") } else { "[]".to_string() };
    text.push_str(&format!("
// The code's layout, by a table of its labels checked a stretch at a time.
{table}{layout}
theorem {prefix}_holes(): {prefix}_code().no_holes().IsTrue() {{ trivial }}

// Every block reads only flags it set itself (issues/x86-undefined-flags.md).
theorem {prefix}_reads(): {prefix}_code().blocks_read_own().IsTrue() {{ trivial }}

theorem {prefix}_laid(): {prefix}_code().laid_out().IsTrue() {{
    {prefix}_table().laid_out_of({prefix}_code(), {length}, {prefix}_checked_{count}(), {prefix}_holes(), {prefix}_reads())
}}

theorem {prefix}_lowers(): {lowered} = Some({prefix}_code()) {{
    {lowers}{prefix}_code(), {prefix}_rest_{last}(), {labels}, {prefix}_emitted_{last}(),
        {prefix}_laid())
}}
", last = m - 1, labels = before.2, count = items.len(), layout = super::labels::layout(prefix, &offsets, &cuts),
        lowered = format!("lower_program_roomed({stem}_program(), {prefix}_placement(), {lent_counts}, {prefix}_rooms())"),
        lowers = format!("lower_program_roomed_emitted({stem}_program(), {prefix}_placement(), {lent_counts}, {prefix}_rooms(), ")));
    text.push_str(&format!("
{agreement}
// The published bytes, a piece at a time from the last item: no one
// statement evaluates more of the code than a piece.
"));
    text.push_str(&super::labels::byte_pieces(prefix, &pieces, &bytes, items.len(), &offsets));
    text.push_str(&format!("
theorem {prefix}_entry_at(): asm_labels({prefix}_code())({label}) = {entry} {{ refl }}
", label = f + 1));
    let comma = if parameters.is_empty() { "" } else { ", " };
    // Through the optimizer, a return theorem takes both programs: the run
    // is the published one's, the lowering and its checks are of the one
    // made, and `{prefix}_cut_keeps` says the one made does at a function
    // reached whatever the published one does.
    let (through, programs, quiet) = if program.optimize {
        ("_through", format!("{prefix}_program(), {stem}_program()"), format!("{prefix}_quiet(), {stem}_quiet()"))
    } else { ("", format!("{prefix}_program()"), format!("{prefix}_quiet()")) };
    let keeps = |function: usize| if program.optimize { format!(" {prefix}_cut_keeps({function}, refl),") } else { String::new() };
    if program.marks.is_some() {
        // A writer: the file is any whose first span is `span`, and the
        // lending lets the marked buffers be written, so `loan` asks of
        // them what a store needs (`Loan::writable`, `stored`, `apart`,
        // `keeps`, `keeps_code`). What it promises is the run's ending: the
        // function's word, and the function's span where `span` was.
        text.push_str(&format!("
// The code computes the source function over its span
// (`Prog::ComputesOver`, function_ir_correct): called at its label with the
// span's address and its words in RDI, RSI, … and past the sixth on the
// stack above the return address (`Stack::Passed`), {room} bytes of stack
// below it, the file in memory with `span` its first buffer
// (`Stack::LentOver`), it returns the source function's word in RAX, keeps
// the callee-saved registers and RSP, stores only into its own room below
// that address and into the bytes of the buffers `{prefix}_marks` marks
// (`Stack::WroteIn`), and leaves the file with the function's span where
// `span` was and the rest as it was (`Stack::AnsweredOver`): on every
// machine, loaded anywhere, at any file lying anywhere the stack does not
// reach.
fn {prefix}_lending(addresses: List<BitVec(64)>, now: Buffers()) → Lending {{
    Lending::writing({prefix}_counts(), addresses, now, {prefix}_marks())
}}

theorem {prefix}_returns<M>(machine: Machine<M>, top: Nat, addresses: List<BitVec(64)>, span: List<BitVec(8)>, rest: Buffers(),
    loan: Loan<M>(machine.fetch, machine.data, machine.stack, top, {prefix}_lending(addresses, Cons(span, rest)).spans()){comma}{typed}):
    {prefix}_code().ComputesOver(machine, top, {prefix}_lending(addresses, Cons(span, rest)), {f}, {room}, {list}, Cons(span, rest),
        Ending(word := {call}.value, buffers := Cons({call}.after, rest))) {{
    λ origin last => {returns}
}}
", room = room(f), returns = if program.tables.is_some() {
            // The root's row of the tables is `{prefix}_marks`, by evaluation.
            format!("Ending::returns_marked{through}<M>({programs}, {prefix}_placement(), {prefix}_rooms(), {prefix}_counts(), addresses, {prefix}_tables(), {prefix}_code(),
        {prefix}_lowers(), {prefix}_evaluable(), {stem}_marked(), machine.fetch, machine.data, last, origin, machine.stack, top, Cons(span, rest), {f}, trivial,{keeps} loan,
        {list}, trivial, rest, {call}, {prefix}_runs(span, rest{comma}{arguments}))", arguments = parameters.join(", "), keeps = keeps(f))
        } else {
            format!("Ending::returns_written{through}<M>({programs}, {prefix}_placement(), {prefix}_rooms(), {prefix}_counts(), addresses, {prefix}_marks(), {prefix}_code(),
        {prefix}_lowers(), {prefix}_evaluable(), {stem}_within(), machine.fetch, machine.data, last, origin, machine.stack, top, Cons(span, rest), loan, {f}, trivial,{keeps}
        {list}, trivial, rest, {call}, {prefix}_runs(span, rest{comma}{arguments}))", arguments = parameters.join(", "), keeps = keeps(f))
        }));
    } else if lent {
        // The file is any (`now`), lying anywhere (`addresses`) under the
        // lending's laws (`loan`: no buffer reaches the stack below `top`).
        // `Stack::LentOver` is what the caller owes for the spans: each
        // span's address and length the words passed for it, the call
        // entered below `top`, and the file readable in memory.
        text.push_str(&format!("
// The code computes the source function over its spans
// (`Prog::ComputesOver`, function_ir_correct): called at its label with
// each span's address and length and its words in RDI, RSI, … and past the
// sixth on the stack above the return address (`Stack::Passed`), {room}
// bytes of stack below it, the spans readable in memory (`Stack::LentOver`),
// it returns the source function's value at the spans in RAX, keeps the
// callee-saved registers and RSP, stores only into its own room below that
// address, and leaves the spans as they were (`Stack::AnsweredOver`): on
// every machine, loaded anywhere, at any file lying anywhere the stack does
// not reach.
fn {prefix}_lending(addresses: List<BitVec(64)>, now: Buffers()) → Lending {{ Lending::reading({prefix}_counts(), addresses, now) }}

theorem {prefix}_returns<M>(machine: Machine<M>, top: Nat, addresses: List<BitVec(64)>, now: Buffers(),
    loan: Loan<M>(machine.fetch, machine.data, machine.stack, top, {prefix}_lending(addresses, now).spans()){comma}{typed}):
    {prefix}_code().ComputesOver(machine, top, {prefix}_lending(addresses, now), {f}, {room}, {list}, now,
        Ending(word := {call}, buffers := now)) {{
    λ origin last => compiled_returns_lent{through}<M>({programs}, {prefix}_placement(), {prefix}_rooms(), {prefix}_lending(addresses, now), {prefix}_code(),
        {prefix}_lowers(), {prefix}_evaluable(), {quiet}, machine.fetch, machine.data, last, origin, machine.stack, top, loan, {f}, trivial,{keeps}
        {list}, trivial, now, {call}, {prefix}_agrees(now{comma}{arguments}))
}}
", room = room(f), arguments = parameters.join(", "), keeps = keeps(f)));
    } else {
        text.push_str(&format!("
// The code computes the source function (`Prog::Computes`,
// function_ir_correct): called at its label with its arguments in RDI,
// RSI, … and past the sixth on the stack above the return address
// (`Stack::Passed`), {room} bytes of stack below it, it returns the source
// function's value in RAX, keeps the callee-saved registers and RSP, and
// leaves memory as it was but for stores into its own room below that
// address (`Stack::Wrote`): on every machine, loaded anywhere.
theorem {prefix}_returns<M>(machine: Machine<M>{comma}{typed}): {prefix}_code().Computes(machine, {f}, {room}, {list}, {call}) {{
    compiled_computes<M>({prefix}_program(), {prefix}_placement(), {prefix}_rooms(), {prefix}_code(), {prefix}_lowers(), {prefix}_evaluable(),
        machine, {f}, trivial, {list}, trivial, {call}, {prefix}_agrees({arguments}))
}}

// The same at every argument list: the code implements the source function
// (`Prog::Implements`).
theorem {prefix}_implements<M>(machine: Machine<M>): {prefix}_code().Implements(machine, {f}, {room}, {arity}, {spec}) {{
    {binders}{prefix}_returns<M>(machine{comma}{arguments})
}}
", room = room(f), arguments = parameters.join(", "), arity = parameters.len(), spec = curried(call, &parameters),
            binders = binders(&parameters)));
    }
    // The program's other exported functions, each at its own label: a
    // function of words, lent nothing, so its contract is the plain one
    // whatever the root's is. In a program that is lent spans that is
    // `compiled_returns_unlent`: the function reads none, and the program
    // stores into none.
    for (entry, at) in program.entries.iter().zip(&entries) {
        let (symbol, g, call) = (&entry.symbol, entry.index, &entry.source);
        let parameters: Vec<String> = (0..entry.arity).map(|i| format!("a{i}")).collect();
        let typed = if parameters.is_empty() { String::new() } else { format!("{}: BitVec(64)", parameters.join(", ")) };
        let list = format!("[{}]", parameters.join(", "));
        let comma = if parameters.is_empty() { "" } else { ", " };
        let arguments = parameters.join(", ");
        let proved = if lent {
            format!("compiled_returns_unlent{through}<M>({programs}, {prefix}_placement(), {prefix}_rooms(), {prefix}_counts(), {prefix}_code(), {prefix}_lowers(),
        {prefix}_evaluable(), {quiet}, machine.fetch, machine.data, last, origin, machine.stack, {g}, trivial,{keeps} refl, {list}, trivial,
        {call}({arguments}), {symbol}_native_agrees({arguments}))", keeps = keeps(g))
        } else {
            format!("compiled_returns<M>({prefix}_program(), {prefix}_placement(), {prefix}_rooms(), {prefix}_code(), {prefix}_lowers(), {prefix}_evaluable(),
        machine.fetch, machine.data, last, origin, machine.stack, {g}, trivial, {list}, trivial, {call}({arguments}),
        {symbol}_native_agrees({arguments}))")
        };
        text.push_str(&format!("
theorem {symbol}_native_entry_at(): asm_labels({prefix}_code())({label}) = {at} {{ refl }}

// `{symbol}` is the program's function {g}, exported at its own label, and
// computes `{call}` (`Prog::Computes`): called there with its arguments in
// RDI, RSI, … and past the sixth on the stack above the return address
// (`Stack::Passed`), {room} bytes of stack below it, the code returns
// `{call}`'s value in RAX, keeps the callee-saved registers and RSP, and
// leaves memory as it was but for stores into its own room below that
// address (`Stack::Wrote`).
theorem {symbol}_native_returns<M>(machine: Machine<M>{comma}{typed}): {prefix}_code().Computes(machine, {g}, {room}, {list}, {call}({arguments})) {{
    λ origin last => {proved}
}}

theorem {symbol}_native_implements<M>(machine: Machine<M>): {prefix}_code().Implements(machine, {g}, {room}, {arity}, {spec}) {{
    {binders}{symbol}_native_returns<M>(machine{comma}{arguments})
}}
", label = g + 1, room = room(g), arity = parameters.len(), spec = curried(&format!("{call}({arguments})"), &parameters),
            binders = binders(&parameters)));
    }
    let rooms = program.entries.iter().map(|entry| room(entry.index)).collect();
    Ok(Compiled { text, bytes, entry, entries, room: room(f), rooms })
}

/// The source function as a value of `Words(n)` (function_ir_correct), from
/// its call at the words `parameters`: the function's name when the call is
/// that name applied to them, and the call under a binder for each word
/// otherwise.
fn curried(call: &str, parameters: &[String]) -> String {
    if parameters.is_empty() { return format!("({call})"); }
    let applied = format!("({})", parameters.join(", "));
    match call.strip_suffix(&applied) {
        Some(name) if !name.is_empty() && name.chars().all(|c| c.is_alphanumeric() || c == '_' || c == ':') => name.to_string(),
        _ => format!("(λ {} => {call})", parameters.iter().map(|p| format!("({p}: BitVec(64))")).collect::<Vec<_>>().join(" ")),
    }
}

/// A binder for each word, before a term at them.
fn binders(parameters: &[String]) -> String {
    if parameters.is_empty() { String::new() } else { format!("λ {} => ", parameters.join(" ")) }
}

/// `{prefix}_evaluable`: the program's functions evaluable, checked by
/// `program_scan_at` (one pass over each function,
/// issues/function-ir-evaluable-quadratic.md) a function per declaration,
/// so the kernel's per-declaration fuel bounds the largest function rather
/// than the program; `program_scan_at_drop` joins them, from the last
/// function (`{prefix}_scans_{k}` covers functions `0..=k`). `arities` is
/// how many words each function takes, the last function's first: a
/// function's statement checks its own entry and reads its callees' there,
/// where reading them off the callees would force each callee's code
/// (issues/compile-x86-certificate-memory.md).
fn evaluable_text(prefix: &str, functions: usize, arities: &str) -> String {
    let (program, table) = (format!("{prefix}_program()"), format!("{prefix}_arities()"));
    let mut text = format!("// How many words each function takes, the last function's first.
fn {prefix}_arities() → List<Nat> {{ {arities} }}

theorem {prefix}_scans_none(): program_scan_at({program}.drop({functions}), {table}.drop({functions})).IsTrue() {{ trivial }}\n");
    for k in 0..functions {
        let below = if k == 0 { "none".to_string() } else { (k - 1).to_string() };
        text.push_str(&format!("theorem {prefix}_scanned_{k}(): program_scan_at_head({program}.drop({d}), {table}.drop({d})).IsTrue() {{ trivial }}
theorem {prefix}_scans_{k}(): program_scan_at({program}.drop({d}), {table}.drop({d})).IsTrue() {{
    program_scan_at_drop({program}, {table}, {d}, {prefix}_scanned_{k}(), {prefix}_scans_{below}())
}}
", d = functions - 1 - k));
    }
    text.push_str(&format!("theorem {prefix}_evaluable(): program_evaluable({program}).IsTrue() {{
    program_scan_at_evaluable({program}, {table}, program_scan_at_drop_zero({program}, {table}, {prefix}_scans_{last}()))
}}", last = functions - 1));
    text
}

/// `{prefix}_quiet`: no function of the program stores into a buffer, so
/// it reads the file it is lent and leaves it. A function at a time, as
/// [`evaluable_text`] is: the kernel's fuel is per declaration, and a
/// program with the scanner's automaton in it is past what one evaluation
/// walks (`program_quiet_drop`).
fn quiet_text(prefix: &str, functions: usize) -> String {
    let program = format!("{prefix}_program()");
    let mut text = format!("// No function of the program stores into a buffer: it reads the file it is
// lent and leaves it.
theorem {prefix}_quiet_none(): program_quiet({program}.drop({functions})).IsTrue() {{ trivial }}\n");
    for k in 0..functions {
        let below = if k == 0 { "none".to_string() } else { (k - 1).to_string() };
        text.push_str(&format!("theorem {prefix}_quiet_head_{k}(): program_quiet_head({program}.drop({d})).IsTrue() {{ trivial }}
theorem {prefix}_quiet_{k}(): program_quiet({program}.drop({d})).IsTrue() {{
    program_quiet_drop({program}, {d}, {prefix}_quiet_head_{k}(), {prefix}_quiet_{below}())
}}
", d = functions - 1 - k));
    }
    text.push_str(&format!("theorem {prefix}_quiet(): program_quiet({program}).IsTrue() {{
    program_quiet_drop_zero({program}, {prefix}_quiet_{last}())
}}", last = functions - 1));
    text
}

/// `{prefix}_marked`: every function's stores are into buffers its own row
/// of `{prefix}_tables` marks, and every call, over views or not, is of a
/// callee whose row its caller's meets (`program_marked_needs`). One
/// evaluation over the program: a call's check reads its callee's row.
fn marked_text(prefix: &str, stem: &str) -> String {
    format!("// Each function stores into the buffers its row of `{prefix}_tables` marks, and calls only callees whose rows its own meets.
theorem {stem}_marked(): program_marked({stem}_program(), {prefix}_tables()).IsTrue() {{ trivial }}")
}

/// `{prefix}_within`: every store of the program is into a buffer
/// `{prefix}_marks` marks, so a caller that lends those to write has lent
/// all the program stores into (`program_stores_marked`). A function at a
/// time, as [`quiet_text`] is.
fn within_text(prefix: &str, stem: &str, functions: usize) -> String {
    let (program, marks) = (format!("{stem}_program()"), format!("{prefix}_marks()"));
    let mut text = format!("// Every store of the program is into a buffer `{prefix}_marks` marks.
theorem {stem}_within_none(): program_stores_within({program}.drop({functions}), {marks}).IsTrue() {{ trivial }}\n");
    for k in 0..functions {
        let below = if k == 0 { "none".to_string() } else { (k - 1).to_string() };
        text.push_str(&format!("theorem {stem}_within_head_{k}(): program_stores_within_head({program}.drop({d}), {marks}).IsTrue() {{ trivial }}
theorem {stem}_within_{k}(): program_stores_within({program}.drop({d}), {marks}).IsTrue() {{
    program_stores_within_drop({program}, {marks}, {d}, {stem}_within_head_{k}(), {stem}_within_{below}())
}}
", d = functions - 1 - k));
    }
    text.push_str(&format!("theorem {stem}_within(): program_stores_within({program}, {marks}).IsTrue() {{
    program_stores_within_drop_zero({program}, {marks}, {stem}_within_{last}())
}}", last = functions - 1));
    text
}

/// The program's agreement with its source: `{prefix}_evaluable`, each
/// function's agreement, and `{prefix}_agrees`, the program's root
/// function evaluating to the source function (`program_eval_sources`).
pub(super) fn agreement_text(prefix: &str, program: &function_ir_source::ReflectedProgram) -> String {
    let root = &program.functions[program.root];
    let f = program.root;
    // Each function proved on its own, its calls answered by its callees'
    // sources; then the program by `program_eval_sources`.
    let sources = format!("{prefix}_sources()");
    let mut answers = "BitVec::zero()".to_string();
    for (k, function) in program.functions.iter().enumerate().rev() {
        let words: Vec<String> = (0..function.arity).map(|i| format!("words.word({i})")).collect();
        answers = format!("match g{k} {{ Zero => {}, Succ(g{}) => {answers} }}", function.answer(&words), k + 1);
    }
    let mut agreements = format!("// What each function computes: its source.
fn {prefix}_sources() → Answers() {{
    λ (g0: Nat) (words: List<BitVec(64)>) => {answers}
}}

");
    let mut sourced = "trivial".to_string();
    for (k, function) in program.functions.iter().enumerate() {
        agreements.push_str(&function_agreement(&format!("{prefix}_fn{k}"), &sources, function));
        let arguments = arguments(function.arity);
        let at = if function.arity == 0 { format!("{prefix}_fn{k}_agrees()") } else { format!("λ {} => {prefix}_fn{k}_agrees({})", arguments.join(" "), arguments.join(", ")) };
        sourced = format!("⟨λ (words: List<BitVec(64)>) (fits: words.len() = {n}) => spread({n}, λ (ws: List<BitVec(64)>) => {prefix}_fn{k}().eval({sources}, ws) = {sources}({k}, ws),
            {at}, words, fits),
        {sourced}⟩", n = function.arity);
    }
    let parameters = arguments(root.arity);
    let typed = typed(&parameters);
    let list = format!("[{}]", parameters.join(", "));
    let call = root.answer(&parameters);
    let arities: Vec<String> = program.functions.iter().rev().map(|function| function.arity.to_string()).collect();
    let evaluable = evaluable_text(prefix, program.functions.len(), &format!("[{}]", arities.join(", ")));
    format!("{evaluable}

{agreements}
theorem {prefix}_sourced(): program_sourced({prefix}_program(), {sources}) {{
    {sourced}
}}

// The program's function {f} evaluates to the source function.
theorem {prefix}_agrees({typed}): program_eval({prefix}_program(), {f}, {list}) = {call} {{
    program_eval_sources({prefix}_program(), {prefix}_evaluable(), {sources}, {prefix}_sourced(), {f}, {list}, trivial)
}}
")
}

/// `import` lines for the modules the program's functions come from.
pub(super) fn owner_imports(program: &function_ir_source::ReflectedProgram) -> String {
    let mut owners: Vec<&str> = program.functions.iter().filter_map(|function| function.source_name.rsplit_once("::").map(|(owner, _)| owner)).collect();
    owners.sort();
    owners.dedup();
    owners.iter().map(|owner| format!("import {owner};\n")).collect()
}

/// The program's definitions: each function `{prefix}_fn{k}()`, the lists `{prefix}_first_{k}()` and `{prefix}_program()`.
pub(super) fn program_text(prefix: &str, program: &function_ir_source::ReflectedProgram) -> String {
    let mut definitions = String::new();
    definitions.push_str(&format!("\n// The program, function `k` the one with `k` after it: {}.\n", program.functions.iter().map(|function| function.source_name.as_str()).collect::<Vec<_>>().join(", ")));
    for (k, function) in program.functions.iter().enumerate() {
        definitions.push_str(&format!("fn {prefix}_fn{k}() → Function {{\n    {}\n}}\n\n", function.render()));
    }
    // The exported function is the last, so the first the program lists;
    // the others answer its calls.
    // The program's first functions, each list the last one's with one
    // more: what each function's emission starts from.
    let m = program.functions.len();
    for k in 0..m {
        let earlier = if k == 0 { "Nil".to_string() } else { format!("{prefix}_first_{}()", k - 1) };
        definitions.push_str(&format!("fn {prefix}_first_{k}() → List<Function> {{ Cons({prefix}_fn{k}(), {earlier}) }}\n"));
    }
    definitions.push_str(&format!("fn {prefix}_program() → List<Function> {{ {prefix}_first_{}() }}\n\n", m - 1));
    definitions
}

/// Function `name`'s agreement with its source, its calls answered by
/// `sources`: by conversion, through an expansion.
fn function_agreement(name: &str, sources: &str, function: &function_ir_source::ProgramFunction) -> String {
    let arguments = arguments(function.arity);
    let typed = typed(&arguments);
    let list = format!("[{}]", arguments.join(", "));
    let answer = function.answer(&arguments);
    let joined = arguments.join(", ");
    let source = &function.source_name;
    // With its calls open, the function is its expansion by conversion and
    // no callee is unfolded; with the callees' sources for them, the
    // expansion is the source.
    let expands = if function.decided { "split_all;\n    all_goals { refl }" } else { "refl" };
    format!("// `{source}` as the decision tree it compiles, its calls answered by `call`.
fn {name}_expansion(call: Answers(){more}) → BitVec(64) {{
    {expansion}
}}

theorem {name}_expanded(call: Answers(){more}): {name}().eval(call, {list}) = {name}_expansion(call{rest}) {{ refl }}

theorem {name}_expands({typed}): {name}_expansion({sources}{rest}) = {answer} {{
    {expands}
}}

theorem {name}_agrees({typed}): {name}().eval({sources}, {list}) = {answer} {{
    trans({name}_expanded({sources}{rest}), {name}_expands({joined}))
}}

", more = if typed.is_empty() { String::new() } else { format!(", {typed}") }, rest = if joined.is_empty() { String::new() } else { format!(", {joined}") },
        expansion = function.expansion)
}

/// A function's arguments as the certificate names them.
fn arguments(arity: usize) -> Vec<String> { (0..arity).map(|i| format!("a{i}")).collect() }

fn typed(arguments: &[String]) -> String {
    if arguments.is_empty() { String::new() } else { format!("{}: BitVec(64)", arguments.join(", ")) }
}

/// Bytes a piece of the published code is cut at, at least: about a
/// quarter of a declaration's fuel at the cost of an assembled byte.
const PIECE: usize = 256;

/// A piece of the published code: how many items from the end it starts,
/// how many items it has, and the byte it starts at.
pub(super) struct Piece { pub back: usize, pub count: usize, pub start: usize }

/// Pieces of whole items, about `size` bytes each, from the end.
pub(super) fn cut_pieces(lens: &[u64], size: usize) -> Vec<Piece> {
    let mut at: usize = lens.iter().sum::<u64>() as usize;
    let mut back = 0;
    let mut pieces = Vec::new();
    let mut items_in = 0;
    let mut start = at;
    for len in lens.iter().rev() {
        start -= *len as usize;
        items_in += 1;
        if at - start >= size {
            pieces.push(Piece { back, count: items_in, start });
            back += items_in;
            items_in = 0;
            at = start;
        }
    }
    if items_in > 0 { pieces.push(Piece { back, count: items_in, start }); }
    pieces
}

pub(super) const GPRS: [&str; 16] = ["Rax", "Rcx", "Rdx", "Rbx", "Rsp", "Rbp", "Rsi", "Rdi", "R8", "R9", "R10", "R11", "R12", "R13", "R14", "R15"];
const LOW_BYTES: [Option<&str>; 16] = [Some("Al"), Some("Cl"), Some("Dl"), Some("Bl"), None, Some("Bpl"), Some("Sil"), Some("Dil"),
    Some("R8b"), Some("R9b"), Some("R10b"), Some("R11b"), Some("R12b"), Some("R13b"), Some("R14b"), Some("R15b")];
const CONDITIONS: [&str; 16] = ["O", "NO", "B", "AE", "E", "NE", "BE", "A", "S", "NS", "P", "NP", "L", "GE", "LE", "G"];

/// The code as `Prog::numbers` writes it, back as source: each item's name
/// and the item. A misreading is no hazard to the proof, which checks the
/// literal against the lowering; it is a refusal the compiler reports.
fn read_items(numbers: &[u64]) -> Result<Vec<(u64, String)>, String> {
    read_items_with(numbers, &|width, n| format!("@bitvec::BitVec::ofNat({width}, {n})"))
}

/// [`read_items`], each immediate spelled by `word` from its width and value.
pub(super) fn read_items_with(numbers: &[u64], word: &dyn Fn(u32, u64) -> String) -> Result<Vec<(u64, String)>, String> {
    let mut at = numbers.iter().copied();
    let mut next = || at.next().ok_or_else(|| "the code's numbers end early".to_string());
    let bad = || "the code's numbers are malformed".to_string();
    let gpr = |n: u64| GPRS.get(n as usize).copied().ok_or_else(bad);
    let low = |n: u64| LOW_BYTES.get(n as usize).copied().flatten().ok_or_else(bad);
    let mut items = Vec::new();
    let total = numbers.len();
    let mut used = 0;
    while used < total {
        let mut take = || { used += 1; next() };
        let name = take()?;
        let item = match take()? {
            0 => {
                let count = take()?;
                let mut instructions = Vec::new();
                for _ in 0..count {
                    let instruction = match take()? {
                        tag @ (0 | 2 | 3 | 4 | 5 | 6 | 7 | 11) => {
                            let op = ["MovRR", "", "AddRR", "SubRR", "AndRR", "OrRR", "XorRR", "CmpRR", "", "", "", "TestRR"][tag as usize];
                            format!("{op}({}, {})", gpr(take()?)?, gpr(take()?)?)
                        }
                        1 => format!("MovRI({}, {})", gpr(take()?)?, word(64, take()?)),
                        tag @ 8..=10 => format!("{}({})", ["SetBelow", "SetLess", "SetEqual"][tag as usize - 8], low(take()?)?),
                        12 => format!("AddRI8({}, {})", gpr(take()?)?, word(8, take()?)),
                        13 => format!("AddRI32({}, {})", gpr(take()?)?, word(32, take()?)),
                        14 => {
                            let op = *["OpShl", "OpShr", "OpSar"].get(take()? as usize).ok_or_else(bad)?;
                            format!("ShiftOne({op}, {})", gpr(take()?)?)
                        }
                        15 => {
                            let op = *["OpShl", "OpShr", "OpSar"].get(take()? as usize).ok_or_else(bad)?;
                            format!("ShiftImm({op}, {}, {})", gpr(take()?)?, word(8, take()?))
                        }
                        16 => format!("Bswap32({})", gpr(take()?)?),
                        19 => format!("CmpRI8({}, {})", gpr(take()?)?, word(8, take()?)),
                        20 => format!("CmpRI32({}, {})", gpr(take()?)?, word(32, take()?)),
                        21 => format!("MovRI32({}, {})", gpr(take()?)?, word(32, take()?)),
                        17 => format!("MovSelf32({})", gpr(take()?)?),
                        18 => format!("RorRI32({}, {})", gpr(take()?)?, word(8, take()?)),
                        _ => return Err(bad()),
                    };
                    instructions.push(instruction);
                }
                // Spelled by its constructors and not as `[…]`: a list
                // literal resolves its `CollectionLiteral` instance and
                // unifies its element type at every use, which made a
                // certificate's `{p}_at_` stretches cost about twice what
                // their constructors do.
                let list = instructions.iter().rev().fold("Nil".to_string(), |rest, i| format!("Cons({i}, {rest})"));
                format!("Block({list})")
            }
            1 => format!("Jcc({}, {})", CONDITIONS.get(take()? as usize).ok_or_else(bad)?, take()?),
            2 => format!("Jmp({})", take()?),
            3 => format!("CallTo({})", take()?),
            4 => "Ret".to_string(),
            5 => format!("Spill(StackStore(source := {}, offset := {}))", gpr(take()?)?, word(8, take()?)),
            6 => format!("Reload(StackLoad(destination := {}, offset := {}))", gpr(take()?)?, word(8, take()?)),
            8 => format!("Load(WordLoad({}, {}))", gpr(take()?)?, gpr(take()?)?),
            9 => format!("Store(WordStore({}, {}))", gpr(take()?)?, gpr(take()?)?),
            10 => format!("LoadByte(ByteLoad({}, {}))", gpr(take()?)?, gpr(take()?)?),
            11 => format!("StoreByte(ByteStore({}, {}))", gpr(take()?)?, gpr(take()?)?),
            12 => "Syscall".to_string(),
            // A piece: its length and its bytes, stated as they are. Its
            // measure is a verdict (x86_64_asm), `True` at a literal's
            // bytes, so the literal is the lowering's piece whichever
            // lemma measured that one.
            13 => {
                let len = take()?;
                let mut bytes = Vec::new();
                for _ in 0..len { bytes.push(word(8, take()?)); }
                let list = bytes.iter().rev().fold("Nil".to_string(), |rest, b| format!("Cons({b}, {rest})"));
                format!("Piece({list}, {len}, trivial)")
            }
            _ => return Err("the lowering emitted an item the compiler does not state".into()),
        };
        items.push((name, item));
    }
    Ok(items)
}
