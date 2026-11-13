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
}

const IMPORTS: &[&str] = &["function_ir", "function_ir_eval", "function_ir_lower", "function_ir_lower_structured",
    "function_ir_lower_calls", "function_ir_compile", "x86_64", "x86_64_block", "x86_64_fetch", "x86_64_data_read",
    "x86_64_fetched_code", "x86_64_stack", "x86_64_asm", "x86_64_asm_runs", "x86_64_asm_table", "x86_64_stack_runs", "bitvec", "bool", "list",
    "logic", "nat", "option"];

/// What a program that is lent buffers needs besides: that it stores into
/// none, and the laws its buffers are lent under.
const LENT_IMPORTS: &[&str] = &["function_ir_writes", "function_ir_lower_reads", "x86_64_lending"];

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
}

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
        }
    }

    /// A `runtime fn`'s program, as its generator published it
    /// (`{source}::program`, its last function `source`, the others the
    /// runtime fns it reaches) with its agreement (`{source}::agrees`, from
    /// the functions' `Compile` instances, docs/runtime-fn-setups-design.md
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
        Shape { functions, root: functions - 1, arity, definitions, agreement, answer, lent: None, marks: None, tables: None, entries: Vec::new() }
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
        let agreement = format!("{evaluable}

{quiet}

// Over any file, the program's function {f} evaluates to the source function
// at the file's spans: the generator's theorem, from each function's
// `Compile` instance.
theorem {prefix}_agrees(now: Buffers(), {typed}): program_eval_over(now, {prefix}_program(), {f}, [{list}]) = {answer} {{
    {source}::agrees_over(now, {list})
}}
", evaluable = evaluable_text(prefix, functions, &format!("{source}::arities")), quiet = quiet_text(prefix, functions), f = functions - 1,
            list = parameters.join(", "));
        Shape { functions, root: functions - 1, arity, definitions, agreement, answer, lent: Some(counts), marks: None, tables: None, entries: Vec::new() }
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
            within = if tables.is_some() { marked_text(prefix) } else { within_text(prefix, functions) }, f = functions - 1,
            list = parameters.join(", "));
        Shape { functions, root: functions - 1, arity, definitions, agreement, answer, lent: Some(counts), marks: Some(marks), tables, entries: Vec::new() }
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
        [_, arity, ..] if arity > 6 => Err(format!("`{source}` takes {arity} words{}: compile-x86 passes at most six, in registers",
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
        if arity > 6 { return Err(format!("`{named}` takes {arity} words: compile-x86 passes at most six, in registers")); }
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

pub(super) fn compile(elab: &Elaborator, prefix: &str, module: &str, program: &Shape) -> Result<Compiled, String> {
    let f = program.root;
    let mut imports = String::new();
    for name in IMPORTS { imports.push_str(&format!("import {name};\n")); }
    let definitions = format!("{imports}{}", program.definitions);
    let m = program.functions;
    // A function's emission after `prog`: under the program's counts of
    // lent buffers where it has them.
    let lent = program.lent.is_some();
    let emit = |prog: &str, k: usize, places: &str, names: u64| if lent {
        format!("{prefix}_fn{k}().emit_lent({prog}, {k}, {places}, {names}, {prefix}_counts())")
    } else {
        format!("{prefix}_fn{k}().emit({prog}, {k}, {places}, {names})")
    };
    // Evaluated on a fork, which only defines: the certificate's statements
    // are the session's to check. A function at a time, each read from the
    // literals the reads before it gave: every read is an evaluation of its
    // own, so one that planned or emitted the whole program would hold all
    // of it at once, and each of them again
    // (issues/compile-x86-certificate-memory.md). The planner runs once per
    // function; a function is emitted onto the code before it as a literal.
    let probe = format!("{module}_probe");
    let mut plans = String::new();
    for k in 0..m {
        plans.push_str(&format!("fn {prefix}_plan_{k}() → List<Nat> {{ {prefix}_fn{k}().plan().map(λ (place: Place) => place.number()) }}\n"));
    }
    // The last `d` items' numbers, as `Prog::numbers` writes them.
    plans.push_str(&format!("fn {prefix}_top(p: Prog, d: Nat, after: List<Nat>) → List<Nat> {{
    match d {{ Zero => after, Succ(j) => match p {{ Start => after, At(before, name, item) => {prefix}_top(before, j, Cons(name, item.numbers() ++ after)) }} }}
}}
"));
    let mut fork = elab.fork();
    let first = format!("{definitions}{plans}");
    fork.elab_module_source(&probe, &first).map_err(|e| e.render(&first))?;
    let read = |fork: &Elaborator, module: &str, item: &str|
        function_ir_source::evaluate_numbers(fork, &format!("{module}::{prefix}_{item}")).map_err(|e| format!("`{prefix}_{item}`: {e}"));
    let mut placement = Vec::new();
    for k in 0..m {
        for n in read(&fork, &probe, &format!("plan_{k}"))? {
            placement.push(match n {
                16 => "Folded".to_string(),
                // A function's count of saves (`Place::number`).
                n if n >= 17 => format!("Saving({})", n - 17),
                n => GPRS.get(n as usize).map(|gpr| format!("Into({gpr})")).ok_or_else(|| "a malformed placement".to_string())?,
            });
        }
    }
    let rest = |left: usize| format!("[{}]", placement[placement.len() - left..].join(", "));
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
    let mut modules = vec![probe.clone()];
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
        fork.elab_module_source(&step, &text).map_err(|e| e.render(&text))?;
        let numbers = read(&fork, &step, &format!("read_{k}"))?;
        match numbers[..] {
            // Which function and where in it: the library's mirror of the
            // emitter's tests says (`function_ir_refusal`,
            // issues/function-ir-planner-register-pressure.md). Each a read
            // of its own, as every read here is.
            [] => {
                let counts = if lent { format!("{prefix}_counts()") } else { "[]".to_string() };
                let why = format!("{probe}_refusal");
                let text = format!("{imports}import function_ir_refusal;\n{}
fn {prefix}_refused() → List<Nat> {{ {prefix}_fn{k}().refusal_bytes({k}, {names}, {counts}) }}
fn {prefix}_shown() → List<Nat> {{ {prefix}_fn{k}().shown_bytes() }}
", uses(&modules));
                let defined = fork.elab_module_source(&why, &text).is_ok();
                let said = |item: &str| read(&fork, &why, item).ok().filter(|_| defined)
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
                // calls only compiled code (docs/native-library-exports-design.md
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
    fork.elab_module_source(&closing, &text).map_err(|e| e.render(&text))?;
    modules.push(closing.clone());
    let lens = read(&fork, &closing, "lens")?;
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
    fork.elab_module_source(&reading, &text).map_err(|e| e.render(&text))?;
    let mut bytes = Vec::with_capacity(length);
    for &cut in cuts.iter().filter(|&&cut| cut > 0) {
        for b in read(&fork, &reading, &format!("bytes_{cut}"))? {
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
    // The code is stated as the literal the lowering computes, a function at
    // a time, each function's emission its own statement from the literal
    // before it: a declaration's fuel is its own, and the lowering is most
    // of what one could spend.
    text.push_str(&format!("
// The placement the heuristic chose; the theorem holds for any.
fn {prefix}_placement() → List<Place> {{ {} }}
", rest(placement.len())));
    // The literal: `{prefix}_at_{c}` its first `c` items at each cut, and
    // each function's code the cut it ends at.
    text.push_str(&super::emission::code(prefix, &items, &cuts));
    let mut before = ("Start".to_string(), format!("{prefix}_placement()"), m as u64);
    for (k, &(count, left, names)) in after.iter().enumerate() {
        text.push_str(&format!("
fn {prefix}_code_{k}() → Prog {{ {prefix}_at_{count}() }}

fn {prefix}_rest_{k}() → List<Place> {{ {} }}
", rest(left)));
        let earlier = if k == 0 { "Nil".to_string() } else { format!("{prefix}_first_{}()", k - 1) };
        let (started, functions, next) = if lent {
            (if k == 0 { format!("emit_functions_lent_start({prefix}_placement(), {m}, {prefix}_counts())") } else { format!("{prefix}_emitted_{}()", k - 1) },
                format!("emit_functions_after_lent(Start, {prefix}_first_{k}(), {prefix}_placement(), {m}, {prefix}_counts())"),
                format!("emit_functions_lent_next({prefix}_fn{k}(), {earlier}, {prefix}_placement(), {m}, {prefix}_counts(), "))
        } else {
            (if k == 0 { format!("emit_functions_start({prefix}_placement(), {m})") } else { format!("{prefix}_emitted_{}()", k - 1) },
                format!("emit_functions({prefix}_first_{k}(), {prefix}_placement(), {m})"),
                format!("emit_functions_next({prefix}_fn{k}(), {earlier}, {prefix}_placement(), {m}, "))
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
        lowered = if lent { format!("lower_program_lent({prefix}_program(), {prefix}_placement(), {prefix}_counts())") }
            else { format!("lower_program({prefix}_program(), {prefix}_placement())") },
        lowers = if lent { format!("lower_program_lent_emitted({prefix}_program(), {prefix}_placement(), {prefix}_counts(), ") }
            else { format!("lower_program_emitted({prefix}_program(), {prefix}_placement(), ") }));
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
    if program.marks.is_some() {
        // A writer: the file is any whose first span is `span`, and the
        // lending lets the marked buffers be written, so `loan` asks of
        // them what a store needs (`Loan::writable`, `stored`, `apart`,
        // `keeps`, `keeps_code`). What it promises is the run's ending: the
        // function's word, and the function's span where `span` was.
        text.push_str(&format!("
// Called at its label with the span's address and its words in RDI, RSI,
// …, a return address at RSP and {room} bytes of stack below it, the file
// in memory with `span` its first buffer (`Stack::LentOver`), the code
// returns the source function's word in RAX, keeps the callee-saved
// registers and RSP, stores only into its own room below that address and
// into the bytes of the buffers `{prefix}_marks` marks (`Stack::WroteIn`), and
// leaves the file with the function's span where `span` was and the rest as
// it was (`Stack::AnsweredOver`): resident anywhere, whatever follows it, at
// any file lying anywhere the stack does not reach.
fn {prefix}_lending(addresses: List<BitVec(64)>, now: Buffers()) → Lending {{
    Lending::writing({prefix}_counts(), addresses, now, {prefix}_marks())
}}

theorem {prefix}_returns<M>(fetch: FetchAccess<M>, data: ByteReadAccess<M>, last: List<BitVec(8)>, origin: BitVec(64),
    stack: Stack<M>(fetch, data), top: Nat, addresses: List<BitVec(64)>, span: List<BitVec(8)>, rest: Buffers(),
    loan: Loan<M>(fetch, data, stack, top, {prefix}_lending(addresses, Cons(span, rest)).spans()){comma}{typed}):
    Site<M>(fetch, data, {prefix}_code(), last, origin).Returns(stack, asm_labels({prefix}_code())({label}),
        λ (i: Nat) (s: MachineState<M>) => (ArgsIn({list}, argument_registers(), s.gprs) ∧ 120 * {label} <= i) ∧
            stack.LentOver({prefix}_lending(addresses, Cons(span, rest)), top, {f}, {list}, Cons(span, rest))(i, s),
        stack.AnsweredOver({prefix}_lending(addresses, Cons(span, rest)), {call}.value, Cons({call}.after, rest))) {{
    {returns}
}}
", label = f + 1, room = 120 * (f + 1), returns = if program.tables.is_some() {
            // The root's row of the tables is `{prefix}_marks`, by evaluation.
            format!("Ending::returns_marked<M>({prefix}_program(), {prefix}_placement(), {prefix}_counts(), addresses, {prefix}_tables(), {prefix}_code(),
        {prefix}_lowers(), {prefix}_evaluable(), {prefix}_marked(), fetch, data, last, origin, stack, top, Cons(span, rest), {f}, trivial, loan,
        {list}, trivial, rest, {call}, {prefix}_runs(span, rest{comma}{arguments}))", arguments = parameters.join(", "))
        } else {
            format!("Ending::returns_written<M>({prefix}_program(), {prefix}_placement(), {prefix}_counts(), addresses, {prefix}_marks(), {prefix}_code(),
        {prefix}_lowers(), {prefix}_evaluable(), {prefix}_within(), fetch, data, last, origin, stack, top, Cons(span, rest), loan, {f}, trivial,
        {list}, trivial, rest, {call}, {prefix}_runs(span, rest{comma}{arguments}))", arguments = parameters.join(", "))
        }));
    } else if lent {
        // The file is any (`now`), lying anywhere (`addresses`) under the
        // lending's laws (`loan`: no buffer reaches the stack below `top`).
        // `Stack::LentOver` is what the caller owes for the spans: each
        // span's address and length the words passed for it, the call
        // entered below `top`, and the file readable in memory.
        text.push_str(&format!("
// Called at its label with each span's address and length and its words in
// RDI, RSI, …, a return address at RSP and {room} bytes of stack below it,
// the spans readable in memory (`Stack::LentOver`), the code returns the
// source function's value at the spans in RAX, keeps the callee-saved
// registers and RSP, stores only into its own room below that address, and
// leaves the spans as they were (`Stack::AnsweredOver`): resident anywhere,
// whatever follows it, at any file lying anywhere the stack does not reach.
fn {prefix}_lending(addresses: List<BitVec(64)>, now: Buffers()) → Lending {{ Lending::reading({prefix}_counts(), addresses, now) }}

theorem {prefix}_returns<M>(fetch: FetchAccess<M>, data: ByteReadAccess<M>, last: List<BitVec(8)>, origin: BitVec(64),
    stack: Stack<M>(fetch, data), top: Nat, addresses: List<BitVec(64)>, now: Buffers(),
    loan: Loan<M>(fetch, data, stack, top, {prefix}_lending(addresses, now).spans()){comma}{typed}):
    Site<M>(fetch, data, {prefix}_code(), last, origin).Returns(stack, asm_labels({prefix}_code())({label}),
        λ (i: Nat) (s: MachineState<M>) => (ArgsIn({list}, argument_registers(), s.gprs) ∧ 120 * {label} <= i) ∧
            stack.LentOver({prefix}_lending(addresses, now), top, {f}, {list}, now)(i, s),
        stack.AnsweredOver({prefix}_lending(addresses, now), {call}, now)) {{
    compiled_returns_lent<M>({prefix}_program(), {prefix}_placement(), {prefix}_lending(addresses, now), {prefix}_code(), {prefix}_lowers(),
        {prefix}_evaluable(), {prefix}_quiet(), fetch, data, last, origin, stack, top, loan, {f}, trivial, {list}, trivial, now, {call},
        {prefix}_agrees(now{comma}{arguments}))
}}
", label = f + 1, room = 120 * (f + 1), arguments = parameters.join(", ")));
    } else {
        text.push_str(&format!("
// Called at its label with its arguments in RDI, RSI, …, a return address
// at RSP and {room} bytes of stack below it, the code returns the source
// function's value in RAX, keeps the callee-saved registers and RSP, and
// leaves memory as it was but for stores into its own room below that
// address (`Stack::Wrote`): resident anywhere, whatever follows it, with
// any stack meeting the `Stack` laws.
theorem {prefix}_returns<M>(fetch: FetchAccess<M>, data: ByteReadAccess<M>, last: List<BitVec(8)>, origin: BitVec(64),
    stack: Stack<M>(fetch, data){comma}{typed}):
    Site<M>(fetch, data, {prefix}_code(), last, origin).Returns(stack, asm_labels({prefix}_code())({label}),
        λ (i: Nat) (s: MachineState<M>) => ArgsIn({list}, argument_registers(), s.gprs) ∧ 120 * {label} <= i,
        stack.CalleePost({call})) {{
    compiled_returns<M>({prefix}_program(), {prefix}_placement(), {prefix}_code(), {prefix}_lowers(), {prefix}_evaluable(),
        fetch, data, last, origin, stack, {f}, trivial, {list}, trivial, {call}, {prefix}_agrees({arguments}))
}}
", label = f + 1, room = 120 * (f + 1), arguments = parameters.join(", ")));
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
            format!("compiled_returns_unlent<M>({prefix}_program(), {prefix}_placement(), {prefix}_counts(), {prefix}_code(), {prefix}_lowers(),
        {prefix}_evaluable(), {prefix}_quiet(), fetch, data, last, origin, stack, {g}, trivial, refl, {list}, trivial, {call}({arguments}),
        {symbol}_native_agrees({arguments}))")
        } else {
            format!("compiled_returns<M>({prefix}_program(), {prefix}_placement(), {prefix}_code(), {prefix}_lowers(), {prefix}_evaluable(),
        fetch, data, last, origin, stack, {g}, trivial, {list}, trivial, {call}({arguments}), {symbol}_native_agrees({arguments}))")
        };
        text.push_str(&format!("
theorem {symbol}_native_entry_at(): asm_labels({prefix}_code())({label}) = {at} {{ refl }}

// `{symbol}` is the program's function {g}, exported at its own label. Called
// there with its arguments in RDI, RSI, …, a return address at RSP and {room}
// bytes of stack below it, the code returns `{call}`'s value in RAX, keeps
// the callee-saved registers and RSP, and leaves memory as it was but for
// stores into its own room below that address (`Stack::Wrote`).
theorem {symbol}_native_returns<M>(fetch: FetchAccess<M>, data: ByteReadAccess<M>, last: List<BitVec(8)>, origin: BitVec(64),
    stack: Stack<M>(fetch, data){comma}{typed}):
    Site<M>(fetch, data, {prefix}_code(), last, origin).Returns(stack, asm_labels({prefix}_code())({label}),
        λ (i: Nat) (s: MachineState<M>) => ArgsIn({list}, argument_registers(), s.gprs) ∧ 120 * {label} <= i,
        stack.CalleePost({call}({arguments}))) {{
    {proved}
}}
", label = g + 1, room = 120 * (g + 1)));
    }
    Ok(Compiled { text, bytes, entry, entries })
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
fn marked_text(prefix: &str) -> String {
    format!("// Each function stores into the buffers its row of `{prefix}_tables` marks, and calls only callees whose rows its own meets.
theorem {prefix}_marked(): program_marked({prefix}_program(), {prefix}_tables()).IsTrue() {{ trivial }}")
}

/// `{prefix}_within`: every store of the program is into a buffer
/// `{prefix}_marks` marks, so a caller that lends those to write has lent
/// all the program stores into (`program_stores_marked`). A function at a
/// time, as [`quiet_text`] is.
fn within_text(prefix: &str, functions: usize) -> String {
    let (program, marks) = (format!("{prefix}_program()"), format!("{prefix}_marks()"));
    let mut text = format!("// Every store of the program is into a buffer `{prefix}_marks` marks.
theorem {prefix}_within_none(): program_stores_within({program}.drop({functions}), {marks}).IsTrue() {{ trivial }}\n");
    for k in 0..functions {
        let below = if k == 0 { "none".to_string() } else { (k - 1).to_string() };
        text.push_str(&format!("theorem {prefix}_within_head_{k}(): program_stores_within_head({program}.drop({d}), {marks}).IsTrue() {{ trivial }}
theorem {prefix}_within_{k}(): program_stores_within({program}.drop({d}), {marks}).IsTrue() {{
    program_stores_within_drop({program}, {marks}, {d}, {prefix}_within_head_{k}(), {prefix}_within_{below}())
}}
", d = functions - 1 - k));
    }
    text.push_str(&format!("theorem {prefix}_within(): program_stores_within({program}, {marks}).IsTrue() {{
    program_stores_within_drop_zero({program}, {marks}, {prefix}_within_{last}())
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
            _ => return Err("the lowering emitted an item the compiler does not state".into()),
        };
        items.push((name, item));
    }
    Ok(items)
}
