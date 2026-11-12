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
}

const IMPORTS: &[&str] = &["function_ir", "function_ir_eval", "function_ir_lower", "function_ir_lower_structured",
    "function_ir_lower_calls", "function_ir_compile", "x86_64", "x86_64_block", "x86_64_fetch", "x86_64_data_read",
    "x86_64_fetched_code", "x86_64_stack", "x86_64_asm", "x86_64_asm_runs", "x86_64_asm_table", "x86_64_stack_runs", "bitvec", "bool", "list",
    "logic", "nat", "option"];

/// What a program that is lent buffers needs besides: that it stores into
/// none, and the laws its buffers are lent under.
const LENT_IMPORTS: &[&str] = &["function_ir_writes", "function_ir_lower_reads", "x86_64_lending"];

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
}

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
        Shape { functions, root: functions - 1, arity, definitions, agreement, answer, lent: None }
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
        Shape { functions, root: functions - 1, arity, definitions, agreement, answer, lent: Some(counts) }
    }
}

/// A `runtime fn`'s [`Shape`]: how many functions its published program
/// has and how many words the function takes, read off the published
/// values; for one that reads spans (`lent`), how many buffers each
/// function of the program is lent as well.
pub(super) fn runtime_shape(elab: &Elaborator, prefix: &str, owner: &str, source: &str, lent: bool) -> Result<Shape, String> {
    let probe = format!("{prefix}_shape");
    let (imports, counts) = if lent { ("import function_ir_lower_calls;\n", format!("program_counts({source}::program)")) } else { ("", "[]".to_string()) };
    let text = format!("import {owner};\nimport runtime;\nimport rt;\nimport list;\nimport function_ir;\n{imports}
fn {prefix}_shape() → List<Nat> {{ Cons({source}::program.len(), Cons({source}::rt.params.len(), {counts})) }}\n");
    let mut fork = elab.fork();
    fork.elab_module_source(&probe, &text).map_err(|e| e.render(&text))?;
    let numbers = function_ir_source::evaluate_numbers(&fork, &format!("{probe}::{prefix}_shape")).map_err(|e| e.to_string())?;
    match numbers[..] {
        [_, arity, ..] if arity > 6 => Err(format!("`{source}` takes {arity} words{}: compile-x86 passes at most six, in registers",
            if lent { ", an address and a length for each span among them" } else { "" })),
        [functions, arity] if functions >= 1 && !lent => Ok(Shape::runtime(prefix, owner, source, functions as usize, arity as usize)),
        [functions, arity, ref counts @ ..] if functions >= 1 && lent && counts.len() == functions as usize =>
            Ok(Shape::runtime_lent(prefix, owner, source, functions as usize, arity as usize, counts.to_vec())),
        _ => Err(format!("`{source}::program` did not read back")),
    }
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
            // Which function, so the search for the node starts there
            // (issues/function-ir-planner-register-pressure.md).
            [] => return Err(format!("the verified lowering refused this program with the planner's placement: its function {k} of {m}, callees first")),
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
    let entry = match items.iter().rposition(|(name, _)| *name == f as u64 + 1) {
        Some(at) => offsets[at] as usize,
        None => return Err("the exported function's label is not in the code".into()),
    };
    if entry >= bytes.len() { return Err("the entry is past the code".into()); }

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
    if lent {
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
        λ (i: Nat) (s: MachineState<M>) => (ArgsIn({list}, argument_registers(), s.gprs) ∧ 72 * {label} <= i) ∧
            stack.LentOver({prefix}_lending(addresses, now), top, {f}, {list}, now)(i, s),
        stack.AnsweredOver({prefix}_lending(addresses, now), {call}, now)) {{
    compiled_returns_lent<M>({prefix}_program(), {prefix}_placement(), {prefix}_lending(addresses, now), {prefix}_code(), {prefix}_lowers(),
        {prefix}_evaluable(), {prefix}_quiet(), fetch, data, last, origin, stack, top, loan, {f}, trivial, {list}, trivial, now, {call},
        {prefix}_agrees(now{comma}{arguments}))
}}
", label = f + 1, room = 72 * (f + 1), arguments = parameters.join(", ")));
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
        λ (i: Nat) (s: MachineState<M>) => ArgsIn({list}, argument_registers(), s.gprs) ∧ 72 * {label} <= i,
        stack.CalleePost({call})) {{
    compiled_returns<M>({prefix}_program(), {prefix}_placement(), {prefix}_code(), {prefix}_lowers(), {prefix}_evaluable(),
        fetch, data, last, origin, stack, {f}, trivial, {list}, trivial, {call}, {prefix}_agrees({arguments}))
}}
", label = f + 1, room = 72 * (f + 1), arguments = parameters.join(", ")));
    }
    Ok(Compiled { text, bytes, entry })
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
