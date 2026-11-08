//! `compile-x86` through the verified lowering
//! (issues/function-ir-verified-lowering.md, round 4).
//!
//! The function and the functions it calls are reflected into a FunctionIR
//! program, and the certificate is what `function_ir_compile` says about it:
//! the program lowered by `lower_program` with the heuristic's placement,
//! evaluable (checked by `program_scan`, one pass over the program, and
//! `program_scan_evaluable`; issues/function-ir-evaluable-quadratic.md),
//! evaluating to the source function, and so returning the
//! source's value at the function's label. Nothing in it is about this
//! program's code beyond equations the kernel checks by evaluation. The
//! bytes and the entry offset are evaluated here, from the same
//! definitions, and stated in the certificate as literals.

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
    "x86_64_fetched_code", "x86_64_stack", "x86_64_asm", "x86_64_asm_runs", "x86_64_stack_runs", "bitvec", "bool", "list",
    "logic", "nat", "option"];

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
", evaluable = evaluable_text(prefix, functions), f = functions - 1, list = parameters.join(", "));
        Shape { functions, root: functions - 1, arity, definitions, agreement, answer }
    }
}

/// A `runtime fn`'s [`Shape`]: how many functions its published program
/// has and how many words the function takes, read off the published
/// values.
pub(super) fn runtime_shape(elab: &Elaborator, prefix: &str, owner: &str, source: &str) -> Result<Shape, String> {
    let probe = format!("{prefix}_shape");
    let text = format!("import {owner};\nimport runtime;\nimport rt;\nimport list;\nimport function_ir;\n
fn {prefix}_shape() → List<Nat> {{ [{source}::program.len(), {source}::rt.params.len()] }}\n");
    let mut fork = elab.fork();
    fork.elab_module_source(&probe, &text).map_err(|e| e.render(&text))?;
    match function_ir_source::evaluate_numbers(&fork, &format!("{probe}::{prefix}_shape")).map_err(|e| e.to_string())?[..] {
        [_, arity] if arity > 6 => Err(format!("`{source}` takes {arity} words: compile-x86 passes at most six, in registers")),
        [functions, arity] if functions >= 1 => Ok(Shape::runtime(prefix, owner, source, functions as usize, arity as usize)),
        _ => Err(format!("`{source}::program` did not read back")),
    }
}

pub(super) fn compile(elab: &Elaborator, prefix: &str, module: &str, program: &Shape) -> Result<Compiled, String> {
    let f = program.root;
    let mut definitions = String::new();
    for name in IMPORTS { definitions.push_str(&format!("import {name};\n")); }
    definitions.push_str(&program.definitions);
    let m = program.functions;
    // Evaluated on a fork, which only defines: the certificate's statements
    // are the session's to check.
    let probe = format!("{module}_probe");
    let mut steps = String::new();
    for k in 0..m {
        let emitted = if k == 0 {
            format!("{prefix}_fn0().emit(Start, 0, plan_program({prefix}_program()), {m})")
        } else {
            format!("match {prefix}_emitted_{}() {{ None => None, Some(b) => {prefix}_fn{k}().emit(b.prog, {k}, b.placement, b.names) }}", k - 1)
        };
        steps.push_str(&format!("fn {prefix}_emitted_{k}() → Option<Emitted> {{ {emitted} }}
fn {prefix}_step_{k}() → List<Nat> {{ match {prefix}_emitted_{k}() {{ None => [], Some(e) => [prog_depth(e.prog), e.placement.len(), e.names] }} }}
"));
    }
    let probes = format!("{definitions}{steps}
fn {prefix}_lowered() → Option<Prog> {{
    match {prefix}_emitted_{last}() {{ None => None, Some(e) => match e.prog.laid_out() {{ False => None, True => Some(e.prog) }} }}
}}
fn {prefix}_placement_numbers() → List<Nat> {{ plan_program({prefix}_program()).map(λ (place: Place) => place.number()) }}
fn {prefix}_refused() → Nat {{ match {prefix}_lowered() {{ None => 1, Some(_) => 0 }} }}
fn {prefix}_code() → Prog {{ match {prefix}_lowered() {{ None => Start, Some(code) => code }} }}
fn {prefix}_code_numbers() → List<Nat> {{ {prefix}_code().numbers() }}
fn {prefix}_lens() → List<Nat> {{ asm_lens({prefix}_code()) }}
fn {prefix}_byte_numbers() → List<Nat> {{ assemble(no_fills(), {prefix}_code(), []).map(λ (b: BitVec(8)) => b.toNat()) }}
fn {prefix}_entry() → Nat {{ asm_labels({prefix}_code())({}) }}
", f + 1, last = m - 1);
    let mut fork = elab.fork();
    fork.elab_module_source(&probe, &probes).map_err(|e| e.render(&probes))?;
    let name = |item: &str| format!("{probe}::{prefix}_{item}");
    let evaluate = |item: &str| function_ir_source::evaluate_number(&fork, &name(item)).map_err(|e| format!("`{prefix}_{item}`: {e}"));
    let numbers = |item: &str| function_ir_source::evaluate_numbers(&fork, &name(item)).map_err(|e| format!("`{prefix}_{item}`: {e}"));
    if evaluate("refused")? != 0 {
        return Err("the verified lowering refused this program with the planner's placement".into());
    }
    let items = read_items(&numbers("code_numbers")?)?;
    let lens = numbers("lens")?;
    let bytes = numbers("byte_numbers")?
        .into_iter().map(|b| u8::try_from(b).map_err(|_| "a byte above 255".to_string())).collect::<Result<Vec<u8>, String>>()?;
    let entry = usize::try_from(evaluate("entry")?).map_err(|_| "an implausible entry".to_string())?;
    if entry >= bytes.len() { return Err("the entry is past the code".into()); }
    if lens.len() != items.len() || lens.iter().sum::<u64>() != bytes.len() as u64 {
        return Err("the items' lengths do not cover the code".into());
    }
    let placement = numbers("placement_numbers")?.into_iter().map(|n| match n {
        16 => Ok("Folded".to_string()),
        n => GPRS.get(n as usize).map(|gpr| format!("Into({gpr})")).ok_or_else(|| "a malformed placement".to_string()),
    }).collect::<Result<Vec<String>, String>>()?;
    // (items so far, places left, next label) after each function.
    let mut after = Vec::new();
    for k in 0..m {
        match numbers(&format!("step_{k}"))?[..] {
            [count, left, names] if count as usize <= items.len() && left as usize <= placement.len() => after.push((count as usize, left as usize, names)),
            _ => return Err(format!("function {k}'s emission did not read back")),
        }
    }
    if after.last().map(|step| step.0) != Some(items.len()) || after.windows(2).any(|w| w[1].0 < w[0].0 || w[1].1 > w[0].1) {
        return Err("the functions' emissions do not make the code".into());
    }

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
    let rest = |left: usize| format!("[{}]", placement[placement.len() - left..].join(", "));
    text.push_str(&format!("
// The placement the heuristic chose; the theorem holds for any.
fn {prefix}_placement() → List<Place> {{ {} }}
", rest(placement.len())));
    let mut before = ("Start".to_string(), format!("{prefix}_placement()"), m as u64);
    let mut taken = 0;
    for (k, &(count, left, names)) in after.iter().enumerate() {
        let mut code = if k == 0 { "Start".to_string() } else { format!("{prefix}_code_{}()", k - 1) };
        for (name, item) in &items[taken..count] { code = format!("At({code},\n    {name}, {item})"); }
        taken = count;
        let earlier = if k == 0 { "Nil".to_string() } else { format!("{prefix}_first_{}()", k - 1) };
        let started = if k == 0 { format!("emit_functions_start({prefix}_placement(), {m})") } else { format!("{prefix}_emitted_{}()", k - 1) };
        text.push_str(&format!("
fn {prefix}_code_{k}() → Prog {{
    {code}
}}

fn {prefix}_rest_{k}() → List<Place> {{ {rest} }}

theorem {prefix}_emits_{k}(): EmitsAs({prefix}_fn{k}().emit({prog}, {k}, {places}, {labels}), {prefix}_code_{k}(), {prefix}_rest_{k}(), {names}) {{
    ⟨refl, ⟨refl, refl⟩⟩
}}

theorem {prefix}_emitted_{k}(): EmitsAs(emit_functions({prefix}_first_{k}(), {prefix}_placement(), {m}), {prefix}_code_{k}(), {prefix}_rest_{k}(), {names}) {{
    emit_functions_next({prefix}_fn{k}(), {earlier}, {prefix}_placement(), {m}, {prog}, {places}, {labels}, {started},
        {prefix}_code_{k}(), {prefix}_rest_{k}(), {names}, {prefix}_emits_{k}())
}}
", rest = rest(left), prog = before.0, places = before.1, labels = before.2));
        before = (format!("{prefix}_code_{k}()"), format!("{prefix}_rest_{k}()"), names);
    }
    text.push_str(&format!("
// The code: what `lower_program` computes with that placement.
fn {prefix}_code() → Prog {{ {prefix}_code_{last}() }}

{layout}
theorem {prefix}_holes(): {prefix}_code().no_holes().IsTrue() {{ trivial }}

theorem {prefix}_laid(): {prefix}_code().laid_out().IsTrue() {{
    {prefix}_code().laid_out_intro({prefix}_holes(), {prefix}_unique_0(), {prefix}_lands_0(), {prefix}_named_0())
}}

theorem {prefix}_lowers(): lower_program({prefix}_program(), {prefix}_placement()) = Some({prefix}_code()) {{
    lower_program_emitted({prefix}_program(), {prefix}_placement(), {prefix}_code(), {prefix}_rest_{last}(), {labels}, {prefix}_emitted_{last}(),
        {prefix}_laid())
}}
", last = m - 1, labels = before.2, layout = layout(prefix, items.len())));
    text.push_str(&format!("
{agreement}
// The published bytes, a piece at a time from the last item: no one
// statement evaluates more of the code than a piece.
"));
    text.push_str(&byte_pieces(prefix, &cut_pieces(&lens, PIECE), &bytes));
    text.push_str(&format!("
theorem {prefix}_entry_at(): asm_labels({prefix}_code())({label}) = {entry} {{ refl }}

// Called at its label with its arguments in RDI, RSI, …, a return address
// at RSP and {room} bytes of stack below it, the code returns the source
// function's value in RAX, keeps the callee-saved registers and RSP, and
// leaves the stack above its return address as it was: resident anywhere,
// whatever follows it, with any stack meeting the `Stack` laws.
theorem {prefix}_returns<M>(fetch: FetchAccess<M>, data: ByteReadAccess<M>, last: List<BitVec(8)>, origin: BitVec(64),
    stack: Stack<M>(fetch, data){comma}{typed}):
    Site<M>(fetch, data, {prefix}_code(), last, origin).Returns(stack, asm_labels({prefix}_code())({label}),
        λ (i: Nat) (s: MachineState<M>) => ArgsIn({list}, argument_registers(), s.gprs) ∧ 72 * {label} <= i,
        stack.CalleePost({call})) {{
    compiled_returns<M>({prefix}_program(), {prefix}_placement(), {prefix}_code(), {prefix}_lowers(), {prefix}_evaluable(),
        fetch, data, last, origin, stack, {f}, trivial, {list}, trivial, {call}, {prefix}_agrees({arguments}))
}}
", label = f + 1, room = 72 * (f + 1), comma = if parameters.is_empty() { "" } else { ", " },
        arguments = parameters.join(", ")));
    Ok(Compiled { text, bytes, entry })
}

/// `{prefix}_evaluable`: the program's functions evaluable, checked by
/// `program_scan` (one pass over each function,
/// issues/function-ir-evaluable-quadratic.md) a function per declaration,
/// so the kernel's per-declaration fuel bounds the largest function rather
/// than the program; `program_scan_drop` joins them, from the last
/// function (`{prefix}_scans_{k}` covers functions `0..=k`).
fn evaluable_text(prefix: &str, functions: usize) -> String {
    let mut text = format!("theorem {prefix}_scans_none(): program_scan({prefix}_program().drop({functions})).IsTrue() {{ trivial }}\n");
    for k in 0..functions {
        let below = if k == 0 { "none".to_string() } else { (k - 1).to_string() };
        text.push_str(&format!("theorem {prefix}_scanned_{k}(): program_scan_head({prefix}_program().drop({d})).IsTrue() {{ trivial }}
theorem {prefix}_scans_{k}(): program_scan({prefix}_program().drop({d})).IsTrue() {{
    program_scan_drop({prefix}_program(), {d}, {prefix}_scanned_{k}(), {prefix}_scans_{below}())
}}
", d = functions - 1 - k));
    }
    text.push_str(&format!("theorem {prefix}_evaluable(): program_evaluable({prefix}_program()).IsTrue() {{
    program_scan_evaluable({prefix}_program(), program_scan_drop_zero({prefix}_program(), {prefix}_scans_{last}()))
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
    let evaluable = evaluable_text(prefix, program.functions.len());
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

/// The layout checks a stretch of items at a time, from the first: their
/// names against the items before them, their jumps against the whole
/// code's labels. Each check reads the whole code per item, so one
/// statement over all of it would be quadratic in the program; a stretch
/// is short enough that its items times the program stay under `READS`.
pub(super) fn layout(prefix: &str, total: usize) -> String {
    let stretch = (READS / total.max(1)).clamp(1, 16);
    let mut text = String::new();
    let mut back = total - total % stretch;
    if back == total && total > 0 { back -= stretch; }
    let mut earlier = None;
    loop {
        let n = (total - back).min(stretch);
        let at = format!("asm_back({prefix}_code(), {back})");
        let chained = |what: &str| earlier.map_or("trivial".to_string(), |e: usize| format!("{prefix}_{what}_{e}()"));
        text.push_str(&format!("theorem {prefix}_fresh_{back}(): {at}.fresh_names({n}).IsTrue() {{ trivial }}

theorem {prefix}_unique_{back}(): {at}.names_unique().IsTrue() {{
    names_unique_back({n}, {at}, {prefix}_fresh_{back}(), {unique})
}}

theorem {prefix}_landing_{back}(): jumps_land_last(asm_labels({prefix}_code()), {at}, {n}).IsTrue() {{ trivial }}

theorem {prefix}_lands_{back}(): jumps_land_in(asm_labels({prefix}_code()), {at}).IsTrue() {{
    jumps_land_back(asm_labels({prefix}_code()), {n}, {at}, {prefix}_landing_{back}(), {lands})
}}

theorem {prefix}_naming_{back}(): targets_named_last({prefix}_code(), {at}, {n}).IsTrue() {{ trivial }}

theorem {prefix}_named_{back}(): targets_named_in({prefix}_code(), {at}).IsTrue() {{
    targets_named_back({prefix}_code(), {n}, {at}, {prefix}_naming_{back}(), {named})
}}

", unique = chained("unique"), lands = chained("lands"), named = chained("named")));
        earlier = Some(back);
        if back == 0 { break; }
        back -= stretch;
    }
    text
}

/// Item reads a layout statement may make, its items times the program's:
/// a jump's check reads the program to find its own offset and its
/// target's, so this keeps a statement well inside a declaration's fuel.
const READS: usize = 4096;

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

/// `{prefix}_code()`'s bytes stated a piece at a time, from the last item,
/// so no one statement evaluates more of the code than a piece; then
/// `{prefix}_bytes`, the whole assembly as the pieces' concatenation.
pub(super) fn byte_pieces(prefix: &str, pieces: &[Piece], bytes: &[u8]) -> String {
    let mut text = String::new();
    let mut end = bytes.len();
    for (c, Piece { back, count, start }) in pieces.iter().enumerate() {
        let literal: Vec<String> = bytes[*start..end].iter().map(|&b| super::word_literal(8, u64::from(b))).collect();
        end = *start;
        text.push_str(&format!("fn {prefix}_piece_{c}() → List<BitVec(8)> {{ [{}] }}\n", literal.join(", ")));
        text.push_str(&format!("theorem {prefix}_piece_{c}_is(): asm_code_after(no_fills(), asm_labels({prefix}_code()), asm_back({prefix}_code(), {back}), {count}) = {prefix}_piece_{c}() {{ refl }}\n"));
    }
    let m = pieces.len();
    let back: usize = pieces.iter().map(|piece| piece.count).sum();
    text.push_str(&format!("
// The code up to each piece's start, from the program's.
fn {prefix}_upto_{m}() → List<BitVec(8)> {{ [] }}
theorem {prefix}_upto_{m}_is(): asm_code(no_fills(), asm_labels({prefix}_code()), asm_back({prefix}_code(), {back})) = {prefix}_upto_{m}() {{ refl }}
"));
    for (c, Piece { back, count, .. }) in pieces.iter().enumerate().rev() {
        let next = c + 1;
        text.push_str(&format!("fn {prefix}_upto_{c}() → List<BitVec(8)> {{ {prefix}_upto_{next}() ++ {prefix}_piece_{c}() }}
theorem {prefix}_upto_{c}_is(): asm_code(no_fills(), asm_labels({prefix}_code()), asm_back({prefix}_code(), {back})) = {prefix}_upto_{c}() {{
    trans(asm_code_back(no_fills(), asm_labels({prefix}_code()), {count}, asm_back({prefix}_code(), {back})),
        trans(cong_fn<List<BitVec(8)>, List<BitVec(8)>>(λ x => x ++ asm_code_after(no_fills(), asm_labels({prefix}_code()), asm_back({prefix}_code(), {back}), {count}), {prefix}_upto_{next}_is()),
            cong_fn<List<BitVec(8)>, List<BitVec(8)>>(λ x => {prefix}_upto_{next}() ++ x, {prefix}_piece_{c}_is())))
}}
"));
    }
    text.push_str(&format!("
theorem {prefix}_bytes(): assemble(no_fills(), {prefix}_code(), []) = {prefix}_upto_0() {{
    trans(List::append_nil(asm_code(no_fills(), asm_labels({prefix}_code()), {prefix}_code())), {prefix}_upto_0_is())
}}
"));
    text
}

const GPRS: [&str; 16] = ["Rax", "Rcx", "Rdx", "Rbx", "Rsp", "Rbp", "Rsi", "Rdi", "R8", "R9", "R10", "R11", "R12", "R13", "R14", "R15"];
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
