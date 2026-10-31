//! `compile-x86` through the verified lowering
//! (issues/function-ir-verified-lowering.md, round 4).
//!
//! The function and the functions it calls are reflected into a FunctionIR
//! program, and the certificate is what `function_ir_compile` says about it:
//! the program lowered by `lower_program` with the heuristic's placement,
//! evaluable, evaluating to the source function, and so returning the
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

/// The program for `source` when the verified lowering's fragment covers it.
pub(super) fn reflect(elab: &Elaborator, source: &str) -> Result<function_ir_source::ReflectedProgram, String> {
    function_ir_source::reflect_program(elab, source).map_err(|e| e.to_string())
}

pub(super) fn compile(elab: &Elaborator, prefix: &str, module: &str, program: &function_ir_source::ReflectedProgram)
    -> Result<Compiled, String>
{
    let root = &program.functions[program.root];
    let f = program.root;
    let mut definitions = String::new();
    for name in IMPORTS { definitions.push_str(&format!("import {name};\n")); }
    let mut owners: Vec<&str> = program.functions.iter().filter_map(|function| function.source_name.rsplit_once("::").map(|(owner, _)| owner)).collect();
    owners.sort();
    owners.dedup();
    for owner in owners { definitions.push_str(&format!("import {owner};\n")); }
    definitions.push_str(&format!("\n// The program, function `k` the one with `k` after it: {}.\n", program.functions.iter().map(|function| function.source_name.as_str()).collect::<Vec<_>>().join(", ")));
    // Each function by name; a loop's pieces too, so that its agreement
    // meets the program at them (`loop_then_eval`).
    for (k, function) in program.functions.iter().enumerate() {
        let name = format!("{prefix}_fn{k}");
        let text = match &function.looped {
            Some(looped) => {
                definitions.push_str(&format!("fn {name}_loop_body() → StructuredRegion {{\n    {}\n}}\n\n", looped.body.render()));
                definitions.push_str(&format!("fn {name}_loop_post() → StructuredRegion {{\n    {}\n}}\n\n", looped.post.render()));
                if let Some(prefix) = looped.measured.as_ref().and_then(|measured| measured.prefix.as_ref()) {
                    definitions.push_str(&format!("fn {name}_loop_bound() → StructuredRegion {{\n    {}\n}}\n\n", prefix.render()));
                }
                format!("Function(parameters := [{}], body := {}, result := {})", parameters(function.arity), loop_function_body(&name, looped), function.result)
            }
            None => function.render(),
        };
        definitions.push_str(&format!("fn {name}() → Function {{\n    {text}\n}}\n\n"));
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

    // Each function proved on its own, its calls answered by its callees'
    // sources; then the program by `program_eval_sources`.
    let sources = format!("{prefix}_sources()");
    let mut answers = "BitVec::zero()".to_string();
    for (k, function) in program.functions.iter().enumerate().rev() {
        let words: Vec<String> = (0..function.arity).map(|i| format!("words.word({i})")).collect();
        answers = format!("match g{k} {{ Zero => {}, Succ(g{}) => {answers} }}", function.answer(&words), k + 1);
    }
    let mut agreements = format!("// What each function computes: its source, a loop's bound its fuel.
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
    let agreement = format!("{agreements}
theorem {prefix}_sourced(): program_sourced({prefix}_program(), {sources}) {{
    {sourced}
}}

// The program's function {f} evaluates to the source function.
theorem {prefix}_agrees({typed}): program_eval({prefix}_program(), {f}, {list}) = {call} {{
    program_eval_sources({prefix}_program(), {prefix}_evaluable(), {sources}, {prefix}_sourced(), {f}, {list}, trivial)
}}
");
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
theorem {prefix}_evaluable(): program_evaluable({prefix}_program()).IsTrue() {{ trivial }}

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

/// Function `name`'s agreement with its source, its calls answered by
/// `sources`: by conversion, through an expansion, or as a loop.
fn function_agreement(name: &str, sources: &str, function: &function_ir_source::ProgramFunction) -> String {
    let arguments = arguments(function.arity);
    let typed = typed(&arguments);
    let list = format!("[{}]", arguments.join(", "));
    let answer = function.answer(&arguments);
    let joined = arguments.join(", ");
    let source = &function.source_name;
    if let Some(looped) = &function.looped {
        return loop_agreement(name, sources, looped, function);
    }
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

/// The agreement of a function that is a loop: by induction on the fuel
/// (`loop_eval_agrees`), the pass by cases on its comparisons, the source's
/// recursion abstracted as `later`.
fn loop_agreement(prefix: &str, call_of: &str, looped: &function_ir_source::ReflectedLoop, function: &function_ir_source::ProgramFunction) -> String {
    use function_ir_source::ids;
    let n = looped.arity;
    let xs: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    let cs: Vec<String> = (0..looped.conditions.len()).map(|k| format!("c{k}")).collect();
    let typed_more = |names: &[String], ty: &str| if names.is_empty() { String::new() } else { format!(", {}: {ty}", names.join(", ")) };
    let (x_typed, c_typed) = (typed_more(&xs, "BitVec(64)"), typed_more(&cs, "Bool"));
    let x_args = xs.join(", ");
    let conditions = looped.conditions.join(", ");
    let with = |list: &str| if list.is_empty() { String::new() } else { format!(", {list}") };
    let at_v: Vec<String> = looped.parameters.iter().map(|p| format!("v(64, {p})")).collect();
    let at_v = at_v.join(", ");
    let source = &function.source_name;
    let words: Vec<String> = (0..n).map(|i| format!("state.word({i})")).collect();
    let finish = |values: &str| format!("loop_finish({prefix}_loop_post(), {call_of}, {values}, [{}], {}, {})", ids(&looped.outputs), looped.exhausted, function.result);
    let step = format!("λ (pass: Valuation()) => {prefix}_loop_body().eval({call_of}, pass)");
    let pass_of = |values: &str| format!("loop_pass({step}, [{}], {}, {}, [{}], {}, later, r, v)", ids(&looped.parameters), looped.count, looped.exit,
        ids(&looped.next), finish(values));
    // The case split, along the pass's tree: each path's comparisons
    // literals, both sides compute.
    let cased = convoy(&|cs: &str| format!("{prefix}_pass_cases(later, {x_args}{cs}) = {prefix}_tree_cases(later, {x_args}{cs})"), &looped.split,
        &mut cs.clone());
    let by_cases = "split_all;\n    all_goals { refl }";
    let unfolds = if looped.decided { by_cases } else { "refl" };
    let base = if looped.base_decided {
        format!("fn {prefix}_base_expansion({x}) → BitVec(64) {{
    {base}
}}

theorem {prefix}_base_expanded(v, values: Valuation()):
    {fin}(LoopEnd(words_of(v, [{params}]), True)) = {prefix}_base_expansion({at_v}) {{ refl }}

theorem {prefix}_base_expands({x}): {prefix}_base_expansion({x_args}) = {prefix}_run(0, [{x_args}]) {{
    {by_cases}
}}

theorem {prefix}_base(v, values: Valuation()):
    {fin}(LoopEnd(words_of(v, [{params}]), True)) = {prefix}_run(0, words_of(v, [{params}])) {{
    trans({prefix}_base_expanded(v, values), {prefix}_base_expands({at_v}))
}}
", x = &x_typed[2..], base = looped.base, fin = finish("values"), params = ids(&looped.parameters))
    } else {
        format!("theorem {prefix}_base(v, values: Valuation()):
    {fin}(LoopEnd(words_of(v, [{params}]), True)) = {prefix}_run(0, words_of(v, [{params}])) {{ refl }}
", fin = finish("values"), params = ids(&looped.parameters))
    };
    let parameters = arguments(function.arity);
    let arguments = parameters.join(", ");
    let answer = function.answer(&parameters);
    let values = format!("Valuation::bind(Valuation::zero(), [{}], [{arguments}])", (0..parameters.len()).map(|i| i.to_string()).collect::<Vec<_>>().join(", "));
    let body = loop_function_body(prefix, looped);
    // The pass, the same for either recursion: its tree, as the program
    // evaluates it, and the two met by cases.
    let passes = format!("// A pass as the source's tree, then as the program evaluates it; its
// comparisons are `c0, …`.
fn {prefix}_tree_cases(later: List<BitVec(64)> → BitVec(64){x_typed}{c_typed}) → BitVec(64) {{
    {tree}
}}

fn {prefix}_tree(later: List<BitVec(64)> → BitVec(64){x_typed}) → BitVec(64) {{ {prefix}_tree_cases(later, {x_args}{conds}) }}

fn {prefix}_pass_cases(later: List<BitVec(64)> → BitVec(64){x_typed}{c_typed}) → BitVec(64) {{
    {pass}
}}

fn {prefix}_pass(later: List<BitVec(64)> → BitVec(64){x_typed}) → BitVec(64) {{ {prefix}_pass_cases(later, {x_args}{conds}) }}

theorem {prefix}_pass_cased(later: List<BitVec(64)> → BitVec(64){x_typed}{c_typed}):
    {prefix}_pass_cases(later, {x_args}{cs_args}) = {prefix}_tree_cases(later, {x_args}{cs_args}) {{
    {cased}
}}

theorem {prefix}_pass_tree(later: List<BitVec(64)> → BitVec(64){x_typed}): {prefix}_pass(later, {x_args}) = {prefix}_tree(later, {x_args}) {{
    {prefix}_pass_cased(later, {x_args}{conds})
}}

theorem {prefix}_pass_expanded(r: Nat, v, values: Valuation(), later: List<BitVec(64)> → BitVec(64)):
    {pass_values} = {prefix}_pass(later, {at_v}) {{ refl }}

theorem {prefix}_pass_agrees(r: Nat, v, values: Valuation(), later: List<BitVec(64)> → BitVec(64)):
    {pass_values} = {prefix}_tree(later, {at_v}) {{
    trans({prefix}_pass_expanded(r, v, values, later), {prefix}_pass_tree(later, {at_v}))
}}

// The function down to its loop.
theorem {prefix}_entered({typed}): {prefix}().eval({call_of}, [{arguments}]) = {body}.eval({call_of}, {values})(64, {result}) {{
    let spelled: ({prefix}().eval({call_of}, [{arguments}]) =
        Function(parameters := [{numbered}], body := {body}, result := {result}).eval({call_of}, [{arguments}])) = refl;
    trans(spelled, function_eval_body([{numbered}], {body}, {result}, {call_of}, [{arguments}]))
}}
", typed = typed(&parameters), numbered = (0..parameters.len()).map(|i| i.to_string()).collect::<Vec<_>>().join(", "), result = function.result,
        tree = looped.tree, pass = looped.pass, conds = with(&conditions), cs_args = with(&cs.join(", ")), pass_values = pass_of("values"));
    if let Some(measured) = &looped.measured {
        return measured_agreement(prefix, call_of, looped, measured, function, &passes);
    }
    format!("// `{source}` recurses on its fuel, and its function is a loop: the two agree by
// induction on the fuel, a pass at a time.
fn {prefix}_run(fuel: Nat, state: List<BitVec(64)>) → BitVec(64) {{ {source}(fuel, {words}) }}

{passes}
theorem {prefix}_unfolds(r: Nat{x_typed}): {source}(Succ(r), {x_args}) = {prefix}_tree(λ (state: List<BitVec(64)>) => {prefix}_run(r, state), {x_args}) {{
    {unfolds}
}}

{base}
// The loop's end made the result, and the source's recursion at the loop's
// fuel and inputs: each step meets the next at the same `loop_eval` and the
// same recursion, unfolded no further, so a constant fuel is never run.
theorem {prefix}_enters({typed}): {prefix}().eval({call_of}, [{arguments}]) =
    {fin_at}(loop_eval({step}, [{params}], {count}, {exit}, [{next}], {values}(64, {bound_id}).toNat(), words_of({values}, [{inputs}]))) {{
    trans({prefix}_entered({arguments}), loop_then_eval([{inputs}], {bound_id}, [{params}], {count}, {prefix}_loop_body(), {exit}, [{next}],
        [{outputs}], {exhausted}, {prefix}_loop_post(), {call_of}, {values}, {result}))
}}

theorem {prefix}_runs({typed}): {prefix}_run({values}(64, {bound_id}).toNat(), words_of({values}, [{inputs}])) = {answer} {{ refl }}

theorem {prefix}_agrees({typed}): {prefix}().eval({call_of}, [{arguments}]) = {answer} {{
    let values = {values};
    trans({prefix}_enters({arguments}), trans(loop_eval_agrees_from({step}, [{params}], {count}, {exit}, [{next}], trivial, refl,
        {fin}, λ (fuel: Nat) (state: List<BitVec(64)>) => {prefix}_run(fuel, state),
        λ v => {prefix}_base(v, values),
        λ r v => trans({prefix}_pass_agrees(r, v, values, λ (state: List<BitVec(64)>) => {prefix}_run(r, state)), sym({prefix}_unfolds(r, {at_v}))),
        values(64, {bound_id}).toNat(), values, [{inputs}], refl), {prefix}_runs({arguments})))
}}

", typed = typed(&parameters), outputs = ids(&looped.outputs), exhausted = looped.exhausted, result = function.result, fin_at = finish(&values),
        words = words.join(", "), fin = finish("values"), params = ids(&looped.parameters), count = looped.count, exit = looped.exit,
        next = ids(&looped.next), bound_id = looped.bound, inputs = ids(&looped.inputs))
}

/// The agreement of a function that is a loop bounded by its measure
/// (`function_ir_source::Measured`): by induction on the passes left
/// (`loop_eval_agrees_measured`), a pass by cases on its comparisons and by
/// `split_all` on the source's step, whose recursion is any `g` that some
/// `later` answers for (`_body_tree`). With no passes left the measure is
/// below one, so the step's recursion is refuted where it would be taken.
fn measured_agreement(prefix: &str, call_of: &str, looped: &function_ir_source::ReflectedLoop, measured: &function_ir_source::Measured,
    function: &function_ir_source::ProgramFunction, passes: &str) -> String
{
    use function_ir_source::ids;
    let n = looped.arity;
    let xs: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    let cs: Vec<String> = (0..looped.conditions.len()).map(|k| format!("c{k}")).collect();
    let x_args = xs.join(", ");
    let x_typed = format!("{x_args}: BitVec(64)");
    let x_lam: String = xs.iter().map(|x| format!("({x}: BitVec(64)) ")).collect();
    let c_typed = if cs.is_empty() { String::new() } else { format!(", {}: Bool", cs.join(", ")) };
    let cs_args: String = cs.iter().map(|c| format!(", {c}")).collect();
    let conds: String = looped.conditions.iter().map(|c| format!(", {c}")).collect();
    let source = &function.source_name;
    let words: Vec<String> = (0..n).map(|i| format!("state.word({i})")).collect();
    let at_v: Vec<String> = looped.parameters.iter().map(|p| format!("v(64, {p})")).collect();
    let at_v = at_v.join(", ");
    let params = ids(&looped.parameters);
    let finish = |values: &str| format!("loop_finish({prefix}_loop_post(), {call_of}, {values}, [{}], {}, {})", ids(&looped.outputs), looped.exhausted, function.result);
    let step = format!("λ (pass: Valuation()) => {prefix}_loop_body().eval({call_of}, pass)");
    let fin = finish("values");
    let rest = |r: &str, state: &str| format!("{fin}(loop_eval({step}, [{params}], {}, {}, [{}], {r}, {state}))", looped.count, looped.exit, ids(&looped.next));
    let later = format!("λ (state: List<BitVec(64)>) => {}", rest("r", "state"));
    let pass_values = format!("loop_pass({step}, [{params}], {}, {}, [{}], {fin}, {later}, r, v)", looped.count, looped.exit, ids(&looped.next));
    let first = "λ (state: List<BitVec(64)>) => state.word(0)";
    let mut assigned = cs.clone();
    let post_cased = convoy(&|cs: &str| format!("{prefix}_post_cases({x_args}{cs}) = {prefix}_tree_cases({first}, {x_args}{cs})"), &looped.split,
        &mut assigned);
    let parameters = arguments(function.arity);
    let arguments = parameters.join(", ");
    let answer = function.answer(&parameters);
    let bound = looped.bound;
    let inputs = ids(&looped.inputs);
    let bind = format!("Valuation::bind(Valuation::zero(), [{}], [{arguments}])", (0..parameters.len()).map(|i| i.to_string()).collect::<Vec<_>>().join(", "));
    // The valuation the loop starts from: after its bound.
    let values = match measured.prefix {
        Some(_) => format!("{prefix}_loop_bound().eval({call_of}, {bind})"),
        None => bind,
    };
    let lt = "nat::Nat::Lt";
    format!("// `{source}` recurses on its measure, and its function is a loop of at most
// as many passes: the two agree by induction on the passes left, a pass at a
// time.
fn {prefix}_measure_of({x_typed}) → Nat {{ @bitvec::BitVec::toNat(64, {word}) }}

fn {prefix}_measure(state: List<BitVec(64)>) → Nat {{ {prefix}_measure_of({words}) }}

fn {prefix}_run(r: Nat, state: List<BitVec(64)>, h: {lt}({prefix}_measure(state), Succ(r))) → BitVec(64) {{ {source}::rec(Succ(r), {words}, h) }}

{passes}
// The source's step is the pass's tree, its recursion answered by `later`.
theorem {prefix}_body_tree(k: Nat, g: ({x_typed}) → {lt}({prefix}_measure_of({x_args}), k) → BitVec(64), later: List<BitVec(64)> → BitVec(64),
    hg: ({x_typed}) → (p: {lt}({prefix}_measure_of({x_args}), k)) → g({x_args}, p) = later([{x_args}]), {x_typed},
    h: {lt}({prefix}_measure_of({x_args}), Succ(k))): {source}::body(k, g, {x_args}, h) = {prefix}_tree(later, {x_args}) {{
    let recurs: ({{{x_typed}}} → {{p: {lt}({prefix}_measure_of({x_args}), k)}} → g({x_args}, p) = later([{x_args}])) = hg;
    split_all;
    all_goals {{ recurs }}
}}

// A pass: going round, the recursion on the passes left.
theorem {prefix}_pass_measured(r: Nat, v, values: Valuation(), h: {lt}({prefix}_measure(words_of(v, [{params}])), Succ(Succ(r))),
    earlier: (state: List<BitVec(64)>) → state.len() = {n} → (p: {lt}({prefix}_measure(state), Succ(r))) →
        {rest_r} = {prefix}_run(r, state, p)):
    {pass_values} = {prefix}_run(Succ(r), words_of(v, [{params}]), h) {{
    trans({prefix}_pass_agrees(r, v, values, {later}), sym({prefix}_body_tree(Succ(r), λ {x_lam}(p: {lt}({prefix}_measure_of({x_args}), Succ(r))) =>
        {source}::rec(Succ(r), {x_args}, p), {later},
        λ {x_lam}(p: {lt}({prefix}_measure_of({x_args}), Succ(r))) => sym(earlier([{x_args}], refl, p)), {at_v}, h)))
}}

// With the passes run out, the tree once more, a recursion reading its next
// first word: none is taken, the measure being below one.
fn {prefix}_post_cases({x_typed}{c_typed}) → BitVec(64) {{
    {exhausted}
}}

fn {prefix}_post({x_typed}) → BitVec(64) {{ {prefix}_post_cases({x_args}{conds}) }}

theorem {prefix}_post_cased({x_typed}{c_typed}): {prefix}_post_cases({x_args}{cs_args}) = {prefix}_tree_cases({first}, {x_args}{cs_args}) {{
    {post_cased}
}}

theorem {prefix}_post_tree({x_typed}): {prefix}_post({x_args}) = {prefix}_tree({first}, {x_args}) {{
    {prefix}_post_cased({x_args}{conds})
}}

theorem {prefix}_post_expanded(v, values: Valuation()): {fin}(LoopEnd(words_of(v, [{params}]), True)) = {prefix}_post({at_v}) {{ refl }}

theorem {prefix}_base(v, values: Valuation(), h: {lt}({prefix}_measure(words_of(v, [{params}])), 1)):
    {fin}(LoopEnd(words_of(v, [{params}]), True)) = {prefix}_run(0, words_of(v, [{params}]), h) {{
    trans({prefix}_post_expanded(v, values), trans({prefix}_post_tree({at_v}), sym({prefix}_body_tree(0,
        λ {x_lam}(p: {lt}({prefix}_measure_of({x_args}), 0)) => {source}::rec(0, {x_args}, p), {first},
        λ {x_lam}(p: {lt}({prefix}_measure_of({x_args}), 0)) => false_elim(p), {at_v}, h))))
}}

// The loop's end made the result, and the source's recursion at a bound on
// its measure, the loop's.
theorem {prefix}_enters({typed}): {prefix}().eval({call_of}, [{arguments}]) =
    {fin_at}(loop_eval({step}, [{params}], {count}, {exit}, [{next}], {values}(64, {bound}).toNat(), words_of({values}, [{inputs}]))) {{
    trans({prefix}_entered({arguments}), loop_then_eval([{inputs}], {bound}, [{params}], {count}, {prefix}_loop_body(), {exit}, [{next}],
        [{outputs}], {exhausted_id}, {prefix}_loop_post(), {call_of}, {values}, {result}))
}}

theorem {prefix}_runs({typed}): {prefix}_run({values}(64, {bound}).toNat(), words_of({values}, [{inputs}]),
    nat::Nat::lt_succ_self({values}(64, {bound}).toNat())) = {answer} {{ refl }}

theorem {prefix}_agrees({typed}): {prefix}().eval({call_of}, [{arguments}]) = {answer} {{
    let values = {values};
    trans({prefix}_enters({arguments}), trans(loop_eval_agrees_measured({step}, [{params}], {count}, {exit}, [{next}], trivial,
        {fin}, λ (state: List<BitVec(64)>) => {prefix}_measure(state),
        λ (r: Nat) (state: List<BitVec(64)>) (h: {lt}({prefix}_measure(state), Succ(r))) => {prefix}_run(r, state, h),
        λ v h => {prefix}_base(v, values, h),
        λ r v h earlier => {prefix}_pass_measured(r, v, values, h, earlier),
        values(64, {bound}).toNat(), words_of(values, [{inputs}]), refl, nat::Nat::lt_succ_self(values(64, {bound}).toNat())),
        {prefix}_runs({arguments})))
}}

", word = measured.word, words = words.join(", "), exhausted = measured.exhausted, rest_r = rest("r", "state"), typed = typed(&parameters),
        fin_at = finish(&values), count = looped.count, exit = looped.exit, next = ids(&looped.next), outputs = ids(&looped.outputs),
        exhausted_id = looped.exhausted, result = function.result)
}

/// A case split along a pass's tree, from the comparisons `assigned`: at
/// each node a convoy on its comparison, both sides of `goal` (at the
/// comparisons as they then stand) computing; at each leaf `refl`.
fn convoy(goal: &dyn Fn(&str) -> String, split: &function_ir_source::Split, assigned: &mut Vec<String>) -> String {
    use function_ir_source::Split;
    match split {
        Split::Leaf => "refl".into(),
        Split::Node(k, no, yes) => {
            let scrutinee = assigned[*k].clone();
            assigned[*k] = format!("b{k}");
            let motive = goal(&assigned.iter().map(|c| format!(", {c}")).collect::<String>());
            assigned[*k] = "False".into();
            let when_false = convoy(goal, no, assigned);
            assigned[*k] = "True".into();
            let when_true = convoy(goal, yes, assigned);
            assigned[*k] = scrutinee.clone();
            format!("match {scrutinee} as λ b{k} => {motive} {{\n        False => {when_false},\n        True => {when_true},\n    }}")
        }
    }
}

/// A loop function's body, its loop's pieces by name: after the regions
/// computing a measured loop's bound.
fn loop_function_body(prefix: &str, looped: &function_ir_source::ReflectedLoop) -> String {
    use function_ir_source::ids;
    let body = format!("Compose(Loop([{}], {}, [{}], {}, {prefix}_loop_body(), {}, [{}], [{}], {}), {prefix}_loop_post())", ids(&looped.inputs), looped.bound,
        ids(&looped.parameters), looped.count, looped.exit, ids(&looped.next), ids(&looped.outputs), looped.exhausted);
    match looped.measured.as_ref().and_then(|measured| measured.prefix.as_ref()) {
        Some(_) => format!("Compose({prefix}_loop_bound(), {body})"),
        None => body,
    }
}

/// A function's parameter ids, as the reflector numbers them.
fn parameters(arity: usize) -> String { (0..arity).map(|i| i.to_string()).collect::<Vec<_>>().join(", ") }

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
