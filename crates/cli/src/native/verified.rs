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
    let source = &root.source_name;
    let mut definitions = String::new();
    for name in IMPORTS { definitions.push_str(&format!("import {name};\n")); }
    let mut owners: Vec<&str> = program.functions.iter().flat_map(|function| std::iter::once(&function.source_name).chain(function.looped.as_ref().map(|looped| &looped.source_name)))
        .filter_map(|name| name.rsplit_once("::").map(|(owner, _)| owner)).collect();
    owners.sort();
    owners.dedup();
    for owner in owners { definitions.push_str(&format!("import {owner};\n")); }
    definitions.push_str(&format!("\n// The program, function `k` the one with `k` after it: {}.\n", program.functions.iter().map(|function| function.source_name.as_str()).collect::<Vec<_>>().join(", ")));
    // The exported function is the last, so the first the program lists;
    // the others answer its calls.
    let earlier: Vec<String> = program.functions[..f].iter().rev().map(|function| function.render()).collect();
    // A loop's pieces by name, so that its agreement meets the program at
    // them (`loop_then_eval`).
    let root_text = match &root.looped {
        Some(looped) => {
            let tail = format!("Compose({}, {prefix}_loop_post())", looped_region(prefix, looped));
            let body = if looped.prefix.is_some() { format!("Compose({prefix}_prefix(), {tail})") } else { tail };
            let parameters: Vec<String> = (0..root.arity).map(|id| id.to_string()).collect();
            let mut pieces = String::new();
            if let Some(region) = &looped.prefix { pieces.push_str(&format!("fn {prefix}_prefix() → StructuredRegion {{\n    {}\n}}\n\n", region.render())); }
            pieces.push_str(&format!("fn {prefix}_loop_body() → StructuredRegion {{\n    {}\n}}\n\n", looped.body.render()));
            pieces.push_str(&format!("fn {prefix}_loop_post() → StructuredRegion {{\n    {}\n}}\n\n", looped.post.render()));
            definitions.push_str(&pieces);
            format!("Function(parameters := [{}], body := {body}, result := {})", parameters.join(", "), root.result)
        }
        None => root.render(),
    };
    definitions.push_str(&format!("fn {prefix}_root() → Function {{\n    {root_text}\n}}\n\n"));
    definitions.push_str(&format!("fn {prefix}_earlier() → List<Function> {{\n    [{}]\n}}\n\n", earlier.join(",\n    ")));
    definitions.push_str(&format!("fn {prefix}_program() → List<Function> {{ Cons({prefix}_root(), {prefix}_earlier()) }}\n\n"));

    // Evaluated on a fork, which only defines: the certificate's statements
    // are the session's to check.
    let probe = format!("{module}_probe");
    let probes = format!("{definitions}
fn {prefix}_lowered() → Option<Prog> {{ lower_program_planned({prefix}_program()) }}
fn {prefix}_refused() → Nat {{ match {prefix}_lowered() {{ None => 1, Some(_) => 0 }} }}
fn {prefix}_code() → Prog {{ match {prefix}_lowered() {{ None => Start, Some(code) => code }} }}
fn {prefix}_code_numbers() → List<Nat> {{ {prefix}_code().numbers() }}
fn {prefix}_lens() → List<Nat> {{ asm_lens({prefix}_code()) }}
fn {prefix}_byte_numbers() → List<Nat> {{ assemble(no_fills(), {prefix}_code(), []).map(λ (b: BitVec(8)) => b.toNat()) }}
fn {prefix}_entry() → Nat {{ asm_labels({prefix}_code())({}) }}
", f + 1);
    let mut fork = elab.fork();
    fork.elab_module_source(&probe, &probes).map_err(|e| e.render(&probes))?;
    let name = |item: &str| format!("{probe}::{prefix}_{item}");
    let evaluate = |item: &str| function_ir_source::evaluate_number(&fork, &name(item)).map_err(|e| e.to_string());
    let numbers = |item: &str| function_ir_source::evaluate_numbers(&fork, &name(item)).map_err(|e| e.to_string());
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

    let parameters: Vec<String> = (0..root.arity).map(|i| format!("a{i}")).collect();
    let typed = if parameters.is_empty() { String::new() } else { format!("{}: BitVec(64)", parameters.join(", ")) };
    let list = format!("[{}]", parameters.join(", "));
    let call = format!("{source}({})", parameters.join(", "));
    // A source that decides a connective or a helper is its expansion by
    // case analysis; the program is the expansion by conversion.
    let agreement = if let Some(looped) = &root.looped {
        loop_agreement(prefix, f, looped, &parameters, &call)
    } else if root.decided {
        format!("// The program's function {f} evaluates to the decision tree it compiles,
// spelled in the source's operations, and that is the source function by
// case analysis on its comparisons.
fn {prefix}_expansion({typed}) → BitVec(64) {{
    {expansion}
}}

theorem {prefix}_expanded({typed}): program_eval({prefix}_program(), {f}, {list}) = {prefix}_expansion({arguments}) {{ refl }}

theorem {prefix}_expands({typed}): {prefix}_expansion({arguments}) = {call} {{
    split_all;
    all_goals {{ refl }}
}}

theorem {prefix}_agrees({typed}): program_eval({prefix}_program(), {f}, {list}) = {call} {{
    trans({prefix}_expanded({arguments}), {prefix}_expands({arguments}))
}}
", expansion = root.expansion, arguments = parameters.join(", "))
    } else {
        format!("// The program's function {f} evaluates to the source function.
theorem {prefix}_agrees({typed}): program_eval({prefix}_program(), {f}, {list}) = {call} {{ refl }}
")
    };
    let mut code = "Start".to_string();
    for (name, item) in &items { code = format!("At({code},\n    {name}, {item})"); }
    let mut text = definitions;
    // The code is stated once, as the literal the lowering computes, so no
    // later statement evaluates the lowering again: a declaration's fuel is
    // its own, and the lowering is most of what one could spend.
    text.push_str(&format!("
// The code: what `lower_program` computes with the heuristic's placement.
fn {prefix}_code() → Prog {{
    {code}
}}

theorem {prefix}_lowers(): lower_program({prefix}_program(), plan_program({prefix}_program())) = Some({prefix}_code()) {{ refl }}

theorem {prefix}_evaluable(): program_evaluable({prefix}_program()).IsTrue() {{ trivial }}

{agreement}
// The published bytes, a piece at a time from the last item: no one
// statement evaluates more of the code than a piece.
"));
    // Pieces of whole items, about `PIECE` bytes each, from the end.
    let mut at = bytes.len();
    let mut back = 0;
    let mut pieces: Vec<(usize, usize, usize)> = Vec::new(); // (back offset, items, start byte)
    let mut items_in = 0;
    let mut start = at;
    for len in lens.iter().rev() {
        start -= *len as usize;
        items_in += 1;
        if at - start >= PIECE {
            pieces.push((back, items_in, start));
            back += items_in;
            items_in = 0;
            at = start;
        }
    }
    if items_in > 0 { pieces.push((back, items_in, start)); back += items_in; }
    let mut end = bytes.len();
    for (c, (back, count, start)) in pieces.iter().enumerate() {
        let literal: Vec<String> = bytes[*start..end].iter().map(|b| format!("@bitvec::BitVec::ofNat(8, {b})")).collect();
        end = *start;
        text.push_str(&format!("fn {prefix}_piece_{c}() → List<BitVec(8)> {{ [{}] }}\n", literal.join(", ")));
        text.push_str(&format!("theorem {prefix}_piece_{c}_is(): asm_code_after(no_fills(), asm_labels({prefix}_code()), asm_back({prefix}_code(), {back}), {count}) = {prefix}_piece_{c}() {{ refl }}\n"));
    }
    let m = pieces.len();
    text.push_str(&format!("
// The code up to each piece's start, from the program's.
fn {prefix}_upto_{m}() → List<BitVec(8)> {{ [] }}
theorem {prefix}_upto_{m}_is(): asm_code(no_fills(), asm_labels({prefix}_code()), asm_back({prefix}_code(), {back})) = {prefix}_upto_{m}() {{ refl }}
"));
    for (c, (back, count, _)) in pieces.iter().enumerate().rev() {
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
    compiled_returns<M>({prefix}_program(), plan_program({prefix}_program()), {prefix}_code(), {prefix}_lowers(), {prefix}_evaluable(),
        fetch, data, last, origin, stack, {f}, trivial, {list}, trivial, {call}, {prefix}_agrees({arguments}))
}}
", label = f + 1, room = 72 * (f + 1), comma = if parameters.is_empty() { "" } else { ", " },
        arguments = parameters.join(", ")));
    Ok(Compiled { text, bytes, entry })
}

/// The agreement of a function that ends in a loop: by induction on the
/// fuel (`loop_eval_agrees`), the pass by cases on its comparisons, the
/// source's recursion abstracted as `later`.
fn loop_agreement(prefix: &str, f: usize, looped: &function_ir_source::ReflectedLoop, parameters: &[String], call: &str) -> String {
    use function_ir_source::{ids, Split};
    let n = looped.arity;
    let xs: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    let cs: Vec<String> = (0..looped.conditions.len()).map(|k| format!("c{k}")).collect();
    let typed = |names: &[String], ty: &str| if names.is_empty() { String::new() } else { format!(", {}: {ty}", names.join(", ")) };
    let (x_typed, c_typed) = (typed(&xs, "BitVec(64)"), typed(&cs, "Bool"));
    let x_args = xs.join(", ");
    let conditions = looped.conditions.join(", ");
    let with = |list: &str| if list.is_empty() { String::new() } else { format!(", {list}") };
    let at_v: Vec<String> = looped.parameters.iter().map(|p| format!("v(64, {p})")).collect();
    let at_v = at_v.join(", ");
    let source = &looped.source_name;
    let words: Vec<String> = (0..n).map(|i| format!("state.word({i})")).collect();
    let call_of = format!("program_eval({prefix}_earlier())");
    let finish = |values: &str| format!("loop_finish({prefix}_loop_post(), {call_of}, {values}, [{}], {}, {})", ids(&looped.outputs), looped.exhausted, f_result(parameters));
    let step = format!("λ (pass: Valuation()) => {prefix}_loop_body().eval({call_of}, pass)");
    let pass_of = |values: &str| format!("loop_pass({step}, [{}], {}, {}, [{}], {}, later, r, v)", ids(&looped.parameters), looped.count, looped.exit,
        ids(&looped.next), finish(values));
    // The case split, along the pass's tree: each path's comparisons
    // literals, both sides compute.
    fn convoy(prefix: &str, x_args: &str, split: &Split, assigned: &mut Vec<String>) -> String {
        match split {
            Split::Leaf => "refl".into(),
            Split::Node(k, no, yes) => {
                let scrutinee = assigned[*k].clone();
                let goal = |assigned: &[String]| format!("{prefix}_pass_cases(later, {x_args}{}) = {prefix}_tree_cases(later, {x_args}{})",
                    assigned.iter().map(|c| format!(", {c}")).collect::<String>(), assigned.iter().map(|c| format!(", {c}")).collect::<String>());
                assigned[*k] = format!("b{k}");
                let motive = goal(assigned);
                assigned[*k] = "False".into();
                let when_false = convoy(prefix, x_args, no, assigned);
                assigned[*k] = "True".into();
                let when_true = convoy(prefix, x_args, yes, assigned);
                assigned[*k] = scrutinee.clone();
                format!("match {scrutinee} as λ b{k} => {motive} {{\n        False => {when_false},\n        True => {when_true},\n    }}")
            }
        }
    }
    let mut assigned = cs.clone();
    let cased = convoy(prefix, &x_args, &looped.split, &mut assigned);
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
    let arguments = parameters.join(", ");
    let bound = parameters.iter().map(|a| a.as_str()).collect::<Vec<_>>();
    let bind = format!("Valuation::bind(Valuation::zero(), [{}], [{}])", (0..bound.len()).map(|i| i.to_string()).collect::<Vec<_>>().join(", "), bound.join(", "));
    let values = match &looped.prefix {
        Some(_) => format!("{prefix}_prefix().eval({call_of}, {bind})"),
        None => bind.clone(),
    };
    let root_parameters = (0..parameters.len()).map(|i| i.to_string()).collect::<Vec<_>>().join(", ");
    let tail = format!("Compose({}, {prefix}_loop_post())", looped_region(prefix, looped));
    let root_body = if looped.prefix.is_some() { format!("Compose({prefix}_prefix(), {tail})") } else { tail.clone() };
    let into_body = match &looped.prefix {
        Some(_) => format!("trans(function_eval_body([{root_parameters}], {root_body}, {result}, {call_of}, [{arguments}]),\n            compose_eval({prefix}_prefix(), {tail}, {call_of}, {bind}, {result}))",
            result = parameters.len(), arguments = parameters.join(", ")),
        None => format!("function_eval_body([{root_parameters}], {root_body}, {}, {call_of}, [{}])", parameters.len(), parameters.join(", ")),
    };
    let typed_arguments = if parameters.is_empty() { String::new() } else { format!("{}: BitVec(64)", arguments) };
    format!("// The program's function {f} ends in a loop, `{source}` recursing on its
// fuel: the two agree by induction on the fuel, a pass at a time.
fn {prefix}_run(fuel: Nat, state: List<BitVec(64)>) → BitVec(64) {{ {source}(fuel, {words}) }}

// A pass as the source's tree, then as the program evaluates it; its
// comparisons are `c0, …`.
fn {prefix}_tree_cases(later: List<BitVec(64)> → BitVec(64){x_typed}{c_typed}) → BitVec(64) {{
    {tree}
}}

fn {prefix}_tree(later: List<BitVec(64)> → BitVec(64){x_typed}) → BitVec(64) {{ {prefix}_tree_cases(later, {x_args}{conds}) }}

fn {prefix}_pass_cases(later: List<BitVec(64)> → BitVec(64){x_typed}{c_typed}) → BitVec(64) {{
    {pass}
}}

fn {prefix}_pass(later: List<BitVec(64)> → BitVec(64){x_typed}) → BitVec(64) {{ {prefix}_pass_cases(later, {x_args}{conds}) }}

theorem {prefix}_unfolds(r: Nat{x_typed}): {source}(Succ(r), {x_args}) = {prefix}_tree(λ (state: List<BitVec(64)>) => {prefix}_run(r, state), {x_args}) {{
    {unfolds}
}}

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

{base}
// The program down to its loop, the loop's end made the result, and the
// source's recursion at the loop's fuel and inputs: each step meets the
// next at the same `loop_eval` and the same recursion, unfolded no
// further, so a constant fuel is never run.
theorem {prefix}_entered({typed_arguments}): program_eval({prefix}_program(), {f}, [{arguments}]) =
    Compose({looped}, {prefix}_loop_post()).eval({call_of}, {at})(64, {result}) {{
    let listed: (program_eval({prefix}_program(), {f}, [{arguments}]) =
        program_eval(Cons({prefix}_root(), {prefix}_earlier()), {prefix}_earlier().len(), [{arguments}])) = refl;
    let spelled: ({prefix}_root().eval({call_of}, [{arguments}]) =
        Function(parameters := [{root_parameters}], body := {root_body}, result := {result}).eval({call_of}, [{arguments}])) = refl;
    trans(listed, trans(program_eval_last({prefix}_root(), {prefix}_earlier(), [{arguments}]), trans(spelled,
        {into_body})))
}}

theorem {prefix}_enters({typed_arguments}): program_eval({prefix}_program(), {f}, [{arguments}]) =
    {fin_at}(loop_eval({step}, [{params}], {count}, {exit}, [{next}], {at}(64, {bound_id}).toNat(), words_of({at}, [{inputs}]))) {{
    trans({prefix}_entered({arguments}), loop_then_eval([{inputs}], {bound_id}, [{params}], {count}, {prefix}_loop_body(), {exit}, [{next}],
        [{outputs}], {exhausted}, {prefix}_loop_post(), {call_of}, {at}, {result}))
}}

theorem {prefix}_runs({typed_arguments}): {prefix}_run({at}(64, {bound_id}).toNat(), words_of({at}, [{inputs}])) = {call} {{ refl }}

theorem {prefix}_agrees({typed_arguments}): program_eval({prefix}_program(), {f}, [{arguments}]) = {call} {{
    let values = {at};
    trans({prefix}_enters({arguments}), trans(loop_eval_agrees_from({step}, [{params}], {count}, {exit}, [{next}], trivial, refl,
        {fin}, λ (fuel: Nat) (state: List<BitVec(64)>) => {prefix}_run(fuel, state),
        λ v => {prefix}_base(v, values),
        λ r v => trans({prefix}_pass_agrees(r, v, values, λ (state: List<BitVec(64)>) => {prefix}_run(r, state)), sym({prefix}_unfolds(r, {at_v}))),
        values(64, {bound_id}).toNat(), values, [{inputs}], refl), {prefix}_runs({arguments})))
}}
", at = values, root_parameters = root_parameters, root_body = root_body, into_body = into_body, looped = looped_region(prefix, looped), call_of = call_of,
        outputs = ids(&looped.outputs), exhausted = looped.exhausted, result = parameters.len(), fin_at = finish(&values), words = words.join(", "), tree = looped.tree, pass = looped.pass,
        conds = with(&conditions), cs_args = with(&cs.join(", ")), pass_values = pass_of("values"), fin = finish("values"),
        params = ids(&looped.parameters), count = looped.count, exit = looped.exit, next = ids(&looped.next), bound_id = looped.bound,
        inputs = ids(&looped.inputs))
}

/// The loop with its body by name.
pub(super) fn looped_region(prefix: &str, looped: &function_ir_source::ReflectedLoop) -> String {
    use function_ir_source::ids;
    format!("Loop([{}], {}, [{}], {}, {prefix}_loop_body(), {}, [{}], [{}], {})", ids(&looped.inputs), looped.bound, ids(&looped.parameters),
        looped.count, looped.exit, ids(&looped.next), ids(&looped.outputs), looped.exhausted)
}

/// A root's result id: its parameters' count, as the reflector numbers it.
fn f_result(parameters: &[String]) -> usize { parameters.len() }

/// Bytes a piece of the published code is cut at, at least: about a
/// quarter of a declaration's fuel at the cost of an assembled byte.
const PIECE: usize = 256;

const GPRS: [&str; 16] = ["Rax", "Rcx", "Rdx", "Rbx", "Rsp", "Rbp", "Rsi", "Rdi", "R8", "R9", "R10", "R11", "R12", "R13", "R14", "R15"];
const LOW_BYTES: [Option<&str>; 16] = [Some("Al"), Some("Cl"), Some("Dl"), Some("Bl"), None, Some("Bpl"), Some("Sil"), Some("Dil"),
    Some("R8b"), Some("R9b"), Some("R10b"), Some("R11b"), Some("R12b"), Some("R13b"), Some("R14b"), Some("R15b")];
const CONDITIONS: [&str; 16] = ["O", "NO", "B", "AE", "E", "NE", "BE", "A", "S", "NS", "P", "NP", "L", "GE", "LE", "G"];

/// The code as `Prog::numbers` writes it, back as source: each item's name
/// and the item. A misreading is no hazard to the proof, which checks the
/// literal against the lowering; it is a refusal the compiler reports.
fn read_items(numbers: &[u64]) -> Result<Vec<(u64, String)>, String> {
    let mut at = numbers.iter().copied();
    let mut next = || at.next().ok_or_else(|| "the code's numbers end early".to_string());
    let bad = || "the code's numbers are malformed".to_string();
    let gpr = |n: u64| GPRS.get(n as usize).copied().ok_or_else(bad);
    let low = |n: u64| LOW_BYTES.get(n as usize).copied().flatten().ok_or_else(bad);
    let word = |width: u32, n: u64| format!("@bitvec::BitVec::ofNat({width}, {n})");
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
                format!("Block([{}])", instructions.join(", "))
            }
            1 => format!("Jcc({}, {})", CONDITIONS.get(take()? as usize).ok_or_else(bad)?, take()?),
            2 => format!("Jmp({})", take()?),
            3 => format!("CallTo({})", take()?),
            4 => "Ret".to_string(),
            5 => format!("Spill(StackStore(source := {}, offset := {}))", gpr(take()?)?, word(8, take()?)),
            6 => format!("Reload(StackLoad(destination := {}, offset := {}))", gpr(take()?)?, word(8, take()?)),
            _ => return Err("the lowering emitted an item the compiler does not state".into()),
        };
        items.push((name, item));
    }
    Ok(items)
}
