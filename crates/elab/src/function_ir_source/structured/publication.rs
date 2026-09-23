//! Typed source boundary over the shared physical certificates. Public premises
//! describe source arguments in registers; internal valuations stay private.
use super::*;

pub(super) fn encode(width: u64, value: &str) -> String {
    if width == 64 { value.into() } else { format!("@bitvec::BitVec::zero_extend({width}, {}, {value})", 64 - width) }
}
fn bit(value: &str) -> String { format!("@bitvec::BitVec::head_bit(0, {value})") }
pub(super) fn vector(ty: StructuredSourceType, value: &str) -> String {
    if ty == StructuredSourceType::Boolean { format!("bitvec::BitVec::ofBool({value})") } else { value.into() }
}

// A width-indexed valuation must return the original neutral argument at its
// declared width, without turning it into a numeral and reconstructing it.
fn at_width(width: u64, value: &str, depth: u64) -> String {
    let index = if depth == 0 { "width".into() } else { format!("w{depth}") };
    let succ = |s: String| (0..depth).fold(s, |s, _| format!("Succ({s})"));
    let zero = if depth == width { value.into() } else { format!("@bitvec::BitVec::zero({depth})") };
    let rest = if depth == width { format!("@bitvec::BitVec::zero({})", succ(format!("Succ(w{})", depth + 1))) }
        else { at_width(width, value, depth + 1) };
    format!("match {index} as λ n => BitVec({}) {{ Zero => {zero}, Succ(w{}) => {rest} }}", succ("n".into()), depth + 1)
}

struct Observed {
    expression: String,
    values: Vec<String>,
    proofs: Vec<String>,
}

fn observe_tree(expansion: &mut Expansion<'_>, region: &StructuredRegion, mut values: Expressions,
    observers: &[String], result_type: &str, observation_types: &[String]) -> Result<Observed, SourceError>
{
    match region {
        StructuredRegion::Dataflow(body) => {
            expansion.dataflow(body, &mut values)?;
            let payload = operand(&values, body.outputs[0].id, expansion.result.scalar_width()?)?.render();
            let observed = if expansion.result.scalar_width()? == 1 { bit(&payload) } else { payload.clone() };
            let scalar = if expansion.result == StructuredSourceType::Boolean { bit(&payload) } else { payload };
            if let Some(choice) = expansion.choice {
                let tag = bit(&operand(&values, body.outputs[1].id, 1)?.render());
                let yes = format!("{}<{}>({scalar})", choice.constructors[1], expansion.result.name());
                let no = format!("{}<{}>({scalar})", choice.constructors[0], expansion.result.name());
                let expression = format!("match {tag} {{ False => {no}, True => {yes} }}");
                let proofs = observers.iter().enumerate().map(|(i, observer)| {
                    let rhs = if i == 0 { observed.clone() } else { "selected".into() };
                    format!("match {tag} as λ selected => {observer}(match selected {{ False => {no}, True => {yes} }}) = {rhs} {{ False => refl, True => refl }}")
                }).collect();
                Ok(Observed { expression, values: vec![observed, tag], proofs })
            } else {
                Ok(Observed { expression: scalar, values: vec![observed], proofs: vec!["refl".into()] })
            }
        }
        StructuredRegion::Sequence { prefix, continuation } => {
            expansion.dataflow(prefix, &mut values)?;
            observe_tree(expansion, continuation, values, observers, result_type, observation_types)
        }
        StructuredRegion::Compose { prefix, continuation } => {
            if prefix.outputs().len() != 1 { return unsupported("typed source composition requires one prefix result"); }
            let port = prefix.outputs()[0];
            let saved_result = expansion.result;
            let saved_choice = expansion.choice.take();
            expansion.result = if port.width == 1 { StructuredSourceType::Boolean } else { StructuredSourceType::Word(port.width) };
            let result = expansion.region(prefix, values.clone())?;
            expansion.result = saved_result;
            expansion.choice = saved_choice;
            let result = if port.width == 1 { HeatherExpr::call("bitvec::BitVec::ofBool", [result]) } else { result };
            values.insert(port.id, (port.width, result));
            observe_tree(expansion, continuation, values, observers, result_type, observation_types)
        }
        StructuredRegion::Conditional { condition, when_true, when_false, .. } => {
            let condition = bit(&operand(&values, *condition, 1)?.render());
            let yes = observe_tree(expansion, when_true, values.clone(), observers, result_type, observation_types)?;
            let no = observe_tree(expansion, when_false, values, observers, result_type, observation_types)?;
            let expression = format!("match {condition} {{ False => {}, True => {} }}", no.expression, yes.expression);
            let proofs = observers.iter().enumerate().map(|(i, observer)| format!(
                "selected_computation_agrees<{result_type}, {}>({condition}, {}, {}, {observer}, {}, {}, {}, {})",
                observation_types[i], no.expression, yes.expression, no.values[i], yes.values[i], no.proofs[i], yes.proofs[i])).collect();
            let values = no.values.iter().zip(&yes.values).map(|(no, yes)| format!("match {condition} {{ False => {no}, True => {yes} }}")).collect();
            Ok(Observed { expression, values, proofs })
        }
    }
}

/// Publish source-named artifacts for every scalar/choice result. Entry premises
/// bind typed source arguments to normalized registers; no graph or valuation
/// assumptions are exposed. Unused Nat arguments remain universally quantified.
/// This is a certificate API, not an OS calling convention or executable wrapper.
pub fn generate_elaborated_typed_x86(
    elaborator: &Elaborator, prefix: &str, source_name: &str,
    inputs: &x86::Placements, temporaries: &[Gpr], outputs: &x86::Placements,
) -> Result<x86::StructuredX86Emission, SourceError> {
    let reflected = reflect_elaborated_structured(elaborator, source_name)?;
    let mut emission = x86::generate_structured_results(prefix, &reflected.region, inputs, temporaries, outputs).map_err(SourceError::Lowering)?;
    let mut module = Module::default();
    module.raw("import x86_64_structured_block; import function_ir; import function_ir_x86_support; import x86_64; import x86_64_block; import bitvec; import bool; import list; import logic; import nat;");
    module.raw(generate_structured_source_expansion(&format!("{prefix}_source"), &reflected)?
        .replace("import bitvec;\n", "").replace("import bool;\n", ""));
    let parameters: Vec<_> = reflected.parameters.iter().enumerate().map(|(i, ty)| Parameter::explicit(format!("arg{i}"), HeatherExpr::raw(ty.name()))).collect();
    let arguments: Vec<_> = (0..parameters.len()).map(|i| HeatherExpr::name(format!("arg{i}"))).collect();
    let args = arguments.iter().map(|a| a.render()).collect::<Vec<_>>().join(", ");
    let result_type = reflected.choice.as_ref().map_or_else(|| reflected.result.name(), |choice| format!("{}<{}>", choice.type_name, reflected.result.name()));
    let ports = reflected.region.outputs();
    let observers: Vec<_> = ports.iter().map(|port| format!("{prefix}_observe_{}", port.id)).collect();
    let observation_types: Vec<String> = ports.iter().map(|port| if port.width == 1 { "Bool".into() } else { format!("BitVec({})", port.width) }).collect();
    for (i, observer) in observers.iter().enumerate() {
        let payload = if reflected.result == StructuredSourceType::Word(1) { bit("payload") } else { "payload".into() };
        let body = if let Some(choice) = &reflected.choice {
            format!("match result {{ {}(payload) => {}, {}(payload) => {} }}", choice.constructors[0].rsplit("::").next().unwrap(), if i == 0 { &payload } else { "False" }, choice.constructors[1].rsplit("::").next().unwrap(), if i == 0 { &payload } else { "True" })
        } else if reflected.result == StructuredSourceType::Word(1) { bit("result") } else { "result".into() };
        module.declaration(Declaration::function(observer, HeatherExpr::raw(&observation_types[i]), Block::expression(HeatherExpr::raw(body)))
            .parameters(vec![Parameter::explicit("result", HeatherExpr::raw(&result_type))]));
    }
    let initial = reflected.parameters.iter().enumerate().filter_map(|(id, ty)| ty.width().map(|width|
        (id as u64, (width, HeatherExpr::raw(vector(*ty, &format!("arg{id}"))))))).collect();
    let mut expansion = Expansion { prefix: &format!("{prefix}_publication"), module: &mut module, next_name: 0, parameters: &parameters, arguments: &arguments, result: reflected.result, choice: reflected.choice.as_ref() };
    let observed = observe_tree(&mut expansion, &reflected.region, initial, &observers, &result_type, &observation_types)?;
    let mut cases = "@bitvec::BitVec::zero(width)".to_string();
    for (id, ty) in reflected.parameters.iter().enumerate().rev() {
        let value = ty.width().map_or_else(|| "@bitvec::BitVec::zero(width)".into(), |width| at_width(width, &vector(*ty, &format!("arg{id}")), 0));
        cases = format!("match id{id} {{ Zero => {value}, Succ(id{}) => {cases} }}", id + 1);
    }
    module.declaration(Declaration::function(format!("{prefix}_typed_values"), HeatherExpr::raw("Valuation()"), Block::expression(HeatherExpr::raw(format!("λ width id0 => {cases}")))).parameters(parameters.clone()));
    let vals = format!("{prefix}_typed_values({args})");
    let mut public = parameters.clone();
    public.push(Parameter::explicit("before", HeatherExpr::raw("MachineState<M>")));
    let mut call_args = if args.is_empty() { "before".into() } else { format!("{args}, before") };
    let mut placed_args = String::new();
    for port in reflected.region.inputs() {
        let id = port.id;
        let name = format!("placed_{id}");
        public.push(Parameter::explicit(&name, HeatherExpr::raw(format!("{} = read_gpr({}, before.gprs)", encode(port.width, &vector(reflected.parameters[id as usize], &format!("arg{id}"))), inputs[&id].heather_name()))));
        placed_args.push_str(&format!(", {name}"));
        call_args.push_str(&format!(", {name}"));
    }
    let mut artifacts = Module::default();
    for (i, port) in ports.iter().enumerate() {
        let name = if i == 0 { prefix.to_string() } else { format!("{prefix}_output_{}", port.id) };
        let observer = &observers[i];
        let observed_value = format!("{observer}({}({args}))", reflected.source_name);
        let normalized = |v: &str| encode(port.width, &if port.width == 1 { format!("bitvec::BitVec::ofBool({v})") } else { v.into() });
        let expected = normalized(&observed_value);
        let source_agreement = format!("trans(cong_fn<{result_type}, {}>({observer}, sym({prefix}_source_source_expands({args}))), {})", observation_types[i], observed.proofs[i]);
        module.declaration(Declaration::theorem(format!("{name}_source_observed"), HeatherExpr::raw(format!("{observed_value} = {}", observed.values[i])), Block::expression(HeatherExpr::raw(source_agreement))).parameters(parameters.clone()));
        // The physical fold and observation fold normalize one-bit branches alike.
        let proof = format!("trans({name}_correct({vals}, before{placed_args}), sym(cong_fn<{}, BitVec(64)>(λ value => {}, {name}_source_observed({args}))))", observation_types[i], normalized("value"));
        artifacts.declaration(Declaration::theorem(format!("{name}_typed_correct"), HeatherExpr::raw(format!("read_gpr({}, {prefix}_after(before).gprs) = {expected}", outputs[&port.id].heather_name())), Block::expression(HeatherExpr::raw(proof))).generic("M").parameters(public.clone()));
        artifacts.declaration(Declaration::theorem(format!("{name}_typed_artifact"), HeatherExpr::raw(format!("StructuredArtifact<M>({prefix}_code(), before, {}, {expected}, {prefix}_Protected)", outputs[&port.id].heather_name())), Block::expression(HeatherExpr::raw(format!("StructuredArtifact(after := {prefix}_after(before), execution := refl, layout := {prefix}_layout(), decoding := {prefix}_decodes(before.rip), result_correct := {name}_typed_correct({call_args}), memory_preserved := {prefix}_memory(before), rip_correct := {prefix}_span(before), registers_preserved := λ register protected => {prefix}_preserves(register, before, protected))")))).generic("M").parameters(public.clone()));
    }
    module.raw(emission.text);
    module.raw(artifacts.render());
    emission.text = module.render();
    Ok(emission)
}
