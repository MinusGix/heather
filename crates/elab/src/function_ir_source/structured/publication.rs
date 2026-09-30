//! Typed source boundary over the shared physical certificates. Public premises
//! describe source arguments in registers; internal valuations stay private.
use super::*;

pub(super) fn encode(width: u64, value: &str) -> String {
    if width == 64 { value.into() } else { format!("@bitvec::BitVec::zero_extend({width}, {}, {value})", 64 - width) }
}
fn bit(value: &str) -> String { format!("@bitvec::BitVec::head_bit(0, {value})") }
pub(super) fn vector(ty: StructuredSourceType, value: &str) -> String {
    match ty {
        StructuredSourceType::Boolean => format!("bitvec::BitVec::ofBool({value})"),
        StructuredSourceType::NatWord => format!("bitvec_nat::word_of_nat(64, {value})"),
        _ => value.into(),
    }
}

use x86::at_width;

struct Observed {
    expression: String,
    values: Vec<String>,
    proofs: Vec<String>,
    /// Each port's value with the branches its narrowed region collapses
    /// taken as their false arm, and a proof that `values[i]` equals it
    /// (cert::narrow_structured_region).
    collapsed: Vec<String>,
    collapse_proofs: Vec<String>,
}
impl Observed {
    fn leaf(expression: String, values: Vec<String>, proofs: Vec<String>) -> Self {
        let collapse_proofs = values.iter().map(|_| "refl".to_string()).collect();
        Self { expression, collapsed: values.clone(), values, proofs, collapse_proofs }
    }
}

fn observe_tree(expansion: &mut Expansion<'_>, region: &StructuredRegion, mut values: Expressions,
    observers: &[String], result_type: &str, observation_types: &[String]) -> Result<Observed, SourceError>
{
    match region {
        StructuredRegion::Dataflow(body) if expansion.record.is_some() => {
            expansion.dataflow(body, &mut values)?;
            let components = expansion.components();
            let mut observed = Vec::new();
            let mut scalars = Vec::new();
            let mut leaves = Vec::new();
            for (ty, port) in components.iter().zip(&body.outputs) {
                let payload = operand(&values, port.id, ty.scalar_width()?)?.render();
                observed.push(if port.width == 1 { bit(&payload) } else { payload.clone() });
                let (scalar, leaf) = match ty {
                    StructuredSourceType::Boolean => (bit(&payload), "refl".to_string()),
                    StructuredSourceType::NatWord => {
                        let (natural, proof) = expansion.natural(port.id)?;
                        (natural.render(), proof.map_or_else(|| "refl".into(), |proof| proof.render()))
                    }
                    _ => (payload, "refl".to_string()),
                };
                scalars.push(HeatherExpr::raw(scalar));
                leaves.push(leaf);
            }
            let value = expansion.assemble(&scalars).render();
            match expansion.choice {
                Some(choice) => {
                    let tag = bit(&operand(&values, body.outputs[components.len()].id, 1)?.render());
                    let payload = expansion.payload_name();
                    let yes = format!("{}<{payload}>({value})", choice.constructors[1]);
                    let no = format!("{}<{payload}>({value})", choice.constructors[0]);
                    let expression = format!("match {tag} {{ False => {no}, True => {yes} }}");
                    let proofs = observers.iter().enumerate().map(|(i, observer)| {
                        let rhs = observed.get(i).cloned().unwrap_or_else(|| "selected".into());
                        let leaf = leaves.get(i).map_or("refl", |leaf| leaf.as_str());
                        format!("match {tag} as λ selected => {observer}(match selected {{ False => {no}, True => {yes} }}) = {rhs} {{ False => {leaf}, True => {leaf} }}")
                    }).collect();
                    observed.push(tag);
                    Ok(Observed::leaf(expression, observed, proofs))
                }
                None => Ok(Observed::leaf(value, observed, leaves)),
            }
        }
        StructuredRegion::Dataflow(body) => {
            expansion.dataflow(body, &mut values)?;
            let payload = operand(&values, body.outputs[0].id, expansion.result.scalar_width()?)?.render();
            let observed = if expansion.result.scalar_width()? == 1 { bit(&payload) } else { payload.clone() };
            // A carried Nat's leaf is not refl: word_of_nat of the source Nat
            // equals the port's word by the tracked proof.
            let (scalar, leaf) = match expansion.result {
                StructuredSourceType::Boolean => (bit(&payload), "refl".to_string()),
                StructuredSourceType::NatWord => {
                    let (natural, proof) = expansion.natural(body.outputs[0].id)?;
                    (natural.render(), proof.map_or_else(|| "refl".into(), |proof| proof.render()))
                }
                _ => (payload, "refl".to_string()),
            };
            if let Some(choice) = expansion.choice {
                let tag = bit(&operand(&values, body.outputs[1].id, 1)?.render());
                let yes = format!("{}<{}>({scalar})", choice.constructors[1], expansion.result.name());
                let no = format!("{}<{}>({scalar})", choice.constructors[0], expansion.result.name());
                let expression = format!("match {tag} {{ False => {no}, True => {yes} }}");
                let proofs = observers.iter().enumerate().map(|(i, observer)| {
                    let rhs = if i == 0 { observed.clone() } else { "selected".into() };
                    let leaf = if i == 0 { leaf.as_str() } else { "refl" };
                    format!("match {tag} as λ selected => {observer}(match selected {{ False => {no}, True => {yes} }}) = {rhs} {{ False => {leaf}, True => {leaf} }}")
                }).collect();
                Ok(Observed::leaf(expression, vec![observed, tag], proofs))
            } else {
                Ok(Observed::leaf(scalar, vec![observed], vec![leaf]))
            }
        }
        StructuredRegion::Sequence { prefix, continuation } => {
            expansion.dataflow(prefix, &mut values)?;
            observe_tree(expansion, continuation, values, observers, result_type, observation_types)
        }
        StructuredRegion::Compose { prefix, continuation } => {
            if prefix.outputs().len() != 1 { return unsupported("typed source composition requires one prefix result"); }
            let port = prefix.outputs()[0];
            if let Some(value) = expansion.sources.get(&port.id) {
                let crossing = expansion.crossing(value, port, &values)?;
                values.insert(port.id, (port.width, crossing));
                return observe_tree(expansion, continuation, values, observers, result_type, observation_types);
            }
            let saved_result = expansion.result;
            let saved_choice = expansion.choice.take();
            let saved_record = expansion.record.take();
            expansion.result = if port.width == 1 { StructuredSourceType::Boolean } else { StructuredSourceType::Word(port.width) };
            let result = expansion.region(prefix, values.clone())?;
            expansion.result = saved_result;
            expansion.choice = saved_choice;
            expansion.record = saved_record;
            let result = if port.width == 1 { HeatherExpr::call("bitvec::BitVec::ofBool", [result]) } else { result };
            values.insert(port.id, (port.width, result));
            observe_tree(expansion, continuation, values, observers, result_type, observation_types)
        }
        StructuredRegion::Conditional { condition, when_true, when_false, .. } => {
            let condition = expansion.test(&values, *condition)?;
            let yes = observe_tree(expansion, when_true, values.clone(), observers, result_type, observation_types)?;
            let no = observe_tree(expansion, when_false, values, observers, result_type, observation_types)?;
            let expression = format!("match {condition} {{ False => {}, True => {} }}", no.expression, yes.expression);
            let proofs = observers.iter().enumerate().map(|(i, observer)| format!(
                "selected_computation_agrees<{result_type}, {}>({condition}, {}, {}, {observer}, {}, {}, {}, {})",
                observation_types[i], no.expression, yes.expression, no.values[i], yes.values[i], no.proofs[i], yes.proofs[i])).collect();
            let values: Vec<String> = no.values.iter().zip(&yes.values).map(|(no, yes)| format!("match {condition} {{ False => {no}, True => {yes} }}")).collect();
            let ports = region.outputs();
            let mut collapsed = Vec::new();
            let mut collapse_proofs = Vec::new();
            for i in 0..values.len() {
                let (nv, yv, nc, yc, np, yp) = (&no.values[i], &yes.values[i], &no.collapsed[i], &yes.collapsed[i], &no.collapse_proofs[i], &yes.collapse_proofs[i]);
                let same = cert::structured_alpha_eq(&cert::narrow_structured_region(when_true, &[ports[i]]), &cert::narrow_structured_region(when_false, &[ports[i]]));
                if same {
                    // The true arm's collapsed value is the false arm's up to
                    // the names of their value definitions: conversion.
                    collapse_proofs.push(format!("match {condition} as λ selected => (match selected {{ False => {nv}, True => {yv} }}) = ({nc}) {{ False => {np}, True => {yp} }}"));
                    collapsed.push(nc.clone());
                } else {
                    collapse_proofs.push(format!("match {condition} as λ selected => (match selected {{ False => {nv}, True => {yv} }}) = (match selected {{ False => {nc}, True => {yc} }}) {{ False => {np}, True => {yp} }}"));
                    collapsed.push(format!("match {condition} {{ False => {nc}, True => {yc} }}"));
                }
            }
            Ok(Observed { expression, values, proofs, collapsed, collapse_proofs })
        }
    }
}

/// What every typed publication of a source shares: the source reflected and
/// expanded, one observer per output port, the observation of the whole
/// result, and the valuation its arguments give the region.
struct Publication {
    module: Module,
    reflected: ReflectedStructuredFunction,
    parameters: Vec<Parameter>,
    args: String,
    result_type: String,
    ports: Vec<Port>,
    observers: Vec<String>,
    observation_types: Vec<String>,
    observed: Observed,
    vals: String,
}

fn publication(elaborator: &Elaborator, prefix: &str, source_name: &str, contract: bool) -> Result<Publication, SourceError> {
    let reflected = reflect_elaborated_structured(elaborator, source_name)?;
    let mut module = Module::default();
    module.raw(format!("import x86_64_structured_block; import function_ir; import function_ir_x86_support; import x86_64; import x86_64_block; import bitvec; import bool; import list; import logic; import nat;{}",
        if contract { " import pair;" } else { "" }));
    module.raw(generate_structured_source_expansion(&format!("{prefix}_source"), &reflected)?
        .replace("import bitvec;\n", "").replace("import bool;\n", ""));
    let parameters = reflected.declared_parameters();
    let arguments = reflected.declared_arguments();
    let args = arguments.iter().map(|a| a.render()).collect::<Vec<_>>().join(", ");
    let result_type = reflected.result_type_name();
    let ports = reflected.region.outputs().to_vec();
    let components = reflected.result_components();
    let observers: Vec<_> = ports.iter().map(|port| format!("{prefix}_observe_{}", port.id)).collect();
    let observation_types: Vec<String> = ports.iter().map(|port| if port.width == 1 { "Bool".into() } else { format!("BitVec({})", port.width) }).collect();
    let names = reflected.choice.as_ref().map(|choice| choice.constructors.clone().map(|name| name.rsplit("::").next().unwrap().to_string()));
    for (i, observer) in observers.iter().enumerate() {
        let body = match (components.get(i), &names) {
            (Some(ty), _) => {
                let observe = |value: &str| match ty {
                    StructuredSourceType::Word(1) => bit(value),
                    StructuredSourceType::NatWord => vector(StructuredSourceType::NatWord, value),
                    _ => value.into(),
                };
                match (&reflected.record, &names) {
                    // Projected after the match, so the observer is
                    // `loop_step_payload(result).f` itself for a loop step.
                    (Some(record), Some([no, yes])) => observe(&format!("{{ let chosen: {} = match result {{ {no}(payload) => payload, {yes}(payload) => payload }}; chosen.{} }}",
                        record.type_name, record.fields[i].0)),
                    (Some(record), None) => observe(&format!("result.{}", record.fields[i].0)),
                    // A carried Nat's word wraps the whole selection, so the
                    // observer is `word_of_nat` of the payload and a consumer
                    // can state it without knowing which constructor the step
                    // chose.
                    (None, Some([no, yes])) if *ty == StructuredSourceType::NatWord => observe(&format!("match result {{ {no}(payload) => payload, {yes}(payload) => payload }}")),
                    (None, Some([no, yes])) => format!("match result {{ {no}(payload) => {}, {yes}(payload) => {} }}", observe("payload"), observe("payload")),
                    // A scalar result is its one field.
                    (None, None) => observe("result"),
                }
            }
            (None, Some([no, yes])) => format!("match result {{ {no}(payload) => False, {yes}(payload) => True }}"),
            (None, None) => return unsupported("a record result has no port past its fields"),
        };
        module.declaration(Declaration::function(observer, HeatherExpr::raw(&observation_types[i]), Block::expression(HeatherExpr::raw(body)))
            .parameters(vec![Parameter::explicit("result", HeatherExpr::raw(&result_type))]));
    }
    let initial = reflected.initial_values();
    let mut expansion = Expansion { prefix: &format!("{prefix}_publication"), module: &mut module, next_name: 0, parameters: &parameters, arguments: &arguments, result: reflected.result, choice: reflected.choice.as_ref(),
        record: reflected.record.as_ref(), naturals: natural_inputs(&reflected), constants: BTreeMap::new(), sources: &reflected.sources, tests: Default::default() };
    let observed = observe_tree(&mut expansion, &reflected.region, initial, &observers, &result_type, &observation_types)?;
    let mut cases = "@bitvec::BitVec::zero(width)".to_string();
    for (id, ty) in reflected.parameters.iter().enumerate().rev() {
        let value = ty.width().map_or_else(|| "@bitvec::BitVec::zero(width)".into(), |width| at_width(width, &vector(*ty, &reflected.spelling(id)), 0));
        cases = format!("match id{id} {{ Zero => {value}, Succ(id{}) => {cases} }}", id + 1);
    }
    module.declaration(Declaration::function(format!("{prefix}_typed_values"), HeatherExpr::raw("Valuation()"), Block::expression(HeatherExpr::raw(format!("λ width id0 => {cases}")))).parameters(parameters.clone()));
    let vals = format!("{prefix}_typed_values({args})");
    Ok(Publication { module, reflected, parameters, args, result_type, ports, observers, observation_types, observed, vals })
}

impl Publication {
    /// A port's value as the source computes it, over `args`, at the port's
    /// width in a 64-bit register.
    fn expected(&self, port: usize, args: &str) -> String {
        let observed = format!("{}({}({args}))", self.observers[port], self.reflected.source_name);
        let width = self.ports[port].width;
        encode(width, &if width == 1 { format!("bitvec::BitVec::ofBool({observed})") } else { observed })
    }

    /// A piece's public premises: the source's arguments, the state, and
    /// each input it reads placed in its register.
    fn placed(&self, inputs: &[Port], registers: &x86::Placements) -> (Vec<Parameter>, String) {
        let mut public = self.parameters.clone();
        public.push(Parameter::explicit("before", HeatherExpr::raw("MachineState<M>")));
        let mut placed_args = String::new();
        for input in inputs {
            let id = input.id;
            let name = format!("placed_{id}");
            public.push(Parameter::explicit(&name, HeatherExpr::raw(format!("{} = read_gpr({}, before.gprs)",
                encode(input.width, &vector(self.reflected.parameters[id as usize], &self.reflected.spelling(id as usize))), registers[&id].heather_name()))));
            placed_args.push_str(&format!(", {name}"));
        }
        (public, placed_args)
    }

    /// `{name}_typed_correct` and `{name}_typed_artifact`: the output register
    /// holds the source's value, from `correct`, the physical certificate's
    /// result restated against the source.
    fn artifact(&self, artifacts: &mut Module, name: &str, code: &str, public: &[Parameter], placed_args: &str, port: usize, output: Gpr, correct: String) {
        let expected = self.expected(port, &self.args);
        let call_args = if self.args.is_empty() { format!("before{placed_args}") } else { format!("{}, before{placed_args}", self.args) };
        artifacts.declaration(Declaration::theorem(format!("{name}_typed_correct"), HeatherExpr::raw(format!("read_gpr({}, {code}_after(before).gprs) = {expected}", output.heather_name())), Block::expression(HeatherExpr::raw(correct))).generic("M").parameters(public.to_vec()));
        artifacts.declaration(Declaration::theorem(format!("{name}_typed_artifact"), HeatherExpr::raw(format!("StructuredArtifact<M>({code}_code(), before, {}, {expected}, {code}_Protected)", output.heather_name())), Block::expression(HeatherExpr::raw(format!("StructuredArtifact(after := {code}_after(before), execution := refl, layout := {code}_layout(), decoding := {code}_decodes(before.rip), result_correct := {name}_typed_correct({call_args}), memory_preserved := {code}_memory(before), rip_correct := {code}_rip(before), registers_preserved := λ register protected => {code}_preserves(register, before, protected))")))).generic("M").parameters(public.to_vec()));
    }

    /// The piece as a process takes it (x86_64_structured_block's
    /// `Computes`): its input the source's arguments as one value (a `Pair`
    /// chain past one), placed in `registers`; its result the source's; and
    /// `{code}_scratch()` the registers it may write, the temporaries and the
    /// output. `{code}_within` says every other register is one the physical
    /// certificate protects.
    fn contract(&self, artifacts: &mut Module, name: &str, code: &str, inputs: &[Port], registers: &x86::Placements, temporaries: &[Gpr], port: usize, output: Gpr) -> Result<(), SourceError> {
        let types: Vec<String> = self.parameters.iter().map(|parameter| parameter.ty().render()).collect();
        let Some(last) = types.len().checked_sub(1) else { return unsupported("a piece's contract needs an argument") };
        let input = types.iter().rev().skip(1).fold(types[last].clone(), |rest, ty| format!("Pair<{ty}, {rest}>"));
        // Argument `i` of the value `x`: `x.fst`, `x.snd.fst`, …, the last
        // one the chain's end.
        let component = |i: usize| format!("x{}{}", ".snd".repeat(i), if i < last { ".fst" } else { "" });
        let components: Vec<String> = (0..types.len()).map(component).collect();
        let at = |spelling: String| -> String {
            let (parameter, field) = spelling.strip_prefix("arg").map(|rest| rest.split_once('.').map_or((rest, None), |(p, f)| (p, Some(f)))).expect("a source spelling");
            let parameter: usize = parameter.parse().expect("a parameter index");
            field.map_or_else(|| components[parameter].clone(), |field| format!("{}.{field}", components[parameter]))
        };
        let facts: Vec<String> = inputs.iter().map(|input| format!("{} = read_gpr({}, g)",
            encode(input.width, &vector(self.reflected.parameters[input.id as usize], &at(self.reflected.spelling(input.id as usize)))), registers[&input.id].heather_name())).collect();
        let placed = match facts.split_last() {
            None => "True".to_string(),
            Some((last, rest)) => rest.iter().rev().fold(last.clone(), |conjunction, fact| format!("({fact}) ∧ ({conjunction})")),
        };
        // Each input's fact out of the conjunction, in the artifact's order.
        let projections: String = (0..inputs.len()).map(|i| format!(", at{}{}", ".right".repeat(i), if i + 1 < inputs.len() { ".left" } else { "" })).collect();
        let mut scratch = temporaries.to_vec();
        if !scratch.contains(&output) { scratch.push(output); }
        let listed = scratch.iter().map(|register| register.heather_name()).collect::<Vec<_>>().join(", ");
        artifacts.raw(format!("fn {code}_scratch() → List<Gpr> {{ [{listed}] }}"));
        let arms: Vec<String> = [Gpr::Rax, Gpr::Rcx, Gpr::Rdx, Gpr::Rbx, Gpr::Rsp, Gpr::Rbp, Gpr::Rsi, Gpr::Rdi, Gpr::R8, Gpr::R9, Gpr::R10, Gpr::R11, Gpr::R12, Gpr::R13, Gpr::R14, Gpr::R15]
            .iter().map(|register| format!("{} => {}", register.heather_name(), if scratch.contains(register) { "kept ⊢ false_elim(kept)" } else { "_ ⊢ trivial" })).collect();
        artifacts.raw(format!("theorem {code}_within(register: Gpr): Kept({code}_scratch(), register) → {code}_Protected(register) {{ match register {{ {} }} }}", arms.join(", ")));
        artifacts.raw(format!("fn {name}_inputs_at(x: {input}, g: Gprs) → Type {{ {placed} }}"));
        artifacts.raw(format!("fn {name}_computed(x: {input}) → BitVec(64) {{ {} }}", self.expected(port, &components.join(", "))));
        let out = output.heather_name();
        artifacts.raw(format!("theorem {name}_computes<M>(): Computes<M, {input}>({code}_code(), {name}_inputs_at, {out}, {name}_computed, {code}_scratch()) {{
    computes_within<M, {input}>({code}_code(), {name}_inputs_at, {out}, {name}_computed, {code}_scratch(), {code}_Protected, {code}_within,
        λ before x at => {name}_typed_artifact({}, before{projections}))
}}", components.join(", ")));
        Ok(())
    }
}

fn typed_whole(
    elaborator: &Elaborator, prefix: &str, source_name: &str,
    inputs: &x86::Placements, temporaries: &[Gpr], consumable: &[Gpr], outputs: &x86::Placements, contract: bool,
) -> Result<x86::StructuredX86Emission, SourceError> {
    let mut publication = publication(elaborator, prefix, source_name, contract)?;
    let mut emission = x86::generate_structured_consuming(prefix, &publication.reflected.region, &publication.reflected.sources, &publication.reflected.bodies, inputs, temporaries,
        &consumable.iter().copied().collect(), outputs).map_err(SourceError::Lowering)?;
    let region_inputs = publication.reflected.region.inputs().to_vec();
    let (public, placed_args) = publication.placed(&region_inputs, inputs);
    let (args, vals) = (publication.args.clone(), publication.vals.clone());
    let mut artifacts = Module::default();
    for i in 0..publication.ports.len() {
        let port = publication.ports[i];
        let name = if i == 0 { prefix.to_string() } else { format!("{prefix}_output_{}", port.id) };
        let observer = &publication.observers[i];
        let observed_value = format!("{observer}({}({args}))", publication.reflected.source_name);
        let source_agreement = format!("trans(cong_fn<{}, {}>({observer}, sym({prefix}_source_source_expands({args}))), {})", publication.result_type, publication.observation_types[i], publication.observed.proofs[i]);
        let observed = publication.observed.values[i].clone();
        publication.module.declaration(Declaration::theorem(format!("{name}_source_observed"), HeatherExpr::raw(format!("{observed_value} = {observed}")), Block::expression(HeatherExpr::raw(source_agreement))).parameters(publication.parameters.clone()));
        // The physical fold and observation fold normalize one-bit branches alike.
        // A composed root reaches the observation through `_meaning`.
        let correct = if emission.text.contains(&format!("theorem {name}_meaning(")) {
            format!("trans({name}_correct({vals}, before{placed_args}), {name}_meaning({vals}))")
        } else { format!("{name}_correct({vals}, before{placed_args})") };
        let normalized = encode(port.width, &if port.width == 1 { "bitvec::BitVec::ofBool(value)".to_string() } else { "value".into() });
        let proof = format!("trans({correct}, sym(cong_fn<{}, BitVec(64)>(λ value => {normalized}, {name}_source_observed({args}))))", publication.observation_types[i]);
        let output = outputs[&port.id];
        publication.artifact(&mut artifacts, &name, prefix, &public, &placed_args, i, output, proof);
        if contract { publication.contract(&mut artifacts, &name, prefix, &region_inputs, inputs, temporaries, i, output)?; }
    }
    let mut module = publication.module;
    module.raw(emission.text);
    module.raw(artifacts.render());
    emission.text = module.render();
    Ok(emission)
}

/// Publish source-named artifacts for every scalar/choice result. Entry premises
/// bind typed source arguments to normalized registers; no graph or valuation
/// assumptions are exposed. Unused Nat arguments remain universally quantified.
/// This is a certificate API, not an OS calling convention or executable wrapper.
pub fn generate_elaborated_typed_x86(
    elaborator: &Elaborator, prefix: &str, source_name: &str,
    inputs: &x86::Placements, temporaries: &[Gpr], outputs: &x86::Placements,
) -> Result<x86::StructuredX86Emission, SourceError> {
    typed_whole(elaborator, prefix, source_name, inputs, temporaries, &[], outputs, false)
}

/// The same, where the inputs in `consumable` registers are dead once read,
/// so a result may take one's register (structured-lowering-in-place-results):
/// a value updated in place.
pub fn generate_elaborated_typed_consuming_x86(
    elaborator: &Elaborator, prefix: &str, source_name: &str,
    inputs: &x86::Placements, temporaries: &[Gpr], consumable: &[Gpr], outputs: &x86::Placements,
) -> Result<x86::StructuredX86Emission, SourceError> {
    typed_whole(elaborator, prefix, source_name, inputs, temporaries, consumable, outputs, false)
}

/// One generated piece of a process (docs/native-architecture-review.md R5):
/// the source's one result into `output`, published as above and as the
/// library's contract, `{prefix}_computes : Computes<M, A>(…)`, whose scratch
/// is `temporaries` and `output`.
pub fn generate_elaborated_piece_x86(
    elaborator: &Elaborator, prefix: &str, source_name: &str,
    inputs: &x86::Placements, temporaries: &[Gpr], output: Gpr,
) -> Result<x86::StructuredX86Emission, SourceError> {
    let reflected = reflect_elaborated_structured(elaborator, source_name)?;
    let [port] = reflected.region.outputs() else { return unsupported("a process's piece has one result") };
    typed_whole(elaborator, prefix, source_name, inputs, temporaries, &[], &x86::Placements::from([(port.id, output)]), true)
}

/// One output of a record-valued step with a certificate of its own
/// (docs/native-wc-design.md §4.6): its result port, its placements and its
/// result register. It reads only the inputs its output depends on; those in
/// `consumable` registers are dead once it has, so its result may take one's
/// register.
pub struct FieldPiece<'a> {
    pub prefix: String,
    pub port: u64,
    pub inputs: &'a x86::Placements,
    pub temporaries: &'a [Gpr],
    pub consumable: &'a [Gpr],
    pub output: Gpr,
}

/// A field piece's physical code and the inputs it reads.
#[derive(Clone, Debug)]
pub struct FieldEmission {
    pub prefix: String,
    pub lowered: x86::LoweredStructured,
    pub inputs: Vec<Port>,
}

/// Several outputs of one source, each alone: one reflection, one source
/// expansion and one observation of the whole result, shared; per piece, the
/// region narrowed to its output, lowered and certified, and a typed artifact
/// stating its register against the source's observed output. A piece placed
/// after another that overwrote a register the first read needs nothing from
/// that register, since its interface doesn't name it.
pub fn generate_elaborated_typed_fields_x86(
    elaborator: &Elaborator, prefix: &str, source_name: &str, pieces: &[FieldPiece<'_>],
) -> Result<(String, Vec<FieldEmission>), SourceError> {
    let mut publication = publication(elaborator, prefix, source_name, false)?;
    let (args, vals) = (publication.args.clone(), publication.vals.clone());
    for (i, port) in publication.ports.clone().iter().enumerate() {
        let observer = &publication.observers[i];
        let source_agreement = format!("trans(cong_fn<{}, {}>({observer}, sym({prefix}_source_source_expands({args}))), {})", publication.result_type, publication.observation_types[i], publication.observed.proofs[i]);
        let declaration = Declaration::theorem(format!("{prefix}_output_{}_source_observed", port.id),
            HeatherExpr::raw(format!("{observer}({}({args})) = {}", publication.reflected.source_name, publication.observed.values[i])), Block::expression(HeatherExpr::raw(source_agreement))).parameters(publication.parameters.clone());
        publication.module.declaration(declaration);
        // The same, with the branches the piece's narrowed region collapses
        // decided: what the piece's code computes.
        let declaration = Declaration::theorem(format!("{prefix}_output_{}_collapsed", port.id),
            HeatherExpr::raw(format!("{observer}({}({args})) = {}", publication.reflected.source_name, publication.observed.collapsed[i])),
            Block::expression(HeatherExpr::raw(format!("trans({prefix}_output_{}_source_observed({args}), {})", port.id, publication.observed.collapse_proofs[i])))).parameters(publication.parameters.clone());
        publication.module.declaration(declaration);
    }
    let mut artifacts = Module::default();
    let mut emissions = Vec::new();
    for piece in pieces {
        let i = publication.ports.iter().position(|port| port.id == piece.port).ok_or_else(|| SourceError::Unsupported(format!("no result port {}", piece.port)))?;
        let port = publication.ports[i];
        let reflected = &publication.reflected;
        let narrowed = cert::narrow_structured_region(&reflected.region, &[port]);
        let inputs: x86::Placements = narrowed.inputs().iter().map(|input| piece.inputs.get(&input.id).copied().map(|r| (input.id, r))
            .ok_or_else(|| SourceError::Unsupported(format!("piece {} reads input {} with no register", piece.prefix, input.id)))).collect::<Result<_, _>>()?;
        let emission = x86::generate_structured_consuming(&piece.prefix, &narrowed, &reflected.sources, &reflected.bodies, &inputs, piece.temporaries,
            &piece.consumable.iter().copied().collect(), &x86::Placements::from([(port.id, piece.output)])).map_err(SourceError::Lowering)?;
        let name = &piece.prefix;
        let (public, placed_args) = publication.placed(narrowed.inputs(), &inputs);
        let correct = if emission.text.contains(&format!("theorem {name}_meaning(")) {
            format!("trans({name}_correct({vals}, before{placed_args}), {name}_meaning({vals}))")
        } else { format!("{name}_correct({vals}, before{placed_args})") };
        let normalized = encode(port.width, &if port.width == 1 { "bitvec::BitVec::ofBool(value)".to_string() } else { "value".into() });
        let proof = format!("trans({correct}, sym(cong_fn<{}, BitVec(64)>(λ value => {normalized}, {prefix}_output_{}_collapsed({args}))))", publication.observation_types[i], port.id);
        publication.artifact(&mut artifacts, name, name, &public, &placed_args, i, piece.output, proof);
        publication.module.raw(emission.text.clone());
        emissions.push(FieldEmission { prefix: piece.prefix.clone(), lowered: emission.lowered, inputs: narrowed.inputs().to_vec() });
    }
    let mut module = publication.module;
    module.raw(artifacts.render());
    Ok((module.render(), emissions))
}
