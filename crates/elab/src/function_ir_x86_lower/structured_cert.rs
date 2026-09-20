//! Certificate fold over recursive selection. Every physical claim is checked
//! against StructuredCode; leaf refinement reuses the ordinary DAG emitter.
use super::*;
use cert::Port;

type Values = BTreeMap<u64, String>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructuredX86Emission {
    pub lowered: LoweredStructured,
    pub text: String,
}

pub fn generate_structured(
    prefix: &str, region: &StructuredRegion, inputs: &Placements,
    temporaries: &[Gpr], output: Gpr,
) -> Result<StructuredX86Emission, LoweringError> {
    let lowered = lower_structured(region, inputs, temporaries, output)?;
    let mut module = Module::default();
    let values = region.inputs().iter().map(|p| (p.id, format!("values(width, {})", p.id))).collect();
    emit(prefix, region, &lowered, &values, &mut module)?;
    Ok(StructuredX86Emission { lowered, text: module.render() })
}

fn val(values: &Values, id: u64, width: u64) -> String {
    values[&id].replace(", width)", &format!(", {width})")).replace("values(width,", &format!("values({width},"))
}
fn placed_value(values: &Values, port: Port) -> String {
    let v = val(values, port.id, port.width);
    if port.width == 1 { format!("bitvec::zero_extend(1, 63, {v})") } else { v }
}
fn params(region: &StructuredRegion, plan: &LoweredStructured, values: &Values) -> Vec<Parameter> {
    let mut ps = vec![emitted_parameter("values", "Valuation()"), emitted_parameter("before", "MachineState<M>")];
    for p in region.inputs() {
        ps.push(emitted_parameter(format!("placed_{}", p.id), format!("{} = read_gpr({}, before.gprs)",
            placed_value(values, *p), plan.inputs[&p.id].heather_name())));
    }
    ps
}
fn args(region: &StructuredRegion) -> String {
    region.inputs().iter().map(|p| format!(", placed_{}", p.id)).collect()
}
fn fun(m: &mut Module, name: String, machine: bool, ps: Vec<Parameter>, ty: String, body: String) {
    m.declaration(emitted_function(name, machine, ps, ty, body));
}
fn thm(m: &mut Module, name: String, machine: bool, ps: Vec<Parameter>, ty: String, body: String) {
    m.declaration(emitted_theorem(name, machine, ps, ty, body));
}
fn before() -> Vec<Parameter> { vec![emitted_parameter("before", "MachineState<M>")] }
fn start() -> Vec<Parameter> { vec![emitted_parameter("start", "BitVec(64)")] }
fn logical() -> Vec<Parameter> { vec![emitted_parameter("values", "Valuation()")] }
fn step(start: &str, length: usize) -> String { format!("next_rip({start}, {length})") }
fn compose(start: &str, a: usize, b: usize) -> String {
    format!("bitvec::iterate_increment_compose(64, {start}, {a}, {b})")
}
fn congr_step(length: usize, proof: &str) -> String { format!("bitvec::cong_iterate_increment(64, {length}, {proof})") }
fn trans(a: &str, b: &str) -> String { format!("trans({a}, {b})") }

// Materialize a local graph valuation from the actual nodes. Inputs are
// explicit expressions from the enclosing interface, never graph assumptions.
fn dataflow_values(n: &str, r: &Region, incoming: &Values, m: &mut Module) -> Values {
    let mut values = incoming.clone();
    for node in &r.nodes {
        let output = node.output().id;
        let body = match *node {
            Node::Const { value, .. } => format!("bitvec::ofNat(width, {value})"),
            Node::UnsignedLessThan { left, right, .. } | Node::SignedLessThan { left, right, .. } => {
                let op = if matches!(node, Node::UnsignedLessThan { .. }) { "unsigned_lt_bit" } else { "signed_lt_bit" };
                format!("match width as λ n => BitVec(n) {{ Zero => bitvec::zero(0), Succ(k) => bitvec::cons_bit(k, bitvec::{op}(64, {}, {}), bitvec::zero(k)) }}", val(&values, left, 64), val(&values, right, 64))
            }
            Node::Add { left, right, .. } | Node::Sub { left, right, .. }
            | Node::BitAnd { left, right, .. } | Node::BitOr { left, right, .. } | Node::BitXor { left, right, .. } => {
                let op = match node { Node::Add { .. } => "add", Node::Sub { .. } => "sub", Node::BitAnd { .. } => "band", Node::BitOr { .. } => "bor", _ => "bxor" };
                format!("bitvec::{op}(width, {}, {})", values[&left], values[&right])
            }
            _ => unreachable!("leaf selection declines unsupported nodes"),
        };
        let name = format!("{n}_value_{output}");
        fun(m, name.clone(), false, vec![emitted_parameter("values", "Valuation()"), emitted_parameter("width", "Nat")], "BitVec(width)".into(), body);
        values.insert(output, format!("{name}(values, width)"));
    }
    let last = *values.keys().max().unwrap();
    let mut cases = "bitvec::zero(width)".to_string();
    for id in (0..=last).rev() {
        let name = if id == 0 { "id".into() } else { format!("id_{id}") };
        let v = values.get(&id).cloned().unwrap_or_else(|| "bitvec::zero(width)".into());
        cases = format!("match {name} {{ Zero => {v}, Succ(id_{}) => {cases} }}", id + 1);
    }
    fun(m, format!("{n}_valuation"), false, logical(), "Valuation()".into(), format!("λ width id => {cases}"));
    let mut witness = "trivial".to_string();
    for _ in &r.nodes { witness = format!("⟨refl, {witness}⟩"); }
    thm(m, format!("{n}_graph"), false, logical(), format!("RegionHolds({n}_raw(), {n}_valuation(values))"), witness);
    values
}

fn emit(n: &str, r: &StructuredRegion, p: &LoweredStructured, incoming: &Values, m: &mut Module) -> Result<(), LoweringError> {
    let output = p.output.1.heather_name();
    let length = p.byte_length;
    let public = params(r, p, incoming);
    let arguments = args(r);
    let (code, result, correct, memory, span, layout, decoding, frame): (String, String, String, String, String, String, String, Box<dyn Fn(Gpr) -> String>) = match (&r, &p.body) {
        (StructuredRegion::Dataflow(region), StructuredPlan::Dataflow(dag)) => {
            m.raw(cert::render_region_function(&format!("{n}_raw"), region));
            let values = dataflow_values(n, region, incoming, m);
            let leaf = format!("{n}_leaf");
            let emission = generate_selected(&leaf, &format!("{n}_raw()"), region, dag.clone())?;
            m.raw(emission.text);
            thm(m, format!("{n}_leaf_span"), false, start(), format!("{leaf}_final_rip(start) = next_rip(start, {length})"), render_block_span_proof(&dag.instructions));
            let proof = format!("{leaf}_refines_function_ir({n}_valuation(values), before{arguments}, {n}_graph(values))");
            let frame_leaf = leaf.clone();
            (format!("CodeBlock({leaf}_instructions())"), placed_value(&values, p.output.0), proof,
                format!("{leaf}_preserves_memory(before)"),
                format!("trans({leaf}_advances_rip(before), {n}_leaf_span(before.rip))"),
                "trivial".into(), format!("{leaf}_block_decodes(start)"),
                Box::new(move |reg| format!("{frame_leaf}_preserves_protected({}, before, trivial)", reg.heather_name())))
        }
        (StructuredRegion::Sequence { prefix, continuation }, StructuredPlan::Sequence { prefix: dag, continuation: next }) => {
            let first = format!("{n}_prefix");
            let rest = format!("{n}_continuation");
            let first_region = StructuredRegion::Dataflow(prefix.clone());
            let first_plan = LoweredStructured { inputs: p.inputs.clone(), output: (prefix.outputs[0], dag.output_register), clobbered: dag.clobbered.clone(), byte_length: dag.instructions.iter().map(|i| i.canonical_length()).sum(), body: StructuredPlan::Dataflow(dag.clone()) };
            emit(&first, &first_region, &first_plan, incoming, m)?;
            let mut carried = incoming.clone();
            carried.insert(dag.output_id, format!("{first}_value_{}(values, width)", dag.output_id));
            // A passthrough output has no defining node.
            if !prefix.nodes.iter().any(|node| node.output().id == dag.output_id) { carried.insert(dag.output_id, incoming[&dag.output_id].clone()); }
            emit(&rest, continuation, next, &carried, m)?;
            let intermediate = format!("{first}_after(before)");
            let carried_proofs = continuation.inputs().iter().map(|port| {
                if port.id == dag.output_id { format!("sym({first}_correct(values, before{arguments}))") }
                else { format!("trans(placed_{}, sym({first}_preserves({}, before, trivial)))", port.id, p.inputs[&port.id].heather_name()) }
            }).collect::<Vec<_>>().join(", ");
            let correct = format!("{rest}_correct(values, {intermediate}{}{})", if carried_proofs.is_empty() { "" } else { ", " }, carried_proofs);
            let span = trans(&format!("{rest}_span({intermediate})"), &trans(&congr_step(next.byte_length, &format!("{first}_span(before)")), &compose("before.rip", first_plan.byte_length, next.byte_length)));
            let memory = format!("trans({rest}_memory({intermediate}), {first}_memory(before))");
            let frame_first = first.clone(); let frame_rest = rest.clone();
            (format!("CodeSequence({first}_code(), {rest}_code())"), format!("{rest}_result(values)"), correct, memory, span,
                format!("⟨{first}_layout(), {rest}_layout()⟩"),
                format!("⟨{first}_decodes(start), {rest}_decodes(next_rip(start, {}))⟩", first_plan.byte_length),
                Box::new(move |reg| format!("trans({frame_rest}_preserves({}, {frame_first}_after(before), trivial), {frame_first}_preserves({}, before, trivial))", reg.heather_name(), reg.heather_name())))
        }
        (StructuredRegion::Conditional { condition, when_true, when_false, .. }, StructuredPlan::Conditional { condition_register, when_true: yes, when_false: no, false_displacement, join_displacement }) => {
            let t = format!("{n}_true"); let f = format!("{n}_false");
            emit(&t, when_true, yes, incoming, m)?; emit(&f, when_false, no, incoming, m)?;
            let register = condition_register.heather_name();
            let fd = format!("bitvec::ofNat(8, {false_displacement})"); let jd = format!("bitvec::ofNat(8, {join_displacement})");
            let entry = format!("structured_branch_entry({register}, {fd}, before)");
            let branch_args = format!("{register}, {fd}, {jd}, {t}_code(), {f}_code(), before");
            let bit = format!("bitvec::head_bit(0, {})", val(incoming, *condition, 1));
            let placed = format!("test_bit_value_placed_zf(λ width _ => {}, {condition}, {register}, before, placed_{condition})", incoming[condition]);
            let child_args = args(when_true);
            let child_t = format!("{t}_correct(values, {entry}{child_args})"); let child_f = format!("{f}_correct(values, {entry}{child_args})");
            let rt = format!("read_gpr({output}, {t}_after({entry}).gprs)"); let rf = format!("read_gpr({output}, {f}_after({entry}).gprs)");
            let choice = format!("select_zero_test({bit}, structured_test({register}, before).flags.zf, {rt}, {rf}, {placed})");
            let agree = format!("match {bit} as λ selected => (match selected {{ False => {rf}, True => {rt} }}) = (match selected {{ False => {f}_result(values), True => {t}_result(values) }}) {{ False => {child_f}, True => {child_t} }}");
            let correct = trans(&format!("structured_branch_read({branch_args}, {output})"), &trans(&choice, &agree));
            let memory = format!("structured_branch_property({branch_args}, λ after => after.memory = before.memory, {t}_memory({entry}), {f}_memory({entry}))");
            for (tag, d) in [("false", *false_displacement as usize), ("join", *join_displacement as usize)] {
                let body = trans(&format!("sym(bitvec::iter_add_eq_add(64, next_rip(start, 2), bitvec::sign_extend(7, 56, bitvec::ofNat(8, {d}))))"), &compose("start", 2, d));
                thm(m, format!("{n}_{tag}_target"), false, start(), format!("short_branch_target(start, bitvec::ofNat(8, {d})) = next_rip(start, {})", 2 + d), body);
            }
            let test_rip = step("before.rip", 3);
            let entry_t = trans(&format!("jump_zero_not_taken_rip(structured_test({register}, before).flags.zf, {test_rip}, {fd}, selected)"), &compose("before.rip", 3, 2));
            let entry_f = trans(&format!("jump_zero_taken_rip(structured_test({register}, before).flags.zf, {test_rip}, {fd}, selected)"), &trans(&format!("{n}_false_target({test_rip})"), &compose("before.rip", 3, 2 + *false_displacement as usize)));
            let en_rip = format!("{entry}.rip");
            let after_t_rip = step(&en_rip, yes.byte_length);
            let jump_cong = format!("cong_fn<BitVec(64), BitVec(64)>(λ rip => short_branch_target(rip, {jd}), {t}_span({entry}))");
            let true_tail = yes.byte_length + 2 + no.byte_length;
            let true_span = trans(&jump_cong, &trans(&format!("{n}_join_target({after_t_rip})"), &trans(&compose(&en_rip, yes.byte_length, 2 + no.byte_length), &trans(&congr_step(true_tail, &entry_t), &compose("before.rip", 5, true_tail)))));
            let false_span = trans(&format!("{f}_span({entry})"), &trans(&congr_step(no.byte_length, &entry_f), &compose("before.rip", 5 + yes.byte_length + 2, no.byte_length)));
            let span = format!("structured_branch_cases({branch_args}, λ after => after.rip = next_rip(before.rip, {length}), λ selected => {true_span}, λ selected => {false_span})");
            let frame_branch_args = branch_args.clone(); let frame_entry = entry.clone(); let frame_t = t.clone(); let frame_f = f.clone();
            (format!("CodeBranch({register}, {fd}, {jd}, {t}_code(), {f}_code())"),
                format!("match {bit} {{ False => {f}_result(values), True => {t}_result(values) }}"), correct, memory, span,
                format!("⟨{n}_false_target, ⟨{n}_join_target, ⟨{t}_layout(), {f}_layout()⟩⟩⟩"),
                format!("⟨canonical_encoding_decodes(start, TestRR({register}, {register})), ⟨decode_short_control_complete(JumpZero({fd})), ⟨{t}_decodes(next_rip(start, 5)), ⟨decode_short_control_complete(Jump({jd})), {f}_decodes(next_rip(start, {}))⟩⟩⟩⟩", 5 + yes.byte_length + 2),
                Box::new(move |reg| format!("structured_branch_property({frame_branch_args}, λ after => read_gpr({}, after.gprs) = read_gpr({}, before.gprs), {frame_t}_preserves({}, {frame_entry}, trivial), {frame_f}_preserves({}, {frame_entry}, trivial))", reg.heather_name(), reg.heather_name(), reg.heather_name(), reg.heather_name())))
        }
        _ => return Err(LoweringError::InvalidStructuredRegion("selected plan disagrees with region shape".into())),
    };
    fun(m, format!("{n}_code"), false, vec![], "StructuredCode".into(), code);
    fun(m, format!("{n}_bytes"), false, vec![], "List<BitVec(8)>".into(), format!("structured_bytes({n}_code())"));
    fun(m, format!("{n}_after"), true, before(), "MachineState<M>".into(), format!("structured_after({n}_code(), before)"));
    fun(m, format!("{n}_result"), false, logical(), "BitVec(64)".into(), result);
    thm(m, format!("{n}_correct"), true, public.clone(), format!("read_gpr({output}, {n}_after(before).gprs) = {n}_result(values)"), correct);
    thm(m, format!("{n}_memory"), true, before(), format!("{n}_after(before).memory = before.memory"), memory);
    thm(m, format!("{n}_span"), true, before(), format!("{n}_after(before).rip = next_rip(before.rip, {length})"), span);
    thm(m, format!("{n}_layout"), false, vec![], format!("StructuredLayout({n}_code())"), layout);
    thm(m, format!("{n}_decodes"), false, start(), format!("StructuredDecodes({n}_code(), start)"), decoding);
    thm(m, format!("{n}_byte_length"), false, vec![], format!("{n}_bytes().len() = {length}"), "refl".into());
    fun(m, format!("{n}_Protected"), false, vec![emitted_parameter("register", "Gpr")], "Type".into(), format!("match register {{ {} }}", render_protected_arms(&p.clobbered)));
    let mut arms = Vec::new();
    for reg in [Gpr::Rax, Gpr::Rcx, Gpr::Rdx, Gpr::Rbx, Gpr::Rsp, Gpr::Rbp, Gpr::Rsi, Gpr::Rdi, Gpr::R8, Gpr::R9, Gpr::R10, Gpr::R11, Gpr::R12, Gpr::R13, Gpr::R14, Gpr::R15] {
        arms.push(format!("{} => {}", reg.heather_name(), if p.clobbered.contains(&reg) { "protected ⊢ false_elim(protected)".into() } else { format!("_ ⊢ {}", frame(reg)) }));
    }
    thm(m, format!("{n}_preserves"), true, vec![emitted_parameter("register", "Gpr"), emitted_parameter("before", "MachineState<M>")], format!("{n}_Protected(register) → read_gpr(register, {n}_after(before).gprs) = read_gpr(register, before.gprs)"), format!("match register {{ {} }}", arms.join(", ")));
    thm(m, format!("{n}_artifact"), true, public, format!("StructuredArtifact<M>({n}_code(), before, {output}, {n}_result(values), {n}_Protected)"),
        format!("StructuredArtifact(after := {n}_after(before), execution := refl, layout := {n}_layout(), decoding := {n}_decodes(before.rip), result_correct := {n}_correct(values, before{arguments}), memory_preserved := {n}_memory(before), rip_correct := {n}_span(before), registers_preserved := λ register protected => {n}_preserves(register, before, protected))"));
    Ok(())
}
