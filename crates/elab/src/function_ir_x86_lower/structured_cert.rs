//! Certificate fold over recursive selection. Every physical claim is checked
//! against StructuredCode; leaf refinement reuses the ordinary DAG emitter.
use super::*;
use cert::Port;

type Values = BTreeMap<u64, String>;

/// The source values of composed helper calls, and the name each crossing
/// has given its value so far: a later crossing spells a produced argument
/// by that name, and nothing compares the argument's expansion again.
struct Crossings<'a> {
    values: &'a cert::SourceValues,
    bodies: &'a cert::SourceBodies,
    /// A crossing's name, with the scope it was named in: a continuation is
    /// certified over its own valuation, so a name made inside one means
    /// nothing outside it, and is spelled out in full there instead.
    named: std::cell::RefCell<BTreeMap<u64, (String, u32)>>,
    scope: std::cell::Cell<u32>,
    scopes: std::cell::Cell<u32>,
    /// The root's name: only it publishes `_artifact` and `_rip`, which no
    /// parent reads.
    root: String,
    /// The widths whose `{root}_at_width_W` placement is declared so far.
    placements: std::cell::RefCell<BTreeSet<u64>>,
}

impl Crossings<'_> {
    /// A produced value as this scope has it: an input carried in, else a
    /// name made here; `None` spells it out in full.
    fn spelled(&self, incoming: &Values, port: Port) -> Option<String> {
        if incoming.contains_key(&port.id) { return Some(val(incoming, port.id, port.width)); }
        self.named.borrow().get(&port.id).filter(|(_, scope)| *scope == self.scope.get()).map(|(name, _)| name.clone())
    }

    /// `value` (a `BitVec(width)`) as a valuation entry, through one
    /// declaration per width: `at_width` spelled inline is quadratic in the
    /// width, and every carry would elaborate it again.
    fn at_width(&self, m: &mut Module, width: u64, value: &str) -> String {
        let name = format!("{}_at_width_{width}", self.root);
        if self.placements.borrow_mut().insert(width) {
            fun(m, name.clone(), false, vec![emitted_parameter("width", "Nat"), emitted_parameter("s", format!("BitVec({width})"))], "BitVec(width)".into(), at_width(width, "s", 0));
        }
        format!("{name}(width, {value})")
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructuredX86Emission {
    pub lowered: LoweredStructured,
    pub text: String,
}

pub fn generate_structured(
    prefix: &str, region: &StructuredRegion, inputs: &Placements,
    temporaries: &[Gpr], output: Gpr,
) -> Result<StructuredX86Emission, LoweringError> {
    if region.outputs().len() != 1 { return Err(LoweringError::OutputCount(region.outputs().len())); }
    generate_structured_results(prefix, region, inputs, temporaries, &Placements::from([(region.outputs()[0].id, output)]))
}

pub fn generate_structured_results(
    prefix: &str, region: &StructuredRegion, inputs: &Placements,
    temporaries: &[Gpr], outputs: &Placements,
) -> Result<StructuredX86Emission, LoweringError> {
    generate_structured_sourced(prefix, region, &cert::SourceValues::new(), &cert::SourceBodies::new(), inputs, temporaries, outputs)
}

/// As `generate_structured_results`, with the source value of each composed
/// helper call (cert::SourceValue): those compositions cross at the call.
pub fn generate_structured_sourced(
    prefix: &str, region: &StructuredRegion, sources: &cert::SourceValues, bodies: &cert::SourceBodies, inputs: &Placements,
    temporaries: &[Gpr], outputs: &Placements,
) -> Result<StructuredX86Emission, LoweringError> {
    generate_structured_consuming(prefix, region, sources, bodies, inputs, temporaries, &BTreeSet::new(), outputs)
}

/// As `generate_structured_sourced`, where the caller reads the inputs in
/// `consumable` registers no more (`lower_structured_consuming`).
#[allow(clippy::too_many_arguments)]
pub fn generate_structured_consuming(
    prefix: &str, region: &StructuredRegion, sources: &cert::SourceValues, bodies: &cert::SourceBodies, inputs: &Placements,
    temporaries: &[Gpr], consumable: &BTreeSet<Gpr>, outputs: &Placements,
) -> Result<StructuredX86Emission, LoweringError> {
    let lowered = lower_structured_consuming(region, inputs, temporaries, consumable, outputs)?;
    let mut module = Module::default();
    let values = region.inputs().iter().map(|p| (p.id, format!("values(width, {})", p.id))).collect();
    let crossings = Crossings { values: sources, bodies, named: Default::default(), scope: Default::default(), scopes: Default::default(),
        root: prefix.to_string(), placements: Default::default() };
    emit(prefix, region, &lowered, &values, &mut module, &crossings)?;
    Ok(StructuredX86Emission { lowered, text: module.render() })
}

fn val(values: &Values, id: u64, width: u64) -> String {
    values[&id].replace(", width)", &format!(", {width})")).replace("values(width,", &format!("values({width},"))
        .replace("match width as", &format!("match {width} as"))
}
fn placed_value(values: &Values, port: Port) -> String {
    let v = val(values, port.id, port.width);
    placed_expression(port.width, &v)
}
// Keep Boolean control outside the one-bit vector constructor. The source
// reflector uses ofBool around a helper's Boolean result; head_bit of this
// representation reduces to that same neutral case tree when composed.
fn branch_value(condition: &str, port: Port, yes: &Values, no: &Values) -> String {
    if port.width == 1 {
        let bit = format!("match {condition} {{ False => @bitvec::BitVec::head_bit(0, {}), True => @bitvec::BitVec::head_bit(0, {}) }}", val(no, port.id, 1), val(yes, port.id, 1));
        format!("match width as λ n => BitVec(n) {{ Zero => @bitvec::BitVec::zero(0), Succ(k) => @bitvec::BitVec::cons_bit(k, {bit}, @bitvec::BitVec::zero(k)) }}")
    } else {
        format!("match {condition} {{ False => {}, True => {} }}", no[&port.id], yes[&port.id])
    }
}

/// `proof : a = b` (at `BitVec(width)`) as the placed words' equation.
fn placed_cong(width: u64, proof: &str) -> String {
    if width == 64 { proof.into() } else { format!("cong_fn<BitVec({width}), BitVec(64)>(λ value => {}, {proof})", placed_expression(width, "value")) }
}

fn normalize_bit_result(proof: String, values: &Values, port: Port) -> String {
    if port.width != 1 { return proof; }
    trans(&proof, &format!("cong_fn<BitVec(1), BitVec(64)>(λ value => @bitvec::BitVec::zero_extend(1, 63, value), bitvec::BitVec::one_bit_eq_ofBool({}))", val(values, port.id, 1)))
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
    format!("bitvec::BitVec::iterate_increment_compose(64, {start}, {a}, {b})")
}
fn congr_step(length: usize, proof: &str) -> String { format!("bitvec::BitVec::cong_iterate_increment(64, {length}, {proof})") }
fn trans(a: &str, b: &str) -> String { format!("trans({a}, {b})") }

// Lengths compose from the children's `_byte_length` lemmas, and a fact
// stated at a literal length is transported to `structured_bytes(…).len()`
// along them: converting that length evaluates every instruction's
// encoding in the subtree, at every level above it.
fn length_of(child: &str) -> String { format!("structured_bytes({child}_code())") }
/// Spelled with constructors so that it has a type of its own beside `++`.
fn literal_bytes(bytes: &[u8]) -> String {
    bytes.iter().rev().fold("Nil<BitVec(8)>".to_string(), |rest, b| format!("Cons(@bitvec::BitVec::ofNat(8, {b}), {rest})"))
}
fn transported(child: &str, motive: &str, fact: &str) -> String {
    format!("j(sym({child}_byte_length()), λ y _ => {motive}, {fact})")
}

// Materialize a local graph valuation from the actual nodes. Inputs are
// explicit expressions from the enclosing interface, never graph assumptions.
fn dataflow_values(n: &str, r: &Region, incoming: &Values, m: &mut Module) -> Values {
    let mut values = incoming.clone();
    for node in &r.nodes {
        let output = node.output().id;
        let mut name = format!("{n}_value_{output}");
        let body = match *node {
            Node::Const { value, .. } => format!("@bitvec::BitVec::ofNat(width, {value})"),
            Node::UnsignedLessThan { width: operand_width, left, right, .. } | Node::SignedLessThan { width: operand_width, left, right, .. }
            | Node::Equal { width: operand_width, left, right, .. } => {
                let op = match node { Node::UnsignedLessThan { .. } => "unsigned_lt_bit", Node::SignedLessThan { .. } => "signed_lt_bit", _ => "eq_bit" };
                // The comparison is its own Boolean (`_test_`), which a
                // branch reads directly: `head_bit` of the word would make
                // conversion evaluate the comparison, and through it every
                // structured producer below. At width one the word is spelled
                // as NodeHolds states it, `ofBool(…)`, for the same reason.
                let test = format!("{n}_test_{output}");
                fun(m, test.clone(), false, logical(), "Bool".into(), format!("@bitvec::BitVec::{op}({operand_width}, {}, {})", val(&values, left, operand_width), val(&values, right, operand_width)));
                name = format!("{n}_compare_{output}");
                let bit = format!("{test}(values)");
                format!("match width as λ n => BitVec(n) {{ Zero => @bitvec::BitVec::zero(0), Succ(k) => match k as λ m => BitVec(Succ(m)) {{ Zero => bitvec::BitVec::ofBool({bit}), Succ(j) => @bitvec::BitVec::cons_bit(Succ(j), {bit}, @bitvec::BitVec::zero(Succ(j))) }} }}")
            }
            // A copy is spelled as the value it copies, as the source does.
            Node::Move { source, .. } => values[&source].clone(),
            Node::Add { left, right, .. } | Node::Sub { left, right, .. }
            | Node::BitAnd { left, right, .. } | Node::BitOr { left, right, .. } | Node::BitXor { left, right, .. } => {
                let op = match node { Node::Add { .. } => "add", Node::Sub { .. } => "sub", Node::BitAnd { .. } => "band", Node::BitOr { .. } => "bor", _ => "bxor" };
                format!("@bitvec::BitVec::{op}(width, {}, {})", values[&left], values[&right])
            }
            _ => unreachable!("leaf selection declines unsupported nodes"),
        };
        fun(m, name.clone(), false, vec![emitted_parameter("values", "Valuation()"), emitted_parameter("width", "Nat")], "BitVec(width)".into(), body);
        values.insert(output, format!("{name}(values, width)"));
    }
    let entries: Vec<_> = values.iter().map(|(id, value)| (*id, value.clone())).collect();
    fun(m, format!("{n}_valuation"), false, logical(), "Valuation()".into(), format!("λ width id => {}", valuation_body(&entries)));
    // The lookups the node's interface reads, at a neutral width: at a
    // literal one, conversion unfolds the other side in lockstep with the
    // lookup's `leb` steps (see the node equations below).
    for port in r.inputs.iter().chain(&r.outputs).map(|port| port.id).collect::<BTreeSet<_>>() {
        thm(m, format!("{n}_at_{port}"), false, vec![emitted_parameter("values", "Valuation()"), emitted_parameter("width", "Nat")],
            format!("{n}_valuation(values)(width, {port}) = {}", values[&port]), "refl".into());
    }
    // Each node's equation by `refl` at a neutral width, used at its own
    // (the leaf's context). At a literal width the lookup's `leb` steps are
    // δ-steps, which conversion takes in lockstep with the other side: one
    // more unfolding of a width-64 `add` per step.
    // A comparison's is at its own width: its `_test_` Boolean is stated at
    // the operand width.
    for node in &r.nodes {
        let (parameters, at) = if is_comparison(node) { (vec![], cert::render_node(*node)) }
            else { (vec![emitted_parameter("w", "Nat")], cert::render_node_at(*node, "w").0) };
        thm(m, format!("{n}_holds_{}", node.output().id), false, [vec![emitted_parameter("values", "Valuation()")], parameters].concat(),
            format!("NodeHolds({n}_valuation(values), {at})"), "refl".into());
    }
    values
}

fn is_comparison(node: &Node) -> bool {
    matches!(node, Node::UnsignedLessThan { .. } | Node::SignedLessThan { .. } | Node::Equal { .. })
}

/// The node's equation as `dataflow_values` proves it, at the node's width.
fn holds(n: &str, node: &Node) -> String {
    let output = node.output().id;
    if is_comparison(node) { format!("{n}_holds_{output}(values)") }
    else { format!("{n}_holds_{output}(values, {})", cert::render_node_at(*node, "w").1) }
}

/// A comparison node's Boolean, when `value` is the word `dataflow_values`
/// spelled for one (`…_compare_N(values, width)` beside `…_test_N`).
fn test_of(value: &str) -> Option<String> {
    let name = value.strip_suffix("(values, width)")?;
    let (owner, id) = name.rsplit_once("_compare_")?;
    id.bytes().all(|b| b.is_ascii_digit()).then(|| format!("{owner}_test_{id}(values)"))
}

fn emit(n: &str, r: &StructuredRegion, p: &LoweredStructured, incoming: &Values, m: &mut Module, sources: &Crossings) -> Result<Values, LoweringError> {
    let length = p.byte_length;
    let (code, results, proofs, memory, span, layout, decoding, byte_length, bytes, frame): (String, Values, Vec<String>, String, String, String, String, String, (String, String), Frame) = match (&r, &p.body) {
        (StructuredRegion::Dataflow(region), StructuredPlan::Dataflow(dag)) => {
            let values = dataflow_values(n, region, incoming, m);
            let leaf = format!("{n}_leaf");
            // No region declaration: a structured leaf's context holds its
            // node equations, not the region's graph.
            let emission = generate_selected(&leaf, "", region, dag.clone(), LeafUse::Structured)?;
            m.raw(emission.text);
            thm(m, format!("{n}_leaf_span"), false, start(), format!("{leaf}_final_rip(start) = next_rip(start, {length})"), render_block_span_proof(&dag.instructions));
            // The leaf states its inputs and result as lookups in the node's
            // valuation; each is met through `_at`, a lookup proved at a
            // neutral width (`dataflow_values`), never converted at its own.
            // Its context's node equations are the node's own `_holds_N`.
            let placed = region.inputs.iter().enumerate().map(|(index, port)|
                format!("input_{index}_placed := trans({}, placed_{})", placed_cong(port.width, &format!("{n}_at_{}(values, {})", port.id, port.width)), port.id));
            let holds = region.nodes.iter().enumerate().map(|(index, node)|
                format!("holds_{index} := {}", holds(n, node)));
            let context = placed.chain(holds).collect::<Vec<_>>().join(", ");
            let output = p.output.0;
            let proof = format!("trans({leaf}_refines_compact({n}_valuation(values), before, {leaf}_Context({context})), {})",
                placed_cong(output.width, &format!("{n}_at_{}(values, {})", output.id, output.width)));
            // The node protects what its leaf does (both are `clobbered`'s
            // arms), so one proof at a neutral register: at a named one,
            // `read_gpr` evaluated the block's state once per register.
            let protected = if p.clobbered == dag.clobbered { "protected".to_string() } else { format!("{leaf}_kept(register, protected)") };
            let kept = if p.clobbered == dag.clobbered { vec![] } else { vec![leaf.clone()] };
            (format!("CodeBlock({leaf}_instructions())"), Values::from([(output.id, values[&output.id].clone())]), vec![proof],
                format!("{leaf}_preserves_memory(before)"),
                format!("trans({leaf}_advances_rip(before), {n}_leaf_span(before.rip))"),
                "trivial".into(), format!("{leaf}_block_decodes(start)"), "refl".into(), (literal_bytes(&encoding::encode_instructions(&dag.instructions)), "refl".into()),
                Frame::Any { children: kept, proof: format!("{leaf}_preserves_protected(register, before, {protected})") })
        }
        (StructuredRegion::Sequence { prefix, continuation }, StructuredPlan::Sequence { prefix: dag, continuation: next }) => {
            let first_region = StructuredRegion::Dataflow(prefix.clone());
            let first_plan = LoweredStructured { inputs: p.inputs.clone(), output: (prefix.outputs[0], dag.output_register), outputs: vec![(prefix.outputs[0], dag.output_register)], clobbered: dag.clobbered.clone(), byte_length: dag.instructions.iter().map(|i| i.canonical_length()).sum(), body: StructuredPlan::Dataflow(dag.clone()) };
            return emit_sequence(n, r, p, &first_region, &first_plan, continuation, next, incoming, m, sources);
        }
        (StructuredRegion::Compose { prefix, continuation }, StructuredPlan::Compose { prefix: first, continuation: next }) => {
            if let Some(value) = prefix.outputs().first().and_then(|port| sources.values.get(&port.id)) {
                return emit_crossing(n, r, p, prefix, first, continuation, next, incoming, m, sources, value);
            }
            return emit_sequence(n, r, p, prefix, first, continuation, next, incoming, m, sources);
        }
        (StructuredRegion::Sequence { prefix, continuation }, StructuredPlan::Compose { prefix: first, continuation: next }) => {
            return emit_sequence(n, r, p, &StructuredRegion::Dataflow(prefix.clone()), first, continuation, next, incoming, m, sources);
        }
        (StructuredRegion::Dataflow(_), StructuredPlan::MultiDataflow(parts)) => {
            return emit_parts(n, r, p, parts, incoming, m, sources);
        }
        (StructuredRegion::Sequence { prefix, continuation }, StructuredPlan::FusedSequence { operands, continuation: next }) => {
            // The prefix without its comparison, which computes the one
            // operand the prefix owns; the branch compares it with the other.
            let fused = structured::fusable(prefix, continuation)?
                .ok_or_else(|| LoweringError::InvalidStructuredRegion("a fused plan over a sequence that does not fuse".into()))?;
            let StructuredRegion::Conditional { condition, arguments, outputs, when_true, when_false, .. } = &**continuation else { unreachable!("fusable checked") };
            let first_region = StructuredRegion::Dataflow(Region { inputs: prefix.inputs.clone(), nodes: structured::cone(prefix, fused.computed.id)?, outputs: vec![fused.computed] });
            let first_plan = LoweredStructured { inputs: p.inputs.clone(), output: (fused.computed, operands.output_register), outputs: vec![(fused.computed, operands.output_register)], clobbered: operands.clobbered.clone(), byte_length: operands.instructions.iter().map(|i| i.canonical_length()).sum(), body: StructuredPlan::Dataflow(operands.clone()) };
            let branch = StructuredRegion::Conditional { inputs: structured::fused_inputs(&fused, arguments), condition: *condition, arguments: arguments.clone(),
                outputs: outputs.clone(), when_true: when_true.clone(), when_false: when_false.clone() };
            return emit_sequence(n, r, p, &first_region, &first_plan, &branch, next, incoming, m, sources);
        }
        (StructuredRegion::Conditional { condition, when_true, when_false, .. }, StructuredPlan::Conditional { test: planned, when_true: yes, when_false: no, one_armed: Some(arm), .. }) => {
            return emit_when(n, r, p, *condition, *planned, *arm, (when_true, yes), (when_false, no), incoming, m, sources);
        }
        (StructuredRegion::Conditional { condition, when_true, when_false, .. }, StructuredPlan::Conditional { test: planned, when_true: yes, when_false: no, false_displacement, join_displacement, near, one_armed: None }) => {
            let t = format!("{n}_true"); let f = format!("{n}_false");
            let tv = emit(&t, when_true, yes, incoming, m, sources)?; let fv = emit(&f, when_false, no, incoming, m, sources)?;
            let (test, bit, placed, selector) = describe_test(n, *planned, *condition, incoming, m, false);
            let compare = matches!(planned, PlannedTest::Compare { .. });
            // The two encodings differ in their jumps only: rel8 JZ/JMP (2
            // bytes each), or JZ rel32 (6) and JMP rel32 (5).
            let (jz, jmp) = if *near { (6usize, 5usize) } else { (2, 2) };
            let (fdn, jdn) = (*false_displacement as usize, *join_displacement as usize);
            let (fd, jd) = if *near { (format!("@bitvec::BitVec::ofNat(32, {fdn})"), format!("@bitvec::BitVec::ofNat(32, {jdn})")) }
                else { (format!("@bitvec::BitVec::ofNat(8, {fdn})"), format!("@bitvec::BitVec::ofNat(8, {jdn})")) };
            let (entry_fn, read_fn, property_fn, cases_fn, constructor) = if *near {
                ("structured_near_entry", "structured_near_branch_read", "structured_near_branch_property", "structured_near_branch_cases", "CodeBranchNear")
            } else { ("structured_branch_entry", "structured_branch_read", "structured_branch_property", "structured_branch_cases", "CodeBranch") };
            let facts = if *near { "structured_near_branch" } else { "structured_branch" };
            let target = |start: &str, length: usize, displacement: &str| if *near { format!("near_branch_target({start}, {length}, {displacement})") }
                else { format!("short_branch_target({start}, {displacement})") };
            let entry = format!("{entry_fn}({test}, {fd}, before)");
            let branch_args = format!("{test}, {fd}, {jd}, {t}_code(), {f}_code(), before");
            let child_args = args(when_true);
            let mut results = Values::new();
            let mut proofs = Vec::new();
            for &(port, reg) in &p.outputs {
                let output = reg.heather_name();
                let suffix = result_suffix(p, port.id);
                let child_t = normalize_bit_result(format!("{t}{suffix}_correct(values, {entry}{child_args})"), &tv, port);
                let child_f = normalize_bit_result(format!("{f}{suffix}_correct(values, {entry}{child_args})"), &fv, port);
                let rt = format!("read_gpr({output}, {t}_after({entry}).gprs)"); let rf = format!("read_gpr({output}, {f}_after({entry}).gprs)");
                let choice = format!("select_zero_test({bit}, {selector}, {rt}, {rf}, {placed})");
                let selected_result = placed_value(&Values::from([(port.id,
                    branch_value("selected", port, &tv, &fv))]), port);
                let agree = format!("match {bit} as λ selected => (match selected {{ False => {rf}, True => {rt} }}) = ({selected_result}) {{ False => {child_f}, True => {child_t} }}");
                let correct = trans(&format!("{read_fn}({branch_args}, {output})"), &trans(&choice, &agree));
                proofs.push(correct);
                results.insert(port.id, branch_value(&bit, port, &tv, &fv));
            }
            let memory = format!("{property_fn}({branch_args}, λ after => after.memory = before.memory, {t}_memory({entry}), {f}_memory({entry}))");
            for (tag, length, d, displacement) in [("false", jz, fdn, &fd), ("join", jmp, jdn, &jd)] {
                let body = if *near { format!("near_branch_forward(start, {length}, {d}, {displacement}, refl)") }
                    else { trans(&format!("sym(bitvec::BitVec::iter_add_eq_add(64, next_rip(start, 2), @bitvec::BitVec::sign_extend(7, 56, {displacement})))"), &compose("start", 2, d)) };
                thm(m, format!("{n}_{tag}_target"), false, start(), format!("{} = next_rip(start, {})", target("start", length, displacement), length + d), body);
            }
            let test_rip = step("before.rip", 3);
            let tested = format!("branch_test_state({test}, before)");
            let (not_taken, taken) = match (compare, *near) {
                (false, true) => (format!("near_not_taken_rip({fd}, {tested}, selected)"), format!("near_taken_rip({fd}, {tested}, selected)")),
                (false, false) => (format!("jump_zero_not_taken_rip({selector}, {test_rip}, {fd}, selected)"), format!("jump_zero_taken_rip({selector}, {test_rip}, {fd}, selected)")),
                (true, true) => (format!("near_if_not_taken_rip(branch_skip({test}), {fd}, {tested}, selected)"), format!("near_if_taken_rip(branch_skip({test}), {fd}, {tested}, selected)")),
                (true, false) => (format!("jump_zero_not_taken_rip({selector}, {test_rip}, {fd}, selected)"), format!("jump_zero_taken_rip({selector}, {test_rip}, {fd}, selected)")),
            };
            let entry_t = trans(&not_taken, &compose("before.rip", 3, jz));
            let entry_f = trans(&taken, &trans(&format!("{n}_false_target({test_rip})"), &compose("before.rip", 3, jz + fdn)));
            let en_rip = format!("{entry}.rip");
            let after_t_rip = step(&en_rip, yes.byte_length);
            let jump_cong = format!("cong_fn<BitVec(64), BitVec(64)>(λ rip => {}, {t}_span({entry}))", target("rip", jmp, &jd));
            let true_tail = yes.byte_length + jmp + no.byte_length;
            let head = 3 + jz;
            let true_span = trans(&jump_cong, &trans(&format!("{n}_join_target({after_t_rip})"), &trans(&compose(&en_rip, yes.byte_length, jmp + no.byte_length), &trans(&congr_step(true_tail, &entry_t), &compose("before.rip", head, true_tail)))));
            let false_span = trans(&format!("{f}_span({entry})"), &trans(&congr_step(no.byte_length, &entry_f), &compose("before.rip", head + yes.byte_length + jmp, no.byte_length)));
            let span = format!("{cases_fn}({branch_args}, λ after => after.rip = next_rip(before.rip, {length}), λ selected => {true_span}, λ selected => {false_span})");
            let frame_branch_args = branch_args.clone(); let frame_entry = entry.clone(); let frame_t = t.clone(); let frame_f = f.clone();
            let frame_property = property_fn.to_string();
            // The node's facts from its children's, through the lemma for
            // its constructor (structured_branch_length, …).
            let (yl, nl) = (yes.byte_length, no.byte_length);
            let children = format!("{test}, {fd}, {jd}, {t}_code(), {f}_code()");
            (format!("{constructor}({test}, {fd}, {jd}, {t}_code(), {f}_code())"),
                results, proofs, memory, span,
                format!("{facts}_layout({children}, {yl}, {nl}, {t}_byte_length(), {f}_byte_length(), λ start => {n}_false_target(start), λ start => {n}_join_target(start), {t}_layout(), {f}_layout())"),
                format!("{facts}_decodes({children}, {yl}, start, {t}_byte_length(), {t}_decodes(next_rip(start, {head})), {f}_decodes(next_rip(start, {head} + {yl} + {jmp})))"),
                format!("{facts}_length({children}, {yl}, {nl}, {t}_byte_length(), {f}_byte_length())"),
                {
                    // The fixed pieces are literal too; conversion checks each
                    // against its few-byte encoding.
                    let (jz_literal, jmp_literal) = if *near {
                        let mut jz = vec![0x0f, 0x80 | planned.skip_code()]; jz.extend((fdn as u32).to_le_bytes());
                        let mut jmp = vec![0xe9]; jmp.extend((jdn as u32).to_le_bytes());
                        (literal_bytes(&jz), literal_bytes(&jmp))
                    } else { (literal_bytes(&[0x70 | planned.skip_code(), fdn as u8]), literal_bytes(&[0xeb, jdn as u8])) };
                    (format!("{} ++ ({jz_literal} ++ ({t}_lit() ++ ({jmp_literal} ++ {f}_lit())))", literal_bytes(&test_literal(*planned))),
                        format!("{facts}_bytes({children}, {t}_lit(), {f}_lit(), {t}_bytes_are(), {f}_bytes_are())"))
                },
                Frame::Any { children: vec![frame_t.clone(), frame_f.clone()],
                    proof: format!("{frame_property}({frame_branch_args}, λ after => read_gpr(register, after.gprs) = read_gpr(register, before.gprs), {frame_t}_preserves(register, {frame_entry}, {frame_t}_kept(register, protected)), {frame_f}_preserves(register, {frame_entry}, {frame_f}_kept(register, protected)))") })
        }
        _ => return Err(LoweringError::InvalidStructuredRegion("selected plan disagrees with region shape".into())),
    };
    finish(n, r, p, incoming, m, sources, code, results, proofs, memory, span, layout, decoding, byte_length, bytes, frame)
}

/// What a branch tests, as `StructuredCode` spells it; the Boolean that picks
/// the true arm; why the machine's selector is that Boolean (its zero test,
/// or itself when `negated`); and the selector. `negated` is a one-armed
/// branch whose body is the false arm: its skip is the comparison holding.
fn describe_test(n: &str, planned: PlannedTest, condition: u64, incoming: &Values, m: &mut Module, negated: bool) -> (String, String, String, String) {
    match planned {
        PlannedTest::NonZero(register) => {
            assert!(!negated, "a materialised bit's TEST has no negated form");
            let register = register.heather_name();
            let bit = test_of(&incoming[&condition]).unwrap_or_else(|| format!("@bitvec::BitVec::head_bit(0, {})", val(incoming, condition, 1)));
            (format!("NonZero({register})"), bit,
                format!("test_bit_value_placed_zf(λ width _ => {}, {condition}, {register}, before, placed_{condition})", incoming[&condition]),
                format!("structured_test({register}, before).flags.zf"))
        }
        PlannedTest::Compare { left, right, operation, left_port, right_port, width } => {
            let (l, rr) = (left.heather_name(), right.heather_name());
            let (a, b) = (val(incoming, left_port, width), val(incoming, right_port, width));
            let (op, cc, lemma, zero_extend_law) = match (operation, negated) {
                (ComparisonOperation::UnsignedLessThan, false) => ("unsigned_lt_bit", "B", "unsigned_compare_skips", Some("unsigned_lt_zero_extend")),
                (ComparisonOperation::SignedLessThan, false) => ("signed_lt_bit", "L", "signed_compare_skips", None),
                (ComparisonOperation::Equal, false) => ("eq_bit", "E", "equal_compare_skips", Some("eq_bit_zero_extend")),
                (ComparisonOperation::UnsignedLessThan, true) => ("unsigned_lt_bit", "AE", "unsigned_compare_holds", Some("unsigned_lt_zero_extend")),
                (ComparisonOperation::SignedLessThan, true) => ("signed_lt_bit", "GE", "signed_compare_holds", None),
                (ComparisonOperation::Equal, true) => ("eq_bit", "NE", "equal_compare_holds", Some("eq_bit_zero_extend")),
            };
            fun(m, format!("{n}_test"), false, logical(), "Bool".into(), format!("@bitvec::BitVec::{op}({width}, {a}, {b})"));
            let test = format!("Compare({l}, {rr}, {cc})");
            // CMP compares the placed words; below 64 bits those are
            // the operands zero-extended, whose comparison is the
            // narrow one by the zero-extension law.
            let (wide_a, wide_b) = (placed_expression(width, &a), placed_expression(width, &b));
            let skips = format!("{lemma}({l}, {rr}, {wide_a}, {wide_b}, before, placed_{left_port}, placed_{right_port})");
            let skips = if width == 64 { skips } else {
                let zero_extend_law = zero_extend_law.expect("fusable refuses a narrow signed comparison");
                let law = format!("bitvec::BitVec::{zero_extend_law}({width}, {}, {a}, {b})", 64 - width);
                if negated { trans(&skips, &law) } else { trans(&skips, &format!("cong_fn<bool::Bool, bool::Bool>(λ bit => bool::Bool::not(bit), {law})")) }
            };
            (test.clone(), format!("{n}_test(values)"), skips, format!("branch_skips({test}, before)"))
        }
    }
}

/// The bytes of a branch's TEST r, r or CMP l, r.
fn test_literal(planned: PlannedTest) -> Vec<u8> {
    match planned {
        PlannedTest::NonZero(register) => {
            let r = encoding::register_code(register);
            vec![0x48 | (r >> 3) | ((r >> 3) << 2), 0x85, 0xc0 | ((r & 7) << 3) | (r & 7)]
        }
        PlannedTest::Compare { .. } => encoding::encode_instructions(&[planned.instruction().expect("a comparison's instruction")]),
    }
}

/// A conditional with one empty arm, laid out as `CodeWhen(test, d, body)`:
/// `test ; Jcc join ; body`. Only the body is a node; the empty arm returns
/// its input where it already is (`passthrough`), so on the skip the result
/// is that input's placement, read through the branch's registers.
#[allow(clippy::too_many_arguments)]
fn emit_when(n: &str, r: &StructuredRegion, p: &LoweredStructured, condition: u64, planned: PlannedTest, arm: OneArmed,
    (when_true, yes): (&StructuredRegion, &LoweredStructured), (when_false, no): (&StructuredRegion, &LoweredStructured),
    incoming: &Values, m: &mut Module, sources: &Crossings,
) -> Result<Values, LoweringError> {
    let (b, body_region, body_plan, empty_region) = match arm {
        OneArmed::True => (format!("{n}_true"), when_true, yes, when_false),
        OneArmed::False => (format!("{n}_false"), when_false, no, when_true),
    };
    let kept_input = structured::passthrough(empty_region)
        .ok_or_else(|| LoweringError::InvalidStructuredRegion("a one-armed plan over an arm that computes".into()))?;
    let bv = emit(&b, body_region, body_plan, incoming, m, sources)?;
    let (test, bit, placed, selector) = describe_test(n, planned, condition, incoming, m, arm == OneArmed::False);
    let bl = body_plan.byte_length;
    let length = p.byte_length;
    let d = format!("@bitvec::BitVec::ofNat(8, {bl})");
    let entry = format!("structured_branch_entry({test}, {d}, before)");
    let when_args = format!("{test}, {d}, {b}_code(), before");
    let child_args = args(body_region);
    let mut results = Values::new();
    let mut proofs = Vec::new();
    for &(port, reg) in &p.outputs {
        let output = reg.heather_name();
        let child = normalize_bit_result(format!("{b}{}_correct(values, {entry}{child_args})", result_suffix(p, port.id)), &bv, port);
        let ran = format!("read_gpr({output}, {b}_after({entry}).gprs)");
        let stayed = format!("read_gpr({output}, before.gprs)");
        let kept = format!("sym(placed_{})", kept_input.id);
        let empty = Values::from([(port.id, incoming[&kept_input.id].clone())]);
        // The read lemma's match is on the skip: the body's read when it
        // ran, the entry's when it was jumped over.
        let (tv, fv, rt, rf, child_t, child_f, choice) = match arm {
            OneArmed::True => (&bv, &empty, ran.clone(), stayed.clone(), child, kept,
                format!("select_zero_test({bit}, {selector}, {ran}, {stayed}, {placed})")),
            OneArmed::False => (&empty, &bv, stayed.clone(), ran.clone(), kept, child,
                format!("cong_fn<bool::Bool, BitVec(64)>(λ skips => match skips {{ False => {ran}, True => {stayed} }}, {placed})")),
        };
        let selected_result = placed_value(&Values::from([(port.id, branch_value("selected", port, tv, fv))]), port);
        let agree = format!("match {bit} as λ selected => (match selected {{ False => {rf}, True => {rt} }}) = ({selected_result}) {{ False => {child_f}, True => {child_t} }}");
        proofs.push(trans(&format!("structured_when_read({when_args}, {output})"), &trans(&choice, &agree)));
        results.insert(port.id, branch_value(&bit, port, tv, fv));
    }
    let memory = format!("structured_when_property({when_args}, λ after => after.memory = before.memory, {b}_memory({entry}), refl)");
    thm(m, format!("{n}_skip_target"), false, start(), format!("short_branch_target(start, {d}) = next_rip(start, {})", 2 + bl),
        trans(&format!("sym(bitvec::BitVec::iter_add_eq_add(64, next_rip(start, 2), @bitvec::BitVec::sign_extend(7, 56, {d})))"), &compose("start", 2, bl)));
    let test_rip = step("before.rip", 3);
    let entry_rip = trans(&format!("jump_zero_not_taken_rip({selector}, {test_rip}, {d}, selected)"), &compose("before.rip", 3, 2));
    let body_span = trans(&format!("{b}_span({entry})"), &trans(&congr_step(bl, &entry_rip), &compose("before.rip", 5, bl)));
    let skip_span = trans(&format!("jump_zero_taken_rip({selector}, {test_rip}, {d}, selected)"),
        &trans(&format!("{n}_skip_target({test_rip})"), &compose("before.rip", 3, 2 + bl)));
    let span = format!("structured_when_cases({when_args}, λ after => after.rip = next_rip(before.rip, {length}), λ selected => {body_span}, λ selected => {skip_span})");
    let jcc = literal_bytes(&[0x70 | arm.skip_code(planned), bl as u8]);
    finish(n, r, p, incoming, m, sources, format!("CodeWhen({test}, {d}, {b}_code())"), results, proofs, memory, span,
        format!("structured_when_layout({test}, {d}, {b}_code(), {bl}, {b}_byte_length(), λ start => {n}_skip_target(start), {b}_layout())"),
        format!("structured_when_decodes({test}, {d}, {b}_code(), start, {b}_decodes(next_rip(start, 5)))"),
        format!("structured_when_length({test}, {d}, {b}_code(), {bl}, {b}_byte_length())"),
        (format!("{} ++ ({jcc} ++ {b}_lit())", literal_bytes(&test_literal(planned))),
            format!("structured_when_bytes({test}, {d}, {b}_code(), {b}_lit(), {b}_bytes_are())")),
        Frame::Any { children: vec![b.clone()],
            proof: format!("structured_when_property({when_args}, λ after => read_gpr(register, after.gprs) = read_gpr(register, before.gprs), {b}_preserves(register, {entry}, {b}_kept(register, protected)), refl)") })
}

/// How `_preserves` is proved: one proof at a neutral `register` from the
/// children's `_preserves` (a leaf's own `_preserves_protected`), given
/// `protected`, with `{child}_kept(register, protected)` for each child whose
/// own premise differs: the states convert by unfolding, register or not.
enum Frame {
    Any { children: Vec<String>, proof: String },
}

fn result_suffix(p: &LoweredStructured, id: u64) -> String {
    if id == p.output.0.id { String::new() } else { format!("_output_{id}") }
}

#[allow(clippy::too_many_arguments)]
fn finish(n: &str, r: &StructuredRegion, p: &LoweredStructured, incoming: &Values, m: &mut Module, sources: &Crossings,
    code: String, results: Values, proofs: Vec<String>, memory: String, span: String,
    layout: String, decoding: String, byte_length: String, bytes: (String, String), frame: Frame,
) -> Result<Values, LoweringError> {
    let root = n == sources.root;
    let public = params(r, p, incoming);
    let arguments = args(r);
    let length = p.byte_length;
    fun(m, format!("{n}_code"), false, vec![], "StructuredCode".into(), code);
    fun(m, format!("{n}_bytes"), false, vec![], "List<BitVec(8)>".into(), format!("structured_bytes({n}_code())"));
    fun(m, format!("{n}_after"), true, before(), "MachineState<M>".into(), format!("structured_after({n}_code(), before)"));
    let mut exported = Values::new();
    for ((port, reg), proof) in p.outputs.iter().zip(proofs) {
        let name = format!("{n}{}", result_suffix(p, port.id));
        fun(m, format!("{name}_value"), false, vec![emitted_parameter("values", "Valuation()"), emitted_parameter("width", "Nat")], "BitVec(width)".into(), results[&port.id].clone());
        // A comparison keeps its own spelling, so a branch on it reads the
        // Boolean (`test_of`) rather than `head_bit` of this wrapper.
        exported.insert(port.id, if test_of(&results[&port.id]).is_some() { results[&port.id].clone() } else { format!("{name}_value(values, width)") });
        fun(m, format!("{name}_result"), false, logical(), "BitVec(64)".into(), placed_value(&exported, *port));
        thm(m, format!("{name}_correct"), true, public.clone(), format!("read_gpr({}, {n}_after(before).gprs) = {name}_result(values)", reg.heather_name()), proof);
    }
    thm(m, format!("{n}_memory"), true, before(), format!("{n}_after(before).memory = before.memory"), memory);
    thm(m, format!("{n}_span"), true, before(), format!("{n}_after(before).rip = next_rip(before.rip, {length})"), span);
    thm(m, format!("{n}_layout"), false, vec![], format!("StructuredLayout({n}_code())"), layout);
    thm(m, format!("{n}_decodes"), false, start(), format!("StructuredDecodes({n}_code(), start)"), decoding);
    thm(m, format!("{n}_byte_length"), false, vec![], format!("{n}_bytes().len() = {length}"), byte_length);
    // The bytes as the leaves' literals, appended in the code's own shape:
    // an exporter compares its published literal with `_lit`, which walks
    // literals only, instead of evaluating every encoding in one proof.
    fun(m, format!("{n}_lit"), false, vec![], "List<BitVec(8)>".into(), bytes.0);
    thm(m, format!("{n}_bytes_are"), false, vec![], format!("{n}_bytes() = {n}_lit()"), bytes.1);
    if root { thm(m, format!("{n}_rip"), true, before(), format!("{n}_after(before).rip = next_rip(before.rip, {}.len())", length_of(n)),
        transported(n, &format!("{n}_after(before).rip = next_rip(before.rip, y)"), &format!("{n}_span(before)"))); }
    fun(m, format!("{n}_Protected"), false, vec![emitted_parameter("register", "Gpr")], "Type".into(), format!("match register {{ {} }}", render_protected_arms(&p.clobbered)));
    let preserved = match frame {
        Frame::Any { children, proof } => {
            // Each child protects what this node does: the one per-register
            // case split, over `Protected` alone, which reduces to a
            // constructor; the machine states are compared once, at a
            // neutral register, rather than evaluated once per register.
            for child in children {
                thm(m, format!("{child}_kept"), false, vec![emitted_parameter("register", "Gpr")], format!("{n}_Protected(register) → {child}_Protected(register)"),
                    format!("match register {{ {}_ => _ ⊢ trivial }}", p.clobbered.iter().map(|reg| format!("{} => protected ⊢ false_elim(protected), ", reg.heather_name())).collect::<String>()));
            }
            format!("λ protected => {proof}")
        }
    };
    thm(m, format!("{n}_preserves"), true, vec![emitted_parameter("register", "Gpr"), emitted_parameter("before", "MachineState<M>")], format!("{n}_Protected(register) → read_gpr(register, {n}_after(before).gprs) = read_gpr(register, before.gprs)"), preserved);
    if root { for &(port, reg) in &p.outputs {
        let name = format!("{n}{}", result_suffix(p, port.id));
        let output = reg.heather_name();
        thm(m, format!("{name}_artifact"), true, public.clone(), format!("StructuredArtifact<M>({n}_code(), before, {output}, {name}_result(values), {n}_Protected)"),
            format!("StructuredArtifact(after := {n}_after(before), execution := refl, layout := {n}_layout(), decoding := {n}_decodes(before.rip), result_correct := {name}_correct(values, before{arguments}), memory_preserved := {n}_memory(before), rip_correct := {n}_rip(before), registers_preserved := λ register protected => {n}_preserves(register, before, protected))"));
    } }
    Ok(exported)
}

#[allow(clippy::too_many_arguments)]
fn emit_sequence(n: &str, r: &StructuredRegion, p: &LoweredStructured,
    first_region: &StructuredRegion, first_plan: &LoweredStructured,
    continuation: &StructuredRegion, next: &LoweredStructured,
    incoming: &Values, m: &mut Module, sources: &Crossings,
) -> Result<Values, LoweringError> {
    let first = format!("{n}_prefix"); let rest = format!("{n}_continuation");
    let produced = emit(&first, first_region, first_plan, incoming, m, sources)?;
    let mut carried = incoming.clone(); carried.extend(produced);
    let results = emit(&rest, continuation, next, &carried, m, sources)?;
    let arguments = args(r);
    let intermediate = format!("{first}_after(before)");
    let carried_proofs = continuation.inputs().iter().map(|port| {
        if first_plan.outputs.iter().any(|(p, _)| p.id == port.id) {
            format!("sym({first}{}_correct(values, before{arguments}))", result_suffix(first_plan, port.id))
        } else {
            format!("trans(placed_{}, sym({first}_preserves({}, before, trivial)))", port.id, p.inputs[&port.id].heather_name())
        }
    }).collect::<Vec<_>>().join(", ");
    let proofs = p.outputs.iter().map(|(port, _)| format!("{rest}{}_correct(values, {intermediate}{}{})", result_suffix(next, port.id), if carried_proofs.is_empty() { "" } else { ", " }, carried_proofs)).collect();
    let span = trans(&format!("{rest}_span({intermediate})"), &trans(&congr_step(next.byte_length, &format!("{first}_span(before)")), &compose("before.rip", first_plan.byte_length, next.byte_length)));
    let memory = format!("trans({rest}_memory({intermediate}), {first}_memory(before))");
    let ff = first.clone(); let fr = rest.clone();
    finish(n, r, p, incoming, m, sources, format!("CodeSequence({first}_code(), {rest}_code())"), results, proofs, memory, span,
        sequence_layout(&first, &rest), sequence_decodes(&first, &rest, first_plan.byte_length),
        sequence_length(&first, &rest, first_plan.byte_length, next.byte_length), sequence_bytes(&first, &rest),
        Frame::Any { children: vec![ff.clone(), fr.clone()],
            proof: format!("trans({fr}_preserves(register, {ff}_after(before), {fr}_kept(register, protected)), {ff}_preserves(register, before, {ff}_kept(register, protected)))") })
}

// A sequence's facts from its two children's (structured_sequence_length, …).
fn sequence_layout(first: &str, rest: &str) -> String {
    format!("structured_sequence_layout({first}_code(), {rest}_code(), {first}_layout(), {rest}_layout())")
}
fn sequence_decodes(first: &str, rest: &str, length: usize) -> String {
    format!("structured_sequence_decodes({first}_code(), {rest}_code(), {length}, start, {first}_byte_length(), {first}_decodes(start), {rest}_decodes(next_rip(start, {length})))")
}
fn sequence_length(first: &str, rest: &str, a: usize, b: usize) -> String {
    format!("structured_sequence_length({first}_code(), {rest}_code(), {a}, {b}, {first}_byte_length(), {rest}_byte_length())")
}
fn sequence_bytes(first: &str, rest: &str) -> (String, String) {
    (format!("{first}_lit() ++ {rest}_lit()"), format!("structured_sequence_bytes({first}_code(), {rest}_code(), {first}_lit(), {rest}_lit(), {first}_bytes_are(), {rest}_bytes_are())"))
}

/// A valuation's body over its populated entries (sorted by id), zero
/// elsewhere. Dispatched by a balanced `Nat::leb` tree rather than by peeling
/// the id: each case step at a `BitVec(width)` result costs in proportion to
/// the width, so a lookup that walked the id would be linear in it
/// (issues/valuation-lookup-case-step-cost.md).
fn valuation_body(entries: &[(u64, String)]) -> String {
    let zero = "@bitvec::BitVec::zero(width)";
    match entries {
        [] => zero.into(),
        [(id, value)] => format!("match Nat::leb({id}, id) {{ False => {zero}, True => match id.leb({id}) {{ False => {zero}, True => {value} }} }}"),
        _ => {
            let (left, right) = entries.split_at(entries.len() / 2);
            format!("match id.leb({}) {{ True => {}, False => {} }}", left.last().unwrap().0, valuation_body(left), valuation_body(right))
        }
    }
}

/// A width-indexed valuation entry: `value` at `width`, zero elsewhere, and
/// the original neutral value at its own width rather than a numeral rebuilt
/// from it.
pub fn at_width(width: u64, value: &str, depth: u64) -> String {
    let index = if depth == 0 { "width".into() } else { format!("w{depth}") };
    let succ = |s: String| (0..depth).fold(s, |s, _| format!("Succ({s})"));
    let zero = if depth == width { value.into() } else { format!("@bitvec::BitVec::zero({depth})") };
    let rest = if depth == width { format!("@bitvec::BitVec::zero({})", succ(format!("Succ(w{})", depth + 1))) }
        else { at_width(width, value, depth + 1) };
    format!("match {index} as λ n => BitVec({}) {{ Zero => {zero}, Succ(w{}) => {rest} }}", succ("n".into()), depth + 1)
}

/// A composition whose prefix is a helper call (cert::SourceValue). The
/// continuation is certified over its own valuation, where the prefix's
/// result is an input like any other, and used at the valuation that carries
/// the call's source spelling. `_link` equates the prefix's result with that
/// call: the one place the helper's body is compared with its source.
#[allow(clippy::too_many_arguments)]
fn emit_crossing(n: &str, r: &StructuredRegion, p: &LoweredStructured,
    prefix: &StructuredRegion, first_plan: &LoweredStructured,
    continuation: &StructuredRegion, next: &LoweredStructured,
    incoming: &Values, m: &mut Module, sources: &Crossings, value: &cert::SourceValue,
) -> Result<Values, LoweringError> {
    let first = format!("{n}_prefix"); let rest = format!("{n}_continuation");
    let port = prefix.outputs()[0];
    let width = port.width;
    emit(&first, prefix, first_plan, incoming, m, sources)?;
    // A prefix that is itself a crossing produced its argument under a name.
    let child = match prefix {
        StructuredRegion::Compose { prefix: inner, .. } => inner.outputs().first().copied().filter(|q| sources.values.contains_key(&q.id)),
        _ => None,
    };
    let spell = |value: &cert::SourceValue, replace: Option<(u64, &str)>| {
        value.render_named(cert::SourceType::Word(width), &|leaf: Port| val(incoming, leaf.id, leaf.width),
            &|produced: Port| match replace { Some((id, name)) if id == produced.id => Some(name.to_string()), _ => sources.spelled(incoming, produced) })
    };
    fun(m, format!("{n}_source"), false, logical(), format!("BitVec({width})"), spell(value, None));
    // What the prefix's own crossing computes from its child: the call when
    // the child is its argument, else the helper body's result.
    let meaning = child.and_then(|child| std::iter::once(value).chain(sources.bodies.get(&port.id).into_iter().flatten())
        .find(|meaning| meaning.produces(child.id)).map(|meaning| (child, meaning.clone())));
    let crossing = format!("{n}_source(values)");
    let first_result = format!("{first}{}", result_suffix(first_plan, port.id));
    let link = format!("{first_result}_result(values) = {}", placed_expression(width, &crossing));
    match meaning {
        // Stated over the argument as a variable, then used at its name: at
        // the name itself, conversion would unfold the argument's whole
        // computation before reducing the carry's lookup of it.
        Some((child, meaning)) => {
            let mut at = logical();
            at.push(emitted_parameter("s", format!("BitVec({})", child.width)));
            thm(m, format!("{n}_link_at"), false, at,
                format!("{} = {}", placed_expression(width, &format!("{first}_continuation_value({first}_carry(values, s), {width})")), placed_expression(width, &spell(&meaning, Some((child.id, "s"))))),
                "refl".into());
            thm(m, format!("{n}_link"), false, logical(), link, format!("{n}_link_at(values, {first}_source(values))"));
        }
        None => thm(m, format!("{n}_link"), false, logical(), link, "refl".into()),
    }
    sources.named.borrow_mut().insert(port.id, (crossing.clone(), sources.scope.get()));
    let own: Values = continuation.inputs().iter().map(|q| (q.id, format!("values(width, {})", q.id))).collect();
    let outer = sources.scope.get();
    sources.scopes.set(sources.scopes.get() + 1);
    sources.scope.set(sources.scopes.get());
    emit(&rest, continuation, next, &own, m, sources)?;
    sources.scope.set(outer);
    // The carry takes the crossing value as a parameter, and `_carry_at`
    // reads it back over a variable; a lookup is never converted against
    // the value's own name, which conversion would unfold first.
    let mut entries: Vec<_> = continuation.inputs().iter().map(|q|
        (q.id, if q.id == port.id { sources.at_width(m, width, "s") } else { incoming[&q.id].clone() })).collect();
    entries.sort_by_key(|(id, _)| *id);
    let mut carry_params = logical();
    carry_params.push(emitted_parameter("s", format!("BitVec({width})")));
    fun(m, format!("{n}_carry"), false, carry_params.clone(), "Valuation()".into(), format!("λ width id => {}", valuation_body(&entries)));
    thm(m, format!("{n}_carry_at"), false, carry_params, format!("{n}_carry(values, s)({width}, {}) = s", port.id), "refl".into());
    let carry = format!("{n}_carry(values, {crossing})");
    let arguments = args(r);
    let intermediate = format!("{first}_after(before)");
    let carried_proofs = continuation.inputs().iter().map(|q| {
        if q.id == port.id {
            let fact = format!("sym(trans({first_result}_correct(values, before{arguments}), {n}_link(values)))");
            format!("j(sym({n}_carry_at(values, {crossing})), λ y _ => {} = read_gpr({}, {intermediate}.gprs), {fact})",
                placed_expression(width, "y"), next.inputs[&q.id].heather_name())
        } else {
            format!("trans(placed_{}, sym({first}_preserves({}, before, trivial)))", q.id, p.inputs[&q.id].heather_name())
        }
    }).collect::<Vec<_>>().join(", ");
    let proofs = p.outputs.iter().map(|(q, _)| format!("{rest}{}_correct({carry}, {intermediate}{}{})", result_suffix(next, q.id), if carried_proofs.is_empty() { "" } else { ", " }, carried_proofs)).collect();
    let results = p.outputs.iter().map(|(q, _)| (q.id, format!("{rest}{}_value({carry}, width)", result_suffix(next, q.id)))).collect();
    let span = trans(&format!("{rest}_span({intermediate})"), &trans(&congr_step(next.byte_length, &format!("{first}_span(before)")), &compose("before.rip", first_plan.byte_length, next.byte_length)));
    let memory = format!("trans({rest}_memory({intermediate}), {first}_memory(before))");
    let ff = first.clone(); let fr = rest.clone();
    let exported = finish(n, r, p, incoming, m, sources, format!("CodeSequence({first}_code(), {rest}_code())"), results, proofs, memory, span,
        sequence_layout(&first, &rest), sequence_decodes(&first, &rest, first_plan.byte_length),
        sequence_length(&first, &rest, first_plan.byte_length, next.byte_length), sequence_bytes(&first, &rest),
        Frame::Any { children: vec![ff.clone(), fr.clone()],
            proof: format!("trans({fr}_preserves(register, {ff}_after(before), {fr}_kept(register, protected)), {ff}_preserves(register, before, {ff}_kept(register, protected)))") })?;
    // The result as the source computes it from the crossing value, stated
    // over the value as a variable: what an exporter compares with the
    // source, instead of converting through the carry at the value's name.
    // After `finish`, which declares `_result`.
    if let [(out, _)] = p.outputs.as_slice() {
        if let Some(meaning) = sources.bodies.get(&out.id).and_then(|bodies| bodies.iter().find(|meaning| meaning.produces(port.id))) {
            let spell = |at: &str| {
                meaning.render_named(cert::SourceType::Word(out.width), &|leaf: Port| val(incoming, leaf.id, leaf.width),
                    &|produced: Port| if produced.id == port.id { Some(at.to_string()) } else { sources.spelled(incoming, produced) })
            };
            let mut at = logical();
            at.push(emitted_parameter("s", format!("BitVec({width})")));
            thm(m, format!("{n}_meaning_at"), false, at,
                format!("{} = {}", placed_expression(out.width, &format!("{rest}{}_value({n}_carry(values, s), {})", result_suffix(next, out.id), out.width)), placed_expression(out.width, &spell("s"))),
                "refl".into());
            thm(m, format!("{n}_meaning"), false, logical(),
                format!("{n}{}_result(values) = {}", result_suffix(p, out.id), placed_expression(out.width, &spell(&crossing))),
                format!("{n}_meaning_at(values, {crossing})"));
        }
    }
    Ok(exported)
}

fn emit_parts(n: &str, r: &StructuredRegion, p: &LoweredStructured, parts: &[(Region, LoweredDag)], incoming: &Values, m: &mut Module, sources: &Crossings) -> Result<Values, LoweringError> {
    let mut results = Values::new();
    let mut proofs = Vec::new();
    let mut names = Vec::new();
    let mut states = vec!["before".to_string()];
    let mut length = 0;
    let mut decoding = Vec::new();
    let mut memory = "refl".to_string();
    let mut span = "refl".to_string();
    for (i, (region, dag)) in parts.iter().enumerate() {
        let name = format!("{n}_part_{i}");
        let port = region.outputs[0];
        let plan = LoweredStructured { inputs: p.inputs.clone(), output: (port, dag.output_register), outputs: vec![(port, dag.output_register)], clobbered: dag.clobbered.clone(), byte_length: dag.instructions.iter().map(|v| v.canonical_length()).sum(), body: StructuredPlan::Dataflow(dag.clone()) };
        results.extend(emit(&name, &StructuredRegion::Dataflow(region.clone()), &plan, incoming, m, sources)?);
        let state = states.last().unwrap();
        let bindings = r.inputs().iter().map(|port| {
            let mut proof = format!("placed_{}", port.id);
            for (j, prev) in names.iter().enumerate() {
                proof = format!("trans({proof}, sym({prev}_preserves({}, {}, trivial)))", p.inputs[&port.id].heather_name(), states[j]);
            }
            format!(", {proof}")
        }).collect::<String>();
        proofs.push(format!("{name}_correct(values, {state}{bindings})"));
        for j in 0..i {
            proofs[j] = format!("trans({name}_preserves({}, {state}, trivial), {})", p.outputs[j].1.heather_name(), proofs[j]);
        }
        let part_memory = format!("{name}_memory({state})");
        let part_span = format!("{name}_span({state})");
        memory = if i == 0 { part_memory } else { trans(&part_memory, &memory) };
        span = if i == 0 { part_span } else { trans(&part_span, &trans(&congr_step(plan.byte_length, &span), &compose("before.rip", length, plan.byte_length))) };
        decoding.push(format!("{name}_decodes(next_rip(start, {length}))"));
        length += plan.byte_length;
        states.push(format!("{name}_after({state})"));
        names.push(name);
    }
    let mut code = format!("{}_code()", names[0]);
    let mut layout = format!("{}_layout()", names[0]);
    let mut decodes = decoding[0].clone();
    for i in 1..names.len() {
        code = format!("CodeSequence({code}, {}_code())", names[i]);
        layout = format!("⟨{layout}, {}_layout()⟩", names[i]);
        decodes = format!("⟨{decodes}, {}⟩", decoding[i]);
    }
    let mut lit = format!("{}_lit()", names[0]);
    for name in &names[1..] { lit = format!("({lit}) ++ {name}_lit()"); }
    finish(n, r, p, incoming, m, sources, code, results, proofs, memory, span, layout, decodes, "refl".into(), (lit, "refl".into()),
        {
            let mut proof = "refl".to_string();
            for (i, name) in names.iter().enumerate() {
                let fact = format!("{name}_preserves(register, {}, {name}_kept(register, protected))", states[i]);
                proof = if i == 0 { fact } else { trans(&fact, &proof) };
            }
            Frame::Any { children: names, proof }
        })
}
