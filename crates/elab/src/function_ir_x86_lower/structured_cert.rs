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
}

impl Crossings<'_> {
    /// A produced value as this scope has it: an input carried in, else a
    /// name made here; `None` spells it out in full.
    fn spelled(&self, incoming: &Values, port: Port) -> Option<String> {
        if incoming.contains_key(&port.id) { return Some(val(incoming, port.id, port.width)); }
        self.named.borrow().get(&port.id).filter(|(_, scope)| *scope == self.scope.get()).map(|(name, _)| name.clone())
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
    let lowered = lower_structured_results(region, inputs, temporaries, outputs)?;
    let mut module = Module::default();
    let values = region.inputs().iter().map(|p| (p.id, format!("values(width, {})", p.id))).collect();
    let crossings = Crossings { values: sources, bodies, named: Default::default(), scope: Default::default(), scopes: Default::default() };
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
/// `(A₁ ++ (A₂ ++ …)).len() = L₁ + (L₂ + …)` from each piece's fact
/// `Aᵢ.len() = Lᵢ`.
fn appended_length(pieces: &[(String, String, usize)]) -> String {
    let (last, rest) = pieces.split_last().unwrap();
    let mut spine = last.0.clone();
    let mut proof = last.1.clone();
    for (piece, fact, length) in rest.iter().rev() {
        proof = trans(&format!("list::List::len_append({piece}, {spine})"),
            &trans(&format!("cong_fn<Nat, Nat>(λ k => k + ({spine}).len(), {fact})"), &format!("cong_fn<Nat, Nat>(λ k => {length} + k, {proof})")));
        spine = format!("{piece} ++ {spine}");
    }
    proof
}
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
            Node::UnsignedLessThan { width: operand_width, left, right, .. } | Node::SignedLessThan { width: operand_width, left, right, .. } => {
                let op = if matches!(node, Node::UnsignedLessThan { .. }) { "unsigned_lt_bit" } else { "signed_lt_bit" };
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
            // A passthrough is spelled as the value it passes, as the source
            // spells it; `0 | x` makes conversion evaluate `x` bit by bit.
            Node::BitOr { left, right, .. } if r.nodes.iter().any(|n| matches!(*n, Node::Const { output, value: 0, .. } if output == left)) => values[&right].clone(),
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
    let mut witness = "trivial".to_string();
    for _ in &r.nodes { witness = format!("⟨refl, {witness}⟩"); }
    thm(m, format!("{n}_graph"), false, logical(), format!("RegionHolds({n}_raw(), {n}_valuation(values))"), witness);
    values
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
    let arguments = args(r);
    let (code, results, proofs, memory, span, layout, decoding, byte_length, bytes, frame): (String, Values, Vec<String>, String, String, String, String, String, (String, String), Box<dyn Fn(Gpr) -> String>) = match (&r, &p.body) {
        (StructuredRegion::Dataflow(region), StructuredPlan::Dataflow(dag)) => {
            m.raw(cert::render_region_function(&format!("{n}_raw"), region));
            let values = dataflow_values(n, region, incoming, m);
            let leaf = format!("{n}_leaf");
            let emission = generate_selected(&leaf, &format!("{n}_raw()"), region, dag.clone())?;
            m.raw(emission.text);
            thm(m, format!("{n}_leaf_span"), false, start(), format!("{leaf}_final_rip(start) = next_rip(start, {length})"), render_block_span_proof(&dag.instructions));
            let proof = format!("{leaf}_refines_function_ir({n}_valuation(values), before{arguments}, {n}_graph(values))");
            let frame_leaf = leaf.clone();
            (format!("CodeBlock({leaf}_instructions())"), Values::from([(p.output.0.id, values[&p.output.0.id].clone())]), vec![proof],
                format!("{leaf}_preserves_memory(before)"),
                format!("trans({leaf}_advances_rip(before), {n}_leaf_span(before.rip))"),
                "trivial".into(), format!("{leaf}_block_decodes(start)"), "refl".into(), (literal_bytes(&encoding::encode_instructions(&dag.instructions)), "refl".into()),
                Box::new(move |reg| format!("{frame_leaf}_preserves_protected({}, before, trivial)", reg.heather_name())))
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
        (StructuredRegion::Conditional { condition, when_true, when_false, .. }, StructuredPlan::Conditional { condition_register, when_true: yes, when_false: no, false_displacement, join_displacement, near }) => {
            let t = format!("{n}_true"); let f = format!("{n}_false");
            let tv = emit(&t, when_true, yes, incoming, m, sources)?; let fv = emit(&f, when_false, no, incoming, m, sources)?;
            let register = condition_register.heather_name();
            // The two encodings differ in their jumps only: rel8 JZ/JMP (2
            // bytes each), or JZ rel32 (6) and JMP rel32 (5).
            let (jz, jmp) = if *near { (6usize, 5usize) } else { (2, 2) };
            let (fdn, jdn) = (*false_displacement as usize, *join_displacement as usize);
            let (fd, jd) = if *near { (format!("@bitvec::BitVec::ofNat(32, {fdn})"), format!("@bitvec::BitVec::ofNat(32, {jdn})")) }
                else { (format!("@bitvec::BitVec::ofNat(8, {fdn})"), format!("@bitvec::BitVec::ofNat(8, {jdn})")) };
            let (entry_fn, read_fn, property_fn, cases_fn, constructor) = if *near {
                ("structured_near_entry", "structured_near_branch_read", "structured_near_branch_property", "structured_near_branch_cases", "CodeBranchNear")
            } else { ("structured_branch_entry", "structured_branch_read", "structured_branch_property", "structured_branch_cases", "CodeBranch") };
            let (jz_bytes, jmp_bytes, jz_decodes, jmp_decodes) = if *near {
                (format!("near_control_bytes(JumpZeroNear({fd}))"), format!("near_control_bytes(JumpNear({jd}))"),
                    format!("decode_near_control_complete(JumpZeroNear({fd}))"), format!("decode_near_control_complete(JumpNear({jd}))"))
            } else {
                (format!("short_control_bytes(JumpZero({fd}))"), format!("short_control_bytes(Jump({jd}))"),
                    format!("decode_short_control_complete(JumpZero({fd}))"), format!("decode_short_control_complete(Jump({jd}))"))
            };
            let target = |start: &str, length: usize, displacement: &str| if *near { format!("near_branch_target({start}, {length}, {displacement})") }
                else { format!("short_branch_target({start}, {displacement})") };
            let entry = format!("{entry_fn}({register}, {fd}, before)");
            let branch_args = format!("{register}, {fd}, {jd}, {t}_code(), {f}_code(), before");
            let bit = test_of(&incoming[condition]).unwrap_or_else(|| format!("@bitvec::BitVec::head_bit(0, {})", val(incoming, *condition, 1)));
            let placed = format!("test_bit_value_placed_zf(λ width _ => {}, {condition}, {register}, before, placed_{condition})", incoming[condition]);
            let child_args = args(when_true);
            let mut results = Values::new();
            let mut proofs = Vec::new();
            for &(port, reg) in &p.outputs {
                let output = reg.heather_name();
                let suffix = result_suffix(p, port.id);
                let child_t = normalize_bit_result(format!("{t}{suffix}_correct(values, {entry}{child_args})"), &tv, port);
                let child_f = normalize_bit_result(format!("{f}{suffix}_correct(values, {entry}{child_args})"), &fv, port);
                let rt = format!("read_gpr({output}, {t}_after({entry}).gprs)"); let rf = format!("read_gpr({output}, {f}_after({entry}).gprs)");
                let choice = format!("select_zero_test({bit}, structured_test({register}, before).flags.zf, {rt}, {rf}, {placed})");
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
            let tested = format!("structured_test({register}, before)");
            let (not_taken, taken) = if *near {
                (format!("near_not_taken_rip({fd}, {tested}, selected)"), format!("near_taken_rip({fd}, {tested}, selected)"))
            } else {
                (format!("jump_zero_not_taken_rip({tested}.flags.zf, {test_rip}, {fd}, selected)"), format!("jump_zero_taken_rip({tested}.flags.zf, {test_rip}, {fd}, selected)"))
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
            let fixed = [("test", format!("canonical_bytes(TestRR({register}, {register}))"), 3), ("jump_zero", jz_bytes.clone(), jz), ("jump", jmp_bytes.clone(), jmp)];
            for (tag, bytes, size) in &fixed {
                thm(m, format!("{n}_{tag}_length"), false, vec![], format!("{bytes}.len() = {size}"), "refl".into());
            }
            let byte_length = appended_length(&[
                (fixed[0].1.clone(), format!("{n}_test_length()"), 3), (fixed[1].1.clone(), format!("{n}_jump_zero_length()"), jz),
                (length_of(&t), format!("{t}_byte_length()"), yes.byte_length), (fixed[2].1.clone(), format!("{n}_jump_length()"), jmp),
                (length_of(&f), format!("{f}_byte_length()"), no.byte_length)]);
            let false_layout = transported(&t, &format!("{} = next_rip(start, {jz} + (y + {jmp}))", target("start", jz, &fd)), &format!("{n}_false_target(start)"));
            let join_layout = transported(&f, &format!("{} = next_rip(start, {jmp} + y)", target("start", jmp, &jd)), &format!("{n}_join_target(start)"));
            let false_decodes = format!("j(cong_fn<Nat, Nat>(λ k => {head} + k + {jmp}, sym({t}_byte_length())), λ y _ => StructuredDecodes({f}_code(), next_rip(start, y)), {f}_decodes(next_rip(start, {head} + {} + {jmp})))", yes.byte_length);
            (format!("{constructor}({register}, {fd}, {jd}, {t}_code(), {f}_code())"),
                results, proofs, memory, span,
                format!("⟨λ start => {false_layout}, ⟨λ start => {join_layout}, ⟨{t}_layout(), {f}_layout()⟩⟩⟩"),
                format!("⟨canonical_encoding_decodes(start, TestRR({register}, {register})), ⟨{jz_decodes}, ⟨{t}_decodes(next_rip(start, {head})), ⟨{jmp_decodes}, {false_decodes}⟩⟩⟩⟩"),
                byte_length,
                {
                    // The fixed pieces are literal too; conversion checks each
                    // against its few-byte encoding.
                    let r = encoding::register_code(*condition_register);
                    let (jz_literal, jmp_literal) = if *near {
                        let mut jz = vec![0x0f, 0x84]; jz.extend((fdn as u32).to_le_bytes());
                        let mut jmp = vec![0xe9]; jmp.extend((jdn as u32).to_le_bytes());
                        (literal_bytes(&jz), literal_bytes(&jmp))
                    } else { (literal_bytes(&[0x74, fdn as u8]), literal_bytes(&[0xeb, jdn as u8])) };
                    let literal = [literal_bytes(&[0x48 | (r >> 3) | ((r >> 3) << 2), 0x85, 0xc0 | ((r & 7) << 3) | (r & 7)]), jz_literal, jmp_literal];
                    let lit = |pieces: &[String; 3], yes: &str, no: &str| format!("{} ++ ({} ++ ({yes} ++ ({} ++ {no})))", pieces[0], pieces[1], pieces[2]);
                    let code = [fixed[0].1.clone(), fixed[1].1.clone(), fixed[2].1.clone()];
                    (lit(&literal, &format!("{t}_lit()"), &format!("{f}_lit()")),
                        trans(&format!("cong_fn<List<BitVec(8)>, List<BitVec(8)>>(λ ys => {}, {t}_bytes_are())", lit(&code, "ys", &format!("{f}_bytes()"))),
                            &format!("cong_fn<List<BitVec(8)>, List<BitVec(8)>>(λ zs => {}, {f}_bytes_are())", lit(&code, &format!("{t}_lit()"), "zs"))))
                },
                Box::new(move |reg| format!("{frame_property}({frame_branch_args}, λ after => read_gpr({}, after.gprs) = read_gpr({}, before.gprs), {frame_t}_preserves({}, {frame_entry}, trivial), {frame_f}_preserves({}, {frame_entry}, trivial))", reg.heather_name(), reg.heather_name(), reg.heather_name(), reg.heather_name())))
        }
        _ => return Err(LoweringError::InvalidStructuredRegion("selected plan disagrees with region shape".into())),
    };
    finish(n, r, p, incoming, m, code, results, proofs, memory, span, layout, decoding, byte_length, bytes, frame)
}

fn result_suffix(p: &LoweredStructured, id: u64) -> String {
    if id == p.output.0.id { String::new() } else { format!("_output_{id}") }
}

#[allow(clippy::too_many_arguments)]
fn finish(n: &str, r: &StructuredRegion, p: &LoweredStructured, incoming: &Values, m: &mut Module,
    code: String, results: Values, proofs: Vec<String>, memory: String, span: String,
    layout: String, decoding: String, byte_length: String, bytes: (String, String), frame: Box<dyn Fn(Gpr) -> String>,
) -> Result<Values, LoweringError> {
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
    thm(m, format!("{n}_rip"), true, before(), format!("{n}_after(before).rip = next_rip(before.rip, {}.len())", length_of(n)),
        transported(n, &format!("{n}_after(before).rip = next_rip(before.rip, y)"), &format!("{n}_span(before)")));
    fun(m, format!("{n}_Protected"), false, vec![emitted_parameter("register", "Gpr")], "Type".into(), format!("match register {{ {} }}", render_protected_arms(&p.clobbered)));
    let mut arms = Vec::new();
    for reg in [Gpr::Rax, Gpr::Rcx, Gpr::Rdx, Gpr::Rbx, Gpr::Rsp, Gpr::Rbp, Gpr::Rsi, Gpr::Rdi, Gpr::R8, Gpr::R9, Gpr::R10, Gpr::R11, Gpr::R12, Gpr::R13, Gpr::R14, Gpr::R15] {
        arms.push(format!("{} => {}", reg.heather_name(), if p.clobbered.contains(&reg) { "protected ⊢ false_elim(protected)".into() } else { format!("_ ⊢ {}", frame(reg)) }));
    }
    thm(m, format!("{n}_preserves"), true, vec![emitted_parameter("register", "Gpr"), emitted_parameter("before", "MachineState<M>")], format!("{n}_Protected(register) → read_gpr(register, {n}_after(before).gprs) = read_gpr(register, before.gprs)"), format!("match register {{ {} }}", arms.join(", ")));
    for &(port, reg) in &p.outputs {
        let name = format!("{n}{}", result_suffix(p, port.id));
        let output = reg.heather_name();
        thm(m, format!("{name}_artifact"), true, public.clone(), format!("StructuredArtifact<M>({n}_code(), before, {output}, {name}_result(values), {n}_Protected)"),
            format!("StructuredArtifact(after := {n}_after(before), execution := refl, layout := {n}_layout(), decoding := {n}_decodes(before.rip), result_correct := {name}_correct(values, before{arguments}), memory_preserved := {n}_memory(before), rip_correct := {n}_rip(before), registers_preserved := λ register protected => {n}_preserves(register, before, protected))"));
    }
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
    finish(n, r, p, incoming, m, format!("CodeSequence({first}_code(), {rest}_code())"), results, proofs, memory, span,
        format!("⟨{first}_layout(), {rest}_layout()⟩"),
        format!("⟨{first}_decodes(start), {}⟩", transported(&first, &format!("StructuredDecodes({rest}_code(), next_rip(start, y))"), &format!("{rest}_decodes(next_rip(start, {}))", first_plan.byte_length))),
        appended_length(&[(length_of(&first), format!("{first}_byte_length()"), first_plan.byte_length), (length_of(&rest), format!("{rest}_byte_length()"), next.byte_length)]),
        (format!("{first}_lit() ++ {rest}_lit()"), trans(&format!("cong_fn<List<BitVec(8)>, List<BitVec(8)>>(λ xs => xs ++ {rest}_bytes(), {first}_bytes_are())"),
            &format!("cong_fn<List<BitVec(8)>, List<BitVec(8)>>(λ ys => {first}_lit() ++ ys, {rest}_bytes_are())"))),
        Box::new(move |reg| format!("trans({fr}_preserves({}, {ff}_after(before), trivial), {ff}_preserves({}, before, trivial))", reg.heather_name(), reg.heather_name())))
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
        (q.id, if q.id == port.id { at_width(width, "s", 0) } else { incoming[&q.id].clone() })).collect();
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
    let exported = finish(n, r, p, incoming, m, format!("CodeSequence({first}_code(), {rest}_code())"), results, proofs, memory, span,
        format!("⟨{first}_layout(), {rest}_layout()⟩"),
        format!("⟨{first}_decodes(start), {}⟩", transported(&first, &format!("StructuredDecodes({rest}_code(), next_rip(start, y))"), &format!("{rest}_decodes(next_rip(start, {}))", first_plan.byte_length))),
        appended_length(&[(length_of(&first), format!("{first}_byte_length()"), first_plan.byte_length), (length_of(&rest), format!("{rest}_byte_length()"), next.byte_length)]),
        (format!("{first}_lit() ++ {rest}_lit()"), trans(&format!("cong_fn<List<BitVec(8)>, List<BitVec(8)>>(λ xs => xs ++ {rest}_bytes(), {first}_bytes_are())"),
            &format!("cong_fn<List<BitVec(8)>, List<BitVec(8)>>(λ ys => {first}_lit() ++ ys, {rest}_bytes_are())"))),
        Box::new(move |reg| format!("trans({fr}_preserves({}, {ff}_after(before), trivial), {ff}_preserves({}, before, trivial))", reg.heather_name(), reg.heather_name())))?;
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
    finish(n, r, p, incoming, m, code, results, proofs, memory, span, layout, decodes, "refl".into(), (lit, "refl".into()),
        Box::new(move |reg| {
            let mut proof = "refl".to_string();
            for (i, name) in names.iter().enumerate() {
                let fact = format!("{name}_preserves({}, {}, trivial)", reg.heather_name(), states[i]);
                proof = if i == 0 { fact } else { trans(&fact, &proof) };
            }
            proof
        }))
}
