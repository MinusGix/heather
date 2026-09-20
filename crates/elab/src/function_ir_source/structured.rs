//! Untrusted reflection into recursive FunctionIR and composition of checked
//! source agreement with the shared physical execution artifact.
use super::*;
use cert::StructuredRegion;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReflectedStructuredFunction {
    pub source_name: String,
    pub region: StructuredRegion,
}

/// Reflect tail-position Boolean matches on resolved unsigned comparisons.
/// Arithmetic remains the shared two-word DAG fragment. Kernel `Case` arms
/// introduce an otherwise unused payload binder, including at nested matches.
pub fn reflect_elaborated_structured(
    elaborator: &Elaborator,
    source_name: &str,
) -> Result<ReflectedStructuredFunction, SourceError> {
    let caller_abs = elaborator.global_abs(source_name).ok_or_else(|| {
        SourceError::Unsupported(format!("unknown source function `{source_name}`"))
    })?;
    let source_name = elaborator.global_qualified_name_at(caller_abs).ok_or_else(|| {
        SourceError::Unsupported("source function has no canonical global name".into())
    })?;
    let (ty, body) = elaborator.global_body(&source_name).ok_or_else(|| {
        SourceError::Unsupported("structured source must be a transparent computing function".into())
    })?;
    if pi_arity(&ty) != 2 { return unsupported("structured source requires exactly two word parameters"); }
    let Term::Lam { body, .. } = &*body else { return unsupported("missing source parameter"); };
    let Term::Lam { body, .. } = &**body else { return unsupported("missing source parameter"); };
    let operations = OperationGlobals::resolve(elaborator)?;
    let comparison = elaborator.global_abs("bitvec::unsigned_lt_bit").ok_or_else(|| {
        SourceError::Unsupported("required operation `bitvec::unsigned_lt_bit` is not loaded".into())
    })?;
    let mut builder = Builder { caller_abs, operations, comparison, next_id: 3 };
    let region = builder.region(body, 0)?;
    cert::validate_structured_region(&region).map_err(SourceError::InvalidRegion)?;
    Ok(ReflectedStructuredFunction { source_name, region })
}

struct Builder {
    caller_abs: usize,
    operations: OperationGlobals,
    comparison: usize,
    next_id: u64,
}

fn inputs() -> Vec<Port> { vec![Port { id: 0, width: 64 }, Port { id: 1, width: 64 }] }
fn outputs() -> Vec<Port> { vec![Port { id: 2, width: 64 }] }

impl Builder {
    fn dag(&self) -> DagBuilder {
        DagBuilder { next_id: self.next_id, ids: BTreeMap::new(), nodes: Vec::new(), node_expressions: Vec::new() }
    }

    fn expression(&self, term: &Term, depth: u32) -> Result<SourceExpr, SourceError> {
        reflect_term_under(term, self.caller_abs, &self.operations, depth)
    }

    fn region(&mut self, term: &Term, depth: u32) -> Result<StructuredRegion, SourceError> {
        if let Term::Case { scrut, case_l, case_r, .. } = term {
            let (head, args) = application_spine(scrut);
            let Term::GlobalTm { var, .. } = head else {
                return unsupported("structured condition must be a resolved unsigned comparison");
            };
            if self.caller_abs.checked_sub(1 + var.0 as usize) != Some(self.comparison)
                || args.len() != 3 || nat_literal(args[0]) != Some(64) {
                return unsupported("structured condition must call bitvec::unsigned_lt_bit at width 64");
            }
            let mut dag = self.dag();
            let left = dag.lower(&self.expression(args[1], depth)?)?;
            let right = dag.lower(&self.expression(args[2], depth)?)?;
            let condition = dag.next_id;
            self.next_id = condition.checked_add(1).ok_or_else(|| {
                SourceError::Unsupported("source graph exhausted stable IDs".into())
            })?;
            dag.nodes.push(Node::UnsignedLessThan { width: 64, output: condition, left, right });
            let bit = Port { id: condition, width: 1 };
            let prefix = Region { inputs: inputs(), nodes: dag.nodes, outputs: vec![bit] };
            let when_false = Box::new(self.region(case_l, depth + 1)?);
            let when_true = Box::new(self.region(case_r, depth + 1)?);
            let mut available = inputs();
            available.push(bit);
            Ok(StructuredRegion::Sequence { prefix, continuation: Box::new(StructuredRegion::Conditional {
                inputs: available, condition, arguments: inputs(), outputs: outputs(), when_true, when_false,
            }) })
        } else {
            let expression = self.expression(term, depth)?;
            let mut dag = self.dag();
            // Name the last operation with the common result ID directly;
            // subexpressions keep globally fresh IDs across both successors.
            let final_node = match &expression {
                SourceExpr::Binary { operation, left, right } => {
                    let left = dag.lower(left)?;
                    let right = dag.lower(right)?;
                    operation.node(2, left, right)
                }
                SourceExpr::Constant(value) => Node::Const { width: 64, output: 2, value: *value },
                SourceExpr::Input(_) => return unsupported("structured result leaves currently require arithmetic or a constant"),
            };
            dag.nodes.push(final_node);
            self.next_id = dag.next_id;
            Ok(StructuredRegion::Dataflow(Region { inputs: inputs(), nodes: dag.nodes, outputs: outputs() }))
        }
    }
}

/// Check recovery of the source expression from a structured graph. This is
/// deliberately only source agreement: it is neither an inhabitant of
/// `StructuredRegionHolds` nor a physical execution/byte certificate. Keeping
/// it separate lets the next composition step reject stale source locally.
pub fn generate_structured_source_expansion(
    prefix: &str,
    reflected: &ReflectedStructuredFunction,
) -> Result<String, SourceError> {
    cert::validate_structured_region(&reflected.region).map_err(SourceError::InvalidRegion)?;
    if reflected.region.inputs() != inputs() || reflected.region.outputs() != outputs() {
        return unsupported("structured source expansion requires the reflected two-word interface");
    }
    let mut module = Module::default();
    module.raw("import bitvec;\nimport bool;");
    if let Some((source_module, _)) = reflected.source_name.rsplit_once("::") {
        module.raw(format!("import {source_module};"));
    }
    let parameters = || vec![
        Parameter::explicit("left", HeatherExpr::name("BitVec(64)")),
        Parameter::explicit("right", HeatherExpr::name("BitVec(64)")),
    ];
    let arguments = || [HeatherExpr::name("left"), HeatherExpr::name("right")];
    let initial = BTreeMap::from([(0, (64, arguments()[0].clone())), (1, (64, arguments()[1].clone()))]);
    let mut expansion = Expansion { prefix, module: &mut module, next_name: 0 };
    let result = expansion.region(&reflected.region, initial)?;
    let name = format!("{prefix}_expression");
    module.declaration(Declaration::function(&name, HeatherExpr::name("BitVec(64)"),
        Block::expression(result)).parameters(parameters()));
    module.declaration(Declaration::theorem(format!("{prefix}_source_expands"),
        HeatherExpr::equal(HeatherExpr::call(name.as_str(), arguments()),
            HeatherExpr::call(reflected.source_name.as_str(), arguments())),
        Block::expression(HeatherExpr::name("refl"))).parameters(parameters()));
    Ok(module.render())
}

// The expression renderer folds FunctionIR itself, not a second source AST.
// Named subexpressions keep repeated DAG uses from duplicating source text.
struct Expansion<'a> {
    prefix: &'a str,
    module: &'a mut Module,
    next_name: usize,
}
type Expressions = BTreeMap<u64, (u64, HeatherExpr)>;

fn operand(values: &Expressions, id: u64, width: u64) -> Result<HeatherExpr, SourceError> {
    match values.get(&id) {
        Some((actual, expression)) if *actual == width => Ok(expression.clone()),
        _ => unsupported(&format!("source expansion has no value {id} at width {width}")),
    }
}

impl Expansion<'_> {
    fn dataflow(&mut self, region: &Region, values: &mut Expressions) -> Result<(), SourceError> {
        for node in &region.nodes {
            let (id, width, body) = match *node {
                Node::Const { width: 64, output, value } => (output, 64,
                    HeatherExpr::call("bitvec::ofNat", [HeatherExpr::nat(64), HeatherExpr::nat(value)])),
                Node::Add { width: 64, output, left, right }
                | Node::Sub { width: 64, output, left, right }
                | Node::BitAnd { width: 64, output, left, right }
                | Node::BitOr { width: 64, output, left, right }
                | Node::BitXor { width: 64, output, left, right }
                | Node::UnsignedLessThan { width: 64, output, left, right } => {
                    let (function, width) = match node {
                        Node::Add { .. } => ("bitvec::add", 64),
                        Node::Sub { .. } => ("bitvec::sub", 64),
                        Node::BitAnd { .. } => ("bitvec::band", 64),
                        Node::BitOr { .. } => ("bitvec::bor", 64),
                        Node::BitXor { .. } => ("bitvec::bxor", 64),
                        Node::UnsignedLessThan { .. } => ("bitvec::unsigned_lt_bit", 1),
                        _ => unreachable!(),
                    };
                    (output, width, HeatherExpr::call(function, [HeatherExpr::nat(64),
                        operand(values, left, 64)?, operand(values, right, 64)?]))
                }
                _ => return unsupported("source expansion encountered an unsupported node"),
            };
            let name = format!("{}_value_{}", self.prefix, self.next_name);
            self.next_name += 1;
            self.module.declaration(Declaration::function(&name,
                HeatherExpr::name(if width == 1 { "Bool" } else { "BitVec(64)" }),
                Block::expression(body))
                .parameter(Parameter::explicit("left", HeatherExpr::name("BitVec(64)")))
                .parameter(Parameter::explicit("right", HeatherExpr::name("BitVec(64)"))));
            values.insert(id, (width, HeatherExpr::call(name.as_str(),
                [HeatherExpr::name("left"), HeatherExpr::name("right")])));
        }
        Ok(())
    }

    fn region(&mut self, region: &StructuredRegion, mut values: Expressions) -> Result<HeatherExpr, SourceError> {
        // Drop values not explicitly carried by this region's interface.
        values.retain(|id, _| region.inputs().iter().any(|port| port.id == *id));
        for port in region.inputs() { operand(&values, port.id, port.width)?; }
        match region {
            StructuredRegion::Dataflow(body) => {
                self.dataflow(body, &mut values)?;
                if body.outputs.len() != 1 { return unsupported("source expansion requires one result"); }
                operand(&values, body.outputs[0].id, 64)
            }
            StructuredRegion::Sequence { prefix, continuation } => {
                self.dataflow(prefix, &mut values)?;
                self.region(continuation, values)
            }
            StructuredRegion::Conditional { condition, when_true, when_false, .. } => {
                let condition = operand(&values, *condition, 1)?;
                let yes = self.region(when_true, values.clone())?;
                let no = self.region(when_false, values)?;
                Ok(HeatherExpr::raw(format!("match {} {{ False => {}, True => {} }}",
                    condition.render(), no.render(), yes.render())))
            }
        }
    }
}

/// Compile the reflected structured source and close all internal graph
/// assumptions. The public artifact needs only an arbitrary entry machine.
pub fn generate_elaborated_structured_x86(
    elaborator: &Elaborator, prefix: &str, source_name: &str,
    input_registers: [Gpr; 2], temporaries: &[Gpr], output: Gpr,
) -> Result<x86::StructuredX86Emission, SourceError> {
    let reflected = reflect_elaborated_structured(elaborator, source_name)?;
    let placements = x86::Placements::from([(0, input_registers[0]), (1, input_registers[1])]);
    let mut emission = x86::generate_structured(prefix, &reflected.region, &placements, temporaries, output).map_err(SourceError::Lowering)?;
    let mut module = Module::default();
    module.raw(generate_structured_source_expansion(prefix, &reflected)?
        .replace("import bitvec;\n", "").replace("import bool;\n", ""));
    module.raw(emission.text);
    let source = &reflected.source_name;
    let left = format!("read_gpr({}, before.gprs)", input_registers[0].heather_name());
    let right = format!("read_gpr({}, before.gprs)", input_registers[1].heather_name());
    let vals = format!("{prefix}_entry_values(before)");
    let decl = |module: &mut Module, name: String, machine: bool, ps: Vec<Parameter>, ty: String, body: String, theorem: bool| {
        let body = Block::expression(HeatherExpr::raw(body));
        let d = if theorem { Declaration::theorem(name, HeatherExpr::raw(ty), body) }
            else { Declaration::function(name, HeatherExpr::raw(ty), body) };
        let d = d.parameters(ps);
        module.declaration(if machine { d.generic("M") } else { d });
    };
    let before = || vec![Parameter::explicit("before", HeatherExpr::name("MachineState<M>"))];
    let values = || vec![Parameter::explicit("values", HeatherExpr::name("Valuation()"))];
    decl(&mut module, format!("{prefix}_result_expands"), false, values(),
        format!("{prefix}_result(values) = {prefix}_expression(values(64, 0), values(64, 1))"), "refl".into(), true);
    decl(&mut module, format!("{prefix}_denotes_source"), false, values(),
        format!("{prefix}_result(values) = {source}(values(64, 0), values(64, 1))"),
        format!("trans({prefix}_result_expands(values), {prefix}_source_expands(values(64, 0), values(64, 1)))"), true);
    decl(&mut module, format!("{prefix}_entry_values"), true, before(), "Valuation()".into(),
        format!("λ width id => match id {{ Zero => bitvec::ofNat(width, bitvec::toNat(64, {left})), Succ(rest) => match rest {{ Zero => bitvec::ofNat(width, bitvec::toNat(64, {right})), Succ(_) => bitvec::zero(width) }} }}"), false);
    let left_roundtrip = format!("bitvec::ofNat_toNat(64, {left})");
    let right_roundtrip = format!("bitvec::ofNat_toNat(64, {right})");
    let source_roundtrip = format!("trans(cong_fn<BitVec(64), BitVec(64)>(λ left => {source}(left, {vals}(64, 1)), {left_roundtrip}), cong_fn<BitVec(64), BitVec(64)>(λ right => {source}({left}, right), {right_roundtrip}))");
    decl(&mut module, format!("{prefix}_source_correct"), true, before(),
        format!("read_gpr({}, {prefix}_after(before).gprs) = {source}({left}, {right})", output.heather_name()),
        format!("trans({prefix}_correct({vals}, before, {left_roundtrip}, {right_roundtrip}), trans({prefix}_denotes_source({vals}), {source_roundtrip}))"), true);
    decl(&mut module, format!("{prefix}_source_artifact"), true, before(),
        format!("StructuredArtifact<M>({prefix}_code(), before, {}, {source}({left}, {right}), {prefix}_Protected)", output.heather_name()),
        format!("StructuredArtifact(after := {prefix}_after(before), execution := refl, layout := {prefix}_layout(), decoding := {prefix}_decodes(before.rip), result_correct := {prefix}_source_correct(before), memory_preserved := {prefix}_memory(before), rip_correct := {prefix}_span(before), registers_preserved := λ register protected => {prefix}_preserves(register, before, protected))"), true);
    emission.text = module.render();
    Ok(emission)
}
