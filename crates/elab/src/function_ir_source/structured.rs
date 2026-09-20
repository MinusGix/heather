//! Untrusted reflection into recursive FunctionIR and composition of checked
//! source agreement with the shared physical execution artifact.
use super::*;
use cert::StructuredRegion;

/// Source types remain distinct even when their FunctionIR ports have the same
/// width: Bool is represented by BitVec(1), but is not a BitVec(1) parameter.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StructuredSourceType { Word(u64), Boolean }
impl StructuredSourceType {
    fn width(self) -> u64 { match self { Self::Word(width) => width, Self::Boolean => 1 } }
    fn name(self) -> String { match self { Self::Word(width) => format!("BitVec({width})"), Self::Boolean => "Bool".into() } }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReflectedStructuredFunction {
    pub source_name: String,
    pub parameters: Vec<StructuredSourceType>,
    pub result: StructuredSourceType,
    pub region: StructuredRegion,
}

fn absolute(term: &Term, caller: usize) -> Option<usize> {
    match term { Term::GlobalTm { var, .. } => caller.checked_sub(1 + var.0 as usize), _ => None }
}

/// Reflect checked Boolean matches and width-aware pure DAGs. No argument
/// count or machine ABI is imposed here. Native export validates its narrower
/// interface separately. Types/operations are recognized by resolved identity.
pub fn reflect_elaborated_structured(elaborator: &Elaborator, source_name: &str)
    -> Result<ReflectedStructuredFunction, SourceError>
{
    let caller = elaborator.global_abs(source_name).ok_or_else(|| SourceError::Unsupported(format!("unknown source function `{source_name}`")))?;
    let source_name = elaborator.global_qualified_name_at(caller).ok_or_else(|| SourceError::Unsupported("source has no canonical global name".into()))?;
    let (ty, body) = elaborator.global_body(&source_name).ok_or_else(|| SourceError::Unsupported("structured source must be transparent".into()))?;
    use crate::gendefs::GenDef;
    let code = |name: &str, parameterized: bool| elaborator.lookup_inductive(name)
        .and_then(|ind| elaborator.types.gdefs().abs_for(&if parameterized { GenDef::TyCodeFn(ind.tag) } else { GenDef::TyCode(ind.tag) }))
        .map(|abs| *abs as usize);
    let boolean = code("bool::Bool", false);
    let word = code("bitvec::BitVec", true);
    let source_type = |ty: &Type| -> Result<StructuredSourceType, SourceError> {
        if let Type::El { tm, .. } = ty {
            let (head, args) = application_spine(tm);
            let abs = absolute(head, caller);
            if boolean.is_some() && abs == boolean && args.is_empty() { return Ok(StructuredSourceType::Boolean); }
            if word.is_some() && abs == word && args.len() == 1 {
                if let Some(width) = nat_literal(args[0]).filter(|width| *width <= 64) { return Ok(StructuredSourceType::Word(width)); }
            }
        }
        unsupported("structured source supports Bool and literal BitVec widths up to 64")
    };
    let mut parameters = Vec::new();
    let mut result = &*ty;
    let mut term = &*body;
    while let Type::Pi { dom, cod, .. } = result {
        parameters.push(source_type(dom)?);
        result = cod;
        let Term::Lam { body, .. } = term else { return unsupported("missing source parameter"); };
        term = body;
    }
    let result = source_type(result)?;
    let operations = OperationGlobals::resolve(elaborator)?;
    let comparison = elaborator.global_abs("bitvec::unsigned_lt_bit").ok_or_else(|| SourceError::Unsupported("unsigned comparison is not loaded".into()))?;
    let payload = |slot| elaborator.lookup_inductive("bool::Bool")
        .and_then(|ind| elaborator.types.gdefs().abs_for(&GenDef::PayloadCode(ind.tag, slot)))
        .map(|abs| *abs as usize).ok_or_else(|| SourceError::Unsupported("Boolean payload identities are not loaded".into()));
    let boolean_payloads = [payload(0)?, payload(1)?];
    let mut builder = Builder { caller, operations, comparison, boolean_payloads, parameters: parameters.clone(), result, next_id: parameters.len() as u64 + 1 };
    let region = builder.region(term, 0)?;
    cert::validate_structured_region(&region).map_err(SourceError::InvalidRegion)?;
    Ok(ReflectedStructuredFunction { source_name, parameters, result, region })
}

struct Builder {
    caller: usize,
    operations: OperationGlobals,
    comparison: usize,
    boolean_payloads: [usize; 2],
    parameters: Vec<StructuredSourceType>,
    result: StructuredSourceType,
    next_id: u64,
}

// Local interning preserves DAG sharing. There is no parallel source AST;
// operands are reflected straight into the existing FunctionIR node family.
#[derive(Default)]
struct Dag { nodes: Vec<Node>, values: BTreeMap<DagKey, Port> }
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum DagKey {
    Constant(u64, u64),
    Binary(SourceBinaryOperation, u64, u64, u64),
    UnsignedLessThan(u64, u64, u64),
}

fn interface(parameters: &[StructuredSourceType]) -> Vec<Port> {
    parameters.iter().enumerate().map(|(id, ty)| Port { id: id as u64, width: ty.width() }).collect()
}

impl Builder {
    fn boolean_components(&self, lhs: &Type, rhs: &Type) -> bool {
        [lhs, rhs].iter().zip(self.boolean_payloads).all(|(ty, abs)| {
            matches!(ty, Type::El { tm, .. } if absolute(tm, self.caller) == Some(abs))
        })
    }
    fn output(&self) -> Port { Port { id: self.parameters.len() as u64, width: self.result.width() } }
    fn fresh(&mut self) -> Result<u64, SourceError> {
        let id = self.next_id;
        self.next_id = id.checked_add(1).ok_or_else(|| SourceError::Unsupported("source graph exhausted stable IDs".into()))?;
        Ok(id)
    }
    fn node(&mut self, dag: &mut Dag, key: DagKey, width: u64, target: Option<u64>, make: impl FnOnce(u64) -> Node) -> Result<Port, SourceError> {
        if target.is_none() { if let Some(port) = dag.values.get(&key) { return Ok(*port); } }
        let port = Port { id: match target { Some(id) => id, None => self.fresh()? }, width };
        dag.nodes.push(make(port.id));
        dag.values.insert(key, port);
        Ok(port)
    }
    fn constant(&mut self, dag: &mut Dag, width: u64, value: u64, target: Option<u64>) -> Result<Port, SourceError> {
        self.node(dag, DagKey::Constant(width, value), width, target, |output| Node::Const { width, output, value })
    }
    fn expression(&mut self, term: &Term, depth: u32, expected: StructuredSourceType, dag: &mut Dag, target: Option<u64>) -> Result<Port, SourceError> {
        let width = expected.width();
        if let Term::Var(LocalVar(index)) = term {
            let index = index.checked_sub(depth).and_then(|index| self.parameters.len().checked_sub(index as usize + 1))
                .ok_or_else(|| SourceError::Unsupported("source expression uses a match payload or an unbound input".into()))?;
            if self.parameters[index] != expected { return unsupported("source operand has the wrong type"); }
            let input = Port { id: index as u64, width };
            return if let Some(output) = target {
                let zero = self.constant(dag, width, 0, None)?;
                self.node(dag, DagKey::Binary(SourceBinaryOperation::BitOr, width, zero.id, input.id), width, Some(output), |output| Node::BitOr { width, output, left: zero.id, right: input.id })
            } else { Ok(input) };
        }
        if expected == StructuredSourceType::Boolean {
            match term {
                Term::Inl { lhs, rhs, .. } if self.boolean_components(lhs, rhs) => return self.constant(dag, 1, 0, target),
                Term::Inr { lhs, rhs, .. } if self.boolean_components(lhs, rhs) => return self.constant(dag, 1, 1, target),
                _ => {}
            }
        }
        let (head, args) = application_spine(term);
        let abs = absolute(head, self.caller).ok_or_else(|| SourceError::Unsupported("source value must use a resolved pure operation".into()))?;
        if abs == self.comparison && args.len() == 3 && expected == StructuredSourceType::Boolean {
            let operand_width = nat_literal(args[0]).filter(|width| *width <= 64).ok_or_else(|| SourceError::Unsupported("comparison width must be a literal up to 64".into()))?;
            let ty = StructuredSourceType::Word(operand_width);
            let left = self.expression(args[1], depth, ty, dag, None)?.id;
            let right = self.expression(args[2], depth, ty, dag, None)?.id;
            return self.node(dag, DagKey::UnsignedLessThan(operand_width, left, right), 1, target, |output| Node::UnsignedLessThan { width: operand_width, output, left, right });
        }
        if let StructuredSourceType::Word(width) = expected {
            if abs == self.operations.of_nat && args.len() == 2 && nat_literal(args[0]) == Some(width) {
                if let Some(value) = nat_literal(args[1]) { return self.constant(dag, width, value, target); }
            }
            if let Some(operation) = self.operations.operations.get(&abs).copied() {
                if args.len() == 3 && nat_literal(args[0]) == Some(width) {
                    let left = self.expression(args[1], depth, expected, dag, None)?.id;
                    let right = self.expression(args[2], depth, expected, dag, None)?.id;
                    return self.node(dag, DagKey::Binary(operation, width, left, right), width, target, |output| operation.node_at_width(width, output, left, right));
                }
            }
        }
        unsupported(if expected == StructuredSourceType::Boolean {
            "Boolean values require an input, constant, or bitvec::unsigned_lt_bit"
        } else { "unsupported structured source operation or result type" })
    }
    fn region(&mut self, term: &Term, depth: u32) -> Result<StructuredRegion, SourceError> {
        let inputs = interface(&self.parameters);
        let outputs = vec![self.output()];
        if let Term::Case { lhs, rhs, scrut, case_l, case_r, .. } = term {
            if !self.boolean_components(lhs, rhs) { return unsupported("structured matches must use the resolved Bool type"); }
            let mut dag = Dag::default();
            let condition = self.expression(scrut, depth, StructuredSourceType::Boolean, &mut dag, None)?;
            let when_false = Box::new(self.region(case_l, depth + 1)?);
            let when_true = Box::new(self.region(case_r, depth + 1)?);
            let mut available = inputs.clone();
            if !available.contains(&condition) { available.push(condition); }
            let branch = StructuredRegion::Conditional { inputs: available, condition: condition.id, arguments: inputs.clone(), outputs, when_true, when_false };
            if dag.nodes.is_empty() { Ok(branch) }
            else { Ok(StructuredRegion::Sequence { prefix: Region { inputs, nodes: dag.nodes, outputs: vec![condition] }, continuation: Box::new(branch) }) }
        } else {
            let mut dag = Dag::default();
            self.expression(term, depth, self.result, &mut dag, Some(self.output().id))?;
            Ok(StructuredRegion::Dataflow(Region { inputs, nodes: dag.nodes, outputs }))
        }
    }
}

/// Source agreement only: this reconstructs expressions from the shared IR.
/// It is not a physical artifact or a global StructuredRegionHolds witness.
pub fn generate_structured_source_expansion(prefix: &str, reflected: &ReflectedStructuredFunction) -> Result<String, SourceError> {
    cert::validate_structured_region(&reflected.region).map_err(SourceError::InvalidRegion)?;
    let output = Port { id: reflected.parameters.len() as u64, width: reflected.result.width() };
    if reflected.region.inputs() != interface(&reflected.parameters) || reflected.region.outputs() != [output] {
        return unsupported("structured source interface does not match its reflected types");
    }
    let mut module = Module::default();
    module.raw("import bitvec;\nimport bool;");
    if let Some((owner, _)) = reflected.source_name.rsplit_once("::") { module.raw(format!("import {owner};")); }
    let parameters: Vec<_> = reflected.parameters.iter().enumerate().map(|(i, ty)| Parameter::explicit(format!("arg{i}"), HeatherExpr::raw(ty.name()))).collect();
    let arguments: Vec<_> = (0..parameters.len()).map(|i| HeatherExpr::name(format!("arg{i}"))).collect();
    let initial = reflected.parameters.iter().enumerate().map(|(id, ty)| {
        let expression = if *ty == StructuredSourceType::Boolean { HeatherExpr::call("bitvec::ofBool", [arguments[id].clone()]) } else { arguments[id].clone() };
        (id as u64, (ty.width(), expression))
    }).collect();
    let mut expansion = Expansion { prefix, module: &mut module, next_name: 0, parameters: &parameters, arguments: &arguments, result: reflected.result };
    let result = expansion.region(&reflected.region, initial)?;
    let name = format!("{prefix}_expression");
    module.declaration(Declaration::function(&name, HeatherExpr::raw(reflected.result.name()), Block::expression(result)).parameters(parameters.clone()));
    module.declaration(Declaration::theorem(format!("{prefix}_source_expands"),
        HeatherExpr::equal(HeatherExpr::call(name.as_str(), arguments.clone()), HeatherExpr::call(reflected.source_name.as_str(), arguments)),
        Block::expression(HeatherExpr::name("refl"))).parameters(parameters));
    Ok(module.render())
}

struct Expansion<'a> {
    prefix: &'a str,
    module: &'a mut Module,
    next_name: usize,
    parameters: &'a [Parameter],
    arguments: &'a [HeatherExpr],
    result: StructuredSourceType,
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
            let (id, width, expression) = match *node {
                Node::Const { width, output, value } => (output, width, HeatherExpr::call("bitvec::ofNat", [HeatherExpr::nat(width), HeatherExpr::nat(value)])),
                Node::Add { width, output, left, right } | Node::Sub { width, output, left, right }
                | Node::BitAnd { width, output, left, right } | Node::BitOr { width, output, left, right }
                | Node::BitXor { width, output, left, right } | Node::UnsignedLessThan { width, output, left, right } => {
                    let (function, comparison) = match node {
                        Node::Add { .. } => ("bitvec::add", false), Node::Sub { .. } => ("bitvec::sub", false),
                        Node::BitAnd { .. } => ("bitvec::band", false), Node::BitOr { .. } => ("bitvec::bor", false),
                        Node::BitXor { .. } => ("bitvec::bxor", false), Node::UnsignedLessThan { .. } => ("bitvec::unsigned_lt_bit", true),
                        _ => unreachable!(),
                    };
                    let expression = HeatherExpr::call(function, [HeatherExpr::nat(width), operand(values, left, width)?, operand(values, right, width)?]);
                    (output, if comparison { 1 } else { width }, if comparison { HeatherExpr::call("bitvec::ofBool", [expression]) } else { expression })
                }
                _ => return unsupported("unsupported source expansion node"),
            };
            let name = format!("{}_value_{}", self.prefix, self.next_name);
            self.next_name += 1;
            self.module.declaration(Declaration::function(&name, HeatherExpr::raw(format!("BitVec({width})")), Block::expression(expression)).parameters(self.parameters.to_vec()));
            values.insert(id, (width, HeatherExpr::call(name.as_str(), self.arguments.to_vec())));
        }
        Ok(())
    }
    fn region(&mut self, region: &StructuredRegion, mut values: Expressions) -> Result<HeatherExpr, SourceError> {
        values.retain(|id, _| region.inputs().iter().any(|port| port.id == *id));
        for port in region.inputs() { operand(&values, port.id, port.width)?; }
        match region {
            StructuredRegion::Dataflow(body) => {
                self.dataflow(body, &mut values)?;
                if body.outputs.len() != 1 { return unsupported("source expansion requires one result"); }
                let value = operand(&values, body.outputs[0].id, self.result.width())?;
                Ok(if self.result == StructuredSourceType::Boolean { HeatherExpr::call("bitvec::head_bit", [HeatherExpr::nat(0), value]) } else { value })
            }
            StructuredRegion::Sequence { prefix, continuation } => { self.dataflow(prefix, &mut values)?; self.region(continuation, values) }
            StructuredRegion::Conditional { condition, when_true, when_false, .. } => {
                let condition = operand(&values, *condition, 1)?;
                let yes = self.region(when_true, values.clone())?;
                let no = self.region(when_false, values)?;
                Ok(HeatherExpr::raw(format!("match bitvec::head_bit(0, {}) {{ False => {}, True => {} }}", condition.render(), no.render(), yes.render())))
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
    if reflected.parameters != [StructuredSourceType::Word(64), StructuredSourceType::Word(64)] || reflected.result != StructuredSourceType::Word(64) {
        return unsupported("native structured export currently requires two BitVec(64) inputs and a BitVec(64) result");
    }
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
