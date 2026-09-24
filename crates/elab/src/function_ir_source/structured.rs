//! Untrusted reflection into recursive FunctionIR and composition of checked
//! source agreement with the shared physical execution artifact.
use super::*;
use cert::StructuredRegion;
mod publication;
mod read;
pub use read::{generate_elaborated_read_x86, ReadX86Emission};
pub use publication::generate_elaborated_typed_x86;

/// Source types remain distinct even when their FunctionIR ports have the same
/// width: Bool is represented by BitVec(1), but is not a BitVec(1) parameter.
/// A Natural parameter the body does not consume has no port, and source
/// agreement still quantifies over its value. One it consumes is `NatWord`: a
/// 64-bit port holding `bitvec_nat::word_of_nat(64, n)`, the modular image,
/// so every equality stays unconditional and reading the word back as the Nat
/// is its consumer's bound (docs/native-bounded-loops-design.md §9a).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StructuredSourceType { Word(u64), Boolean, Natural, NatWord }
impl StructuredSourceType {
    fn width(self) -> Option<u64> { match self { Self::Word(width) => Some(width), Self::Boolean => Some(1), Self::Natural => None, Self::NatWord => Some(64) } }
    fn scalar_width(self) -> Result<u64, SourceError> { self.width().ok_or_else(|| SourceError::Unsupported("Nat values need a representation proof before lowering".into())) }
    fn name(self) -> String { match self { Self::Word(width) => format!("BitVec({width})"), Self::Boolean => "Bool".into(), Self::Natural | Self::NatWord => "Nat".into() } }
    /// A Nat in a result position is always carried.
    fn carried(self) -> Self { if self == Self::Natural { Self::NatWord } else { self } }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReflectedStructuredFunction {
    pub source_name: String,
    pub parameters: Vec<StructuredSourceType>,
    pub result: StructuredSourceType,
    pub region: StructuredRegion,
    pub choice: Option<StructuredSourceChoice>,
}

/// Two constructors with the same scalar payload use a discriminator and a
/// payload result port. Constructor identities exist only at the source edge.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructuredSourceChoice {
    pub type_name: String,
    pub constructors: [String; 2],
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
    let mut parameters = Vec::new();
    let mut result = &*ty;
    let mut term = &*body;
    while let Type::Pi { dom, cod, .. } = result {
        parameters.push(source_type(elaborator, caller, dom)?);
        result = cod;
        let Term::Lam { body, .. } = term else { return unsupported("missing source parameter"); };
        term = body;
    }
    let (result, choice) = result_type(elaborator, caller, result)?;
    let comparison = elaborator.global_abs("bitvec::BitVec::unsigned_lt_bit").ok_or_else(|| SourceError::Unsupported("unsigned comparison is not loaded".into()))?;
    let payload = |slot| elaborator.lookup_inductive("bool::Bool")
        .and_then(|ind| elaborator.types.gdefs().abs_for(&crate::gendefs::GenDef::PayloadCode(ind.tag, slot)))
        .map(|abs| *abs as usize).ok_or_else(|| SourceError::Unsupported("Boolean payload identities are not loaded".into()));
    let boolean_payloads = [payload(0)?, payload(1)?];
    let output = Port { id: parameters.len() as u64, width: result.scalar_width()? };
    let exit = choice.as_ref().map(|_| Port { id: output.id + 1, width: 1 });
    // Every Nat starts erased; one the body turns out to consume gets a port
    // and the reflection runs again.
    loop {
        let bindings = parameters.iter().enumerate().map(|(id, ty)| (*ty, ty.width().map(|width| Port { id: id as u64, width }))).collect();
        let mut builder = Builder { elaborator, caller, operations: OperationGlobals::resolve(elaborator)?, comparison, boolean_payloads,
            inputs: interface(&parameters), bindings, result, output, exit, stack: vec![caller],
            next_id: output.id + 1 + u64::from(exit.is_some()), needs_port: None };
        match builder.region(term, 0) {
            Ok(region) => {
                cert::validate_structured_region(&region).map_err(SourceError::InvalidRegion)?;
                return Ok(ReflectedStructuredFunction { source_name, parameters, result, region, choice });
            }
            Err(error) => match builder.needs_port {
                Some(index) if parameters[index] == StructuredSourceType::Natural => parameters[index] = StructuredSourceType::NatWord,
                _ => return Err(error),
            },
        }
    }
}

fn source_code(elaborator: &Elaborator, caller: usize, tm: &Term) -> Result<StructuredSourceType, SourceError> {
    use crate::gendefs::GenDef;
    if matches!(tm, Term::TmNat) { return Ok(StructuredSourceType::Natural); }
    let (head, args) = application_spine(tm);
    let code = absolute(head, caller).and_then(|abs| elaborator.types.gdefs().key_for_abs(&(abs as u32)));
    match code {
        Some(GenDef::TyCode(tag)) if args.is_empty() && elaborator.lookup_inductive("bool::Bool").is_some_and(|ind| ind.tag == *tag) => Ok(StructuredSourceType::Boolean),
        Some(GenDef::TyCodeFn(tag)) if args.len() == 1 && elaborator.lookup_inductive("bitvec::BitVec").is_some_and(|ind| ind.tag == *tag) => {
            nat_literal(args[0]).filter(|width| *width <= 64).map(StructuredSourceType::Word)
                .ok_or_else(|| SourceError::Unsupported("bitvector widths must be literals up to 64".into()))
        }
        _ => unsupported("structured source supports Bool, literal BitVec widths up to 64, and unused Nat parameters"),
    }
}
fn source_type(elaborator: &Elaborator, caller: usize, ty: &Type) -> Result<StructuredSourceType, SourceError> {
    match ty {
        Type::Nat => Ok(StructuredSourceType::Natural),
        Type::El { tm, .. } => source_code(elaborator, caller, tm),
        _ => unsupported("unsupported structured source type"),
    }
}
fn result_type(elaborator: &Elaborator, caller: usize, ty: &Type) -> Result<(StructuredSourceType, Option<StructuredSourceChoice>), SourceError> {
    if let Ok(scalar) = source_type(elaborator, caller, ty) {
        let scalar = scalar.carried();
        scalar.scalar_width()?;
        return Ok((scalar, None));
    }
    let Type::El { tm, .. } = ty else { return unsupported("unsupported result type"); };
    let (head, args) = application_spine(tm);
    let key = absolute(head, caller).and_then(|abs| elaborator.types.gdefs().key_for_abs(&(abs as u32)));
    let Some(crate::gendefs::GenDef::TyCodeFn(tag)) = key else { return unsupported("result must be scalar or a two-constructor scalar choice"); };
    let ind = elaborator.types.by_tag(*tag).ok_or_else(|| SourceError::Unsupported("missing result declaration".into()))?;
    if ind.recursive || ind.index.is_some() || !ind.valparams.is_empty() || ind.params.len() != 1 || args.len() != 1 || ind.ctors.len() != 2
        || !ind.ctors.iter().all(|ctor| ctor.fields.len() == 1 && matches!(&ctor.fields[0].1.kind, TyKind::Named { name, args } if name == &ind.params[0] && args.is_empty())) {
        return unsupported("choice results require two single-field constructors with the same scalar type parameter");
    }
    let scalar = source_code(elaborator, caller, args[0])?.carried();
    scalar.scalar_width()?;
    let qualify = |name: &str| if ind.scope.module.is_empty() { name.to_string() } else { format!("{}::{name}", ind.scope.module) };
    Ok((scalar, Some(StructuredSourceChoice { type_name: qualify(&ind.name), constructors: [qualify(&ind.ctors[0].name), qualify(&ind.ctors[1].name)] })))
}

struct Builder<'a> {
    elaborator: &'a Elaborator,
    caller: usize,
    operations: OperationGlobals,
    comparison: usize,
    boolean_payloads: [usize; 2],
    inputs: Vec<Port>,
    bindings: Vec<(StructuredSourceType, Option<Port>)>,
    result: StructuredSourceType,
    output: Port,
    exit: Option<Port>,
    next_id: u64,
    stack: Vec<usize>,
    /// Set when the body consumes an erased Nat parameter: reflection retries
    /// with that parameter carried.
    needs_port: Option<usize>,
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
    parameters.iter().enumerate().filter_map(|(id, ty)| ty.width().map(|width| Port { id: id as u64, width })).collect()
}

impl Builder<'_> {
    fn boolean_components(&self, lhs: &Type, rhs: &Type) -> bool {
        [lhs, rhs].iter().zip(self.boolean_payloads).all(|(ty, abs)| {
            matches!(ty, Type::El { tm, .. } if absolute(tm, self.caller) == Some(abs))
        })
    }
    fn outputs(&self) -> Vec<Port> { let mut outputs = vec![self.output]; if let Some(exit) = self.exit { outputs.push(exit); } outputs }
    fn fresh(&mut self) -> Result<u64, SourceError> {
        if self.next_id >= 16384 { return unsupported("structured reflection exceeds its value budget"); }
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
        let width = expected.scalar_width()?;
        if let Term::Var(LocalVar(index)) = term {
            let index = index.checked_sub(depth).and_then(|index| self.bindings.len().checked_sub(index as usize + 1))
                .ok_or_else(|| SourceError::Unsupported("source expression uses a match payload or an unbound input".into()))?;
            if self.bindings[index].0 == StructuredSourceType::Natural && expected == StructuredSourceType::NatWord {
                self.needs_port = Some(index);
                return unsupported("a consumed Nat parameter needs a port");
            }
            if self.bindings[index].0 != expected { return unsupported("source operand has the wrong type"); }
            let input = self.bindings[index].1.ok_or_else(|| SourceError::Unsupported("used Nat parameter requires a representation proof".into()))?;
            return if let Some(output) = target {
                let zero = self.constant(dag, width, 0, None)?;
                self.node(dag, DagKey::Binary(SourceBinaryOperation::BitOr, width, zero.id, input.id), width, Some(output), |output| Node::BitOr { width, output, left: zero.id, right: input.id })
            } else { Ok(input) };
        }
        if expected == StructuredSourceType::Boolean {
            match term {
                Term::Inl { lhs, rhs, .. } if self.boolean_components(lhs, rhs) => return self.constant(dag, 1, 0, target),
                Term::Inr { lhs, rhs, .. } if self.boolean_components(lhs, rhs) => return self.constant(dag, 1, 1, target),
                // The checked spelling carries no summands to test
                // (docs/intro-by-type-design.md §4.2), and needs none: the
                // position is already known to be Boolean, and the kernel
                // checked the injection against that type.
                Term::InlAt { .. } => return self.constant(dag, 1, 0, target),
                Term::InrAt { .. } => return self.constant(dag, 1, 1, target),
                _ => {}
            }
        }
        if expected == StructuredSourceType::NatWord {
            return match term {
                Term::Zero => self.constant(dag, 64, 0, target),
                Term::NatLit(value) => self.constant(dag, 64, *value, target),
                Term::Succ(inner) => {
                    let inner = self.expression(inner, depth, expected, dag, None)?.id;
                    let one = self.constant(dag, 64, 1, None)?.id;
                    let add = SourceBinaryOperation::Add;
                    self.node(dag, DagKey::Binary(add, 64, inner, one), 64, target, |output| add.node_at_width(64, output, inner, one))
                }
                _ => unsupported("a carried Nat must be a parameter, Zero, a literal, or Succ of one"),
            };
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
            "Boolean values require an input, constant, or bitvec::BitVec::unsigned_lt_bit"
        } else { "unsupported structured source operation or result type" })
    }
    fn predicate(&mut self, term: &Term, depth: u32, target: Option<u64>) -> Result<(Option<StructuredRegion>, Port), SourceError> {
        let mut dag = Dag::default();
        let primitive_error = match self.expression(term, depth, StructuredSourceType::Boolean, &mut dag, target) {
            Ok(port) => return Ok((if dag.nodes.is_empty() { None } else { Some(StructuredRegion::Dataflow(Region { inputs: self.inputs.clone(), nodes: dag.nodes, outputs: vec![port] })) }, port)),
            Err(error) => error,
        };
        let (head, args) = application_spine(term);
        let Some(callee) = absolute(head, self.caller) else { return Err(primitive_error); };
        let Some(name) = self.elaborator.global_qualified_name_at(callee) else { return Err(primitive_error); };
        let Some((ty, body)) = self.elaborator.global_body(&name) else { return Err(primitive_error); };
        if self.stack.contains(&callee) || self.stack.len() >= 32 { return unsupported("recursive or excessively deep helper expansion"); }
        let mut ty = &*ty;
        let mut body = &*body;
        let mut parameters = Vec::new();
        while let Type::Pi { dom, cod, .. } = ty {
            let Ok(parameter) = source_type(self.elaborator, callee, dom) else { return Err(primitive_error); };
            parameters.push(parameter);
            ty = cod;
            let Term::Lam { body: next, .. } = body else { return Err(primitive_error); };
            body = next;
        }
        if parameters.len() != args.len() || source_type(self.elaborator, callee, ty).ok() != Some(StructuredSourceType::Boolean) { return Err(primitive_error); }
        let mut arguments = Dag::default();
        let mut bindings = Vec::new();
        let mut inputs = self.inputs.clone();
        for (ty, arg) in parameters.into_iter().zip(args) {
            let port = if ty == StructuredSourceType::Natural { None } else { Some(self.expression(arg, depth, ty, &mut arguments, None)?) };
            if let Some(port) = port { if !inputs.contains(&port) { inputs.push(port); } }
            bindings.push((ty, port));
        }
        let output = Port { id: match target { Some(id) => id, None => self.fresh()? }, width: 1 };
        let mut stack = self.stack.clone();
        stack.push(callee);
        let mut nested = Builder { elaborator: self.elaborator, caller: callee,
            operations: OperationGlobals::resolve(self.elaborator)?, comparison: self.comparison,
            boolean_payloads: self.boolean_payloads, inputs: inputs.clone(), bindings,
            result: StructuredSourceType::Boolean, output, exit: None, next_id: self.next_id, stack, needs_port: None };
        let region = nested.region(body, 0)?;
        self.next_id = nested.next_id;
        Ok((Some(if arguments.nodes.is_empty() { region } else {
            StructuredRegion::Sequence { prefix: Region { inputs: self.inputs.clone(), nodes: arguments.nodes, outputs: inputs }, continuation: Box::new(region) }
        }), output))
    }
    fn region(&mut self, term: &Term, depth: u32) -> Result<StructuredRegion, SourceError> {
        let inputs = self.inputs.clone();
        let outputs = self.outputs();
        if let Term::Case { lhs, rhs, scrut, case_l, case_r, .. } = term {
            if !self.boolean_components(lhs, rhs) { return unsupported("structured matches must use the resolved Bool type"); }
            let (producer, condition) = self.predicate(scrut, depth, None)?;
            let when_false = Box::new(self.region(case_l, depth + 1)?);
            let when_true = Box::new(self.region(case_r, depth + 1)?);
            let mut available = inputs.clone();
            if !available.contains(&condition) { available.push(condition); }
            let branch = StructuredRegion::Conditional { inputs: available, condition: condition.id, arguments: inputs.clone(), outputs, when_true, when_false };
            Ok(match producer {
                None => branch,
                Some(StructuredRegion::Dataflow(prefix)) => StructuredRegion::Sequence { prefix, continuation: Box::new(branch) },
                Some(prefix) => StructuredRegion::Compose { prefix: Box::new(prefix), continuation: Box::new(branch) },
            })
        } else {
            let mut dag = Dag::default();
            if let Some(exit) = self.exit {
                // Either spelling (docs/intro-by-type-design.md §4.2).
                let (tag, fields) = match crate::spelling::inj_of(term) {
                    Some((true, val)) => (0, &**val), Some((false, val)) => (1, &**val),
                    None => return unsupported("choice result must construct one of its two alternatives"),
                };
                let Some((_, snd)) = crate::spelling::pair_of(fields) else { return unsupported("missing choice constructor fields"); };
                let Some((fst, snd)) = crate::spelling::pair_of(snd) else { return unsupported("missing choice payload"); };
                if !matches!(&**snd, Term::Triv { .. }) { return unsupported("choice constructor has extra fields"); }
                self.expression(fst, depth, self.result, &mut dag, Some(self.output.id))?;
                self.constant(&mut dag, 1, tag, Some(exit.id))?;
            } else if self.result == StructuredSourceType::Boolean {
                let (producer, port) = self.predicate(term, depth, Some(self.output.id))?;
                if let Some(producer) = producer { return Ok(producer); }
                debug_assert_eq!(port, self.output);
            } else {
                self.expression(term, depth, self.result, &mut dag, Some(self.output.id))?;
            }
            Ok(StructuredRegion::Dataflow(Region { inputs, nodes: dag.nodes, outputs }))
        }
    }
}

/// Source agreement only: this reconstructs expressions from the shared IR.
/// It is not a physical artifact or a global StructuredRegionHolds witness.
pub fn generate_structured_source_expansion(prefix: &str, reflected: &ReflectedStructuredFunction) -> Result<String, SourceError> {
    cert::validate_structured_region(&reflected.region).map_err(SourceError::InvalidRegion)?;
    let output = Port { id: reflected.parameters.len() as u64, width: reflected.result.scalar_width()? };
    let mut outputs = vec![output];
    if reflected.choice.is_some() { outputs.push(Port { id: output.id + 1, width: 1 }); }
    if reflected.region.inputs() != interface(&reflected.parameters) || reflected.region.outputs() != outputs {
        return unsupported("structured source interface does not match its reflected types");
    }
    let mut module = Module::default();
    module.raw("import bitvec;\nimport bool;");
    if reflected.carries_nat() { module.raw("import bitvec_nat;"); }
    if let Some((owner, _)) = reflected.source_name.rsplit_once("::") { module.raw(format!("import {owner};")); }
    if let Some(choice) = &reflected.choice {
        if let Some((owner, _)) = choice.type_name.rsplit_once("::") {
            if reflected.source_name.rsplit_once("::").map(|(owner, _)| owner) != Some(owner) { module.raw(format!("import {owner};")); }
        }
    }
    let parameters: Vec<_> = reflected.parameters.iter().enumerate().map(|(i, ty)| Parameter::explicit(format!("arg{i}"), HeatherExpr::raw(ty.name()))).collect();
    let arguments: Vec<_> = (0..parameters.len()).map(|i| HeatherExpr::name(format!("arg{i}"))).collect();
    let initial = reflected.parameters.iter().enumerate().filter_map(|(id, ty)| {
        let width = ty.width()?;
        Some((id as u64, (width, HeatherExpr::raw(publication::vector(*ty, &arguments[id].render())))))
    }).collect();
    let mut expansion = Expansion { prefix, module: &mut module, next_name: 0, parameters: &parameters, arguments: &arguments, result: reflected.result, choice: reflected.choice.as_ref(),
        naturals: natural_inputs(&reflected.parameters), constants: BTreeMap::new() };
    let result = expansion.region(&reflected.region, initial)?;
    let name = format!("{prefix}_expression");
    let result_name = reflected.choice.as_ref().map_or_else(|| reflected.result.name(), |choice| format!("{}<{}>", choice.type_name, reflected.result.name()));
    module.declaration(Declaration::function(&name, HeatherExpr::raw(result_name), Block::expression(result)).parameters(parameters.clone()));
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
    choice: Option<&'a StructuredSourceChoice>,
    /// For each port carrying a Nat: its source expression, and a proof that
    /// `word_of_nat(64, expression)` is the port's word (`None`: definitional).
    /// Port IDs are unique, and a branch reads its result right after writing
    /// it, so one map serves every arm.
    naturals: BTreeMap<u64, (HeatherExpr, Option<HeatherExpr>)>,
    constants: BTreeMap<u64, u64>,
}

impl ReflectedStructuredFunction {
    fn carries_nat(&self) -> bool {
        self.result == StructuredSourceType::NatWord || self.parameters.contains(&StructuredSourceType::NatWord)
    }
}

fn natural_inputs(parameters: &[StructuredSourceType]) -> BTreeMap<u64, (HeatherExpr, Option<HeatherExpr>)> {
    parameters.iter().enumerate().filter(|(_, ty)| **ty == StructuredSourceType::NatWord)
        .map(|(id, _)| (id as u64, (HeatherExpr::name(format!("arg{id}")), None))).collect()
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
                Node::Const { width, output, value } => (output, width, HeatherExpr::explicit_call("bitvec::BitVec::ofNat", [HeatherExpr::nat(width), HeatherExpr::nat(value)])),
                Node::Add { width, output, left, right } | Node::Sub { width, output, left, right }
                | Node::BitAnd { width, output, left, right } | Node::BitOr { width, output, left, right }
                | Node::BitXor { width, output, left, right } | Node::UnsignedLessThan { width, output, left, right } => {
                    let (function, comparison) = match node {
                        Node::Add { .. } => ("bitvec::BitVec::add", false), Node::Sub { .. } => ("bitvec::BitVec::sub", false),
                        Node::BitAnd { .. } => ("bitvec::BitVec::band", false), Node::BitOr { .. } => ("bitvec::BitVec::bor", false),
                        Node::BitXor { .. } => ("bitvec::BitVec::bxor", false), Node::UnsignedLessThan { .. } => ("bitvec::BitVec::unsigned_lt_bit", true),
                        _ => unreachable!(),
                    };
                    let expression = HeatherExpr::explicit_call(function, [HeatherExpr::nat(width), operand(values, left, width)?, operand(values, right, width)?]);
                    (output, if comparison { 1 } else { width }, if comparison { HeatherExpr::call("bitvec::BitVec::ofBool", [expression]) } else { expression })
                }
                _ => return unsupported("unsupported source expansion node"),
            };
            self.track_natural(node);
            let name = format!("{}_value_{}", self.prefix, self.next_name);
            self.next_name += 1;
            self.module.declaration(Declaration::function(&name, HeatherExpr::raw(format!("BitVec({width})")), Block::expression(expression)).parameters(self.parameters.to_vec()));
            values.insert(id, (width, HeatherExpr::call(name.as_str(), self.arguments.to_vec())));
        }
        Ok(())
    }
    /// Follow a Nat through the only nodes a carried Nat reflects to: `Succ` as
    /// `Add(n, 1)`, and a passthrough as `BitOr(0, n)`.
    fn track_natural(&mut self, node: &Node) {
        match *node {
            Node::Const { width: 64, output, value } => { self.constants.insert(output, value); }
            Node::Add { width: 64, output, left, right } if self.constants.get(&right) == Some(&1) => {
                if let Some((natural, proof)) = self.naturals.get(&left).cloned() {
                    let succ = format!("bitvec_nat::word_of_nat_succ({})", natural.render());
                    let proof = match proof {
                        None => succ,
                        Some(inner) => format!("trans({succ}, cong_fn<BitVec(64), BitVec(64)>(λ word => @bitvec::BitVec::add(64, word, @bitvec::BitVec::ofNat(64, 1)), {}))", inner.render()),
                    };
                    self.naturals.insert(output, (HeatherExpr::raw(format!("Succ({})", natural.render())), Some(HeatherExpr::raw(proof))));
                }
            }
            Node::BitOr { width: 64, output, left, right } if self.constants.get(&left) == Some(&0) => {
                if let Some(carried) = self.naturals.get(&right).cloned() { self.naturals.insert(output, carried); }
            }
            _ => {}
        }
    }
    /// The Nat a result port carries. A literal's proof is definitional (a
    /// closed computation, linear in the literal).
    fn natural(&self, id: u64) -> Result<(HeatherExpr, Option<HeatherExpr>), SourceError> {
        if let Some(found) = self.naturals.get(&id) { return Ok(found.clone()); }
        self.constants.get(&id).map(|value| (HeatherExpr::nat(*value), None))
            .ok_or_else(|| SourceError::Unsupported(format!("result {id} carries no Nat the source names")))
    }
    fn region(&mut self, region: &StructuredRegion, mut values: Expressions) -> Result<HeatherExpr, SourceError> {
        values.retain(|id, _| region.inputs().iter().any(|port| port.id == *id));
        for port in region.inputs() { operand(&values, port.id, port.width)?; }
        match region {
            StructuredRegion::Dataflow(body) => {
                self.dataflow(body, &mut values)?;
                if body.outputs.len() != 1 + usize::from(self.choice.is_some()) { return unsupported("source expansion result arity differs from source interface"); }
                let value = operand(&values, body.outputs[0].id, self.result.scalar_width()?)?;
                let value = match self.result {
                    StructuredSourceType::Boolean => HeatherExpr::explicit_call("bitvec::BitVec::head_bit", [HeatherExpr::nat(0), value]),
                    StructuredSourceType::NatWord => self.natural(body.outputs[0].id)?.0,
                    _ => value,
                };
                if let Some(choice) = self.choice {
                    let tag = operand(&values, body.outputs[1].id, 1)?;
                    Ok(HeatherExpr::raw(format!("match @bitvec::BitVec::head_bit(0, {}) {{ False => {}<{}>({}), True => {}<{}>({}) }}", tag.render(), choice.constructors[0], self.result.name(), value.render(), choice.constructors[1], self.result.name(), value.render())))
                } else { Ok(value) }
            }
            StructuredRegion::Sequence { prefix, continuation } => { self.dataflow(prefix, &mut values)?; self.region(continuation, values) }
            StructuredRegion::Compose { prefix, continuation } => {
                if prefix.outputs().len() != 1 { return unsupported("source composition currently requires one prefix result"); }
                let port = prefix.outputs()[0];
                let saved_result = self.result;
                let saved_choice = self.choice.take();
                self.result = if port.width == 1 { StructuredSourceType::Boolean } else { StructuredSourceType::Word(port.width) };
                let result = self.region(prefix, values.clone())?;
                self.result = saved_result;
                self.choice = saved_choice;
                let result = if port.width == 1 { HeatherExpr::call("bitvec::BitVec::ofBool", [result]) } else { result };
                values.insert(port.id, (port.width, result));
                self.region(continuation, values)
            }
            StructuredRegion::Conditional { condition, when_true, when_false, .. } => {
                let condition = operand(&values, *condition, 1)?;
                let yes = self.region(when_true, values.clone())?;
                let no = self.region(when_false, values)?;
                Ok(HeatherExpr::raw(format!("match @bitvec::BitVec::head_bit(0, {}) {{ False => {}, True => {} }}", condition.render(), no.render(), yes.render())))
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
    if reflected.choice.is_some() || reflected.parameters != [StructuredSourceType::Word(64), StructuredSourceType::Word(64)] || reflected.result != StructuredSourceType::Word(64) {
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
        format!("λ width id => match id {{ Zero => @bitvec::BitVec::ofNat(width, @bitvec::BitVec::toNat(64, {left})), Succ(rest) => match rest {{ Zero => @bitvec::BitVec::ofNat(width, @bitvec::BitVec::toNat(64, {right})), Succ(_) => @bitvec::BitVec::zero(width) }} }}"), false);
    let left_roundtrip = format!("bitvec::BitVec::ofNat_toNat(64, {left})");
    let right_roundtrip = format!("bitvec::BitVec::ofNat_toNat(64, {right})");
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
