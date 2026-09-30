//! First source-to-FunctionIR certification path.
//!
//! The fragment is intentionally narrow: one monomorphic pure `BitVec(64)`
//! binary operation. The surface declaration chooses a graph, but the emitted
//! theorem names the actual source function, so stale translation is rejected
//! by ordinary elaboration and kernel checking.

use std::collections::BTreeMap;

mod readonly_loop;
pub use readonly_loop::{LoopCarry, ReflectedReadonlyLoop, reflect_elaborated_readonly_loop, generate_readonly_loop_certificate};

mod loop_native;
pub use loop_native::{generate_elaborated_loop_x86, LoopX86Emission, NativeLoopPlacement};

mod structured;
pub use structured::{generate_elaborated_read_x86, ReadX86Emission, generate_elaborated_typed_x86, generate_elaborated_piece_x86, generate_elaborated_typed_fields_x86, FieldPiece, FieldEmission, generate_elaborated_structured_x86, generate_structured_source_expansion, reflect_elaborated_structured, ReflectedStructuredFunction, StructuredSourceType, StructuredSourceChoice, StructuredSourceRecord};

use heather_kernel::term::{LocalVar, Term, Type};
use heather_syntax::{Decl, DeclKind, Expr, ExprKind, Ty, TyKind};

use crate::Elaborator;
use crate::function_ir_cert::{self as cert, Node, Port, Region};
use crate::function_ir_x86_lower::{self as x86, Gpr, LoweringError};
use crate::heather_emit::{Block, Declaration, Expr as HeatherExpr, Module, Parameter, Statement};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum SourceBinaryOperation {
    Add,
    Sub,
    BitAnd,
    BitOr,
    BitXor,
}

impl SourceBinaryOperation {
    fn from_name(name: &str) -> Option<Self> {
        match name {
            "bitvec::BitVec::add" => Some(Self::Add),
            "bitvec::BitVec::sub" => Some(Self::Sub),
            "bitvec::BitVec::band" => Some(Self::BitAnd),
            "bitvec::BitVec::bor" => Some(Self::BitOr),
            "bitvec::BitVec::bxor" => Some(Self::BitXor),
            _ => None,
        }
    }

    fn node(self, output: u64, left: u64, right: u64) -> Node {
        self.node_at_width(64, output, left, right)
    }

    fn node_at_width(self, width: u64, output: u64, left: u64, right: u64) -> Node {
        match self {
            Self::Add => Node::Add { width, output, left, right },
            Self::Sub => Node::Sub { width, output, left, right },
            Self::BitAnd => Node::BitAnd { width, output, left, right },
            Self::BitOr => Node::BitOr { width, output, left, right },
            Self::BitXor => Node::BitXor { width, output, left, right },
        }
    }

    fn semantic_name(self) -> &'static str {
        match self {
            Self::Add => "bitvec::BitVec::add",
            Self::Sub => "bitvec::BitVec::sub",
            Self::BitAnd => "bitvec::BitVec::band",
            Self::BitOr => "bitvec::BitVec::bor",
            Self::BitXor => "bitvec::BitVec::bxor",
        }
    }

    fn congruence_name(self) -> &'static str {
        match self {
            Self::Add => "bitvec64_add_congruent",
            Self::Sub => "bitvec64_sub_congruent",
            Self::BitAnd => "bitvec64_band_congruent",
            Self::BitOr => "bitvec64_bor_congruent",
            Self::BitXor => "bitvec64_bxor_congruent",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum SourceExpr {
    Input(u64),
    Constant(u64),
    Binary {
        operation: SourceBinaryOperation,
        left: Box<SourceExpr>,
        right: Box<SourceExpr>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReflectedFunction {
    pub source_name: String,
    pub parameter_names: [String; 2],
    pub operation: SourceBinaryOperation,
    pub region: Region,
    pub result: SourceExpr,
    pub node_expressions: Vec<(u64, SourceExpr)>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceX86Emission {
    pub reflected: ReflectedFunction,
    pub instructions: Vec<x86::Instruction>,
    pub text: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceFunctionIrEmission {
    pub reflected: ReflectedFunction,
    pub text: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SourceError {
    Unsupported(String),
    InvalidRegion(String),
    Lowering(LoweringError),
}

impl std::fmt::Display for SourceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unsupported(message) | Self::InvalidRegion(message) => f.write_str(message),
            Self::Lowering(error) => write!(f, "x86 lowering declined: {error:?}"),
        }
    }
}

impl std::error::Error for SourceError {}

pub fn reflect(declaration: &Decl) -> Result<ReflectedFunction, SourceError> {
    if declaration.kind != DeclKind::Fn {
        return unsupported("only computing `fn` declarations are compilable");
    }
    if declaration.is_meta || !declaration.tyvars.is_empty() {
        return unsupported("meta and polymorphic functions are outside the initial fragment");
    }
    if declaration.params.len() != 2 {
        return unsupported("the initial fragment requires exactly two parameters");
    }
    if !declaration.body.stmts.is_empty() || !declaration.body.ons.is_empty() {
        return unsupported("local statements and proof discharges are not yet supported");
    }
    for parameter in &declaration.params {
        if parameter.implicit || parameter.solver.is_some() || !is_bitvec_64(&parameter.ty) {
            return unsupported("parameters must be explicit `BitVec(64)` values");
        }
    }
    if !is_bitvec_64(&declaration.result) {
        return unsupported("the result must be `BitVec(64)`");
    }

    let (operation, left, right) = binary_call(&declaration.body.result)?;
    let left_id = parameter_id(left, declaration)?;
    let right_id = parameter_id(right, declaration)?;
    let output = 2;
    let result = SourceExpr::Binary {
        operation,
        left: Box::new(SourceExpr::Input(left_id)),
        right: Box::new(SourceExpr::Input(right_id)),
    };
    let region = Region {
        inputs: vec![Port { id: 0, width: 64 }, Port { id: 1, width: 64 }],
        nodes: vec![operation.node(output, left_id, right_id)],
        outputs: vec![Port {
            id: output,
            width: 64,
        }],
    };
    Ok(ReflectedFunction {
        source_name: declaration.name.clone(),
        parameter_names: [
            declaration.params[0].name.clone(),
            declaration.params[1].name.clone(),
        ],
        operation,
        region,
        result: result.clone(),
        node_expressions: vec![(output, result)],
    })
}

/// Reflect a checked global's elaborated body. Unlike [`reflect`], this sees
/// resolved operation identities and elaborated-away surface `let`s.
pub fn reflect_elaborated(
    elaborator: &Elaborator,
    source_name: &str,
) -> Result<ReflectedFunction, SourceError> {
    let caller_abs = elaborator.global_abs(source_name).ok_or_else(|| {
        SourceError::Unsupported(format!("unknown source function `{source_name}`"))
    })?;
    let qualified_source_name =
        elaborator
            .global_qualified_name_at(caller_abs)
            .ok_or_else(|| {
                SourceError::Unsupported(format!(
                    "source function `{source_name}` has no canonical global name"
                ))
            })?;
    let (ty, body) = elaborator.global_body(source_name).ok_or_else(|| {
        SourceError::Unsupported(format!(
            "`{source_name}` is not a transparent computing function"
        ))
    })?;
    if pi_arity(&ty) != 2 {
        return unsupported("the initial elaborated fragment requires exactly two parameters");
    }
    let mut core = &*body;
    let mut lambda_count = 0usize;
    while let Term::Lam { body, .. } = core {
        lambda_count += 1;
        core = body;
    }
    if lambda_count != 2 {
        return unsupported("the checked source body must elaborate to exactly two lambdas");
    }

    let operations = OperationGlobals::resolve(elaborator)?;
    let result = reflect_term(core, caller_abs, &operations)?;
    let operation = match &result {
        SourceExpr::Binary { operation, .. } => *operation,
        _ => return unsupported("the source result must be a supported binary BitVec expression"),
    };
    let (region, node_expressions) = build_region(&result)?;
    Ok(ReflectedFunction {
        source_name: qualified_source_name,
        parameter_names: ["argument_0".to_string(), "argument_1".to_string()],
        operation,
        region,
        result,
        node_expressions,
    })
}

struct OperationGlobals {
    operations: BTreeMap<usize, SourceBinaryOperation>,
    of_nat: usize,
}

impl OperationGlobals {
    fn resolve(elaborator: &Elaborator) -> Result<Self, SourceError> {
        let mut operations = BTreeMap::new();
        for (name, operation) in [
            ("bitvec::BitVec::add", SourceBinaryOperation::Add),
            ("bitvec::BitVec::sub", SourceBinaryOperation::Sub),
            ("bitvec::BitVec::band", SourceBinaryOperation::BitAnd),
            ("bitvec::BitVec::bor", SourceBinaryOperation::BitOr),
            ("bitvec::BitVec::bxor", SourceBinaryOperation::BitXor),
        ] {
            let abs = elaborator.global_abs(name).ok_or_else(|| {
                SourceError::Unsupported(format!("required operation `{name}` is not loaded"))
            })?;
            operations.insert(abs, operation);
        }
        let of_nat = elaborator.global_abs("bitvec::BitVec::ofNat").ok_or_else(|| {
            SourceError::Unsupported("required operation `bitvec::BitVec::ofNat` is not loaded".to_string())
        })?;
        Ok(Self { operations, of_nat })
    }
}

fn pi_arity(ty: &Type) -> usize {
    let mut arity = 0;
    let mut current = ty;
    while let Type::Pi { cod, .. } = current {
        arity += 1;
        current = cod;
    }
    arity
}

fn reflect_term(
    term: &Term,
    caller_abs: usize,
    globals: &OperationGlobals,
) -> Result<SourceExpr, SourceError> {
    reflect_term_under(term, caller_abs, globals, 0)
}

fn reflect_term_under(
    term: &Term,
    caller_abs: usize,
    globals: &OperationGlobals,
    branch_binders: u32,
) -> Result<SourceExpr, SourceError> {
    if let Term::Var(LocalVar(index)) = term {
        return match index.checked_sub(branch_binders) {
            Some(1) => Ok(SourceExpr::Input(0)),
            Some(0) => Ok(SourceExpr::Input(1)),
            _ => unsupported("the source expression captures an unsupported local binder"),
        };
    }

    let (head, arguments) = application_spine(term);
    let Term::GlobalTm { var, .. } = head else {
        return unsupported("the source expression is not headed by a resolved global operation");
    };
    let head_abs = caller_abs.checked_sub(1 + var.0 as usize).ok_or_else(|| {
        SourceError::Unsupported("source global reference escapes its Ψ prefix".to_string())
    })?;
    if let Some(operation) = globals.operations.get(&head_abs).copied() {
        if arguments.len() != 3 || nat_literal(arguments[0]) != Some(64) {
            return unsupported("supported BitVec binary operations must be applied at width 64");
        }
        return Ok(SourceExpr::Binary {
            operation,
            left: Box::new(reflect_term_under(arguments[1], caller_abs, globals, branch_binders)?),
            right: Box::new(reflect_term_under(arguments[2], caller_abs, globals, branch_binders)?),
        });
    }
    if head_abs == globals.of_nat {
        if arguments.len() != 2 || nat_literal(arguments[0]) != Some(64) {
            return unsupported("BitVec constants must use `@bitvec::BitVec::ofNat(64, literal)`");
        }
        let Some(value) = nat_literal(arguments[1]) else {
            return unsupported("the initial constant fragment requires a closed Nat literal");
        };
        return Ok(SourceExpr::Constant(value));
    }
    unsupported("the elaborated source calls an operation outside Add/Sub/AND/OR/XOR/ofNat")
}

/// Initial call fragment: a checked forwarding wrapper, with resolved identity.
/// No surface-name matching, argument reordering, hidden captures, or inlining.
pub fn reflect_forwarded_call(elaborator: &Elaborator, source_name: &str) -> Result<String, SourceError> {
    let (callee, local) = reflect_call_wrapper(elaborator, source_name)?;
    if local { return unsupported("expected a forwarding-only wrapper"); }
    Ok(callee)
}

/// Bounded frame customer: caller = leaf(left, right) XOR (left XOR right).
/// The producer saves the second expression before the call and reloads it.
pub fn reflect_call_wrapper(elaborator: &Elaborator, source_name: &str) -> Result<(String, bool), SourceError> {
    let (callee, local, twice) = reflect_call_plan(elaborator, source_name)?;
    if twice { return unsupported("expected a single-call wrapper"); }
    Ok((callee, local))
}

/// The two-call slice threads the first result into the second call's left
/// argument, retaining the original right argument and caller XOR local.
pub fn reflect_call_plan(elaborator: &Elaborator, source_name: &str) -> Result<(String, bool, bool), SourceError> {
    let caller = elaborator.global_abs(source_name)
        .ok_or_else(|| SourceError::Unsupported(format!("unknown source function `{source_name}`")))?;
    let (ty, body) = elaborator.global_body(source_name)
        .ok_or_else(|| SourceError::Unsupported("caller must be a transparent function".into()))?;
    if pi_arity(&ty) != 2 { return unsupported("call wrapper requires two parameters"); }
    let Term::Lam { body, .. } = &*body else { return unsupported("expected first caller parameter"); };
    let Term::Lam { body, .. } = &**body else { return unsupported("expected second caller parameter"); };
    let abs = |head: &Term| match head {
        Term::GlobalTm { var, .. } => caller.checked_sub(1 + var.0 as usize),
        _ => None,
    };
    let (mut head, mut args) = application_spine(body);
    let mut saved_local = false;
    if abs(head) == elaborator.global_abs("bitvec::BitVec::bxor") {
        if args.len() != 3 || nat_literal(args[0]) != Some(64) { return unsupported("expected width-64 caller XOR"); }
        let (saved, values) = application_spine(args[2]);
        if abs(saved) != elaborator.global_abs("bitvec::BitVec::bxor") || values.len() != 3
            || nat_literal(values[0]) != Some(64) || !matches!(values[1], Term::Var(LocalVar(1)))
            || !matches!(values[2], Term::Var(LocalVar(0))) {
            return unsupported("supported frame expression is leaf(left, right) XOR (left XOR right)");
        }
        (head, args) = application_spine(args[1]);
        saved_local = true;
    }
    let Term::GlobalTm { var, .. } = head else { return unsupported("caller must directly call one resolved function"); };
    if args.len() != 2 || !matches!(args[1], Term::Var(LocalVar(0))) {
        return unsupported("call wrapper must retain its original right argument");
    }
    let twice = !matches!(args[0], Term::Var(LocalVar(1)));
    if twice {
        let (inner, values) = application_spine(args[0]);
        if !saved_local || abs(inner) != abs(head) || values.len() != 2
            || !matches!(values[0], Term::Var(LocalVar(1))) || !matches!(values[1], Term::Var(LocalVar(0))) {
            return unsupported("two-call wrapper requires leaf(leaf(left, right), right) XOR (left XOR right)");
        }
    }
    let callee = caller.checked_sub(1 + var.0 as usize)
        .ok_or_else(|| SourceError::Unsupported("callee escapes source scope".into()))?;
    elaborator.global_qualified_name_at(callee)
        .map(|name| (name, saved_local, twice))
        .ok_or_else(|| SourceError::Unsupported("callee has no qualified identity".into()))
}

fn application_spine(term: &Term) -> (&Term, Vec<&Term>) {
    let mut head = term;
    let mut arguments = Vec::new();
    while let Some((fun, arg)) = crate::spelling::app_of(head) {
        arguments.push(&**arg);
        head = fun;
    }
    arguments.reverse();
    (head, arguments)
}

/// A bounded, pure caller expression. Calls retain resolved source identities;
/// the native producer must still prove its translation against the source.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum CallExpr {
    Input(usize),
    Constant(u64),
    Binary(SourceBinaryOperation, Box<CallExpr>, Box<CallExpr>),
    Call(Box<CallExpr>, Box<CallExpr>),
}

impl CallExpr {
    pub fn expression(&self, callee: &str, inputs: &[HeatherExpr; 2]) -> HeatherExpr {
        match self {
            Self::Input(i) => inputs[*i].clone(),
            Self::Constant(n) => HeatherExpr::explicit_call("bitvec::BitVec::ofNat", [HeatherExpr::nat(64), HeatherExpr::nat(*n)]),
            Self::Binary(op, left, right) => HeatherExpr::explicit_call(op.semantic_name(), [HeatherExpr::nat(64), left.expression(callee, inputs), right.expression(callee, inputs)]),
            Self::Call(left, right) => HeatherExpr::call(callee, [left.expression(callee, inputs), right.expression(callee, inputs)]),
        }
    }
}

pub fn reflect_call_expression(elaborator: &Elaborator, source: &str, callee: &str) -> Result<CallExpr, SourceError> {
    let caller = elaborator.global_abs(source).ok_or_else(|| SourceError::Unsupported(format!("unknown source function `{source}`")))?;
    let selected = elaborator.global_abs(callee).ok_or_else(|| SourceError::Unsupported(format!("unknown opted-in callee `{callee}`")))?;
    let (ty, body) = elaborator.global_body(source).ok_or_else(|| SourceError::Unsupported("caller must be a transparent function".into()))?;
    if pi_arity(&ty) != 2 { return unsupported("caller requires two BitVec(64) parameters"); }
    let Term::Lam { body, .. } = &*body else { return unsupported("expected first caller parameter"); };
    let Term::Lam { body, .. } = &**body else { return unsupported("expected second caller parameter"); };
    let globals = OperationGlobals::resolve(elaborator)?;
    fn walk(term: &Term, caller: usize, selected: usize, globals: &OperationGlobals, budget: &mut usize, calls: &mut std::collections::BTreeSet<CallExpr>) -> Result<CallExpr, SourceError> {
        if *budget == 0 { return unsupported("caller expression exceeds the 64-node composition limit"); }
        *budget -= 1;
        if let Term::Var(LocalVar(index)) = term {
            return match index { 1 => Ok(CallExpr::Input(0)), 0 => Ok(CallExpr::Input(1)), _ => unsupported("unsupported caller capture") };
        }
        let (head, args) = application_spine(term);
        let Term::GlobalTm { var, .. } = head else { return unsupported("caller supports straight-line arithmetic and direct calls only"); };
        let abs = caller.checked_sub(1 + var.0 as usize).ok_or_else(|| SourceError::Unsupported("caller reference escapes source scope".into()))?;
        if abs == selected && args.len() == 2 {
            let call = CallExpr::Call(Box::new(walk(args[0], caller, selected, globals, budget, calls)?), Box::new(walk(args[1], caller, selected, globals, budget, calls)?));
            calls.insert(call.clone());
            if calls.len() > 4 { return unsupported("caller exceeds the four-call composition limit"); }
            return Ok(call);
        }
        if let Some(op) = globals.operations.get(&abs) {
            if args.len() != 3 || nat_literal(args[0]) != Some(64) { return unsupported("caller arithmetic requires width 64"); }
            return Ok(CallExpr::Binary(*op, Box::new(walk(args[1], caller, selected, globals, budget, calls)?), Box::new(walk(args[2], caller, selected, globals, budget, calls)?)));
        }
        if abs == globals.of_nat && args.len() == 2 && nat_literal(args[0]) == Some(64) {
            if let Some(n) = nat_literal(args[1]) { return Ok(CallExpr::Constant(n)); }
        }
        unsupported("caller contains an unsupported operation or a call to a function not selected by --callee")
    }
    let mut calls = std::collections::BTreeSet::new();
    let result = walk(body, caller, selected, &globals, &mut 64, &mut calls)?;
    if calls.is_empty() { return unsupported("caller must call the opted-in callee"); }
    Ok(result)
}

fn nat_literal(term: &Term) -> Option<u64> {
    match term {
        Term::Zero => Some(0),
        Term::NatLit(value) => value.as_u64(),
        Term::Succ(predecessor) => nat_literal(predecessor)?.checked_add(1),
        _ => None,
    }
}

fn build_region(result: &SourceExpr) -> Result<(Region, Vec<(u64, SourceExpr)>), SourceError> {
    let mut builder = DagBuilder {
        next_id: 2,
        ids: BTreeMap::new(),
        nodes: Vec::new(),
        node_expressions: Vec::new(),
    };
    let output = builder.lower(result)?;
    Ok((
        Region {
            inputs: vec![Port { id: 0, width: 64 }, Port { id: 1, width: 64 }],
            nodes: builder.nodes,
            outputs: vec![Port {
                id: output,
                width: 64,
            }],
        },
        builder.node_expressions,
    ))
}

struct DagBuilder {
    next_id: u64,
    ids: BTreeMap<SourceExpr, u64>,
    nodes: Vec<Node>,
    node_expressions: Vec<(u64, SourceExpr)>,
}

impl DagBuilder {
    fn lower(&mut self, expression: &SourceExpr) -> Result<u64, SourceError> {
        if let SourceExpr::Input(id) = expression {
            return Ok(*id);
        }
        if let Some(id) = self.ids.get(expression) {
            return Ok(*id);
        }
        let operands = match expression {
            SourceExpr::Input(_) => unreachable!(),
            SourceExpr::Constant(_) => None,
            SourceExpr::Binary { left, right, .. } => Some((self.lower(left)?, self.lower(right)?)),
        };
        let id = self.next_id;
        let node = match (expression, operands) {
            (SourceExpr::Constant(value), None) => Node::Const {
                width: 64,
                output: id,
                value: *value,
            },
            (SourceExpr::Binary { operation, .. }, Some((left, right))) => {
                operation.node(id, left, right)
            }
            _ => unreachable!(),
        };
        self.next_id = self.next_id.checked_add(1).ok_or_else(|| {
            SourceError::Unsupported("source DAG exhausted stable IDs".to_string())
        })?;
        self.ids.insert(expression.clone(), id);
        self.nodes.push(node);
        self.node_expressions.push((id, expression.clone()));
        Ok(id)
    }
}

/// Emit raw FunctionIR, compact validity, and the equality between its output
/// and the actual source call.
pub fn generate_function_ir(
    prefix: &str,
    declaration: &Decl,
) -> Result<SourceFunctionIrEmission, SourceError> {
    generate_reflected_function_ir(prefix, reflect(declaration)?)
}

pub fn generate_elaborated_function_ir(
    elaborator: &Elaborator,
    prefix: &str,
    source_name: &str,
) -> Result<SourceFunctionIrEmission, SourceError> {
    generate_reflected_function_ir(prefix, reflect_elaborated(elaborator, source_name)?)
}

fn generate_reflected_function_ir(
    prefix: &str,
    reflected: ReflectedFunction,
) -> Result<SourceFunctionIrEmission, SourceError> {
    let region_name = format!("{prefix}_raw");
    let valid_name = format!("{prefix}_valid");
    let region_expr = format!("{region_name}()");
    let validity = cert::generate(&valid_name, &region_expr, &reflected.region)
        .map_err(SourceError::InvalidRegion)?;

    let mut module = Module::default();
    if let Some((source_module, _)) = reflected.source_name.rsplit_once("::") {
        module.raw(format!("import {source_module};"));
    }
    module.raw(cert::render_region_function(
        &region_name,
        &reflected.region,
    ));
    module.raw(validity.text);
    emit_source_semantics(prefix, &region_name, &reflected, &mut module)?;
    let output = reflected.region.outputs[0].id;
    let source_call = source_call(&reflected);
    let expression_ids = reflected
        .node_expressions
        .iter()
        .map(|(id, expression)| (expression.clone(), *id))
        .collect::<BTreeMap<_, _>>();
    let root_expansion =
        emit_source_expansion_theorems(prefix, &reflected, &expression_ids, &mut module)?;
    let expansion_name = format!("{prefix}_source_expands");
    module.declaration(
        Declaration::theorem(
            &expansion_name,
            HeatherExpr::equal(
                HeatherExpr::call(
                    source_term_name(prefix, output),
                    [HeatherExpr::name("values")],
                ),
                source_call.clone(),
            ),
            Block::expression(root_expansion),
        )
        .parameter(Parameter::explicit(
            "values",
            HeatherExpr::nullary("Valuation"),
        )),
    );
    module.declaration(
        Declaration::theorem(
            format!("{prefix}_denotes_source"),
            HeatherExpr::equal(valuation(output), source_call),
            Block::expression(HeatherExpr::call(
                "trans",
                [
                    value_fact(prefix, output),
                    HeatherExpr::call(expansion_name.as_str(), [HeatherExpr::name("values")]),
                ],
            )),
        )
        .parameter(Parameter::explicit(
            "values",
            HeatherExpr::nullary("Valuation"),
        ))
        .parameter(Parameter::explicit("graph", region_holds(&region_name))),
    );

    Ok(SourceFunctionIrEmission {
        reflected,
        text: module.render(),
    })
}

/// Compose source certification with x86 lowering and retarget the backend
/// artifact's result from a valuation entry to the source call. No correctness
/// statement factors through `ir_v1`.
pub fn generate_x86(
    prefix: &str,
    declaration: &Decl,
    input_registers: [Gpr; 2],
    temporary_registers: &[Gpr],
    requested_output: Gpr,
) -> Result<SourceX86Emission, SourceError> {
    generate_reflected_x86(
        prefix,
        reflect(declaration)?,
        input_registers,
        temporary_registers,
        requested_output,
    )
}

pub fn generate_elaborated_x86(
    elaborator: &Elaborator,
    prefix: &str,
    source_name: &str,
    input_registers: [Gpr; 2],
    temporary_registers: &[Gpr],
    requested_output: Gpr,
) -> Result<SourceX86Emission, SourceError> {
    generate_reflected_x86(
        prefix,
        reflect_elaborated(elaborator, source_name)?,
        input_registers,
        temporary_registers,
        requested_output,
    )
}

fn generate_reflected_x86(
    prefix: &str,
    reflected: ReflectedFunction,
    input_registers: [Gpr; 2],
    temporary_registers: &[Gpr],
    requested_output: Gpr,
) -> Result<SourceX86Emission, SourceError> {
    let frontend = generate_reflected_function_ir(prefix, reflected)?;
    let reflected = frontend.reflected;
    let region_name = format!("{prefix}_raw");
    let region_expr = format!("{region_name}()");
    let backend = x86::generate(
        prefix,
        &region_expr,
        &reflected.region,
        &input_registers,
        temporary_registers,
        requested_output,
    )
    .map_err(SourceError::Lowering)?;
    let source_call = source_call(&reflected);
    let mut module = Module::default();
    module.raw(frontend.text);
    module.raw(backend.text);

    let parameters = vec![
        Parameter::explicit("values", HeatherExpr::nullary("Valuation")),
        Parameter::explicit("before", HeatherExpr::name("MachineState<M>")),
        Parameter::explicit(
            "input_0_placed",
            HeatherExpr::call(
                "ValuePlaced",
                [
                    HeatherExpr::name("values"),
                    HeatherExpr::nat(0),
                    HeatherExpr::name(input_registers[0].heather_name()),
                    HeatherExpr::name("before"),
                ],
            ),
        ),
        Parameter::explicit(
            "input_1_placed",
            HeatherExpr::call(
                "ValuePlaced",
                [
                    HeatherExpr::name("values"),
                    HeatherExpr::nat(1),
                    HeatherExpr::name(input_registers[1].heather_name()),
                    HeatherExpr::name("before"),
                ],
            ),
        ),
        Parameter::explicit("graph", region_holds(&region_name)),
    ];
    let backend_artifact = HeatherExpr::call(
        format!("{prefix}_artifact"),
        [
            HeatherExpr::name("values"),
            HeatherExpr::name("before"),
            HeatherExpr::name("input_0_placed"),
            HeatherExpr::name("input_1_placed"),
            HeatherExpr::name("graph"),
        ],
    );
    let source_artifact = HeatherExpr::named_call(
        "BlockArtifact",
        [
            ("after", HeatherExpr::name("artifact").project("after")),
            (
                "execution",
                HeatherExpr::name("artifact").project("execution"),
            ),
            (
                "result_correct",
                HeatherExpr::call(
                    "trans",
                    [
                        HeatherExpr::name("artifact").project("result_correct"),
                        HeatherExpr::call(
                            format!("{prefix}_denotes_source"),
                            [HeatherExpr::name("values"), HeatherExpr::name("graph")],
                        ),
                    ],
                ),
            ),
            (
                "memory_preserved",
                HeatherExpr::name("artifact").project("memory_preserved"),
            ),
            (
                "rip_correct",
                HeatherExpr::name("artifact").project("rip_correct"),
            ),
            (
                "registers_preserved",
                HeatherExpr::name("artifact").project("registers_preserved"),
            ),
        ],
    );
    module.declaration(
        Declaration::theorem(
            format!("{prefix}_source_artifact"),
            HeatherExpr::call(
                "BlockArtifact<M>",
                [
                    HeatherExpr::nullary(format!("{prefix}_instructions")),
                    HeatherExpr::name("before"),
                    HeatherExpr::name(requested_output.heather_name()),
                    source_call,
                    HeatherExpr::name(format!("{prefix}_Protected")),
                    HeatherExpr::call(
                        format!("{prefix}_final_rip"),
                        [HeatherExpr::name("before").project("rip")],
                    ),
                ],
            ),
            Block::new(
                [Statement::let_value("artifact", backend_artifact)],
                source_artifact,
            ),
        )
        .generic("M")
        .parameters(parameters),
    );

    Ok(SourceX86Emission {
        reflected,
        instructions: backend.lowered.instructions,
        text: module.render(),
    })
}

fn emit_source_semantics(
    prefix: &str,
    region_name: &str,
    reflected: &ReflectedFunction,
    module: &mut Module,
) -> Result<(), SourceError> {
    let node_count = reflected.region.nodes.len();
    let expression_ids = reflected
        .node_expressions
        .iter()
        .map(|(id, expression)| (expression.clone(), *id))
        .collect::<BTreeMap<_, _>>();
    module.declaration(Declaration::function(
        source_nodes_name(prefix, node_count),
        HeatherExpr::name("List<Node>"),
        Block::expression(HeatherExpr::list([])),
    ));
    for index in (0..node_count).rev() {
        module.declaration(Declaration::function(
            source_nodes_name(prefix, index),
            HeatherExpr::name("List<Node>"),
            Block::expression(HeatherExpr::call(
                "Cons",
                [
                    node_to_heather(reflected.region.nodes[index])?,
                    HeatherExpr::nullary(source_nodes_name(prefix, index + 1)),
                ],
            )),
        ));
    }

    for (id, expression) in &reflected.node_expressions {
        let body = match expression {
            SourceExpr::Input(_) => unreachable!(),
            SourceExpr::Constant(value) => HeatherExpr::explicit_call(
                "bitvec::BitVec::ofNat",
                [HeatherExpr::nat(64), HeatherExpr::nat(*value)],
            ),
            SourceExpr::Binary {
                operation,
                left,
                right,
            } => HeatherExpr::explicit_call(
                operation.semantic_name(),
                [
                    HeatherExpr::nat(64),
                    source_operand(prefix, left, &expression_ids)?,
                    source_operand(prefix, right, &expression_ids)?,
                ],
            ),
        };
        module.declaration(
            Declaration::function(
                source_term_name(prefix, *id),
                HeatherExpr::name("BitVec(64)"),
                Block::expression(body),
            )
            .parameter(Parameter::explicit(
                "values",
                HeatherExpr::nullary("Valuation"),
            )),
        );
    }

    for index in 0..node_count {
        let body = if index == 0 {
            HeatherExpr::name("graph")
        } else {
            HeatherExpr::call(
                source_graph_name(prefix, index - 1),
                [HeatherExpr::name("values"), HeatherExpr::name("graph")],
            )
            .project("right")
        };
        module.declaration(
            Declaration::theorem(
                source_graph_name(prefix, index),
                HeatherExpr::call(
                    "NodesHold",
                    [
                        HeatherExpr::name("values"),
                        HeatherExpr::nullary(source_nodes_name(prefix, index)),
                    ],
                ),
                Block::expression(body),
            )
            .parameter(Parameter::explicit(
                "values",
                HeatherExpr::nullary("Valuation"),
            ))
            .parameter(Parameter::explicit("graph", region_holds(region_name))),
        );
    }

    for (index, ((id, expression), node)) in reflected
        .node_expressions
        .iter()
        .zip(&reflected.region.nodes)
        .enumerate()
    {
        let equation = HeatherExpr::call(
            source_graph_name(prefix, index),
            [HeatherExpr::name("values"), HeatherExpr::name("graph")],
        )
        .project("left");
        let proof = match (expression, node) {
            (SourceExpr::Constant(_), Node::Const { .. }) => equation,
            (
                SourceExpr::Binary {
                    operation,
                    left,
                    right,
                },
                Node::Add {
                    left: left_id,
                    right: right_id,
                    ..
                }
                | Node::Sub {
                    left: left_id,
                    right: right_id,
                    ..
                }
                | Node::BitAnd {
                    left: left_id,
                    right: right_id,
                    ..
                }
                | Node::BitOr {
                    left: left_id,
                    right: right_id,
                    ..
                }
                | Node::BitXor {
                    left: left_id,
                    right: right_id,
                    ..
                },
            ) => HeatherExpr::call(
                "binary_node_denotes",
                [
                    HeatherExpr::nat(64),
                    HeatherExpr::nat(*id),
                    HeatherExpr::nat(*left_id),
                    HeatherExpr::nat(*right_id),
                    operation_lambda(*operation),
                    source_operand(prefix, left, &expression_ids)?,
                    source_operand(prefix, right, &expression_ids)?,
                    HeatherExpr::name("values"),
                    source_value_proof(prefix, left, &expression_ids)?,
                    source_value_proof(prefix, right, &expression_ids)?,
                    equation,
                ],
            ),
            _ => {
                return unsupported("reflected expression and FunctionIR node schedules disagree");
            }
        };
        module.declaration(
            Declaration::theorem(
                source_value_name(prefix, *id),
                HeatherExpr::equal(
                    valuation(*id),
                    HeatherExpr::call(source_term_name(prefix, *id), [HeatherExpr::name("values")]),
                ),
                Block::expression(proof),
            )
            .parameter(Parameter::explicit(
                "values",
                HeatherExpr::nullary("Valuation"),
            ))
            .parameter(Parameter::explicit("graph", region_holds(region_name))),
        );
    }
    Ok(())
}

fn source_nodes_name(prefix: &str, index: usize) -> String {
    format!("{prefix}_source_nodes_{index}")
}

fn source_graph_name(prefix: &str, index: usize) -> String {
    format!("{prefix}_source_graph_{index}")
}

fn source_value_name(prefix: &str, id: u64) -> String {
    format!("{prefix}_source_value_{id}")
}

fn source_term_name(prefix: &str, id: u64) -> String {
    format!("{prefix}_source_term_{id}")
}

fn value_fact(prefix: &str, id: u64) -> HeatherExpr {
    HeatherExpr::call(
        source_value_name(prefix, id),
        [HeatherExpr::name("values"), HeatherExpr::name("graph")],
    )
}

fn source_value_proof(
    prefix: &str,
    expression: &SourceExpr,
    expression_ids: &BTreeMap<SourceExpr, u64>,
) -> Result<HeatherExpr, SourceError> {
    match expression {
        SourceExpr::Input(id) => Ok(HeatherExpr::call(
            "equality_refl<BitVec(64)>",
            [valuation(*id)],
        )),
        _ => expression_ids
            .get(expression)
            .copied()
            .map(|id| value_fact(prefix, id))
            .ok_or_else(|| {
                SourceError::Unsupported(
                    "source expression is absent from the reflected DAG schedule".to_string(),
                )
            }),
    }
}

fn operation_lambda(operation: SourceBinaryOperation) -> HeatherExpr {
    HeatherExpr::lambda(
        ["left", "right"],
        HeatherExpr::explicit_call(
            operation.semantic_name(),
            [
                HeatherExpr::nat(64),
                HeatherExpr::name("left"),
                HeatherExpr::name("right"),
            ],
        ),
    )
}

fn source_operand(
    prefix: &str,
    expression: &SourceExpr,
    expression_ids: &BTreeMap<SourceExpr, u64>,
) -> Result<HeatherExpr, SourceError> {
    match expression {
        SourceExpr::Input(id) => Ok(valuation(*id)),
        _ => expression_ids
            .get(expression)
            .copied()
            .map(|id| {
                HeatherExpr::call(source_term_name(prefix, id), [HeatherExpr::name("values")])
            })
            .ok_or_else(|| {
                SourceError::Unsupported(
                    "source operand is absent from the reflected DAG schedule".to_string(),
                )
            }),
    }
}

fn source_expansion_fact(
    prefix: &str,
    expression: &SourceExpr,
    expression_ids: &BTreeMap<SourceExpr, u64>,
) -> Result<HeatherExpr, SourceError> {
    match expression {
        SourceExpr::Input(_) => Ok(HeatherExpr::name("refl")),
        _ => expression_ids
            .get(expression)
            .copied()
            .map(|id| {
                HeatherExpr::call(
                    source_expansion_name(prefix, id),
                    [HeatherExpr::name("values")],
                )
            })
            .ok_or_else(|| {
                SourceError::Unsupported(
                    "source expression is absent from the reflected DAG schedule".to_string(),
                )
            }),
    }
}

fn emit_source_expansion_theorems(
    prefix: &str,
    reflected: &ReflectedFunction,
    expression_ids: &BTreeMap<SourceExpr, u64>,
    module: &mut Module,
) -> Result<HeatherExpr, SourceError> {
    let output = reflected.region.outputs[0].id;
    for (id, expression) in &reflected.node_expressions {
        let name = source_expansion_name(prefix, *id);
        let body = match expression {
            SourceExpr::Input(_) => unreachable!(),
            SourceExpr::Constant(_) => Block::expression(HeatherExpr::name("refl")),
            SourceExpr::Binary {
                operation,
                left,
                right,
            } => Block::expression(HeatherExpr::call(
                format!("@{}", operation.congruence_name()),
                [
                    source_operand(prefix, left, expression_ids)?,
                    source_expression(left),
                    source_operand(prefix, right, expression_ids)?,
                    source_expression(right),
                    source_expansion_fact(prefix, left, expression_ids)?,
                    source_expansion_fact(prefix, right, expression_ids)?,
                ],
            )),
        };
        module.declaration(
            Declaration::theorem(
                &name,
                HeatherExpr::equal(
                    HeatherExpr::call(source_term_name(prefix, *id), [HeatherExpr::name("values")]),
                    source_expression(expression),
                ),
                body,
            )
            .parameter(Parameter::explicit(
                "values",
                HeatherExpr::nullary("Valuation"),
            )),
        );
    }
    Ok(HeatherExpr::call(
        source_expansion_name(prefix, output),
        [HeatherExpr::name("values")],
    ))
}

fn source_expansion_name(prefix: &str, id: u64) -> String {
    format!("{prefix}_source_expansion_{id}")
}

fn source_expression(expression: &SourceExpr) -> HeatherExpr {
    match expression {
        SourceExpr::Input(id) => valuation(*id),
        SourceExpr::Constant(value) => HeatherExpr::explicit_call(
            "bitvec::BitVec::ofNat",
            [HeatherExpr::nat(64), HeatherExpr::nat(*value)],
        ),
        SourceExpr::Binary {
            operation,
            left,
            right,
        } => HeatherExpr::explicit_call(
            operation.semantic_name(),
            [
                HeatherExpr::nat(64),
                source_expression(left),
                source_expression(right),
            ],
        ),
    }
}

fn node_to_heather(node: Node) -> Result<HeatherExpr, SourceError> {
    let binary = |constructor: &'static str, width, output, left, right| {
        HeatherExpr::named_call(
            constructor,
            [
                ("width", HeatherExpr::nat(width)),
                ("output", HeatherExpr::nat(output)),
                ("left", HeatherExpr::nat(left)),
                ("right", HeatherExpr::nat(right)),
            ],
        )
    };
    match node {
        Node::Const {
            width,
            output,
            value,
        } => Ok(HeatherExpr::named_call(
            "Const",
            [
                ("width", HeatherExpr::nat(width)),
                ("output", HeatherExpr::nat(output)),
                ("value", HeatherExpr::nat(value)),
            ],
        )),
        Node::Add {
            width,
            output,
            left,
            right,
        } => Ok(binary("Add", width, output, left, right)),
        Node::Sub {
            width,
            output,
            left,
            right,
        } => Ok(binary("Sub", width, output, left, right)),
        Node::BitAnd {
            width,
            output,
            left,
            right,
        } => Ok(binary("BitAnd", width, output, left, right)),
        Node::BitOr {
            width,
            output,
            left,
            right,
        } => Ok(binary("BitOr", width, output, left, right)),
        Node::BitXor {
            width,
            output,
            left,
            right,
        } => Ok(binary("BitXor", width, output, left, right)),
        _ => unsupported("source semantics do not yet support this FunctionIR node"),
    }
}

fn valuation(id: u64) -> HeatherExpr {
    HeatherExpr::call("values", [HeatherExpr::nat(64), HeatherExpr::nat(id)])
}

fn source_call(reflected: &ReflectedFunction) -> HeatherExpr {
    HeatherExpr::call(reflected.source_name.clone(), [valuation(0), valuation(1)])
}

fn region_holds(region_name: &str) -> HeatherExpr {
    HeatherExpr::call(
        "RegionHolds",
        [
            HeatherExpr::nullary(region_name),
            HeatherExpr::name("values"),
        ],
    )
}

fn unsupported<T>(message: &str) -> Result<T, SourceError> {
    Err(SourceError::Unsupported(message.to_string()))
}

fn is_bitvec_64(ty: &Ty) -> bool {
    let TyKind::OfExpr(expression) = &ty.kind else {
        return false;
    };
    let ExprKind::App {
        head, args, named, ..
    } = &expression.kind
    else {
        return false;
    };
    matches!(&head.kind, ExprKind::Var(name) if name == "BitVec")
        && named.is_empty()
        && matches!(
            args.as_slice(),
            [Expr {
                kind: ExprKind::Num(width),
                ..
            }] if width.as_u64() == Some(64)
        )
}

fn binary_call(body: &Expr) -> Result<(SourceBinaryOperation, &Expr, &Expr), SourceError> {
    let ExprKind::App {
        head, args, named, ..
    } = &body.kind
    else {
        return unsupported("the body must be one supported BitVec binary operation");
    };
    let ExprKind::Var(name) = &head.kind else {
        return unsupported("the body call must have a named operation at its head");
    };
    let Some(operation) = SourceBinaryOperation::from_name(name) else {
        return unsupported("supported operations are bitvec::BitVec::add/sub/band/bor/bxor");
    };
    if !named.is_empty() || args.len() != 3 {
        return unsupported("the BitVec operation must have width, left, and right arguments");
    }
    if !matches!(&args[0].kind, ExprKind::Num(width) if width.as_u64() == Some(64)) {
        return unsupported("the initial fragment supports only width 64");
    }
    Ok((operation, &args[1], &args[2]))
}

fn parameter_id(argument: &Expr, declaration: &Decl) -> Result<u64, SourceError> {
    let ExprKind::Var(name) = &argument.kind else {
        return unsupported("binary operands must be source parameters");
    };
    declaration
        .params
        .iter()
        .position(|parameter| parameter.name == *name)
        .map(|index| index as u64)
        .ok_or_else(|| SourceError::Unsupported(format!("unknown source operand `{name}`")))
}

#[cfg(test)]
mod tests {
    use super::{build_region, SourceBinaryOperation, SourceExpr};
    use crate::function_ir_cert::Node;

    #[test]
    fn structural_postorder_recovers_shared_subexpressions() {
        let shared = SourceExpr::Binary {
            operation: SourceBinaryOperation::Add,
            left: Box::new(SourceExpr::Input(0)),
            right: Box::new(SourceExpr::Input(1)),
        };
        let result = SourceExpr::Binary {
            operation: SourceBinaryOperation::BitXor,
            left: Box::new(shared.clone()),
            right: Box::new(SourceExpr::Binary {
                operation: SourceBinaryOperation::Add,
                left: Box::new(shared),
                right: Box::new(SourceExpr::Constant(7)),
            }),
        };
        let (region, _) = build_region(&result).expect("lower shared expression");
        assert_eq!(
            region.nodes,
            vec![
                Node::Add {
                    width: 64,
                    output: 2,
                    left: 0,
                    right: 1
                },
                Node::Const {
                    width: 64,
                    output: 3,
                    value: 7
                },
                Node::Add {
                    width: 64,
                    output: 4,
                    left: 2,
                    right: 3
                },
                Node::BitXor {
                    width: 64,
                    output: 5,
                    left: 2,
                    right: 4
                },
            ],
        );
    }
}
