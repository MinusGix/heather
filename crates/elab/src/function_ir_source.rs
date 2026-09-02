//! First source-to-FunctionIR certification path.
//!
//! The fragment is intentionally narrow: one monomorphic pure `BitVec(64)`
//! binary operation. The surface declaration chooses a graph, but the emitted
//! theorem names the actual source function, so stale translation is rejected
//! by ordinary elaboration and kernel checking.

use heather_syntax::{Decl, DeclKind, Expr, ExprKind, Ty, TyKind};

use crate::function_ir_cert::{self as cert, Node, Port, Region};
use crate::function_ir_x86_lower::{self as x86, Gpr, LoweringError};
use crate::heather_emit::{Block, Declaration, Expr as HeatherExpr, Module, Parameter, Statement};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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
            "bitvec::add" => Some(Self::Add),
            "bitvec::sub" => Some(Self::Sub),
            "bitvec::band" => Some(Self::BitAnd),
            "bitvec::bor" => Some(Self::BitOr),
            "bitvec::bxor" => Some(Self::BitXor),
            _ => None,
        }
    }

    fn node(self, output: u64, left: u64, right: u64) -> Node {
        match self {
            Self::Add => Node::Add {
                width: 64,
                output,
                left,
                right,
            },
            Self::Sub => Node::Sub {
                width: 64,
                output,
                left,
                right,
            },
            Self::BitAnd => Node::BitAnd {
                width: 64,
                output,
                left,
                right,
            },
            Self::BitOr => Node::BitOr {
                width: 64,
                output,
                left,
                right,
            },
            Self::BitXor => Node::BitXor {
                width: 64,
                output,
                left,
                right,
            },
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReflectedFunction {
    pub source_name: String,
    pub parameter_names: [String; 2],
    pub operation: SourceBinaryOperation,
    pub region: Region,
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
    })
}

/// Emit raw FunctionIR, compact validity, and the equality between its output
/// and the actual source call.
pub fn generate_function_ir(
    prefix: &str,
    declaration: &Decl,
) -> Result<SourceFunctionIrEmission, SourceError> {
    let reflected = reflect(declaration)?;
    let region_name = format!("{prefix}_raw");
    let valid_name = format!("{prefix}_valid");
    let region_expr = format!("{region_name}()");
    let validity = cert::generate(&valid_name, &region_expr, &reflected.region)
        .map_err(SourceError::InvalidRegion)?;

    let mut module = Module::default();
    module.raw(cert::render_region_function(
        &region_name,
        &reflected.region,
    ));
    module.raw(validity.text);
    let source_call = source_call(&reflected);
    module.declaration(
        Declaration::theorem(
            format!("{prefix}_denotes_source"),
            HeatherExpr::equal(valuation(2), source_call),
            Block::expression(HeatherExpr::name("graph").project("left")),
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
    let frontend = generate_function_ir(prefix, declaration)?;
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
                kind: ExprKind::Num(64),
                ..
            }]
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
        return unsupported("supported operations are bitvec::add/sub/band/bor/bxor");
    };
    if !named.is_empty() || args.len() != 3 {
        return unsupported("the BitVec operation must have width, left, and right arguments");
    }
    if !matches!(args[0].kind, ExprKind::Num(64)) {
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
