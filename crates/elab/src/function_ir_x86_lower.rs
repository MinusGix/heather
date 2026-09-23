//! Untrusted spill-free x86 selection and register assignment for the current
//! pure FunctionIR word ALU and zero-extended narrow-value fragment.
//! Proof emission consumes this explicit plan;
//! neither the allocator nor the plan is trusted by the kernel.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

mod encoding;
pub use encoding::{encode_instructions, encode_structured, register_code};
mod access;
pub use access::AccessFragment;
mod data_read;
pub use data_read::ByteLoad;
mod structured;
mod structured_cert;
pub use structured_cert::{generate_structured, generate_structured_results, StructuredX86Emission};
pub use structured::{lower_structured, lower_structured_results, LoweredStructured, Placements, StructuredPlan};

use crate::function_ir_cert::{
    self as cert, BlockArgument, ControlRegion, Node, Region, StructuredRegion,
};
use crate::heather_emit::{Block, Declaration, Expr, Module, Parameter};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinaryOperation {
    Add,
    Sub,
    BitAnd,
    BitOr,
    BitXor,
}

impl BinaryOperation {
    fn semantic_function(self) -> &'static str {
        match self {
            BinaryOperation::Add => "bitvec::BitVec::add",
            BinaryOperation::Sub => "bitvec::BitVec::sub",
            BinaryOperation::BitAnd => "bitvec::BitVec::band",
            BinaryOperation::BitOr => "bitvec::BitVec::bor",
            BinaryOperation::BitXor => "bitvec::BitVec::bxor",
        }
    }

    fn commutativity_theorem(self) -> Option<&'static str> {
        match self {
            BinaryOperation::Add => Some("bitvec::BitVec::add_comm"),
            BinaryOperation::Sub => None,
            BinaryOperation::BitAnd => Some("bitvec::BitVec::band_comm"),
            BinaryOperation::BitOr => Some("bitvec::BitVec::bor_comm"),
            BinaryOperation::BitXor => Some("bitvec::BitVec::bxor_comm"),
        }
    }
}

impl BinaryNode {
    fn render(self) -> String {
        let constructor = match self.operation {
            BinaryOperation::Add => "Add",
            BinaryOperation::Sub => "Sub",
            BinaryOperation::BitAnd => "BitAnd",
            BinaryOperation::BitOr => "BitOr",
            BinaryOperation::BitXor => "BitXor",
        };
        format!(
            "{constructor}(width := {}, output := {}, left := {}, right := {})",
            self.width, self.output, self.left, self.right,
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ConstantNode {
    pub width: u64,
    pub output: u64,
    pub value: u64,
}

impl ConstantNode {
    fn render(self) -> String {
        format!(
            "Const(width := {}, output := {}, value := {})",
            self.width, self.output, self.value,
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SelectedNode {
    Constant(ConstantNode),
    Binary(BinaryNode),
    Comparison(ComparisonNode),
}

impl SelectedNode {
    fn render(self) -> String {
        match self {
            SelectedNode::Constant(node) => node.render(),
            SelectedNode::Binary(node) => node.render(),
            SelectedNode::Comparison(node) => node.render(),
        }
    }

    fn output(self) -> u64 {
        match self {
            SelectedNode::Constant(node) => node.output,
            SelectedNode::Binary(node) => node.output,
            SelectedNode::Comparison(node) => node.output,
        }
    }

    fn width(self) -> u64 {
        match self {
            SelectedNode::Constant(node) => node.width,
            SelectedNode::Binary(node) => node.width,
            SelectedNode::Comparison(_) => 1,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BinaryNode {
    pub operation: BinaryOperation,
    pub width: u64,
    pub output: u64,
    pub left: u64,
    pub right: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ComparisonOperation {
    UnsignedLessThan,
    SignedLessThan,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ComparisonNode {
    pub operation: ComparisonOperation,
    pub operand_width: u64,
    pub output: u64,
    pub left: u64,
    pub right: u64,
}

impl ComparisonNode {
    fn render(self) -> String {
        let constructor = match self.operation {
            ComparisonOperation::UnsignedLessThan => "UnsignedLessThan",
            ComparisonOperation::SignedLessThan => "SignedLessThan",
        };
        format!(
            "{constructor}(width := {}, output := {}, left := {}, right := {})",
            self.operand_width, self.output, self.left, self.right,
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OperandOrientation {
    Original,
    Reversed,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Gpr {
    Rax,
    Rcx,
    Rdx,
    Rbx,
    Rsp,
    Rbp,
    Rsi,
    Rdi,
    R8,
    R9,
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LowByteGpr {
    Al,
    Cl,
    Dl,
    Bl,
}

impl LowByteGpr {
    fn from_gpr(register: Gpr) -> Option<Self> {
        match register {
            Gpr::Rax => Some(Self::Al),
            Gpr::Rcx => Some(Self::Cl),
            Gpr::Rdx => Some(Self::Dl),
            Gpr::Rbx => Some(Self::Bl),
            _ => None,
        }
    }

    fn gpr(self) -> Gpr {
        match self {
            Self::Al => Gpr::Rax,
            Self::Cl => Gpr::Rcx,
            Self::Dl => Gpr::Rdx,
            Self::Bl => Gpr::Rbx,
        }
    }

    fn heather_name(self) -> &'static str {
        match self {
            Self::Al => "Al",
            Self::Cl => "Cl",
            Self::Dl => "Dl",
            Self::Bl => "Bl",
        }
    }
}

impl Gpr {
    pub fn heather_name(self) -> &'static str {
        match self {
            Gpr::Rax => "Rax",
            Gpr::Rcx => "Rcx",
            Gpr::Rdx => "Rdx",
            Gpr::Rbx => "Rbx",
            Gpr::Rsp => "Rsp",
            Gpr::Rbp => "Rbp",
            Gpr::Rsi => "Rsi",
            Gpr::Rdi => "Rdi",
            Gpr::R8 => "R8",
            Gpr::R9 => "R9",
            Gpr::R10 => "R10",
            Gpr::R11 => "R11",
            Gpr::R12 => "R12",
            Gpr::R13 => "R13",
            Gpr::R14 => "R14",
            Gpr::R15 => "R15",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Instruction {
    MovRR { destination: Gpr, source: Gpr },
    MovRI { destination: Gpr, immediate: u64 },
    AddRR { destination: Gpr, source: Gpr },
    SubRR { destination: Gpr, source: Gpr },
    AndRR { destination: Gpr, source: Gpr },
    OrRR { destination: Gpr, source: Gpr },
    XorRR { destination: Gpr, source: Gpr },
    CmpRR { left: Gpr, right: Gpr },
    SetBelow { destination: LowByteGpr },
    SetLess { destination: LowByteGpr },
}

impl Instruction {
    pub fn render(self) -> String {
        self.heather_expr().render()
    }

    pub fn heather_expr(self) -> Expr {
        match self {
            Instruction::MovRR {
                destination,
                source,
            } => register_pair("MovRR", destination, source),
            Instruction::MovRI {
                destination,
                immediate,
            } => Expr::call(
                "MovRI",
                [
                    Expr::name(destination.heather_name()),
                    Expr::explicit_call("bitvec::BitVec::ofNat", [Expr::nat(64), Expr::nat(immediate)]),
                ],
            ),
            Instruction::AddRR {
                destination,
                source,
            } => register_pair("AddRR", destination, source),
            Instruction::SubRR {
                destination,
                source,
            } => register_pair("SubRR", destination, source),
            Instruction::AndRR {
                destination,
                source,
            } => register_pair("AndRR", destination, source),
            Instruction::OrRR {
                destination,
                source,
            } => register_pair("OrRR", destination, source),
            Instruction::XorRR {
                destination,
                source,
            } => register_pair("XorRR", destination, source),
            Instruction::CmpRR { left, right } => register_pair("CmpRR", left, right),
            Instruction::SetBelow { destination } => {
                Expr::call("SetBelow", [Expr::name(destination.heather_name())])
            }
            Instruction::SetLess { destination } => {
                Expr::call("SetLess", [Expr::name(destination.heather_name())])
            }
        }
    }

    pub fn destination(self) -> Option<Gpr> {
        match self {
            Instruction::MovRR { destination, .. }
            | Instruction::MovRI { destination, .. }
            | Instruction::AddRR { destination, .. }
            | Instruction::SubRR { destination, .. }
            | Instruction::AndRR { destination, .. }
            | Instruction::OrRR { destination, .. }
            | Instruction::XorRR { destination, .. } => Some(destination),
            Instruction::CmpRR { .. } => None,
            Instruction::SetBelow { destination } | Instruction::SetLess { destination } => {
                Some(destination.gpr())
            }
        }
    }

    pub fn canonical_length(self) -> usize {
        match self {
            Instruction::MovRI { .. } => 10,
            _ => 3,
        }
    }
}

fn register_pair(constructor: &str, left: Gpr, right: Gpr) -> Expr {
    Expr::call(
        constructor,
        [
            Expr::name(left.heather_name()),
            Expr::name(right.heather_name()),
        ],
    )
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NodePlan {
    pub node_index: usize,
    pub node: SelectedNode,
    pub left_register: Option<Gpr>,
    pub right_register: Option<Gpr>,
    pub destination: Gpr,
    pub reused_value: Option<u64>,
    pub orientation: OperandOrientation,
    pub instructions: Vec<Instruction>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoweredDag {
    pub input_registers: Vec<Gpr>,
    pub node_plans: Vec<NodePlan>,
    pub instructions: Vec<Instruction>,
    pub output_id: u64,
    pub output_width: u64,
    pub output_register: Gpr,
    pub clobbered: BTreeSet<Gpr>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct X86Emission {
    pub lowered: LoweredDag,
    pub text: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConditionalX86Emission {
    pub lowered: LoweredConditional,
    pub text: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrefixedConditionalX86Emission {
    pub prefix: LoweredDag,
    pub continuation: LoweredConditional,
    pub text: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ControlX86Emission {
    pub lowered: LoweredControlRegion,
    pub text: String,
}

/// Construct one still-expression-raw declaration through the structured
/// emission boundary.  Control certificate migration deliberately makes raw
/// expression leaves visible here while names, binders, declaration kinds,
/// and block structure are represented by `heather_emit` values.
fn emitted_parameter(name: impl Into<String>, ty: impl Into<String>) -> Parameter {
    Parameter::explicit(name, Expr::raw(ty))
}

fn emitted_function(
    name: impl Into<String>,
    machine_generic: bool,
    parameters: Vec<Parameter>,
    result: impl Into<String>,
    body: impl Into<String>,
) -> Declaration {
    let declaration =
        Declaration::function(name, Expr::raw(result), Block::expression(Expr::raw(body)))
            .parameters(parameters);
    if machine_generic {
        declaration.generic("M")
    } else {
        declaration
    }
}

fn emitted_theorem(
    name: impl Into<String>,
    machine_generic: bool,
    parameters: Vec<Parameter>,
    result: impl Into<String>,
    body: impl Into<String>,
) -> Declaration {
    let declaration =
        Declaration::theorem(name, Expr::raw(result), Block::expression(Expr::raw(body)))
            .parameters(parameters);
    if machine_generic {
        declaration.generic("M")
    } else {
        declaration
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoweredConditional {
    pub condition_id: u64,
    pub condition_register: Gpr,
    pub when_true: LoweredDag,
    pub when_false: LoweredDag,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoweredControlRegion {
    pub prefix: LoweredDag,
    pub condition_register: Gpr,
    pub when_true_transfer: Vec<Instruction>,
    pub when_false_transfer: Vec<Instruction>,
    pub join_registers: Vec<Gpr>,
    pub continuation: LoweredDag,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LoweringError {
    InputPlacementCount {
        inputs: usize,
        registers: usize,
    },
    DuplicateRegister(Gpr),
    InputOverlapsTemporary(Gpr),
    OutputRegisterUnavailable(Gpr),
    UnsupportedWidth {
        value: u64,
        width: u64,
    },
    DuplicateValue(u64),
    UndefinedValue(u64),
    OutputCount(usize),
    OutputPlacementCount { outputs: usize, registers: usize },
    UnsupportedOperation {
        node_index: usize,
    },
    NoSafeByteRegister {
        node_index: usize,
    },
    RegisterPressure {
        node_index: usize,
        live_temporaries: usize,
    },
    InvalidStructuredRegion(String),
    StructuredPath { path: String, reason: Box<LoweringError> },
    UnsupportedStructuredRegion,
    MissingConditionPlacement(u64),
    UnsupportedSequenceInterface,
    UnsupportedJoinArm,
    JoinPlacementCount {
        parameters: usize,
        registers: usize,
    },
    ParallelCopyNeedsTemporary,
    ShortBranchOutOfRange {
        bytes: usize,
    },
}

impl fmt::Display for LoweringError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LoweringError::InputPlacementCount { inputs, registers } => write!(
                f,
                "region has {inputs} inputs but {registers} input registers were supplied",
            ),
            LoweringError::DuplicateRegister(register) => {
                write!(f, "register {} appears twice", register.heather_name())
            }
            LoweringError::InputOverlapsTemporary(register) => write!(
                f,
                "input register {} also appears in the temporary pool",
                register.heather_name(),
            ),
            LoweringError::OutputRegisterUnavailable(register) => write!(
                f,
                "output register {} is not an assignable temporary",
                register.heather_name(),
            ),
            LoweringError::UnsupportedWidth { value, width } => {
                write!(
                    f,
                    "value {value} has unsupported x86 lowering width {width}"
                )
            }
            LoweringError::DuplicateValue(value) => {
                write!(f, "value {value} is defined more than once")
            }
            LoweringError::UndefinedValue(value) => write!(f, "value {value} is undefined"),
            LoweringError::OutputPlacementCount { outputs, registers } => write!(f, "result interface has {outputs} outputs but {registers} placements (at least one result is required)"),
            LoweringError::OutputCount(count) => {
                write!(f, "single-result block lowering received {count} outputs")
            }
            LoweringError::UnsupportedOperation { node_index } => {
                write!(f, "node {node_index} is not yet supported by x86 lowering")
            }
            LoweringError::NoSafeByteRegister { node_index } => write!(
                f,
                "node {node_index} needs one of RAX/RCX/RDX/RBX for safe no-REX SETcc materialization",
            ),
            LoweringError::RegisterPressure {
                node_index,
                live_temporaries,
            } => write!(
                f,
                "node {node_index} needs another register while {live_temporaries} temporaries are live",
            ),
            LoweringError::StructuredPath { path, reason } => write!(f, "{path}: {reason}"),
            LoweringError::InvalidStructuredRegion(message) => {
                write!(f, "invalid structured region: {message}")
            }
            LoweringError::UnsupportedStructuredRegion => write!(
                f,
                "the first x86 conditional lowering requires two dataflow leaves",
            ),
            LoweringError::MissingConditionPlacement(condition) => write!(
                f,
                "conditional value {condition} has no input register placement",
            ),
            LoweringError::UnsupportedSequenceInterface => write!(
                f,
                "the first prefixed conditional lowering requires one one-bit prefix output and branch arguments inherited from prefix inputs",
            ),
            LoweringError::UnsupportedJoinArm => write!(
                f,
                "the first block-argument lowering requires dataflow-free join arms",
            ),
            LoweringError::JoinPlacementCount { parameters, registers } => write!(
                f,
                "join has {parameters} parameters but {registers} join registers were supplied",
            ),
            LoweringError::ParallelCopyNeedsTemporary => write!(
                f,
                "join edge contains a register cycle and needs a parallel-copy temporary",
            ),
            LoweringError::ShortBranchOutOfRange { bytes } => write!(
                f,
                "linked conditional needs a {bytes}-byte forward displacement, beyond rel8 range",
            ),
        }
    }
}

/// Lower the first genuine block-argument diamond.  The prefix computes the
/// selector, each edge performs a parallel value transfer into one common
/// register interface, and the continuation is selected exactly once.
pub fn lower_control_region(
    region: &ControlRegion,
    input_registers: &[Gpr],
    condition_register: Gpr,
    join_registers: &[Gpr],
    continuation_temporaries: &[Gpr],
    requested_output: Gpr,
) -> Result<LoweredControlRegion, LoweringError> {
    cert::validate_control_region(region).map_err(LoweringError::InvalidStructuredRegion)?;
    if region.inputs().len() != input_registers.len() {
        return Err(LoweringError::InputPlacementCount {
            inputs: region.inputs().len(),
            registers: input_registers.len(),
        });
    }
    if region.join.when_true.nodes.len() != 0 || region.join.when_false.nodes.len() != 0 {
        return Err(LoweringError::UnsupportedJoinArm);
    }
    if region.join.true_arguments.len() != join_registers.len() {
        return Err(LoweringError::JoinPlacementCount {
            parameters: region.join.true_arguments.len(),
            registers: join_registers.len(),
        });
    }

    let prefix = lower_dag(
        &region.prefix,
        input_registers,
        &[condition_register],
        condition_register,
    )?;
    if region.prefix.outputs[0].id != region.join.condition || region.prefix.outputs[0].width != 1 {
        return Err(LoweringError::UnsupportedSequenceInterface);
    }

    let mut available = region
        .prefix
        .inputs
        .iter()
        .zip(input_registers)
        .map(|(port, register)| (port.id, *register))
        .collect::<BTreeMap<_, _>>();
    available.insert(region.join.condition, condition_register);
    let true_transfer =
        lower_edge_transfer(&region.join.true_arguments, join_registers, &available)?;
    let false_transfer =
        lower_edge_transfer(&region.join.false_arguments, join_registers, &available)?;
    let continuation = lower_dag(
        &region.join.continuation,
        join_registers,
        continuation_temporaries,
        requested_output,
    )?;
    Ok(LoweredControlRegion {
        prefix,
        condition_register,
        when_true_transfer: true_transfer,
        when_false_transfer: false_transfer,
        join_registers: join_registers.to_vec(),
        continuation,
    })
}

fn lower_edge_transfer(
    arguments: &[BlockArgument],
    destinations: &[Gpr],
    available: &BTreeMap<u64, Gpr>,
) -> Result<Vec<Instruction>, LoweringError> {
    let mut pending = arguments
        .iter()
        .zip(destinations)
        .map(|(argument, destination)| {
            let source = available
                .get(&argument.value)
                .copied()
                .ok_or(LoweringError::UndefinedValue(argument.value))?;
            Ok((*destination, source))
        })
        .collect::<Result<Vec<_>, LoweringError>>()?;
    pending.retain(|(destination, source)| destination != source);
    let mut instructions = Vec::with_capacity(pending.len());
    while !pending.is_empty() {
        let Some(index) = pending
            .iter()
            .position(|(destination, _)| !pending.iter().any(|(_, source)| source == destination))
        else {
            return Err(LoweringError::ParallelCopyNeedsTemporary);
        };
        let (destination, source) = pending.remove(index);
        instructions.push(Instruction::MovRR {
            destination,
            source,
        });
    }
    Ok(instructions)
}

/// Lower the first structured control-flow slice. Each successor is selected
/// and allocated independently from the same explicit branch interface; only
/// the selected leaf will execute at the machine boundary.
pub fn lower_conditional(
    region: &StructuredRegion,
    input_registers: &[Gpr],
    temporary_registers: &[Gpr],
    requested_output: Gpr,
) -> Result<LoweredConditional, LoweringError> {
    cert::validate_structured_region(region).map_err(LoweringError::InvalidStructuredRegion)?;
    let StructuredRegion::Conditional {
        inputs,
        condition,
        arguments,
        when_true,
        when_false,
        ..
    } = region
    else {
        return Err(LoweringError::UnsupportedStructuredRegion);
    };
    if inputs.len() != input_registers.len() {
        return Err(LoweringError::InputPlacementCount {
            inputs: inputs.len(),
            registers: input_registers.len(),
        });
    }
    let placements = inputs
        .iter()
        .zip(input_registers)
        .map(|(port, register)| (port.id, *register))
        .collect::<BTreeMap<_, _>>();
    let condition_register = placements
        .get(condition)
        .copied()
        .ok_or(LoweringError::MissingConditionPlacement(*condition))?;
    let argument_registers = arguments
        .iter()
        .map(|port| {
            placements
                .get(&port.id)
                .copied()
                .ok_or(LoweringError::UndefinedValue(port.id))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let (StructuredRegion::Dataflow(when_true), StructuredRegion::Dataflow(when_false)) =
        (&**when_true, &**when_false)
    else {
        return Err(LoweringError::UnsupportedStructuredRegion);
    };
    Ok(LoweredConditional {
        condition_id: *condition,
        condition_register,
        when_true: lower_dag(
            when_true,
            &argument_registers,
            temporary_registers,
            requested_output,
        )?,
        when_false: lower_dag(
            when_false,
            &argument_registers,
            temporary_registers,
            requested_output,
        )?,
    })
}

/// Render the checked leaves plus their structured machine selector and join.
/// Branch-transfer byte placement remains a linker obligation; both leaf byte
/// streams and the state-dependent selected execution are checked here.
#[allow(clippy::too_many_arguments)]
pub fn generate_conditional(
    prefix: &str,
    structured_region_expr: &str,
    true_region_expr: &str,
    false_region_expr: &str,
    region: &StructuredRegion,
    input_registers: &[Gpr],
    temporary_registers: &[Gpr],
    requested_output: Gpr,
) -> Result<ConditionalX86Emission, LoweringError> {
    let lowered = lower_conditional(
        region,
        input_registers,
        temporary_registers,
        requested_output,
    )?;
    let StructuredRegion::Conditional {
        inputs,
        condition,
        arguments,
        when_true,
        when_false,
        ..
    } = region
    else {
        unreachable!("lower_conditional accepted only Conditional")
    };
    let (StructuredRegion::Dataflow(true_region), StructuredRegion::Dataflow(false_region)) =
        (&**when_true, &**when_false)
    else {
        unreachable!("lower_conditional accepted only dataflow leaves")
    };
    let placements = inputs
        .iter()
        .zip(input_registers)
        .map(|(port, register)| (port.id, *register))
        .collect::<BTreeMap<_, _>>();
    let argument_registers = arguments
        .iter()
        .map(|port| placements[&port.id])
        .collect::<Vec<_>>();
    let true_prefix = format!("{prefix}_true");
    let false_prefix = format!("{prefix}_false");
    let true_emission = generate(
        &true_prefix,
        true_region_expr,
        true_region,
        &argument_registers,
        temporary_registers,
        requested_output,
    )?;
    let false_emission = generate(
        &false_prefix,
        false_region_expr,
        false_region,
        &argument_registers,
        temporary_registers,
        requested_output,
    )?;
    let condition_register = lowered.condition_register.heather_name();
    let output_id = true_region.outputs[0].id;
    let mut public_parameters = vec![
        "values: Valuation()".to_string(),
        "before: MachineState<M>".to_string(),
    ];
    let mut branch_arguments = Vec::new();
    for (index, port) in arguments.iter().enumerate() {
        let register = argument_registers[index].heather_name();
        public_parameters.push(format!(
            "argument_{index}_placed: ValuePlaced(values, {}, {register}, before)",
            port.id,
        ));
        branch_arguments.push(format!("argument_{index}_placed"));
    }
    public_parameters.push(format!(
        "condition_placed: BitValuePlaced(values, {condition}, {condition_register}, before)",
    ));
    public_parameters.push(format!(
        "graph: StructuredRegionHolds(values, {structured_region_expr})",
    ));
    let branch_arguments = if branch_arguments.is_empty() {
        String::new()
    } else {
        format!(", {}", branch_arguments.join(", "))
    };
    let control_name = format!("{prefix}_control");
    let after_name = format!("{prefix}_after");
    let mut text = true_emission.text;
    text.push('\n');
    text.push_str(&false_emission.text);
    text.push_str(&format!(
        "\n\nfn {control_name}() → ConditionalBlock {{\n\
         \x20   ConditionalBlock(condition_register := {condition_register},\n\
         \x20       when_true := {true_prefix}_instructions(),\n\
         \x20       when_false := {false_prefix}_instructions())\n\
         }}\n\n\
         fn {after_name}<M>(before: MachineState<M>) → MachineState<M> {{\n\
         \x20   conditional_block_after({control_name}(), before,\n\
         \x20       {true_prefix}_after(before), {false_prefix}_after(before))\n\
         }}\n\n\
         theorem {prefix}_control_is_allowed<M>(before: MachineState<M>):\n\
         \x20   ExecuteConditionalBlock({control_name}(), before, {after_name}(before))\n\
         {{\n\
         \x20   execute_conditional_selected({control_name}(), before,\n\
         \x20       {true_prefix}_after(before), {false_prefix}_after(before),\n\
         \x20       {true_prefix}_block_is_allowed(before),\n\
         \x20       {false_prefix}_block_is_allowed(before))\n\
         }}\n\n\
         theorem {prefix}_refines_function_ir<M>({}):\n\
         \x20   read_gpr({}, {after_name}(before).gprs) = values(64, {output_id})\n\
         {{\n\
         \x20   j(sym(bit_value_placed_condition(values, {condition},\n\
         \x20           {condition_register}, before, condition_placed)),\n\
         \x20       λ selected _ => read_gpr({}, selected_block_after(selected,\n\
         \x20           {true_prefix}_after(before),\n\
         \x20           {false_prefix}_after(before)).gprs) = values(64, {output_id}),\n\
         \x20       (match @bitvec::BitVec::head_bit(0, values(1, {condition})) as λ selected =>\n\
         \x20           (match selected {{\n\
         \x20               False => RegionHolds({false_region_expr}, values),\n\
         \x20               True => RegionHolds({true_region_expr}, values),\n\
         \x20           }}) → read_gpr({}, selected_block_after(selected,\n\
         \x20               {true_prefix}_after(before),\n\
         \x20               {false_prefix}_after(before)).gprs) = values(64, {output_id})\n\
         \x20       {{\n\
         \x20           False => selected_graph ⊢ {false_prefix}_refines_function_ir(\n\
         \x20               values, before{branch_arguments}, selected_graph),\n\
         \x20           True => selected_graph ⊢ {true_prefix}_refines_function_ir(\n\
         \x20               values, before{branch_arguments}, selected_graph),\n\
         \x20       }})(graph))\n\
         }}\n",
        public_parameters.join(",\n    "),
        requested_output.heather_name(),
        requested_output.heather_name(),
        requested_output.heather_name(),
    ));
    Ok(ConditionalX86Emission { lowered, text })
}

/// Generate a comparison-producing straight-line prefix followed by the first
/// structured conditional. The comparison result is placed by the prefix,
/// while inherited 64-bit arguments are carried across using its frame proof.
#[allow(clippy::too_many_arguments)]
pub fn generate_prefixed_conditional(
    prefix: &str,
    structured_region_expr: &str,
    prefix_region_expr: &str,
    conditional_region_expr: &str,
    true_region_expr: &str,
    false_region_expr: &str,
    region: &StructuredRegion,
    input_registers: &[Gpr],
    condition_register: Gpr,
    branch_temporary_registers: &[Gpr],
    requested_output: Gpr,
) -> Result<PrefixedConditionalX86Emission, LoweringError> {
    cert::validate_structured_region(region).map_err(LoweringError::InvalidStructuredRegion)?;
    let StructuredRegion::Sequence {
        prefix: prefix_region,
        continuation,
    } = region
    else {
        return Err(LoweringError::UnsupportedStructuredRegion);
    };
    let StructuredRegion::Conditional {
        condition,
        arguments,
        outputs,
        ..
    } = &**continuation
    else {
        return Err(LoweringError::UnsupportedStructuredRegion);
    };
    if prefix_region.inputs.len() != input_registers.len() {
        return Err(LoweringError::InputPlacementCount {
            inputs: prefix_region.inputs.len(),
            registers: input_registers.len(),
        });
    }
    if prefix_region.outputs.len() != 1
        || prefix_region.outputs[0].id != *condition
        || prefix_region.outputs[0].width != 1
        || outputs.len() != 1
        || outputs[0].width != 64
        || arguments
            .iter()
            .any(|argument| !prefix_region.inputs.contains(argument))
    {
        return Err(LoweringError::UnsupportedSequenceInterface);
    }
    let input_placements = prefix_region
        .inputs
        .iter()
        .zip(input_registers)
        .map(|(port, register)| (port.id, *register))
        .collect::<BTreeMap<_, _>>();
    let conditional_inputs = continuation
        .inputs()
        .iter()
        .map(|port| {
            if port.id == *condition && port.width == 1 {
                Ok(condition_register)
            } else {
                input_placements
                    .get(&port.id)
                    .copied()
                    .ok_or(LoweringError::UnsupportedSequenceInterface)
            }
        })
        .collect::<Result<Vec<_>, _>>()?;
    let prefix_name = format!("{prefix}_prefix");
    let continuation_name = format!("{prefix}_continuation");
    let prefix_emission = generate(
        &prefix_name,
        prefix_region_expr,
        prefix_region,
        input_registers,
        &[condition_register],
        condition_register,
    )?;
    let continuation_emission = generate_conditional(
        &continuation_name,
        conditional_region_expr,
        true_region_expr,
        false_region_expr,
        continuation,
        &conditional_inputs,
        branch_temporary_registers,
        requested_output,
    )?;
    let true_bytes = continuation_emission
        .lowered
        .when_true
        .instructions
        .iter()
        .map(|instruction| instruction.canonical_length())
        .sum::<usize>();
    let false_bytes = continuation_emission
        .lowered
        .when_false
        .instructions
        .iter()
        .map(|instruction| instruction.canonical_length())
        .sum::<usize>();
    let false_displacement = true_bytes + 2;
    let join_displacement = false_bytes;
    for bytes in [false_displacement, join_displacement] {
        if bytes > i8::MAX as usize {
            return Err(LoweringError::ShortBranchOutOfRange { bytes });
        }
    }
    let input_indices = prefix_region
        .inputs
        .iter()
        .enumerate()
        .map(|(index, port)| (port.id, index))
        .collect::<BTreeMap<_, _>>();
    let mut public_parameters = vec![
        "values: Valuation()".to_string(),
        "before: MachineState<M>".to_string(),
    ];
    let mut prefix_arguments = Vec::new();
    for (index, (port, register)) in prefix_region.inputs.iter().zip(input_registers).enumerate() {
        public_parameters.push(format!(
            "input_{index}_placed: ValuePlaced(values, {}, {}, before)",
            port.id,
            register.heather_name(),
        ));
        prefix_arguments.push(format!("input_{index}_placed"));
    }
    public_parameters.push(format!(
        "graph: StructuredRegionHolds(values, {structured_region_expr})",
    ));
    let public_parameters_rendered = public_parameters.join(",\n    ");
    let prefix_arguments = if prefix_arguments.is_empty() {
        String::new()
    } else {
        format!(", {}", prefix_arguments.join(", "))
    };
    let carried_arguments = arguments
        .iter()
        .map(|argument| {
            let index = input_indices[&argument.id];
            let register = input_registers[index];
            format!(
                "placed_after_frame(values, {}, {}, before, {prefix_name}_after(before), input_{index}_placed, {prefix_name}_preserves_protected({}, before, trivial))",
                argument.id,
                register.heather_name(),
                register.heather_name(),
            )
        })
        .collect::<Vec<_>>();
    let carried_arguments = if carried_arguments.is_empty() {
        String::new()
    } else {
        format!(", {}", carried_arguments.join(", "))
    };
    let control_name = format!("{prefix}_block");
    let after_name = format!("{prefix}_after");
    let continuation_control = format!("{continuation_name}_control");
    let continuation_after = format!("{continuation_name}_after");
    let linked_name = format!("{prefix}_linked");
    let true_name = format!("{continuation_name}_true");
    let false_name = format!("{continuation_name}_false");
    let linked_byte_length = prefix_emission
        .lowered
        .instructions
        .iter()
        .map(|instruction| instruction.canonical_length())
        .sum::<usize>()
        + 3
        + 2
        + true_bytes
        + 2
        + false_bytes;
    let prefix_span_proof = render_block_span_proof(&prefix_emission.lowered.instructions);
    let true_span_proof =
        render_block_span_proof(&continuation_emission.lowered.when_true.instructions);
    let false_span_proof =
        render_block_span_proof(&continuation_emission.lowered.when_false.instructions);
    let mut text = prefix_emission.text;
    text.push('\n');
    text.push_str(&continuation_emission.text);
    text.push_str(&format!(
        "\n\nfn {control_name}() → PrefixedConditionalBlock {{\n\
         \x20   PrefixedConditionalBlock(\n\
         \x20       prefix := {prefix_name}_instructions(),\n\
         \x20       continuation := {continuation_control}())\n\
         }}\n\n\
         fn {after_name}<M>(before: MachineState<M>) → MachineState<M> {{\n\
         \x20   {continuation_after}({prefix_name}_after(before))\n\
         }}\n\n\
         theorem {prefix}_control_is_allowed<M>(before: MachineState<M>):\n\
         \x20   ExecutePrefixedConditionalBlock({control_name}(), before,\n\
         \x20       {after_name}(before))\n\
         {{\n\
         \x20   execute_prefixed_conditional({control_name}(), before,\n\
         \x20       {prefix_name}_after(before), {after_name}(before),\n\
         \x20       {prefix_name}_block_is_allowed(before),\n\
         \x20       {continuation_name}_control_is_allowed(\n\
         \x20           {prefix_name}_after(before)))\n\
         }}\n\n\
         theorem {prefix}_refines_function_ir<M>({}):\n\
         \x20   read_gpr({}, {after_name}(before).gprs) = values(64, {})\n\
         {{\n\
         \x20   {continuation_name}_refines_function_ir(values,\n\
         \x20       {prefix_name}_after(before){carried_arguments},\n\
         \x20       sym({prefix_name}_refines_function_ir(\n\
         \x20           values, before{prefix_arguments}, graph.left)), graph.right)\n\
         }}\n\n\
         fn {linked_name}_block() → LinkedConditionalBlock {{\n\
         \x20   LinkedConditionalBlock(\n\
         \x20       prefix := {prefix_name}_instructions(),\n\
         \x20       test_register := {},\n\
         \x20       false_displacement := @bitvec::BitVec::ofNat(8, {false_displacement}),\n\
         \x20       when_true := {true_name}_instructions(),\n\
         \x20       join_displacement := @bitvec::BitVec::ofNat(8, {join_displacement}),\n\
         \x20       when_false := {false_name}_instructions())\n\
         }}\n\n\
         fn {linked_name}_bytes() → List<BitVec(8)> {{\n\
         \x20   linked_conditional_bytes({linked_name}_block())\n\
         }}\n\n\
         theorem {linked_name}_byte_length():\n\
         \x20   {linked_name}_bytes().len() = {linked_byte_length}\n\
         {{ refl }}\n\n\
         theorem {linked_name}_decodes(start: BitVec(64)):\n\
         \x20   LinkedConditionalDecodes({linked_name}_block(), start)\n\
         {{\n\
         \x20   LinkedConditionalDecodes(\n\
         \x20     prefix_decoding := canonical_block_decodes(\n\
         \x20       {prefix_name}_instructions(), start),\n\
         \x20     test_decoding := canonical_encoding_decodes(\n\
         \x20       linked_test_start({linked_name}_block(), start), TestRR({}, {})),\n\
         \x20     branch_decoding := decode_short_control_complete(JumpZero(\n\
         \x20           @bitvec::BitVec::ofNat(8, {false_displacement}))),\n\
         \x20     true_decoding := canonical_block_decodes({true_name}_instructions(),\n\
         \x20           linked_true_start({linked_name}_block(), start)),\n\
         \x20     join_decoding := decode_short_control_complete(Jump(\n\
         \x20             @bitvec::BitVec::ofNat(8, {join_displacement}))),\n\
         \x20     false_decoding := canonical_block_decodes(\n\
         \x20       {false_name}_instructions(),\n\
         \x20       linked_false_start({linked_name}_block(), start)))\n\
         }}\n\n\
         theorem {linked_name}_false_span(start: BitVec(64)):\n\
         \x20   short_branch_target(start, @bitvec::BitVec::ofNat(8, {false_displacement})) =\n\
         \x20   @bitvec::BitVec::iterate_increment(64, next_rip(start, 2),\n\
         \x20     {false_displacement})\n\
         {{ sym(bitvec::BitVec::iter_add_eq_add(64, next_rip(start, 2),\n\
         \x20     @bitvec::BitVec::sign_extend(7, 56, @bitvec::BitVec::ofNat(8, {false_displacement})))) }}\n\n\
         theorem {linked_name}_join_span(start: BitVec(64)):\n\
         \x20   short_branch_target(start, @bitvec::BitVec::ofNat(8, {join_displacement})) =\n\
         \x20   @bitvec::BitVec::iterate_increment(64, next_rip(start, 2),\n\
         \x20     {join_displacement})\n\
         {{ sym(bitvec::BitVec::iter_add_eq_add(64, next_rip(start, 2),\n\
         \x20     @bitvec::BitVec::sign_extend(7, 56, @bitvec::BitVec::ofNat(8, {join_displacement})))) }}\n\n\
         theorem {linked_name}_prefix_span(start: BitVec(64)):\n\
         \x20   {prefix_name}_final_rip(start) =\n\
         \x20     after_canonical_block(start, {prefix_name}_instructions())\n\
         {{ {prefix_span_proof} }}\n\n\
         theorem {linked_name}_true_block_span(start: BitVec(64)):\n\
         \x20   {true_name}_final_rip(start) =\n\
         \x20     after_canonical_block(start, {true_name}_instructions())\n\
         {{ {true_span_proof} }}\n\n\
         theorem {linked_name}_false_block_span(start: BitVec(64)):\n\
         \x20   {false_name}_final_rip(start) =\n\
         \x20     after_canonical_block(start, {false_name}_instructions())\n\
         {{ {false_span_proof} }}\n\n\
         theorem {linked_name}_false_target(start: BitVec(64)):\n\
         \x20   short_branch_target(linked_branch_start(\n\
         \x20     {linked_name}_block(), start), @bitvec::BitVec::ofNat(8, {false_displacement})) =\n\
         \x20   linked_false_start({linked_name}_block(), start)\n\
         {{\n\
         \x20   calc {{\n\
         \x20     short_branch_target(linked_branch_start(\n\
         \x20       {linked_name}_block(), start),\n\
         \x20       @bitvec::BitVec::ofNat(8, {false_displacement}))\n\
         \x20       = @bitvec::BitVec::iterate_increment(64,\n\
         \x20           linked_true_start({linked_name}_block(), start),\n\
         \x20           {false_displacement}) := {linked_name}_false_span(\n\
         \x20             linked_branch_start({linked_name}_block(), start)),\n\
         \x20       = linked_false_start({linked_name}_block(), start) :=\n\
         \x20             sym(bitvec::BitVec::iterate_increment_compose(64,\n\
         \x20               linked_true_start({linked_name}_block(), start),\n\
         \x20               {true_bytes}, 2)),\n\
         \x20   }}\n\
         }}\n\n\
         theorem {linked_name}_join_target(start: BitVec(64)):\n\
         \x20   short_branch_target(linked_join_jump_start(\n\
         \x20     {linked_name}_block(), start), @bitvec::BitVec::ofNat(8, {join_displacement})) =\n\
         \x20   linked_join_start({linked_name}_block(), start)\n\
         {{\n\
         \x20   trans({linked_name}_join_span(\n\
         \x20       linked_join_jump_start({linked_name}_block(), start)),\n\
         \x20     refl)\n\
         }}\n\n\
         theorem {linked_name}_layout():\n\
         \x20   LinkedConditionalLayout({linked_name}_block())\n\
         {{\n\
         \x20   LinkedConditionalLayout(\n\
         \x20     false_forward := refl,\n\
         \x20     false_distance := refl,\n\
         \x20     join_forward := refl,\n\
         \x20     join_distance := refl,\n\
         \x20     false_target := {linked_name}_false_target,\n\
         \x20     join_target := {linked_name}_join_target)\n\
         }}\n\n\
         theorem {linked_name}_executes<M>(before: MachineState<M>):\n\
         \x20   ExecuteLinkedConditionalBlock({linked_name}_block(), before,\n\
         \x20       linked_conditional_after({linked_name}_block(), before))\n\
         {{ canonical_linked_conditional_executes({linked_name}_block(), before) }}\n\n\
         theorem {linked_name}_prefix_at<M>(before: MachineState<M>):\n\
         \x20   linked_prefix_after({linked_name}_block(), before).rip =\n\
         \x20     linked_test_start({linked_name}_block(), before.rip)\n\
         {{\n\
         \x20   trans({prefix_name}_advances_rip(before),\n\
         \x20     {linked_name}_prefix_span(before.rip))\n\
         }}\n\n\
         theorem {linked_name}_true_at<M>(before: MachineState<M>):\n\
         \x20   linked_true_after({linked_name}_block(), before).rip =\n\
         \x20     after_canonical_block(\n\
         \x20       linked_branch_after({linked_name}_block(), before).rip,\n\
         \x20       {true_name}_instructions())\n\
         {{\n\
         \x20   trans({true_name}_advances_rip(\n\
         \x20       linked_branch_after({linked_name}_block(), before)),\n\
         \x20     {linked_name}_true_block_span(\n\
         \x20       linked_branch_after({linked_name}_block(), before).rip))\n\
         }}\n\n\
         theorem {linked_name}_false_at<M>(before: MachineState<M>):\n\
         \x20   linked_false_after({linked_name}_block(), before).rip =\n\
         \x20     after_canonical_block(\n\
         \x20       linked_branch_after({linked_name}_block(), before).rip,\n\
         \x20       {false_name}_instructions())\n\
         {{\n\
         \x20   trans({false_name}_advances_rip(\n\
         \x20       linked_branch_after({linked_name}_block(), before)),\n\
         \x20     {linked_name}_false_block_span(\n\
         \x20       linked_branch_after({linked_name}_block(), before).rip))\n\
         }}\n\n\
         theorem {linked_name}_not_taken_at<M>(before: MachineState<M>,\n\
         \x20   selected: linked_test_after(\n\
         \x20     {linked_name}_block(), before).flags.zf = False):\n\
         \x20   linked_branch_after({linked_name}_block(), before).rip =\n\
         \x20     linked_true_start({linked_name}_block(), before.rip)\n\
         {{\n\
         \x20   trans(jump_zero_not_taken_rip(\n\
         \x20       linked_test_after({linked_name}_block(), before).flags.zf,\n\
         \x20       linked_test_after({linked_name}_block(), before).rip,\n\
         \x20       {linked_name}_block().false_displacement, selected),\n\
         \x20     bitvec::BitVec::cong_iterate_increment(64, 2,\n\
         \x20       linked_test_reaches_branch_start(\n\
         \x20         {linked_name}_block(), before,\n\
         \x20         {linked_name}_prefix_at(before))))\n\
         }}\n\n\
         theorem {linked_name}_taken_at<M>(before: MachineState<M>,\n\
         \x20   selected: linked_test_after(\n\
         \x20     {linked_name}_block(), before).flags.zf = True):\n\
         \x20   linked_branch_after({linked_name}_block(), before).rip =\n\
         \x20     linked_false_start({linked_name}_block(), before.rip)\n\
         {{\n\
         \x20   trans(jump_zero_taken_rip(\n\
         \x20       linked_test_after({linked_name}_block(), before).flags.zf,\n\
         \x20       linked_test_after({linked_name}_block(), before).rip,\n\
         \x20       {linked_name}_block().false_displacement, selected),\n\
         \x20     trans(cong_fn<BitVec(64), BitVec(64)>(\n\
         \x20         λ rip => short_branch_target(rip,\n\
         \x20           {linked_name}_block().false_displacement),\n\
         \x20         linked_test_reaches_branch_start(\n\
         \x20           {linked_name}_block(), before,\n\
         \x20           {linked_name}_prefix_at(before))),\n\
         \x20       {linked_name}_layout().false_target(before.rip)))\n\
         }}\n\n\
         theorem {linked_name}_true_reaches_join<M>(before: MachineState<M>,\n\
         \x20   selected: linked_test_after(\n\
         \x20     {linked_name}_block(), before).flags.zf = False):\n\
         \x20   linked_true_jump_after({linked_name}_block(), before).rip =\n\
         \x20     linked_join_start({linked_name}_block(), before.rip)\n\
         {{\n\
         \x20   calc {{\n\
         \x20     linked_true_jump_after({linked_name}_block(), before).rip\n\
         \x20       = short_branch_target(\n\
         \x20           linked_true_after({linked_name}_block(), before).rip,\n\
         \x20           {linked_name}_block().join_displacement) := refl,\n\
         \x20       = short_branch_target(linked_join_jump_start(\n\
         \x20           {linked_name}_block(), before.rip),\n\
         \x20           {linked_name}_block().join_displacement) :=\n\
         \x20           cong_fn<BitVec(64), BitVec(64)>(\n\
         \x20             λ rip => short_branch_target(rip,\n\
         \x20               {linked_name}_block().join_displacement),\n\
         \x20             trans({linked_name}_true_at(before),\n\
         \x20               cong_fn<BitVec(64), BitVec(64)>(\n\
         \x20                 λ rip => after_canonical_block(rip,\n\
         \x20                   {true_name}_instructions()),\n\
         \x20                 {linked_name}_not_taken_at(before, selected)))),\n\
         \x20       = linked_join_start({linked_name}_block(), before.rip) :=\n\
         \x20           {linked_name}_layout().join_target(before.rip),\n\
         \x20   }}\n\
         }}\n\n\
         theorem {linked_name}_false_reaches_join<M>(before: MachineState<M>,\n\
         \x20   selected: linked_test_after(\n\
         \x20     {linked_name}_block(), before).flags.zf = True):\n\
         \x20   linked_false_after({linked_name}_block(), before).rip =\n\
         \x20     linked_join_start({linked_name}_block(), before.rip)\n\
         {{\n\
         \x20   calc {{\n\
         \x20     linked_false_after({linked_name}_block(), before).rip\n\
         \x20       = after_canonical_block(linked_branch_after(\n\
         \x20           {linked_name}_block(), before).rip,\n\
         \x20           {false_name}_instructions()) :=\n\
         \x20           {linked_name}_false_at(before),\n\
         \x20       = after_canonical_block(linked_false_start(\n\
         \x20           {linked_name}_block(), before.rip),\n\
         \x20           {false_name}_instructions()) :=\n\
         \x20           cong_fn<BitVec(64), BitVec(64)>(\n\
         \x20             λ rip => after_canonical_block(rip,\n\
         \x20               {false_name}_instructions()),\n\
         \x20             {linked_name}_taken_at(before, selected)),\n\
         \x20       = linked_join_start({linked_name}_block(), before.rip) := refl,\n\
         \x20   }}\n\
         }}\n\n\
         theorem {linked_name}_reaches_join<M>(before: MachineState<M>):\n\
         \x20   linked_conditional_after({linked_name}_block(), before).rip =\n\
         \x20     linked_join_start({linked_name}_block(), before.rip)\n\
         {{\n\
         \x20   trans(linked_conditional_rip({linked_name}_block(), before),\n\
         \x20     selected_rip_reaches(\n\
         \x20       linked_test_after({linked_name}_block(), before).flags.zf,\n\
         \x20       linked_true_jump_after({linked_name}_block(), before).rip,\n\
         \x20       linked_false_after({linked_name}_block(), before).rip,\n\
         \x20       linked_join_start({linked_name}_block(), before.rip),\n\
         \x20       λ selected => {linked_name}_true_reaches_join(before, selected),\n\
         \x20       λ selected => {linked_name}_false_reaches_join(before, selected)))\n\
         }}\n",
        public_parameters.join(",\n    "),
        requested_output.heather_name(),
        outputs[0].id,
        condition_register.heather_name(),
        condition_register.heather_name(),
        condition_register.heather_name(),
    ));
    if continuation_emission
        .lowered
        .when_true
        .instructions
        .iter()
        .copied()
        .all(|instruction| render_gpr_only_step(instruction).is_some())
        && continuation_emission
            .lowered
            .when_false
            .instructions
            .iter()
            .copied()
            .all(|instruction| render_gpr_only_step(instruction).is_some())
    {
        text.push_str(&format!(
            "\n\ntheorem {linked_name}_condition_placed<M>({public_parameters_rendered}):\n\
             \x20   BitValuePlaced(values, {condition}, {},\n\
             \x20     linked_prefix_after({linked_name}_block(), before))\n\
             {{\n\
             \x20   sym({prefix_name}_refines_function_ir(\n\
             \x20     values, before{prefix_arguments}, graph.left))\n\
             }}\n\n\
             theorem {linked_name}_test_selects<M>({public_parameters_rendered}):\n\
             \x20   linked_test_after({linked_name}_block(), before).flags.zf =\n\
             \x20     zero_test_selector(@bitvec::BitVec::head_bit(0, values(1, {condition})))\n\
             {{\n\
             \x20   linked_test_bit_value_placed_zf(values, {condition},\n\
             \x20     {linked_name}_block(), before,\n\
             \x20     {linked_name}_condition_placed(\n\
             \x20       values, before{prefix_arguments}, graph))\n\
             }}\n\n\
             theorem {linked_name}_condition_matches<M>({public_parameters_rendered}):\n\
             \x20   machine_condition({}, {prefix_name}_after(before)) =\n\
             \x20     @bitvec::BitVec::head_bit(0, values(1, {condition}))\n\
             {{\n\
             \x20   bit_value_placed_condition(values, {condition}, {},\n\
             \x20     {prefix_name}_after(before),\n\
             \x20     sym({prefix_name}_refines_function_ir(\n\
             \x20       values, before{prefix_arguments}, graph.left)))\n\
             }}\n\n\
             theorem {linked_name}_false_path_agrees<M>(before: MachineState<M>):\n\
             \x20   read_gpr({}, linked_false_after(\n\
             \x20       {linked_name}_block(), before).gprs) = read_gpr({},\n\
             \x20       {false_name}_after({prefix_name}_after(before)).gprs)\n\
             {{\n\
             \x20   cong_fn<Gprs, BitVec(64)>(\n\
             \x20     read_gpr({}, ·),\n\
             \x20     {false_name}_gprs_congruent(\n\
             \x20       linked_branch_after({linked_name}_block(), before),\n\
             \x20       {prefix_name}_after(before),\n\
             \x20       linked_branch_preserves_prefix_gprs(\n\
             \x20         {linked_name}_block(), before)))\n\
             }}\n\n\
             theorem {linked_name}_true_path_agrees<M>(before: MachineState<M>):\n\
             \x20   read_gpr({}, linked_true_jump_after(\n\
             \x20       {linked_name}_block(), before).gprs) = read_gpr({},\n\
             \x20       {true_name}_after({prefix_name}_after(before)).gprs)\n\
             {{\n\
             \x20   cong_fn<Gprs, BitVec(64)>(read_gpr({}, ·), trans(\n\
             \x20     execute_short_control_preserves_gprs(Jump(\n\
             \x20       {linked_name}_block().join_displacement),\n\
             \x20       linked_true_after({linked_name}_block(), before)),\n\
             \x20     {true_name}_gprs_congruent(\n\
             \x20       linked_branch_after({linked_name}_block(), before),\n\
             \x20       {prefix_name}_after(before),\n\
             \x20       linked_branch_preserves_prefix_gprs(\n\
             \x20         {linked_name}_block(), before))))\n\
             }}\n\n\
             theorem {linked_name}_agrees_with_structured<M>({public_parameters_rendered}):\n\
             \x20   read_gpr({}, linked_conditional_after(\n\
             \x20       {linked_name}_block(), before).gprs) =\n\
             \x20     read_gpr({}, {after_name}(before).gprs)\n\
             {{\n\
             \x20   linked_conditional_read_agrees(\n\
             \x20     @bitvec::BitVec::head_bit(0, values(1, {condition})), {},\n\
             \x20     {linked_name}_block(), before, {continuation_control}(),\n\
             \x20     {prefix_name}_after(before),\n\
             \x20     {true_name}_after({prefix_name}_after(before)),\n\
             \x20     {false_name}_after({prefix_name}_after(before)),\n\
             \x20     {linked_name}_test_selects(\n\
             \x20       values, before{prefix_arguments}, graph),\n\
             \x20     {linked_name}_condition_matches(\n\
             \x20       values, before{prefix_arguments}, graph),\n\
             \x20     {linked_name}_false_path_agrees(before),\n\
             \x20     {linked_name}_true_path_agrees(before))\n\
             }}\n\n\
             theorem {linked_name}_refines_function_ir<M>({public_parameters_rendered}):\n\
             \x20   read_gpr({}, linked_conditional_after(\n\
             \x20       {linked_name}_block(), before).gprs) = values(64, {})\n\
             {{\n\
             \x20   trans({linked_name}_agrees_with_structured(\n\
             \x20       values, before{prefix_arguments}, graph),\n\
             \x20     {prefix}_refines_function_ir(\n\
             \x20       values, before{prefix_arguments}, graph))\n\
             }}\n",
            condition_register.heather_name(),
            condition_register.heather_name(),
            condition_register.heather_name(),
            requested_output.heather_name(),
            requested_output.heather_name(),
            requested_output.heather_name(),
            requested_output.heather_name(),
            requested_output.heather_name(),
            requested_output.heather_name(),
            requested_output.heather_name(),
            requested_output.heather_name(),
            requested_output.heather_name(),
            requested_output.heather_name(),
            outputs[0].id,
        ));
    }
    Ok(PrefixedConditionalX86Emission {
        prefix: prefix_emission.lowered,
        continuation: continuation_emission.lowered,
        text,
    })
}

/// Generate one complete checked x86 artifact for the current four-block
/// `ControlRegion`: comparison prefix, selected edge transfer, physical join,
/// and one shared straight-line continuation.
///
/// This first certificate slice deliberately accepts the useful two-argument
/// shape exercised by `max_plus`: the first parameter is copied by each edge,
/// while the second is already resident in its join register.  The lowering
/// plan remains general enough to diagnose more parallel copies; extending
/// their proof renderer is tracked separately.
#[allow(clippy::too_many_arguments)]
pub fn generate_control_region(
    prefix: &str,
    region_expr: &str,
    region: &ControlRegion,
    input_registers: &[Gpr],
    condition_register: Gpr,
    join_registers: &[Gpr],
    continuation_temporaries: &[Gpr],
    requested_output: Gpr,
) -> Result<ControlX86Emission, LoweringError> {
    let lowered = lower_control_region(
        region,
        input_registers,
        condition_register,
        join_registers,
        continuation_temporaries,
        requested_output,
    )?;
    if region.join.true_arguments.len() != 2 || region.join.false_arguments.len() != 2 {
        return Err(LoweringError::UnsupportedJoinArm);
    }

    let prefix_name = format!("{prefix}_prefix");
    let true_name = format!("{prefix}_true_transfer");
    let false_name = format!("{prefix}_false_transfer");
    let continuation_name = format!("{prefix}_continuation");
    let linked_name = format!("{prefix}_linked_conditional");
    let control_name = format!("{prefix}_linked_control");

    let prefix_expr = format!("{region_expr}.prefix");
    let continuation_expr = format!("{region_expr}.join.continuation");
    let true_edge_name = format!("{prefix}_true_transfer_raw");
    let false_edge_name = format!("{prefix}_false_transfer_raw");
    let true_edge_expr = format!("{true_edge_name}()");
    let false_edge_expr = format!("{false_edge_name}()");
    let edge_region = |argument: BlockArgument| Region {
        inputs: region.join.arguments.clone(),
        nodes: vec![],
        outputs: vec![cert::Port {
            id: argument.value,
            width: argument.width,
        }],
    };
    let true_edge = edge_region(region.join.true_arguments[0]);
    let false_edge = edge_region(region.join.false_arguments[0]);

    let available = region
        .prefix
        .inputs
        .iter()
        .zip(input_registers)
        .map(|(port, register)| (port.id, *register))
        .chain(std::iter::once((region.join.condition, condition_register)))
        .collect::<BTreeMap<_, _>>();
    let edge_input_registers = region
        .join
        .arguments
        .iter()
        .map(|port| {
            available
                .get(&port.id)
                .copied()
                .ok_or(LoweringError::UndefinedValue(port.id))
        })
        .collect::<Result<Vec<_>, _>>()?;

    let prefix_emission = generate(
        &prefix_name,
        &prefix_expr,
        &region.prefix,
        input_registers,
        &[condition_register],
        condition_register,
    )?;
    let true_emission = generate(
        &true_name,
        &true_edge_expr,
        &true_edge,
        &edge_input_registers,
        &[join_registers[0]],
        join_registers[0],
    )?;
    let false_emission = generate(
        &false_name,
        &false_edge_expr,
        &false_edge,
        &edge_input_registers,
        &[join_registers[0]],
        join_registers[0],
    )?;
    let continuation_emission = generate(
        &continuation_name,
        &continuation_expr,
        &region.join.continuation,
        join_registers,
        continuation_temporaries,
        requested_output,
    )?;
    if true_emission.lowered.instructions != lowered.when_true_transfer
        || false_emission.lowered.instructions != lowered.when_false_transfer
        || true_emission.lowered.instructions.len() != 1
        || false_emission.lowered.instructions.len() != 1
    {
        return Err(LoweringError::UnsupportedJoinArm);
    }
    let (continuation_output_id, continuation_left_id, continuation_right_id) =
        match region.join.continuation.nodes.as_slice() {
            [Node::Add {
                width: 64,
                output,
                left,
                right,
            }] => (*output, *left, *right),
            _ => return Err(LoweringError::UnsupportedJoinArm),
        };
    if continuation_left_id != region.join.true_arguments[0].parameter
        || continuation_left_id != region.join.false_arguments[0].parameter
        || continuation_right_id != region.join.true_arguments[1].parameter
        || continuation_right_id != region.join.false_arguments[1].parameter
    {
        return Err(LoweringError::UnsupportedJoinArm);
    }
    let continuation_inputs = region
        .join
        .continuation
        .inputs
        .iter()
        .zip(join_registers)
        .map(|(port, register)| (port.id, *register))
        .collect::<BTreeMap<_, _>>();
    let continuation_left_register = continuation_inputs
        .get(&continuation_left_id)
        .copied()
        .ok_or(LoweringError::UndefinedValue(continuation_left_id))?;
    let continuation_right_register = continuation_inputs
        .get(&continuation_right_id)
        .copied()
        .ok_or(LoweringError::UndefinedValue(continuation_right_id))?;
    let expected_continuation = vec![
        Instruction::MovRR {
            destination: requested_output,
            source: continuation_left_register,
        },
        Instruction::AddRR {
            destination: requested_output,
            source: continuation_right_register,
        },
    ];
    if continuation_emission.lowered.instructions != expected_continuation
        || continuation_output_id != region.join.continuation.outputs[0].id
    {
        return Err(LoweringError::UnsupportedJoinArm);
    }

    let true_bytes = true_emission
        .lowered
        .instructions
        .iter()
        .map(|instruction| instruction.canonical_length())
        .sum::<usize>();
    let false_bytes = false_emission
        .lowered
        .instructions
        .iter()
        .map(|instruction| instruction.canonical_length())
        .sum::<usize>();
    let false_displacement = true_bytes + 2;
    let join_displacement = false_bytes;
    for bytes in [false_displacement, join_displacement] {
        if bytes > i8::MAX as usize {
            return Err(LoweringError::ShortBranchOutOfRange { bytes });
        }
    }
    let conditional_length = prefix_emission
        .lowered
        .instructions
        .iter()
        .map(|instruction| instruction.canonical_length())
        .sum::<usize>()
        + 3
        + 2
        + true_bytes
        + 2
        + false_bytes;
    let continuation_length = continuation_emission
        .lowered
        .instructions
        .iter()
        .map(|instruction| instruction.canonical_length())
        .sum::<usize>();
    let prefix_span = render_block_span_proof(&prefix_emission.lowered.instructions);
    let true_span = render_block_span_proof(&true_emission.lowered.instructions);
    let false_span = render_block_span_proof(&false_emission.lowered.instructions);
    let prefix_span_at = prefix_span.replace("start", "before.rip");
    let true_span_at = true_span.replace(
        "start",
        &format!("linked_branch_after({linked_name}(), before).rip"),
    );
    let false_span_at = false_span.replace(
        "start",
        &format!("linked_branch_after({linked_name}(), before).rip"),
    );

    let input_indices = region
        .prefix
        .inputs
        .iter()
        .enumerate()
        .map(|(index, port)| (port.id, index))
        .collect::<BTreeMap<_, _>>();
    let prefix_input_args = (0..region.prefix.inputs.len())
        .map(|index| format!("input_{index}_placed"))
        .collect::<Vec<_>>()
        .join(", ");
    let prefix_call_args = if prefix_input_args.is_empty() {
        String::new()
    } else {
        format!(", {prefix_input_args}")
    };
    let value_machine_parameters = || {
        let mut parameters = vec![
            emitted_parameter("values", "Valuation()"),
            emitted_parameter("before", "MachineState<M>"),
        ];
        parameters.extend(
            region
                .prefix
                .inputs
                .iter()
                .zip(input_registers)
                .enumerate()
                .map(|(index, (port, register))| {
                    emitted_parameter(
                        format!("input_{index}_placed"),
                        format!(
                            "ValuePlaced(values, {}, {}, before)",
                            port.id,
                            register.heather_name(),
                        ),
                    )
                }),
        );
        parameters
    };
    let prefix_placed = |port: cert::Port| {
        let index = input_indices[&port.id];
        let register = input_registers[index];
        format!(
            "placed_after_frame(values, {}, {}, before, {prefix_name}_after(before), \
             input_{index}_placed, {prefix_name}_preserves_protected({}, before, trivial))",
            port.id,
            register.heather_name(),
            register.heather_name(),
        )
    };
    let edge_args = region
        .join
        .arguments
        .iter()
        .map(|port| prefix_placed(*port))
        .collect::<Vec<_>>()
        .join(",\n        ");

    let first_true = region.join.true_arguments[0];
    let second_true = region.join.true_arguments[1];
    let first_false = region.join.false_arguments[0];
    let second_false = region.join.false_arguments[1];
    let first_join_register = join_registers[0].heather_name();
    let second_join_register = join_registers[1].heather_name();
    let second_true_register = available[&second_true.value].heather_name();
    let second_false_register = available[&second_false.value].heather_name();
    if second_true_register != second_join_register || second_false_register != second_join_register
    {
        return Err(LoweringError::UnsupportedJoinArm);
    }

    let mut module = Module::default();
    module.raw(cert::render_region_function(&true_edge_name, &true_edge));
    module.raw(cert::render_region_function(&false_edge_name, &false_edge));
    module.raw(prefix_emission.text);
    module.raw(true_emission.text);
    module.raw(false_emission.text);
    module.raw(continuation_emission.text);

    module.declaration(emitted_function(
        &linked_name,
        false,
        vec![],
        "LinkedConditionalBlock",
        format!(
            "LinkedConditionalBlock(\n\
                 prefix := {prefix_name}_instructions(),\n\
                 test_register := {},\n\
                 false_displacement := @bitvec::BitVec::ofNat(8, {false_displacement}),\n\
                 when_true := {true_name}_instructions(),\n\
                 join_displacement := @bitvec::BitVec::ofNat(8, {join_displacement}),\n\
                 when_false := {false_name}_instructions())",
            condition_register.heather_name(),
        ),
    ));
    module.declaration(emitted_function(
        &control_name,
        false,
        vec![],
        "LinkedControlBlock",
        format!(
            "LinkedControlBlock(conditional := {linked_name}(),\n\
                 continuation := {continuation_name}_instructions())"
        ),
    ));
    module.declaration(emitted_function(
        format!("{control_name}_bytes"),
        false,
        vec![],
        "List<BitVec(8)>",
        format!("linked_control_bytes({control_name}())"),
    ));
    module.declaration(emitted_theorem(
        format!("{control_name}_byte_length"),
        false,
        vec![],
        format!(
            "{control_name}_bytes().len() = {}",
            conditional_length + continuation_length,
        ),
        "refl",
    ));
    module.declaration(emitted_theorem(
        format!("{linked_name}_decodes"),
        false,
        vec![emitted_parameter("start", "BitVec(64)")],
        format!("LinkedConditionalDecodes({linked_name}(), start)"),
        format!(
            "LinkedConditionalDecodes(\n\
                 prefix_decoding := canonical_block_decodes(\n\
                   {prefix_name}_instructions(), start),\n\
                 test_decoding := canonical_encoding_decodes(\n\
                   linked_test_start({linked_name}(), start), TestRR({}, {})),\n\
                 branch_decoding := decode_short_control_complete(JumpZero(\n\
                   @bitvec::BitVec::ofNat(8, {false_displacement}))),\n\
                 true_decoding := canonical_block_decodes(\n\
                   {true_name}_instructions(), linked_true_start({linked_name}(), start)),\n\
                 join_decoding := decode_short_control_complete(Jump(\n\
                   @bitvec::BitVec::ofNat(8, {join_displacement}))),\n\
                 false_decoding := canonical_block_decodes(\n\
                   {false_name}_instructions(), linked_false_start({linked_name}(), start)))",
            condition_register.heather_name(),
            condition_register.heather_name(),
        ),
    ));
    module.declaration(emitted_theorem(
        format!("{linked_name}_false_target"),
        false,
        vec![emitted_parameter("start", "BitVec(64)")],
        format!(
            "short_branch_target(linked_branch_start({linked_name}(), start), @bitvec::BitVec::ofNat(8, {false_displacement})) = linked_false_start({linked_name}(), start)"
        ),
        format!(
            "trans(sym(bitvec::BitVec::iter_add_eq_add(64,\n\
                 next_rip(linked_branch_start({linked_name}(), start), 2),\n\
                 @bitvec::BitVec::sign_extend(7, 56, @bitvec::BitVec::ofNat(8, {false_displacement})))),\n\
             sym(bitvec::BitVec::iterate_increment_compose(64,\n\
                 linked_true_start({linked_name}(), start), {true_bytes}, 2)))"
        ),
    ));
    module.declaration(emitted_theorem(
        format!("{linked_name}_join_target"),
        false,
        vec![emitted_parameter("start", "BitVec(64)")],
        format!(
            "short_branch_target(linked_join_jump_start({linked_name}(), start), @bitvec::BitVec::ofNat(8, {join_displacement})) = linked_join_start({linked_name}(), start)"
        ),
        format!(
            "sym(bitvec::BitVec::iter_add_eq_add(64,\n\
                 next_rip(linked_join_jump_start({linked_name}(), start), 2),\n\
                 @bitvec::BitVec::sign_extend(7, 56, @bitvec::BitVec::ofNat(8, {join_displacement}))))"
        ),
    ));
    module.declaration(emitted_theorem(
        format!("{linked_name}_layout"),
        false,
        vec![],
        format!("LinkedConditionalLayout({linked_name}())"),
        format!(
            "LinkedConditionalLayout(false_forward := refl, false_distance := refl,\n\
                 join_forward := refl, join_distance := refl,\n\
                 false_target := {linked_name}_false_target,\n\
                 join_target := {linked_name}_join_target)"
        ),
    ));

    let machine_before = || vec![emitted_parameter("before", "MachineState<M>")];
    module.declaration(emitted_theorem(
        format!("{linked_name}_prefix_at"),
        true,
        machine_before(),
        format!("linked_prefix_after({linked_name}(), before).rip = linked_test_start({linked_name}(), before.rip)"),
        format!("trans({prefix_name}_advances_rip(before), {prefix_span_at})"),
    ));
    for (side, after, block, span) in [
        ("true", "linked_true_after", &true_name, &true_span_at),
        ("false", "linked_false_after", &false_name, &false_span_at),
    ] {
        module.declaration(emitted_theorem(
            format!("{linked_name}_{side}_at"),
            true,
            machine_before(),
            format!("{after}({linked_name}(), before).rip = after_canonical_block(linked_branch_after({linked_name}(), before).rip, {block}_instructions())"),
            format!("trans({block}_advances_rip(linked_branch_after({linked_name}(), before)), {span})"),
        ));
    }
    for (side, selected, start, body) in [
        (
            "not_taken",
            "False",
            "linked_true_start",
            format!(
                "trans(jump_zero_not_taken_rip(\n\
                     linked_test_after({linked_name}(), before).flags.zf,\n\
                     linked_test_after({linked_name}(), before).rip,\n\
                     {linked_name}().false_displacement, selected),\n\
                   bitvec::BitVec::cong_iterate_increment(64, 2,\n\
                     linked_test_reaches_branch_start({linked_name}(), before,\n\
                       {linked_name}_prefix_at(before))))"
            ),
        ),
        (
            "taken",
            "True",
            "linked_false_start",
            format!(
                "trans(jump_zero_taken_rip(\n\
                     linked_test_after({linked_name}(), before).flags.zf,\n\
                     linked_test_after({linked_name}(), before).rip,\n\
                     {linked_name}().false_displacement, selected),\n\
                   trans(cong_fn<BitVec(64), BitVec(64)>(\n\
                     λ rip => short_branch_target(rip, {linked_name}().false_displacement),\n\
                     linked_test_reaches_branch_start({linked_name}(), before,\n\
                       {linked_name}_prefix_at(before))),\n\
                     {linked_name}_layout().false_target(before.rip)))"
            ),
        ),
    ] {
        module.declaration(emitted_theorem(
            format!("{linked_name}_{side}_at"),
            true,
            vec![
                emitted_parameter("before", "MachineState<M>"),
                emitted_parameter(
                    "selected",
                    format!("linked_test_after({linked_name}(), before).flags.zf = {selected}"),
                ),
            ],
            format!("linked_branch_after({linked_name}(), before).rip = {start}({linked_name}(), before.rip)"),
            body,
        ));
    }
    module.declaration(emitted_theorem(
        format!("{linked_name}_true_reaches_join"),
        true,
        vec![
            emitted_parameter("before", "MachineState<M>"),
            emitted_parameter("selected", format!("linked_test_after({linked_name}(), before).flags.zf = False")),
        ],
        format!("linked_true_jump_after({linked_name}(), before).rip = linked_join_start({linked_name}(), before.rip)"),
        format!(
            "calc {{\n\
               linked_true_jump_after({linked_name}(), before).rip\n\
                 = short_branch_target(linked_true_after({linked_name}(), before).rip, {linked_name}().join_displacement) := refl,\n\
                 = short_branch_target(linked_join_jump_start({linked_name}(), before.rip), {linked_name}().join_displacement) :=\n\
                   cong_fn<BitVec(64), BitVec(64)>(\n\
                     λ rip => short_branch_target(rip, {linked_name}().join_displacement),\n\
                     trans({linked_name}_true_at(before),\n\
                       cong_fn<BitVec(64), BitVec(64)>(\n\
                         λ rip => after_canonical_block(rip, {true_name}_instructions()),\n\
                         {linked_name}_not_taken_at(before, selected)))),\n\
                 = linked_join_start({linked_name}(), before.rip) := {linked_name}_layout().join_target(before.rip),\n\
             }}"
        ),
    ));
    module.declaration(emitted_theorem(
        format!("{linked_name}_false_reaches_join"),
        true,
        vec![
            emitted_parameter("before", "MachineState<M>"),
            emitted_parameter("selected", format!("linked_test_after({linked_name}(), before).flags.zf = True")),
        ],
        format!("linked_false_after({linked_name}(), before).rip = linked_join_start({linked_name}(), before.rip)"),
        format!(
            "calc {{\n\
               linked_false_after({linked_name}(), before).rip\n\
                 = after_canonical_block(linked_branch_after({linked_name}(), before).rip, {false_name}_instructions()) := {linked_name}_false_at(before),\n\
                 = after_canonical_block(linked_false_start({linked_name}(), before.rip), {false_name}_instructions()) :=\n\
                   cong_fn<BitVec(64), BitVec(64)>(\n\
                     λ rip => after_canonical_block(rip, {false_name}_instructions()),\n\
                     {linked_name}_taken_at(before, selected)),\n\
                 = linked_join_start({linked_name}(), before.rip) := refl,\n\
             }}"
        ),
    ));
    module.declaration(emitted_theorem(
        format!("{linked_name}_spans"),
        true,
        machine_before(),
        format!("LinkedConditionalSpans<M>({linked_name}(), before)"),
        format!(
            "LinkedConditionalSpans(\n\
               true_reaches_join := λ selected => {linked_name}_true_reaches_join(before, selected),\n\
               false_reaches_join := λ selected => {linked_name}_false_reaches_join(before, selected))"
        ),
    ));
    module.declaration(emitted_theorem(
        format!("{linked_name}_reaches_join"),
        true,
        machine_before(),
        format!("linked_conditional_after({linked_name}(), before).rip = linked_join_start({linked_name}(), before.rip)"),
        format!("linked_conditional_reaches_join({linked_name}(), before, {linked_name}_spans(before))"),
    ));
    module.declaration(emitted_theorem(
        format!("{control_name}_executes"),
        true,
        machine_before(),
        format!("ExecuteLinkedControlBlock<M>({control_name}(), before, linked_control_after({control_name}(), before))"),
        format!("canonical_linked_control_executes({control_name}(), before)"),
    ));

    // Register agreement between the physical edge states and the same
    // canonical transfer blocks started at the logical prefix state.
    for (side, edge_name, actual) in [
        ("true", &true_name, "linked_true_jump_after"),
        ("false", &false_name, "linked_false_after"),
    ] {
        for register in join_registers {
            let register = register.heather_name();
            let edge_agreement = format!(
                "{edge_name}_gprs_congruent(\n       linked_branch_after({linked_name}(), before),\n       {prefix_name}_after(before),\n       linked_branch_preserves_prefix_gprs({linked_name}(), before))"
            );
            let agreement = if side == "true" {
                format!(
                    "trans(execute_short_control_preserves_gprs(Jump({linked_name}().join_displacement), linked_true_after({linked_name}(), before)), {edge_agreement})"
                )
            } else {
                edge_agreement
            };
            module.declaration(emitted_theorem(
                format!("{linked_name}_{side}_{register}_agrees"),
                true,
                machine_before(),
                format!(
                    "read_gpr({register}, {actual}({linked_name}(), before).gprs) = read_gpr({register}, {edge_name}_after({prefix_name}_after(before)).gprs)"
                ),
                format!("cong_fn<Gprs, BitVec(64)>(read_gpr({register}, ·), {agreement})"),
            ));
        }
    }

    let true_refine_args = format!(
        "{true_name}_refines_function_ir(values, {prefix_name}_after(before),\n        {edge_args}, trivial)"
    );
    let false_refine_args = format!(
        "{false_name}_refines_function_ir(values, {prefix_name}_after(before),\n        {edge_args}, trivial)"
    );
    let true_second_prefix = prefix_placed(cert::Port {
        id: second_true.value,
        width: second_true.width,
    });
    let false_second_prefix = prefix_placed(cert::Port {
        id: second_false.value,
        width: second_false.width,
    });

    for (name, result, body) in [
        (
            format!("{linked_name}_condition_placed"),
            format!("BitValuePlaced(values, {}, {}, linked_prefix_after({linked_name}(), before))", region.join.condition, condition_register.heather_name()),
            format!("sym({prefix_name}_refines_function_ir(values, before{prefix_call_args}, prefix_graph))"),
        ),
        (
            format!("{linked_name}_test_selects"),
            format!("linked_test_after({linked_name}(), before).flags.zf = zero_test_selector(@bitvec::BitVec::head_bit(0, values(1, {})))", region.join.condition),
            format!("linked_test_bit_value_placed_zf(values, {}, {linked_name}(), before, {linked_name}_condition_placed(values, before{prefix_call_args}, prefix_graph))", region.join.condition),
        ),
    ] {
        let mut parameters = value_machine_parameters();
        parameters.push(emitted_parameter(
            "prefix_graph",
            format!("RegionHolds({prefix_expr}, values)"),
        ));
        module.declaration(emitted_theorem(name, true, parameters, result, body));
    }

    for (side, ordinal, value, register, after, refinement, second_prefix, edge_name) in [
        (
            "true",
            "first",
            first_true.value,
            first_join_register,
            "linked_true_jump_after",
            &true_refine_args,
            None,
            &true_name,
        ),
        (
            "false",
            "first",
            first_false.value,
            first_join_register,
            "linked_false_after",
            &false_refine_args,
            None,
            &false_name,
        ),
        (
            "true",
            "second",
            second_true.value,
            second_join_register,
            "linked_true_jump_after",
            &true_refine_args,
            Some(&true_second_prefix),
            &true_name,
        ),
        (
            "false",
            "second",
            second_false.value,
            second_join_register,
            "linked_false_after",
            &false_refine_args,
            Some(&false_second_prefix),
            &false_name,
        ),
    ] {
        let body = if let Some(second_prefix) = second_prefix {
            format!(
                "placed_after_frame(values, {value}, {register},\n\
                   {prefix_name}_after(before), {after}({linked_name}(), before),\n\
                   {second_prefix},\n\
                   trans({linked_name}_{side}_{register}_agrees(before),\n\
                     {edge_name}_preserves_protected({register}, {prefix_name}_after(before), trivial)))"
            )
        } else {
            format!("sym(trans({linked_name}_{side}_{register}_agrees(before), {refinement}))")
        };
        module.declaration(emitted_theorem(
            format!("{linked_name}_{side}_{ordinal}_placed"),
            true,
            value_machine_parameters(),
            format!("ValuePlaced(values, {value}, {register}, {after}({linked_name}(), before))"),
            body,
        ));
    }

    let continuation_output = region.join.continuation.outputs[0].id;
    let continuation_destination = requested_output.heather_name();
    let continuation_left_register = continuation_left_register.heather_name();
    let continuation_right_register = continuation_right_register.heather_name();
    let first_false_value = first_false.value;
    let first_false_parameter = first_false.parameter;
    let second_false_value = second_false.value;
    let second_false_parameter = second_false.parameter;
    let first_true_value = first_true.value;
    let first_true_parameter = first_true.parameter;
    let second_true_value = second_true.value;
    let second_true_parameter = second_true.parameter;
    for (side, edge_name) in [("false", &false_name), ("true", &true_name)] {
        module.declaration(emitted_function(
            format!("{prefix}_{side}_entry"),
            true,
            machine_before(),
            "MachineState<M>",
            format!(
                "MachineState<M>(\n\
                 \x20 gprs := {edge_name}_after({prefix_name}_after(before)).gprs,\n\
                 \x20 flags := before.flags, rip := before.rip, memory := before.memory)"
            ),
        ));
    }
    module.declaration(emitted_function(
        format!("{prefix}_continuation_gprs"),
        false,
        vec![emitted_parameter("entry", "Gprs")],
        "Gprs",
        format!(
            "execute_add({continuation_destination}, {continuation_right_register},\n\
             \x20 write_gpr({continuation_destination}, read_gpr({continuation_left_register}, entry), entry)).gprs"
        ),
    ));
    module.declaration(emitted_theorem(
        format!("{prefix}_continuation_gprs_computes"),
        false,
        vec![emitted_parameter("entry", "Gprs")],
        format!(
            "read_gpr({continuation_destination}, {prefix}_continuation_gprs(entry)) = @bitvec::BitVec::add(64, read_gpr({continuation_left_register}, entry), read_gpr({continuation_right_register}, entry))"
        ),
        format!(
            "gpr_move_add_reads({continuation_destination}, {continuation_left_register}, {continuation_right_register}, entry, refl)"
        ),
    ));
    module.declaration(emitted_theorem(
        format!("{prefix}_continuation_gprs_agrees"),
        true,
        machine_before(),
        format!("{continuation_name}_after(before).gprs = {prefix}_continuation_gprs(before.gprs)"),
        "refl",
    ));

    let sides = [
        (
            "false",
            &false_name,
            first_false_value,
            first_false_parameter,
            second_false_value,
            second_false_parameter,
        ),
        (
            "true",
            &true_name,
            first_true_value,
            first_true_parameter,
            second_true_value,
            second_true_parameter,
        ),
    ];
    for (side, edge_name, first_value, _, second_value, _) in sides {
        for (index, ordinal, value, register) in [
            (0, "first", first_value, first_join_register),
            (1, "second", second_value, second_join_register),
        ] {
            module.declaration(emitted_theorem(
                format!("{prefix}_{side}_value_{index}"),
                true,
                value_machine_parameters(),
                format!(
                    "ValuePlaced(values, {value}, {register}, {edge_name}_after({prefix_name}_after(before)))"
                ),
                format!(
                    "trans({linked_name}_{side}_{ordinal}_placed(values, before{prefix_call_args}), {linked_name}_{side}_{register}_agrees(before))"
                ),
            ));
        }
    }
    for (side, edge_name, first_value, first_parameter, second_value, second_parameter) in sides {
        for (index, value, parameter, register) in [
            (0, first_value, first_parameter, first_join_register),
            (1, second_value, second_parameter, second_join_register),
        ] {
            let binding = format!("values(64, {parameter}) = values(64, {value})");
            let mut parameters = value_machine_parameters();
            parameters.push(emitted_parameter("binding", &binding));
            module.declaration(emitted_theorem(
                format!("{prefix}_{side}_parameter_{index}"),
                true,
                parameters.clone(),
                format!(
                    "ValuePlaced(values, {parameter}, {register}, {edge_name}_after({prefix_name}_after(before)))"
                ),
                format!(
                    "placed_for_parameter(values, {value}, {parameter}, {register},\n\
                     \x20 {edge_name}_after({prefix_name}_after(before)), binding,\n\
                     \x20 {prefix}_{side}_value_{index}(values, before{prefix_call_args}))"
                ),
            ));
            module.declaration(emitted_theorem(
                format!("{prefix}_{side}_entry_parameter_{index}"),
                true,
                parameters,
                format!(
                    "GprValuePlaced(values, {parameter}, {register}, {prefix}_{side}_entry(before).gprs)"
                ),
                format!(
                    "{prefix}_{side}_parameter_{index}(values, before{prefix_call_args}, binding)"
                ),
            ));
        }
    }
    for (side, _, first_value, first_parameter, second_value, second_parameter) in sides {
        let _ = (first_value, second_value);
        for (direction, index, parameter, register, continuation_id) in [
            (
                "left",
                0,
                first_parameter,
                continuation_left_register,
                continuation_left_id,
            ),
            (
                "right",
                1,
                second_parameter,
                continuation_right_register,
                continuation_right_id,
            ),
        ] {
            let mut parameters = value_machine_parameters();
            parameters.push(emitted_parameter(
                "binding",
                format!(
                    "values(64, {parameter}) = values(64, {})",
                    if index == 0 {
                        if side == "false" {
                            first_false_value
                        } else {
                            first_true_value
                        }
                    } else if side == "false" {
                        second_false_value
                    } else {
                        second_true_value
                    },
                ),
            ));
            module.declaration(emitted_theorem(
                format!("{prefix}_{side}_{direction}_agrees"),
                true,
                parameters,
                format!(
                    "read_gpr({register}, {prefix}_{side}_entry(before).gprs) = values(64, {continuation_id})"
                ),
                format!(
                    "sym({prefix}_{side}_entry_parameter_{index}(values, before{prefix_call_args}, binding))"
                ),
            ));
        }
    }
    for (side, ..) in sides {
        module.declaration(emitted_function(
            format!("{prefix}_{side}_sum"),
            true,
            machine_before(),
            "BitVec(64)",
            format!(
                "@bitvec::BitVec::add(64,\n\
                 \x20 read_gpr({continuation_left_register}, {prefix}_{side}_entry(before).gprs),\n\
                 \x20 read_gpr({continuation_right_register}, {prefix}_{side}_entry(before).gprs))"
            ),
        ));
        module.declaration(emitted_function(
            format!("{prefix}_{side}_left_sum"),
            true,
            vec![
                emitted_parameter("values", "Valuation()"),
                emitted_parameter("before", "MachineState<M>"),
            ],
            "BitVec(64)",
            format!(
                "@bitvec::BitVec::add(64, values(64, {continuation_left_id}),\n\
                 \x20 read_gpr({continuation_right_register}, {prefix}_{side}_entry(before).gprs))"
            ),
        ));
    }
    module.declaration(emitted_function(
        format!("{prefix}_semantic_sum"),
        false,
        vec![emitted_parameter("values", "Valuation()")],
        "BitVec(64)",
        format!(
            "@bitvec::BitVec::add(64, values(64, {continuation_left_id}), values(64, {continuation_right_id}))"
        ),
    ));
    module.declaration(emitted_theorem(
        format!("{prefix}_continuation_spec"),
        false,
        vec![
            emitted_parameter("values", "Valuation()"),
            emitted_parameter(
                "graph",
                format!("RegionHolds({region_expr}.join.continuation, values)"),
            ),
        ],
        format!("{prefix}_semantic_sum(values) = values(64, {continuation_output})"),
        "sym(graph.left)",
    ));

    for (side, _, first_value, first_parameter, second_value, second_parameter) in sides {
        for (direction, parameter, value, result, body) in [
            (
                "left",
                first_parameter,
                first_value,
                format!(
                    "{prefix}_{side}_sum(before) = {prefix}_{side}_left_sum(values, before)"
                ),
                format!(
                    "cong_fn<BitVec(64), BitVec(64)>(\n\
                     \x20 @bitvec::BitVec::add(64, ·, read_gpr({continuation_right_register}, {prefix}_{side}_entry(before).gprs)),\n\
                     \x20 {prefix}_{side}_left_agrees(values, before{prefix_call_args}, binding))"
                ),
            ),
            (
                "right",
                second_parameter,
                second_value,
                format!(
                    "{prefix}_{side}_left_sum(values, before) = {prefix}_semantic_sum(values)"
                ),
                format!(
                    "cong_fn<BitVec(64), BitVec(64)>(\n\
                     \x20 @bitvec::BitVec::add(64, values(64, {continuation_left_id}), ·),\n\
                     \x20 {prefix}_{side}_right_agrees(values, before{prefix_call_args}, binding))"
                ),
            ),
        ] {
            let mut parameters = value_machine_parameters();
            parameters.push(emitted_parameter(
                "binding",
                format!("values(64, {parameter}) = values(64, {value})"),
            ));
            module.declaration(emitted_theorem(
                format!("{prefix}_{side}_rewrite_{direction}"),
                true,
                parameters,
                result,
                body,
            ));
        }
        module.declaration(emitted_theorem(
            format!("{prefix}_{side}_computes"),
            true,
            machine_before(),
            format!(
                "read_gpr({continuation_destination}, {prefix}_continuation_gprs({prefix}_{side}_entry(before).gprs)) = {prefix}_{side}_sum(before)"
            ),
            format!(
                "{prefix}_continuation_gprs_computes({prefix}_{side}_entry(before).gprs)"
            ),
        ));
        let mut parameters = value_machine_parameters();
        parameters.extend([
            emitted_parameter(
                "left_binding",
                format!("values(64, {first_parameter}) = values(64, {first_value})"),
            ),
            emitted_parameter(
                "right_binding",
                format!("values(64, {second_parameter}) = values(64, {second_value})"),
            ),
            emitted_parameter(
                "continuation_graph",
                format!("RegionHolds({region_expr}.join.continuation, values)"),
            ),
        ]);
        module.declaration(emitted_theorem(
            format!("{prefix}_{side}_inputs_refine"),
            true,
            parameters,
            format!(
                "{prefix}_{side}_sum(before) = values(64, {continuation_output})"
            ),
            format!(
                "binary_observation_refines(values, {continuation_output},\n\
                 \x20 {continuation_left_id}, {continuation_right_id}, @bitvec::BitVec::add(64),\n\
                 \x20 read_gpr({continuation_left_register}, {prefix}_{side}_entry(before).gprs),\n\
                 \x20 read_gpr({continuation_right_register}, {prefix}_{side}_entry(before).gprs),\n\
                 \x20 continuation_graph.left,\n\
                 \x20 {prefix}_{side}_left_agrees(values, before{prefix_call_args}, left_binding),\n\
                 \x20 {prefix}_{side}_right_agrees(values, before{prefix_call_args}, right_binding))"
            ),
        ));
    }

    for (side, _, first_value, first_parameter, second_value, second_parameter) in sides {
        let selected_graph_type = format!(
            "RegionHolds({region_expr}.join.when_{side}, values) ∧ (BlockArgumentsHold(values, {region_expr}.join.{side}_arguments) ∧ RegionHolds({region_expr}.join.continuation, values))"
        );
        for (index, value, parameter, body) in [
            (
                0,
                first_value,
                first_parameter,
                format!(
                    "block_arguments_hold_head(values,\n\
                     \x20 BlockArgument(width := 64, value := {first_value}, parameter := {first_parameter}),\n\
                     \x20 Cons(BlockArgument(width := 64, value := {second_value}, parameter := {second_parameter}), Nil),\n\
                     \x20 selected_graph.right.left)"
                ),
            ),
            (
                1,
                second_value,
                second_parameter,
                format!(
                    "block_arguments_hold_head(values,\n\
                     \x20 BlockArgument(width := 64, value := {second_value}, parameter := {second_parameter}), Nil,\n\
                     \x20 block_arguments_hold_tail(values,\n\
                     \x20   BlockArgument(width := 64, value := {first_value}, parameter := {first_parameter}),\n\
                     \x20   Cons(BlockArgument(width := 64, value := {second_value}, parameter := {second_parameter}), Nil),\n\
                     \x20   selected_graph.right.left))"
                ),
            ),
        ] {
            module.declaration(emitted_theorem(
                format!("{prefix}_{side}_selected_binding_{index}"),
                false,
                vec![
                    emitted_parameter("values", "Valuation()"),
                    emitted_parameter("selected_graph", &selected_graph_type),
                ],
                format!("values(64, {parameter}) = values(64, {value})"),
                body,
            ));
        }
        module.declaration(emitted_theorem(
            format!("{prefix}_{side}_selected_continuation"),
            false,
            vec![
                emitted_parameter("values", "Valuation()"),
                emitted_parameter("selected_graph", selected_graph_type),
            ],
            format!("RegionHolds({region_expr}.join.continuation, values)"),
            "selected_graph.right.right",
        ));
    }

    for (suffix, result, false_body, true_body) in [
        (
            "selected_gprs",
            "Gprs",
            format!("{prefix}_continuation_gprs({prefix}_false_entry(before).gprs)"),
            format!("{prefix}_continuation_gprs({prefix}_true_entry(before).gprs)"),
        ),
        (
            "selected_sum",
            "BitVec(64)",
            format!("{prefix}_false_sum(before)"),
            format!("{prefix}_true_sum(before)"),
        ),
    ] {
        module.declaration(emitted_function(
            format!("{prefix}_{suffix}"),
            true,
            vec![
                emitted_parameter("values", "Valuation()"),
                emitted_parameter("before", "MachineState<M>"),
            ],
            result,
            format!(
                "match @bitvec::BitVec::head_bit(0, values(1, {region_expr}.join.condition)) {{\n\
                 \x20 False => {false_body},\n\
                 \x20 True => {true_body},\n\
                 }}"
            ),
        ));
    }
    module.declaration(emitted_theorem(
        format!("{prefix}_false_machine_agrees"),
        true,
        machine_before(),
        format!(
            "execute_block_normal({continuation_name}_instructions(), linked_false_after({linked_name}(), before)).gprs = {prefix}_continuation_gprs({prefix}_false_entry(before).gprs)"
        ),
        format!(
            "compose_equality<Gprs>(\n\
             \x20 execute_block_normal({continuation_name}_instructions(), linked_false_after({linked_name}(), before)).gprs,\n\
             \x20 execute_block_normal({continuation_name}_instructions(), {prefix}_false_entry(before)).gprs,\n\
             \x20 {prefix}_continuation_gprs({prefix}_false_entry(before).gprs),\n\
             \x20 {continuation_name}_gprs_congruent(\n\
             \x20   linked_false_after({linked_name}(), before), {prefix}_false_entry(before),\n\
             \x20   {false_name}_gprs_congruent(linked_branch_after({linked_name}(), before),\n\
             \x20     {prefix_name}_after(before), linked_branch_preserves_prefix_gprs({linked_name}(), before))),\n\
             \x20 {prefix}_continuation_gprs_agrees({prefix}_false_entry(before)))"
        ),
    ));
    module.declaration(emitted_theorem(
        format!("{prefix}_true_entry_agrees"),
        true,
        machine_before(),
        format!(
            "linked_true_jump_after({linked_name}(), before).gprs = {prefix}_true_entry(before).gprs"
        ),
        format!(
            "compose_equality<Gprs>(\n\
             \x20 linked_true_jump_after({linked_name}(), before).gprs,\n\
             \x20 linked_true_after({linked_name}(), before).gprs,\n\
             \x20 {prefix}_true_entry(before).gprs,\n\
             \x20 execute_short_control_preserves_gprs(Jump({linked_name}().join_displacement), linked_true_after({linked_name}(), before)),\n\
             \x20 {true_name}_gprs_congruent(linked_branch_after({linked_name}(), before),\n\
             \x20   {prefix_name}_after(before), linked_branch_preserves_prefix_gprs({linked_name}(), before)))"
        ),
    ));
    module.declaration(emitted_theorem(
        format!("{prefix}_true_machine_agrees"),
        true,
        machine_before(),
        format!(
            "execute_block_normal({continuation_name}_instructions(), linked_true_jump_after({linked_name}(), before)).gprs = {prefix}_continuation_gprs({prefix}_true_entry(before).gprs)"
        ),
        format!(
            "compose_equality<Gprs>(\n\
             \x20 execute_block_normal({continuation_name}_instructions(), linked_true_jump_after({linked_name}(), before)).gprs,\n\
             \x20 execute_block_normal({continuation_name}_instructions(), {prefix}_true_entry(before)).gprs,\n\
             \x20 {prefix}_continuation_gprs({prefix}_true_entry(before).gprs),\n\
             \x20 {continuation_name}_gprs_congruent(linked_true_jump_after({linked_name}(), before),\n\
             \x20   {prefix}_true_entry(before), {prefix}_true_entry_agrees(before)),\n\
             \x20 {prefix}_continuation_gprs_agrees({prefix}_true_entry(before)))"
        ),
    ));

    let mut linked_parameters = value_machine_parameters();
    linked_parameters.push(emitted_parameter(
        "prefix_graph",
        format!("RegionHolds({prefix_expr}, values)"),
    ));
    module.declaration(emitted_theorem(
        format!("{prefix}_linked_agrees"),
        true,
        linked_parameters,
        format!(
            "read_gpr({continuation_destination}, linked_control_after({control_name}(), before).gprs) = read_gpr({continuation_destination}, {prefix}_selected_gprs(values, before))"
        ),
        format!(
            "trans(linked_control_read_after({continuation_destination}, {control_name}(), before),\n\
             \x20 cong_fn<Gprs, BitVec(64)>(read_gpr({continuation_destination}, ·), selected_results_agree(\n\
             \x20   @bitvec::BitVec::head_bit(0, values(1, {region_expr}.join.condition)),\n\
             \x20   linked_test_after({linked_name}(), before).flags.zf,\n\
             \x20   execute_block_normal({continuation_name}_instructions(), linked_true_jump_after({linked_name}(), before)).gprs,\n\
             \x20   execute_block_normal({continuation_name}_instructions(), linked_false_after({linked_name}(), before)).gprs,\n\
             \x20   {prefix}_continuation_gprs({prefix}_true_entry(before).gprs),\n\
             \x20   {prefix}_continuation_gprs({prefix}_false_entry(before).gprs),\n\
             \x20   {linked_name}_test_selects(values, before{prefix_call_args}, prefix_graph),\n\
             \x20   {prefix}_false_machine_agrees(before), {prefix}_true_machine_agrees(before))))"
        ),
    ));
    module.declaration(emitted_theorem(
        format!("{prefix}_selected_computes"),
        true,
        vec![
            emitted_parameter("values", "Valuation()"),
            emitted_parameter("before", "MachineState<M>"),
        ],
        format!(
            "read_gpr({continuation_destination}, {prefix}_selected_gprs(values, before)) = {prefix}_selected_sum(values, before)"
        ),
        format!(
            "selected_computation_agrees<Gprs, BitVec(64)>(\n\
             \x20 @bitvec::BitVec::head_bit(0, values(1, {region_expr}.join.condition)),\n\
             \x20 {prefix}_continuation_gprs({prefix}_false_entry(before).gprs),\n\
             \x20 {prefix}_continuation_gprs({prefix}_true_entry(before).gprs),\n\
             \x20 read_gpr({continuation_destination}, ·), {prefix}_false_sum(before),\n\
             \x20 {prefix}_true_sum(before), {prefix}_false_computes(before), {prefix}_true_computes(before))"
        ),
    ));
    let mut selected_parameters = value_machine_parameters();
    selected_parameters.push(emitted_parameter(
        "join_graph",
        format!("ControlJoinHolds(values, {region_expr}.join)"),
    ));
    module.declaration(emitted_theorem(
        format!("{prefix}_selected_semantic_refines"),
        true,
        selected_parameters.clone(),
        format!("{prefix}_selected_sum(values, before) = values(64, {continuation_output})"),
        format!(
            "control_join_cases(values, {region_expr}.join,\n\
             \x20 λ selected => (match selected {{\n\
             \x20   False => {prefix}_false_sum(before),\n\
             \x20   True => {prefix}_true_sum(before),\n\
             \x20 }}) = values(64, {continuation_output}),\n\
             \x20 join_graph,\n\
             \x20 λ selected_graph => {prefix}_false_inputs_refine(\n\
             \x20   values, before{prefix_call_args},\n\
             \x20   {prefix}_false_selected_binding_0(values, selected_graph),\n\
             \x20   {prefix}_false_selected_binding_1(values, selected_graph),\n\
             \x20   {prefix}_false_selected_continuation(values, selected_graph)),\n\
             \x20 λ selected_graph => {prefix}_true_inputs_refine(\n\
             \x20   values, before{prefix_call_args},\n\
             \x20   {prefix}_true_selected_binding_0(values, selected_graph),\n\
             \x20   {prefix}_true_selected_binding_1(values, selected_graph),\n\
             \x20   {prefix}_true_selected_continuation(values, selected_graph)))"
        ),
    ));
    module.declaration(emitted_theorem(
        format!("{prefix}_selected_refines"),
        true,
        selected_parameters,
        format!(
            "read_gpr({continuation_destination}, {prefix}_selected_gprs(values, before)) = values(64, {continuation_output})"
        ),
        format!(
            "compose_equality<BitVec(64)>(\n\
             \x20 read_gpr({continuation_destination}, {prefix}_selected_gprs(values, before)),\n\
             \x20 {prefix}_selected_sum(values, before), values(64, {continuation_output}),\n\
             \x20 {prefix}_selected_computes(values, before),\n\
             \x20 {prefix}_selected_semantic_refines(values, before{prefix_call_args}, join_graph))"
        ),
    ));
    let mut final_parameters = value_machine_parameters();
    final_parameters.push(emitted_parameter(
        "graph",
        format!("ControlRegionHolds(values, {region_expr})"),
    ));
    module.declaration(emitted_theorem(
        format!("{prefix}_refines_function_ir"),
        true,
        final_parameters,
        format!(
            "read_gpr({continuation_destination}, linked_control_after({control_name}(), before).gprs) = values(64, {continuation_output})"
        ),
        format!(
            "trans({prefix}_linked_agrees(values, before{prefix_call_args}, graph.left),\n\
             \x20 {prefix}_selected_refines(values, before{prefix_call_args}, graph.right))"
        ),
    ));

    let text = module.render();
    Ok(ControlX86Emission { lowered, text })
}

/// Lower one valid-looking, 64-bit, single-output constant/binary-ALU DAG. The generated
/// certificate remains responsible for proving that this untrusted plan agrees
/// with the actual Heather region.
pub fn lower_dag(
    region: &Region,
    input_registers: &[Gpr],
    temporary_registers: &[Gpr],
    requested_output: Gpr,
) -> Result<LoweredDag, LoweringError> {
    if region.inputs.len() != input_registers.len() {
        return Err(LoweringError::InputPlacementCount {
            inputs: region.inputs.len(),
            registers: input_registers.len(),
        });
    }
    if region.outputs.len() != 1 {
        return Err(LoweringError::OutputCount(region.outputs.len()));
    }

    let mut all_registers = BTreeSet::new();
    for &register in input_registers {
        if !all_registers.insert(register) {
            return Err(LoweringError::DuplicateRegister(register));
        }
    }
    let mut temporary_set = BTreeSet::new();
    for &register in temporary_registers {
        if !temporary_set.insert(register) {
            return Err(LoweringError::DuplicateRegister(register));
        }
        if all_registers.contains(&register) {
            return Err(LoweringError::InputOverlapsTemporary(register));
        }
    }
    if !temporary_set.contains(&requested_output) {
        return Err(LoweringError::OutputRegisterUnavailable(requested_output));
    }

    let mut placements = BTreeMap::new();
    let mut widths = BTreeMap::new();
    for (port, &register) in region.inputs.iter().zip(input_registers) {
        require_placement_width(port.id, port.width)?;
        if placements.insert(port.id, register).is_some() {
            return Err(LoweringError::DuplicateValue(port.id));
        }
        widths.insert(port.id, port.width);
    }

    let mut uses = BTreeMap::<u64, usize>::new();
    for (node_index, node) in region.nodes.iter().enumerate() {
        match selected_node(*node, node_index)? {
            SelectedNode::Binary(node) => {
                *uses.entry(node.left).or_default() += 1;
                *uses.entry(node.right).or_default() += 1;
            }
            SelectedNode::Comparison(node) => {
                *uses.entry(node.left).or_default() += 1;
                *uses.entry(node.right).or_default() += 1;
            }
            SelectedNode::Constant(_) => {}
        }
    }
    for output in &region.outputs {
        *uses.entry(output.id).or_default() += 1;
    }

    let mut owners = BTreeMap::<Gpr, u64>::new();
    let mut instructions = Vec::new();
    let mut node_plans = Vec::with_capacity(region.nodes.len());
    let mut clobbered = BTreeSet::new();

    for (node_index, &raw_node) in region.nodes.iter().enumerate() {
        let selected = selected_node(raw_node, node_index)?;
        match selected {
            SelectedNode::Binary(BinaryNode { operation: BinaryOperation::Add | BinaryOperation::Sub, .. }) => require_width(selected.output(), selected.width())?,
            _ => require_placement_width(selected.output(), selected.width())?,
        }
        if placements.contains_key(&selected.output()) {
            return Err(LoweringError::DuplicateValue(selected.output()));
        }
        let produces_output = region.outputs[0].id == selected.output();

        let (
            left_register,
            right_register,
            destination,
            reused_value,
            orientation,
            step_instructions,
        ) = match selected {
            SelectedNode::Constant(node) => {
                let preferred = produces_output
                    .then_some(requested_output)
                    .filter(|register| !owners.contains_key(register));
                let destination = preferred
                    .or_else(|| {
                        temporary_registers
                            .iter()
                            .copied()
                            .find(|register| !owners.contains_key(register))
                    })
                    .ok_or(LoweringError::RegisterPressure {
                        node_index,
                        live_temporaries: owners.len(),
                    })?;
                (
                    None,
                    None,
                    destination,
                    None,
                    OperandOrientation::Original,
                    vec![Instruction::MovRI {
                        destination,
                        immediate: if node.width == 64 { node.value } else { node.value & ((1u64 << node.width) - 1) },
                    }],
                )
            }
            SelectedNode::Binary(node) => {
                let Some(&left_register) = placements.get(&node.left) else {
                    return Err(LoweringError::UndefinedValue(node.left));
                };
                let Some(&right_register) = placements.get(&node.right) else {
                    return Err(LoweringError::UndefinedValue(node.right));
                };
                for value in [node.left, node.right] {
                    if widths.get(&value) != Some(&node.width) {
                        return Err(LoweringError::UnsupportedWidth {
                            value,
                            width: *widths.get(&value).unwrap_or(&0),
                        });
                    }
                }

                let left_last = last_use_in_node(&uses, node.left, node.left, node.right);
                let right_last = last_use_in_node(&uses, node.right, node.left, node.right);
                let left_reusable = left_last && owners.get(&left_register) == Some(&node.left);
                let right_reusable = node.operation.commutativity_theorem().is_some()
                    && right_last
                    && owners.get(&right_register) == Some(&node.right);
                let (reused_value, orientation) = if produces_output
                    && right_reusable
                    && right_register == requested_output
                    && (!left_reusable || left_register != requested_output)
                {
                    (Some(node.right), OperandOrientation::Reversed)
                } else if left_reusable {
                    (Some(node.left), OperandOrientation::Original)
                } else if right_reusable {
                    (Some(node.right), OperandOrientation::Reversed)
                } else {
                    (None, OperandOrientation::Original)
                };
                let (destination, step_instructions) = match reused_value {
                    Some(_) => {
                        let (destination, source) = match orientation {
                            OperandOrientation::Original => (left_register, right_register),
                            OperandOrientation::Reversed => (right_register, left_register),
                        };
                        (
                            destination,
                            vec![binary_instruction(node.operation, destination, source)],
                        )
                    }
                    None => {
                        let destination = temporary_registers
                            .iter()
                            .copied()
                            .find(|register| !owners.contains_key(register))
                            .ok_or(LoweringError::RegisterPressure {
                                node_index,
                                live_temporaries: owners.len(),
                            })?;
                        (
                            destination,
                            vec![
                                Instruction::MovRR {
                                    destination,
                                    source: left_register,
                                },
                                binary_instruction(node.operation, destination, right_register),
                            ],
                        )
                    }
                };
                consume_use(&mut uses, node.left)?;
                consume_use(&mut uses, node.right)?;
                for value in [node.left, node.right] {
                    if uses.get(&value) == Some(&0) {
                        if let Some(&register) = placements.get(&value) {
                            if register != destination && owners.get(&register) == Some(&value) {
                                owners.remove(&register);
                            }
                        }
                    }
                }
                (
                    Some(left_register),
                    Some(right_register),
                    destination,
                    reused_value,
                    orientation,
                    step_instructions,
                )
            }
            SelectedNode::Comparison(node) => {
                if !produces_output {
                    return Err(LoweringError::UnsupportedOperation { node_index });
                }
                if node.operand_width > 64 || (node.operand_width != 64 && node.operation == ComparisonOperation::SignedLessThan) {
                    return Err(LoweringError::UnsupportedWidth {
                        value: node.output,
                        width: node.operand_width,
                    });
                }
                let Some(&left_register) = placements.get(&node.left) else {
                    return Err(LoweringError::UndefinedValue(node.left));
                };
                let Some(&right_register) = placements.get(&node.right) else {
                    return Err(LoweringError::UndefinedValue(node.right));
                };
                for value in [node.left, node.right] {
                    if widths.get(&value) != Some(&node.operand_width) {
                        return Err(LoweringError::UnsupportedWidth {
                            value,
                            width: *widths.get(&value).unwrap_or(&0),
                        });
                    }
                }
                let preferred = produces_output
                    .then_some(requested_output)
                    .filter(|register| !owners.contains_key(register))
                    .and_then(|register| LowByteGpr::from_gpr(register).map(|_| register));
                let destination = preferred.or_else(|| {
                    temporary_registers.iter().copied().find(|register| {
                        !owners.contains_key(register) && LowByteGpr::from_gpr(*register).is_some()
                    })
                });
                let destination = match destination {
                    Some(destination) => destination,
                    None if temporary_registers
                        .iter()
                        .any(|register| !owners.contains_key(register)) =>
                    {
                        return Err(LoweringError::NoSafeByteRegister { node_index });
                    }
                    None => {
                        return Err(LoweringError::RegisterPressure {
                            node_index,
                            live_temporaries: owners.len(),
                        });
                    }
                };
                let byte_destination = LowByteGpr::from_gpr(destination)
                    .expect("comparison destination was filtered to a low-byte register");
                consume_use(&mut uses, node.left)?;
                consume_use(&mut uses, node.right)?;
                for value in [node.left, node.right] {
                    if uses.get(&value) == Some(&0) {
                        if let Some(&register) = placements.get(&value) {
                            if owners.get(&register) == Some(&value) {
                                owners.remove(&register);
                            }
                        }
                    }
                }
                let set = match node.operation {
                    ComparisonOperation::UnsignedLessThan => Instruction::SetBelow {
                        destination: byte_destination,
                    },
                    ComparisonOperation::SignedLessThan => Instruction::SetLess {
                        destination: byte_destination,
                    },
                };
                (
                    Some(left_register),
                    Some(right_register),
                    destination,
                    None,
                    OperandOrientation::Original,
                    vec![
                        Instruction::MovRI {
                            destination,
                            immediate: 0,
                        },
                        Instruction::CmpRR {
                            left: left_register,
                            right: right_register,
                        },
                        set,
                    ],
                )
            }
        };
        if uses.get(&selected.output()).copied().unwrap_or(0) > 0 {
            owners.insert(destination, selected.output());
        } else {
            owners.remove(&destination);
        }
        placements.insert(selected.output(), destination);
        widths.insert(selected.output(), selected.width());
        clobbered.insert(destination);
        instructions.extend(step_instructions.iter().copied());
        node_plans.push(NodePlan {
            node_index,
            node: selected,
            left_register,
            right_register,
            destination,
            reused_value,
            orientation,
            instructions: step_instructions,
        });
    }

    let output = region.outputs[0];
    if output.width > 64 {
        return Err(LoweringError::UnsupportedWidth {
            value: output.id,
            width: output.width,
        });
    }
    if widths.get(&output.id) != Some(&output.width) {
        return Err(LoweringError::UndefinedValue(output.id));
    }
    let mut output_register = *placements
        .get(&output.id)
        .ok_or(LoweringError::UndefinedValue(output.id))?;
    if output_register != requested_output {
        instructions.push(Instruction::MovRR {
            destination: requested_output,
            source: output_register,
        });
        clobbered.insert(requested_output);
        output_register = requested_output;
    }

    Ok(LoweredDag {
        input_registers: input_registers.to_vec(),
        node_plans,
        instructions,
        output_id: output.id,
        output_width: output.width,
        output_register,
        clobbered,
    })
}

/// Select, assign, and render a checked Heather artifact for one concrete
/// region. The renderer's machine equalities are deliberately `refl`: any
/// disagreement between this plan and the real x86 semantics is rejected when
/// the emitted module elaborates.
pub fn generate(
    prefix: &str,
    region_expr: &str,
    region: &Region,
    input_registers: &[Gpr],
    temporary_registers: &[Gpr],
    requested_output: Gpr,
) -> Result<X86Emission, LoweringError> {
    let lowered = lower_dag(
        region,
        input_registers,
        temporary_registers,
        requested_output,
    )?;
    generate_selected(prefix, region_expr, region, lowered)
}

pub(super) fn generate_selected(
    prefix: &str, region_expr: &str, region: &Region, lowered: LoweredDag,
) -> Result<X86Emission, LoweringError> {
    let input_registers = &lowered.input_registers;
    let instructions_name = format!("{prefix}_instructions");
    let bytes_name = format!("{prefix}_bytes");
    let after_name = format!("{prefix}_after");
    let protected_name = format!("{prefix}_Protected");
    let public_parameters = common_parameters(region_expr, region, input_registers);
    let public_arguments = common_arguments(region);
    let compact_parameters = compact_parameters(prefix);
    let context_arguments = context_constructor_arguments(region);
    let arguments = "values, before, context";
    let mut header = Module::default();
    emit_instruction_spine(prefix, &lowered.instructions, &mut header);
    header.declaration(Declaration::function(
        &instructions_name,
        Expr::name("List<Instruction>"),
        Block::expression(instruction_cons(prefix, &lowered.instructions, 0)),
    ));
    header.declaration(Declaration::function(
        &bytes_name,
        Expr::name("List<BitVec(8)>"),
        Block::expression(Expr::call(
            "canonical_block_bytes",
            [Expr::nullary(instructions_name.clone())],
        )),
    ));
    header.declaration(Declaration::theorem(
        format!("{prefix}_byte_length"),
        Expr::equal(
            Expr::nullary(Expr::nullary(bytes_name.clone()).project("len")),
            Expr::nat(
                lowered
                    .instructions
                    .iter()
                    .map(|instruction| instruction.canonical_length())
                    .sum::<usize>() as u64,
            ),
        ),
        Block::expression(Expr::name("refl")),
    ));
    header.declaration(
        Declaration::theorem(
            format!("{prefix}_block_decodes"),
            Expr::call(
                "CanonicalBlockDecodes",
                [
                    Expr::nullary(instructions_name.clone()),
                    Expr::name("start"),
                ],
            ),
            Block::expression(Expr::call(
                "canonical_block_decodes",
                [
                    Expr::nullary(instructions_name.clone()),
                    Expr::name("start"),
                ],
            )),
        )
        .parameter(Parameter::explicit("start", Expr::name("BitVec(64)"))),
    );
    let mut text = header.render();
    text.push('\n');

    text.push_str(&format!(
        "fn {prefix}_state_0<M>(before: MachineState<M>) → MachineState<M> {{ before }}\n"
    ));
    for (index, instruction) in lowered.instructions.iter().copied().enumerate() {
        text.push_str(&format!(
            "fn {prefix}_state_{}<M>(before: MachineState<M>) → MachineState<M> {{\n\
             \x20   execute_normal(decoded_canonical({}), {prefix}_state_{index}(before))\n\
             }}\n",
            index + 1,
            instruction.render(),
        ));
    }
    text.push_str(&format!(
        "fn {after_name}<M>(before: MachineState<M>) → MachineState<M> {{\n\
         \x20   {prefix}_state_{}(before)\n\
         }}\n\n",
        lowered.instructions.len(),
    ));

    if let Some(congruence) = render_gpr_congruence(prefix, &lowered.instructions) {
        text.push_str(&congruence);
    }

    emit_execution_stages(prefix, &lowered.instructions, &mut text);
    text.push_str(&format!(
        "theorem {prefix}_block_is_allowed<M>(before: MachineState<M>):\n\
         \x20   ExecuteBlock({instructions_name}(), before, {after_name}(before))\n\
         {{\n\
         \x20   {prefix}_execute_from_0(before)\n\
         }}\n\n"
    ));

    text.push_str(&format!(
        "record {prefix}_Context<M>(values: Valuation(), before: MachineState<M>) {{\n\
{}\
         \x20   graph: RegionHolds({region_expr}, values),\n\
         }}\n\n",
        render_context_fields(region, input_registers),
    ));
    emit_graph_stages(prefix, &lowered.node_plans, &mut text);

    let final_placement = emit_placement_proofs(
        prefix,
        region,
        &lowered,
        &compact_parameters,
        &arguments,
        &mut text,
    );
    let result_expression = placed_expression(lowered.output_width, &format!("values({}, {})", lowered.output_width, lowered.output_id));
    text.push_str(&format!(
        "theorem {prefix}_refines_compact<M>({compact_parameters}):\n\
         \x20   read_gpr({}, {after_name}(before).gprs) = {result_expression}\n\
         {{\n\
         \x20   sym({final_placement})\n\
         }}\n\n\
         theorem {prefix}_refines_function_ir<M>({public_parameters}):\n\
         \x20   read_gpr({}, {after_name}(before).gprs) = {result_expression}\n\
         {{\n\
         \x20   {prefix}_refines_compact(values, before,\n\
         \x20       {prefix}_Context({context_arguments}))\n\
         }}\n\n",
        lowered.output_register.heather_name(),
        lowered.output_register.heather_name(),
    ));

    text.push_str(&format!(
        "theorem {prefix}_preserves_memory<M>(before: MachineState<M>):\n\
         \x20   {after_name}(before).memory = before.memory\n\
         {{ refl }}\n\n\
         fn {prefix}_final_rip(start: BitVec(64)) → BitVec(64) {{ {} }}\n\n\
         theorem {prefix}_advances_rip<M>(before: MachineState<M>):\n\
         \x20   {after_name}(before).rip = {prefix}_final_rip(before.rip)\n\
         {{ refl }}\n\n",
        render_final_rip("start", &lowered.instructions),
    ));

    let protected_arms = render_protected_arms(&lowered.clobbered);
    text.push_str(&format!(
        "fn {protected_name}(register: Gpr) → Type {{\n\
         \x20   match register {{ {protected_arms} }}\n\
         }}\n\n\
         theorem {prefix}_preserves_protected<M>(register: Gpr,\n\
         \x20   before: MachineState<M>): {protected_name}(register) →\n\
         \x20   read_gpr(register, {after_name}(before).gprs) =\n\
         \x20       read_gpr(register, before.gprs)\n\
         {{\n\
         \x20   match register {{\n{}\
         \x20   }}\n\
         }}\n\n",
        render_preservation_arms(&lowered.clobbered),
    ));

    text.push_str(&format!(
        "theorem {prefix}_artifact<M>({public_parameters}):\n\
         \x20   BlockArtifact<M>({instructions_name}(), before, {},\n\
         \x20       {result_expression}, {protected_name},\n\
         \x20       {prefix}_final_rip(before.rip))\n\
         {{\n\
         \x20   BlockArtifact(\n\
         \x20       after := {after_name}(before),\n\
         \x20       execution := {prefix}_block_is_allowed(before),\n\
         \x20       result_correct := {prefix}_refines_function_ir({public_arguments}),\n\
         \x20       memory_preserved := {prefix}_preserves_memory(before),\n\
         \x20       rip_correct := {prefix}_advances_rip(before),\n\
         \x20       registers_preserved := λ register protected =>\n\
         \x20           {prefix}_preserves_protected(register, before, protected))\n\
         }}\n",
        lowered.output_register.heather_name(),
    ));

    Ok(X86Emission { lowered, text })
}

fn common_parameters(region_expr: &str, region: &Region, registers: &[Gpr]) -> String {
    let mut parameters = vec![
        "values: Valuation()".to_string(),
        "before: MachineState<M>".to_string(),
    ];
    for ((index, port), register) in region.inputs.iter().enumerate().zip(registers) {
        parameters.push(format!(
            "input_{index}_placed: {}",
            placement_type(port.width, port.id, *register, "before"),
        ));
    }
    parameters.push(format!("graph: RegionHolds({region_expr}, values)"));
    parameters.join(",\n    ")
}

fn common_arguments(region: &Region) -> String {
    let mut arguments = vec!["values".to_string(), "before".to_string()];
    arguments.extend((0..region.inputs.len()).map(|index| format!("input_{index}_placed")));
    arguments.push("graph".to_string());
    arguments.join(", ")
}

fn render_context_fields(region: &Region, registers: &[Gpr]) -> String {
    let mut fields = String::new();
    for ((index, port), register) in region.inputs.iter().enumerate().zip(registers) {
        fields.push_str(&format!(
            "    input_{index}_placed: {},\n",
            placement_type(port.width, port.id, *register, "before"),
        ));
    }
    fields
}

fn compact_parameters(prefix: &str) -> String {
    format!(
        "values: Valuation(),\n    before: MachineState<M>,\n    context: {prefix}_Context<M>(values, before)"
    )
}

fn context_constructor_arguments(region: &Region) -> String {
    let mut arguments = (0..region.inputs.len())
        .map(|index| format!("input_{index}_placed"))
        .collect::<Vec<_>>();
    arguments.push("graph := graph".to_string());
    arguments.join(", ")
}

fn emit_instruction_spine(prefix: &str, instructions: &[Instruction], module: &mut Module) {
    module.declaration(Declaration::function(
        format!("{prefix}_instructions_{}", instructions.len()),
        Expr::name("List<Instruction>"),
        Block::expression(Expr::list([])),
    ));
    for index in (1..instructions.len()).rev() {
        module.declaration(Declaration::function(
            format!("{prefix}_instructions_{index}"),
            Expr::name("List<Instruction>"),
            Block::expression(instruction_cons(prefix, instructions, index)),
        ));
    }
}

fn instruction_cons(prefix: &str, instructions: &[Instruction], index: usize) -> Expr {
    Expr::call(
        "Cons",
        [
            instructions[index].heather_expr(),
            Expr::nullary(format!("{prefix}_instructions_{}", index + 1)),
        ],
    )
}

fn render_block_span_proof(instructions: &[Instruction]) -> String {
    let mut total = 0;
    let mut proof = "refl".to_string();
    let mut nested = "start".to_string();
    for (index, instruction) in instructions.iter().enumerate() {
        let length = instruction.canonical_length();
        if index != 0 {
            proof = format!(
                "trans(@bitvec::BitVec::cong_iterate_increment(64, {length},\n        {nested}, @bitvec::BitVec::iterate_increment(64, start, {total}), {proof}),\n        bitvec::BitVec::iterate_increment_compose(64, start, {total}, {length}))"
            );
        }
        nested = format!("@bitvec::BitVec::iterate_increment(64, {nested}, {length})");
        total += length;
    }
    proof
}

fn render_gpr_only_step(instruction: Instruction) -> Option<String> {
    match instruction {
        Instruction::MovRR {
            destination,
            source,
        } => Some(format!(
            "gpr_only_mov_rr({}, {})",
            destination.heather_name(),
            source.heather_name(),
        )),
        Instruction::MovRI {
            destination,
            immediate,
        } => Some(format!(
            "gpr_only_mov_ri({}, @bitvec::BitVec::ofNat(64, {}))",
            destination.heather_name(),
            immediate,
        )),
        Instruction::AddRR {
            destination,
            source,
        } => Some(format!(
            "gpr_only_add({}, {})",
            destination.heather_name(),
            source.heather_name(),
        )),
        Instruction::SubRR {
            destination,
            source,
        } => Some(format!(
            "gpr_only_sub({}, {})",
            destination.heather_name(),
            source.heather_name(),
        )),
        Instruction::AndRR {
            destination,
            source,
        } => Some(format!(
            "gpr_only_and({}, {})",
            destination.heather_name(),
            source.heather_name(),
        )),
        Instruction::OrRR {
            destination,
            source,
        } => Some(format!(
            "gpr_only_or({}, {})",
            destination.heather_name(),
            source.heather_name(),
        )),
        Instruction::XorRR {
            destination,
            source,
        } => Some(format!(
            "gpr_only_xor({}, {})",
            destination.heather_name(),
            source.heather_name(),
        )),
        Instruction::CmpRR { .. } | Instruction::SetBelow { .. } | Instruction::SetLess { .. } => {
            None
        }
    }
}

fn render_gpr_congruence(prefix: &str, instructions: &[Instruction]) -> Option<String> {
    let effects = instructions
        .iter()
        .copied()
        .map(render_gpr_only_step)
        .collect::<Option<Vec<_>>>()?;
    let proof = instructions
        .iter()
        .zip(effects)
        .enumerate()
        .fold("same".to_string(), |same, (index, (instruction, effect))| {
            format!(
                "execute_normal_gprs_congruent({},\n            {prefix}_state_{index}(left), {prefix}_state_{index}(right),\n            {effect}, {same})",
                instruction.render(),
            )
        });
    Some(format!(
        "theorem {prefix}_gprs_congruent<M>(left, right: MachineState<M>,\n\
         \x20   same: left.gprs = right.gprs):\n\
         \x20   {prefix}_after(left).gprs = {prefix}_after(right).gprs\n\
         {{\n\
         \x20   {proof}\n\
         }}\n\n"
    ))
}

fn instruction_suffix_name(prefix: &str, index: usize) -> String {
    if index == 0 {
        format!("{prefix}_instructions()")
    } else {
        format!("{prefix}_instructions_{index}()")
    }
}

fn emit_execution_stages(prefix: &str, instructions: &[Instruction], text: &mut String) {
    let final_index = instructions.len();
    text.push_str(&format!(
        "theorem {prefix}_execute_from_{final_index}<M>(before: MachineState<M>):\n\
         \x20   ExecuteBlock({prefix}_instructions_{final_index}(),\n\
         \x20       {prefix}_state_{final_index}(before), {prefix}_state_{final_index}(before))\n\
         {{ execute_block_nil({prefix}_state_{final_index}(before)) }}\n"
    ));
    for index in (0..instructions.len()).rev() {
        let suffix = instruction_suffix_name(prefix, index);
        let tail = instruction_suffix_name(prefix, index + 1);
        text.push_str(&format!(
            "theorem {prefix}_execute_from_{index}<M>(before: MachineState<M>):\n\
             \x20   ExecuteBlock({suffix}, {prefix}_state_{index}(before),\n\
             \x20       {prefix}_state_{final_index}(before))\n\
             {{\n\
             \x20   canonical_execute_block_cons({}, {tail},\n\
             \x20       {prefix}_state_{index}(before), {prefix}_state_{final_index}(before),\n\
             \x20       {prefix}_execute_from_{}(before))\n\
             }}\n",
            instructions[index].render(),
            index + 1,
        ));
    }
}

fn emit_graph_stages(prefix: &str, plans: &[NodePlan], text: &mut String) {
    let node_count = plans.len();
    text.push_str(&format!(
        "fn {prefix}_nodes_{node_count}() → List<Node> {{ [] }}\n"
    ));
    for index in (0..node_count).rev() {
        text.push_str(&format!(
            "fn {prefix}_nodes_{index}() → List<Node> {{\n\
             \x20   Cons({}, {prefix}_nodes_{}())\n\
             }}\n",
            plans[index].node.render(),
            index + 1,
        ));
    }
    text.push_str(&format!(
        "theorem {prefix}_graph_0<M>(values: Valuation(), before: MachineState<M>,\n\
         \x20   context: {prefix}_Context<M>(values, before)):\n\
         \x20   NodesHold(values, {prefix}_nodes_0())\n\
         {{ context.graph }}\n"
    ));
    for index in 0..node_count {
        text.push_str(&format!(
            "theorem {prefix}_graph_{}<M>(values: Valuation(), before: MachineState<M>,\n\
             \x20   context: {prefix}_Context<M>(values, before)):\n\
             \x20   NodesHold(values, {prefix}_nodes_{}())\n\
             {{ {prefix}_graph_{index}(values, before, context).right }}\n",
            index + 1,
            index + 1,
        ));
    }
    text.push('\n');
}

fn emit_placement_proofs(
    prefix: &str,
    region: &Region,
    lowered: &LoweredDag,
    parameters: &str,
    arguments: &str,
    text: &mut String,
) -> String {
    let widths = region.inputs.iter().copied().chain(region.nodes.iter().map(|node| node.output()))
        .map(|port| (port.id, port.width)).collect::<BTreeMap<_, _>>();
    let mut frame_facts = BTreeSet::new();
    let mut remaining = BTreeMap::<u64, usize>::new();
    for plan in &lowered.node_plans {
        match plan.node {
            SelectedNode::Binary(node) => {
                *remaining.entry(node.left).or_default() += 1;
                *remaining.entry(node.right).or_default() += 1;
            }
            SelectedNode::Comparison(node) => {
                *remaining.entry(node.left).or_default() += 1;
                *remaining.entry(node.right).or_default() += 1;
            }
            SelectedNode::Constant(_) => {}
        }
    }
    for output in &region.outputs {
        *remaining.entry(output.id).or_default() += 1;
    }
    let mut live = BTreeMap::<u64, (Gpr, String)>::new();
    let input_indices = region
        .inputs
        .iter()
        .enumerate()
        .map(|(index, port)| (port.id, index))
        .collect::<BTreeMap<_, _>>();
    for (index, (port, register)) in region
        .inputs
        .iter()
        .zip(&lowered.input_registers)
        .enumerate()
    {
        live.insert(
            port.id,
            (*register, format!("context.input_{index}_placed")),
        );
    }

    let mut instruction_index = 0;
    for plan in &lowered.node_plans {
        let before_index = instruction_index;
        instruction_index += plan.instructions.len();
        let after_index = instruction_index;
        let equation = format!(
            "{prefix}_graph_{}(values, before, context).left",
            plan.node_index,
        );
        let output_name = format!(
            "{prefix}_value_{}_after_node_{}",
            plan.node.output(),
            plan.node_index
        );
        if !matches!(plan.node, SelectedNode::Comparison(_)) {
            for (offset, instruction) in plan.instructions.iter().copied().enumerate() {
                emit_step_result_fact(prefix, before_index + offset, instruction, text);
            }
        }
        match plan.node {
            SelectedNode::Constant(node) => {
                debug_assert_eq!(plan.instructions.len(), 1);
                let equation = if node.width == 64 { equation } else {
                    format!("cong_fn<BitVec({}), BitVec(64)>(λ value => {}, {equation})", node.width, placed_expression(node.width, "value"))
                };
                text.push_str(&format!("theorem {output_name}<M>({parameters}): {} {{ trans({equation}, sym({prefix}_step_{before_index}_result({prefix}_state_{before_index}(before)))) }}\n",
                    placement_type(node.width, node.output, plan.destination, &format!("{prefix}_state_{after_index}(before)"))));
            }
            SelectedNode::Binary(node) if node.width != 64 => {
                let left_register = plan.left_register.expect("binary left");
                let right_register = plan.right_register.expect("binary right");
                let left_stored = &live[&node.left].1;
                let right_stored = &live[&node.right].1;
                let mut left_proof = placement_at_state(prefix, node.left, left_register, before_index, left_stored, &input_indices);
                let mut right_proof = placement_at_state(prefix, node.right, right_register, before_index, right_stored, &input_indices);
                let mut actual_left = left_register;
                let binary_index = after_index - 1;
                if plan.instructions.len() == 2 {
                    left_proof = format!("trans({left_proof}, sym({prefix}_step_{before_index}_result({prefix}_state_{before_index}(before))))");
                    let frame = emit_step_frame_fact(prefix, before_index, plan.instructions[0], right_register, &mut frame_facts, text);
                    right_proof = format!("trans({right_proof}, sym({frame}({prefix}_state_{before_index}(before))))");
                    actual_left = plan.destination;
                }
                let width = node.width;
                let op = node.operation.semantic_function();
                let logical_right = placed_expression(width, &format!("values({width}, {})", node.right));
                let machine_left = format!("read_gpr({}, {prefix}_state_{binary_index}(before).gprs)", actual_left.heather_name());
                let machine_right = format!("read_gpr({}, {prefix}_state_{binary_index}(before).gprs)", right_register.heather_name());
                let lifted = format!("sym({op}_zero_extend({width}, {}, values({width}, {}), values({width}, {})))", 64 - width, node.left, node.right);
                let left_agrees = format!("cong_fn<BitVec(64), BitVec(64)>(λ found => @{op}(64, found, {logical_right}), {left_proof})");
                let right_agrees = format!("cong_fn<BitVec(64), BitVec(64)>(λ found => @{op}(64, {machine_left}, found), {right_proof})");
                let agreement = format!("trans({lifted}, trans({left_agrees}, {right_agrees}))");
                let agreement = if plan.orientation == OperandOrientation::Reversed {
                    format!("trans({agreement}, {}(64, {machine_left}, {machine_right}))", node.operation.commutativity_theorem().unwrap())
                } else { agreement };
                let lifted_equation = format!("cong_fn<BitVec({width}), BitVec(64)>(λ value => {}, {equation})", placed_expression(width, "value"));
                text.push_str(&format!("theorem {output_name}<M>({parameters}): {} {{ trans({lifted_equation}, trans({agreement}, sym({prefix}_step_{binary_index}_result({prefix}_state_{binary_index}(before))))) }}\n",
                    placement_type(width, node.output, plan.destination, &format!("{prefix}_state_{after_index}(before)"))));
                consume_known_use(&mut remaining, node.left);
                consume_known_use(&mut remaining, node.right);
            }
            SelectedNode::Binary(node) => {
                let plan_left_register = plan.left_register.expect("binary left register");
                let plan_right_register = plan.right_register.expect("binary right register");
                let (&left_register, left_stored_proof) = live
                    .get(&node.left)
                    .map(|(register, proof)| (register, proof))
                    .expect("validated left placement");
                let (&right_register, right_stored_proof) = live
                    .get(&node.right)
                    .map(|(register, proof)| (register, proof))
                    .expect("validated right placement");
                let left_proof = placement_at_state(
                    prefix,
                    node.left,
                    left_register,
                    before_index,
                    left_stored_proof,
                    &input_indices,
                );
                let right_proof = placement_at_state(
                    prefix,
                    node.right,
                    right_register,
                    before_index,
                    right_stored_proof,
                    &input_indices,
                );
                let (
                    binary_before_index,
                    binary_left_register,
                    binary_left_proof,
                    binary_right_proof,
                ) = if plan.instructions.len() == 2 {
                    let move_after_index = before_index + 1;
                    let moved_name = format!(
                        "{prefix}_value_{}_moved_for_node_{}",
                        node.left, plan.node_index,
                    );
                    text.push_str(&format!(
                    "theorem {moved_name}<M>({parameters}):\n\
                     \x20   ValuePlaced(values, {}, {}, {prefix}_state_{move_after_index}(before))\n\
                     {{\n\
                     \x20   placed_after_move(values, {}, {}, {},\n\
                     \x20       {prefix}_state_{before_index}(before),\n\
                     \x20       {prefix}_state_{move_after_index}(before), {left_proof},\n\
                     \x20       {prefix}_step_{before_index}_result(\n\
                     \x20           {prefix}_state_{before_index}(before)))\n\
                     }}\n",
                    node.left,
                    plan.destination.heather_name(),
                    node.left,
                    plan_left_register.heather_name(),
                    plan.destination.heather_name(),
                ));
                    let right_after_move = if input_indices.contains_key(&node.right) {
                        placement_at_state(
                            prefix,
                            node.right,
                            plan_right_register,
                            move_after_index,
                            right_stored_proof,
                            &input_indices,
                        )
                    } else {
                        let right_name = format!(
                            "{prefix}_value_{}_before_add_node_{}",
                            node.right, plan.node_index,
                        );
                        let right_frame = emit_step_frame_fact(
                            prefix,
                            before_index,
                            plan.instructions[0],
                            plan_right_register,
                            &mut frame_facts,
                            text,
                        );
                        text.push_str(&format!(
                        "theorem {right_name}<M>({parameters}):\n\
                         \x20   ValuePlaced(values, {}, {}, {prefix}_state_{move_after_index}(before))\n\
                         {{\n\
                         \x20   placed_after_frame(values, {}, {},\n\
                         \x20       {prefix}_state_{before_index}(before),\n\
                         \x20       {prefix}_state_{move_after_index}(before), {right_proof},\n\
                         \x20       {right_frame}({prefix}_state_{before_index}(before)))\n\
                         }}\n",
                        node.right,
                        plan_right_register.heather_name(),
                        node.right,
                        plan_right_register.heather_name(),
                    ));
                        format!("{right_name}({arguments})")
                    };
                    (
                        move_after_index,
                        plan.destination,
                        format!("{moved_name}({arguments})"),
                        right_after_move,
                    )
                } else {
                    debug_assert_eq!(plan.instructions.len(), 1);
                    (
                        before_index,
                        plan_left_register,
                        left_proof.clone(),
                        right_proof.clone(),
                    )
                };
                let (machine_left_value, machine_right_value, placement_equation) =
                    match plan.orientation {
                        OperandOrientation::Original => (node.left, node.right, equation.clone()),
                        OperandOrientation::Reversed => {
                            let commuted_name =
                                format!("{prefix}_node_{}_commuted_equation", plan.node_index,);
                            text.push_str(&format!(
                                "theorem {commuted_name}<M>({parameters}):\n\
                     \x20   values(64, {}) = @{}(64, values(64, {}), values(64, {}))\n\
                     {{\n\
                     \x20   trans({equation}, {}(64, values(64, {}), values(64, {})))\n\
                     }}\n",
                                node.output,
                                node.operation.semantic_function(),
                                node.right,
                                node.left,
                                node.operation
                                    .commutativity_theorem()
                                    .expect("only commutative operations reverse"),
                                node.left,
                                node.right,
                            ));
                            (
                                node.right,
                                node.left,
                                format!("{commuted_name}({arguments})"),
                            )
                        }
                    };
                let placement_head = format!(
                    "placed_after_binary(values, {}, {}, {}, @{}(64, ·, ·)",
                    node.output,
                    machine_left_value,
                    machine_right_value,
                    node.operation.semantic_function(),
                );
                let (
                    binary_left_register,
                    binary_right_register,
                    binary_left_proof,
                    binary_right_proof,
                ) = match plan.orientation {
                    OperandOrientation::Original => (
                        binary_left_register,
                        plan_right_register,
                        binary_left_proof,
                        binary_right_proof,
                    ),
                    OperandOrientation::Reversed => (
                        plan_right_register,
                        binary_left_register,
                        binary_right_proof,
                        binary_left_proof,
                    ),
                };
                text.push_str(&format!(
            "theorem {output_name}<M>({parameters}):\n\
             \x20   ValuePlaced(values, {}, {}, {prefix}_state_{after_index}(before))\n\
             {{\n\
             \x20   {placement_head}, {}, {}, {},\n\
             \x20       {prefix}_state_{binary_before_index}(before), {prefix}_state_{after_index}(before),\n\
             \x20       {placement_equation}, {binary_left_proof}, {binary_right_proof},\n\
             \x20       {prefix}_step_{binary_before_index}_result(\n\
             \x20           {prefix}_state_{binary_before_index}(before)))\n\
             }}\n",
            node.output,
            plan.destination.heather_name(),
            binary_left_register.heather_name(),
            binary_right_register.heather_name(),
            plan.destination.heather_name(),
        ));

                consume_known_use(&mut remaining, node.left);
                consume_known_use(&mut remaining, node.right);
            }
            SelectedNode::Comparison(node) => {
                debug_assert_eq!(plan.instructions.len(), 3);
                let left_register = plan.left_register.expect("comparison left register");
                let right_register = plan.right_register.expect("comparison right register");
                let (_, left_stored_proof) = live
                    .get(&node.left)
                    .expect("validated comparison left placement");
                let (_, right_stored_proof) = live
                    .get(&node.right)
                    .expect("validated comparison right placement");
                let compare_state = before_index + 1;
                let mut advance_operand =
                    |value: u64,
                     register: Gpr,
                     stored_proof: &str,
                     side: &str,
                     text: &mut String| {
                        if input_indices.contains_key(&value) {
                            return placement_at_state(
                                prefix,
                                value,
                                register,
                                compare_state,
                                stored_proof,
                                &input_indices,
                            );
                        }
                        let frame = emit_step_frame_fact(
                            prefix,
                            before_index,
                            plan.instructions[0],
                            register,
                            &mut frame_facts,
                            text,
                        );
                        let name =
                            format!("{prefix}_comparison_{}_{}_at_cmp", plan.node_index, side,);
                        text.push_str(&format!("theorem {name}<M>({parameters}): {} {{ trans({stored_proof}, sym({frame}({prefix}_state_{before_index}(before)))) }}\n",
                            placement_type(widths[&value], value, register, &format!("{prefix}_state_{compare_state}(before)"))));
                        format!("{name}({arguments})")
                    };
                let left_proof =
                    advance_operand(node.left, left_register, left_stored_proof, "left", text);
                let right_proof = advance_operand(
                    node.right,
                    right_register,
                    right_stored_proof,
                    "right",
                    text,
                );
                let condition = match node.operation {
                    ComparisonOperation::UnsignedLessThan => "@bitvec::BitVec::unsigned_lt_bit",
                    ComparisonOperation::SignedLessThan => "@bitvec::BitVec::signed_lt_bit",
                };
                let result_name = format!("{prefix}_comparison_{}_result", plan.node_index);
                text.push_str(&format!(
                    "theorem {result_name}<M>(before: MachineState<M>):\n\
                     \x20   read_gpr({}, {prefix}_state_{after_index}(before).gprs) =\n\
                     \x20       @bitvec::BitVec::zero_extend(1, 63, bitvec::BitVec::ofBool(\n\
                     \x20           {condition}(64, read_gpr({}, {prefix}_state_{compare_state}(before).gprs),\n\
                     \x20               read_gpr({}, {prefix}_state_{compare_state}(before).gprs))))\n\
                     {{ refl }}\n",
                    plan.destination.heather_name(),
                    left_register.heather_name(),
                    right_register.heather_name(),
                ));
                if node.operand_width == 64 {
                    text.push_str(&format!(
                        "theorem {output_name}<M>({parameters}):\n\
                         \x20   BitValuePlaced(values, {}, {}, {prefix}_state_{after_index}(before))\n\
                         {{\n\
                         \x20   placed_after_comparison(values, {}, {}, {}, {condition}(64, ·, ·),\n\
                         \x20       {}, {}, {}, {prefix}_state_{compare_state}(before),\n\
                         \x20       {prefix}_state_{after_index}(before), {equation}, {left_proof}, {right_proof},\n\
                         \x20       {result_name}(before))\n\
                         }}\n",
                        node.output,
                        plan.destination.heather_name(),
                        node.output,
                        node.left,
                        node.right,
                        left_register.heather_name(),
                        right_register.heather_name(),
                        plan.destination.heather_name(),
                    ));
                } else {
                    let logical_right = placed_expression(node.operand_width, &format!("values({}, {})", node.operand_width, node.right));
                    let machine_left = format!("read_gpr({}, {prefix}_state_{compare_state}(before).gprs)", left_register.heather_name());
                    let lifted = format!("sym(bitvec::BitVec::unsigned_lt_zero_extend({}, {}, values({}, {}), values({}, {})))", node.operand_width, 64 - node.operand_width, node.operand_width, node.left, node.operand_width, node.right);
                    let left_agrees = format!("cong_fn<BitVec(64), bool::Bool>(λ found => {condition}(64, found, {logical_right}), {left_proof})");
                    let right_agrees = format!("cong_fn<BitVec(64), bool::Bool>(λ found => {condition}(64, {machine_left}, found), {right_proof})");
                    let agreement = format!("trans({lifted}, trans({left_agrees}, {right_agrees}))");
                    text.push_str(&format!("theorem {output_name}<M>({parameters}): BitValuePlaced(values, {}, {}, {prefix}_state_{after_index}(before)) {{ trans(cong_fn<BitVec(1), BitVec(64)>(λ value => @bitvec::BitVec::zero_extend(1, 63, value), {equation}), trans(cong_fn<bool::Bool, BitVec(64)>(λ bit => @bitvec::BitVec::zero_extend(1, 63, bitvec::BitVec::ofBool(bit)), {agreement}), sym({result_name}(before)))) }}\n", node.output, plan.destination.heather_name()));
                }
                consume_known_use(&mut remaining, node.left);
                consume_known_use(&mut remaining, node.right);
            }
        }
        let mut next_live = BTreeMap::new();
        for (&value, &(register, ref proof)) in &live {
            if remaining.get(&value).copied().unwrap_or(0) == 0 {
                continue;
            }
            if input_indices.contains_key(&value) {
                next_live.insert(value, (register, proof.clone()));
                continue;
            }
            let mut frame_proof = proof.clone();
            for step in 0..plan.instructions.len() {
                let step_before = before_index + step;
                let step_after = step_before + 1;
                let frame_fact = emit_step_frame_fact(
                    prefix,
                    step_before,
                    plan.instructions[step],
                    register,
                    &mut frame_facts,
                    text,
                );
                let frame_name = format!(
                    "{prefix}_value_{value}_after_node_{}_step_{}",
                    plan.node_index,
                    step + 1,
                );
                text.push_str(&format!("theorem {frame_name}<M>({parameters}): {} {{ trans({frame_proof}, sym({frame_fact}({prefix}_state_{step_before}(before)))) }}\n",
                    placement_type(widths[&value], value, register, &format!("{prefix}_state_{step_after}(before)"))));
                frame_proof = format!("{frame_name}({arguments})");
            }
            next_live.insert(value, (register, frame_proof));
        }
        if remaining.get(&plan.node.output()).copied().unwrap_or(0) > 0 {
            next_live.insert(
                plan.node.output(),
                (plan.destination, format!("{output_name}({arguments})")),
            );
        }
        live = next_live;
    }

    let (source_register, source_proof) = live
        .get(&lowered.output_id)
        .expect("the sole output remains live");
    if instruction_index == lowered.instructions.len() {
        source_proof.clone()
    } else {
        debug_assert_eq!(instruction_index + 1, lowered.instructions.len());
        emit_step_result_fact(
            prefix,
            instruction_index,
            lowered.instructions[instruction_index],
            text,
        );
        let final_name = format!("{prefix}_output_placed");
        let _ = source_register;
        text.push_str(&format!("theorem {final_name}<M>({parameters}): {} {{ trans({source_proof}, sym({prefix}_step_{instruction_index}_result({prefix}_state_{instruction_index}(before)))) }}\n",
            placement_type(lowered.output_width, lowered.output_id, lowered.output_register, &format!("{prefix}_state_{}(before)", lowered.instructions.len()))));
        format!("{final_name}({arguments})")
    }
}

fn placement_at_state(
    _prefix: &str,
    value: u64,
    register: Gpr,
    state: usize,
    stored_proof: &str,
    input_indices: &BTreeMap<u64, usize>,
) -> String {
    let Some(&input_index) = input_indices.get(&value) else {
        return stored_proof.to_string();
    };
    if state == 0 {
        return format!("context.input_{input_index}_placed");
    }
    format!("trans(context.input_{input_index}_placed, equality_refl(read_gpr({}, before.gprs)))", register.heather_name())
}

fn consume_known_use(remaining: &mut BTreeMap<u64, usize>, value: u64) {
    *remaining.get_mut(&value).expect("validated use count") -= 1;
}

fn emit_step_result_fact(prefix: &str, step: usize, instruction: Instruction, text: &mut String) {
    let (destination, operation) = match instruction {
        Instruction::MovRR {
            destination,
            source,
        } => (
            destination,
            format!("read_gpr({}, state.gprs)", source.heather_name()),
        ),
        Instruction::MovRI {
            destination,
            immediate,
        } => (destination, format!("@bitvec::BitVec::ofNat(64, {immediate})")),
        Instruction::AddRR {
            destination,
            source,
        } => render_binary_result(BinaryOperation::Add, destination, source),
        Instruction::SubRR {
            destination,
            source,
        } => render_binary_result(BinaryOperation::Sub, destination, source),
        Instruction::AndRR {
            destination,
            source,
        } => render_binary_result(BinaryOperation::BitAnd, destination, source),
        Instruction::OrRR {
            destination,
            source,
        } => render_binary_result(BinaryOperation::BitOr, destination, source),
        Instruction::XorRR {
            destination,
            source,
        } => render_binary_result(BinaryOperation::BitXor, destination, source),
        Instruction::CmpRR { .. } | Instruction::SetBelow { .. } | Instruction::SetLess { .. } => {
            panic!("comparison instructions use their composed result fact")
        }
    };
    text.push_str(&format!(
        "theorem {prefix}_step_{step}_result<M>(state: MachineState<M>):\n\
         \x20   read_gpr({}, execute_normal(decoded_canonical({}), state).gprs) =\n\
         \x20       {operation}\n\
         {{ refl }}\n",
        destination.heather_name(),
        instruction.render(),
    ));
}

fn render_binary_result(
    operation: BinaryOperation,
    destination: Gpr,
    source: Gpr,
) -> (Gpr, String) {
    (
        destination,
        format!(
            "@{}(64, read_gpr({}, state.gprs), read_gpr({}, state.gprs))",
            operation.semantic_function(),
            destination.heather_name(),
            source.heather_name(),
        ),
    )
}

fn emit_step_frame_fact(
    prefix: &str,
    step: usize,
    instruction: Instruction,
    register: Gpr,
    emitted: &mut BTreeSet<(usize, Gpr)>,
    text: &mut String,
) -> String {
    debug_assert_ne!(instruction.destination(), Some(register));
    let name = format!("{prefix}_step_{step}_preserves_{}", register.heather_name());
    if emitted.insert((step, register)) {
        text.push_str(&format!(
            "theorem {name}<M>(state: MachineState<M>):\n\
             \x20   read_gpr({}, execute_normal(decoded_canonical({}), state).gprs) =\n\
             \x20       read_gpr({}, state.gprs)\n\
             {{ refl }}\n",
            register.heather_name(),
            instruction.render(),
            register.heather_name(),
        ));
    }
    name
}

fn render_final_rip(start: &str, instructions: &[Instruction]) -> String {
    instructions
        .iter()
        .fold(start.to_string(), |rip, instruction| {
            format!("next_rip({rip}, {})", instruction.canonical_length())
        })
}

fn render_protected_arms(clobbered: &BTreeSet<Gpr>) -> String {
    let mut arms = clobbered
        .iter()
        .map(|register| format!("{} => False", register.heather_name()))
        .collect::<Vec<_>>();
    arms.push("_ => True".to_string());
    arms.join(", ")
}

fn render_preservation_arms(clobbered: &BTreeSet<Gpr>) -> String {
    let mut arms = clobbered
        .iter()
        .map(|register| {
            format!(
                "         {} => protected ⊢ false_elim(protected),",
                register.heather_name(),
            )
        })
        .collect::<Vec<_>>();
    arms.push("         _ => protected ⊢ refl,".to_string());
    arms.join("\n")
}

fn selected_node(node: Node, node_index: usize) -> Result<SelectedNode, LoweringError> {
    match node {
        Node::Const {
            width,
            output,
            value,
        } => Ok(SelectedNode::Constant(ConstantNode {
            width,
            output,
            value,
        })),
        Node::Add {
            width,
            output,
            left,
            right,
        } => Ok(SelectedNode::Binary(BinaryNode {
            operation: BinaryOperation::Add,
            width,
            output,
            left,
            right,
        })),
        Node::Sub {
            width,
            output,
            left,
            right,
        } => Ok(SelectedNode::Binary(BinaryNode {
            operation: BinaryOperation::Sub,
            width,
            output,
            left,
            right,
        })),
        Node::BitAnd {
            width,
            output,
            left,
            right,
        } => Ok(SelectedNode::Binary(BinaryNode {
            operation: BinaryOperation::BitAnd,
            width,
            output,
            left,
            right,
        })),
        Node::BitOr {
            width,
            output,
            left,
            right,
        } => Ok(SelectedNode::Binary(BinaryNode {
            operation: BinaryOperation::BitOr,
            width,
            output,
            left,
            right,
        })),
        Node::BitXor {
            width,
            output,
            left,
            right,
        } => Ok(SelectedNode::Binary(BinaryNode {
            operation: BinaryOperation::BitXor,
            width,
            output,
            left,
            right,
        })),
        Node::UnsignedLessThan {
            width,
            output,
            left,
            right,
        } => Ok(SelectedNode::Comparison(ComparisonNode {
            operation: ComparisonOperation::UnsignedLessThan,
            operand_width: width,
            output,
            left,
            right,
        })),
        Node::SignedLessThan {
            width,
            output,
            left,
            right,
        } => Ok(SelectedNode::Comparison(ComparisonNode {
            operation: ComparisonOperation::SignedLessThan,
            operand_width: width,
            output,
            left,
            right,
        })),
        _ => Err(LoweringError::UnsupportedOperation { node_index }),
    }
}

fn binary_instruction(operation: BinaryOperation, destination: Gpr, source: Gpr) -> Instruction {
    match operation {
        BinaryOperation::Add => Instruction::AddRR {
            destination,
            source,
        },
        BinaryOperation::Sub => Instruction::SubRR {
            destination,
            source,
        },
        BinaryOperation::BitAnd => Instruction::AndRR {
            destination,
            source,
        },
        BinaryOperation::BitOr => Instruction::OrRR {
            destination,
            source,
        },
        BinaryOperation::BitXor => Instruction::XorRR {
            destination,
            source,
        },
    }
}

fn require_placement_width(value: u64, width: u64) -> Result<(), LoweringError> {
    if width <= 64 { Ok(()) } else { Err(LoweringError::UnsupportedWidth { value, width }) }
}

fn placed_expression(width: u64, value: &str) -> String {
    if width == 64 { value.into() } else { format!("@bitvec::BitVec::zero_extend({width}, {}, {value})", 64 - width) }
}

fn placement_type(width: u64, id: u64, register: Gpr, state: &str) -> String {
    format!("{} = read_gpr({}, {state}.gprs)", placed_expression(width, &format!("values({width}, {id})")), register.heather_name())
}

fn require_width(value: u64, width: u64) -> Result<(), LoweringError> {
    if width == 64 {
        Ok(())
    } else {
        Err(LoweringError::UnsupportedWidth { value, width })
    }
}

fn last_use_in_node(uses: &BTreeMap<u64, usize>, value: u64, left: u64, right: u64) -> bool {
    let uses_here = usize::from(left == value) + usize::from(right == value);
    uses.get(&value).copied().unwrap_or(0) == uses_here
}

fn consume_use(uses: &mut BTreeMap<u64, usize>, value: u64) -> Result<(), LoweringError> {
    let Some(remaining) = uses.get_mut(&value) else {
        return Err(LoweringError::UndefinedValue(value));
    };
    *remaining = remaining
        .checked_sub(1)
        .ok_or(LoweringError::UndefinedValue(value))?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::function_ir_cert::{BlockArgument, ConditionalJoinRegion, ControlRegion, Port};

    #[test]
    fn max_plus_lowers_to_edge_moves_and_one_shared_continuation() {
        let p = |id, width| Port { id, width };
        let branch_inputs = vec![p(0, 64), p(1, 64), p(2, 64)];
        let graph = ControlRegion {
            prefix: Region {
                inputs: branch_inputs.clone(),
                nodes: vec![Node::UnsignedLessThan {
                    width: 64,
                    output: 3,
                    left: 0,
                    right: 1,
                }],
                outputs: vec![p(3, 1)],
            },
            join: ConditionalJoinRegion {
                inputs: vec![p(0, 64), p(1, 64), p(2, 64), p(3, 1)],
                condition: 3,
                arguments: branch_inputs.clone(),
                when_true: Region {
                    inputs: branch_inputs.clone(),
                    nodes: vec![],
                    outputs: vec![p(1, 64), p(2, 64)],
                },
                true_arguments: vec![
                    BlockArgument {
                        width: 64,
                        value: 1,
                        parameter: 4,
                    },
                    BlockArgument {
                        width: 64,
                        value: 2,
                        parameter: 5,
                    },
                ],
                when_false: Region {
                    inputs: branch_inputs,
                    nodes: vec![],
                    outputs: vec![p(0, 64), p(2, 64)],
                },
                false_arguments: vec![
                    BlockArgument {
                        width: 64,
                        value: 0,
                        parameter: 4,
                    },
                    BlockArgument {
                        width: 64,
                        value: 2,
                        parameter: 5,
                    },
                ],
                continuation: Region {
                    inputs: vec![p(4, 64), p(5, 64)],
                    nodes: vec![Node::Add {
                        width: 64,
                        output: 6,
                        left: 4,
                        right: 5,
                    }],
                    outputs: vec![p(6, 64)],
                },
            },
        };
        let lowered = lower_control_region(
            &graph,
            &[Gpr::Rdi, Gpr::Rsi, Gpr::Rdx],
            Gpr::Rcx,
            &[Gpr::R8, Gpr::Rdx],
            &[Gpr::Rax],
            Gpr::Rax,
        )
        .unwrap();
        assert_eq!(
            lowered.when_true_transfer,
            vec![Instruction::MovRR {
                destination: Gpr::R8,
                source: Gpr::Rsi
            }]
        );
        assert_eq!(
            lowered.when_false_transfer,
            vec![Instruction::MovRR {
                destination: Gpr::R8,
                source: Gpr::Rdi
            }]
        );
        assert_eq!(
            lowered.continuation.instructions,
            vec![
                Instruction::MovRR {
                    destination: Gpr::Rax,
                    source: Gpr::R8
                },
                Instruction::AddRR {
                    destination: Gpr::Rax,
                    source: Gpr::Rdx
                },
            ]
        );
    }

    fn sum4(left_first: bool) -> Region {
        let left = Node::Add {
            width: 64,
            output: 4,
            left: 0,
            right: 1,
        };
        let right = Node::Add {
            width: 64,
            output: 5,
            left: 2,
            right: 3,
        };
        Region {
            inputs: (0..4).map(|id| Port { id, width: 64 }).collect(),
            nodes: if left_first {
                vec![
                    left,
                    right,
                    Node::Add {
                        width: 64,
                        output: 6,
                        left: 4,
                        right: 5,
                    },
                ]
            } else {
                vec![
                    right,
                    left,
                    Node::Add {
                        width: 64,
                        output: 6,
                        left: 4,
                        right: 5,
                    },
                ]
            },
            outputs: vec![Port { id: 6, width: 64 }],
        }
    }

    #[test]
    fn add64_selects_one_move_and_one_destructive_add() {
        let region = Region {
            inputs: vec![Port { id: 0, width: 64 }, Port { id: 1, width: 64 }],
            nodes: vec![Node::Add {
                width: 64,
                output: 2,
                left: 0,
                right: 1,
            }],
            outputs: vec![Port { id: 2, width: 64 }],
        };
        let lowered = lower_dag(&region, &[Gpr::Rdi, Gpr::Rsi], &[Gpr::Rax], Gpr::Rax).unwrap();
        assert_eq!(
            lowered.instructions,
            vec![
                Instruction::MovRR {
                    destination: Gpr::Rax,
                    source: Gpr::Rdi
                },
                Instruction::AddRR {
                    destination: Gpr::Rax,
                    source: Gpr::Rsi
                },
            ]
        );
    }

    #[test]
    fn constant_and_add_use_real_lengths_and_one_temporary() {
        let region = Region {
            inputs: vec![Port { id: 0, width: 64 }],
            nodes: vec![
                Node::Const {
                    width: 64,
                    output: 1,
                    value: u64::MAX,
                },
                Node::Add {
                    width: 64,
                    output: 2,
                    left: 0,
                    right: 1,
                },
            ],
            outputs: vec![Port { id: 2, width: 64 }],
        };
        let lowered = lower_dag(&region, &[Gpr::Rdi], &[Gpr::Rax], Gpr::Rax).unwrap();
        assert_eq!(
            lowered.instructions,
            vec![
                Instruction::MovRI {
                    destination: Gpr::Rax,
                    immediate: u64::MAX,
                },
                Instruction::AddRR {
                    destination: Gpr::Rax,
                    source: Gpr::Rdi,
                },
            ]
        );
        assert_eq!(
            lowered
                .instructions
                .iter()
                .map(|instruction| instruction.canonical_length())
                .sum::<usize>(),
            13,
        );
        assert_eq!(
            render_final_rip("start", &lowered.instructions),
            "next_rip(next_rip(start, 10), 3)"
        );
    }

    #[test]
    fn comparisons_use_a_safe_zero_cmp_setcc_sequence() {
        for (node, final_instruction) in [
            (
                Node::UnsignedLessThan {
                    width: 64,
                    output: 2,
                    left: 0,
                    right: 1,
                },
                Instruction::SetBelow {
                    destination: LowByteGpr::Al,
                },
            ),
            (
                Node::SignedLessThan {
                    width: 64,
                    output: 2,
                    left: 0,
                    right: 1,
                },
                Instruction::SetLess {
                    destination: LowByteGpr::Al,
                },
            ),
        ] {
            let region = Region {
                inputs: vec![Port { id: 0, width: 64 }, Port { id: 1, width: 64 }],
                nodes: vec![node],
                outputs: vec![Port { id: 2, width: 1 }],
            };
            let lowered = lower_dag(&region, &[Gpr::Rdi, Gpr::Rsi], &[Gpr::Rax], Gpr::Rax).unwrap();
            assert_eq!(
                lowered.instructions,
                vec![
                    Instruction::MovRI {
                        destination: Gpr::Rax,
                        immediate: 0,
                    },
                    Instruction::CmpRR {
                        left: Gpr::Rdi,
                        right: Gpr::Rsi,
                    },
                    final_instruction,
                ]
            );
            assert_eq!(lowered.output_width, 1);
            assert_eq!(
                lowered
                    .instructions
                    .iter()
                    .map(|instruction| instruction.canonical_length())
                    .sum::<usize>(),
                16,
            );
        }
    }

    #[test]
    fn comparison_declines_an_unsafe_byte_register_pool() {
        let region = Region {
            inputs: vec![Port { id: 0, width: 64 }, Port { id: 1, width: 64 }],
            nodes: vec![Node::UnsignedLessThan {
                width: 64,
                output: 2,
                left: 0,
                right: 1,
            }],
            outputs: vec![Port { id: 2, width: 1 }],
        };
        assert_eq!(
            lower_dag(&region, &[Gpr::Rdi, Gpr::Rsi], &[Gpr::R8], Gpr::R8),
            Err(LoweringError::NoSafeByteRegister { node_index: 0 }),
        );
    }

    #[test]
    fn structured_conditional_lowers_independent_selected_leaves() {
        let branch = |node| Region {
            inputs: vec![Port { id: 0, width: 64 }, Port { id: 1, width: 64 }],
            nodes: vec![node],
            outputs: vec![Port { id: 2, width: 64 }],
        };
        let region = StructuredRegion::Conditional {
            inputs: vec![
                Port { id: 0, width: 64 },
                Port { id: 1, width: 64 },
                Port { id: 3, width: 1 },
            ],
            condition: 3,
            arguments: vec![Port { id: 0, width: 64 }, Port { id: 1, width: 64 }],
            outputs: vec![Port { id: 2, width: 64 }],
            when_true: Box::new(StructuredRegion::Dataflow(branch(Node::Add {
                width: 64,
                output: 2,
                left: 0,
                right: 1,
            }))),
            when_false: Box::new(StructuredRegion::Dataflow(branch(Node::Sub {
                width: 64,
                output: 2,
                left: 0,
                right: 1,
            }))),
        };
        let lowered = lower_conditional(
            &region,
            &[Gpr::Rdi, Gpr::Rsi, Gpr::Rdx],
            &[Gpr::Rax],
            Gpr::Rax,
        )
        .unwrap();
        assert_eq!(lowered.condition_register, Gpr::Rdx);
        assert_eq!(
            lowered.when_true.instructions,
            vec![
                Instruction::MovRR {
                    destination: Gpr::Rax,
                    source: Gpr::Rdi,
                },
                Instruction::AddRR {
                    destination: Gpr::Rax,
                    source: Gpr::Rsi,
                },
            ],
        );
        assert_eq!(
            lowered.when_false.instructions.last(),
            Some(&Instruction::SubRR {
                destination: Gpr::Rax,
                source: Gpr::Rsi,
            }),
        );
    }

    #[test]
    fn sum4_reuses_the_operand_already_in_the_requested_output_register() {
        let inputs = [Gpr::Rdi, Gpr::Rsi, Gpr::Rdx, Gpr::Rcx];
        let temporaries = [Gpr::Rax, Gpr::R8];
        for left_first in [true, false] {
            let lowered = lower_dag(&sum4(left_first), &inputs, &temporaries, Gpr::Rax).unwrap();
            let plan = &lowered.node_plans[2];
            assert_eq!(plan.reused_value, Some(if left_first { 4 } else { 5 }));
            assert_eq!(
                plan.orientation,
                if left_first {
                    OperandOrientation::Original
                } else {
                    OperandOrientation::Reversed
                }
            );
            assert_eq!(lowered.instructions.len(), 5);
            assert_eq!(
                lowered.instructions.last(),
                Some(&Instruction::AddRR {
                    destination: Gpr::Rax,
                    source: Gpr::R8,
                })
            );
        }
    }

    #[test]
    fn a_chain_reuses_one_temporary_without_pressure_growth() {
        let mut region = Region {
            inputs: vec![Port { id: 0, width: 64 }, Port { id: 1, width: 64 }],
            nodes: Vec::new(),
            outputs: Vec::new(),
        };
        let mut left = 0;
        for output in 2..102 {
            region.nodes.push(Node::Add {
                width: 64,
                output,
                left,
                right: 1,
            });
            left = output;
        }
        region.outputs.push(Port {
            id: left,
            width: 64,
        });
        let lowered = lower_dag(&region, &[Gpr::Rdi, Gpr::Rsi], &[Gpr::Rax], Gpr::Rax).unwrap();
        assert_eq!(lowered.instructions.len(), 101);
        assert!(lowered.node_plans[1..]
            .iter()
            .all(|step| step.reused_value.is_some()));
    }

    #[test]
    fn independent_live_results_report_register_pressure() {
        let error = lower_dag(
            &sum4(true),
            &[Gpr::Rdi, Gpr::Rsi, Gpr::Rdx, Gpr::Rcx],
            &[Gpr::Rax],
            Gpr::Rax,
        )
        .unwrap_err();
        assert_eq!(
            error,
            LoweringError::RegisterPressure {
                node_index: 1,
                live_temporaries: 1,
            }
        );
    }

    fn right_temporary_region(final_node: Node) -> Region {
        Region {
            inputs: (0..3).map(|id| Port { id, width: 64 }).collect(),
            nodes: vec![
                Node::BitAnd {
                    width: 64,
                    output: 3,
                    left: 1,
                    right: 2,
                },
                final_node,
            ],
            outputs: vec![Port { id: 4, width: 64 }],
        }
    }

    #[test]
    fn dying_right_operand_is_reused_for_each_proven_commutative_operation() {
        let final_nodes = [
            Node::Add {
                width: 64,
                output: 4,
                left: 0,
                right: 3,
            },
            Node::BitAnd {
                width: 64,
                output: 4,
                left: 0,
                right: 3,
            },
            Node::BitOr {
                width: 64,
                output: 4,
                left: 0,
                right: 3,
            },
            Node::BitXor {
                width: 64,
                output: 4,
                left: 0,
                right: 3,
            },
        ];
        for final_node in final_nodes {
            let region = right_temporary_region(final_node);
            let lowered = lower_dag(
                &region,
                &[Gpr::Rdi, Gpr::Rsi, Gpr::Rdx],
                &[Gpr::Rax],
                Gpr::Rax,
            )
            .unwrap();
            assert_eq!(lowered.instructions.len(), 3);
            assert_eq!(lowered.node_plans[1].reused_value, Some(3));
            assert_eq!(
                lowered.node_plans[1].orientation,
                OperandOrientation::Reversed
            );
            assert_eq!(lowered.instructions[2].destination(), Some(Gpr::Rax));
        }
    }

    #[test]
    fn subtraction_never_reverses_to_reuse_its_right_operand() {
        let region = right_temporary_region(Node::Sub {
            width: 64,
            output: 4,
            left: 0,
            right: 3,
        });
        let error = lower_dag(
            &region,
            &[Gpr::Rdi, Gpr::Rsi, Gpr::Rdx],
            &[Gpr::Rax],
            Gpr::Rax,
        )
        .unwrap_err();
        assert_eq!(
            error,
            LoweringError::RegisterPressure {
                node_index: 1,
                live_temporaries: 1,
            }
        );
    }
}
