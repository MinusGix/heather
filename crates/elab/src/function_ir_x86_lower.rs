//! Untrusted spill-free x86 selection and register assignment for the current
//! pure FunctionIR 64-bit binary-ALU fragment. Proof emission consumes this explicit plan;
//! neither the allocator nor the plan is trusted by the kernel.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::function_ir_cert::{Node, Region};

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
            BinaryOperation::Add => "bitvec::add",
            BinaryOperation::Sub => "bitvec::sub",
            BinaryOperation::BitAnd => "bitvec::band",
            BinaryOperation::BitOr => "bitvec::bor",
            BinaryOperation::BitXor => "bitvec::bxor",
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
pub struct BinaryNode {
    pub operation: BinaryOperation,
    pub width: u64,
    pub output: u64,
    pub left: u64,
    pub right: u64,
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
    AddRR { destination: Gpr, source: Gpr },
    SubRR { destination: Gpr, source: Gpr },
    AndRR { destination: Gpr, source: Gpr },
    OrRR { destination: Gpr, source: Gpr },
    XorRR { destination: Gpr, source: Gpr },
}

impl Instruction {
    pub fn render(self) -> String {
        match self {
            Instruction::MovRR {
                destination,
                source,
            } => format!(
                "MovRR({}, {})",
                destination.heather_name(),
                source.heather_name(),
            ),
            Instruction::AddRR {
                destination,
                source,
            } => format!(
                "AddRR({}, {})",
                destination.heather_name(),
                source.heather_name(),
            ),
            Instruction::SubRR {
                destination,
                source,
            } => format!(
                "SubRR({}, {})",
                destination.heather_name(),
                source.heather_name(),
            ),
            Instruction::AndRR {
                destination,
                source,
            } => format!(
                "AndRR({}, {})",
                destination.heather_name(),
                source.heather_name(),
            ),
            Instruction::OrRR {
                destination,
                source,
            } => format!(
                "OrRR({}, {})",
                destination.heather_name(),
                source.heather_name(),
            ),
            Instruction::XorRR {
                destination,
                source,
            } => format!(
                "XorRR({}, {})",
                destination.heather_name(),
                source.heather_name(),
            ),
        }
    }

    pub fn destination(self) -> Gpr {
        match self {
            Instruction::MovRR { destination, .. }
            | Instruction::AddRR { destination, .. }
            | Instruction::SubRR { destination, .. }
            | Instruction::AndRR { destination, .. }
            | Instruction::OrRR { destination, .. }
            | Instruction::XorRR { destination, .. } => destination,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NodePlan {
    pub node_index: usize,
    pub node: BinaryNode,
    pub left_register: Gpr,
    pub right_register: Gpr,
    pub destination: Gpr,
    pub reused_value: Option<u64>,
    pub instructions: Vec<Instruction>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoweredBinaryDag {
    pub input_registers: Vec<Gpr>,
    pub node_plans: Vec<NodePlan>,
    pub instructions: Vec<Instruction>,
    pub output_id: u64,
    pub output_register: Gpr,
    pub clobbered: BTreeSet<Gpr>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct X86Emission {
    pub lowered: LoweredBinaryDag,
    pub text: String,
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
    UnsupportedOperation {
        node_index: usize,
    },
    RegisterPressure {
        node_index: usize,
        live_temporaries: usize,
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
            LoweringError::OutputCount(count) => {
                write!(f, "single-result block lowering received {count} outputs")
            }
            LoweringError::UnsupportedOperation { node_index } => {
                write!(f, "node {node_index} is not yet supported by x86 lowering")
            }
            LoweringError::RegisterPressure {
                node_index,
                live_temporaries,
            } => write!(
                f,
                "node {node_index} needs another register while {live_temporaries} temporaries are live",
            ),
        }
    }
}

/// Lower one valid-looking, 64-bit, single-output binary-ALU DAG. The generated
/// certificate remains responsible for proving that this untrusted plan agrees
/// with the actual Heather region.
pub fn lower_binary_dag(
    region: &Region,
    input_registers: &[Gpr],
    temporary_registers: &[Gpr],
    requested_output: Gpr,
) -> Result<LoweredBinaryDag, LoweringError> {
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
        require_width(port.id, port.width)?;
        if placements.insert(port.id, register).is_some() {
            return Err(LoweringError::DuplicateValue(port.id));
        }
        widths.insert(port.id, port.width);
    }

    let mut uses = BTreeMap::<u64, usize>::new();
    for (node_index, node) in region.nodes.iter().enumerate() {
        let node = binary_node(*node, node_index)?;
        *uses.entry(node.left).or_default() += 1;
        *uses.entry(node.right).or_default() += 1;
    }
    for output in &region.outputs {
        *uses.entry(output.id).or_default() += 1;
    }

    let mut owners = BTreeMap::<Gpr, u64>::new();
    let mut instructions = Vec::new();
    let mut node_plans = Vec::with_capacity(region.nodes.len());
    let mut clobbered = BTreeSet::new();

    for (node_index, &node) in region.nodes.iter().enumerate() {
        let node = binary_node(node, node_index)?;
        require_width(node.output, node.width)?;
        let Some(&left_register) = placements.get(&node.left) else {
            return Err(LoweringError::UndefinedValue(node.left));
        };
        let Some(&right_register) = placements.get(&node.right) else {
            return Err(LoweringError::UndefinedValue(node.right));
        };
        if widths.get(&node.left) != Some(&node.width) {
            return Err(LoweringError::UnsupportedWidth {
                value: node.left,
                width: *widths.get(&node.left).unwrap_or(&0),
            });
        }
        if widths.get(&node.right) != Some(&node.width) {
            return Err(LoweringError::UnsupportedWidth {
                value: node.right,
                width: *widths.get(&node.right).unwrap_or(&0),
            });
        }
        if placements.contains_key(&node.output) {
            return Err(LoweringError::DuplicateValue(node.output));
        }

        let left_last = last_use_in_node(&uses, node.left, node.left, node.right);
        let left_reusable = left_last && owners.get(&left_register) == Some(&node.left);
        let produces_output = region.outputs[0].id == node.output;

        let reused_value = if produces_output && left_reusable && left_register == requested_output
        {
            Some(node.left)
        } else if left_reusable {
            Some(node.left)
        } else {
            None
        };

        let (destination, step_instructions) = match reused_value {
            Some(_) => (
                left_register,
                vec![binary_instruction(
                    node.operation,
                    left_register,
                    right_register,
                )],
            ),
            None => {
                let Some(&destination) = temporary_registers
                    .iter()
                    .find(|register| !owners.contains_key(register))
                else {
                    return Err(LoweringError::RegisterPressure {
                        node_index,
                        live_temporaries: owners.len(),
                    });
                };
                owners.insert(destination, node.output);
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
        owners.insert(destination, node.output);
        placements.insert(node.output, destination);
        widths.insert(node.output, node.width);
        clobbered.insert(destination);
        instructions.extend(step_instructions.iter().copied());
        node_plans.push(NodePlan {
            node_index,
            node,
            left_register,
            right_register,
            destination,
            reused_value,
            instructions: step_instructions,
        });
    }

    let output = region.outputs[0];
    require_width(output.id, output.width)?;
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

    Ok(LoweredBinaryDag {
        input_registers: input_registers.to_vec(),
        node_plans,
        instructions,
        output_id: output.id,
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
    let lowered = lower_binary_dag(
        region,
        input_registers,
        temporary_registers,
        requested_output,
    )?;
    let instructions_name = format!("{prefix}_instructions");
    let bytes_name = format!("{prefix}_bytes");
    let after_name = format!("{prefix}_after");
    let protected_name = format!("{prefix}_Protected");
    let public_parameters = common_parameters(region_expr, region, input_registers);
    let public_arguments = common_arguments(region);
    let compact_parameters = compact_parameters(prefix);
    let context_arguments = context_constructor_arguments(region);
    let arguments = "values, before, context";
    let instruction_spine = render_instruction_spine(prefix, &lowered.instructions);
    let mut text = format!(
        "{instruction_spine}\
         fn {instructions_name}() → List<Instruction> {{\n\
         \x20   {}\n\
         }}\n\n\
         fn {bytes_name}() → List<BitVec(8)> {{\n\
         \x20   canonical_block_bytes({instructions_name}())\n\
         }}\n\n\
         theorem {prefix}_byte_length(): {bytes_name}().len() = {} {{ refl }}\n\n\
         theorem {prefix}_block_decodes(start: BitVec(64)):\n\
         \x20   CanonicalBlockDecodes({instructions_name}(), start)\n\
         {{\n\
         \x20   canonical_block_decodes({instructions_name}(), start)\n\
         }}\n\n",
        render_instruction_cons(prefix, &lowered.instructions, 0),
        lowered.instructions.len() * 3,
    );

    text.push_str(&format!(
        "fn {prefix}_state_0<M>(before: MachineState<M>) → MachineState<M> {{ before }}\n"
    ));
    for (index, instruction) in lowered.instructions.iter().copied().enumerate() {
        text.push_str(&format!(
            "fn {prefix}_state_{}<M>(before: MachineState<M>) → MachineState<M> {{\n\
             \x20   execute_normal(decoded_rr({}), {prefix}_state_{index}(before))\n\
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
    text.push_str(&format!(
        "theorem {prefix}_refines_compact<M>({compact_parameters}):\n\
         \x20   read_gpr({}, {after_name}(before).gprs) = values(64, {})\n\
         {{\n\
         \x20   sym({final_placement})\n\
         }}\n\n\
         theorem {prefix}_refines_function_ir<M>({public_parameters}):\n\
         \x20   read_gpr({}, {after_name}(before).gprs) = values(64, {})\n\
         {{\n\
         \x20   {prefix}_refines_compact(values, before,\n\
         \x20       {prefix}_Context({context_arguments}))\n\
         }}\n\n",
        lowered.output_register.heather_name(),
        lowered.output_id,
        lowered.output_register.heather_name(),
        lowered.output_id,
    ));

    text.push_str(&format!(
        "theorem {prefix}_preserves_memory<M>(before: MachineState<M>):\n\
         \x20   {after_name}(before).memory = before.memory\n\
         {{ refl }}\n\n\
         fn {prefix}_final_rip(start: BitVec(64)) → BitVec(64) {{ {} }}\n\n\
         theorem {prefix}_advances_rip<M>(before: MachineState<M>):\n\
         \x20   {after_name}(before).rip = {prefix}_final_rip(before.rip)\n\
         {{ refl }}\n\n",
        render_final_rip("start", lowered.instructions.len()),
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
         \x20       values(64, {}), {protected_name},\n\
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
        lowered.output_id,
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
            "input_{index}_placed: ValuePlaced(values, {}, {}, before)",
            port.id,
            register.heather_name(),
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
            "         \x20   input_{index}_placed: ValuePlaced(values, {}, {}, before),\n\
             ",
            port.id,
            register.heather_name(),
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

fn render_instruction_spine(prefix: &str, instructions: &[Instruction]) -> String {
    let mut text = format!(
        "fn {prefix}_instructions_{}() → List<Instruction> {{ [] }}\n",
        instructions.len(),
    );
    for index in (1..instructions.len()).rev() {
        text.push_str(&format!(
            "fn {prefix}_instructions_{index}() → List<Instruction> {{ {} }}\n",
            render_instruction_cons(prefix, instructions, index),
        ));
    }
    text
}

fn render_instruction_cons(prefix: &str, instructions: &[Instruction], index: usize) -> String {
    format!(
        "Cons({}, {prefix}_instructions_{}())",
        instructions[index].render(),
        index + 1,
    )
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
    lowered: &LoweredBinaryDag,
    parameters: &str,
    arguments: &str,
    text: &mut String,
) -> String {
    let mut frame_facts = BTreeSet::new();
    let mut remaining = BTreeMap::<u64, usize>::new();
    for plan in &lowered.node_plans {
        let node = plan.node;
        *remaining.entry(node.left).or_default() += 1;
        *remaining.entry(node.right).or_default() += 1;
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
        let (&left_register, left_stored_proof) = live
            .get(&plan.node.left)
            .map(|(register, proof)| (register, proof))
            .expect("validated left placement");
        let (&right_register, right_stored_proof) = live
            .get(&plan.node.right)
            .map(|(register, proof)| (register, proof))
            .expect("validated right placement");
        let left_proof = placement_at_state(
            prefix,
            plan.node.left,
            left_register,
            before_index,
            left_stored_proof,
            &input_indices,
        );
        let right_proof = placement_at_state(
            prefix,
            plan.node.right,
            right_register,
            before_index,
            right_stored_proof,
            &input_indices,
        );
        let equation = format!(
            "{prefix}_graph_{}(values, before, context).left",
            plan.node_index,
        );
        let output_name = format!(
            "{prefix}_value_{}_after_node_{}",
            plan.node.output, plan.node_index
        );
        for (offset, instruction) in plan.instructions.iter().copied().enumerate() {
            emit_step_result_fact(prefix, before_index + offset, instruction, text);
        }
        let (binary_before_index, binary_left_register, binary_left_proof, binary_right_proof) =
            if plan.instructions.len() == 2 {
                let move_after_index = before_index + 1;
                let moved_name = format!(
                    "{prefix}_value_{}_moved_for_node_{}",
                    plan.node.left, plan.node_index,
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
                    plan.node.left,
                    plan.destination.heather_name(),
                    plan.node.left,
                    plan.left_register.heather_name(),
                    plan.destination.heather_name(),
                ));
                let right_after_move = if input_indices.contains_key(&plan.node.right) {
                    placement_at_state(
                        prefix,
                        plan.node.right,
                        plan.right_register,
                        move_after_index,
                        right_stored_proof,
                        &input_indices,
                    )
                } else {
                    let right_name = format!(
                        "{prefix}_value_{}_before_add_node_{}",
                        plan.node.right, plan.node_index,
                    );
                    let right_frame = emit_step_frame_fact(
                        prefix,
                        before_index,
                        plan.instructions[0],
                        plan.right_register,
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
                        plan.node.right,
                        plan.right_register.heather_name(),
                        plan.node.right,
                        plan.right_register.heather_name(),
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
                    plan.left_register,
                    left_proof.clone(),
                    right_proof.clone(),
                )
            };
        text.push_str(&format!(
            "theorem {output_name}<M>({parameters}):\n\
             \x20   ValuePlaced(values, {}, {}, {prefix}_state_{after_index}(before))\n\
             {{\n\
             \x20   placed_after_binary(values, {}, {}, {}, {}(64, ·, ·), {}, {}, {},\n\
             \x20       {prefix}_state_{binary_before_index}(before), {prefix}_state_{after_index}(before),\n\
             \x20       {equation}, {binary_left_proof}, {binary_right_proof},\n\
             \x20       {prefix}_step_{binary_before_index}_result(\n\
             \x20           {prefix}_state_{binary_before_index}(before)))\n\
             }}\n",
            plan.node.output,
            plan.destination.heather_name(),
            plan.node.output,
            plan.node.left,
            plan.node.right,
            plan.node.operation.semantic_function(),
            binary_left_register.heather_name(),
            plan.right_register.heather_name(),
            plan.destination.heather_name(),
        ));

        consume_known_use(&mut remaining, plan.node.left);
        consume_known_use(&mut remaining, plan.node.right);
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
                text.push_str(&format!(
                    "theorem {frame_name}<M>({parameters}):\n\
                     \x20   ValuePlaced(values, {value}, {}, {prefix}_state_{step_after}(before))\n\
                     {{\n\
                     \x20   placed_after_frame(values, {value}, {},\n\
                     \x20       {prefix}_state_{step_before}(before), {prefix}_state_{step_after}(before),\n\
                     \x20       {frame_proof},\n\
                     \x20       {frame_fact}({prefix}_state_{step_before}(before)))\n\
                     }}\n",
                    register.heather_name(),
                    register.heather_name(),
                ));
                frame_proof = format!("{frame_name}({arguments})");
            }
            next_live.insert(value, (register, frame_proof));
        }
        if remaining.get(&plan.node.output).copied().unwrap_or(0) > 0 {
            next_live.insert(
                plan.node.output,
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
        text.push_str(&format!(
            "theorem {final_name}<M>({parameters}):\n\
             \x20   ValuePlaced(values, {}, {}, {prefix}_state_{}(before))\n\
             {{\n\
             \x20   placed_after_move(values, {}, {}, {},\n\
             \x20       {prefix}_state_{instruction_index}(before),\n\
             \x20       {prefix}_state_{}(before), {source_proof},\n\
             \x20       {prefix}_step_{instruction_index}_result(\n\
             \x20           {prefix}_state_{instruction_index}(before)))\n\
             }}\n",
            lowered.output_id,
            lowered.output_register.heather_name(),
            lowered.instructions.len(),
            lowered.output_id,
            source_register.heather_name(),
            lowered.output_register.heather_name(),
            lowered.instructions.len(),
        ));
        format!("{final_name}({arguments})")
    }
}

fn placement_at_state(
    prefix: &str,
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
    format!(
        "placed_after_frame(values, {value}, {}, before, {prefix}_state_{state}(before), \
         context.input_{input_index}_placed, refl)",
        register.heather_name(),
    )
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
    };
    text.push_str(&format!(
        "theorem {prefix}_step_{step}_result<M>(state: MachineState<M>):\n\
         \x20   read_gpr({}, execute_normal(decoded_rr({}), state).gprs) =\n\
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
            "{}(64, read_gpr({}, state.gprs), read_gpr({}, state.gprs))",
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
    debug_assert_ne!(instruction.destination(), register);
    let name = format!("{prefix}_step_{step}_preserves_{}", register.heather_name());
    if emitted.insert((step, register)) {
        text.push_str(&format!(
            "theorem {name}<M>(state: MachineState<M>):\n\
             \x20   read_gpr({}, execute_normal(decoded_rr({}), state).gprs) =\n\
             \x20       read_gpr({}, state.gprs)\n\
             {{ refl }}\n",
            register.heather_name(),
            instruction.render(),
            register.heather_name(),
        ));
    }
    name
}

fn render_final_rip(start: &str, instruction_count: usize) -> String {
    (0..instruction_count).fold(start.to_string(), |rip, _| format!("next_rip({rip}, 3)"))
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

fn binary_node(node: Node, node_index: usize) -> Result<BinaryNode, LoweringError> {
    match node {
        Node::Add {
            width,
            output,
            left,
            right,
        } => Ok(BinaryNode {
            operation: BinaryOperation::Add,
            width,
            output,
            left,
            right,
        }),
        Node::Sub {
            width,
            output,
            left,
            right,
        } => Ok(BinaryNode {
            operation: BinaryOperation::Sub,
            width,
            output,
            left,
            right,
        }),
        Node::BitAnd {
            width,
            output,
            left,
            right,
        } => Ok(BinaryNode {
            operation: BinaryOperation::BitAnd,
            width,
            output,
            left,
            right,
        }),
        Node::BitOr {
            width,
            output,
            left,
            right,
        } => Ok(BinaryNode {
            operation: BinaryOperation::BitOr,
            width,
            output,
            left,
            right,
        }),
        Node::BitXor {
            width,
            output,
            left,
            right,
        } => Ok(BinaryNode {
            operation: BinaryOperation::BitXor,
            width,
            output,
            left,
            right,
        }),
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
    use crate::function_ir_cert::Port;

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
        let lowered =
            lower_binary_dag(&region, &[Gpr::Rdi, Gpr::Rsi], &[Gpr::Rax], Gpr::Rax).unwrap();
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
    fn sum4_reuses_left_operands_and_moves_only_when_the_schedule_requires_it() {
        let inputs = [Gpr::Rdi, Gpr::Rsi, Gpr::Rdx, Gpr::Rcx];
        let temporaries = [Gpr::Rax, Gpr::R8];
        for left_first in [true, false] {
            let lowered =
                lower_binary_dag(&sum4(left_first), &inputs, &temporaries, Gpr::Rax).unwrap();
            assert_eq!(lowered.node_plans[2].reused_value, Some(4));
            if left_first {
                assert_eq!(lowered.instructions.len(), 5);
                assert_eq!(
                    lowered.instructions.last(),
                    Some(&Instruction::AddRR {
                        destination: Gpr::Rax,
                        source: Gpr::R8,
                    })
                );
            } else {
                assert_eq!(lowered.instructions.len(), 6);
                assert_eq!(
                    lowered.instructions.last(),
                    Some(&Instruction::MovRR {
                        destination: Gpr::Rax,
                        source: Gpr::R8,
                    })
                );
            }
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
        let lowered =
            lower_binary_dag(&region, &[Gpr::Rdi, Gpr::Rsi], &[Gpr::Rax], Gpr::Rax).unwrap();
        assert_eq!(lowered.instructions.len(), 101);
        assert!(
            lowered.node_plans[1..]
                .iter()
                .all(|step| step.reused_value.is_some())
        );
    }

    #[test]
    fn independent_live_results_report_register_pressure() {
        let error = lower_binary_dag(
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
}
