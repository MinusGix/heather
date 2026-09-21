//! Canonical byte encoding shared by native export and composed read bodies.
use super::{Gpr, Instruction, LowByteGpr};

pub fn register_code(register: Gpr) -> u8 {
    match register {
        Gpr::Rax => 0, Gpr::Rcx => 1, Gpr::Rdx => 2, Gpr::Rbx => 3,
        Gpr::Rsp => 4, Gpr::Rbp => 5, Gpr::Rsi => 6, Gpr::Rdi => 7,
        Gpr::R8 => 8, Gpr::R9 => 9, Gpr::R10 => 10, Gpr::R11 => 11,
        Gpr::R12 => 12, Gpr::R13 => 13, Gpr::R14 => 14, Gpr::R15 => 15,
    }
}

pub fn encode_instructions(instructions: &[Instruction]) -> Vec<u8> {
    let mut bytes = Vec::new();
    for &instruction in instructions {
        let (opcode, destination, source) = match instruction {
            Instruction::MovRI { destination, immediate } => {
                let r = register_code(destination);
                bytes.extend([0x48 | (r >> 3), 0xb8 | (r & 7)]);
                bytes.extend(immediate.to_le_bytes());
                continue;
            }
            Instruction::SetBelow { destination } | Instruction::SetLess { destination } => {
                let r = match destination { LowByteGpr::Al => 0, LowByteGpr::Cl => 1, LowByteGpr::Dl => 2, LowByteGpr::Bl => 3 };
                bytes.extend([0x0f, if matches!(instruction, Instruction::SetBelow { .. }) { 0x92 } else { 0x9c }, 0xc0 | r]);
                continue;
            }
            Instruction::MovRR { destination, source } => (0x89, destination, source),
            Instruction::AddRR { destination, source } => (0x01, destination, source),
            Instruction::SubRR { destination, source } => (0x29, destination, source),
            Instruction::AndRR { destination, source } => (0x21, destination, source),
            Instruction::OrRR { destination, source } => (0x09, destination, source),
            Instruction::XorRR { destination, source } => (0x31, destination, source),
            Instruction::CmpRR { left, right } => (0x39, left, right),
        };
        let (rm, r) = (register_code(destination), register_code(source));
        bytes.extend([0x48 | (rm >> 3) | ((r >> 3) << 2), opcode, 0xc0 | ((r & 7) << 3) | (rm & 7)]);
    }
    bytes
}

pub fn encode_structured(plan: &super::LoweredStructured) -> Vec<u8> {
    use super::StructuredPlan;
    match &plan.body {
        StructuredPlan::Dataflow(dag) => encode_instructions(&dag.instructions),
        StructuredPlan::MultiDataflow(parts) => parts.iter().flat_map(|(_, dag)| encode_instructions(&dag.instructions)).collect(),
        StructuredPlan::Compose { prefix, continuation } => {
            let mut bytes = encode_structured(prefix);
            bytes.extend(encode_structured(continuation));
            bytes
        }
        StructuredPlan::Sequence { prefix, continuation } => {
            let mut bytes = encode_instructions(&prefix.instructions);
            bytes.extend(encode_structured(continuation));
            bytes
        }
        StructuredPlan::Conditional { condition_register, when_true, when_false, false_displacement, join_displacement } => {
            let r = register_code(*condition_register);
            let mut bytes = vec![0x48 | (r >> 3) | ((r >> 3) << 2), 0x85, 0xc0 | ((r & 7) << 3) | (r & 7), 0x74, *false_displacement];
            bytes.extend(encode_structured(when_true));
            bytes.extend([0xeb, *join_displacement]);
            bytes.extend(encode_structured(when_false));
            bytes
        }
    }
}

