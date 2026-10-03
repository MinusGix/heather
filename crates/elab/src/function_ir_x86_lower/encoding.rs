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
            // REX (40, or 41 for R8B–R15B) unless AL–BL, then 0F 9x /0.
            Instruction::SetBelow { destination } | Instruction::SetLess { destination } | Instruction::SetEqual { destination } => {
                let r = register_code(destination.gpr());
                if !LowByteGpr::legacy(destination.gpr()) { bytes.push(0x40 | (r >> 3)); }
                let opcode = match instruction { Instruction::SetBelow { .. } => 0x92, Instruction::SetLess { .. } => 0x9c, _ => 0x94 };
                bytes.extend([0x0f, opcode, 0xc0 | (r & 7)]);
                continue;
            }
            // REX.W 83 /0 ib and REX.W 81 /0 id.
            Instruction::AddRI8 { destination, immediate } => {
                let r = register_code(destination);
                bytes.extend([0x48 | (r >> 3), 0x83, 0xc0 | (r & 7), immediate]);
                continue;
            }
            Instruction::AddRI32 { destination, immediate } => {
                let r = register_code(destination);
                bytes.extend([0x48 | (r >> 3), 0x81, 0xc0 | (r & 7)]);
                bytes.extend(immediate.to_le_bytes());
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
        StructuredPlan::FusedSequence { operands, continuation } => {
            let mut bytes = encode_instructions(&operands.instructions);
            bytes.extend(encode_structured(continuation));
            bytes
        }
        StructuredPlan::Conditional { test, when_true, when_false, false_displacement, join_displacement, near } => {
            let mut bytes = match (test, test.instruction()) {
                (_, Some(instruction)) => encode_instructions(&[instruction]),
                (super::PlannedTest::NonZero(register), None) => {
                    let r = register_code(*register);
                    vec![0x48 | (r >> 3) | ((r >> 3) << 2), 0x85, 0xc0 | ((r & 7) << 3) | (r & 7)]
                }
                (super::PlannedTest::Compare { .. }, None) => unreachable!("a comparison has its instruction"),
            };
            if *near { bytes.extend([0x0f, 0x80 | test.skip_code()]); bytes.extend(false_displacement.to_le_bytes()); }
            else { bytes.extend([0x70 | test.skip_code(), *false_displacement as u8]); }
            bytes.extend(encode_structured(when_true));
            if *near { bytes.push(0xe9); bytes.extend(join_displacement.to_le_bytes()); }
            else { bytes.extend([0xeb, *join_displacement as u8]); }
            bytes.extend(encode_structured(when_false));
            bytes
        }
    }
}

