//! Source-driven recursive selection regressions. Physical certificate and
//! native publication gates live in their own acceptance targets.
mod support;

use std::collections::BTreeMap;
use heather_elab::function_ir_cert::{Node, Port, Region, StructuredRegion};
use heather_elab::function_ir_source::{generate_structured_source_expansion, reflect_elaborated, reflect_elaborated_structured};
use heather_elab::function_ir_x86_lower::{lower_structured, Gpr, Instruction, LoweredDag, LoweredStructured, Placements, StructuredPlan};

const SCRATCH: &[Gpr] = &[Gpr::Rax, Gpr::Rcx, Gpr::Rdx, Gpr::R8];
const SOURCE: &str = r#"
import bitvec;
import bool;
fn nested_true(a, b: BitVec(64)) → BitVec(64) {
    match bitvec::unsigned_lt_bit(64, a, b) {
        False => bitvec::sub(64, a, b),
        True => match bitvec::unsigned_lt_bit(64, b, bitvec::ofNat(64, 10)) {
            False => bitvec::bxor(64, b, a),
            True => bitvec::add(64, a, b),
        },
    }
}
fn nested_false(a, b: BitVec(64)) → BitVec(64) {
    match bitvec::unsigned_lt_bit(64, a, b) {
        False => match bitvec::unsigned_lt_bit(64, a, bitvec::ofNat(64, 10)) {
            False => bitvec::sub(64, b, a),
            True => bitvec::bor(64, a, b),
        },
        True => bitvec::add(64, b, a),
    }
}
fn wrong_condition(a, b: BitVec(64)) → BitVec(64) {
    match bitvec::signed_lt_bit(64, a, b) {
        False => bitvec::sub(64, a, b), True => bitvec::add(64, a, b),
    }
}
"#;

fn source_elaborator() -> heather_elab::Elaborator {
    let modules = [
        ("logic", include_str!("../../../lib/std/logic.hthr")),
        ("bool", include_str!("../../../lib/std/bool.hthr")),
        ("nat", include_str!("../../../lib/std/nat.hthr")),
        ("option", include_str!("../../../lib/std/option.hthr")),
        ("pair", include_str!("../../../lib/std/pair.hthr")),
        ("list", include_str!("../../../lib/std/list.hthr")),
        ("algebra", include_str!("../../../lib/std/algebra.hthr")),
        ("int", include_str!("../../../lib/std/int.hthr")),
        ("bitvec", include_str!("../../../lib/std/bitvec.hthr")),
    ];
    let mut elab = support::semantic_test_base(&modules);
    elab.elab_module_source("recursive_source", SOURCE).unwrap();
    elab
}

fn placement() -> Placements { BTreeMap::from([(0, Gpr::Rdi), (1, Gpr::Rsi)]) }

// Independent word-level execution of the selected instructions, including
// partial-byte SETcc writes. This is a regression oracle, not a certificate.
fn run_dag(dag: &LoweredDag, regs: &mut BTreeMap<Gpr, u64>) {
    let mut below = false;
    for &instruction in &dag.instructions {
        let read = |r| regs[&r];
        let (destination, value) = match instruction {
            Instruction::MovRR { destination, source } => (destination, read(source)),
            Instruction::MovRI { destination, immediate } => (destination, immediate),
            Instruction::AddRR { destination, source } => (destination, read(destination).wrapping_add(read(source))),
            Instruction::SubRR { destination, source } => (destination, read(destination).wrapping_sub(read(source))),
            Instruction::AndRR { destination, source } => (destination, read(destination) & read(source)),
            Instruction::OrRR { destination, source } => (destination, read(destination) | read(source)),
            Instruction::XorRR { destination, source } => (destination, read(destination) ^ read(source)),
            Instruction::CmpRR { left, right } => { below = read(left) < read(right); continue; }
            Instruction::SetBelow { destination } => {
                use heather_elab::function_ir_x86_lower::LowByteGpr;
                let reg = match destination { LowByteGpr::Al => Gpr::Rax, LowByteGpr::Cl => Gpr::Rcx, LowByteGpr::Dl => Gpr::Rdx, LowByteGpr::Bl => Gpr::Rbx };
                (reg, (read(reg) & !255) | u64::from(below))
            }
            other => panic!("unexpected instruction {other:?}"),
        };
        regs.insert(destination, value);
    }
}

fn run(plan: &LoweredStructured, regs: &mut BTreeMap<Gpr, u64>) {
    match &plan.body {
        StructuredPlan::Dataflow(dag) => run_dag(dag, regs),
        StructuredPlan::Sequence { prefix, continuation } => { run_dag(prefix, regs); run(continuation, regs); }
        StructuredPlan::Conditional { condition_register, when_true, when_false, false_displacement, join_displacement } => {
            assert_eq!(*false_displacement as usize, when_true.byte_length + 2);
            assert_eq!(*join_displacement as usize, when_false.byte_length);
            run(if regs[condition_register] != 0 { when_true } else { when_false }, regs);
        }
    }
}

#[test]
fn nested_source_selection_in_both_arms_preserves_live_inputs() {
    let elab = source_elaborator();
    for name in ["nested_true", "nested_false"] {
        let reflected = reflect_elaborated_structured(&elab, name).unwrap();
        assert_eq!(reflected.source_name, format!("recursive_source::{name}"));
        assert_eq!(reflected, reflect_elaborated_structured(&elab, &reflected.source_name).unwrap());
        let plan = lower_structured(&reflected.region, &placement(), SCRATCH, Gpr::Rax).unwrap();
        assert!(!plan.clobbered.contains(&Gpr::Rdi));
        assert!(!plan.clobbered.contains(&Gpr::Rsi));
        for a in [0u64, 1, 9, 10, 11, u64::MAX] {
            for b in [0u64, 1, 9, 10, 11, u64::MAX] {
                let expected = if name == "nested_true" {
                    if a < b { if b < 10 { a.wrapping_add(b) } else { b ^ a } } else { a.wrapping_sub(b) }
                } else {
                    if a < b { b.wrapping_add(a) } else if a < 10 { a | b } else { b.wrapping_sub(a) }
                };
                let mut regs = BTreeMap::from([(Gpr::Rdi, a), (Gpr::Rsi, b)]);
                for r in SCRATCH { regs.insert(*r, u64::MAX); }
                run(&plan, &mut regs);
                assert_eq!(regs[&Gpr::Rax], expected, "{name}({a}, {b})");
                assert_eq!((regs[&Gpr::Rdi], regs[&Gpr::Rsi]), (a, b));
            }
        }
        // Straight-line reflection must not silently flatten a structured body.
        assert!(reflect_elaborated(&elab, name).is_err());
    }
    assert!(reflect_elaborated_structured(&elab, "wrong_condition").unwrap_err().to_string().contains("unsigned_lt_bit"));
}

fn leaf() -> StructuredRegion {
    StructuredRegion::Dataflow(Region {
        inputs: vec![Port { id: 41, width: 64 }, Port { id: 7, width: 64 }],
        nodes: vec![Node::Sub { width: 64, output: 99, left: 41, right: 7 }],
        outputs: vec![Port { id: 99, width: 64 }],
    })
}

#[test]
fn placement_ids_and_refusals_are_explicit() {
    let region = leaf();
    let inputs = BTreeMap::from([(7, Gpr::Rsi), (41, Gpr::Rdi)]);
    let plan = lower_structured(&region, &inputs, SCRATCH, Gpr::Rax).unwrap();
    let StructuredPlan::Dataflow(dag) = plan.body else { panic!() };
    assert_eq!(dag.input_registers, [Gpr::Rdi, Gpr::Rsi]);
    for (mapping, scratch, output, diagnostic) in [
        (BTreeMap::from([(7, Gpr::Rsi), (42, Gpr::Rdi)]), SCRATCH, Gpr::Rax, "value 41 is undefined"),
        (BTreeMap::from([(7, Gpr::Rsi), (41, Gpr::Rsi)]), SCRATCH, Gpr::Rax, "appears twice"),
        (BTreeMap::from([(7, Gpr::Rsi), (41, Gpr::Rax)]), SCRATCH, Gpr::Rax, "temporary pool"),
        (inputs.clone(), SCRATCH, Gpr::Rdi, "not an assignable temporary"),
    ] {
        let error = lower_structured(&region, &mapping, scratch, output).unwrap_err().to_string();
        assert!(error.starts_with("root:"), "{error}");
        assert!(error.contains(diagnostic), "{error}");
    }
}

#[test]
fn nested_branch_range_and_pressure_decline_at_the_boundary() {
    let elab = source_elaborator();
    let reflected = reflect_elaborated_structured(&elab, "nested_true").unwrap();
    let error = lower_structured(&reflected.region, &placement(), &[Gpr::Rax], Gpr::Rax).unwrap_err().to_string();
    assert!(error.contains("root:") && error.contains("another register"), "{error}");
    let mut region = reflected.region;
    let StructuredRegion::Sequence { continuation, .. } = &mut region else { panic!() };
    let StructuredRegion::Conditional { when_false, .. } = &mut **continuation else { panic!() };
    let StructuredRegion::Dataflow(leaf) = &mut **when_false else { panic!() };
    leaf.nodes.clear();
    let mut previous = 0;
    for id in 100..150 {
        leaf.nodes.push(Node::Add { width: 64, output: id, left: previous, right: 1 });
        previous = id;
    }
    leaf.nodes.push(Node::Sub { width: 64, output: 2, left: previous, right: 1 });
    let error = lower_structured(&region, &placement(), SCRATCH, Gpr::Rax).unwrap_err().to_string();
    assert!(error.contains("root.continuation:") && error.contains("rel8"), "{error}");
}

#[test]
fn sequence_carries_a_word_result_and_inherited_input_by_id() {
    let region = StructuredRegion::Sequence {
        prefix: Region {
            inputs: vec![Port { id: 41, width: 64 }, Port { id: 7, width: 64 }],
            nodes: vec![Node::Add { width: 64, output: 20, left: 41, right: 7 }],
            outputs: vec![Port { id: 20, width: 64 }],
        },
        continuation: Box::new(StructuredRegion::Dataflow(Region {
            // Reverse order deliberately: positional forwarding would swap
            // the operands of this noncommutative instruction.
            inputs: vec![Port { id: 7, width: 64 }, Port { id: 20, width: 64 }],
            nodes: vec![Node::Sub { width: 64, output: 99, left: 7, right: 20 }],
            outputs: vec![Port { id: 99, width: 64 }],
        })),
    };
    let inputs = BTreeMap::from([(7, Gpr::Rsi), (41, Gpr::Rdi)]);
    let plan = lower_structured(&region, &inputs, SCRATCH, Gpr::Rax).unwrap();
    let mut regs = BTreeMap::from([(Gpr::Rdi, 17), (Gpr::Rsi, 5)]);
    run(&plan, &mut regs);
    assert_eq!(regs[&Gpr::Rax], 5u64.wrapping_sub(22));
    assert_eq!((regs[&Gpr::Rdi], regs[&Gpr::Rsi]), (17, 5));

    let mut missing = region.clone();
    let StructuredRegion::Sequence { continuation, .. } = &mut missing else { panic!() };
    let StructuredRegion::Dataflow(body) = &mut **continuation else { panic!() };
    body.inputs[1].id = 21;
    assert!(lower_structured(&missing, &inputs, SCRATCH, Gpr::Rax).unwrap_err().to_string().contains("not available from the prefix"));

    let mut multiple = region;
    let StructuredRegion::Sequence { prefix, .. } = &mut multiple else { panic!() };
    prefix.outputs.push(Port { id: 7, width: 64 });
    assert!(lower_structured(&multiple, &inputs, SCRATCH, Gpr::Rax).unwrap_err().to_string().contains("2 outputs"));
}

#[test]
fn source_expansion_is_kernel_checked_and_rejects_stale_source_and_bindings() {
    let elab = source_elaborator();
    let image = elab.semantic_image();
    for name in ["nested_true", "nested_false"] {
        let reflected = reflect_elaborated_structured(&elab, name).unwrap();
        let text = generate_structured_source_expansion("recovered", &reflected).unwrap();
        let mut checker = image.elaborator();
        checker.elab_module_source("agreement", &text).unwrap_or_else(|error| panic!("{}", error.render(&text)));

        let mut stale = reflected.clone();
        stale.source_name = format!("recursive_source::{}", if name == "nested_true" { "nested_false" } else { "nested_true" });
        let text = generate_structured_source_expansion("stale", &stale).unwrap();
        assert!(image.elaborator().elab_module_source("stale_agreement", &text).is_err());

        let mut wrong = reflected;
        let StructuredRegion::Sequence { prefix, .. } = &mut wrong.region else { panic!() };
        let Node::UnsignedLessThan { left, right, .. } = prefix.nodes.last_mut().unwrap() else { panic!() };
        std::mem::swap(left, right);
        let text = generate_structured_source_expansion("wrong", &wrong).unwrap();
        assert!(image.elaborator().elab_module_source("wrong_agreement", &text).is_err());
    }
}
