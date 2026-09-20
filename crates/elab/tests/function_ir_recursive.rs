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
        StructuredPlan::MultiDataflow(parts) => { for (_, dag) in parts { run_dag(dag, regs); } }
        StructuredPlan::Compose { prefix, continuation } => { run(prefix, regs); run(continuation, regs); }
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
        let reflected = reflect_elaborated_structured(&elab, name).unwrap_or_else(|e| panic!("{name}: {e}"));
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
    lower_structured(&multiple, &inputs, SCRATCH, Gpr::Rax).unwrap();
}

#[test]
fn source_expansion_is_kernel_checked_and_rejects_stale_source_and_bindings() {
    let elab = source_elaborator();
    let image = elab.semantic_image();
    for name in ["nested_true", "nested_false"] {
        let reflected = reflect_elaborated_structured(&elab, name).unwrap_or_else(|e| panic!("{name}: {e}"));
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

const TYPED_SOURCE: &str = r#"
import bitvec; import bool;
fn mixed(flag: Bool, left: BitVec(8), right: BitVec(8), fallback: BitVec(8)) → BitVec(8) {
    match flag {
        False => fallback,
        True => match bitvec::unsigned_lt_bit(8, left, right) {
            False => bitvec::sub(8, left, right), True => bitvec::add(8, left, right),
        },
    }
}
fn bool_carry(flag: Bool, left: BitVec(8), right: BitVec(8), saved: Bool) → Bool {
    match flag {
        False => saved,
        True => match bitvec::unsigned_lt_bit(8, left, right) { False => False, True => True },
    }
}
fn one_bit_word(word: BitVec(1)) → BitVec(1) { word }
fn one_bit_bool(value: Bool) → Bool { value }
fn no_inputs() → Bool { True }
fn widths(a: BitVec(16), b: BitVec(32), choose: Bool) → BitVec(32) {
    match bitvec::unsigned_lt_bit(16, a, bitvec::ofNat(16, 12)) {
        False => b,
        True => match choose { False => bitvec::ofNat(32, 0), True => bitvec::bxor(32, b, bitvec::ofNat(32, 15)) },
    }
}
fn shared(a, b: BitVec(8)) → BitVec(8) {
    bitvec::add(8, bitvec::bxor(8, a, b), bitvec::bxor(8, a, b))
}
fn too_wide(a: BitVec(128)) → BitVec(128) { a }
fn dynamic(width: Nat, value: BitVec(width)) → BitVec(width) { value }
fn natural(value: Nat) → Nat { value }
fn unsupported_helper(a: BitVec(8)) → BitVec(8) { bitvec::neg(8, a) }
inductive CounterfeitBool { Off, On }
fn other_sum() → Bool { match Off { Off => False, On => True } }
fn unsigned_lt_bit(width: Nat, a, b: BitVec(width)) → Bool { True }
fn shadowed_compare(a, b: BitVec(8)) → Bool { unsigned_lt_bit(8, a, b) }
"#;

#[test]
fn typed_structured_interfaces_and_source_agreement() {
    use heather_elab::function_ir_source::StructuredSourceType::{Boolean, Word};
    let mut elab = source_elaborator();
    elab.elab_module_source("typed_source", TYPED_SOURCE).unwrap_or_else(|e| panic!("{}", e.render(TYPED_SOURCE)));
    for name in ["mixed", "bool_carry", "one_bit_word", "one_bit_bool", "no_inputs", "widths", "shared"] {
        let reflected = reflect_elaborated_structured(&elab, name).unwrap_or_else(|e| panic!("{name}: {e}"));
        heather_elab::function_ir_cert::validate_structured_region(&reflected.region).unwrap();
        let text = generate_structured_source_expansion(name, &reflected).unwrap();
        elab.elab_module_source(&format!("{name}_agreement"), &text).unwrap_or_else(|e| panic!("{}", e.render(&text)));
    }
    let reflected = reflect_elaborated_structured(&elab, "mixed").unwrap();
    assert_eq!(reflected.parameters, [Boolean, Word(8), Word(8), Word(8)]);
    assert_eq!(reflected.result, Word(8));
    assert_eq!(reflected.region.outputs(), [Port { id: 4, width: 8 }]);
    let shared = reflect_elaborated_structured(&elab, "shared").unwrap();
    let StructuredRegion::Dataflow(body) = &shared.region else { panic!() };
    assert_eq!(body.nodes.len(), 2, "repeated subexpressions must share their DAG node");
    for name in ["too_wide", "dynamic", "natural", "unsupported_helper", "other_sum", "shadowed_compare"] {
        assert!(reflect_elaborated_structured(&elab, name).is_err(), "must decline {name}");
    }
    assert!(heather_elab::function_ir_source::generate_elaborated_structured_x86(&elab, "mixed_native", "mixed", [Gpr::Rdi, Gpr::Rsi], SCRATCH, Gpr::Rax).is_err());

    let image = elab.semantic_image();
    let mut wrong = reflected;
    wrong.parameters[0] = Word(1); // Same IR width, different source interface.
    let text = generate_structured_source_expansion("wrong_type", &wrong).unwrap();
    heather_syntax::parse_file(&text).unwrap();
    assert!(image.elaborator().elab_module_source("wrong_type", &text).is_err());
    let mut wrong = reflect_elaborated_structured(&elab, "one_bit_word").unwrap();
    wrong.source_name = "typed_source::one_bit_bool".into();
    let text = generate_structured_source_expansion("wrong_source", &wrong).unwrap();
    heather_syntax::parse_file(&text).unwrap();
    assert!(image.elaborator().elab_module_source("wrong_source", &text).is_err());
}

#[test]
fn loop_byte_predicate_uses_shared_structured_frontend() {
    use heather_elab::function_ir_source::StructuredSourceType::{Boolean, Word};
    let mut elab = source_elaborator();
    let model = include_str!("../../../lib/function_ir_loop.hthr");
    elab.elab_module_source("function_ir_loop", model).unwrap_or_else(|e| panic!("{}", e.render(model)));
    let source = include_str!("../../../examples/function-ir/readonly-loops.hthr");
    elab.elab_module_source("readonly_loops", source).unwrap_or_else(|e| panic!("{}", e.render(source)));
    let reflected = reflect_elaborated_structured(&elab, "readonly_loops::byte_equal").unwrap();
    assert_eq!(reflected.parameters, [Word(8), Word(8)]);
    assert_eq!(reflected.result, Boolean);
    let text = generate_structured_source_expansion("byte_equal", &reflected).unwrap();
    elab.elab_module_source("byte_agreement", &text).unwrap_or_else(|e| panic!("{}", e.render(&text)));
    let image = elab.semantic_image();
    let mut wrong = reflected;
    let StructuredRegion::Sequence { prefix, .. } = &mut wrong.region else { panic!() };
    let Node::UnsignedLessThan { left, right, .. } = prefix.nodes.last_mut().unwrap() else { panic!() };
    std::mem::swap(left, right);
    let text = generate_structured_source_expansion("wrong_byte", &wrong).unwrap();
    heather_syntax::parse_file(&text).unwrap();
    assert!(image.elaborator().elab_module_source("wrong_byte", &text).is_err());
    // Nat carries still need representation proofs; the Boolean body now
    // lowers completely, while its cursor remains universally quantified.
    assert!(reflect_elaborated_structured(&elab, "readonly_loops::count_body").is_err());
    let body = reflect_elaborated_structured(&elab, "readonly_loops::search_body").unwrap();
    assert_eq!(body.parameters[1], heather_elab::function_ir_source::StructuredSourceType::Natural);
    assert_eq!(body.region.inputs(), [Port { id: 0, width: 8 }, Port { id: 2, width: 8 }, Port { id: 3, width: 1 }]);
    assert_eq!(body.region.outputs(), [Port { id: 4, width: 1 }, Port { id: 5, width: 1 }]);
    assert!(matches!(body.region, StructuredRegion::Compose { .. }));
    let text = generate_structured_source_expansion("search_body", &body).unwrap();
    elab.elab_module_source("search_body_agreement", &text).unwrap_or_else(|e| panic!("{}", e.render(&text)));
}

const COMPOSED_SOURCE: &str = r#"
import bitvec; import bool;
inductive Decision<A> { Yield(value: A), Stop(value: A) }
fn below(a, b: BitVec(8)) → Bool { bitvec::unsigned_lt_bit(8, a, b) }
fn choose(a, b: BitVec(8)) → Bool {
    match below(a, b) { False => False, True => True }
}
fn relay(ignored: Nat, a, b: BitVec(8), old: BitVec(8)) → Decision<BitVec(8)> {
    match choose(b, bitvec::add(8, a, b)) {
        False => Yield(old),
        True => Stop(bitvec::sub(8, a, old)),
    }
}
fn tail_helper(a, b: BitVec(8)) → Bool { below(b, bitvec::add(8, a, b)) }
fn ignore_natural(n: Nat, bit: Bool) → Bool { bit }
fn used_natural(n: Nat, bit: Bool) → Bool { match n { Zero => bit, Succ(_) => False } }
inductive Mixed<A> { One(value: A), Two(value: Nat) }
fn mixed_result(a: Bool) → Mixed<Bool> { One(a) }
"#;

#[test]
fn composed_helpers_and_generic_choice_results_check() {
    let mut elab = source_elaborator();
    elab.elab_module_source("composed_source", COMPOSED_SOURCE).unwrap_or_else(|e| panic!("{}", e.render(COMPOSED_SOURCE)));
    for name in ["relay", "tail_helper", "ignore_natural"] {
        let reflected = reflect_elaborated_structured(&elab, name).unwrap_or_else(|e| panic!("{name}: {e}"));
        let text = generate_structured_source_expansion(name, &reflected).unwrap();
        elab.elab_module_source(&format!("{name}_agreement"), &text).unwrap_or_else(|e| panic!("{}", e.render(&text)));
    }
    for name in ["used_natural", "mixed_result"] {
        assert!(reflect_elaborated_structured(&elab, name).is_err(), "must refuse {name}");
    }
    let reflected = reflect_elaborated_structured(&elab, "relay").unwrap();
    assert_eq!(reflected.region.outputs(), [Port { id: 4, width: 8 }, Port { id: 5, width: 1 }]);
    let image = elab.semantic_image();
    let stale_text = generate_structured_source_expansion("stale_helper", &reflected).unwrap();
    let changed_helper = COMPOSED_SOURCE.replace("bitvec::unsigned_lt_bit(8, a, b)", "bitvec::unsigned_lt_bit(8, b, a)");
    assert_ne!(changed_helper, COMPOSED_SOURCE);
    let mut changed = source_elaborator();
    changed.elab_module_source("composed_source", &changed_helper).unwrap_or_else(|e| panic!("{}", e.render(&changed_helper)));
    reject_structured(&changed.semantic_image(), "stale_helper", &stale_text);
    let mut swapped = reflected.clone();
    swapped.choice.as_mut().unwrap().constructors.swap(0, 1);
    reject_structured(&image, "swapped_constructors", &generate_structured_source_expansion("swapped", &swapped).unwrap());
    let mut wrong_exit = reflected.clone();
    let StructuredRegion::Compose { continuation, .. } = &mut wrong_exit.region else { panic!("expected structured predicate producer") };
    let StructuredRegion::Conditional { when_false, .. } = &mut **continuation else { panic!() };
    let StructuredRegion::Dataflow(leaf) = &mut **when_false else { panic!() };
    let Node::Const { value, .. } = leaf.nodes.last_mut().unwrap() else { panic!() };
    *value = 1;
    reject_structured(&image, "wrong_exit", &generate_structured_source_expansion("wrong_exit", &wrong_exit).unwrap());
    let mut wrong_payload = reflected.clone();
    let StructuredRegion::Compose { continuation, .. } = &mut wrong_payload.region else { panic!() };
    let StructuredRegion::Conditional { when_true, .. } = &mut **continuation else { panic!() };
    let StructuredRegion::Dataflow(leaf) = &mut **when_true else { panic!() };
    let Node::Sub { left, right, .. } = leaf.nodes.iter_mut().find(|node| matches!(node, Node::Sub { .. })).unwrap() else { panic!() };
    std::mem::swap(left, right);
    reject_structured(&image, "wrong_payload", &generate_structured_source_expansion("wrong_payload", &wrong_payload).unwrap());
    let mut unavailable = reflected;
    let StructuredRegion::Compose { continuation, .. } = &mut unavailable.region else { panic!() };
    let StructuredRegion::Conditional { inputs, .. } = &mut **continuation else { panic!() };
    inputs.push(Port { id: 999, width: 8 });
    assert!(heather_elab::function_ir_cert::validate_structured_region(&unavailable.region).unwrap_err().contains("not available"));
}

fn reject_structured(image: &heather_elab::SemanticImage, name: &str, source: &str) {
    heather_syntax::parse_file(source).expect("mutation must parse");
    let error = image.elaborator().elab_module_source(name, source).expect_err("dishonest source certificate must fail");
    let message = error.render(source);
    assert!(!message.contains("unknown") && !message.contains("not in scope"), "wrong rejection: {message}");
}

#[test]
fn structured_composition_model_checks_open_contracts() {
    let mut elab = source_elaborator();
    let model = include_str!("../../../lib/function_ir.hthr");
    elab.elab_module_source("function_ir", model).unwrap_or_else(|e| panic!("{}", e.render(model)));
    let positive = r#"
import function_ir; import list; import logic;
theorem composition(prefix, next: StructuredRegion, values: Valuation(),
    first: StructuredRegionValid(prefix),
    bindings: InterfaceSubset(structured_inputs(next).entries, structured_inputs(prefix).entries ++ structured_outputs(prefix).entries),
    last: StructuredRegionValid(next), a: StructuredRegionHolds(values, prefix), b: StructuredRegionHolds(values, next)):
    StructuredRegionValid(Compose(prefix, next)) ∧ StructuredRegionHolds(values, Compose(prefix, next)) {
    ⟨structured_compose_valid(prefix, next, first, bindings, last), structured_compose_holds(values, prefix, next, a, b)⟩
}
"#;
    elab.elab_module_source("composition_laws", positive).unwrap_or_else(|e| panic!("{}", e.render(positive)));
    let negative = positive.replace("structured_compose_holds(values, prefix, next, a, b)", "structured_compose_holds(values, prefix, next, a, a)");
    assert_ne!(negative, positive);
    reject_structured(&elab.semantic_image(), "wrong_continuation", &negative);
}

#[test]
fn helper_expansion_has_a_structural_depth_bound() {
    let mut elab = source_elaborator();
    let mut source = String::from("import bitvec; import bool; fn helper0(a, b: BitVec(8)) → Bool { True }\n");
    for i in 1..=32 {
        source.push_str(&format!("fn helper{i}(a, b: BitVec(8)) → Bool {{ helper{}(a, b) }}\n", i - 1));
    }
    elab.elab_module_source("helper_depth", &source).unwrap_or_else(|e| panic!("{}", e.render(&source)));
    assert!(reflect_elaborated_structured(&elab, "helper31").is_ok());
    assert!(reflect_elaborated_structured(&elab, "helper32").unwrap_err().to_string().contains("deep helper"));
}

#[path = "support/structured_composition.rs"]
mod composed_fixture;

#[test]
fn composed_multiple_results_execute_and_protect_each_other() {
    use heather_elab::function_ir_x86_lower::lower_structured_results;
    let region = composed_fixture::fixture();
    let scratch = &[Gpr::Rax, Gpr::Rdx, Gpr::Rcx, Gpr::Rbx, Gpr::R8, Gpr::R9];
    let outputs = Placements::from([(5, Gpr::Rax), (6, Gpr::Rdx)]);
    let plan = lower_structured_results(&region, &placement(), scratch, &outputs).unwrap();
    for a in [0u64, 1, 9, u64::MAX, 1 << 63] {
        for b in [0u64, 1, 10, u64::MAX, 1 << 63] {
            let mut regs = BTreeMap::from([(Gpr::Rdi, a), (Gpr::Rsi, b)]);
            for r in scratch { regs.insert(*r, u64::MAX); }
            run(&plan, &mut regs);
            let difference = if a < b { b.wrapping_sub(a) } else { a.wrapping_sub(b) };
            assert_eq!(regs[&Gpr::Rax], a.wrapping_add(b).wrapping_sub(difference));
            assert_eq!(regs[&Gpr::Rdx], u64::from(difference < a));
            assert_eq!((regs[&Gpr::Rdi], regs[&Gpr::Rsi]), (a, b));
        }
    }
    for invalid in [Placements::from([(5, Gpr::Rax), (6, Gpr::Rax)]), Placements::from([(5, Gpr::Rax), (7, Gpr::Rdx)])] {
        assert!(lower_structured_results(&region, &placement(), scratch, &invalid).is_err());
    }
    assert!(lower_structured_results(&region, &placement(), &[Gpr::Rax, Gpr::Rdx], &outputs).is_err());
}

#[test]
fn composed_branch_preserves_an_inherited_selector() {
    let word = |id| Port { id, width: 64 };
    let bit = Port { id: 0, width: 1 };
    let branch = StructuredRegion::Conditional {
        inputs: vec![bit, word(1)], condition: 0, arguments: vec![word(1)], outputs: vec![word(2)],
        when_true: Box::new(StructuredRegion::Dataflow(Region { inputs: vec![word(1)], nodes: vec![Node::Add { width: 64, output: 2, left: 1, right: 1 }], outputs: vec![word(2)] })),
        when_false: Box::new(StructuredRegion::Dataflow(Region { inputs: vec![word(1)], nodes: vec![Node::Sub { width: 64, output: 2, left: 1, right: 1 }], outputs: vec![word(2)] })),
    };
    let region = StructuredRegion::Compose { prefix: Box::new(branch), continuation: Box::new(StructuredRegion::Conditional {
        inputs: vec![bit, word(2)], condition: 0, arguments: vec![word(2)], outputs: vec![word(3)],
        when_true: Box::new(StructuredRegion::Dataflow(Region { inputs: vec![word(2)], nodes: vec![Node::Add { width: 64, output: 3, left: 2, right: 2 }], outputs: vec![word(3)] })),
        when_false: Box::new(StructuredRegion::Dataflow(Region { inputs: vec![word(2)], nodes: vec![Node::Const { width: 64, output: 3, value: 9 }], outputs: vec![word(3)] })),
    }) };
    let plan = lower_structured(&region, &Placements::from([(0, Gpr::Rdi), (1, Gpr::Rsi)]), SCRATCH, Gpr::Rax).unwrap();
    assert!(!plan.clobbered.contains(&Gpr::Rdi));
    for flag in [0, 1] {
        let mut regs = BTreeMap::from([(Gpr::Rdi, flag), (Gpr::Rsi, 7)]);
        run(&plan, &mut regs);
        assert_eq!(regs[&Gpr::Rax], if flag == 0 { 9 } else { 28 });
        assert_eq!(regs[&Gpr::Rdi], flag);
    }
}
