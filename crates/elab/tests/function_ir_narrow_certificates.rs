use crate::common;

use heather_elab::function_ir_cert::{Node, Port, Region, StructuredRegion};
use heather_elab::function_ir_x86_lower::{generate_structured, Gpr, Placements};

const IMPORTS: &str = "import x86_64_structured_block; import function_ir; import function_ir_x86_support; import x86_64; import x86_64_block; import bitvec; import bool; import list; import logic; import nat;";

fn checker() -> heather_elab::Elaborator {
    let mut elab = common::base_image(common::MODULES.len());
    let model = include_str!("../../../lib/std/arch/x86_64/x86_64_structured_block.hthr");
    elab.elab_module_source("x86_64_structured_block", model).unwrap_or_else(|e| panic!("{}", e.render(model)));
    elab
}

#[test]
fn narrow_constants_passthrough_and_comparisons_check() {
    let mut elab = checker();
    for (name, region, inputs) in [
        ("byte_constant", Region { inputs: vec![], nodes: vec![Node::Const { width: 8, output: 0, value: 511 }], outputs: vec![Port { id: 0, width: 8 }] }, Placements::new()),
        ("empty_constant", Region { inputs: vec![], nodes: vec![Node::Const { width: 0, output: 0, value: 511 }], outputs: vec![Port { id: 0, width: 0 }] }, Placements::new()),
        ("byte_bitwise", Region { inputs: vec![Port { id: 0, width: 8 }, Port { id: 1, width: 8 }], nodes: vec![
            Node::Const { width: 8, output: 3, value: 255 },
            Node::BitAnd { width: 8, output: 4, left: 0, right: 1 },
            Node::BitXor { width: 8, output: 5, left: 4, right: 3 },
        ], outputs: vec![Port { id: 5, width: 8 }] }, Placements::from([(0, Gpr::Rdi), (1, Gpr::Rsi)])),
        ("boolean_copy", Region { inputs: vec![Port { id: 0, width: 1 }], nodes: vec![], outputs: vec![Port { id: 0, width: 1 }] }, Placements::from([(0, Gpr::Rdi)])),
        // Narrow sums and differences: copied into the result, in place at
        // the left operand's last use, reversed onto the right's, at a width
        // of none, and in a chain whose sum feeds a difference.
        ("byte_add", Region { inputs: vec![Port { id: 0, width: 8 }, Port { id: 1, width: 8 }], nodes: vec![Node::Add { width: 8, output: 2, left: 0, right: 1 }],
            outputs: vec![Port { id: 2, width: 8 }] }, Placements::from([(0, Gpr::Rdi), (1, Gpr::Rsi)])),
        ("byte_sub_constant", Region { inputs: vec![Port { id: 0, width: 8 }], nodes: vec![
            Node::Const { width: 8, output: 1, value: 0x20 },
            Node::Sub { width: 8, output: 2, left: 0, right: 1 },
        ], outputs: vec![Port { id: 2, width: 8 }] }, Placements::from([(0, Gpr::Rdi)])),
        ("byte_add_reversed", Region { inputs: vec![Port { id: 0, width: 8 }, Port { id: 1, width: 8 }], nodes: vec![
            Node::Const { width: 8, output: 3, value: 13 },
            Node::BitAnd { width: 8, output: 4, left: 0, right: 1 },
            Node::Add { width: 8, output: 5, left: 4, right: 3 },
        ], outputs: vec![Port { id: 5, width: 8 }] }, Placements::from([(0, Gpr::Rdi), (1, Gpr::Rsi)])),
        ("empty_sub", Region { inputs: vec![Port { id: 0, width: 0 }, Port { id: 1, width: 0 }], nodes: vec![Node::Sub { width: 0, output: 2, left: 0, right: 1 }],
            outputs: vec![Port { id: 2, width: 0 }] }, Placements::from([(0, Gpr::Rdi), (1, Gpr::Rsi)])),
        ("half_chain", Region { inputs: vec![Port { id: 0, width: 16 }, Port { id: 1, width: 16 }], nodes: vec![
            Node::Add { width: 16, output: 2, left: 0, right: 1 },
            Node::Sub { width: 16, output: 3, left: 2, right: 1 },
        ], outputs: vec![Port { id: 3, width: 16 }] }, Placements::from([(0, Gpr::Rdi), (1, Gpr::Rsi)])),
        ("byte_less", Region { inputs: vec![Port { id: 0, width: 8 }, Port { id: 1, width: 8 }], nodes: vec![Node::UnsignedLessThan { width: 8, output: 2, left: 0, right: 1 }], outputs: vec![Port { id: 2, width: 1 }] }, Placements::from([(0, Gpr::Rdi), (1, Gpr::Rsi)])),
        // Narrow equality, of two open bytes and of a byte with a literal,
        // compared zero-extended (`eq_bit_zero_extend`).
        ("byte_equal", Region { inputs: vec![Port { id: 0, width: 8 }, Port { id: 1, width: 8 }], nodes: vec![Node::Equal { width: 8, output: 2, left: 0, right: 1 }], outputs: vec![Port { id: 2, width: 1 }] }, Placements::from([(0, Gpr::Rdi), (1, Gpr::Rsi)])),
        ("byte_is_newline", Region { inputs: vec![Port { id: 0, width: 8 }], nodes: vec![
            Node::Const { width: 8, output: 1, value: 10 },
            Node::Equal { width: 8, output: 2, left: 0, right: 1 },
        ], outputs: vec![Port { id: 2, width: 1 }] }, Placements::from([(0, Gpr::Rdi)])),
    ] {
        let emission = generate_structured(name, &StructuredRegion::Dataflow(region), &inputs, &[Gpr::Rax, Gpr::Rcx, Gpr::Rdx], Gpr::Rax).unwrap();
        if name == "byte_bitwise" || name == "byte_add_reversed" {
            let heather_elab::function_ir_x86_lower::StructuredPlan::Dataflow(dag) = &emission.lowered.body else { panic!() };
            assert_eq!(dag.node_plans.last().unwrap().orientation, heather_elab::function_ir_x86_lower::OperandOrientation::Reversed);
        }
        let source = format!("{IMPORTS}\n{}", emission.text);
        elab.elab_module_source(name, &source).unwrap_or_else(|e| panic!("{}", e.render(&source)));
        if name.starts_with("byte_equal") || name == "byte_is_newline" {
            assert!(emission.text.contains("SetEqual(") && emission.text.contains("eq_bit_zero_extend(8, 56,"), "{}", emission.text);
        }
    }
    // Zero extension preserves equality but not a truncation: the law is
    // refused at a wider operand truncated back.
    let truncated = "import bitvec; import bool; import logic; theorem truncated_equal(a, b: BitVec(16)): @bitvec::BitVec::eq_bit(8, bitvec::BitVec::truncate(8, 8, a), bitvec::BitVec::truncate(8, 8, b)) = @bitvec::BitVec::eq_bit(16, a, b) { bitvec::BitVec::eq_bit_zero_extend(8, 8, bitvec::BitVec::truncate(8, 8, a), bitvec::BitVec::truncate(8, 8, b)) }";
    let error = elab.elab_module_source("truncated_equal", truncated).expect_err("truncation does not preserve equality");
    assert!(!error.render(truncated).contains("unknown"));
    let invalid = "import bitvec; import bool; import logic; theorem signed_is_unsigned(a, b: BitVec(8)): @bitvec::BitVec::signed_lt_bit(8, a, b) = @bitvec::BitVec::unsigned_lt_bit(64, @bitvec::BitVec::zero_extend(8, 56, a), @bitvec::BitVec::zero_extend(8, 56, b)) { sym(bitvec::BitVec::unsigned_lt_zero_extend(8, 56, a, b)) }";
    let error = elab.elab_module_source("wrong_signed_extension", invalid).expect_err("zero extension does not preserve signed comparison");
    assert!(!error.render(invalid).contains("unknown"));
    // The word's sum is not the narrow one: only the mask makes it so.
    let unmasked = "import bitvec; import bool; import logic; theorem unmasked_sum(a, b: BitVec(8)): @bitvec::BitVec::zero_extend(8, 56, bitvec::BitVec::add(a, b)) = bitvec::BitVec::add(@bitvec::BitVec::zero_extend(8, 56, a), @bitvec::BitVec::zero_extend(8, 56, b)) { sym(bitvec::BitVec::add_zero_extend_mask(8, 56, a, b)) }";
    let error = elab.elab_module_source("unmasked_sum", unmasked).expect_err("a narrow sum is the word's only under the mask");
    assert!(!error.render(unmasked).contains("unknown"));
    let masked = unmasked.replace("theorem unmasked_sum", "theorem masked_sum").replace("{ sym(", "{ sym(").replace(
        "= bitvec::BitVec::add(@bitvec::BitVec::zero_extend(8, 56, a), @bitvec::BitVec::zero_extend(8, 56, b))",
        "= bitvec::BitVec::band(bitvec::BitVec::add(@bitvec::BitVec::zero_extend(8, 56, a), @bitvec::BitVec::zero_extend(8, 56, b)), @bitvec::BitVec::ofNat(64, 255))");
    elab.elab_module_source("masked_sum", &masked).unwrap_or_else(|e| panic!("{}", e.render(&masked)));
}

// A byte comparison a branch alone reads fuses into CMP + Jcc on the
// zero-extended words (`eq_bit_zero_extend`, `unsigned_lt_zero_extend`):
// against a literal and against a computed sum, for equality and for the
// unsigned order. A branch testing another condition, or the operands the
// other way round, is refused; a narrow signed comparison is not fused.
#[test]
fn narrow_fused_branches_check_and_refuse_another_test() {
    use heather_elab::function_ir_x86_lower::{ComparisonOperation, PlannedTest, StructuredPlan};
    let elab = checker();
    let byte = |id| Port { id, width: 8 };
    let bit = Port { id: 3, width: 1 };
    let arm = |node| Box::new(StructuredRegion::Dataflow(Region { inputs: vec![byte(0), byte(1)], nodes: vec![node], outputs: vec![byte(4)] }));
    let branch = |when_true, when_false| Box::new(StructuredRegion::Conditional { inputs: vec![bit, byte(0), byte(1)], condition: 3,
        arguments: vec![byte(0), byte(1)], outputs: vec![byte(4)], when_true, when_false });
    let region = |operand: Node, compare: Node| StructuredRegion::Sequence {
        prefix: Region { inputs: vec![byte(0), byte(1)], nodes: vec![operand, compare], outputs: vec![bit] },
        continuation: branch(arm(Node::Sub { width: 8, output: 4, left: 1, right: 0 }), arm(Node::BitXor { width: 8, output: 4, left: 0, right: 1 })),
    };
    let newline = Node::Const { width: 8, output: 2, value: 10 };
    let sum = Node::Add { width: 8, output: 2, left: 0, right: 1 };
    let cases = [
        ("byte_is_newline_branch", region(newline, Node::Equal { width: 8, output: 3, left: 0, right: 2 }), ComparisonOperation::Equal, "E", ["NE", "B", "LE"]),
        ("byte_sum_equal_branch", region(sum, Node::Equal { width: 8, output: 3, left: 2, right: 1 }), ComparisonOperation::Equal, "E", ["NE", "B", "L"]),
        ("byte_below_newline_branch", region(newline, Node::UnsignedLessThan { width: 8, output: 3, left: 0, right: 2 }), ComparisonOperation::UnsignedLessThan, "B", ["AE", "L", "E"]),
        ("byte_sum_below_branch", region(sum, Node::UnsignedLessThan { width: 8, output: 3, left: 2, right: 0 }), ComparisonOperation::UnsignedLessThan, "B", ["AE", "L", "BE"]),
    ];
    for (name, region, expected, cc, others) in cases {
        let emission = generate_structured(name, &region, &Placements::from([(0, Gpr::Rdi), (1, Gpr::Rsi)]), &[Gpr::Rax, Gpr::Rcx, Gpr::Rdx, Gpr::R8], Gpr::Rax)
            .unwrap_or_else(|e| panic!("{name}: {e:?}"));
        let StructuredPlan::FusedSequence { continuation, .. } = &emission.lowered.body else { panic!("{name}: expected a fused sequence, got {:?}", emission.lowered.body) };
        let StructuredPlan::Conditional { test: PlannedTest::Compare { left, right, operation, width, .. }, .. } = continuation.body else { panic!("{name}: expected a compared branch") };
        assert_eq!((operation, width), (expected, 8), "{name}");
        let text = format!("{IMPORTS}\n{}", emission.text);
        assert!(!text.contains("SetEqual(") && !text.contains("SetBelow("), "{name}: the bit is not materialised");
        elab.semantic_image().elaborator().elab_module_source(&format!("{name}_certificate"), &text).unwrap_or_else(|e| panic!("{}", e.render(&text)));
        let (l, r) = (left.heather_name(), right.heather_name());
        let code = format!("CodeBranch(Compare({l}, {r}, {cc})");
        assert!(text.contains(&code), "{name}: the code should branch on Compare({l}, {r}, {cc})");
        let swapped = format!("CodeBranch(Compare({r}, {l}, {cc})");
        for mutant in others.iter().map(|other| text.replacen(&code, &format!("CodeBranch(Compare({l}, {r}, {other})"), 1))
            .chain((expected == ComparisonOperation::UnsignedLessThan).then(|| text.replacen(&code, &swapped, 1))) {
            let error = elab.semantic_image().elaborator().elab_module_source(&format!("{name}_mutant"), &mutant)
                .expect_err("a branch testing something else must be refused");
            let message = error.render(&mutant);
            assert!(!message.contains("unknown") && !message.contains("not in scope") && !message.contains("unbound"), "{name} failed on a name: {message}");
        }
    }
    let signed = region(newline, Node::SignedLessThan { width: 8, output: 3, left: 0, right: 2 });
    if let Ok(emission) = generate_structured("byte_signed_branch", &signed, &Placements::from([(0, Gpr::Rdi), (1, Gpr::Rsi)]), &[Gpr::Rax, Gpr::Rcx, Gpr::Rdx, Gpr::R8], Gpr::Rax) {
        assert!(!matches!(emission.lowered.body, StructuredPlan::FusedSequence { .. }), "a narrow signed comparison is not fused");
    }
}

// With only REX registers to spare, a materialised comparison lands in one
// (SETcc into R8B–R15B under REX.B, into SIL, DIL or BPL under an empty
// REX), a byte longer than into AL–BL, and its certificate checks; naming
// another byte register in its place is refused.
#[test]
fn comparisons_materialise_into_rex_byte_registers() {
    use heather_elab::function_ir_x86_lower::{encode_structured, StructuredPlan};
    let elab = checker();
    let byte = |id| Port { id, width: 8 };
    let word = |id| Port { id, width: 64 };
    for (name, region, inputs, temporaries, output, sets) in [
        ("rex_byte_equal", Region { inputs: vec![byte(0), byte(1)], nodes: vec![Node::Equal { width: 8, output: 2, left: 0, right: 1 }], outputs: vec![Port { id: 2, width: 1 }] },
            Placements::from([(0, Gpr::Rax), (1, Gpr::Rcx)]), vec![Gpr::R9, Gpr::R10], Gpr::R9, &["SetEqual(R9b)"][..]),
        ("rex_word_below", Region { inputs: vec![word(0), word(1)], nodes: vec![Node::UnsignedLessThan { width: 64, output: 2, left: 0, right: 1 }], outputs: vec![Port { id: 2, width: 1 }] },
            Placements::from([(0, Gpr::Rdi), (1, Gpr::Rdx)]), vec![Gpr::Rsi, Gpr::R15], Gpr::Rsi, &["SetBelow(Sil)"][..]),
        ("rex_word_less", Region { inputs: vec![word(0), word(1)], nodes: vec![Node::SignedLessThan { width: 64, output: 2, left: 0, right: 1 }], outputs: vec![Port { id: 2, width: 1 }] },
            Placements::from([(0, Gpr::Rdi), (1, Gpr::Rdx)]), vec![Gpr::R15, Gpr::Rbp], Gpr::R15, &["SetLess(R15b)"][..]),
        ("rex_byte_newline", Region { inputs: vec![byte(0)], nodes: vec![Node::Const { width: 8, output: 1, value: 10 }, Node::Equal { width: 8, output: 2, left: 0, right: 1 }],
            outputs: vec![Port { id: 2, width: 1 }] }, Placements::from([(0, Gpr::Rax)]), vec![Gpr::Rbp, Gpr::R11], Gpr::Rbp, &["SetEqual(Bpl)", "SetEqual(R11b)"][..]),
    ] {
        let emission = generate_structured(name, &StructuredRegion::Dataflow(region), &inputs, &temporaries, output).unwrap_or_else(|e| panic!("{name}: {e:?}"));
        let StructuredPlan::Dataflow(dag) = &emission.lowered.body else { panic!("{name}: a dataflow plan") };
        let bytes = encode_structured(&emission.lowered);
        assert_eq!(bytes.len(), emission.lowered.byte_length, "{name}: the planned length is the encoding's");
        assert_eq!(dag.instructions.iter().map(|i| i.canonical_length()).sum::<usize>(), bytes.len(), "{name}");
        let source = format!("{IMPORTS}\n{}", emission.text);
        let set = *sets.iter().find(|set| source.contains(**set)).unwrap_or_else(|| panic!("{name}: expected one of {sets:?}"));
        elab.semantic_image().elaborator().elab_module_source(name, &source).unwrap_or_else(|e| panic!("{}", e.render(&source)));
        let other = if set.contains("R9b") { set.replace("R9b", "R10b") } else if set.contains("Sil") { set.replace("Sil", "Dil") } else if set.contains("R15b") { set.replace("R15b", "R14b") } else if set.contains("Bpl") { set.replace("Bpl", "Bl") } else { set.replace("R11b", "R12b") };
        let mutant = source.replace(set, &other);
        let error = elab.semantic_image().elaborator().elab_module_source(&format!("{name}_mutant"), &mutant).expect_err("another byte register must be refused");
        let message = error.render(&mutant);
        assert!(!message.contains("unknown") && !message.contains("not in scope") && !message.contains("unbound"), "{name} failed on a name: {message}");
    }
}

// A fused byte test whose true arm is past rel8's reach takes the near
// jumps (JNE rel32, JMP rel32), and its certificate checks.
#[test]
fn a_narrow_fused_branch_past_rel8_is_near() {
    use heather_elab::function_ir_x86_lower::{encode_structured, PlannedTest, StructuredPlan};
    let elab = checker();
    let word = |id| Port { id, width: 64 };
    let byte = |id| Port { id, width: 8 };
    let bit = Port { id: 3, width: 1 };
    // Sixteen constants past imm32, each a 10-byte load and an ADD.
    let mut long = Vec::new();
    let mut last = 0;
    for k in 0..16u64 {
        long.push(Node::Const { width: 64, output: 100 + 2 * k, value: (1 << 40) + k });
        long.push(Node::Add { width: 64, output: 101 + 2 * k, left: last, right: 100 + 2 * k });
        last = 101 + 2 * k;
    }
    long.push(Node::Move { width: 64, output: 4, source: last });
    let arm = |nodes| Box::new(StructuredRegion::Dataflow(Region { inputs: vec![word(0), byte(1)], nodes, outputs: vec![word(4)] }));
    let region = StructuredRegion::Sequence {
        prefix: Region { inputs: vec![word(0), byte(1)], nodes: vec![Node::Const { width: 8, output: 2, value: 10 }, Node::Equal { width: 8, output: 3, left: 1, right: 2 }], outputs: vec![bit] },
        continuation: Box::new(StructuredRegion::Conditional { inputs: vec![bit, word(0), byte(1)], condition: 3, arguments: vec![word(0), byte(1)], outputs: vec![word(4)],
            when_true: arm(long), when_false: arm(vec![Node::Move { width: 64, output: 4, source: 0 }]) }),
    };
    let emission = generate_structured("near_byte_branch", &region, &Placements::from([(0, Gpr::Rdi), (1, Gpr::Rsi)]), &[Gpr::Rax, Gpr::Rcx, Gpr::Rdx, Gpr::R8], Gpr::Rax)
        .unwrap_or_else(|e| panic!("{e:?}"));
    let StructuredPlan::FusedSequence { continuation, .. } = &emission.lowered.body else { panic!("expected a fused sequence, got {:?}", emission.lowered.body) };
    let StructuredPlan::Conditional { test: PlannedTest::Compare { width: 8, .. }, near: true, .. } = continuation.body else { panic!("expected a near byte comparison") };
    assert_eq!(encode_structured(&emission.lowered).len(), emission.lowered.byte_length);
    let text = format!("{IMPORTS}\n{}", emission.text);
    assert!(text.contains("CodeBranchNear(Compare("), "expected a near compared branch");
    elab.semantic_image().elaborator().elab_module_source("near_byte_branch_certificate", &text).unwrap_or_else(|e| panic!("{}", e.render(&text)));
}
