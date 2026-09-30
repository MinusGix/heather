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
    ] {
        let emission = generate_structured(name, &StructuredRegion::Dataflow(region), &inputs, &[Gpr::Rax, Gpr::Rcx, Gpr::Rdx], Gpr::Rax).unwrap();
        if name == "byte_bitwise" || name == "byte_add_reversed" {
            let heather_elab::function_ir_x86_lower::StructuredPlan::Dataflow(dag) = &emission.lowered.body else { panic!() };
            assert_eq!(dag.node_plans.last().unwrap().orientation, heather_elab::function_ir_x86_lower::OperandOrientation::Reversed);
        }
        let source = format!("{IMPORTS}\n{}", emission.text);
        elab.elab_module_source(name, &source).unwrap_or_else(|e| panic!("{}", e.render(&source)));
    }
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
