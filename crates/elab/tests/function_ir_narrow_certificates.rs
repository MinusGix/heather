#[path = "function_ir_x86.rs"]
mod common;

use heather_elab::function_ir_cert::{Node, Port, Region, StructuredRegion};
use heather_elab::function_ir_x86_lower::{generate_structured, Gpr, Placements};

const IMPORTS: &str = "import x86_64_structured_block; import function_ir; import function_ir_x86_support; import x86_64; import x86_64_block; import bitvec; import bool; import list; import logic; import nat;";

fn checker() -> heather_elab::Elaborator {
    let mut elab = common::base_image(common::MODULES.len());
    let model = include_str!("../../../lib/std/arch/x86_64/structured_block.hthr");
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
        ("byte_less", Region { inputs: vec![Port { id: 0, width: 8 }, Port { id: 1, width: 8 }], nodes: vec![Node::UnsignedLessThan { width: 8, output: 2, left: 0, right: 1 }], outputs: vec![Port { id: 2, width: 1 }] }, Placements::from([(0, Gpr::Rdi), (1, Gpr::Rsi)])),
    ] {
        let emission = generate_structured(name, &StructuredRegion::Dataflow(region), &inputs, &[Gpr::Rax, Gpr::Rcx, Gpr::Rdx], Gpr::Rax).unwrap();
        if name == "byte_bitwise" {
            let heather_elab::function_ir_x86_lower::StructuredPlan::Dataflow(dag) = &emission.lowered.body else { panic!() };
            assert_eq!(dag.node_plans.last().unwrap().orientation, heather_elab::function_ir_x86_lower::OperandOrientation::Reversed);
        }
        let source = format!("{IMPORTS}\n{}", emission.text);
        elab.elab_module_source(name, &source).unwrap_or_else(|e| panic!("{}", e.render(&source)));
    }
    let invalid = "import bitvec; import bool; import logic; theorem signed_is_unsigned(a, b: BitVec(8)): bitvec::signed_lt_bit(8, a, b) = bitvec::unsigned_lt_bit(64, bitvec::zero_extend(8, 56, a), bitvec::zero_extend(8, 56, b)) { sym(bitvec::unsigned_lt_zero_extend(8, 56, a, b)) }";
    let error = elab.elab_module_source("wrong_signed_extension", invalid).expect_err("zero extension does not preserve signed comparison");
    assert!(!error.render(invalid).contains("unknown"));
}
