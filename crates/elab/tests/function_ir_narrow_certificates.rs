#[path = "function_ir_x86.rs"]
mod common;

use heather_elab::function_ir_cert::{Node, Port, Region, StructuredRegion};
use heather_elab::function_ir_x86_lower::{generate_structured, generate_structured_results, Gpr, Placements};

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

#[test]
fn search_body_uses_shared_narrow_physical_certificates() {
    use heather_elab::function_ir_source::{reflect_elaborated_structured, generate_structured_source_expansion};
    let mut elab = checker();
    let model = include_str!("../../../lib/function_ir_loop.hthr");
    elab.elab_module_source("function_ir_loop", model).unwrap_or_else(|e| panic!("{}", e.render(model)));
    let source = include_str!("../../../examples/function-ir/readonly-loops.hthr");
    elab.elab_module_source("readonly_loops", source).unwrap_or_else(|e| panic!("{}", e.render(source)));
    let body = reflect_elaborated_structured(&elab, "readonly_loops::search_body").unwrap();
    let expansion = generate_structured_source_expansion("search_source", &body).unwrap();
    elab.elab_module_source("search_source", &expansion).unwrap_or_else(|e| panic!("{}", e.render(&expansion)));
    let emission = generate_structured_results("search", &body.region,
        &Placements::from([(0, Gpr::Rdi), (2, Gpr::Rsi), (3, Gpr::R8)]),
        &[Gpr::Rax, Gpr::Rdx, Gpr::Rcx, Gpr::R9, Gpr::R10],
        &Placements::from([(4, Gpr::Rax), (5, Gpr::Rdx)])).unwrap();
    let text = format!("{IMPORTS}\n{}", emission.text);
    elab.elab_module_source("search_physical", &text).unwrap_or_else(|e| panic!("{}", e.render(&text)));
    let negative = format!("{IMPORTS} import search_physical; theorem wrong_byte_placement<M>(values: Valuation(), before: MachineState<M>, needle: values(64, 0) = read_gpr(Rdi, before.gprs), byte: values(64, 2) = read_gpr(Rsi, before.gprs), found: bitvec::zero_extend(1, 63, values(1, 3)) = read_gpr(R8, before.gprs)): read_gpr(Rax, search_after(before).gprs) = search_result(values) {{ search_correct(values, before, needle, byte, found) }}");
    heather_syntax::parse_file(&negative).unwrap();
    let error = elab.elab_module_source("wrong_byte_placement", &negative).expect_err("unnormalized word placement must not prove a byte placement");
    let message = error.render(&negative);
    assert!(!message.contains("unknown") && !message.contains("not in scope"), "{message}");
}
