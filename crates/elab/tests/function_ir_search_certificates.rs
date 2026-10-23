use crate::common;

use heather_elab::function_ir_x86_lower::{generate_structured_results, Gpr, Placements};

const IMPORTS: &str = "import x86_64_structured_block; import function_ir; import function_ir_x86_support; import x86_64; import x86_64_block; import bitvec; import bool; import list; import logic; import nat;";

fn checker() -> heather_elab::Elaborator {
    common::structured_base()
}

#[test]
fn search_body_uses_shared_narrow_physical_certificates() {
    use heather_elab::function_ir_source::{reflect_elaborated_structured, generate_structured_source_expansion};
    let mut elab = checker();
    let model = include_str!("../../../lib/native/function_ir/function_ir_loop.hthr");
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
    let negative = format!("{IMPORTS} import search_physical; theorem wrong_byte_placement<M>(values: Valuation(), before: MachineState<M>, needle: values(64, 0) = read_gpr(Rdi, before.gprs), byte: values(64, 2) = read_gpr(Rsi, before.gprs), found: @bitvec::BitVec::zero_extend(1, 63, values(1, 3)) = read_gpr(R8, before.gprs)): read_gpr(Rax, search_after(before).gprs) = search_result(values) {{ search_correct(values, before, needle, byte, found) }}");
    heather_syntax::parse_file(&negative).unwrap();
    let error = elab.elab_module_source("wrong_byte_placement", &negative).expect_err("unnormalized word placement must not prove a byte placement");
    let message = error.render(&negative);
    assert!(!message.contains("unknown") && !message.contains("not in scope"), "{message}");
}
