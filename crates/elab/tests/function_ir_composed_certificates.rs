use crate::common;

use crate::composed_fixture;

#[test]
fn composed_multiple_result_certificates_check() {
    use heather_elab::function_ir_x86_lower::{generate_structured_results, Gpr, Placements};
    let mut elab = common::structured_base();
    let emission = generate_structured_results("composed", &composed_fixture::fixture(), &Placements::from([(0, Gpr::Rdi), (1, Gpr::Rsi)]),
        &[Gpr::Rax, Gpr::Rdx, Gpr::Rcx, Gpr::Rbx, Gpr::R8, Gpr::R9], &Placements::from([(5, Gpr::Rax), (6, Gpr::Rdx)])).unwrap();
    let imports = "import x86_64_structured_block; import function_ir; import function_ir_x86_support; import x86_64; import x86_64_block; import bitvec; import bool; import list; import logic; import nat;";
    let text = format!("{imports}\n{}", emission.text);
    elab.elab_module_source("composed_certificate", &text).unwrap_or_else(|e| panic!("{}", e.render(&text)));
    let image = elab.semantic_image();
    let parameters = "values: Valuation(), before: MachineState<M>, a: values(64, 0) = read_gpr(Rdi, before.gprs), b: values(64, 1) = read_gpr(Rsi, before.gprs)";
    for (name, claim, proof) in [
        ("wrong_second_destination", "read_gpr(Rax, composed_after(before).gprs) = composed_output_6_result(values)", "composed_output_6_correct(values, before, a, b)"),
        ("wrong_second_value", "read_gpr(Rdx, composed_after(before).gprs) = composed_result(values)", "composed_output_6_correct(values, before, a, b)"),
        ("wrong_carried_binding", "read_gpr(Rbx, composed_prefix_after(before).gprs) = composed_prefix_output_4_result(values)", "composed_prefix_correct(values, before, a, b)"),
        ("wrong_frame", "read_gpr(Rdx, composed_after(before).gprs) = read_gpr(Rdx, before.gprs)", "composed_preserves(Rdx, before, trivial)"),
    ] {
        let mutant = format!("{imports} import composed_certificate; theorem {name}<M>({parameters}): {claim} {{ {proof} }}");
        heather_syntax::parse_file(&mutant).unwrap();
        let error = image.elaborator().elab_module_source(name, &mutant).expect_err("dishonest multi-result certificate must fail");
        let message = error.render(&mutant);
        assert!(!message.contains("unknown") && !message.contains("not in scope"), "{message}");
    }
}
