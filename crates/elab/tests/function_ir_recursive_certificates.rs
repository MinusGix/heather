use crate::common;

#[test]
fn recursive_physical_model_checks() {
    let mut elab = common::base_image(common::MODULES.len());
    let model = include_str!("../../../lib/std/arch/x86_64/structured_block.hthr");
    elab.elab_module_source("x86_64_structured_block", model)
        .unwrap_or_else(|e| panic!("{}", e.render(model)));
}

#[test]
fn recursive_leaf_certificate_checks() {
    use heather_elab::function_ir_cert::{Node, Port, Region, StructuredRegion};
    use heather_elab::function_ir_x86_lower::{generate_structured, Gpr, Placements};
    let mut elab = common::base_image(common::MODULES.len());
    let model = include_str!("../../../lib/std/arch/x86_64/structured_block.hthr");
    elab.elab_module_source("x86_64_structured_block", model).unwrap_or_else(|e| panic!("{}", e.render(model)));
    let region = StructuredRegion::Dataflow(Region { inputs: vec![Port { id: 0, width: 64 }, Port { id: 1, width: 64 }], nodes: vec![Node::Add { width: 64, output: 2, left: 0, right: 1 }], outputs: vec![Port { id: 2, width: 64 }] });
    let emission = generate_structured("recursive", &region, &Placements::from([(0, Gpr::Rdi), (1, Gpr::Rsi)]), &[Gpr::Rax, Gpr::Rcx, Gpr::Rdx], Gpr::Rax).unwrap();
    let text = format!("import x86_64_structured_block; import function_ir; import function_ir_x86_support; import x86_64; import x86_64_block; import bitvec; import bool; import list; import logic; import nat;\n{}", emission.text);
    elab.elab_module_source("recursive_certificate", &text).unwrap_or_else(|e| panic!("{}", e.render(&text)));
}

#[test]
fn nested_source_physical_certificate_checks() {
    use heather_elab::function_ir_source::generate_elaborated_structured_x86;
    use heather_elab::function_ir_x86_lower::Gpr;
    let mut elab = common::base_image(common::MODULES.len());
    let model = include_str!("../../../lib/std/arch/x86_64/structured_block.hthr");
    elab.elab_module_source("x86_64_structured_block", model).unwrap_or_else(|e| panic!("{}", e.render(model)));
    let source = include_str!("../../../examples/x86-native/branches.hthr");
    elab.elab_module_source("branches", source).unwrap_or_else(|e| panic!("{}", e.render(source)));
    let emission = generate_elaborated_structured_x86(&elab, "nested", "branches::nested_true", [Gpr::Rdi, Gpr::Rsi], &[Gpr::Rax, Gpr::Rcx, Gpr::Rdx, Gpr::R8], Gpr::Rax).unwrap();
    let text = format!("import x86_64_structured_block; import function_ir; import function_ir_x86_support; import x86_64; import x86_64_block; import bitvec; import bool; import list; import logic; import nat;\n{}", emission.text);
    elab.elab_module_source("nested_certificate", &text).unwrap_or_else(|e| panic!("{}", e.render(&text)));
    let image = elab.semantic_image();
    use heather_elab::function_ir_x86_lower::StructuredPlan;
    let StructuredPlan::Sequence { continuation, .. } = &emission.lowered.body else { panic!() };
    let StructuredPlan::Conditional { condition_register, false_displacement, join_displacement, .. } = &continuation.body else { panic!() };
    let wrong_code = format!("CodeBranch({}, @bitvec::BitVec::ofNat(8, {}), @bitvec::BitVec::ofNat(8, {}), nested_continuation_true_code(), nested_continuation_false_code())", condition_register.heather_name(), false_displacement + 1, join_displacement);
    let imports = "import nested_certificate; import branches; import x86_64_structured_block; import x86_64; import function_ir; import bitvec; import logic;";
    for (name, claim) in [
        ("wrong_target", format!("theorem wrong_target(): StructuredLayout({wrong_code}) {{ nested_continuation_layout() }}")),
        ("wrong_encoding", format!("theorem wrong_encoding(): structured_bytes({wrong_code}) = nested_continuation_bytes() {{ refl }}")),
        ("wrong_clobber", "theorem wrong_clobber<M>(before: MachineState<M>): read_gpr(Rax, nested_after(before).gprs) = read_gpr(Rax, before.gprs) { nested_preserves(Rax, before, trivial) }".into()),
        ("wrong_binding", "theorem wrong_binding<M>(values: Valuation(), before: MachineState<M>, a: values(64, 0) = read_gpr(Rsi, before.gprs), b: values(64, 1) = read_gpr(Rdi, before.gprs)): read_gpr(Rax, nested_after(before).gprs) = nested_result(values) { nested_correct(values, before, a, b) }".into()),
        ("wrong_destination", "theorem wrong_destination<M>(before: MachineState<M>): StructuredArtifact<M>(nested_code(), before, Rdi, branches::nested_true(read_gpr(Rdi, before.gprs), read_gpr(Rsi, before.gprs)), nested_Protected) { nested_source_artifact(before) }".into()),
        ("stale_source", "theorem stale_source<M>(before: MachineState<M>): StructuredArtifact<M>(nested_code(), before, Rax, branches::nested_false(read_gpr(Rdi, before.gprs), read_gpr(Rsi, before.gprs)), nested_Protected) { nested_source_artifact(before) }".into()),
    ] {
        let mutant = format!("{imports}\n{claim}");
        heather_syntax::parse_file(&mutant).expect("negative control must parse");
        let error = image.elaborator().elab_module_source(name, &mutant).expect_err("dishonest artifact must be rejected");
        let message = error.render(&mutant);
        assert!(!message.contains("unknown") && !message.contains("not in scope"), "negative control failed on a missing name: {message}");
    }
}
