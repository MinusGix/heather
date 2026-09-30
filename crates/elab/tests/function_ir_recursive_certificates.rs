use crate::common;

#[test]
fn recursive_physical_model_checks() {
    let mut elab = common::base_image(common::MODULES.len());
    let model = include_str!("../../../lib/std/arch/x86_64/x86_64_structured_block.hthr");
    elab.elab_module_source("x86_64_structured_block", model)
        .unwrap_or_else(|e| panic!("{}", e.render(model)));
}

#[test]
fn recursive_leaf_certificate_checks() {
    use heather_elab::function_ir_cert::{Node, Port, Region, StructuredRegion};
    use heather_elab::function_ir_x86_lower::{generate_structured, Gpr, Placements};
    let mut elab = common::base_image(common::MODULES.len());
    let model = include_str!("../../../lib/std/arch/x86_64/x86_64_structured_block.hthr");
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
    let model = include_str!("../../../lib/std/arch/x86_64/x86_64_structured_block.hthr");
    elab.elab_module_source("x86_64_structured_block", model).unwrap_or_else(|e| panic!("{}", e.render(model)));
    let source = include_str!("../../../examples/x86-native/branches.hthr");
    elab.elab_module_source("branches", source).unwrap_or_else(|e| panic!("{}", e.render(source)));
    let emission = generate_elaborated_structured_x86(&elab, "nested", "branches::nested_true", [Gpr::Rdi, Gpr::Rsi], &[Gpr::Rax, Gpr::Rcx, Gpr::Rdx, Gpr::R8], Gpr::Rax).unwrap();
    let text = format!("import x86_64_structured_block; import function_ir; import function_ir_x86_support; import x86_64; import x86_64_block; import bitvec; import bool; import list; import logic; import nat;\n{}", emission.text);
    elab.elab_module_source("nested_certificate", &text).unwrap_or_else(|e| panic!("{}", e.render(&text)));
    let image = elab.semantic_image();
    use heather_elab::function_ir_x86_lower::StructuredPlan;
    let StructuredPlan::Sequence { continuation, .. } = &emission.lowered.body else { panic!() };
    let StructuredPlan::Conditional { test: heather_elab::function_ir_x86_lower::PlannedTest::NonZero(condition_register), false_displacement, join_displacement, .. } = &continuation.body else { panic!() };
    let wrong_code = format!("CodeBranch(NonZero({}), @bitvec::BitVec::ofNat(8, {}), @bitvec::BitVec::ofNat(8, {}), nested_continuation_true_code(), nested_continuation_false_code())", condition_register.heather_name(), false_displacement + 1, join_displacement);
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

// A comparison against a constant that only the branch reads certifies as
// CMP and a Jcc on its flags (docs/structured-lowering-code-size-design.md
// §2.2): from source (unsigned; the reflector reads no signed condition yet)
// and from a hand-built region (signed, the constant on the left). A
// certificate whose code tests the other condition code, or compares its
// operands the other way round, is refused.
#[test]
fn fused_compare_certificates_check_and_refuse_another_test() {
    use heather_elab::function_ir_cert::{Node, Port, Region, StructuredRegion};
    use heather_elab::function_ir_source::generate_elaborated_structured_x86;
    use heather_elab::function_ir_x86_lower::{generate_structured, Gpr, Placements, PlannedTest, StructuredPlan, StructuredX86Emission};
    let mut elab = common::base_image(common::MODULES.len());
    let model = include_str!("../../../lib/std/arch/x86_64/x86_64_structured_block.hthr");
    elab.elab_module_source("x86_64_structured_block", model).unwrap_or_else(|e| panic!("{}", e.render(model)));
    let source = include_str!("../../../examples/x86-native/branches.hthr");
    elab.elab_module_source("branches", source).unwrap_or_else(|e| panic!("{}", e.render(source)));
    let scratch = [Gpr::Rax, Gpr::Rcx, Gpr::Rdx, Gpr::R8];
    let sourced = generate_elaborated_structured_x86(&elab, "unsigned_threshold", "branches::unsigned_threshold", [Gpr::Rdi, Gpr::Rsi], &scratch, Gpr::Rax)
        .unwrap_or_else(|e| panic!("unsigned_threshold: {e:?}"));
    // 16 <s a ? b - a : a ^ b, over a and b in RDI and RSI.
    let word = |id| Port { id, width: 64 };
    let arm = |node| StructuredRegion::Dataflow(Region { inputs: vec![word(0), word(1)], nodes: vec![node], outputs: vec![word(4)] });
    let region = StructuredRegion::Sequence {
        prefix: Region { inputs: vec![word(0), word(1)], nodes: vec![Node::Const { width: 64, output: 2, value: 16 },
            Node::SignedLessThan { width: 64, output: 3, left: 2, right: 0 }], outputs: vec![Port { id: 3, width: 1 }] },
        continuation: Box::new(StructuredRegion::Conditional { inputs: vec![Port { id: 3, width: 1 }, word(0), word(1)], condition: 3,
            arguments: vec![word(0), word(1)], outputs: vec![word(4)],
            when_true: Box::new(arm(Node::Sub { width: 64, output: 4, left: 1, right: 0 })),
            when_false: Box::new(arm(Node::BitXor { width: 64, output: 4, left: 0, right: 1 })) }),
    };
    let built = generate_structured("signed_threshold", &region, &Placements::from([(0, Gpr::Rdi), (1, Gpr::Rsi)]), &scratch, Gpr::Rax)
        .unwrap_or_else(|e| panic!("signed_threshold: {e:?}"));
    let emissions: [(&str, &str, &str, StructuredX86Emission); 2] = [("unsigned_threshold", "B", "L", sourced), ("signed_threshold", "L", "B", built)];
    for (name, cc, other, emission) in emissions {
        let StructuredPlan::FusedSequence { continuation, .. } = &emission.lowered.body else { panic!("{name}: expected a fused sequence") };
        let StructuredPlan::Conditional { test: PlannedTest::Compare { left, right, .. }, .. } = continuation.body else { panic!("{name}: expected a compared branch") };
        let text = format!("import x86_64_structured_block; import function_ir; import function_ir_x86_support; import x86_64; import x86_64_block; import bitvec; import bool; import list; import logic; import nat;\n{}", emission.text);
        let (l, r) = (left.heather_name(), right.heather_name());
        let code = format!("CodeBranch(Compare({l}, {r}, {cc})");
        assert!(text.contains(&code), "{name}: the code should branch on Compare({l}, {r}, {cc})");
        elab.semantic_image().elaborator().elab_module_source(&format!("{name}_certificate"), &text).unwrap_or_else(|e| panic!("{}", e.render(&text)));
        for (mutation, replacement) in [("wrong_condition", format!("CodeBranch(Compare({l}, {r}, {other})")),
            ("swapped_operands", format!("CodeBranch(Compare({r}, {l}, {cc})"))] {
            let mutant = text.replacen(&code, &replacement, 1);
            let error = elab.semantic_image().elaborator().elab_module_source(&format!("{name}_{mutation}"), &mutant)
                .expect_err("a branch testing something else must be refused");
            let message = error.render(&mutant);
            assert!(!message.contains("unknown") && !message.contains("not in scope") && !message.contains("unbound"), "{name} {mutation} failed on a name: {message}");
        }
    }
}

// The false arm takes away the constant the fused comparison loaded, from
// the comparison's register (docs/structured-lowering-code-size-design.md
// §7.1, V5): the certificate checks, loads the constant once, and an arm
// claiming to take away another value is refused.
#[test]
fn a_carried_constant_certifies_and_another_value_is_refused() {
    use heather_elab::function_ir_source::generate_elaborated_structured_x86;
    use heather_elab::function_ir_x86_lower::Gpr;
    let mut elab = common::base_image(common::MODULES.len());
    let model = include_str!("../../../lib/std/arch/x86_64/x86_64_structured_block.hthr");
    elab.elab_module_source("x86_64_structured_block", model).unwrap_or_else(|e| panic!("{}", e.render(model)));
    let source = include_str!("../../../examples/x86-native/branches.hthr");
    elab.elab_module_source("branches", source).unwrap_or_else(|e| panic!("{}", e.render(source)));
    let scratch = [Gpr::Rax, Gpr::Rcx, Gpr::Rdx, Gpr::R8];
    let emission = generate_elaborated_structured_x86(&elab, "take_threshold", "branches::take_threshold", [Gpr::Rdi, Gpr::Rsi], &scratch, Gpr::Rax)
        .unwrap_or_else(|e| panic!("take_threshold: {e:?}"));
    let text = format!("import x86_64_structured_block; import function_ir; import function_ir_x86_support; import x86_64; import x86_64_block; import bitvec; import bool; import list; import logic; import nat;\n{}", emission.text);
    // Each block's instruction list spells a load on a line of its own.
    let loads = text.lines().filter(|line| line.trim_start().starts_with("MovRI(") && line.ends_with("ofNat(64, 4294967296)),")).count();
    assert_eq!(loads, 1, "the threshold is loaded once");
    elab.semantic_image().elaborator().elab_module_source("take_threshold_certificate", &text).unwrap_or_else(|e| panic!("{}", e.render(&text)));
    let claim = "@bitvec::BitVec::sub(width, values(width, 0), take_threshold_prefix_value(values, width))";
    assert!(text.contains(claim), "the false arm should take away the carried constant");
    let mutant = text.replacen(claim, "@bitvec::BitVec::sub(width, values(width, 0), values(width, 1))", 1);
    let error = elab.semantic_image().elaborator().elab_module_source("take_threshold_another_value", &mutant)
        .expect_err("an arm taking away another value must be refused");
    let message = error.render(&mutant);
    assert!(!message.contains("unknown") && !message.contains("not in scope") && !message.contains("unbound"), "failed on a name: {message}");
}

// A helper's result lands where its caller wants it, and the caller consumes
// it in place (docs/structured-lowering-code-size-design.md §3): `x + x`
// then `+ y` is two instructions into RAX. An input the caller says it reads
// no more may be overwritten too, and the certificate then no longer
// protects it: a caller keeping RDI is refused exactly when RDI was
// consumed.
#[test]
fn a_consumed_input_is_no_longer_protected() {
    use heather_elab::function_ir_cert::{Node, Port, Region, StructuredRegion};
    use heather_elab::function_ir_x86_lower::{generate_structured_consuming, Gpr, Instruction, Placements, StructuredPlan};
    use std::collections::BTreeSet;
    let mut elab = common::base_image(common::MODULES.len());
    let model = include_str!("../../../lib/std/arch/x86_64/x86_64_structured_block.hthr");
    elab.elab_module_source("x86_64_structured_block", model).unwrap_or_else(|e| panic!("{}", e.render(model)));
    let word = |id| Port { id, width: 64 };
    let region = StructuredRegion::Compose {
        prefix: Box::new(StructuredRegion::Dataflow(Region { inputs: vec![word(0), word(1)], nodes: vec![Node::Add { width: 64, output: 2, left: 0, right: 0 }], outputs: vec![word(2)] })),
        continuation: Box::new(StructuredRegion::Dataflow(Region { inputs: vec![word(1), word(2)], nodes: vec![Node::Add { width: 64, output: 3, left: 2, right: 1 }], outputs: vec![word(3)] })),
    };
    let inputs = Placements::from([(0, Gpr::Rdi), (1, Gpr::Rsi)]);
    let outputs = Placements::from([(3, Gpr::Rax)]);
    for consumable in [BTreeSet::new(), BTreeSet::from([Gpr::Rdi])] {
        let name = if consumable.is_empty() { "kept" } else { "consumed" };
        let emission = generate_structured_consuming(name, &region, &Default::default(), &Default::default(), &inputs, &[Gpr::Rax, Gpr::Rcx, Gpr::R8], &consumable, &outputs)
            .unwrap_or_else(|e| panic!("{name}: {e:?}"));
        let StructuredPlan::Compose { prefix, continuation } = &emission.lowered.body else { panic!("{name}: expected a composition") };
        assert_eq!(prefix.outputs[0].1, Gpr::Rax, "{name}: the helper's result goes where the caller's does");
        let StructuredPlan::Dataflow(dag) = &continuation.body else { panic!("{name}: expected a dataflow continuation") };
        assert_eq!(dag.instructions, vec![Instruction::AddRR { destination: Gpr::Rax, source: Gpr::Rsi }], "{name}: the caller adds in place");
        assert_eq!(emission.lowered.clobbered.contains(&Gpr::Rdi), !consumable.is_empty(), "{name}");
        assert!(!emission.lowered.clobbered.contains(&Gpr::Rsi), "{name}: y is read after the helper");
        let text = format!("import x86_64_structured_block; import function_ir; import function_ir_x86_support; import x86_64; import x86_64_block; import bitvec; import bool; import list; import logic; import nat;\n{}\n\
            theorem {name}_keeps_rdi<M>(values: Valuation(), before: MachineState<M>,\n\
                placed_0: values(64, 0) = read_gpr(Rdi, before.gprs), placed_1: values(64, 1) = read_gpr(Rsi, before.gprs)):\n\
                read_gpr(Rdi, {name}_artifact(values, before, placed_0, placed_1).after.gprs) = read_gpr(Rdi, before.gprs)\n\
            {{ {name}_artifact(values, before, placed_0, placed_1).registers_preserved(Rdi, trivial) }}\n", emission.text);
        let checked = elab.semantic_image().elaborator().elab_module_source(&format!("{name}_certificate"), &text);
        if consumable.is_empty() {
            checked.unwrap_or_else(|e| panic!("{}", e.render(&text)));
        } else {
            let message = checked.expect_err("a caller keeping a consumed input must be refused").render(&text);
            assert!(message.contains("but `False` is expected"), "refused for another reason: {message}");
            let body = &text[..text.find("theorem consumed_keeps_rdi").unwrap()];
            elab.semantic_image().elaborator().elab_module_source("consumed_body", body).unwrap_or_else(|e| panic!("{}", e.render(body)));
        }
    }
}

// The outer step's passthrough arm is empty, and its certificate checks; a
// region whose Move copies another value there is refused.
#[test]
fn an_empty_passthrough_arm_certifies_and_another_copy_is_refused() {
    use heather_elab::function_ir_source::generate_elaborated_structured_x86;
    use heather_elab::function_ir_x86_lower::Gpr;
    let mut elab = common::base_image(common::MODULES.len());
    let model = include_str!("../../../lib/std/arch/x86_64/x86_64_structured_block.hthr");
    elab.elab_module_source("x86_64_structured_block", model).unwrap_or_else(|e| panic!("{}", e.render(model)));
    let source = include_str!("../../../examples/x86-native/branches.hthr");
    elab.elab_module_source("branches", source).unwrap_or_else(|e| panic!("{}", e.render(source)));
    let scratch = [Gpr::Rax, Gpr::Rcx, Gpr::Rdx, Gpr::R8];
    let emission = generate_elaborated_structured_x86(&elab, "keep_twice", "branches::keep_twice", [Gpr::Rdi, Gpr::Rsi], &scratch, Gpr::Rax)
        .unwrap_or_else(|e| panic!("keep_twice: {e:?}"));
    let text = format!("import x86_64_structured_block; import function_ir; import function_ir_x86_support; import x86_64; import x86_64_block; import bitvec; import bool; import list; import logic; import nat;\n{}", emission.text);
    assert!(text.contains("CodeBlock([])") || text.contains("_leaf_instructions() → List<Instruction>\n{\n    []"), "an arm should be an empty block");
    elab.semantic_image().elaborator().elab_module_source("keep_twice_certificate", &text).unwrap_or_else(|e| panic!("{}", e.render(&text)));
    let moves = text.match_indices("Move(width := 64, output := ").map(|(at, _)| at).collect::<Vec<_>>();
    assert!(!moves.is_empty(), "the passthrough should be a Move");
    let at = moves[moves.len() - 1];
    let end = at + text[at..].find(')').unwrap();
    let node = &text[at..=end];
    let source = node.rsplit("source := ").next().unwrap().trim_end_matches(')');
    let mutant = format!("{}{}{}", &text[..at], node.replace(&format!("source := {source})"), "source := 1)"), &text[end + 1..]);
    assert_ne!(source, "1", "the mutant must copy another value");
    let error = elab.semantic_image().elaborator().elab_module_source("keep_twice_another_copy", &mutant)
        .expect_err("a Move of another value must be refused");
    let message = error.render(&mutant);
    assert!(!message.contains("unknown") && !message.contains("not in scope") && !message.contains("unbound"), "failed on a name: {message}");
}

// An ADD of a constant an immediate extends to certifies, and the kernel
// holds the processor to its sign extension: a certificate claiming the
// imm32 0x80000000 adds +2^31 (it adds -2^31) is refused, with every other
// spelling of the constant changed alike.
#[test]
fn an_immediate_add_certifies_at_its_sign_extension() {
    use heather_elab::function_ir_cert::{Node, Port, Region, StructuredRegion};
    use heather_elab::function_ir_x86_lower::{generate_structured, Gpr, Instruction, Placements, StructuredPlan};
    let mut elab = common::base_image(common::MODULES.len());
    let model = include_str!("../../../lib/std/arch/x86_64/x86_64_structured_block.hthr");
    elab.elab_module_source("x86_64_structured_block", model).unwrap_or_else(|e| panic!("{}", e.render(model)));
    let word = |id| Port { id, width: 64 };
    let negative = 0xffff_ffff_8000_0000u64;
    for (name, value, form) in [("minus_one", u64::MAX, Instruction::AddRI8 { destination: Gpr::Rax, immediate: 0xff }),
        ("minus_two_pow_31", negative, Instruction::AddRI32 { destination: Gpr::Rax, immediate: 0x8000_0000 })] {
        let region = StructuredRegion::Dataflow(Region { inputs: vec![word(0)], nodes: vec![Node::Const { width: 64, output: 1, value },
            Node::Add { width: 64, output: 2, left: 0, right: 1 }], outputs: vec![word(2)] });
        let emission = generate_structured(name, &region, &Placements::from([(0, Gpr::Rdi)]), &[Gpr::Rax, Gpr::Rcx], Gpr::Rax)
            .unwrap_or_else(|e| panic!("{name}: {e:?}"));
        let StructuredPlan::Dataflow(dag) = &emission.lowered.body else { panic!("{name}: expected a dataflow") };
        assert_eq!(dag.instructions, vec![Instruction::MovRR { destination: Gpr::Rax, source: Gpr::Rdi }, form], "{name}");
        let text = format!("import x86_64_structured_block; import function_ir; import function_ir_x86_support; import x86_64; import x86_64_block; import bitvec; import bool; import list; import logic; import nat;\n{}", emission.text);
        elab.semantic_image().elaborator().elab_module_source(&format!("{name}_certificate"), &text).unwrap_or_else(|e| panic!("{}", e.render(&text)));
        if value == negative {
            let mutant = text.replace(&value.to_string(), &(1u64 << 31).to_string());
            assert!(mutant.contains("AddRI32(Rax, @bitvec::BitVec::ofNat(32, 2147483648))"), "the instruction keeps its imm32");
            let error = elab.semantic_image().elaborator().elab_module_source("positive_two_pow_31", &mutant)
                .expect_err("an imm32 read as unsigned must be refused");
            let message = error.render(&mutant);
            assert!(message.contains("step_1_result") && message.contains("NotConvertible"), "refused elsewhere: {message}");
        }
    }
}
