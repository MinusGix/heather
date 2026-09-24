use crate::common;

use heather_elab::function_ir_x86_lower::{Gpr, Placements};


fn checker() -> heather_elab::Elaborator {
    let mut elab = common::base_image(common::MODULES.len());
    let model = include_str!("../../../lib/std/arch/x86_64/structured_block.hthr");
    elab.elab_module_source("x86_64_structured_block", model).unwrap_or_else(|e| panic!("{}", e.render(model)));
    elab
}

#[test]
fn scalar_and_choice_publication_checks() {
    use heather_elab::function_ir_source::generate_elaborated_typed_x86;
    let mut elab = checker();
    let source = r#"import bitvec; import bool;
inductive Outcome<A> { First(value: A), Second(value: A) }
fn byte_copy(x: BitVec(8)) → BitVec(8) { x }
fn bit_copy(x: BitVec(1)) → BitVec(1) { x }
fn word_copy(x: BitVec(64)) → BitVec(64) { x }
fn empty() → BitVec(0) { @bitvec::BitVec::ofNat(0, 0) }
fn choose(flag: Bool, x: BitVec(8)) → Outcome<BitVec(8)> {
    match flag { False => First<BitVec(8)>(x), True => Second<BitVec(8)>(@bitvec::BitVec::ofNat(8, 7)) }
}
"#;
    elab.elab_module_source("typed_examples", source).unwrap_or_else(|e| panic!("{}", e.render(source)));
    for name in ["byte_copy", "bit_copy", "word_copy", "empty", "choose"] {
        let inputs = if name == "empty" { Placements::new() } else if name == "choose" { Placements::from([(0, Gpr::Rdi), (1, Gpr::Rsi)]) } else { Placements::from([(0, Gpr::Rdi)]) };
        let outputs = if name == "choose" { Placements::from([(2, Gpr::Rax), (3, Gpr::Rdx)]) } else { Placements::from([(inputs.len() as u64, Gpr::Rax)]) };
        let emission = generate_elaborated_typed_x86(&elab, name, &format!("typed_examples::{name}"), &inputs, &[Gpr::Rax, Gpr::Rdx, Gpr::Rcx], &outputs).unwrap_or_else(|e| panic!("{name}: {e}"));
        elab.elab_module_source(&format!("{name}_publication"), &emission.text).unwrap_or_else(|e| panic!("{}", e.render(&emission.text)));
    }

    let imports = "import choose_publication; import typed_examples; import x86_64_structured_block; import x86_64; import bitvec; import bool; import logic;";
    let parameters = "flag: Bool, x: BitVec(8), before: MachineState<M>, flag_placed: @bitvec::BitVec::zero_extend(1, 63, bitvec::BitVec::ofBool(flag)) = read_gpr(Rdi, before.gprs), x_placed: @bitvec::BitVec::zero_extend(8, 56, x) = read_gpr(Rsi, before.gprs)";
    let arguments = "flag, x, before, flag_placed, x_placed";
    let consume = format!("{imports} theorem consume<M>({parameters}): StructuredArtifact<M>(choose_code(), before, Rdx, @bitvec::BitVec::zero_extend(1, 63, bitvec::BitVec::ofBool(match typed_examples::choose(flag, x) {{ First(_) => False, Second(_) => True }})), choose_Protected) {{ choose_output_3_typed_artifact({arguments}) }}");
    elab.elab_module_source("typed_consumer", &consume).unwrap_or_else(|e| panic!("{}", e.render(&consume)));
    for (name, expected, premises) in [
        ("wrong_result_register", "read_gpr(Rdx, choose_after(before).gprs) = @bitvec::BitVec::zero_extend(8, 56, choose_observe_2(typed_examples::choose(flag, x)))", parameters.to_string()),
        ("wrong_input_placement", "read_gpr(Rax, choose_after(before).gprs) = @bitvec::BitVec::zero_extend(8, 56, choose_observe_2(typed_examples::choose(flag, x)))", parameters.replace("read_gpr(Rsi, before.gprs)", "read_gpr(Rdi, before.gprs)")),
    ] {
        let negative = format!("{imports} theorem {name}<M>({premises}): {expected} {{ choose_typed_correct({arguments}) }}");
        heather_syntax::parse_file(&negative).unwrap();
        let error = elab.elab_module_source(name, &negative).expect_err("incorrect typed boundary must be rejected");
        let message = error.render(&negative);
        assert!(!message.contains("unknown") && !message.contains("not in scope"), "{message}");
    }
    let swapped = consume.replace("First(_) => False, Second(_) => True", "First(_) => True, Second(_) => False");
    let error = elab.elab_module_source("wrong_constructor_encoding", &swapped).expect_err("reversed constructor encoding must be rejected");
    assert!(!error.render(&swapped).contains("unknown"));
}
