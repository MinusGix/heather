use crate::read_loop_fixture::checker;
use heather_elab::function_ir_source::generate_elaborated_typed_x86;
use heather_elab::function_ir_x86_lower::{Gpr, Placements};

const BV_OMEGA: &str = include_str!("../../../lib/std/bitvec/bitvec_omega.hthr");
const DECIMAL: &str = include_str!("../../../lib/decimal_line.hthr");
pub(crate) const FIELD: &str = include_str!("../../../lib/field_line.hthr");

pub(crate) fn base() -> heather_elab::Elaborator {
    let mut elab = checker();
    elab.elab_module_source("bitvec_omega", BV_OMEGA).unwrap_or_else(|e| panic!("{}", e.render(BV_OMEGA)));
    elab.elab_module_source("decimal_line", DECIMAL).unwrap_or_else(|e| panic!("{}", e.render(DECIMAL)));
    elab
}

// One of the field formatter's words at the registers the three-field tail
// gives it (docs/native-wc-design.md §5): the count in R11, the high word's
// tail in R10, the word to RAX; R11 and R13–R15, which hold the counts still
// to print, are never touched. Its certificate checks against the source
// function and is what the tail asks of it (field_line's FieldLowCert or
// FieldHighCert, and the registers elf64_read_fields' FieldsFormat needs
// kept); it is refused by a library whose function differs in one threshold.
// Each word runs in a process of its own: together they pass the CPU rail.
pub(crate) fn word_certifies(function: &str) {
    use Gpr::*;
    let (inputs, temporaries, cert, keeps, kept, lambda) = match function {
        "field_low" => (Placements::from([(0, R11)]), vec![Rax, Rcx, Rdx, Rbx, R8, R9, R10, R12, Rsi, Rdi, Rbp], "FieldLowCert",
            "field_low_Protected(R11) ∧ (field_low_Protected(R13) ∧ (field_low_Protected(R14) ∧ field_low_Protected(R15)))",
            "⟨trivial, ⟨trivial, ⟨trivial, trivial⟩⟩⟩",
            "λ before n placed => field_low_typed_artifact(n, before, placed)"),
        _ => (Placements::from([(0, R11), (1, R10)]), vec![Rax, Rcx, Rdx, Rbx, R8, R9, R12, Rsi, Rdi, Rbp], "FieldHighCert",
            "field_high_Protected(R13) ∧ (field_high_Protected(R14) ∧ field_high_Protected(R15))",
            "⟨trivial, ⟨trivial, trivial⟩⟩",
            "λ before n tail at_n at_tail => field_high_typed_artifact(n, tail, before, at_n, at_tail)"),
    };
    let outputs = Placements::from([(inputs.len() as u64, Rax)]);
    let mut elab = base();
    elab.elab_module_source("field_line", FIELD).unwrap_or_else(|e| panic!("{}", e.render(FIELD)));
    elab.elab_module_source("field_context", "import field_line; import decimal_line; import bitvec; import bool;").unwrap();
    let emission = generate_elaborated_typed_x86(&elab, function, &format!("field_line::{function}"), &inputs, &temporaries, &outputs)
        .unwrap_or_else(|e| panic!("{function}: {e:?}"));
    let module = format!("{function}_format");
    elab.elab_module_source(&module, &emission.text).unwrap_or_else(|e| panic!("{}", e.render(&emission.text)));
    let fits = format!("import field_line; import {module}; import x86_64_structured_block; import x86_64; import logic;
theorem {function}_fits<M>(): {cert}<M>({function}_code(), {function}_Protected) {{ {lambda} }}
theorem {function}_keeps(): {keeps} {{ {kept} }}");
    elab.elab_module_source(&format!("{function}_fits"), &fits).unwrap_or_else(|e| panic!("{}", e.render(&fits)));
    let bad = FIELD.replace("BitVec::ofNat(4294967296000), ", "BitVec::ofNat(4294967296001), ");
    assert_ne!(bad, FIELD);
    let mut other = base();
    other.elab_module_source("field_line", &cut_meaning(&bad)).unwrap_or_else(|e| panic!("{}", e.render(&bad)));
    let error = other.elab_module_source(&module, &emission.text).expect_err(function).render(&emission.text);
    assert!(!error.contains("unbound") && !error.contains("ambiguous"), "{function}: {error}");
}

// The functions without the lemmas about them, which a changed function
// would refuse first.
fn cut_meaning(text: &str) -> String {
    let at = text.find("// The words' certificates at the registers").expect("section");
    text[..at].to_string()
}

#[test]
fn field_low_certifies() { word_certifies("field_low"); }

// The meaning lemmas refuse a formatter that marks the wrong column, places
// a digit's weight in the wrong byte, keeps a stale top digit in the high
// word, or starts a column at '0' instead of a space.
#[test]
fn slow_acceptance_field_line_refusals() {
    let library = base().semantic_image();
    for (name, from, to) in [
        ("mark_wrong_column", "BitVec::ofNat(4294967296 * 100000), BitVec::ofNat(4096))", "BitVec::ofNat(4294967296 * 100000), BitVec::ofNat(16))"),
        ("digit_wrong_byte", "BitVec::ofNat(4294967296 * 800), BitVec::ofNat(8))", "BitVec::ofNat(4294967296 * 800), BitVec::ofNat(2048))"),
        ("strip_weighs", "BitVec::ofNat(4294967296 * 8000), BitVec::ofNat(0))", "BitVec::ofNat(4294967296 * 8000), BitVec::ofNat(1))"),
        ("zero_not_space", "fn low_start(n: Nat) → BitVec(64) { raise32(bitvec_nat::word_of_nat(64, n)).add(BitVec::ofNat(538976288)) }",
            "fn low_start(n: Nat) → BitVec(64) { raise32(bitvec_nat::word_of_nat(64, n)).add(BitVec::ofNat(808464432)) }"),
    ] {
        let bad = FIELD.replacen(from, to, 1);
        assert_ne!(bad, FIELD, "{name}");
        let error = library.elaborator().elab_module_source("field_line", &bad).expect_err(name).render(&bad);
        assert!(!error.contains("unbound") && !error.contains("ambiguous"), "{name}: {error}");
    }
}
