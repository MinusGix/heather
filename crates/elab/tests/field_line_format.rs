use crate::read_loop_fixture::checker;
use heather_elab::function_ir_source::generate_elaborated_typed_x86;
use heather_elab::function_ir_x86_lower::{Gpr, Placements};

const BV_OMEGA: &str = include_str!("../../../lib/std/bitvec/omega.hthr");
const DECIMAL: &str = include_str!("../../../lib/decimal_line.hthr");
const FIELD: &str = include_str!("../../../lib/field_line.hthr");

fn base() -> heather_elab::Elaborator {
    let mut elab = checker();
    elab.elab_module_source("bitvec_omega", BV_OMEGA).unwrap_or_else(|e| panic!("{}", e.render(BV_OMEGA)));
    elab.elab_module_source("decimal_line", DECIMAL).unwrap_or_else(|e| panic!("{}", e.render(DECIMAL)));
    elab
}

// The field formatter's two words at the registers the three-field tail
// gives them (docs/native-wc-design.md §5): the count in R11, the high
// word's tail in R10, each word to RAX; R13–R15, which hold the counts still
// to print, are never touched.
fn parts() -> [(&'static str, Placements, Vec<Gpr>, Placements); 2] {
    use Gpr::*;
    [
        ("field_low", Placements::from([(0, R11)]), vec![Rax, Rcx, Rdx, Rbx, R8, R9, R10, R12, Rsi, Rdi, Rbp], Placements::from([(1, Rax)])),
        ("field_high", Placements::from([(0, R11), (1, R10)]), vec![Rax, Rcx, Rdx, Rbx, R8, R9, R12, Rsi, Rdi, Rbp], Placements::from([(2, Rax)])),
    ]
}

// The library's meaning lemmas check, and both words compile to code whose
// certificates check against the source functions. Each certificate is
// refused by a library whose function differs in one threshold.
#[test]
fn field_words_certify() {
    let mut elab = base();
    elab.elab_module_source("field_line", FIELD).unwrap_or_else(|e| panic!("{}", e.render(FIELD)));
    elab.elab_module_source("field_context", "import field_line; import decimal_line; import bitvec; import bool;").unwrap();
    let mut emissions = Vec::new();
    for (function, inputs, temporaries, outputs) in parts() {
        let emission = generate_elaborated_typed_x86(&elab, function, &format!("field_line::{function}"), &inputs, &temporaries, &outputs)
            .unwrap_or_else(|e| panic!("{function}: {e:?}"));
        elab.semantic_image().elaborator().elab_module_source(&format!("{function}_format"), &emission.text)
            .unwrap_or_else(|e| panic!("{}", e.render(&emission.text)));
        emissions.push((function, emission.text));
    }
    let bad = FIELD.replace("BitVec::ofNat(4294967296000), ", "BitVec::ofNat(4294967296001), ");
    assert_ne!(bad, FIELD);
    let mut other = base();
    other.elab_module_source("field_line", &cut_meaning(&bad)).unwrap_or_else(|e| panic!("{}", e.render(&bad)));
    let other = other.semantic_image();
    for (function, text) in emissions {
        let error = other.elaborator().elab_module_source(&format!("{function}_format"), &text).expect_err(function).render(&text);
        assert!(!error.contains("unbound") && !error.contains("ambiguous"), "{function}: {error}");
    }
}

// The functions without the lemmas about them, which a changed function
// would refuse first.
fn cut_meaning(text: &str) -> String {
    let at = text.find("// ---------------------------------------------------------------------------\n// What a field means.").expect("section");
    text[..at].to_string()
}

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
