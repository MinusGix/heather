use crate::common;

use heather_elab::function_ir_x86_lower::{Gpr, Placements};


fn checker() -> heather_elab::Elaborator {
    let mut elab = common::base_image(common::MODULES.len());
    let model = include_str!("../../../lib/std/arch/x86_64/structured_block.hthr");
    elab.elab_module_source("x86_64_structured_block", model).unwrap_or_else(|e| panic!("{}", e.render(model)));
    elab
}

#[test]
fn typed_search_publication_checks() {
    use heather_elab::function_ir_source::generate_elaborated_typed_x86;
    let mut elab = checker();
    let model = include_str!("../../../lib/function_ir_loop.hthr");
    elab.elab_module_source("function_ir_loop", model).unwrap_or_else(|e| panic!("{}", e.render(model)));
    let source = include_str!("../../../examples/function-ir/readonly-loops.hthr");
    elab.elab_module_source("readonly_loops", source).unwrap_or_else(|e| panic!("{}", e.render(source)));
    let emission = generate_elaborated_typed_x86(&elab, "search", "readonly_loops::search_body",
        &Placements::from([(0, Gpr::Rdi), (2, Gpr::Rsi), (3, Gpr::R8)]),
        &[Gpr::Rax, Gpr::Rdx, Gpr::Rcx, Gpr::R9, Gpr::R10],
        &Placements::from([(4, Gpr::Rax), (5, Gpr::Rdx)])).unwrap();
    let text = emission.text;
    elab.elab_module_source("typed_search", &text).unwrap_or_else(|e| panic!("{}", e.render(&text)));

}

const COMPOSED: &str = r#"
import bitvec; import bool;
fn below(a, b: BitVec(64)) → Bool { @bitvec::BitVec::unsigned_lt_bit(64, a, b) }
fn step(state, limit: BitVec(64)) → BitVec(64) {
    match below(state, limit) { False => @bitvec::BitVec::sub(64, state, limit), True => state }
}
fn chain(x: BitVec(64)) → BitVec(64) { step(step(step(x, @bitvec::BitVec::ofNat(64, 40)), @bitvec::BitVec::ofNat(64, 20)), @bitvec::BitVec::ofNat(64, 10)) }
"#;

// Word- and Bool-valued helpers compose, each crossing at its source call
// (cert::SourceValue). A certificate generated against one helper body is
// refused under another: the body meets the machine code at a `_link`, or in
// the expansion when the call is the function's own result.
#[test]
fn composed_helpers_cross_at_the_call() {
    use heather_elab::function_ir_source::generate_elaborated_typed_x86;
    let mut elab = checker();
    elab.elab_module_source("composed", COMPOSED).unwrap_or_else(|e| panic!("{}", e.render(COMPOSED)));
    let emission = generate_elaborated_typed_x86(&elab, "chain", "composed::chain",
        &Placements::from([(0, Gpr::Rdi)]), &[Gpr::Rax, Gpr::Rdx, Gpr::Rcx, Gpr::R9, Gpr::R10], &Placements::from([(1, Gpr::Rax)])).unwrap();
    let text = emission.text;
    assert!(text.contains("_link(") && text.contains("_source(values)"), "compositions must cross at the call");
    elab.semantic_image().elaborator().elab_module_source("typed_chain", &text).unwrap_or_else(|e| panic!("{}", e.render(&text)));
    let changed = COMPOSED.replace("@bitvec::BitVec::sub(64, state, limit)", "@bitvec::BitVec::sub(64, limit, state)");
    assert_ne!(changed, COMPOSED);
    let mut stale = checker();
    stale.elab_module_source("composed", &changed).unwrap_or_else(|e| panic!("{}", e.render(&changed)));
    let error = stale.semantic_image().elaborator().elab_module_source("typed_chain", &text).expect_err("a stale helper body must be refused").render(&text);
    assert!(error.contains("kernel rejected") && !error.contains("unbound"), "{error}");
}


// A step over a record state (docs/native-wc-design.md §4.1): each field of
// the record parameter is a port, and each field of the record payload a
// result, beside the choice's discriminator. `wc`'s step: whitespace ends a
// word (and a newline counts a line); anything else starts one unless inside.
const RECORD_STEP: &str = r#"
import bitvec; import bool; import function_ir_loop;
record WcState { lines: Nat, words: Nat, inside: Bool }
fn newline_byte(b: BitVec(8)) → Bool {
    match b.unsigned_lt_bit(BitVec::ofNat(10)) { True => False, False => b.unsigned_lt_bit(BitVec::ofNat(11)) }
}
fn space_byte(b: BitVec(8)) → Bool {
    match b.unsigned_lt_bit(BitVec::ofNat(14)) {
        True => match b.unsigned_lt_bit(BitVec::ofNat(9)) { True => False, False => True },
        False => match b.unsigned_lt_bit(BitVec::ofNat(32)) { True => False, False => b.unsigned_lt_bit(BitVec::ofNat(33)) },
    }
}
fn wc_body(needle: BitVec(8), cursor: Nat, byte: BitVec(8), s: WcState) → LoopStep<WcState> {
    match space_byte(byte) {
        True => match newline_byte(byte) {
            True => Continue(WcState(Succ(s.lines), s.words, False)),
            False => Continue(WcState(s.lines, s.words, False)),
        },
        False => match s.inside {
            True => Continue(s),
            False => Continue(WcState(s.lines, Succ(s.words), True)),
        },
    }
}
"#;

#[test]
fn record_state_step_publication_checks() {
    use heather_elab::function_ir_source::generate_elaborated_typed_x86;
    let mut elab = checker();
    let model = include_str!("../../../lib/function_ir_loop.hthr");
    elab.elab_module_source("function_ir_loop", model).unwrap_or_else(|e| panic!("{}", e.render(model)));
    let nat = include_str!("../../../lib/std/bitvec/nat.hthr");
    elab.elab_module_source("bitvec_nat", nat).unwrap_or_else(|e| panic!("{}", e.render(nat)));
    elab.elab_module_source("record_step", RECORD_STEP).unwrap_or_else(|e| panic!("{}", e.render(RECORD_STEP)));
    let emission = generate_elaborated_typed_x86(&elab, "wc_step", "record_step::wc_body",
        &Placements::from([(0, Gpr::Rdi), (2, Gpr::Rsi), (3, Gpr::R8), (4, Gpr::R9), (5, Gpr::R10)]),
        &[Gpr::Rax, Gpr::Rdx, Gpr::Rcx, Gpr::Rbx, Gpr::R11, Gpr::R12],
        &Placements::from([(6, Gpr::R11), (7, Gpr::R12), (8, Gpr::Rbx), (9, Gpr::Rdx)])).unwrap_or_else(|e| panic!("{e:?}"));
    let text = emission.text;
    elab.elab_module_source("typed_wc_step", &text).unwrap_or_else(|e| panic!("{}", e.render(&text)));
    for field in ["wc_step_typed_artifact", "wc_step_output_7_typed_artifact", "wc_step_output_8_typed_artifact", "wc_step_output_9_typed_artifact"] {
        assert!(text.contains(&format!("theorem {field}<M>(")), "missing {field}");
    }
    // Its arms are past rel8's reach, so this is also the near conditional's test.
    assert!(text.contains("CodeBranchNear("), "expected a near conditional");
}

// The record step's certificate names its source: against a source whose one
// leaf drops the word count's `Succ`, or swaps two fields, it is refused where
// the expansion meets the source, not by a missing name.
#[test]
fn record_state_step_certificate_refuses_other_sources() {
    use heather_elab::function_ir_source::generate_elaborated_typed_x86;
    let build = |source: &str| {
        let mut elab = checker();
        let model = include_str!("../../../lib/function_ir_loop.hthr");
        elab.elab_module_source("function_ir_loop", model).unwrap_or_else(|e| panic!("{}", e.render(model)));
        let nat = include_str!("../../../lib/std/bitvec/nat.hthr");
        elab.elab_module_source("bitvec_nat", nat).unwrap_or_else(|e| panic!("{}", e.render(nat)));
        elab.elab_module_source("record_step", source).unwrap_or_else(|e| panic!("{}", e.render(source)));
        elab
    };
    let emission = generate_elaborated_typed_x86(&build(RECORD_STEP), "wc_step", "record_step::wc_body",
        &Placements::from([(0, Gpr::Rdi), (2, Gpr::Rsi), (3, Gpr::R8), (4, Gpr::R9), (5, Gpr::R10)]),
        &[Gpr::Rax, Gpr::Rdx, Gpr::Rcx, Gpr::Rbx, Gpr::R11, Gpr::R12],
        &Placements::from([(6, Gpr::R11), (7, Gpr::R12), (8, Gpr::Rbx), (9, Gpr::Rdx)])).unwrap_or_else(|e| panic!("{e:?}"));
    for (name, from, to) in [
        ("word_not_counted", "False => Continue(WcState(s.lines, Succ(s.words), True)),", "False => Continue(WcState(s.lines, s.words, True)),"),
        ("fields_swapped", "False => Continue(WcState(s.lines, s.words, False)),", "False => Continue(WcState(s.words, s.lines, False)),"),
    ] {
        let bad = RECORD_STEP.replacen(from, to, 1);
        assert_ne!(bad, RECORD_STEP, "{name}");
        let error = build(&bad).elab_module_source("typed_wc_step", &emission.text).expect_err(name).render(&emission.text);
        assert!(!error.contains("unbound") && !error.contains("ambiguous"), "{name}: {error}");
    }
}

// The same step one field at a time (docs/native-wc-design.md §4.6): each
// output's certificate reads only what that output depends on, so a field
// computed after another was written back needs nothing from the register
// that other one overwrote.
#[test]
fn record_state_fields_publish_alone() {
    use heather_elab::function_ir_source::{generate_elaborated_typed_fields_x86, FieldPiece};
    let mut elab = checker();
    let model = include_str!("../../../lib/function_ir_loop.hthr");
    elab.elab_module_source("function_ir_loop", model).unwrap_or_else(|e| panic!("{}", e.render(model)));
    let nat = include_str!("../../../lib/std/bitvec/nat.hthr");
    elab.elab_module_source("bitvec_nat", nat).unwrap_or_else(|e| panic!("{}", e.render(nat)));
    elab.elab_module_source("record_step", RECORD_STEP).unwrap_or_else(|e| panic!("{}", e.render(RECORD_STEP)));
    let inputs = Placements::from([(0, Gpr::Rdi), (2, Gpr::Rsi), (3, Gpr::R8), (4, Gpr::R9), (5, Gpr::R10)]);
    let temps = [Gpr::Rax, Gpr::Rdx, Gpr::Rcx, Gpr::Rbx];
    let pieces: Vec<_> = [(6, "lines"), (7, "words"), (8, "inside"), (9, "step")].into_iter().map(|(port, field)| FieldPiece {
        prefix: format!("wc_{field}"), port, inputs: &inputs, temporaries: &temps, output: Gpr::Rax }).collect();
    let (text, emissions) = generate_elaborated_typed_fields_x86(&elab, "wc_fields", "record_step::wc_body", &pieces).unwrap_or_else(|e| panic!("{e:?}"));
    elab.elab_module_source("typed_wc_fields", &text).unwrap_or_else(|e| panic!("{}", e.render(&text)));
    let reads = |field: &str| emissions.iter().find(|e| e.prefix == format!("wc_{field}")).unwrap().inputs.iter().map(|p| p.id).collect::<Vec<_>>();
    // A branch whose arms compute a field alike is collapsed, so a field
    // reads only what it depends on: the lines don't read the flag, and
    // nothing reads the needle. The flag still reads itself here, since one
    // arm passes the state through and the other writes `True`: equal
    // values, not alike computations. The words read the flag, which is why
    // the flag is written back after them.
    assert_eq!(reads("lines"), vec![2, 3]);
    assert_eq!(reads("words"), vec![2, 4, 5]);
    assert_eq!(reads("inside"), vec![2, 5]);
    assert!(reads("step").is_empty(), "a folding step's discriminator is a constant");
}
