// The step piece the generator certifies for a stream filter
// (docs/native-stream-filter-design.md §5): a step reflected with its
// `Filtered` result, or `counting(g)` / `mapping(f)`, lowered output by
// output, the emit first and then the state in place, and published as
// `filter_step_piece::StepPiece`, kernel-checked.
use std::sync::OnceLock;

use crate::read_loop_fixture::checker;
use heather_elab::function_ir_source::{generate_elaborated_filter_step_x86, reflect_filter_step, FilterStep, FilterStepEmission};
use heather_elab::{Elaborator, SemanticImage};

const READ_PIECES: &str = include_str!("../../../lib/elf64_read_pieces.hthr");
const STREAM_FILTER: &str = include_str!("../../../lib/stream_filter.hthr");
const STEP_PIECE: &str = include_str!("../../../lib/filter_step_piece.hthr");

// The steps: `tr -d '\n'` (no state), `tr -s '\n'` (the last byte and
// whether there was one), `wc` and `wc -l` as counting steps, and `tr a-z
// A-Z` as a mapping, each as its example program spells it.
const FILTERS: &str = r#"import stream_filter; import filter_step_piece; import bitvec; import bool; import nat; import option;
fn newline(b: BitVec(8)) → Bool {
    match b.unsigned_lt_bit(BitVec::ofNat(10)) { True => False, False => b.unsigned_lt_bit(BitVec::ofNat(11)) }
}
fn drop_step(s: Stateless, b: BitVec(8)) → Filtered<Stateless> {
    match newline(b) { True => Filtered(s, None), False => Filtered(s, Some(b)) }
}
// drop_step with its emit the other way round: a negative control's claim.
fn keep_step(s: Stateless, b: BitVec(8)) → Filtered<Stateless> {
    match newline(b) { True => Filtered(s, Some(b)), False => Filtered(s, None) }
}
record Last { byte: BitVec(8), some: Bool }
fn squeeze_step(s: Last, b: BitVec(8)) → Filtered<Last> {
    match newline(b) {
        False => Filtered(Last(b, True), Some(b)),
        True => match s.some {
            False => Filtered(Last(b, True), Some(b)),
            True => match newline(s.byte) { True => Filtered(s, None), False => Filtered(Last(b, True), Some(b)) },
        },
    }
}
// squeeze_step forgetting the byte it emitted: a negative control's claim.
fn stale_step(s: Last, b: BitVec(8)) → Filtered<Last> {
    match newline(b) {
        False => Filtered(Last(s.byte, True), Some(b)),
        True => match s.some {
            False => Filtered(Last(b, True), Some(b)),
            True => match newline(s.byte) { True => Filtered(s, None), False => Filtered(Last(b, True), Some(b)) },
        },
    }
}
record WcState { lines: Nat, words: Nat, bytes: Nat, inside: Bool }
fn newline_byte(b: BitVec(8)) → Bool {
    match b.unsigned_lt_bit(BitVec::ofNat(10)) { True => False, False => b.unsigned_lt_bit(BitVec::ofNat(11)) }
}
fn space_byte(b: BitVec(8)) → Bool {
    match b.unsigned_lt_bit(BitVec::ofNat(14)) {
        True => match b.unsigned_lt_bit(BitVec::ofNat(9)) { True => False, False => True },
        False => match b.unsigned_lt_bit(BitVec::ofNat(32)) { True => False, False => b.unsigned_lt_bit(BitVec::ofNat(33)) },
    }
}
fn wc_step(s: WcState, byte: BitVec(8)) → WcState {
    match space_byte(byte) {
        True => match newline_byte(byte) {
            True => WcState(Succ(s.lines), s.words, Succ(s.bytes), False),
            False => WcState(s.lines, s.words, Succ(s.bytes), False),
        },
        False => match s.inside {
            True => WcState(s.lines, s.words, Succ(s.bytes), True),
            False => WcState(s.lines, Succ(s.words), Succ(s.bytes), True),
        },
    }
}
fn wc_filter() → WcState → BitVec(8) → Filtered<WcState> { counting(wc_step) }
fn line_step(count: Nat, byte: BitVec(8)) → Nat {
    match newline(byte) { False => count, True => Succ(count) }
}
fn lines_filter() → Nat → BitVec(8) → Filtered<Nat> { counting(line_step) }
fn lower_byte(b: BitVec(8)) → Bool {
    match b.unsigned_lt_bit(BitVec::ofNat(0x61)) { True => False, False => b.unsigned_lt_bit(BitVec::ofNat(0x7b)) }
}
fn upcase(b: BitVec(8)) → BitVec(8) {
    match lower_byte(b) { True => b.sub(BitVec::ofNat(0x20)), False => b }
}
fn upcase_filter() → Stateless → BitVec(8) → Filtered<Stateless> { mapping(upcase) }
// The newline as one equality test (`eq_bit`), as a step and as a count; the
// keep step is a negative control's claim.
fn eq_drop_step(s: Stateless, b: BitVec(8)) → Filtered<Stateless> {
    match b.eq_bit(BitVec::ofNat(10)) { True => Filtered(s, None), False => Filtered(s, Some(b)) }
}
fn eq_keep_step(s: Stateless, b: BitVec(8)) → Filtered<Stateless> {
    match b.eq_bit(BitVec::ofNat(10)) { True => Filtered(s, Some(b)), False => Filtered(s, None) }
}
fn eq_line_step(count: Nat, byte: BitVec(8)) → Nat {
    match byte.eq_bit(BitVec::ofNat(10)) { False => count, True => Succ(count) }
}
fn eq_lines_filter() → Nat → BitVec(8) → Filtered<Nat> { counting(eq_line_step) }
"#;

// What every test stands on, built once per process.
fn library() -> Elaborator {
    static IMAGE: OnceLock<SemanticImage> = OnceLock::new();
    IMAGE.get_or_init(|| {
        let mut elab = checker();
        for (name, source) in [("elf64_read_pieces", READ_PIECES), ("stream_filter", STREAM_FILTER), ("filter_step_piece", STEP_PIECE), ("filters", FILTERS)] {
            elab.elab_module_source(name, source).unwrap_or_else(|e| panic!("{name}: {}", e.render(source)));
        }
        elab.semantic_image()
    }).elaborator()
}

fn generate(elab: &Elaborator, prefix: &str, step: &str, init: Option<&str>) -> FilterStepEmission {
    let step = reflect_filter_step(elab, step).unwrap_or_else(|e| panic!("{e}"));
    generate_elaborated_filter_step_x86(elab, prefix, &step, init).unwrap_or_else(|e| panic!("{e}"))
}

// Generated and elaborated: the pieces, then the step piece over them.
fn certify(prefix: &str, step: &str, init: Option<&str>) -> (Elaborator, FilterStepEmission) {
    let mut elab = library();
    let emission = generate(&elab, prefix, step, init);
    elab.elab_module_source(&format!("{prefix}_pieces"), &emission.pieces).unwrap_or_else(|e| panic!("{}", e.render(&emission.pieces)));
    elab.elab_module_source(&format!("{prefix}_step"), &emission.text).unwrap_or_else(|e| panic!("{}", e.render(&emission.text)));
    (elab, emission)
}

#[test]
fn steps_are_read_by_shape() {
    let elab = library();
    let read = |name: &str| reflect_filter_step(&elab, name).unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(read("filters::drop_step"), FilterStep::Step("filters::drop_step".into()));
    assert_eq!(read("filters::wc_filter"), FilterStep::Counting("filters::wc_step".into()));
    assert_eq!(read("filters::upcase_filter"), FilterStep::Mapping("filters::upcase".into()));
}

// `tr -d '\n'`: no state, so `rep` is `True` and nothing is counted; the
// piece is also used at a literal byte, where its flag is the step's.
#[test]
fn drop_step_piece_certifies() {
    let (elab, emission) = certify("drop", "filters::drop_step", None);
    assert!(!emission.bytes.is_empty());
    let client = "import drop_step; import filter_step_piece; import stream_filter; import filters; import function_ir_loop_trace; \
        import x86_64; import bitvec; import logic;
theorem drop_newline_silent<M>(before: MachineState<M>, rax: read_gpr(Rax, before.gprs) = @bitvec::BitVec::ofNat(8, 10).zero_extend(56)):
    read_gpr(Rbx, drop_step_piece<M>()(before, Stateless(), BitVec::ofNat(10), trivial, rax, trivial).after.gprs) = BitVec::ofNat(0) {
    drop_step_piece<M>()(before, Stateless(), BitVec::ofNat(10), trivial, rax, trivial).flag_is
}
theorem drop_letter_kept<M>(before: MachineState<M>, rax: read_gpr(Rax, before.gprs) = @bitvec::BitVec::ofNat(8, 0x61).zero_extend(56)):
    read_gpr(Rdx, drop_step_piece<M>()(before, Stateless(), BitVec::ofNat(0x61), trivial, rax, trivial).after.gprs) = BitVec::ofNat(0x61) {
    drop_step_piece<M>()(before, Stateless(), BitVec::ofNat(0x61), trivial, rax, trivial).byte_is
}";
    elab.semantic_image().elaborator().elab_module_source("drop_client", client).unwrap_or_else(|e| panic!("{}", e.render(client)));
}

// The same code claimed for a step that emits the other way round is
// refused where the claim is checked, not by a missing name.
#[test]
fn drop_code_is_not_another_steps_piece() {
    let elab = library();
    let emission = generate(&elab, "drop", "filters::drop_step", None);
    let mut elab = elab;
    elab.elab_module_source("drop_pieces", &emission.pieces).unwrap_or_else(|e| panic!("{}", e.render(&emission.pieces)));
    let claim = "StepPiece<M, stream_filter::Stateless>(drop_code(), drop_rep, drop_counts(), filters::drop_step)";
    assert!(emission.text.contains(claim), "{}", emission.text);
    let bad = emission.text.replace(claim, "StepPiece<M, stream_filter::Stateless>(drop_code(), drop_rep, drop_counts(), filters::keep_step)");
    let error = elab.elab_module_source("drop_step", &bad).expect_err("keep_step's claim").render(&bad);
    assert!(!error.contains("unbound") && !error.contains("ambiguous"), "{error}");
}

// `tr -s '\n'`: a byte and a Bool, updated in place, one branch passing the
// state through whole; at a literal state and byte the piece keeps it.
#[test]
fn squeeze_step_piece_certifies() {
    let (elab, _) = certify("squeeze", "filters::squeeze_step", Some("filters::Last(BitVec::ofNat(0), False)"));
    let client = "import squeeze_step; import filter_step_piece; import stream_filter; import filters; import function_ir_loop_trace; \
        import x86_64; import bitvec; import logic;
theorem squeeze_repeat_silent<M>(before: MachineState<M>, held: squeeze_rep(before.gprs, Last(BitVec::ofNat(10), True)),
    rax: read_gpr(Rax, before.gprs) = @bitvec::BitVec::ofNat(8, 10).zero_extend(56)):
    read_gpr(Rbx, squeeze_step_piece<M>()(before, Last(BitVec::ofNat(10), True), BitVec::ofNat(10), held, rax, trivial).after.gprs) = BitVec::ofNat(0) {
    squeeze_step_piece<M>()(before, Last(BitVec::ofNat(10), True), BitVec::ofNat(10), held, rax, trivial).flag_is
}";
    elab.semantic_image().elaborator().elab_module_source("squeeze_client", client).unwrap_or_else(|e| panic!("{}", e.render(client)));
}

#[test]
fn squeeze_code_is_not_another_steps_piece() {
    let elab = library();
    let emission = generate(&elab, "squeeze", "filters::squeeze_step", None);
    let mut elab = elab;
    elab.elab_module_source("squeeze_pieces", &emission.pieces).unwrap_or_else(|e| panic!("{}", e.render(&emission.pieces)));
    let claim = "squeeze_counts(), filters::squeeze_step)";
    assert!(emission.text.contains(claim), "{}", emission.text);
    let bad = emission.text.replace(claim, "squeeze_counts(), filters::stale_step)");
    let error = elab.elab_module_source("squeeze_step", &bad).expect_err("stale_step's claim").render(&bad);
    assert!(!error.contains("unbound") && !error.contains("ambiguous"), "{error}");
}

// `wc`'s step as a counting filter: three counts and a flag in R13-R15 and
// R8, nothing emitted.
#[test]
fn wc_counting_piece_certifies() {
    let (_, emission) = certify("wc", "filters::wc_filter", None);
    assert!(emission.text.contains("[λ (s: filters::WcState) => s.lines, λ (s: filters::WcState) => s.words, λ (s: filters::WcState) => s.bytes]"), "{}", emission.text);
}

// `wc -l`'s step: a Nat state, its count the state itself.
#[test]
fn lines_counting_piece_certifies() {
    let (_, emission) = certify("lines", "filters::lines_filter", None);
    assert!(emission.text.contains("[λ (s: Nat) => s]"), "{}", emission.text);
}

// `tr a-z A-Z` as a mapping: no state, always emitting the image.
#[test]
fn upcase_mapping_piece_certifies() {
    certify("upcase", "filters::upcase_filter", None);
}

// `tr -d '\n'` with the newline tested by `eq_bit`: certified, at a literal
// newline silent and at a letter kept; the same code claimed for the step
// that keeps newlines is refused at the claim.
#[test]
fn equality_step_piece_certifies() {
    let (elab, emission) = certify("eq_drop", "filters::eq_drop_step", None);
    assert!(emission.pieces.contains("eq_bit") || emission.text.contains("eq_bit"), "{}", emission.pieces);
    let client = "import eq_drop_step; import filter_step_piece; import stream_filter; import filters; import function_ir_loop_trace; \
        import x86_64; import bitvec; import logic;
theorem eq_drop_newline_silent<M>(before: MachineState<M>, rax: read_gpr(Rax, before.gprs) = @bitvec::BitVec::ofNat(8, 10).zero_extend(56)):
    read_gpr(Rbx, eq_drop_step_piece<M>()(before, Stateless(), BitVec::ofNat(10), trivial, rax, trivial).after.gprs) = BitVec::ofNat(0) {
    eq_drop_step_piece<M>()(before, Stateless(), BitVec::ofNat(10), trivial, rax, trivial).flag_is
}
theorem eq_drop_letter_kept<M>(before: MachineState<M>, rax: read_gpr(Rax, before.gprs) = @bitvec::BitVec::ofNat(8, 0x61).zero_extend(56)):
    read_gpr(Rdx, eq_drop_step_piece<M>()(before, Stateless(), BitVec::ofNat(0x61), trivial, rax, trivial).after.gprs) = BitVec::ofNat(0x61) {
    eq_drop_step_piece<M>()(before, Stateless(), BitVec::ofNat(0x61), trivial, rax, trivial).byte_is
}";
    elab.semantic_image().elaborator().elab_module_source("eq_drop_client", client).unwrap_or_else(|e| panic!("{}", e.render(client)));
    let elab = library();
    let emission = generate(&elab, "eq_drop", "filters::eq_drop_step", None);
    let mut elab = elab;
    elab.elab_module_source("eq_drop_pieces", &emission.pieces).unwrap_or_else(|e| panic!("{}", e.render(&emission.pieces)));
    let claim = "eq_drop_counts(), filters::eq_drop_step)";
    assert!(emission.text.contains(claim), "{}", emission.text);
    let bad = emission.text.replace(claim, "eq_drop_counts(), filters::eq_keep_step)");
    let error = elab.elab_module_source("eq_drop_step", &bad).expect_err("eq_keep_step's claim").render(&bad);
    assert!(!error.contains("unbound") && !error.contains("ambiguous"), "{error}");
}

// `wc -l`'s count with the newline tested by `eq_bit`.
#[test]
fn equality_counting_piece_certifies() {
    let (_, emission) = certify("eq_lines", "filters::eq_lines_filter", None);
    assert!(emission.text.contains("[λ (s: Nat) => s]"), "{}", emission.text);
}

// Steps the generator does not take are refused when they are read, with a
// message that says why.
#[test]
fn unsupported_steps_are_refused() {
    let mut elab = library();
    let source = r#"import stream_filter; import filters; import bitvec; import bool; import nat; import option;
record Outer { inner: Last, count: Nat }
fn nested_step(s: Outer, b: BitVec(8)) → Filtered<Outer> { Filtered(s, None) }
fn delegated_step(s: Last, b: BitVec(8)) → Filtered<Last> { squeeze_step(s, b) }
"#;
    elab.elab_module_source("refused", source).unwrap_or_else(|e| panic!("{}", e.render(source)));
    for (step, expected) in [("refused::nested_step", "record fields must be Nat, Bool, or BitVec(w)"),
        ("refused::delegated_step", "must construct Filtered(next, emit)")] {
        let step = reflect_filter_step(&elab, step).unwrap_or_else(|e| panic!("{e}"));
        let error = generate_elaborated_filter_step_x86(&elab, "refused", &step, None).expect_err("refused").to_string();
        assert!(error.contains(expected), "{error}");
    }
}
