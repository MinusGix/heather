//! First x86-64 vertical slice: decoded register MOV/ADD/SUB/CMP/TEST, flags, opaque
//! memory preservation, and length-derived RIP fallthrough.

use crate::support;

use heather_elab::{ElabError, Elaborator, stats};

const LOGIC: &str = include_str!("../../../lib/std/core/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/core/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/num/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/core/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/core/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/data/list.hthr");
const ALGEBRA: &str = include_str!("../../../lib/std/algebra/algebra.hthr");
const INT: &str = include_str!("../../../lib/std/num/int.hthr");
const BITVEC: &str = include_str!("../../../lib/std/bitvec/bitvec.hthr");
const RELATION: &str = include_str!("../../../lib/std/relation/relation.hthr");
const LOCATION: &str = include_str!("../../../lib/std/machine/location.hthr");
const CERTIFIED_LOOKUP: &str = include_str!("../../../lib/std/data/certified_lookup.hthr");
const X86_64: &str = include_str!("../../../lib/std/arch/x86_64/x86_64.hthr");

const X86_MODULES: &[(&str, &str)] = &[
    ("logic", LOGIC),
    ("bool", BOOL),
    ("nat", NAT),
    ("option", OPTION),
    ("pair", PAIR),
    ("list", LIST),
    ("algebra", ALGEBRA),
    ("int", INT),
    ("bitvec", BITVEC),
    ("relation", RELATION),
    ("relation_props", include_str!("../../../lib/std/relation/relation_props.hthr")),
    ("location", LOCATION),
    ("certified_lookup", CERTIFIED_LOOKUP),
    ("x86_64", X86_64),
];

fn elaborated() -> Elaborator {
    let report_metrics = std::env::var_os("HEATHER_VALUE_METRICS").is_some();
    let timings = stats::Dest::from_env();
    let report_phases = timings.is_some();
    if !report_metrics && !report_phases {
        return support::semantic_test_base(X86_MODULES);
    }

    // Profiling asks what fresh elaboration of the x86 module costs. Keep
    // that path source-only; replay numbers have their own session benchmark.
    let mut e = Elaborator::with_prelude().expect("prelude");
    for &(name, src) in &X86_MODULES[..X86_MODULES.len() - 1] {
        if let Err(err) = e.elab_module_source(name, src) {
            panic!("{name} did not check: {}", err.render(src));
        }
    }
    if report_metrics {
        e.enable_value_metrics();
    }
    // One dump, from the one registry (`docs/instrumentation-design.md` §4).
    if report_phases {
        e.enable_item_timings();
    }
    {
        let _module = stats::scope(stats::ScopeKind::Module, "x86_64", "");
        if let Err(err) = e.elab_module_source("x86_64", X86_64) {
            panic!("x86_64 did not check: {}", err.render(X86_64));
        }
    }
    if let Some(dest) = &timings {
        let _ = stats::dump(dest, &e.take_item_timings());
    }
    if report_metrics {
        eprintln!(
            "x86_64 module value metrics: {:?}",
            e.value_metrics().unwrap()
        );
    }
    e
}

#[test]
fn x86_64_suite() {
    let base = elaborated();
    if std::env::var_os("HEATHER_X86_BASE_ONLY").is_some() {
        return;
    }
    let report_metrics = std::env::var_os("HEATHER_VALUE_METRICS").is_some();
    if report_metrics {
        base.reset_value_metrics();
    }
    fetched_instruction_boundary_checks(&base);
    register_and_execution_laws_check(&base);
    mov_ri_encoding_decoding_and_execution_check(&base);
    setcc_encoding_decoding_and_execution_check(&base);
    same_defined_setoid_check(&base);
    if report_metrics {
        eprintln!(
            "x86_64 execution-law metrics: {:?}",
            base.value_metrics().unwrap()
        );
        base.reset_value_metrics();
    }
    direct_decoder_agrees_with_reference_on_boundary_cases(&base);
    if report_metrics {
        eprintln!(
            "x86_64 decoder-agreement metrics: {:?}",
            base.value_metrics().unwrap()
        );
        base.reset_value_metrics();
    }
    invalid_decoded_lengths_are_refused(&base);
    unsupported_or_malformed_byte_spans_are_refused(&base);
    if report_metrics {
        eprintln!(
            "x86_64 negative-control metrics: {:?}",
            base.value_metrics().unwrap()
        );
    }
}

// `SameDefinedState` is `=` pulled back along `erase_af`: a registered
// equivalence, `≈` at `MachineState`, and congruence through the steps that
// commute with erasing AF. The controls: a function that branches on AF has
// no such proof and no certificate for `rel_cong`, and TEST's two permitted
// results are related without being equal.
fn same_defined_setoid_check(base: &Elaborator) {
    let mut e = base.clone();
    let src = r#"
import x86_64;
import relation_props;
import bool;
import logic;
import list;

// Two ordinary instructions in a row, from states that differ only in AF:
// congruence walks both steps, each by its registered evidence.
theorem two_steps_related<M>(first, second: Instruction, a, b: MachineState<M>, same: a ≈ b):
    execute_normal(decoded_canonical(second), execute_normal(decoded_canonical(first), a)) ≈
    execute_normal(decoded_canonical(second), execute_normal(decoded_canonical(first), b)) {
    rel_cong(same)
}

// TEST's two permitted results, then one more step, then back.
theorem test_then_step<M>(left, right: Gpr, next: Instruction, before: MachineState<M>, x: MachineState<M>,
    back: x = execute_normal(decoded_canonical(next), execute_test(left, right, 3, before, False))):
    execute_normal(decoded_canonical(next), execute_test(left, right, 3, before, True)) ≈ x {
    calc {
        execute_normal(decoded_canonical(next), execute_test(left, right, 3, before, True)) ≈
            execute_normal(decoded_canonical(next), execute_test(left, right, 3, before, False)) :=
            rel_cong(execute_test_same_defined(left, right, 3, before, True, False)),
        ≈ x := SameDefinedState::of_equal(sym(back)),
    }
}

// Generic setoid lemmas apply: the registered equivalence is found by resolution.
theorem meet<A: Equivalence(R)>(R: A → A → Type, a, b, c: A, ab: R(a, b), cb: R(c, b)): R(a, c) {
    A.rel_trans(a, b, c, ab, A.rel_sym(c, b, cb))
}
theorem through_the_instance<M>(a, b, c: MachineState<M>, ab: a ≈ b, cb: c ≈ b): a ≈ c {
    meet(SameDefinedState<M>, a, b, c, ab, cb)
}
"#;
    if let Err(err) = e.elab_module_source("same_defined_setoid", src) {
        panic!("the SameDefinedState setoid did not check: {}", err.render(src));
    }
    let header = "import x86_64;\nimport relation_props;\nimport bool;\nimport logic;\nimport list;\n\n\
        fn branch_on_af<M>(s: MachineState<M>) → MachineState<M> {\n\
        MachineState(s.gprs, s.flags, match s.flags.af { True => s.rip, False => next_rip(s.rip, 1) }, s.memory)\n}\n";
    for (name, body, expect) in [
        (
            "af_reader_commutes",
            "theorem af_reader_respects<M>(): PreservesRelation(SameDefinedState<M>, SameDefinedState<M>, branch_on_af<M>) {\n\
                 same_defined_respects(branch_on_af<M>, λ state => refl)\n}\n",
            "NotConvertible",
        ),
        (
            "af_reader_congruence",
            "theorem af_reader_related<M>(a, b: MachineState<M>, same: a ≈ b): branch_on_af(a) ≈ branch_on_af(b) {\n\
                 rel_cong(same)\n}\n",
            "?compatibility",
        ),
        (
            "test_results_equal",
            "theorem test_results_equal<M>(left, right: Gpr, before: MachineState<M>):\n\
                 execute_test(left, right, 3, before, True) = execute_test(left, right, 3, before, False) {\n    refl\n}\n",
            "NotConvertible",
        ),
    ] {
        let bad = format!("{header}\n{body}");
        let mut e = base.clone();
        let error = e.elab_module_source(name, &bad).expect_err(name).render(&bad);
        assert!(error.contains(expect), "{name}: {error}");
    }
}

fn setcc_encoding_decoding_and_execution_check(base: &Elaborator) {
    let mut e = base.clone();
    let src = r#"
import x86_64;
import bool;
import bitvec;
import list;
import logic;
import option;

theorem canonical_setcc_bytes():
    canonical_bytes(SetBelow(Al)) =
        [@bitvec::BitVec::ofNat(8, 15), @bitvec::BitVec::ofNat(8, 146), @bitvec::BitVec::ofNat(8, 192)]
    ∧ canonical_bytes(SetLess(Bl)) =
        [@bitvec::BitVec::ofNat(8, 15), @bitvec::BitVec::ofNat(8, 156), @bitvec::BitVec::ofNat(8, 195)]
    ∧ canonical_bytes(SetEqual(Cl)) =
        [@bitvec::BitVec::ofNat(8, 15), @bitvec::BitVec::ofNat(8, 148), @bitvec::BitVec::ofNat(8, 193)]
{
    And(refl, And(refl, refl))
}

theorem canonical_setcc_decodes():
    decode_instruction(canonical_bytes(SetBelow(Al))) =
        Some(decoded_canonical(SetBelow(Al)))
    ∧ decode_instruction(canonical_bytes(SetLess(Bl))) =
        Some(decoded_canonical(SetLess(Bl)))
    ∧ decode_instruction(canonical_bytes(SetEqual(Cl))) =
        Some(decoded_canonical(SetEqual(Cl)))
{
    And(refl, And(refl, refl))
}

// 0F 95 (SETNE) is not modelled and must not decode as SETE.
theorem unmodelled_setcc_is_rejected():
    decode_instruction(
        [@bitvec::BitVec::ofNat(8, 15), @bitvec::BitVec::ofNat(8, 149), @bitvec::BitVec::ofNat(8, 192)]) = None
{
    refl
}

theorem malformed_setcc_is_rejected():
    decode_instruction(
        [@bitvec::BitVec::ofNat(8, 15), @bitvec::BitVec::ofNat(8, 146)]) = None
    ∧ decode_instruction(
        [@bitvec::BitVec::ofNat(8, 14), @bitvec::BitVec::ofNat(8, 146), @bitvec::BitVec::ofNat(8, 192)]) = None
    ∧ decode_instruction(
        [@bitvec::BitVec::ofNat(8, 15), @bitvec::BitVec::ofNat(8, 146), @bitvec::BitVec::ofNat(8, 196)]) = None
    ∧ decode_instruction(
        [@bitvec::BitVec::ofNat(8, 15), @bitvec::BitVec::ofNat(8, 146), @bitvec::BitVec::ofNat(8, 192),
            @bitvec::BitVec::ofNat(8, 0)]) = None
{
    And(refl, And(refl, And(refl, refl)))
}

theorem cmp_flags_are_function_ir_conditions(left, right: BitVec(64)):
    sub_flags(left, right).cf = @bitvec::BitVec::unsigned_lt_bit(64, left, right)
    ∧ bool::Bool::xor(sub_flags(left, right).sf, sub_flags(left, right).of) =
        @bitvec::BitVec::signed_lt_bit(64, left, right)
{
    And(refl, refl)
}

// ZF is equality by a law rather than by definition.
theorem cmp_zero_flag_is_equality(left, right: BitVec(64)):
    sub_flags(left, right).zf = @bitvec::BitVec::eq_bit(64, left, right)
{
    zero_bits_sub(64, left, right)
}

"#;
    if let Err(err) = e.elab_module_source("x86_setcc_checks", src) {
        panic!("x86 SETcc checks did not check: {}", err.render(src));
    }
}

fn register_and_execution_laws_check(base: &Elaborator) {
    let mut e = base.clone();
    let src = r#"
import x86_64;
import bitvec;
import bool;
import logic;
import nat;
import list;
import option;

theorem register_indices(): Rax.index() = 0 ∧ R15.index() = 15
{ And(refl, refl) }

theorem register_write_is_observable(register: Gpr, value: BitVec(64),
    registers: Gprs):
    read_gpr(register, write_gpr(register, value, registers)) = value
{
    read_gpr_after_write(register, value, registers)
}

theorem execution_advances_rip<M>(decoded: DecodedInstruction,
    before: MachineState<M>):
    execute_normal(decoded, before).rip =
        next_rip(before.rip, decoded.length)
{
    execute_normal_advances_rip(decoded, before)
}

theorem test_has_both_architectural_af_outcomes<M>(left, right: Gpr,
    length: Nat, valid: ∥1 <= length ∧ length <= 15∥,
    before: MachineState<M>):
    Execute(
        DecodedInstruction(instruction := TestRR(left, right),
            length := length, valid_length := valid),
        before, Returned(execute_test(left, right, length, before, False)))
    ∧
    Execute(
        DecodedInstruction(instruction := TestRR(left, right),
            length := length, valid_length := valid),
        before, Returned(execute_test(left, right, length, before, True)))
{
    And(test_allows_af(left, right, length, valid, before, False),
        test_allows_af(left, right, length, valid, before, True))
}

theorem test_preserves_the_frame<M>(left, right: Gpr, length: Nat,
    before: MachineState<M>, af: Bool):
    execute_test(left, right, length, before, af).gprs = before.gprs
    ∧ execute_test(left, right, length, before, af).memory = before.memory
    ∧ execute_test(left, right, length, before, af).rip =
        next_rip(before.rip, length)
{
    execute_test_frames(left, right, length, before, af)
}

theorem canonical_low_register_bytes():
    canonical_bytes(MovRR(Rax, Rbx)) =
        Cons(@BitVec::ofNat(8, 72), Cons(@BitVec::ofNat(8, 137), Cons(@BitVec::ofNat(8, 216), Nil)))
{
    refl
}

theorem canonical_extended_register_bytes():
    canonical_bytes(AddRR(R9, R10)) =
        Cons(@BitVec::ofNat(8, 77), Cons(@BitVec::ofNat(8, 1), Cons(@BitVec::ofNat(8, 209), Nil)))
{
    refl
}

theorem canonical_sub_and_cmp_bytes():
    canonical_bytes(SubRR(R9, R10)) =
        Cons(@BitVec::ofNat(8, 77), Cons(@BitVec::ofNat(8, 41), Cons(@BitVec::ofNat(8, 209), Nil)))
    ∧ canonical_bytes(CmpRR(Rax, Rbx)) =
        Cons(@BitVec::ofNat(8, 72), Cons(@BitVec::ofNat(8, 57), Cons(@BitVec::ofNat(8, 216), Nil)))
{
    And(refl, refl)
}

theorem canonical_logic_bytes():
    canonical_bytes(AndRR(R9, R10)) =
        Cons(@BitVec::ofNat(8, 77), Cons(@BitVec::ofNat(8, 33), Cons(@BitVec::ofNat(8, 209), Nil)))
    ∧ canonical_bytes(OrRR(Rax, Rbx)) =
        Cons(@BitVec::ofNat(8, 72), Cons(@BitVec::ofNat(8, 9), Cons(@BitVec::ofNat(8, 216), Nil)))
    ∧ canonical_bytes(XorRR(R15, Rax)) =
        Cons(@BitVec::ofNat(8, 73), Cons(@BitVec::ofNat(8, 49), Cons(@BitVec::ofNat(8, 199), Nil)))
{
    And(refl, And(refl, refl))
}

theorem canonical_test_extension_bytes():
    canonical_bytes(TestRR(R15, Rax)) =
        Cons(@BitVec::ofNat(8, 73), Cons(@BitVec::ofNat(8, 133), Cons(@BitVec::ofNat(8, 199), Nil)))
{
    refl
}

theorem mov_direction_encodings_normalize(start: BitVec(64)):
    DecodedAt(encoded_at(start, MovRR(Rax, Rbx)),
        decoded_rr(MovRR(Rax, Rbx)))
    ∧ DecodedAt(
        InstructionBytes(start := start,
            bytes := Cons(@BitVec::ofNat(8, 72), Cons(@BitVec::ofNat(8, 139),
                Cons(@BitVec::ofNat(8, 195), Nil)))),
        decoded_rr(MovRR(Rax, Rbx)))
{
    And(canonical_encoding_decodes(start, MovRR(Rax, Rbx)),
        alternate_mov_encoding_decodes(start, Rax, Rbx))
}

theorem add_direction_encodings_normalize(start: BitVec(64)):
    DecodedAt(encoded_at(start, AddRR(R9, R10)),
        decoded_rr(AddRR(R9, R10)))
    ∧ DecodedAt(
        InstructionBytes(start := start,
            bytes := Cons(@BitVec::ofNat(8, 77), Cons(@BitVec::ofNat(8, 3),
                Cons(@BitVec::ofNat(8, 202), Nil)))),
        decoded_rr(AddRR(R9, R10)))
{
    And(canonical_encoding_decodes(start, AddRR(R9, R10)),
        alternate_add_encoding_decodes(start, R9, R10))
}

theorem sub_and_cmp_direction_encodings_normalize(start: BitVec(64)):
    DecodedAt(encoded_at(start, SubRR(R9, R10)),
        decoded_rr(SubRR(R9, R10)))
    ∧ DecodedAt(
        InstructionBytes(start := start,
            bytes := alternate_sub_bytes(R9, R10)),
        decoded_rr(SubRR(R9, R10)))
    ∧ DecodedAt(encoded_at(start, CmpRR(Rax, Rbx)),
        decoded_rr(CmpRR(Rax, Rbx)))
    ∧ DecodedAt(
        InstructionBytes(start := start,
            bytes := alternate_cmp_bytes(Rax, Rbx)),
        decoded_rr(CmpRR(Rax, Rbx)))
{
    And(canonical_encoding_decodes(start, SubRR(R9, R10)),
        And(alternate_sub_encoding_decodes(start, R9, R10),
            And(canonical_encoding_decodes(start, CmpRR(Rax, Rbx)),
                alternate_cmp_encoding_decodes(start, Rax, Rbx))))
}

theorem compiler_bytes_reach_execution<M>(instruction: Instruction,
    before: MachineState<M>):
    ExecuteAt(encoded_at(before.rip, instruction),
        decoded_canonical(instruction), before,
        Returned(execute_normal(decoded_canonical(instruction), before)))
{
    canonical_encoding_executes(instruction, before)
}

theorem decoded_length_drives_fallthrough<M>(span: InstructionBytes,
    decoded: DecodedInstruction, before: MachineState<M>,
    decoding: DecodedAt(span, decoded)):
    execute_normal(decoded, before).rip =
        next_rip(before.rip, canonical_length(decoded.instruction))
{
    decoded_execution_advances_by_consumed_length(span, decoded, before, decoding)
}

theorem alternate_mov_bytes_reach_execution<M>(destination, source: Gpr,
    before: MachineState<M>):
    ExecuteAt(
        InstructionBytes(start := before.rip,
            bytes := alternate_mov_bytes(destination, source)),
        decoded_rr(MovRR(destination, source)), before,
        Returned(execute_normal(decoded_rr(MovRR(destination, source)), before)))
{
    alternate_mov_encoding_executes(destination, source, before)
}

theorem alternate_add_bytes_reach_execution<M>(destination, source: Gpr,
    before: MachineState<M>):
    ExecuteAt(
        InstructionBytes(start := before.rip,
            bytes := alternate_add_bytes(destination, source)),
        decoded_rr(AddRR(destination, source)), before,
        Returned(execute_normal(decoded_rr(AddRR(destination, source)), before)))
{
    alternate_add_encoding_executes(destination, source, before)
}

theorem executable_decoder_accepts_canonical_mov():
    decode_instruction(canonical_bytes(MovRR(Rax, Rbx))) =
        Some(decoded_rr(MovRR(Rax, Rbx)))
{
    refl
}

theorem executable_decoder_accepts_alternate_mov():
    decode_instruction(alternate_mov_bytes(Rax, Rbx)) =
        Some(decoded_rr(MovRR(Rax, Rbx)))
{
    refl
}

theorem executable_decoder_accepts_both_add_directions():
    decode_instruction(canonical_bytes(AddRR(Rax, Rcx))) =
        Some(decoded_rr(AddRR(Rax, Rcx)))
    ∧ decode_instruction(alternate_add_bytes(Rax, Rcx)) =
        Some(decoded_rr(AddRR(Rax, Rcx)))
{
    And(refl, refl)
}

theorem executable_decoder_accepts_test():
    decode_instruction(canonical_bytes(TestRR(Rax, Rbx))) =
        Some(decoded_rr(TestRR(Rax, Rbx)))
{
    refl
}

theorem executable_decoder_accepts_logic():
    decode_instruction(canonical_bytes(AndRR(R9, R10))) =
        Some(decoded_rr(AndRR(R9, R10)))
    ∧ decode_instruction(canonical_bytes(OrRR(Rax, Rbx))) =
        Some(decoded_rr(OrRR(Rax, Rbx)))
    ∧ decode_instruction(canonical_bytes(XorRR(R15, Rax))) =
        Some(decoded_rr(XorRR(R15, Rax)))
{
    And(refl, And(refl, refl))
}

theorem executable_decoder_accepts_both_sub_and_cmp_directions():
    decode_instruction(canonical_bytes(SubRR(R9, R10))) =
        Some(decoded_rr(SubRR(R9, R10)))
    ∧ decode_instruction(alternate_sub_bytes(R9, R10)) =
        Some(decoded_rr(SubRR(R9, R10)))
    ∧ decode_instruction(canonical_bytes(CmpRR(Rax, Rbx))) =
        Some(decoded_rr(CmpRR(Rax, Rbx)))
    ∧ decode_instruction(alternate_cmp_bytes(Rax, Rbx)) =
        Some(decoded_rr(CmpRR(Rax, Rbx)))
{
    And(refl, And(refl, And(refl, refl)))
}

theorem executable_decoder_is_complete(bytes: List<BitVec(8)>,
    instruction: Instruction,
    decoding: DecodesInstruction(bytes, instruction)):
    decode_instruction(bytes) = Some(decoded_canonical(instruction))
{
    decode_instruction_complete(bytes, instruction, decoding)
}

theorem direct_decoder_agrees_when_reference_succeeds(
    bytes: List<BitVec(8)>, result: ByteDecode(bytes),
    success: decode_bytes_reference(bytes) = Some(result)):
    decode_instruction(bytes) = decode_instruction_reference(bytes)
{
    direct_agrees_with_successful_reference(bytes, result, success)
}

theorem subtraction_writes_the_difference(destination, source: Gpr,
    before: Gprs):
    read_gpr(destination, execute_sub(destination, source, before).gprs) =
        @bitvec::BitVec::sub(64, read_gpr(destination, before),
            read_gpr(source, before))
{
    execute_sub_writes_difference(destination, source, before)
}

theorem comparison_preserves_registers_and_memory<M>(left, right: Gpr,
    length: Nat, valid: ∥1 <= length ∧ length <= 15∥,
    before: MachineState<M>):
    execute_normal(
        DecodedInstruction(instruction := CmpRR(left, right),
            length := length, valid_length := valid), before).gprs = before.gprs
    ∧ execute_normal(
        DecodedInstruction(instruction := CmpRR(left, right),
            length := length, valid_length := valid), before).memory = before.memory
{
    And(execute_cmp_frames(left, right, length, valid, before).left,
        execute_cmp_frames(left, right, length, valid, before).right.left)
}

theorem executable_decoder_accepts_extended_registers():
    decode_instruction(canonical_bytes(MovRR(Rax, R8))) =
        Some(decoded_rr(MovRR(Rax, R8)))
{
    refl
}

theorem executable_decoder_rejects_bad_shape_and_opcode():
    decode_instruction(Cons(@BitVec::ofNat(8, 72), Cons(@BitVec::ofNat(8, 137), Nil))) = None
    ∧ decode_instruction(rr_bytes(144, Rax, Rbx)) = None
{
    And(refl, refl)
}

theorem executable_decoder_rejects_missing_rex_w_and_memory_modrm():
    decode_instruction(Cons(@BitVec::ofNat(8, 64), Cons(@BitVec::ofNat(8, 137),
        Cons(@BitVec::ofNat(8, 216), Nil)))) = None
    ∧ decode_instruction(Cons(@BitVec::ofNat(8, 72), Cons(@BitVec::ofNat(8, 137),
        Cons(@BitVec::ofNat(8, 24), Nil)))) = None
{
    And(refl, refl)
}

theorem executable_decoder_soundness_is_carried_by_result(
    bytes: List<BitVec(8)>, result: ByteDecode(bytes),
    success: decode_bytes(bytes) = Some(result)):
    DecodesInstruction(bytes, result.instruction)
{
    decode_bytes_sound(bytes, result, success)
}

theorem executable_decoder_result_reaches_execution<M>(
    bytes: List<BitVec(8)>, result: ByteDecode(bytes), before: MachineState<M>):
    ExecuteAt(
        InstructionBytes(start := before.rip, bytes := bytes),
        decoded_canonical(result.instruction), before,
        Returned(execute_normal(decoded_canonical(result.instruction), before)))
{
    decoded_byte_result_executes(bytes, result, before)
}

theorem external_mov_bytes_reach_execution<M>(before: MachineState<M>):
    ExecuteAt(
        InstructionBytes(start := before.rip,
            bytes := Cons(@BitVec::ofNat(8, 72), Cons(@BitVec::ofNat(8, 137),
                Cons(@BitVec::ofNat(8, 216), Nil)))),
        decoded_rr(MovRR(Rax, Rbx)), before,
        Returned(execute_normal(decoded_rr(MovRR(Rax, Rbx)), before)))
{
    external_decoding_executes(
        InstructionBytes(start := before.rip,
            bytes := Cons(@BitVec::ofNat(8, 72), Cons(@BitVec::ofNat(8, 137),
                Cons(@BitVec::ofNat(8, 216), Nil)))),
        decoded_rr(MovRR(Rax, Rbx)), before,
        Returned(execute_normal(decoded_rr(MovRR(Rax, Rbx)), before)),
        refl, And(Inl(And(refl, And(refl, refl))), refl),
        canonical_execute_normal_is_allowed(MovRR(Rax, Rbx), before))
}

"#;
    if let Err(err) = e.elab_module_source("probe", src) {
        let msg = match err {
            ElabError::Elab { msg, .. } => msg,
            other => format!("{other}"),
        };
        panic!("x86 computations did not check: {msg}");
    }
}

fn mov_ri_encoding_decoding_and_execution_check(base: &Elaborator) {
    let mut e = base.clone();
    let src = r#"
import x86_64;
import bitvec;
import list;
import option;
import logic;

theorem mov_ri_low_zero_bytes():
    canonical_bytes(MovRI(Rax, @BitVec::zero(64))) =
        [@BitVec::ofNat(8, 72), @BitVec::ofNat(8, 184),
         @BitVec::zero(8), @BitVec::zero(8), @BitVec::zero(8), @BitVec::zero(8),
         @BitVec::zero(8), @BitVec::zero(8), @BitVec::zero(8), @BitVec::zero(8)]
{ refl }

theorem mov_ri_extended_ones_bytes():
    canonical_bytes(MovRI(R15, @BitVec::all_ones(64))) =
        [@BitVec::ofNat(8, 73), @BitVec::ofNat(8, 191),
         @BitVec::all_ones(8), @BitVec::all_ones(8), @BitVec::all_ones(8), @BitVec::all_ones(8),
         @BitVec::all_ones(8), @BitVec::all_ones(8), @BitVec::all_ones(8), @BitVec::all_ones(8)]
{ refl }

// A full-width asymmetric immediate pins the little-endian byte order, and a
// high-bit one the top byte; both check under ordinary fuel now that
// `ofNat` is width-bounded (issues/bitvec-ofnat-large-literals.md).
theorem mov_ri_full_width_asymmetric_bytes():
    canonical_bytes(MovRI(R9, @BitVec::ofNat(64, 81985529216486895))) =
        [@BitVec::ofNat(8, 73), @BitVec::ofNat(8, 185),
         @BitVec::ofNat(8, 239), @BitVec::ofNat(8, 205), @BitVec::ofNat(8, 171), @BitVec::ofNat(8, 137),
         @BitVec::ofNat(8, 103), @BitVec::ofNat(8, 69), @BitVec::ofNat(8, 35), @BitVec::ofNat(8, 1)]
{ refl }

theorem mov_ri_high_bit_bytes():
    canonical_bytes(MovRI(Rax, @BitVec::ofNat(64, 9223372036854775809))) =
        [@BitVec::ofNat(8, 72), @BitVec::ofNat(8, 184),
         @BitVec::ofNat(8, 1), @BitVec::zero(8), @BitVec::zero(8), @BitVec::zero(8),
         @BitVec::zero(8), @BitVec::zero(8), @BitVec::zero(8), @BitVec::ofNat(8, 128)]
{ refl }

theorem mov_ri_canonical_lengths():
    canonical_length(MovRI(Rax, @BitVec::zero(64))) = 10
    ∧ canonical_bytes(MovRI(R15, @BitVec::all_ones(64))).len() = 10
    ∧ decoded_canonical(MovRI(R8, @BitVec::one(64))).length = 10
{ And(refl, And(refl, refl)) }

theorem mov_ri_decoder_accepts_boundaries():
    decode_instruction(canonical_bytes(MovRI(Rax, @BitVec::zero(64)))) =
        Some(decoded_canonical(MovRI(Rax, @BitVec::zero(64))))
    ∧ decode_instruction(canonical_bytes(MovRI(R15, @BitVec::all_ones(64)))) =
        Some(decoded_canonical(MovRI(R15, @BitVec::all_ones(64))))
{
    And(decode_mov_ri_complete(Rax, @BitVec::zero(64)),
        decode_mov_ri_complete(R15, @BitVec::all_ones(64)))
}

theorem mov_ri_decoder_rejects_truncated_trailing_and_bad_head():
    decode_instruction(
        [@BitVec::ofNat(8, 72), @BitVec::ofNat(8, 184),
         @BitVec::zero(8), @BitVec::zero(8), @BitVec::zero(8), @BitVec::zero(8),
         @BitVec::zero(8), @BitVec::zero(8), @BitVec::zero(8)]) = None
    ∧ decode_instruction(
        [@BitVec::ofNat(8, 72), @BitVec::ofNat(8, 184),
         @BitVec::zero(8), @BitVec::zero(8), @BitVec::zero(8), @BitVec::zero(8),
         @BitVec::zero(8), @BitVec::zero(8), @BitVec::zero(8), @BitVec::zero(8), @BitVec::zero(8)]) = None
    ∧ decode_instruction(
        [@BitVec::ofNat(8, 64), @BitVec::ofNat(8, 184),
         @BitVec::zero(8), @BitVec::zero(8), @BitVec::zero(8), @BitVec::zero(8),
         @BitVec::zero(8), @BitVec::zero(8), @BitVec::zero(8), @BitVec::zero(8)]) = None
{ And(refl, And(refl, refl)) }

theorem mov_ri_executes_and_frames<M>(destination: Gpr,
    immediate: BitVec(64), before: MachineState<M>):
    read_gpr(destination,
        execute_normal(decoded_canonical(MovRI(destination, immediate)),
            before).gprs) = immediate
    ∧ execute_normal(decoded_canonical(MovRI(destination, immediate)),
        before).flags = before.flags
    ∧ execute_normal(decoded_canonical(MovRI(destination, immediate)),
        before).memory = before.memory
    ∧ execute_normal(decoded_canonical(MovRI(destination, immediate)),
        before).rip = next_rip(before.rip, 10)
{
    And(mov_ri_writes_immediate(destination, immediate, before),
        And(mov_ri_preserves_flags(destination, immediate, before),
            And(mov_ri_preserves_memory(destination, immediate, before), refl)))
}
"#;
    if let Err(err) = e.elab_module_source("mov_ri", src) {
        let msg = match err {
            ElabError::Elab { msg, .. } => msg,
            other => format!("{other}"),
        };
        panic!("MOV r64, imm64 laws did not check: {msg}");
    }

    // Byte order is load-bearing: the same bytes big-endian are refused by
    // conversion, not by fuel.
    let mut e = base.clone();
    let swapped = r#"
import x86_64;
import bitvec;
import list;

theorem mov_ri_big_endian_is_wrong():
    canonical_bytes(MovRI(R9, @BitVec::ofNat(64, 81985529216486895))) =
        [@BitVec::ofNat(8, 73), @BitVec::ofNat(8, 185),
         @BitVec::ofNat(8, 1), @BitVec::ofNat(8, 35), @BitVec::ofNat(8, 69), @BitVec::ofNat(8, 103),
         @BitVec::ofNat(8, 137), @BitVec::ofNat(8, 171), @BitVec::ofNat(8, 205), @BitVec::ofNat(8, 239)]
{ refl }
"#;
    match e.elab_module_source("mov_ri_swapped", swapped) {
        Ok(()) => panic!("big-endian immediate bytes were accepted"),
        Err(err) => {
            let msg = err.render(swapped);
            assert!(msg.contains("NotConvertible"), "{msg}");
        }
    }
}

fn direct_decoder_agrees_with_reference_on_boundary_cases(base: &Elaborator) {
    let mut e = base.clone();
    let src = r#"
import x86_64;
import bitvec;
import list;
import logic;

theorem reference_decoder_accepts_extended_mov():
    decode_instruction_reference(canonical_bytes(MovRR(R8, R9))) =
        Some(decoded_rr(MovRR(R8, R9)))
{ refl }

theorem reference_decoder_accepts_logic():
    decode_instruction_reference(canonical_bytes(AndRR(Rax, Rbx))) =
        Some(decoded_rr(AndRR(Rax, Rbx)))
    ∧ decode_instruction_reference(canonical_bytes(OrRR(Rax, Rbx))) =
        Some(decoded_rr(OrRR(Rax, Rbx)))
    ∧ decode_instruction_reference(canonical_bytes(XorRR(Rax, Rbx))) =
        Some(decoded_rr(XorRR(Rax, Rbx)))
{ And(refl, And(refl, refl)) }

theorem reference_decoder_rejects_bad_rex():
    decode_instruction_reference(Cons(@BitVec::ofNat(8, 64), Cons(@BitVec::ofNat(8, 137),
        Cons(@BitVec::ofNat(8, 216), Nil)))) = None
{ refl }
"#;
    if let Err(err) = e.elab_module_source("decoder_agreement", src) {
        let msg = match err {
            ElabError::Elab { msg, .. } => msg,
            other => format!("{other}"),
        };
        panic!("direct/reference decoder agreement did not check: {msg}");
    }
}

fn invalid_decoded_lengths_are_refused(base: &Elaborator) {
    let mut e = base.clone();
    let src = r#"
import x86_64;
fn impossible() -> DecodedInstruction {
    DecodedInstruction(instruction := MovRR(Rax, Rbx), length := 0,
        valid_length := squash(And(trivial, trivial)))
}
"#;
    assert!(
        e.elab_module_source("bad", src).is_err(),
        "a zero-byte x86 instruction was accepted"
    );
}

fn unsupported_or_malformed_byte_spans_are_refused(base: &Elaborator) {
    let cases = [
        // Missing ModRM byte: exact-span decoding rejects truncation.
        r#"
import x86_64;
import bitvec;
import list;
fn impossible(start: BitVec(64)) -> DecodedAt(
    InstructionBytes(start := start,
        bytes := Cons(@BitVec::ofNat(8, 72), Cons(@BitVec::ofNat(8, 137), Nil))),
    decoded_rr(MovRR(Rax, Rbx)))
{
    And(refl, refl)
}
"#,
        // 8B reverses operand roles; keeping the 89 ModRM changes the instruction.
        r#"
import x86_64;
import bitvec;
import list;
fn impossible(start: BitVec(64)) -> DecodedAt(
    InstructionBytes(start := start,
        bytes := Cons(@BitVec::ofNat(8, 72), Cons(@BitVec::ofNat(8, 139),
            Cons(@BitVec::ofNat(8, 216), Nil)))),
    decoded_rr(MovRR(Rax, Rbx)))
{
    And(refl, refl)
}
"#,
        // A three-byte shape without REX.W is not a 64-bit instruction here.
        r#"
import x86_64;
import bitvec;
import list;
fn impossible(start: BitVec(64)) -> DecodedAt(
    InstructionBytes(start := start,
        bytes := Cons(@BitVec::ofNat(8, 64), Cons(@BitVec::ofNat(8, 137),
            Cons(@BitVec::ofNat(8, 216), Nil)))),
    decoded_rr(MovRR(Rax, Rbx)))
{
    And(Inl(And(refl, And(refl, refl))), refl)
}
"#,
        // ModRM.mod = 00 is a memory form, not register-register coverage.
        r#"
import x86_64;
import bitvec;
import list;
fn impossible(start: BitVec(64)) -> DecodedAt(
    InstructionBytes(start := start,
        bytes := Cons(@BitVec::ofNat(8, 72), Cons(@BitVec::ofNat(8, 137),
            Cons(@BitVec::ofNat(8, 24), Nil)))),
    decoded_rr(MovRR(Rax, Rbx)))
{
    And(Inl(And(refl, And(refl, refl))), refl)
}
"#,
        // Correct bytes cannot certify a decoded object with the wrong length.
        r#"
import x86_64;
import bitvec;
import list;
fn impossible(start: BitVec(64)) -> DecodedAt(
    InstructionBytes(start := start,
        bytes := Cons(@BitVec::ofNat(8, 72), Cons(@BitVec::ofNat(8, 137),
            Cons(@BitVec::ofNat(8, 216), Nil)))),
    DecodedInstruction(instruction := MovRR(Rax, Rbx), length := 2,
        valid_length := squash(And(trivial, trivial))))
{
    And(refl, refl)
}
"#,
    ];

    for src in cases {
        let mut e = base.clone();
        assert!(
            e.elab_module_source("bad_bytes", src).is_err(),
            "an unsupported or malformed byte span was accepted:\n{src}"
        );
    }
}


fn fetched_instruction_boundary_checks(base: &Elaborator) {
    let mut e = base.clone();
    let library = include_str!("../../../lib/std/arch/x86_64/x86_64_fetch.hthr");
    if let Err(err) = e.elab_module_source("x86_64_fetch", library) {
        panic!("fetch library: {}", err.render(library));
    }
    let source = r#"
import x86_64;
import x86_64_fetch;
import bitvec;
import bool;
import list;
import nat;
import option;
import logic;
import relation;
fn test_read(bytes: List<BitVec(8)>, address: BitVec(64)) -> Option<BitVec(8)> {
    bytes.nth(@bitvec::BitVec::toNat(64, address))
}
fn test_access() -> FetchAccess<List<BitVec(8)>> {
    FetchAccess(test_read, λ memory address => True)
}
fn bytes() -> List<BitVec(8)> { canonical_bytes(MovRR(Rax, Rbx)) }
fn start() -> BitVec(64) { @bitvec::BitVec::ofNat(64, 0) }
theorem read_exact(): fetch_instruction_bytes(test_access(), bytes(), 3, start())
    = FetchedBytes(bytes()) { refl }
theorem missing_tail(): fetch_instruction_bytes(test_access(), bytes(), 4, start())
    = FetchMissing(@bitvec::BitVec::ofNat(64, 3)) { refl }
theorem denied_before_read(): fetch_instruction_bytes(
    FetchAccess<List<BitVec(8)>>(test_read, λ memory address => False), Nil, 1, start())
    = FetchDenied(start()) { refl }
fn constant_access() -> FetchAccess<Nat> {
    FetchAccess(λ memory address => Some(@bitvec::BitVec::ofNat(8, 72)), λ memory address => True)
}
fn last_address() -> BitVec(64) { @bitvec::BitVec::all_ones(64) }
theorem last_byte(): fetch_instruction_bytes(constant_access(), 0, 1, last_address())
    = FetchedBytes([@bitvec::BitVec::ofNat(8, 72)]) { refl }
theorem wrap_rejected(): fetch_instruction_bytes(constant_access(), 0, 2, last_address())
    = FetchAddressWrap { refl }
theorem neutral_byte<M>(memory: M, address: BitVec(64), byte: BitVec(8)):
    fetch_instruction_bytes(FetchAccess<M>(λ m a => Some(byte), λ m a => True),
        memory, 1, address) = FetchedBytes([byte]) { refl }
theorem neutral_certificate<M>(memory: M, address: BitVec(64), byte: BitVec(8)):
    FetchedFrom(FetchAccess<M>(λ m a => Some(byte), λ m a => True), memory,
        InstructionBytes(address, [byte]))
{ fetch_span_one(FetchAccess<M>(λ m a => Some(byte), λ m a => True), memory, address, byte, refl, refl) }
theorem certificate_agrees<M>(memory: M, address: BitVec(64), byte: BitVec(8)):
    fetch_instruction_bytes(FetchAccess<M>(λ m a => Some(byte), λ m a => True), memory, 1, address)
        = FetchedBytes([byte])
{ fetched_result(FetchAccess<M>(λ m a => Some(byte), λ m a => True), memory,
    InstructionBytes(address, [byte]), neutral_certificate(memory, address, byte)) }
theorem unsupported_bytes_still_fetch(): fetch_instruction_bytes(
    test_access(), [@bitvec::BitVec::ofNat(8, 0)], 1, start())
    = FetchedBytes([@bitvec::BitVec::ofNat(8, 0)]) { refl }
theorem unsupported_decode(): decode_instruction([@bitvec::BitVec::ofNat(8, 0)]) = None { refl }
theorem no_read_for_empty(): fetch_instruction_bytes(test_access(), Nil, 0, start())
    = FetchedBytes(Nil) { refl }
fn before() -> MachineState<List<BitVec(8)>> {
    MachineState(zero_gprs(), clear_flags(), start(), bytes())
}
theorem fetched_executes(): ExecuteFetched(test_access(),
    encoded_at(start(), MovRR(Rax, Rbx)), decoded_canonical(MovRR(Rax, Rbx)),
    before(), Returned(execute_normal(decoded_canonical(MovRR(Rax, Rbx)), before())))
{ ⟨FetchedFrom(⟨refl, ⟨refl, ⟨refl, ⟨refl, ⟨refl, ⟨refl, ⟨refl, ⟨refl, trivial⟩⟩⟩⟩⟩⟩⟩⟩), canonical_encoding_executes(MovRR(Rax, Rbx), before())⟩ }
"#;
    if let Err(err) = e.elab_module_source("fetch_checks", source) {
        panic!("fetch checks: {}", err.render(source));
    }
    for (name, claim) in [
        ("wrong_byte", "FetchedFrom(test_access(), [@bitvec::BitVec::ofNat(8, 0)], InstructionBytes(start(), [@bitvec::BitVec::ofNat(8, 72)]))"),
        ("wrong_address", "FetchedFrom(test_access(), bytes(), InstructionBytes(@bitvec::BitVec::ofNat(64, 1), bytes()))"),
        ("non_executable", "FetchedFrom(FetchAccess<List<BitVec(8)>>(test_read, λ memory address => False), bytes(), InstructionBytes(start(), bytes()))"),
    ] {
        let count = if name == "wrong_byte" { 1 } else { 3 };
        let mut witness = "⟨refl, ⟨refl, trivial⟩⟩".to_string();
        for _ in 1..count { witness = format!("⟨refl, ⟨refl, ⟨refl, {witness}⟩⟩⟩"); }
        let bad = format!("import fetch_checks;\nimport x86_64_fetch;\nimport x86_64;\nimport bitvec;\nimport list;\nimport bool;\ntheorem bad(): {claim} {{ FetchedFrom({witness}) }}");
        let error = e.clone().elab_module_source(name, &bad).expect_err("accepted invalid fetch");
        let rendered = error.render(&bad);
        assert!(!rendered.contains("unbound") && !rendered.contains("parse error"),
            "{name} failed before checking its proof: {rendered}");
    }
}
