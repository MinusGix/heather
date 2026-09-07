//! First x86-64 vertical slice: decoded register MOV/ADD/SUB/CMP/TEST, flags, opaque
//! memory preservation, and length-derived RIP fallthrough.

mod support;

use heather_elab::{ElabError, Elaborator, stats};
use std::time::Instant;

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/list.hthr");
const ALGEBRA: &str = include_str!("../../../lib/std/algebra.hthr");
const INT: &str = include_str!("../../../lib/std/int.hthr");
const BITVEC: &str = include_str!("../../../lib/std/bitvec.hthr");
const RELATION: &str = include_str!("../../../lib/std/relation.hthr");
const LOCATION: &str = include_str!("../../../lib/std/location.hthr");
const CERTIFIED_LOOKUP: &str = include_str!("../../../lib/std/certified_lookup.hthr");
const X86_64: &str = include_str!("../../../lib/std/arch/x86_64/model.hthr");

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
    ("location", LOCATION),
    ("certified_lookup", CERTIFIED_LOOKUP),
    ("x86_64", X86_64),
];

fn elaborated() -> Elaborator {
    let report_metrics = std::env::var_os("HEATHER_VALUE_METRICS").is_some();
    let report_phases = std::env::var_os("HEATHER_X86_PHASES").is_some();
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
    if report_phases {
        stats::reset_kernel_ns();
    }
    let started = Instant::now();
    if let Err(err) = e.elab_module_source("x86_64", X86_64) {
        panic!("x86_64 did not check: {}", err.render(X86_64));
    }
    if report_phases {
        let total_ns = started.elapsed().as_nanos() as u64;
        let kernel_ns = stats::kernel_ns();
        eprintln!(
            "x86_64 phases: total={:.3}s kernel={:.3}s frontend={:.3}s",
            total_ns as f64 / 1e9,
            kernel_ns as f64 / 1e9,
            total_ns.saturating_sub(kernel_ns) as f64 / 1e9,
        );
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

fn setcc_encoding_decoding_and_execution_check(base: &Elaborator) {
    let mut e = base.clone();
    let src = r#"
import x86_64;
import bitvec;
import list;
import logic;
import option;

theorem canonical_setcc_bytes():
    canonical_bytes(SetBelow(Al)) =
        [bitvec::ofNat(8, 15), bitvec::ofNat(8, 146), bitvec::ofNat(8, 192)]
    ∧ canonical_bytes(SetLess(Bl)) =
        [bitvec::ofNat(8, 15), bitvec::ofNat(8, 156), bitvec::ofNat(8, 195)]
{
    And(refl, refl)
}

theorem canonical_setcc_decodes():
    decode_instruction(canonical_bytes(SetBelow(Al))) =
        Some(decoded_canonical(SetBelow(Al)))
    ∧ decode_instruction(canonical_bytes(SetLess(Bl))) =
        Some(decoded_canonical(SetLess(Bl)))
{
    And(refl, refl)
}

theorem malformed_setcc_is_rejected():
    decode_instruction(
        [bitvec::ofNat(8, 15), bitvec::ofNat(8, 146)]) = None
    ∧ decode_instruction(
        [bitvec::ofNat(8, 14), bitvec::ofNat(8, 146), bitvec::ofNat(8, 192)]) = None
    ∧ decode_instruction(
        [bitvec::ofNat(8, 15), bitvec::ofNat(8, 146), bitvec::ofNat(8, 196)]) = None
    ∧ decode_instruction(
        [bitvec::ofNat(8, 15), bitvec::ofNat(8, 146), bitvec::ofNat(8, 192),
            bitvec::ofNat(8, 0)]) = None
{
    And(refl, And(refl, And(refl, refl)))
}

theorem cmp_flags_are_function_ir_conditions(left, right: BitVec(64)):
    sub_flags(left, right).cf = bitvec::unsigned_lt_bit(64, left, right)
    ∧ bitvec::xor_bit(sub_flags(left, right).sf, sub_flags(left, right).of) =
        bitvec::signed_lt_bit(64, left, right)
{
    And(refl, refl)
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

theorem register_indices(): gpr_index(Rax) = 0 ∧ gpr_index(R15) = 15
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
        Cons(ofNat(8, 72), Cons(ofNat(8, 137), Cons(ofNat(8, 216), Nil)))
{
    refl
}

theorem canonical_extended_register_bytes():
    canonical_bytes(AddRR(R9, R10)) =
        Cons(ofNat(8, 77), Cons(ofNat(8, 1), Cons(ofNat(8, 209), Nil)))
{
    refl
}

theorem canonical_sub_and_cmp_bytes():
    canonical_bytes(SubRR(R9, R10)) =
        Cons(ofNat(8, 77), Cons(ofNat(8, 41), Cons(ofNat(8, 209), Nil)))
    ∧ canonical_bytes(CmpRR(Rax, Rbx)) =
        Cons(ofNat(8, 72), Cons(ofNat(8, 57), Cons(ofNat(8, 216), Nil)))
{
    And(refl, refl)
}

theorem canonical_logic_bytes():
    canonical_bytes(AndRR(R9, R10)) =
        Cons(ofNat(8, 77), Cons(ofNat(8, 33), Cons(ofNat(8, 209), Nil)))
    ∧ canonical_bytes(OrRR(Rax, Rbx)) =
        Cons(ofNat(8, 72), Cons(ofNat(8, 9), Cons(ofNat(8, 216), Nil)))
    ∧ canonical_bytes(XorRR(R15, Rax)) =
        Cons(ofNat(8, 73), Cons(ofNat(8, 49), Cons(ofNat(8, 199), Nil)))
{
    And(refl, And(refl, refl))
}

theorem canonical_test_extension_bytes():
    canonical_bytes(TestRR(R15, Rax)) =
        Cons(ofNat(8, 73), Cons(ofNat(8, 133), Cons(ofNat(8, 199), Nil)))
{
    refl
}

theorem mov_direction_encodings_normalize(start: BitVec(64)):
    DecodedAt(encoded_at(start, MovRR(Rax, Rbx)),
        decoded_rr(MovRR(Rax, Rbx)))
    ∧ DecodedAt(
        InstructionBytes(start := start,
            bytes := Cons(ofNat(8, 72), Cons(ofNat(8, 139),
                Cons(ofNat(8, 195), Nil)))),
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
            bytes := Cons(ofNat(8, 77), Cons(ofNat(8, 3),
                Cons(ofNat(8, 202), Nil)))),
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
        bitvec::sub(64, read_gpr(destination, before),
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
    decode_instruction(Cons(ofNat(8, 72), Cons(ofNat(8, 137), Nil))) = None
    ∧ decode_instruction(rr_bytes(144, Rax, Rbx)) = None
{
    And(refl, refl)
}

theorem executable_decoder_rejects_missing_rex_w_and_memory_modrm():
    decode_instruction(Cons(ofNat(8, 64), Cons(ofNat(8, 137),
        Cons(ofNat(8, 216), Nil)))) = None
    ∧ decode_instruction(Cons(ofNat(8, 72), Cons(ofNat(8, 137),
        Cons(ofNat(8, 24), Nil)))) = None
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
            bytes := Cons(ofNat(8, 72), Cons(ofNat(8, 137),
                Cons(ofNat(8, 216), Nil)))),
        decoded_rr(MovRR(Rax, Rbx)), before,
        Returned(execute_normal(decoded_rr(MovRR(Rax, Rbx)), before)))
{
    external_decoding_executes(
        InstructionBytes(start := before.rip,
            bytes := Cons(ofNat(8, 72), Cons(ofNat(8, 137),
                Cons(ofNat(8, 216), Nil)))),
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
    canonical_bytes(MovRI(Rax, zero(64))) =
        [ofNat(8, 72), ofNat(8, 184),
         zero(8), zero(8), zero(8), zero(8),
         zero(8), zero(8), zero(8), zero(8)]
{ refl }

theorem mov_ri_extended_ones_bytes():
    canonical_bytes(MovRI(R15, all_ones(64))) =
        [ofNat(8, 73), ofNat(8, 191),
         all_ones(8), all_ones(8), all_ones(8), all_ones(8),
         all_ones(8), all_ones(8), all_ones(8), all_ones(8)]
{ refl }

theorem mov_ri_canonical_lengths():
    canonical_length(MovRI(Rax, zero(64))) = 10
    ∧ canonical_bytes(MovRI(R15, all_ones(64))).len() = 10
    ∧ decoded_canonical(MovRI(R8, one(64))).length = 10
{ And(refl, And(refl, refl)) }

theorem mov_ri_decoder_accepts_boundaries():
    decode_instruction(canonical_bytes(MovRI(Rax, zero(64)))) =
        Some(decoded_canonical(MovRI(Rax, zero(64))))
    ∧ decode_instruction(canonical_bytes(MovRI(R15, all_ones(64)))) =
        Some(decoded_canonical(MovRI(R15, all_ones(64))))
{
    And(decode_mov_ri_complete(Rax, zero(64)),
        decode_mov_ri_complete(R15, all_ones(64)))
}

theorem mov_ri_decoder_rejects_truncated_trailing_and_bad_head():
    decode_instruction(
        [ofNat(8, 72), ofNat(8, 184),
         zero(8), zero(8), zero(8), zero(8),
         zero(8), zero(8), zero(8)]) = None
    ∧ decode_instruction(
        [ofNat(8, 72), ofNat(8, 184),
         zero(8), zero(8), zero(8), zero(8),
         zero(8), zero(8), zero(8), zero(8), zero(8)]) = None
    ∧ decode_instruction(
        [ofNat(8, 64), ofNat(8, 184),
         zero(8), zero(8), zero(8), zero(8),
         zero(8), zero(8), zero(8), zero(8)]) = None
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
    decode_instruction_reference(Cons(ofNat(8, 64), Cons(ofNat(8, 137),
        Cons(ofNat(8, 216), Nil)))) = None
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
        bytes := Cons(ofNat(8, 72), Cons(ofNat(8, 137), Nil))),
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
        bytes := Cons(ofNat(8, 72), Cons(ofNat(8, 139),
            Cons(ofNat(8, 216), Nil)))),
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
        bytes := Cons(ofNat(8, 64), Cons(ofNat(8, 137),
            Cons(ofNat(8, 216), Nil)))),
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
        bytes := Cons(ofNat(8, 72), Cons(ofNat(8, 137),
            Cons(ofNat(8, 24), Nil)))),
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
        bytes := Cons(ofNat(8, 72), Cons(ofNat(8, 137),
            Cons(ofNat(8, 216), Nil)))),
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
    let library = include_str!("../../../lib/std/arch/x86_64/fetch.hthr");
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
    bytes.nth(bitvec::toNat(64, address))
}
fn test_access() -> FetchAccess<List<BitVec(8)>> {
    FetchAccess(test_read, λ memory address => True)
}
fn bytes() -> List<BitVec(8)> { canonical_bytes(MovRR(Rax, Rbx)) }
fn start() -> BitVec(64) { bitvec::ofNat(64, 0) }
theorem read_exact(): fetch_instruction_bytes(test_access(), bytes(), 3, start())
    = FetchedBytes(bytes()) { refl }
theorem missing_tail(): fetch_instruction_bytes(test_access(), bytes(), 4, start())
    = FetchMissing(bitvec::ofNat(64, 3)) { refl }
theorem denied_before_read(): fetch_instruction_bytes(
    FetchAccess<List<BitVec(8)>>(test_read, λ memory address => False), Nil, 1, start())
    = FetchDenied(start()) { refl }
fn constant_access() -> FetchAccess<Nat> {
    FetchAccess(λ memory address => Some(bitvec::ofNat(8, 72)), λ memory address => True)
}
fn last_address() -> BitVec(64) { bitvec::all_ones(64) }
theorem last_byte(): fetch_instruction_bytes(constant_access(), 0, 1, last_address())
    = FetchedBytes([bitvec::ofNat(8, 72)]) { refl }
theorem wrap_rejected(): fetch_instruction_bytes(constant_access(), 0, 2, last_address())
    = FetchAddressWrap { refl }
theorem neutral_byte<M>(memory: M, address: BitVec(64), byte: BitVec(8)):
    fetch_instruction_bytes(FetchAccess<M>(λ m a => Some(byte), λ m a => True),
        memory, 1, address) = FetchedBytes([byte]) { refl }
theorem unsupported_bytes_still_fetch(): fetch_instruction_bytes(
    test_access(), [bitvec::ofNat(8, 0)], 1, start())
    = FetchedBytes([bitvec::ofNat(8, 0)]) { refl }
theorem unsupported_decode(): decode_instruction([bitvec::ofNat(8, 0)]) = None { refl }
theorem no_read_for_empty(): fetch_instruction_bytes(test_access(), Nil, 0, start())
    = FetchedBytes(Nil) { refl }
fn before() -> MachineState<List<BitVec(8)>> {
    MachineState(zero_gprs(), clear_flags(), start(), bytes())
}
theorem fetched_executes(): ExecuteFetched(test_access(),
    encoded_at(start(), MovRR(Rax, Rbx)), decoded_canonical(MovRR(Rax, Rbx)),
    before(), Returned(execute_normal(decoded_canonical(MovRR(Rax, Rbx)), before())))
{ ⟨refl, canonical_encoding_executes(MovRR(Rax, Rbx), before())⟩ }
"#;
    if let Err(err) = e.elab_module_source("fetch_checks", source) {
        panic!("fetch checks: {}", err.render(source));
    }
    for (name, claim) in [
        ("wrong_byte", "FetchedFrom(test_access(), [bitvec::ofNat(8, 0)], InstructionBytes(start(), [bitvec::ofNat(8, 72)]))"),
        ("wrong_address", "FetchedFrom(test_access(), bytes(), InstructionBytes(bitvec::ofNat(64, 1), bytes()))"),
        ("non_executable", "FetchedFrom(FetchAccess<List<BitVec(8)>>(test_read, λ memory address => False), bytes(), InstructionBytes(start(), bytes()))"),
    ] {
        let bad = format!("import fetch_checks;\nimport x86_64_fetch;\nimport x86_64;\nimport bitvec;\nimport list;\nimport bool;\ntheorem bad(): {claim} {{ refl }}");
        let error = e.clone().elab_module_source(name, &bad).expect_err("accepted invalid fetch");
        let rendered = error.render(&bad);
        assert!(!rendered.contains("unbound") && !rendered.contains("parse error"),
            "{name} failed before checking its proof: {rendered}");
    }
}
