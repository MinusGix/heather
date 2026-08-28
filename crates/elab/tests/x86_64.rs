//! First x86-64 vertical slice: decoded register MOV/ADD/SUB/CMP/TEST, flags, opaque
//! memory preservation, and length-derived RIP fallthrough.

use heather_elab::{stats, ElabError, Elaborator};
use std::sync::Mutex;
use std::time::Instant;

static ELAB_LOCK: Mutex<()> = Mutex::new(());

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

fn elaborated() -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    for (name, src) in [
        ("logic", LOGIC), ("bool", BOOL), ("nat", NAT), ("option", OPTION),
        ("pair", PAIR), ("list", LIST), ("algebra", ALGEBRA), ("int", INT),
        ("bitvec", BITVEC), ("relation", RELATION), ("location", LOCATION),
        ("certified_lookup", CERTIFIED_LOOKUP),
    ] {
        if let Err(err) = e.elab_module_source(name, src) {
            panic!("{name} did not check: {}", err.render(src));
        }
    }
    let report_metrics = std::env::var_os("HEATHER_VALUE_METRICS").is_some();
    if report_metrics {
        e.enable_value_metrics();
    }
    let report_phases = std::env::var_os("HEATHER_X86_PHASES").is_some();
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
        eprintln!("x86_64 module value metrics: {:?}", e.value_metrics().unwrap());
    }
    e
}

#[test]
fn the_x86_64_module_checks() {
    let _guard = ELAB_LOCK.lock().unwrap_or_else(|p| p.into_inner());
    elaborated();
}

#[test]
fn register_and_execution_laws_check() {
    let _guard = ELAB_LOCK.lock().unwrap_or_else(|p| p.into_inner());
    let mut e = elaborated();
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
    ExecuteAt(encoded_at(before.rip, instruction), decoded_rr(instruction), before,
        Returned(execute_normal(decoded_rr(instruction), before)))
{
    canonical_encoding_executes(instruction, before)
}

theorem decoded_length_drives_fallthrough<M>(span: InstructionBytes,
    decoded: DecodedInstruction, before: MachineState<M>,
    decoding: DecodedAt(span, decoded)):
    execute_normal(decoded, before).rip = next_rip(before.rip, 3)
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
    decode_instruction(bytes) = Some(decoded_rr(instruction))
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
        decoded_rr(result.instruction), before,
        Returned(execute_normal(decoded_rr(result.instruction), before)))
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

#[test]
fn direct_decoder_agrees_with_reference_on_boundary_cases() {
    let _guard = ELAB_LOCK.lock().unwrap_or_else(|p| p.into_inner());
    let mut e = elaborated();
    let src = r#"
import x86_64;
import bitvec;
import list;
import logic;

theorem supported_opcodes_agree():
    decode_instruction(canonical_bytes(MovRR(Rax, Rbx))) =
        decode_instruction_reference(canonical_bytes(MovRR(Rax, Rbx)))
    ∧ decode_instruction(alternate_mov_bytes(Rax, Rbx)) =
        decode_instruction_reference(alternate_mov_bytes(Rax, Rbx))
    ∧ decode_instruction(canonical_bytes(AddRR(Rax, Rcx))) =
        decode_instruction_reference(canonical_bytes(AddRR(Rax, Rcx)))
    ∧ decode_instruction(alternate_add_bytes(Rax, Rcx)) =
        decode_instruction_reference(alternate_add_bytes(Rax, Rcx))
    ∧ decode_instruction(canonical_bytes(TestRR(Rax, Rbx))) =
        decode_instruction_reference(canonical_bytes(TestRR(Rax, Rbx)))
{
    And(refl, And(refl, And(refl, And(refl, refl))))
}

theorem rex_extension_combinations_agree():
    decode_instruction(canonical_bytes(MovRR(Rax, Rbx))) =
        decode_instruction_reference(canonical_bytes(MovRR(Rax, Rbx)))
    ∧ decode_instruction(canonical_bytes(MovRR(R8, Rbx))) =
        decode_instruction_reference(canonical_bytes(MovRR(R8, Rbx)))
    ∧ decode_instruction(canonical_bytes(MovRR(Rax, R8))) =
        decode_instruction_reference(canonical_bytes(MovRR(Rax, R8)))
    ∧ decode_instruction(canonical_bytes(MovRR(R8, R9))) =
        decode_instruction_reference(canonical_bytes(MovRR(R8, R9)))
{
    And(refl, And(refl, And(refl, refl)))
}

theorem sub_and_cmp_opcodes_agree():
    decode_instruction(canonical_bytes(SubRR(Rax, Rbx))) =
        decode_instruction_reference(canonical_bytes(SubRR(Rax, Rbx)))
    ∧ decode_instruction(alternate_sub_bytes(Rax, Rbx)) =
        decode_instruction_reference(alternate_sub_bytes(Rax, Rbx))
    ∧ decode_instruction(canonical_bytes(CmpRR(Rax, Rbx))) =
        decode_instruction_reference(canonical_bytes(CmpRR(Rax, Rbx)))
    ∧ decode_instruction(alternate_cmp_bytes(Rax, Rbx)) =
        decode_instruction_reference(alternate_cmp_bytes(Rax, Rbx))
{
    And(refl, And(refl, And(refl, refl)))
}

theorem malformed_inputs_agree():
    decode_instruction(Cons(ofNat(8, 64), Cons(ofNat(8, 137),
        Cons(ofNat(8, 216), Nil)))) =
        decode_instruction_reference(Cons(ofNat(8, 64), Cons(ofNat(8, 137),
            Cons(ofNat(8, 216), Nil))))
    ∧ decode_instruction(Cons(ofNat(8, 72), Cons(ofNat(8, 137),
        Cons(ofNat(8, 24), Nil)))) =
        decode_instruction_reference(Cons(ofNat(8, 72), Cons(ofNat(8, 137),
            Cons(ofNat(8, 24), Nil))))
    ∧ decode_instruction(Cons(ofNat(8, 72), Cons(ofNat(8, 137), Nil))) =
        decode_instruction_reference(Cons(ofNat(8, 72),
            Cons(ofNat(8, 137), Nil)))
{
    And(refl, And(refl, refl))
}
"#;
    if let Err(err) = e.elab_module_source("decoder_agreement", src) {
        let msg = match err {
            ElabError::Elab { msg, .. } => msg,
            other => format!("{other}"),
        };
        panic!("direct/reference decoder agreement did not check: {msg}");
    }
}

#[test]
fn invalid_decoded_lengths_are_refused() {
    let _guard = ELAB_LOCK.lock().unwrap_or_else(|p| p.into_inner());
    let mut e = elaborated();
    let src = r#"
import x86_64;
fn impossible() -> DecodedInstruction {
    DecodedInstruction(instruction := MovRR(Rax, Rbx), length := 0,
        valid_length := squash(And(trivial, trivial)))
}
"#;
    assert!(e.elab_module_source("bad", src).is_err(),
        "a zero-byte x86 instruction was accepted");
}

#[test]
fn unsupported_or_malformed_byte_spans_are_refused() {
    let _guard = ELAB_LOCK.lock().unwrap_or_else(|p| p.into_inner());
    let base = elaborated();
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
        assert!(e.elab_module_source("bad_bytes", src).is_err(),
            "an unsupported or malformed byte span was accepted:\n{src}");
    }
}
