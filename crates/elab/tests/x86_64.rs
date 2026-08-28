//! First x86-64 vertical slice: decoded register MOV/ADD/TEST, flags, opaque
//! memory preservation, and length-derived RIP fallthrough.

use heather_elab::{ElabError, Elaborator};
use std::sync::Mutex;

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
const X86_64: &str = include_str!("../../../lib/std/arch/x86_64/model.hthr");

fn elaborated() -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    for (name, src) in [
        ("logic", LOGIC), ("bool", BOOL), ("nat", NAT), ("option", OPTION),
        ("pair", PAIR), ("list", LIST), ("algebra", ALGEBRA), ("int", INT),
        ("bitvec", BITVEC), ("relation", RELATION), ("location", LOCATION),
    ] {
        if let Err(err) = e.elab_module_source(name, src) {
            panic!("{name} did not check: {}", err.render(src));
        }
    }
    let report_metrics = std::env::var_os("HEATHER_VALUE_METRICS").is_some();
    if report_metrics {
        e.enable_value_metrics();
    }
    if let Err(err) = e.elab_module_source("x86_64", X86_64) {
        panic!("x86_64 did not check: {}", err.render(X86_64));
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
