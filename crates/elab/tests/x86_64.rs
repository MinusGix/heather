//! First x86-64 vertical slice: decoded register MOV/ADD, flags, opaque
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
        ("x86_64", X86_64),
    ] {
        if let Err(err) = e.elab_module_source(name, src) {
            panic!("{name} did not check: {}", err.render(src));
        }
    }
    e
}

#[test]
fn the_x86_64_module_checks() {
    let _guard = ELAB_LOCK.lock().unwrap_or_else(|p| p.into_inner());
    elaborated();
}

#[test]
fn register_names_and_indices_compute() {
    let _guard = ELAB_LOCK.lock().unwrap_or_else(|p| p.into_inner());
    let mut e = elaborated();
    let src = r#"
import x86_64;
import bitvec;
import logic;

theorem register_indices(): gpr_index(Rax) = 0 ∧ gpr_index(R15) = 15
{ And(refl, refl) }

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
