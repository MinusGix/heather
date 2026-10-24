//! The call control of the Wp stack items (`issues/wp-stack-items.md`): a
//! program that calls a function which spills a register to a frame slot,
//! reloads it into another and returns, proved through `Wp`, the function
//! against its contract and the program with that contract at its CALL; and
//! mutants of its program, the proof unchanged, refused: a reload from the
//! wrong slot, and an exit with the wrong status.

use crate::linux_wp::{assert_refused, MODULES};
use crate::read_loop_fixture::checker_with;

const CALL: &str = include_str!("fixtures/linux_wp_call.hthr");

/// The control with `from` replaced by `to` in its program, refused where
/// the unchanged proof no longer proves it.
fn mutant_refused(name: &str, from: &str, to: &str) {
    assert_eq!(CALL.matches(from).count(), 1, "{name}: `{from}` must name one place in the program");
    let mutant = CALL.replace(from, to);
    let mut e = checker_with(MODULES);
    match e.elab_module_source(name, &mutant) {
        Ok(()) => panic!("{name} should be refused"),
        Err(err) => assert_refused(name, &err.render(&mutant)),
    }
}

#[test]
fn the_call_spills_reloads_and_returns() {
    let mut e = checker_with(MODULES);
    if let Err(err) = e.elab_module_source("linux_wp_call", CALL) {
        panic!("{}", err.render(CALL));
    }
}

// The function reloads slot 2, where it spilled slot 1.
#[test]
fn a_reload_from_the_wrong_slot_is_refused() {
    mutant_refused("linux_wp_call_slot", "Reload(StackLoad(Rdi, slot_offset(1)))", "Reload(StackLoad(Rdi, slot_offset(2)))");
}

// What comes back is 1 where the spec exits 0.
#[test]
fn an_exit_with_the_wrong_status_is_refused() {
    mutant_refused("linux_wp_call_status", "MovRI(Rbx, BitVec::ofNat(0))", "MovRI(Rbx, BitVec::ofNat(1))");
}
