//! The pure loop control of `linux_wp.rs` (round S2,
//! `issues/native-loop-rule.md`): seven hand-written items counting a frame
//! slot down to zero and exiting 0, proved through `loop_at` with the slot as
//! its variant; and mutants of its program, the proof unchanged, refused: a
//! loop over the wrong slot, and an exit with the wrong status.

use crate::linux_wp::{assert_refused, MODULES};
use crate::read_loop_fixture::checker_with;

const COUNT: &str = include_str!("fixtures/linux_wp_count.hthr");

/// The control with `from` replaced by `to` in its program, refused where
/// the unchanged proof no longer proves it.
fn mutant_refused(name: &str, from: &str, to: &str) {
    assert_eq!(COUNT.matches(from).count(), 1, "{name}: `{from}` must name one place in the program");
    let mutant = COUNT.replace(from, to);
    let mut e = checker_with(MODULES);
    match e.elab_module_source(name, &mutant) {
        Ok(()) => panic!("{name} should be refused"),
        Err(err) => assert_refused(name, &err.render(&mutant)),
    }
}

#[test]
fn the_pure_loop_counts_down_and_exits() {
    let mut e = checker_with(MODULES);
    if let Err(err) = e.elab_module_source("linux_wp_count", COUNT) {
        panic!("{}", err.render(COUNT));
    }
}

// The loop loads and stores slot 1, where the invariant counts slot 0.
#[test]
fn a_loop_over_the_wrong_slot_is_refused() {
    mutant_refused("linux_wp_count_slot", "MovRI(Rbx, BitVec::ofNat(0x411000))", "MovRI(Rbx, BitVec::ofNat(0x411008))");
}

// The exit's status is 1 where the spec returns 0.
#[test]
fn an_exit_with_the_wrong_status_is_refused() {
    mutant_refused("linux_wp_count_status", "MovRI(Rdi, BitVec::ofNat(0))", "MovRI(Rdi, BitVec::ofNat(1))");
}
