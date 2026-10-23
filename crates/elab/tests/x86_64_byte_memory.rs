//! x86_64's memory as the byte model (`issues/memory-model-machine-instances.md`,
//! `docs/byte-memory-design.md` §6): the access records over
//! `lib/std/machine/memory.hthr` (`x86_64_byte_memory`), the stack built from a data
//! region by proof, and the `LinuxIo` record and buffer view for `Wp`
//! (`linux_x86_64_byte_memory`).
//!
//!  1. the modules and a client: literal reads, stores and the canonical
//!     refusal by evaluation; the stack's laws at a literal region and at an
//!     open one; a buffer read into and loaded from through the view;
//!  2. negative controls: the kernel half does not read, an executable
//!     region is not a data region, and a store past a buffer's end has no
//!     view arm.

use crate::read_loop_fixture::checker_with;
// The one-Wp round's list carries the byte model, so both share one semantic
// test image.
use crate::linux_wp::{assert_refused, MODULES};

const EXAMPLES: &str = include_str!("fixtures/x86_64_byte_memory_examples.hthr");

fn imports() -> String {
    EXAMPLES.lines().filter(|l| l.starts_with("import")).collect::<Vec<_>>().join("\n")
}

#[test]
fn the_machine_runs_on_the_byte_model() {
    let mut e = checker_with(MODULES);
    if let Err(err) = e.elab_module_source("x86_64_byte_memory_examples", EXAMPLES) {
        panic!("{}", err.render(EXAMPLES));
    }
}

// The fixture's profile, without the rest of the fixture: a control checks
// only what it refuses.
const FLAT: &str = "fn at(n: Nat) → BitVec(64) { BitVec::ofNat(n) }
fn stack_data(perms: BitVec(64) → Perm) → Type { (i: Nat) → i < 64 → perms(next_rip(at(65536), i)) = Perm::data() }
fn profile() → X86Profile { X86Profile(stack_data) }
fn blank() → X86Memory(profile()) {
    X86Memory(cells := λ (a: BitVec(64)) => BitVec::zero(), perms := λ (a: BitVec(64)) => Perm::data(), relied := λ i _ => refl)
}";

fn refused(e: &mut heather_elab::Elaborator, name: &str, body: &str, check: impl Fn(&str, &str)) {
    let src = format!("{}\n{FLAT}\n{body}\n", imports());
    match e.elab_module_source(name, &src) {
        Ok(()) => panic!("{name} should be refused"),
        Err(err) => check(name, &err.render(&src)),
    }
}

#[test]
fn what_the_model_refuses_the_machine_does_not_get() {
    let mut e = checker_with(MODULES);
    // The first address of the kernel half reads as nothing, though the
    // profile calls it data.
    refused(&mut e, "kernel_half_reads", "theorem wrong(): profile().read(blank(), at(Nat::pow(2, 47))) = Some(BitVec::zero()) { refl }",
        assert_refused);
    // A region the profile relies on being executable is not a data region:
    // its stack could overwrite code.
    refused(&mut e, "executable_region", "fn wx(perms: BitVec(64) → Perm) → Type {
            (i: Nat) → i < 64 → perms(next_rip(at(65536), i)) = Perm(True, True, True)
        }
        fn wx_region() → DataRegion {
            DataRegion(profile := X86Profile(wx), low := at(65536), size := 64,
                canonical := Nat::leb_sound(at(65536).toNat() + 64, Nat::pow(2, 47), trivial), data := λ perms relied => relied)
        }", assert_refused);
    // A word stored into a four-byte buffer runs past its end: the view has
    // no index to put it at.
    refused(&mut e, "store_past_the_end", "theorem wrong(r: DataRegion, v: Nat → BitVec(8), w: BitVec(64), small: r.size = 4):
            r.buffer_view().Stores(v, r.low, word_bytes(w), λ _ => True) {
            {
                let eight: (word_bytes(w).len() = 8) = refl;
                Exists(0, ⟨omega(eight, small), ⟨refl, trivial⟩⟩)
            }
        }", |name, msg| assert!(msg.contains("omega") && msg.contains("stuck"), "{name}: {msg}"));
}
