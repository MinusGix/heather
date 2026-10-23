//! `lib/std/machine/memory.hthr` — byte-addressed memory with explicit access
//! outcomes (`issues/byte-memory-access-model.md`,
//! `docs/byte-memory-design.md`), with `lib/std/data/vector.hthr` and the byte
//! packing in `lib/std/bitvec/bitvec_bytes.hthr`.
//!
//!  1. the closure checks: the modules and the showcase client, which runs a
//!     16-byte memory by evaluation (wrapping, self-overlap, refused spans)
//!     and proves adjacent-word and buffer facts for every memory;
//!  2. the model's choices hold at a literal memory *and* at an open one:
//!     a refused span stores nothing at any refusal position, and the
//!     endianness is the packing's, not memory's;
//!  3. negative controls: a self-overlapping span does not read back, a
//!     refused write has no `Ok`, the two packings differ, and the
//!     read-back theorem is refused without its `Distinct` premise.

use std::sync::OnceLock;

use heather_elab::{Elaborator, SemanticImage};

use crate::support;

const MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/core/logic.hthr")),
    ("bool", include_str!("../../../lib/std/core/bool.hthr")),
    ("nat", include_str!("../../../lib/std/num/nat.hthr")),
    ("option", include_str!("../../../lib/std/core/option.hthr")),
    ("pair", include_str!("../../../lib/std/core/pair.hthr")),
    ("list", include_str!("../../../lib/std/data/list.hthr")),
    ("algebra", include_str!("../../../lib/std/algebra/algebra.hthr")),
    ("int", include_str!("../../../lib/std/num/int.hthr")),
    ("omega", include_str!("../../../lib/std/tactic/omega.hthr")),
    ("result", include_str!("../../../lib/std/core/result.hthr")),
    ("bitvec", include_str!("../../../lib/std/bitvec/bitvec.hthr")),
    (
        "bitvec_nat",
        include_str!("../../../lib/std/bitvec/bitvec_nat.hthr"),
    ),
    ("vector", include_str!("../../../lib/std/data/vector.hthr")),
    (
        "bitvec_bytes",
        include_str!("../../../lib/std/bitvec/bitvec_bytes.hthr"),
    ),
    ("memory", include_str!("../../../lib/std/machine/memory.hthr")),
];

static BASE: OnceLock<SemanticImage> = OnceLock::new();

fn base() -> Elaborator {
    BASE.get_or_init(|| support::semantic_test_base(MODULES).semantic_image()).elaborator()
}

fn check(e: &mut Elaborator, name: &str, src: &str) {
    if let Err(err) = e.elab_module_source(name, src) {
        panic!("{}", err.render(src));
    }
}

/// Refused, with `needle` in the rendered error, so a control fails for the
/// reason it names rather than an unrelated one.
fn refused(name: &str, src: &str, needle: &str) {
    let mut e = base();
    match e.elab_module_source(name, src) {
        Ok(()) => panic!("{name} should be refused"),
        Err(err) => {
            let message = err.render(src);
            assert!(message.contains(needle), "{name}: {message}");
        }
    }
}

const IMPORTS: &str = "import logic; import algebra; import nat; import omega; import option; import result;
    import bitvec; import bitvec_bytes; import vector; import memory;\n";

// A four-byte memory over 2-bit addresses: address 2 refuses writes.
const SMALL: &str = "
fn perms4(a: BitVec(2)) → Perm { match a.eq_bit(2) { True => Perm(True, False, False), False => Perm::data() } }
fn zeros4() → Memory<BitVec(2), BitVec(8)> {
    Memory<BitVec(2), BitVec(8)>(BitVec::space(2), λ (a: BitVec(2)) => BitVec::zero(), perms4)
}
fn byte(n: Nat) → BitVec(8) { BitVec::ofNat(n) }
";

#[test]
fn the_modules_and_their_client_check() {
    let mut e = base();
    check(
        &mut e,
        "memory_client",
        include_str!("../../../docs/showcase/memory_client.hthr"),
    );
}

#[test]
fn a_refused_span_stores_nothing_wherever_the_refusal_falls() {
    let mut e = base();
    let src = format!(
        "{IMPORTS}{SMALL}
        // The refusal at the first, middle and last index of a span.
        theorem refused_first(): zeros4().write_span(2, [byte(1), byte(2)]) = Err(WriteFault(BitVec::ofNat(2))) {{ refl }}
        theorem refused_middle(): zeros4().write_span(1, [byte(1), byte(2), byte(3)]) = Err(WriteFault(BitVec::ofNat(2))) {{ refl }}
        theorem refused_last(): zeros4().write_span(0, [byte(1), byte(2), byte(3)]) = Err(WriteFault(BitVec::ofNat(2))) {{ refl }}
        // The same span wrapping past 3 refuses at 2, its third address.
        theorem refused_after_wrap(): zeros4().write_span(0, [byte(1), byte(2), byte(3), byte(4)]) = Err(WriteFault(BitVec::ofNat(2))) {{ refl }}
        // At an open memory: a refusal is exactly an `Err` carrying the first
        // refused address, and that address is in the span with its bit clear.
        theorem open_refusal<A, C>(m: Memory<A, C>, a: A, cs: [C; 3], x: A,
            r: m.refused(Perm::writes, a, 3) = Some(x)): m.write_span(a, cs) = Err(WriteFault(x)) {{
            m.write_span_refused(a, cs, x, r)
        }}
        theorem open_refusal_exact<A, C>(m: Memory<A, C>, a: A, x: A,
            r: m.refused(Perm::writes, a, 3) = Some(x)): Perm::writes(m.perms(x)) = False {{
            m.refused_some(Perm::writes, a, 3, x, r).clear
        }}
        // A read-only address reads.
        theorem read_only_reads(): zeros4().read_span(1, 2) = Ok([byte(0), byte(0)]) {{ refl }}\n"
    );
    check(&mut e, "memory_refusals", &src);
}

#[test]
fn endianness_is_the_packing_at_open_words() {
    let mut e = base();
    let src = format!(
        "{IMPORTS}
        theorem le_round_trip(w: BitVec(32)): BitVec::of_bytes_le(w.bytes_le(4)) = w {{ BitVec::of_bytes_le_bytes_le(4, w) }}
        theorem be_round_trip(bytes: [BitVec(8); 8]): BitVec::of_bytes_be(bytes).bytes_be(8) = bytes {{ BitVec::bytes_be_of_bytes_be(8, bytes) }}
        theorem be_is_reversed_le(bytes: [BitVec(8); 2]): BitVec::of_bytes_be(bytes) = BitVec::of_bytes_le(reverse(bytes)) {{ refl }}
        // The open read-back, at a buffer of any capacity.
        theorem open_buffer<C>(cap: Nat, cells: Nat → C, i: Nat, cs: [C; 3], fits: i + 3 <= cap):
            Memory<Nat, C>(Nat::space(), cells, Perm::below(cap)).write_span(i, cs) =
                Ok(Memory<Nat, C>(Nat::space(), cells, Perm::below(cap)).set_span(i, cs)) {{
            Memory<Nat, C>(Nat::space(), cells, Perm::below(cap)).write_span_allowed(i, cs, Memory::buffer_writes(cap, cells, i, 3, fits))
        }}\n"
    );
    check(&mut e, "memory_packing", &src);
}

#[test]
fn a_self_overlapping_span_does_not_read_back() {
    // Five bytes in a four-byte space: index 4 lands on index 0.
    refused(
        "memory_overlap_reads_back",
        &format!(
            "{IMPORTS}{SMALL}
            theorem wrong(): zeros4().set_span(0, [byte(1), byte(2), byte(3), byte(4), byte(5)]).get_span(0, 5) =
                [byte(1), byte(2), byte(3), byte(4), byte(5)] {{ refl }}\n"
        ),
        "NotConvertible",
    );
    let mut e = base();
    let src = format!(
        "{IMPORTS}{SMALL}
        theorem right(): zeros4().set_span(0, [byte(1), byte(2), byte(3), byte(4), byte(5)]).get_span(0, 5) =
            [byte(5), byte(2), byte(3), byte(4), byte(5)] {{ refl }}\n"
    );
    check(&mut e, "memory_overlap_later_wins", &src);
}

#[test]
fn a_refused_write_has_no_ok() {
    refused(
        "memory_refused_ok",
        &format!(
            "{IMPORTS}{SMALL}
            theorem wrong(): zeros4().write_span(1, [byte(1), byte(2)]) =
                Ok(zeros4().set_span(1, [byte(1), byte(2)])) {{ refl }}\n"
        ),
        "NotConvertible",
    );
}

#[test]
fn the_two_packings_differ() {
    refused(
        "memory_le_is_be",
        &format!(
            "{IMPORTS}{SMALL}
            theorem wrong(): BitVec::of_bytes_le([byte(1), byte(2)]) = BitVec::of_bytes_be([byte(1), byte(2)]) {{ refl }}\n"
        ),
        "NotConvertible",
    );
}

#[test]
fn read_back_needs_its_distinct_premise() {
    refused(
        "memory_read_back_unpremised",
        &format!(
            "{IMPORTS}
            theorem wrong<A, C>(m: Memory<A, C>, laws: SpaceLaws<A>(m.space), a: A, cs: [C; 2]):
                m.set_span(a, cs).get_span(a, 2) = cs {{ m.get_set_span(laws, a, cs) }}\n"
        ),
        "too few arguments",
    );
}
