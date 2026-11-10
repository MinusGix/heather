//! The linked SHA-512 against the standard's vectors, against plain Rust a
//! function at a time, and against an independent implementation.
//!
//! The Heather side is proved: each linked function is its source function
//! (the certificate) and the source function is the specification's
//! (`lib/native/crypto/sha512_round.hthr`). What no theorem covers is the
//! seam: the assembler, the linker, `extern "sysv64"`, and the Rust around
//! the calls (`crates/linked/src/lib.rs`). These tests are that check, in
//! the shape `crates/cache/tests/sha256.rs` gives the compiler's own hash:
//! published vectors, then an oracle over every length through the padding
//! boundaries. All inputs are deterministic.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]

use heather_linked::sha512::{K, compress, digest, next, t1, t2};
use sha2::{Digest, Sha512};

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn oracle(bytes: &[u8]) -> [u8; 64] {
    let mut h = Sha512::new();
    h.update(bytes);
    h.finalize().into()
}

/// A 64-bit LCG (Knuth's MMIX constants), as `crates/cache/tests/sha256.rs`
/// uses: varied, reproducible, no clock.
struct Lcg(u64);

impl Lcg {
    fn word(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        // The low bits of an LCG are weak; fold the high half over them.
        self.0 ^ (self.0 >> 32)
    }

    fn bytes(&mut self, n: usize) -> Vec<u8> {
        (0..n).map(|_| (self.word() >> 24) as u8).collect()
    }
}

/// Words a wrong carry, a wrong shift count or a swapped argument cannot
/// all survive: the corners, single bits at both ends, and patterns whose
/// every byte differs.
const CORNERS: [u64; 10] = [
    0,
    1,
    u64::MAX,
    1 << 63,
    (1 << 63) - 1,
    0x0123_4567_89ab_cdef,
    0xfedc_ba98_7654_3210,
    0xaaaa_aaaa_aaaa_aaaa,
    0x5555_5555_5555_5555,
    0x8000_0000_0000_0001,
];

// The functions as FIPS 180-4 §4.1.3 writes them, in Rust.
fn ch(x: u64, y: u64, z: u64) -> u64 { (x & y) ^ (!x & z) }
fn maj(x: u64, y: u64, z: u64) -> u64 { (x & y) ^ (x & z) ^ (y & z) }
fn big0(x: u64) -> u64 { x.rotate_right(28) ^ x.rotate_right(34) ^ x.rotate_right(39) }
fn big1(x: u64) -> u64 { x.rotate_right(14) ^ x.rotate_right(18) ^ x.rotate_right(41) }
fn small0(x: u64) -> u64 { x.rotate_right(1) ^ x.rotate_right(8) ^ (x >> 7) }
fn small1(x: u64) -> u64 { x.rotate_right(19) ^ x.rotate_right(61) ^ (x >> 6) }

fn t1_reference(h: u64, e: u64, f: u64, g: u64, k: u64, w: u64) -> u64 {
    h.wrapping_add(big1(e)).wrapping_add(ch(e, f, g)).wrapping_add(k).wrapping_add(w)
}

fn t2_reference(a: u64, b: u64, c: u64) -> u64 {
    big0(a).wrapping_add(maj(a, b, c))
}

fn next_reference(w2: u64, w7: u64, w15: u64, w16: u64) -> u64 {
    small1(w2).wrapping_add(w7).wrapping_add(small0(w15)).wrapping_add(w16)
}

/// Each argument in turn takes every corner while the others hold distinct
/// words, so an argument read from the wrong register shows.
#[test]
fn each_word_function_agrees_at_the_corners() {
    let rest = [0x1111_1111_1111_1111u64, 0x2222_2222_2222_2222, 0x4444_4444_4444_4444,
        0x8888_8888_8888_8888, 0x0f0f_0f0f_0f0f_0f0f, 0x00ff_00ff_00ff_00ff];
    for position in 0..6 {
        for corner in CORNERS {
            let mut a = rest;
            a[position] = corner;
            assert_eq!(t1(a[0], a[1], a[2], a[3], a[4], a[5]), t1_reference(a[0], a[1], a[2], a[3], a[4], a[5]),
                "T1 with argument {position} = {corner:#x}");
            if position < 3 {
                assert_eq!(t2(a[0], a[1], a[2]), t2_reference(a[0], a[1], a[2]),
                    "T2 with argument {position} = {corner:#x}");
            }
            if position < 4 {
                assert_eq!(next(a[0], a[1], a[2], a[3]), next_reference(a[0], a[1], a[2], a[3]),
                    "the schedule word with argument {position} = {corner:#x}");
            }
        }
    }
}

#[test]
fn each_word_function_agrees_on_varied_words() {
    let mut lcg = Lcg(0x5eed);
    for case in 0..100_000 {
        let a: [u64; 6] = std::array::from_fn(|_| lcg.word());
        assert_eq!(t1(a[0], a[1], a[2], a[3], a[4], a[5]), t1_reference(a[0], a[1], a[2], a[3], a[4], a[5]), "T1, case {case}: {a:x?}");
        assert_eq!(t2(a[0], a[1], a[2]), t2_reference(a[0], a[1], a[2]), "T2, case {case}: {a:x?}");
        assert_eq!(next(a[0], a[1], a[2], a[3]), next_reference(a[0], a[1], a[2], a[3]), "schedule word, case {case}: {a:x?}");
    }
}

/// A call must leave its caller's registers as the System V contract says:
/// the certificate proves the callee-saved ones are kept, and this holds
/// live values across many calls so a clobber the compiler relied on shows
/// as a wrong sum.
#[test]
fn calls_keep_their_callers_values() {
    let mut lcg = Lcg(7);
    let (mut x, mut y, mut z) = (lcg.word(), lcg.word(), lcg.word());
    let (x0, y0, z0) = (x, y, z);
    let mut folded = 0u64;
    for round in 0..10_000u64 {
        folded = folded.wrapping_add(t1(x, y, z, round, folded, x ^ y))
            .wrapping_add(t2(y, z, x))
            .wrapping_add(next(z, x, y, round));
        (x, y, z) = (y.rotate_left(1), z.rotate_left(3), x.rotate_left(5));
    }
    let (mut x, mut y, mut z) = (x0, y0, z0);
    let mut expected = 0u64;
    for round in 0..10_000u64 {
        expected = expected.wrapping_add(t1_reference(x, y, z, round, expected, x ^ y))
            .wrapping_add(t2_reference(y, z, x))
            .wrapping_add(next_reference(z, x, y, round));
        (x, y, z) = (y.rotate_left(1), z.rotate_left(3), x.rotate_left(5));
    }
    assert_eq!(folded, expected);
}

/// FIPS 180-4's examples and NIST CAVS: the empty string, "abc" (the vector
/// `lib/_tests/std/crypto/sha2_tests.hthr` proves of the specification) and
/// the two-block message.
#[test]
fn nist_vectors() {
    let cases: &[(&str, &str)] = &[
        ("", "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"),
        ("abc", "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"),
        (
            "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu",
            "8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909",
        ),
    ];
    for (message, want) in cases {
        assert_eq!(hex(&digest(message.as_bytes())), *want, "SHA-512({message:?})");
    }
}

/// A million `a`s, the long-message vector: 7,813 blocks.
#[test]
fn the_million_a_vector() {
    assert_eq!(hex(&digest(&vec![b'a'; 1_000_000])),
        "e718483d0ce769644e2e42c7bc15b4638e1f98b13b2044285632a803afa973ebde0ff244877ea60a4cb0432ce577c31beb009c5c2c49aa2e4eadb217ad8cc09b");
}

/// Every length from empty through three blocks: each padding shape (the
/// length field fitting the last block, and not) at every offset.
#[test]
fn differential_every_length_through_three_blocks() {
    let mut lcg = Lcg(1);
    for length in 0..=3 * 128 + 1 {
        let message = lcg.bytes(length);
        assert_eq!(hex(&digest(&message)), hex(&oracle(&message)), "length {length}");
    }
}

#[test]
fn differential_long_messages() {
    let mut lcg = Lcg(2);
    for case in 0..64 {
        let length = (lcg.word() % 20_000) as usize;
        let message = lcg.bytes(length);
        assert_eq!(hex(&digest(&message)), hex(&oracle(&message)), "case {case}, length {length}");
    }
}

/// The compression function by itself, from an arbitrary hash value, against
/// the rounds written out in Rust: the oracle crate does not expose its own.
#[test]
fn compress_agrees_from_any_hash_value() {
    let mut lcg = Lcg(3);
    for case in 0..2_000 {
        let start: [u64; 8] = std::array::from_fn(|_| lcg.word());
        let block: [u8; 128] = lcg.bytes(128).try_into().unwrap();
        let mut linked = start;
        compress(&mut linked, &block);

        let mut w = [0u64; 80];
        for (word, bytes) in w.iter_mut().zip(block.chunks_exact(8)) {
            *word = u64::from_be_bytes(bytes.try_into().unwrap());
        }
        for t in 16..80 {
            w[t] = next_reference(w[t - 2], w[t - 7], w[t - 15], w[t - 16]);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = start;
        for t in 0..80 {
            let first = t1_reference(h, e, f, g, K[t], w[t]);
            let second = t2_reference(a, b, c);
            (h, g, f, e, d, c, b, a) = (g, f, e, d.wrapping_add(first), c, b, a, first.wrapping_add(second));
        }
        let expected: [u64; 8] = std::array::from_fn(|i| start[i].wrapping_add([a, b, c, d, e, f, g, h][i]));
        assert_eq!(linked, expected, "case {case}");
    }
}
