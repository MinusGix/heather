//! The linked SHA-256 against the standard's vectors, against plain Rust a
//! function at a time, and against an independent implementation.
//!
//! The same check as `tests/sha512.rs`, with one more seam to hold: the
//! words are 32 bits and the boundary is 64 (`src/sha256.rs`). So besides
//! the function-by-function comparison, the tests here call each export
//! with garbage in the upper halves of its arguments (the theorem says the
//! function truncates them away) and read the upper half of what comes back
//! (the theorem says it is zero). A lowering that let an upper half leak
//! into a rotation, which is the mistake a compiler that keeps 32-bit
//! values in 64-bit registers can make, fails every one of them.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]

use heather_linked::sha256::{INITIAL, K, block, compress, digest, next, t1, t2, wide};
use sha2::{Digest, Sha256};

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn oracle(bytes: &[u8]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(bytes);
    h.finalize().into()
}

/// The LCG of `tests/sha512.rs`.
struct Lcg(u64);

impl Lcg {
    fn word(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0 ^ (self.0 >> 32)
    }

    fn bytes(&mut self, n: usize) -> Vec<u8> {
        (0..n).map(|_| (self.word() >> 24) as u8).collect()
    }
}

/// The corners of a 32-bit word: a wrong carry, a wrong shift count, a
/// swapped argument or an upper half read as data cannot survive them all.
const CORNERS: [u32; 10] = [
    0,
    1,
    u32::MAX,
    1 << 31,
    (1 << 31) - 1,
    0x0123_4567,
    0xfedc_ba98,
    0xaaaa_aaaa,
    0x5555_5555,
    0x8000_0001,
];

/// What a caller might leave above a 32-bit argument.
const ABOVE: [u64; 5] = [0, u64::MAX << 32, 1 << 32, 1 << 63, 0xdead_beef << 32];

// The functions as FIPS 180-4 §4.1.2 writes them, in Rust.
fn ch(x: u32, y: u32, z: u32) -> u32 { (x & y) ^ (!x & z) }
fn maj(x: u32, y: u32, z: u32) -> u32 { (x & y) ^ (x & z) ^ (y & z) }
fn big0(x: u32) -> u32 { x.rotate_right(2) ^ x.rotate_right(13) ^ x.rotate_right(22) }
fn big1(x: u32) -> u32 { x.rotate_right(6) ^ x.rotate_right(11) ^ x.rotate_right(25) }
fn small0(x: u32) -> u32 { x.rotate_right(7) ^ x.rotate_right(18) ^ (x >> 3) }
fn small1(x: u32) -> u32 { x.rotate_right(17) ^ x.rotate_right(19) ^ (x >> 10) }

fn t1_reference(h: u32, e: u32, f: u32, g: u32, k: u32, w: u32) -> u32 {
    h.wrapping_add(big1(e)).wrapping_add(ch(e, f, g)).wrapping_add(k).wrapping_add(w)
}

fn t2_reference(a: u32, b: u32, c: u32) -> u32 {
    big0(a).wrapping_add(maj(a, b, c))
}

fn next_reference(w2: u32, w7: u32, w15: u32, w16: u32) -> u32 {
    small1(w2).wrapping_add(w7).wrapping_add(small0(w15)).wrapping_add(w16)
}

/// Each argument in turn takes every corner while the others hold distinct
/// words, so an argument read from the wrong register shows.
#[test]
fn each_word_function_agrees_at_the_corners() {
    let rest = [0x1111_1111u32, 0x2222_2222, 0x4444_4444, 0x8888_8888, 0x0f0f_0f0f, 0x00ff_00ff];
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

/// Carries out of bit 31 are where 32-bit arithmetic in a 64-bit register
/// goes wrong: every sum here overflows, some of them more than once.
#[test]
fn sums_that_carry_out_of_the_word_wrap() {
    for h in [u32::MAX, 1 << 31, 0xffff_0000] {
        for k in [u32::MAX, 1 << 31, 1] {
            for w in [u32::MAX, 1 << 31, 0x8000_0001] {
                assert_eq!(t1(h, u32::MAX, u32::MAX, 0, k, w), t1_reference(h, u32::MAX, u32::MAX, 0, k, w));
                assert_eq!(next(h, k, w, u32::MAX), next_reference(h, k, w, u32::MAX));
            }
        }
        assert_eq!(t2(h, u32::MAX, u32::MAX), t2_reference(h, u32::MAX, u32::MAX));
    }
}

#[test]
fn each_word_function_agrees_on_varied_words() {
    let mut lcg = Lcg(0x5eed);
    for case in 0..100_000 {
        let a: [u32; 6] = std::array::from_fn(|_| lcg.word() as u32);
        assert_eq!(t1(a[0], a[1], a[2], a[3], a[4], a[5]), t1_reference(a[0], a[1], a[2], a[3], a[4], a[5]), "T1, case {case}: {a:x?}");
        assert_eq!(t2(a[0], a[1], a[2]), t2_reference(a[0], a[1], a[2]), "T2, case {case}: {a:x?}");
        assert_eq!(next(a[0], a[1], a[2], a[3]), next_reference(a[0], a[1], a[2], a[3]), "schedule word, case {case}: {a:x?}");
    }
}

/// The 64-bit boundary: whatever sits above an argument is ignored, and
/// nothing sits above the result. At the corners, each argument in turn
/// carrying each kind of garbage.
#[test]
fn upper_halves_are_ignored_and_the_result_has_none() {
    let rest = [0x1111_1111u32, 0x2222_2222, 0x4444_4444, 0x8888_8888, 0x0f0f_0f0f, 0x00ff_00ff];
    for position in 0..6 {
        for corner in CORNERS {
            for above in ABOVE {
                let mut low = rest;
                low[position] = corner;
                let mut a = low.map(u64::from);
                a[position] |= above;
                assert_eq!(wide::t1(a[0], a[1], a[2], a[3], a[4], a[5]),
                    u64::from(t1_reference(low[0], low[1], low[2], low[3], low[4], low[5])),
                    "T1 with argument {position} = {:#x}", a[position]);
                if position < 3 {
                    assert_eq!(wide::t2(a[0], a[1], a[2]), u64::from(t2_reference(low[0], low[1], low[2])),
                        "T2 with argument {position} = {:#x}", a[position]);
                }
                if position < 4 {
                    assert_eq!(wide::next(a[0], a[1], a[2], a[3]),
                        u64::from(next_reference(low[0], low[1], low[2], low[3])),
                        "the schedule word with argument {position} = {:#x}", a[position]);
                }
            }
        }
    }
}

/// The same over varied whole words: every argument's upper half is
/// garbage at once.
#[test]
fn upper_halves_are_ignored_on_varied_words() {
    let mut lcg = Lcg(0xab0e);
    for case in 0..100_000 {
        let a: [u64; 6] = std::array::from_fn(|_| lcg.word());
        let low = a.map(|word| word as u32);
        assert_eq!(wide::t1(a[0], a[1], a[2], a[3], a[4], a[5]),
            u64::from(t1_reference(low[0], low[1], low[2], low[3], low[4], low[5])), "T1, case {case}: {a:x?}");
        assert_eq!(wide::t2(a[0], a[1], a[2]), u64::from(t2_reference(low[0], low[1], low[2])), "T2, case {case}: {a:x?}");
        assert_eq!(wide::next(a[0], a[1], a[2], a[3]),
            u64::from(next_reference(low[0], low[1], low[2], low[3])), "schedule word, case {case}: {a:x?}");
    }
}

/// As `tests/sha512.rs`: live values held across many calls.
#[test]
fn calls_keep_their_callers_values() {
    let mut lcg = Lcg(7);
    let (mut x, mut y, mut z) = (lcg.word() as u32, lcg.word() as u32, lcg.word() as u32);
    let (x0, y0, z0) = (x, y, z);
    let mut folded = 0u32;
    for round in 0..10_000u32 {
        folded = folded.wrapping_add(t1(x, y, z, round, folded, x ^ y))
            .wrapping_add(t2(y, z, x))
            .wrapping_add(next(z, x, y, round));
        (x, y, z) = (y.rotate_left(1), z.rotate_left(3), x.rotate_left(5));
    }
    let (mut x, mut y, mut z) = (x0, y0, z0);
    let mut expected = 0u32;
    for round in 0..10_000u32 {
        expected = expected.wrapping_add(t1_reference(x, y, z, round, expected, x ^ y))
            .wrapping_add(t2_reference(y, z, x))
            .wrapping_add(next_reference(z, x, y, round));
        (x, y, z) = (y.rotate_left(1), z.rotate_left(3), x.rotate_left(5));
    }
    assert_eq!(folded, expected);
}

/// FIPS 180-4's examples and NIST CAVS: the empty string, "abc" (the vector
/// `lib/_tests/std/crypto/sha2_tests.hthr` proves of the specification) and
/// the two-block messages. The vectors `crates/cache/tests/sha256.rs` holds
/// the compiler's own hash to.
#[test]
fn nist_vectors() {
    let cases: &[(&str, &str)] = &[
        ("", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
        ("abc", "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
        (
            "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1",
        ),
        (
            "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu",
            "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1",
        ),
    ];
    for (message, want) in cases {
        assert_eq!(hex(&digest(message.as_bytes())), *want, "SHA-256({message:?})");
    }
}

/// A million `a`s, the long-message vector: 15,625 blocks.
#[test]
fn the_million_a_vector() {
    assert_eq!(hex(&digest(&vec![b'a'; 1_000_000])),
        "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0");
}

/// Every length from empty through three blocks: each padding shape (the
/// length field fitting the last block, and not) at every offset.
#[test]
fn differential_every_length_through_three_blocks() {
    let mut lcg = Lcg(1);
    for length in 0..=3 * 64 + 1 {
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

/// §6.2.2 written out in Rust, over the reference word functions.
fn compress_reference(start: [u32; 8], block: &[u8; 64]) -> [u32; 8] {
    let mut w = [0u32; 64];
    for (word, bytes) in w.iter_mut().zip(block.chunks_exact(4)) {
        *word = u32::from_be_bytes(bytes.try_into().unwrap());
    }
    for t in 16..64 {
        w[t] = next_reference(w[t - 2], w[t - 7], w[t - 15], w[t - 16]);
    }
    let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = start;
    for t in 0..64 {
        let first = t1_reference(h, e, f, g, K[t], w[t]);
        let second = t2_reference(a, b, c);
        (h, g, f, e, d, c, b, a) = (g, f, e, d.wrapping_add(first), c, b, a, first.wrapping_add(second));
    }
    std::array::from_fn(|i| start[i].wrapping_add([a, b, c, d, e, f, g, h][i]))
}

/// The compression function by itself, from an arbitrary hash value, against
/// the rounds written out in Rust.
#[test]
fn compress_agrees_from_any_hash_value() {
    let mut lcg = Lcg(3);
    for case in 0..2_000 {
        let start: [u32; 8] = std::array::from_fn(|_| lcg.word() as u32);
        let block: [u8; 64] = lcg.bytes(64).try_into().unwrap();
        let mut linked = start;
        compress(&mut linked, &block);
        assert_eq!(linked, compress_reference(start, &block), "case {case}");
    }
}

// ---------------------------------------------------------------------------
// The compression function whole (`sha256_compress`, `sha256::block`)

/// The same, of the function that is all compiled Heather.
#[test]
fn block_compress_agrees_from_any_hash_value() {
    let mut lcg = Lcg(4);
    for case in 0..2_000 {
        let start: [u32; 8] = std::array::from_fn(|_| lcg.word() as u32);
        let block: [u8; 64] = lcg.bytes(64).try_into().unwrap();
        let mut linked = start;
        block::compress(&mut linked, &block);
        assert_eq!(linked, compress_reference(start, &block), "case {case}");
    }
}

/// Words where every sum carries and every rotation moves a set bit across
/// the word's ends: all ones, the top bit alone, and the two alternations,
/// as hash value and as block.
#[test]
fn block_compress_agrees_at_the_corners() {
    for hash_word in CORNERS {
        for block_byte in [0x00u8, 0xff, 0x80, 0x01, 0xaa, 0x55] {
            let start = [hash_word; 8];
            let block = [block_byte; 64];
            let mut linked = start;
            block::compress(&mut linked, &block);
            assert_eq!(linked, compress_reference(start, &block), "hash words {hash_word:#x}, block bytes {block_byte:#x}");
        }
    }
}

#[test]
fn block_nist_vectors() {
    let cases: &[(&str, &str)] = &[
        ("", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
        ("abc", "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
        (
            "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1",
        ),
        (
            "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu",
            "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1",
        ),
    ];
    for (message, want) in cases {
        assert_eq!(hex(&block::digest(message.as_bytes())), *want, "SHA-256({message:?})");
    }
}

/// A million `a`s through one context: 15,625 calls, each on what the last
/// left.
#[test]
fn block_the_million_a_vector() {
    assert_eq!(hex(&block::digest(&vec![b'a'; 1_000_000])),
        "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0");
}

#[test]
fn block_differential_every_length_through_three_blocks() {
    let mut lcg = Lcg(5);
    for length in 0..=3 * 64 + 1 {
        let message = lcg.bytes(length);
        assert_eq!(hex(&block::digest(&message)), hex(&oracle(&message)), "length {length}");
    }
}

#[test]
fn block_differential_long_messages() {
    let mut lcg = Lcg(6);
    for case in 0..64 {
        let length = (lcg.word() % 20_000) as usize;
        let message = lcg.bytes(length);
        assert_eq!(hex(&block::digest(&message)), hex(&oracle(&message)), "case {case}, length {length}");
    }
}

/// The Heather function transcribed: a context and a block of any lengths,
/// each read answering zero and each store doing nothing past its span's
/// end, in the order `lib/native/crypto/sha256_block.hthr` makes them. On a
/// whole context and a whole block it is `compress_reference`, which
/// `the_model_is_the_standard_on_whole_spans` holds; on short ones it is
/// what the linked function is certified to compute.
fn model(context: &mut [u8], block: &[u8]) -> u64 {
    fn word_at(span: &[u8], i: u64) -> u32 {
        let byte = |k: u64| u32::from(span.get(i.wrapping_add(k) as usize).copied().unwrap_or(0));
        byte(0) << 24 | byte(1) << 16 | byte(2) << 8 | byte(3)
    }
    fn put(span: &mut [u8], i: u64, byte: u8) {
        if let Some(slot) = span.get_mut(i as usize) {
            *slot = byte;
        }
    }
    fn put_word(span: &mut [u8], i: u64, word: u32) {
        for (k, byte) in word.to_be_bytes().into_iter().enumerate() {
            put(span, i.wrapping_add(k as u64), byte);
        }
    }
    // `sha256_take_block`, `sha256_expand`, `sha256_begin`.
    for i in 0..64 {
        put(context, i + 64, block.get(i as usize).copied().unwrap_or(0));
    }
    for i in 16..64 {
        let at = i * 4 + 64;
        let word = next_reference(word_at(context, at - 8), word_at(context, at - 28), word_at(context, at - 60), word_at(context, at - 64));
        put_word(context, at, word);
    }
    for i in 0..32 {
        let byte = context.get(i as usize).copied().unwrap_or(0);
        put(context, i + 32, byte);
    }
    // `sha256_rounds`: `sha256_step`, `sha256_turn`, `sha256_set`.
    for t in 0..64u64 {
        let first = t1_reference(word_at(context, 60), word_at(context, 48), word_at(context, 52), word_at(context, 56), K[t as usize],
            word_at(context, t * 4 + 64));
        let a = first.wrapping_add(t2_reference(word_at(context, 32), word_at(context, 36), word_at(context, 40)));
        let e = word_at(context, 44).wrapping_add(first);
        for i in 0..7 {
            let at = 56 - i * 4;
            let moved = word_at(context, at);
            put_word(context, at + 4, moved);
        }
        put_word(context, 32, a);
        put_word(context, 48, e);
    }
    // `sha256_end`.
    for i in 0..8 {
        let at = i * 4;
        let sum = word_at(context, at).wrapping_add(word_at(context, at + 32));
        put_word(context, at, sum);
    }
    8
}

fn context_of(hash: [u32; 8], rest: &[u8]) -> Vec<u8> {
    let mut context: Vec<u8> = hash.iter().flat_map(|word| word.to_be_bytes()).collect();
    context.extend_from_slice(rest);
    context
}

#[test]
fn the_model_is_the_standard_on_whole_spans() {
    let mut lcg = Lcg(8);
    for case in 0..200 {
        let start: [u32; 8] = std::array::from_fn(|_| lcg.word() as u32);
        let block: [u8; 64] = lcg.bytes(64).try_into().unwrap();
        let mut context = context_of(start, &[0; block::CONTEXT - 32]);
        model(&mut context, &block);
        assert_eq!(context[..32], context_of(compress_reference(start, &block), &[])[..], "case {case}");
    }
}

/// Every byte of the context after a call, not only the hash value: the
/// working variables and the whole schedule are where the Heather function
/// leaves them, and the answer is its last loop's count.
#[test]
fn block_leaves_the_whole_context_as_the_function_does() {
    let mut lcg = Lcg(9);
    for case in 0..500 {
        let start: [u32; 8] = std::array::from_fn(|_| lcg.word() as u32);
        let block = lcg.bytes(64);
        let mut linked = context_of(start, &lcg.bytes(block::CONTEXT - 32));
        let mut modelled = linked.clone();
        assert_eq!(block::compress_spans(&mut linked, &block), model(&mut modelled, &block), "case {case}");
        assert_eq!(linked, modelled, "case {case}");
    }
}

/// What the working area held before a call is never read: the hash value
/// after it is a function of the hash value before and the block alone.
#[test]
fn block_reads_nothing_of_the_working_area() {
    let mut lcg = Lcg(10);
    for case in 0..200 {
        let start: [u32; 8] = std::array::from_fn(|_| lcg.word() as u32);
        let block: [u8; 64] = lcg.bytes(64).try_into().unwrap();
        let mut context = context_of(start, &lcg.bytes(block::CONTEXT - 32));
        block::compress_spans(&mut context, &block);
        assert_eq!(context[..32], context_of(compress_reference(start, &block), &[])[..], "case {case}");
    }
}

/// Spans of every shorter length. The lengths are the function's own
/// bounds: a block that ends early is read as zeros from there, a context
/// that ends early is stored into only up to its end, and what lies after
/// either in the caller's memory is neither read as data nor changed. The
/// buffers here are longer than the spans lent from them, with a pattern
/// after the end that a stray store would break and a stray read would
/// carry into the result.
#[test]
fn block_keeps_within_short_spans() {
    let mut lcg = Lcg(11);
    let context_lengths = (0..=40).chain([63, 64, 65, 95, 96, 97, 127, 128, 255, 256, 316, 317, 318, 319, 320]);
    for context_length in context_lengths {
        for block_length in [0usize, 1, 3, 4, 31, 32, 55, 56, 63, 64] {
            let mut linked = lcg.bytes(block::CONTEXT + 64);
            let after: Vec<u8> = linked[context_length..].to_vec();
            let mut held = lcg.bytes(64 + 64);
            held[block_length..].fill(0xa5);
            let mut modelled = linked[..context_length].to_vec();
            let answered = block::compress_spans(&mut linked[..context_length], &held[..block_length]);
            assert_eq!(answered, model(&mut modelled, &held[..block_length]), "context {context_length}, block {block_length}");
            assert_eq!(linked[..context_length], modelled[..], "context {context_length}, block {block_length}");
            assert_eq!(linked[context_length..], after[..], "bytes after a context of {context_length}, block {block_length}");
        }
    }
}

/// A short block is the block with zeros after it.
#[test]
fn block_reads_a_short_block_as_zero_filled() {
    let mut lcg = Lcg(12);
    for length in 0..64 {
        let bytes = lcg.bytes(length);
        let mut filled = [0u8; 64];
        filled[..length].copy_from_slice(&bytes);
        let mut context = context_of(INITIAL, &[0; block::CONTEXT - 32]);
        block::compress_spans(&mut context, &bytes);
        assert_eq!(context[..32], context_of(compress_reference(INITIAL, &filled), &[])[..], "length {length}");
    }
}

/// A context lent again and again is the same as a fresh one each time:
/// nothing of one call's working area reaches the next.
#[test]
fn block_and_the_word_functions_agree_block_by_block() {
    let mut lcg = Lcg(13);
    let mut by_words = INITIAL;
    let mut by_block = INITIAL;
    for round in 0..1_000 {
        let block: [u8; 64] = lcg.bytes(64).try_into().unwrap();
        compress(&mut by_words, &block);
        block::compress(&mut by_block, &block);
        assert_eq!(by_words, by_block, "round {round}");
    }
}
