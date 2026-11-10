//! SHA-256 whose every word is computed by compiled Heather.
//!
//! The same split as [`crate::sha512`], at the width the compiler's own hash
//! uses (`crates/cache/src/sha256.rs`): [`t1`], [`t2`] and [`next`] are the
//! linked functions, and [`compress`] and [`digest`] are the Rust around
//! them.
//!
//! # 32-bit words through a 64-bit boundary
//!
//! A `runtime fn`'s parameters and result are 64-bit words, so each linked
//! function takes its 32-bit arguments in the low halves of 64-bit ones and
//! returns its 32-bit result zero-extended. The function itself truncates
//! every argument first (`lib/native/crypto/sha256_round.hthr`), so what a
//! caller leaves in the upper halves cannot matter, and the theorems there
//! (`sha256_t1_spec` and its neighbours) are stated at exactly this
//! boundary: the specification's word, widened, in; the specification's
//! word in the low half out. Inside, the arithmetic is 32-bit: the compiler
//! keeps a narrow value zero-extended in its register and clears the upper
//! half after each addition and left shift
//! (`lib/native/function_ir/function_ir_lower.hthr`, "Narrow widths").

use crate::exports;

/// `T1 = h + Σ1(e) + Ch(e, f, g) + K + W` (FIPS 180-4 §6.2.2).
#[inline]
pub fn t1(h: u32, e: u32, f: u32, g: u32, k: u32, w: u32) -> u32 {
    exports::sha256_t1(h.into(), e.into(), f.into(), g.into(), k.into(), w.into()) as u32
}

/// `T2 = Σ0(a) + Maj(a, b, c)`.
#[inline]
pub fn t2(a: u32, b: u32, c: u32) -> u32 {
    exports::sha256_t2(a.into(), b.into(), c.into()) as u32
}

/// One schedule word: `σ1(W(t−2)) + W(t−7) + σ0(W(t−15)) + W(t−16)`.
#[inline]
pub fn next(w2: u32, w7: u32, w15: u32, w16: u32) -> u32 {
    exports::sha256_next(w2.into(), w7.into(), w15.into(), w16.into()) as u32
}

/// The linked functions at the boundary they are compiled for: whole 64-bit
/// words in, a whole 64-bit word out. The tests use these to hold the two
/// halves of the contract the 32-bit wrappers above cannot see: the upper
/// halves of the arguments are ignored, and the upper half of the result is
/// zero.
pub mod wide {
    use crate::exports;

    #[inline]
    pub fn t1(h: u64, e: u64, f: u64, g: u64, k: u64, w: u64) -> u64 {
        exports::sha256_t1(h, e, f, g, k, w)
    }

    #[inline]
    pub fn t2(a: u64, b: u64, c: u64) -> u64 {
        exports::sha256_t2(a, b, c)
    }

    #[inline]
    pub fn next(w2: u64, w7: u64, w15: u64, w16: u64) -> u64 {
        exports::sha256_next(w2, w7, w15, w16)
    }
}

/// The round constants, §4.2.2.
pub const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

/// The initial hash value, §5.3.3.
pub const INITIAL: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

/// §6.2.2: the hash value after one more block.
pub fn compress(hash: &mut [u32; 8], block: &[u8; 64]) {
    let mut w = [0u32; 64];
    for (word, bytes) in w.iter_mut().zip(block.chunks_exact(4)) {
        *word = u32::from_be_bytes(bytes.try_into().expect("four bytes"));
    }
    for t in 16..64 {
        w[t] = next(w[t - 2], w[t - 7], w[t - 15], w[t - 16]);
    }
    let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = *hash;
    for t in 0..64 {
        let first = t1(h, e, f, g, K[t], w[t]);
        let second = t2(a, b, c);
        // `Sha2State::turn`.
        (h, g, f, e, d, c, b, a) = (g, f, e, d.wrapping_add(first), c, b, a, first.wrapping_add(second));
    }
    for (word, turned) in hash.iter_mut().zip([a, b, c, d, e, f, g, h]) {
        *word = word.wrapping_add(turned);
    }
}

/// SHA-256 of a message.
pub fn digest(message: &[u8]) -> [u8; 32] {
    let mut hash = INITIAL;
    let mut blocks = message.chunks_exact(64);
    for block in &mut blocks {
        compress(&mut hash, block.try_into().expect("a whole block"));
    }
    // §5.1.1: 0x80, zeros, and the length in bits as eight bytes, ending on
    // a block boundary: one more block, or two when the tail leaves no room
    // for the nine.
    let tail = blocks.remainder();
    let mut last = [0u8; 128];
    last[..tail.len()].copy_from_slice(tail);
    last[tail.len()] = 0x80;
    let padded = if tail.len() + 9 <= 64 { 64 } else { 128 };
    let bits = (message.len() as u64).wrapping_mul(8);
    last[padded - 8..padded].copy_from_slice(&bits.to_be_bytes());
    for block in last[..padded].chunks_exact(64) {
        compress(&mut hash, block.try_into().expect("a whole block"));
    }
    let mut out = [0u8; 32];
    for (bytes, word) in out.chunks_exact_mut(4).zip(hash) {
        bytes.copy_from_slice(&word.to_be_bytes());
    }
    out
}
