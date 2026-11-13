//! SHA-256 whose every word is computed by compiled Heather.
//!
//! The same split as [`crate::sha512`], at the width the compiler's own hash
//! uses (`crates/cache/src/sha256.rs`): [`t1`], [`t2`] and [`next`] are the
//! linked functions, and [`compress`] and [`digest`] are the Rust around
//! them.
//!
//! [`block`] is the compression function whole: one linked function over
//! two spans of bytes, with the schedule, the sixty-four rounds and the
//! final sums all compiled Heather, and only the padding left to Rust.
//!
//! [`stream`] is the hash whole: [`stream::Sha256`] takes a message in
//! parts and every byte of the work, the padding included, is compiled
//! Heather. What is Rust's there is the bytes it lends, as many as the
//! Heather module says a context is.
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

/// The compression function as one linked function,
/// `sha256_compress` of `lib/native/crypto/sha256_one_block.hthr`.
///
/// It works in a *context* of [`CONTEXT`](block::CONTEXT) bytes that its
/// caller lends it, the `Sha256` record of
/// `lib/native/crypto/sha256_context.hthr`: the hash value's eight words,
/// the eight working variables and the schedule's sixty-four words, each
/// word four bytes with the most significant first, and the stream's
/// count, which this function leaves alone. Where each lies is that
/// module's declaration's to say; Rust is told the context's size and
/// where the hash value is ([`HASH`](block::HASH)), and needs nothing
/// else. It reads the hash value and the block, and stores the hash
/// value, the working variables and the schedule; the hash value after
/// the block is where the one before it was. Nothing of the working area
/// is read before it is stored, so a caller need not clear it.
///
/// Every read and store is under the length of the span it is in
/// (`List::byte_within`, `List::put_within`): a block shorter than
/// sixty-four bytes is read as though zeros followed it, and nothing is
/// stored past the end of a context that is too short, where the function
/// then computes something else that is still a function of the bytes it
/// was lent. [`compress`](block::compress) lends it exactly what it asks.
///
/// What is certified is that the code computes the Heather function, with
/// the memory safety that goes with it. That the Heather function is
/// FIPS 180-4's is not proved yet (`issues/sha2-compress-native.md`); the
/// tests hold it to the standard's vectors and to an independent
/// implementation.
pub mod block {
    use super::INITIAL;
    use crate::exports;

    /// The bytes of a context: the Heather module's
    /// `SHA256_CONTEXT_BYTES`, which is its record's size by a theorem
    /// there.
    pub const CONTEXT: usize = crate::constants::SHA256_CONTEXT_BYTES as usize;

    /// Where the hash value's thirty-two bytes begin in a context: the
    /// module's `SHA256_DIGEST_AT`, held to the record the same way.
    pub const HASH: usize = crate::constants::SHA256_DIGEST_AT as usize;

    /// The linked function at its boundary: any two spans. Answers 8, the
    /// count its last loop stops at.
    #[inline]
    pub fn compress_spans(context: &mut [u8], block: &[u8]) -> u64 {
        exports::sha256_compress(context, block)
    }

    /// §6.2.2: the hash value after one more block.
    pub fn compress(hash: &mut [u32; 8], block: &[u8; 64]) {
        let mut context = [0u8; CONTEXT];
        for (bytes, word) in context[HASH..HASH + 32].chunks_exact_mut(4).zip(*hash) {
            bytes.copy_from_slice(&word.to_be_bytes());
        }
        exports::sha256_compress(&mut context, block);
        for (word, bytes) in hash.iter_mut().zip(context[HASH..HASH + 32].chunks_exact(4)) {
            *word = u32::from_be_bytes(bytes.try_into().expect("four bytes"));
        }
    }

    /// SHA-256 of a message: one context through every block, and the
    /// digest read off the hash value's thirty-two bytes, which are
    /// already its words in the order §6.2.2 spells them.
    pub fn digest(message: &[u8]) -> [u8; 32] {
        let mut context = [0u8; CONTEXT];
        for (bytes, word) in context[HASH..HASH + 32].chunks_exact_mut(4).zip(INITIAL) {
            bytes.copy_from_slice(&word.to_be_bytes());
        }
        let mut blocks = message.chunks_exact(64);
        for block in &mut blocks {
            exports::sha256_compress(&mut context, block);
        }
        // §5.1.1, as `super::digest` pads.
        let tail = blocks.remainder();
        let mut last = [0u8; 128];
        last[..tail.len()].copy_from_slice(tail);
        last[tail.len()] = 0x80;
        let padded = if tail.len() + 9 <= 64 { 64 } else { 128 };
        let bits = (message.len() as u64).wrapping_mul(8);
        last[padded - 8..padded].copy_from_slice(&bits.to_be_bytes());
        for block in last[..padded].chunks_exact(64) {
            exports::sha256_compress(&mut context, block);
        }
        context[HASH..HASH + 32].try_into().expect("thirty-two bytes")
    }
}

/// The hash over a message that arrives in parts, all of it linked:
/// `sha256_init`, `sha256_update` and `sha256_finish` of
/// `lib/native/crypto/sha256_stream.hthr`.
///
/// The context the three share is [`block`]'s, with its count of bytes
/// taken, most significant first. A block is assembled in the schedule's
/// first sixteen words, so a part that ends inside a block leaves its
/// bytes in the context for the next part to follow, and the padding of
/// §5.1.1 is the linked code's. The digest is the hash value's
/// thirty-two bytes after `sha256_finish`.
///
/// Each function reads and stores only under the length of the span it is
/// in, as [`block`]'s does, and what is certified is the same: the code
/// computes the Heather functions. That those are FIPS 180-4's is the
/// tests' claim.
pub mod stream {
    use crate::exports;

    /// The bytes of a context: [`super::block::CONTEXT`].
    pub const CONTEXT: usize = super::block::CONTEXT;

    /// The linked functions at their boundary: any spans.
    pub mod spans {
        use crate::exports;

        /// The initial hash value and a count of zero. Answers 0.
        #[inline]
        pub fn init(context: &mut [u8]) -> u64 {
            exports::sha256_init(context)
        }

        /// One more part. Answers the count of bytes taken so far.
        #[inline]
        pub fn update(context: &mut [u8], message: &[u8]) -> u64 {
            exports::sha256_update(context, message)
        }

        /// The padding and the last block.
        #[inline]
        pub fn finish(context: &mut [u8]) -> u64 {
            exports::sha256_finish(context)
        }
    }

    /// SHA-256 in progress: `crates/cache/src/sha256.rs`'s three calls,
    /// each one linked function.
    #[derive(Clone)]
    pub struct Sha256 {
        context: [u8; CONTEXT],
    }

    impl Sha256 {
        pub fn new() -> Sha256 {
            let mut context = [0u8; CONTEXT];
            exports::sha256_init(&mut context);
            Sha256 { context }
        }

        /// One more part of the message.
        pub fn update(&mut self, bytes: &[u8]) {
            exports::sha256_update(&mut self.context, bytes);
        }

        /// The digest of everything taken.
        pub fn finish(mut self) -> [u8; 32] {
            exports::sha256_finish(&mut self.context);
            self.context[super::block::HASH..super::block::HASH + 32].try_into().expect("thirty-two bytes")
        }
    }

    impl Default for Sha256 {
        fn default() -> Sha256 {
            Sha256::new()
        }
    }

    /// SHA-256 of a message in one part.
    pub fn digest(message: &[u8]) -> [u8; 32] {
        let mut hash = Sha256::new();
        hash.update(message);
        hash.finish()
    }
}
