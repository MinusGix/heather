//! SHA-256 (FIPS 180-4), first-party.
//!
//! `docs/infrastructure/cache-v1-design.md` §2 argues the choice: a cache entry is believed
//! at rung 1, so a collision here is a wrongly accepted proof, which puts this
//! module in the same category as the kernel — the one place above the kernel
//! with a trust story to protect. FNV-1a (the determinism test's hash) is 64
//! bits and non-cryptographic and is right for a golden constant, not for a
//! key that must not collide adversarially.
//!
//! The implementation is deliberately the textbook one: a frozen
//! specification, no design decisions, and published test vectors, which is
//! why writing it beats depending on it. `tests/sha256.rs` pins it against the
//! NIST vectors plus a long message that exercises multi-block padding.
//!
//! **This file is also compiled into `build.rs`** by path (the build script
//! needs the same hash to fingerprint the kernel source, and cannot depend on
//! the crate it is building), so it must stay self-contained: `std` only, no
//! `use crate::`, no items from elsewhere in this crate.

/// Streaming SHA-256.
///
/// Implements [`std::fmt::Write`], so it can *be* the sink
/// `heather_kernel::fmt::write_exact` streams a term into — nothing the size
/// of the printed tree is ever held in memory.
#[derive(Clone)]
pub struct Sha256 {
    state: [u32; 8],
    /// Bytes not yet absorbed into a full 64-byte block.
    buf: [u8; 64],
    buf_len: usize,
    /// Total message length in bytes (the padding encodes it in bits).
    total: u64,
    /// Compress with the CPU's SHA extensions rather than the scalar
    /// rounds. Decided once, in [`Sha256::new`]; [`Sha256::scalar`] forces
    /// the portable path so a test can compare the two on one machine.
    sha_extensions: bool,
}

const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

impl Sha256 {
    pub fn new() -> Sha256 {
        Sha256 {
            state: [
                0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
                0x5be0cd19,
            ],
            buf: [0; 64],
            buf_len: 0,
            total: 0,
            sha_extensions: sha_extensions_available(),
        }
    }

    /// The portable rounds, whatever the CPU offers. The same function as
    /// [`Sha256::new`] on a machine without the extensions.
    pub fn scalar() -> Sha256 {
        Sha256 { sha_extensions: false, ..Sha256::new() }
    }

    /// Whether this hasher compresses with the SHA extensions.
    pub fn uses_sha_extensions(&self) -> bool {
        self.sha_extensions
    }

    pub fn update(&mut self, mut bytes: &[u8]) {
        self.total = self.total.wrapping_add(bytes.len() as u64);
        if self.buf_len > 0 {
            let want = 64 - self.buf_len;
            let take = want.min(bytes.len());
            self.buf[self.buf_len..self.buf_len + take].copy_from_slice(&bytes[..take]);
            self.buf_len += take;
            bytes = &bytes[take..];
            if self.buf_len == 64 {
                let block = self.buf;
                self.compress_blocks(&block);
                self.buf_len = 0;
            }
        }
        let whole = bytes.len() - bytes.len() % 64;
        if whole > 0 {
            self.compress_blocks(&bytes[..whole]);
            bytes = &bytes[whole..];
        }
        if !bytes.is_empty() {
            self.buf[..bytes.len()].copy_from_slice(bytes);
            self.buf_len = bytes.len();
        }
    }

    pub fn finish(mut self) -> [u8; 32] {
        let bits = self.total.wrapping_mul(8);
        self.update(&[0x80]);
        // `update` moved `total` on, but padding length is fixed by the
        // pre-padding length captured above, so drive the zeros off buf_len.
        while self.buf_len != 56 {
            self.update(&[0]);
        }
        let block_tail = bits.to_be_bytes();
        self.update(&block_tail);
        debug_assert_eq!(self.buf_len, 0);
        let mut out = [0u8; 32];
        for (i, w) in self.state.iter().enumerate() {
            out[i * 4..i * 4 + 4].copy_from_slice(&w.to_be_bytes());
        }
        out
    }

    /// Every 64-byte block of `blocks` (a multiple of 64 long), in order.
    #[allow(unsafe_code)]
    fn compress_blocks(&mut self, blocks: &[u8]) {
        #[cfg(target_arch = "x86_64")]
        if self.sha_extensions {
            // SAFETY: `sha_extensions` is set only when `is_x86_feature_detected!`
            // reported every feature the function enables, and `blocks` is a
            // whole number of 64-byte blocks read through unaligned loads.
            unsafe { compress_blocks_sha(&mut self.state, blocks) };
            return;
        }
        for block in blocks.chunks_exact(64) {
            let mut b = [0u8; 64];
            b.copy_from_slice(block);
            self.compress(&b);
        }
    }

    fn compress(&mut self, block: &[u8; 64]) {
        let mut w = [0u32; 64];
        for i in 0..16 {
            w[i] = u32::from_be_bytes([
                block[i * 4],
                block[i * 4 + 1],
                block[i * 4 + 2],
                block[i * 4 + 3],
            ]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = self.state;
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ ((!e) & g);
            let t1 = h
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(K[i])
                .wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let t2 = s0.wrapping_add(maj);
            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(t1);
            d = c;
            c = b;
            b = a;
            a = t1.wrapping_add(t2);
        }
        let add = [a, b, c, d, e, f, g, h];
        for (s, v) in self.state.iter_mut().zip(add) {
            *s = s.wrapping_add(v);
        }
    }
}

// ---- the SHA extensions path -------------------------------------------
//
// Same function, one instruction per round instead of ~a dozen. The walk
// feeds this hasher hundreds of megabytes per cold check of a large module
// (`issues/merkle-walk-cold-share.md`: 445 MB on the showcase, ~1.4 s of a
// 3.1 s walk at the scalar rate), and every x86-64 the project builds on
// has the extensions. Selected once per hasher from the CPU's own word;
// the scalar path is the same specification and the one every other
// target runs. `tests/sha256.rs` checks both against the vectors and
// against each other, so neither can drift from the other unnoticed.

#[cfg(target_arch = "x86_64")]
fn sha_extensions_available() -> bool {
    std::arch::is_x86_feature_detected!("sha")
        && std::arch::is_x86_feature_detected!("sse4.1")
        && std::arch::is_x86_feature_detected!("ssse3")
}

#[cfg(not(target_arch = "x86_64"))]
fn sha_extensions_available() -> bool {
    false
}

/// Compress every 64-byte block of `blocks` (whose length is a multiple of
/// 64) with the SHA extensions. Intel's reference schedule: the state is
/// held as the two lane pairs ABEF/CDGH the `rnds2` instruction works on,
/// four rounds per instruction pair, the message schedule advanced with
/// `msg1`/`msg2` once the first sixteen words are consumed.
///
/// # Safety
///
/// The CPU must have the `sha`, `ssse3` and `sse4.1` extensions
/// ([`sha_extensions_available`]); `blocks.len()` must be a multiple of 64.
#[cfg(target_arch = "x86_64")]
#[allow(unsafe_code)]
#[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
unsafe fn compress_blocks_sha(state: &mut [u32; 8], blocks: &[u8]) {
    use std::arch::x86_64::*;
    debug_assert_eq!(blocks.len() % 64, 0);

    #[inline]
    #[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
    fn k(i: usize) -> __m128i {
        _mm_setr_epi32(K[4 * i] as i32, K[4 * i + 1] as i32, K[4 * i + 2] as i32, K[4 * i + 3] as i32)
    }
    #[inline]
    #[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
    fn rounds4(abef: &mut __m128i, cdgh: &mut __m128i, w: __m128i, i: usize) {
        let t1 = _mm_add_epi32(w, k(i));
        *cdgh = _mm_sha256rnds2_epu32(*cdgh, *abef, t1);
        let t2 = _mm_shuffle_epi32(t1, 0x0E);
        *abef = _mm_sha256rnds2_epu32(*abef, *cdgh, t2);
    }
    #[inline]
    #[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
    fn schedule(v0: __m128i, v1: __m128i, v2: __m128i, v3: __m128i) -> __m128i {
        let t1 = _mm_sha256msg1_epu32(v0, v1);
        let t2 = _mm_alignr_epi8(v3, v2, 4);
        let t3 = _mm_add_epi32(t1, t2);
        _mm_sha256msg2_epu32(t3, v3)
    }
    /// Four little-endian words as one lane group, in big-endian word order.
    #[inline]
    #[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
    fn load_words(bytes: &[u8; 16]) -> __m128i {
        let mask = _mm_set_epi64x(0x0C0D_0E0F_0809_0A0Bu64 as i64, 0x0405_0607_0001_0203u64 as i64);
        // SAFETY: a 16-byte array is exactly one unaligned 128-bit load.
        let raw = unsafe { _mm_loadu_si128(bytes.as_ptr() as *const __m128i) };
        _mm_shuffle_epi8(raw, mask)
    }
    #[inline]
    #[target_feature(enable = "sse2")]
    fn load_state(words: &[u32; 4]) -> __m128i {
        // SAFETY: four `u32`s are exactly one unaligned 128-bit load.
        unsafe { _mm_loadu_si128(words.as_ptr() as *const __m128i) }
    }
    #[inline]
    #[target_feature(enable = "sse2")]
    fn store_state(words: &mut [u32; 4], v: __m128i) {
        // SAFETY: four `u32`s are exactly one unaligned 128-bit store.
        unsafe { _mm_storeu_si128(words.as_mut_ptr() as *mut __m128i, v) }
    }

    let (lo, hi) = state.split_at_mut(4);
    let lo: &mut [u32; 4] = lo.try_into().expect("four words");
    let hi: &mut [u32; 4] = hi.try_into().expect("four words");
    let dcba = load_state(lo);
    let efgh = load_state(hi);
    let cdab = _mm_shuffle_epi32(dcba, 0xB1);
    let efgh = _mm_shuffle_epi32(efgh, 0x1B);
    let mut abef = _mm_alignr_epi8(cdab, efgh, 8);
    let mut cdgh = _mm_blend_epi16(efgh, cdab, 0xF0);

    for block in blocks.chunks_exact(64) {
        let abef_save = abef;
        let cdgh_save = cdgh;
        let quarter = |i: usize| -> &[u8; 16] { block[16 * i..16 * i + 16].try_into().expect("sixteen bytes") };
        let mut w0 = load_words(quarter(0));
        let mut w1 = load_words(quarter(1));
        let mut w2 = load_words(quarter(2));
        let mut w3 = load_words(quarter(3));
        let mut w4;

        rounds4(&mut abef, &mut cdgh, w0, 0);
        rounds4(&mut abef, &mut cdgh, w1, 1);
        rounds4(&mut abef, &mut cdgh, w2, 2);
        rounds4(&mut abef, &mut cdgh, w3, 3);
        w4 = schedule(w0, w1, w2, w3);
        rounds4(&mut abef, &mut cdgh, w4, 4);
        w0 = schedule(w1, w2, w3, w4);
        rounds4(&mut abef, &mut cdgh, w0, 5);
        w1 = schedule(w2, w3, w4, w0);
        rounds4(&mut abef, &mut cdgh, w1, 6);
        w2 = schedule(w3, w4, w0, w1);
        rounds4(&mut abef, &mut cdgh, w2, 7);
        w3 = schedule(w4, w0, w1, w2);
        rounds4(&mut abef, &mut cdgh, w3, 8);
        w4 = schedule(w0, w1, w2, w3);
        rounds4(&mut abef, &mut cdgh, w4, 9);
        w0 = schedule(w1, w2, w3, w4);
        rounds4(&mut abef, &mut cdgh, w0, 10);
        w1 = schedule(w2, w3, w4, w0);
        rounds4(&mut abef, &mut cdgh, w1, 11);
        w2 = schedule(w3, w4, w0, w1);
        rounds4(&mut abef, &mut cdgh, w2, 12);
        w3 = schedule(w4, w0, w1, w2);
        rounds4(&mut abef, &mut cdgh, w3, 13);
        w4 = schedule(w0, w1, w2, w3);
        rounds4(&mut abef, &mut cdgh, w4, 14);
        w0 = schedule(w1, w2, w3, w4);
        rounds4(&mut abef, &mut cdgh, w0, 15);

        abef = _mm_add_epi32(abef, abef_save);
        cdgh = _mm_add_epi32(cdgh, cdgh_save);
    }

    let feba = _mm_shuffle_epi32(abef, 0x1B);
    let dchg = _mm_shuffle_epi32(cdgh, 0xB1);
    let dcba = _mm_blend_epi16(feba, dchg, 0xF0);
    let hgef = _mm_alignr_epi8(dchg, feba, 8);
    store_state(lo, dcba);
    store_state(hi, hgef);
}

impl Default for Sha256 {
    fn default() -> Sha256 {
        Sha256::new()
    }
}

impl std::fmt::Write for Sha256 {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.update(s.as_bytes());
        Ok(())
    }
}

/// Lowercase hex, 64 characters. The one spelling of a hash anywhere in the
/// cache: on disk, in messages, and inside the Merkle substitution.
pub fn hex(bytes: &[u8; 32]) -> String {
    let mut buf = [0u8; 64];
    hex_into(bytes, &mut buf);
    String::from_utf8(buf.to_vec()).expect("hex digits are ASCII")
}

/// [`hex`] without the allocation, for the Merkle substitution — which emits
/// one of these per global reference, in the innermost loop of the only thing
/// a warm run spends time on.
pub fn hex_into(bytes: &[u8; 32], out: &mut [u8; 64]) {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    for (i, b) in bytes.iter().enumerate() {
        out[i * 2] = DIGITS[(b >> 4) as usize];
        out[i * 2 + 1] = DIGITS[(b & 0xf) as usize];
    }
}

/// Parse the output of [`hex`]. `None` for anything that is not exactly 64
/// lowercase hex digits — the shape check a corrupted cache line fails.
pub fn unhex(s: &str) -> Option<[u8; 32]> {
    if s.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    let b = s.as_bytes();
    for i in 0..32 {
        let hi = (b[i * 2] as char).to_digit(16)?;
        let lo = (b[i * 2 + 1] as char).to_digit(16)?;
        if b[i * 2].is_ascii_uppercase() || b[i * 2 + 1].is_ascii_uppercase() {
            return None;
        }
        out[i] = (hi * 16 + lo) as u8;
    }
    Some(out)
}

/// One-shot convenience.
pub fn sha256(bytes: &[u8]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(bytes);
    h.finish()
}
