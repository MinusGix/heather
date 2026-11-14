//! SHA-256 as a textbook writes it in Rust (FIPS 180-4 §6.2.2): the hash
//! value, the schedule and the working variables in locals, words read
//! with `from_be_bytes`. The fifth reference: what plain scalar code costs
//! on this machine, with no SHA instructions.

use heather_linked::sha256::{INITIAL, K};

pub fn compress(hash: &mut [u32; 8], block: &[u8; 64]) {
    let mut w = [0u32; 64];
    for (word, bytes) in w.iter_mut().zip(block.chunks_exact(4)) {
        *word = u32::from_be_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
    }
    for t in 16..64 {
        let s0 = w[t - 15].rotate_right(7) ^ w[t - 15].rotate_right(18) ^ (w[t - 15] >> 3);
        let s1 = w[t - 2].rotate_right(17) ^ w[t - 2].rotate_right(19) ^ (w[t - 2] >> 10);
        w[t] = s1.wrapping_add(w[t - 7]).wrapping_add(s0).wrapping_add(w[t - 16]);
    }
    let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = *hash;
    for t in 0..64 {
        let big1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
        let ch = (e & f) ^ (!e & g);
        let t1 = h.wrapping_add(big1).wrapping_add(ch).wrapping_add(K[t]).wrapping_add(w[t]);
        let big0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
        let maj = (a & b) ^ (a & c) ^ (b & c);
        let t2 = big0.wrapping_add(maj);
        h = g;
        g = f;
        f = e;
        e = d.wrapping_add(t1);
        d = c;
        c = b;
        b = a;
        a = t1.wrapping_add(t2);
    }
    for (word, turned) in hash.iter_mut().zip([a, b, c, d, e, f, g, h]) {
        *word = word.wrapping_add(turned);
    }
}

pub fn digest(message: &[u8]) -> [u8; 32] {
    let mut hash = INITIAL;
    let mut blocks = message.chunks_exact(64);
    for block in &mut blocks {
        compress(&mut hash, block.try_into().expect("a whole block"));
    }
    let tail = blocks.remainder();
    let mut last = [0u8; 128];
    last[..tail.len()].copy_from_slice(tail);
    last[tail.len()] = 0x80;
    let padded = if tail.len() + 9 <= 64 { 64 } else { 128 };
    last[padded - 8..padded].copy_from_slice(&(message.len() as u64).wrapping_mul(8).to_be_bytes());
    for block in last[..padded].chunks_exact(64) {
        compress(&mut hash, block.try_into().expect("a whole block"));
    }
    let mut out = [0u8; 32];
    for (bytes, word) in out.chunks_exact_mut(4).zip(hash) {
        bytes.copy_from_slice(&word.to_be_bytes());
    }
    out
}
