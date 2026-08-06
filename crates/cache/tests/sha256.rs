//! SHA-256 against its published vectors, and against an independent
//! implementation.
//!
//! The whole argument for a first-party hash (`docs/cache-v1-design.md` §2) is
//! that SHA-256 is a frozen specification with a *checkable* correctness
//! criterion rather than an arguable one. This file is that check; without it
//! the argument does not hold.
//!
//! The vectors alone were the weak form of it: four short messages and one
//! long one leave most of the padding logic — every length that is not
//! 0, 3, 56, 112 or a million — untested, and "probably fine" is not the
//! standard for a module whose collisions are wrongly accepted proofs. The
//! `differential_*` tests below fix that by running the `sha2` crate as an
//! **oracle**: dev-dependency only, never linked into anything shipped
//! (`Cargo.toml` says why), and the assertion is byte-identical digests. All
//! inputs are deterministic (a seeded LCG or counting bytes), so a failure is
//! reproducible from the test name alone.

use heather_cache::sha256::{Sha256, hex, sha256, unhex};
use sha2::{Digest, Sha256 as OracleSha256};

/// The oracle's digest of `bytes`.
fn oracle(bytes: &[u8]) -> [u8; 32] {
    let mut h = OracleSha256::new();
    h.update(bytes);
    h.finalize().into()
}

/// Deterministic pseudo-random bytes: a 64-bit LCG (Knuth's MMIX constants),
/// seeded per call. No clock, no `rand`, no nondeterminism — the property is
/// byte-identical digests, so the *content* only has to be varied, not random.
fn lcg_bytes(seed: u64, n: usize) -> Vec<u8> {
    let mut s = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
    (0..n)
        .map(|_| {
            s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            (s >> 33) as u8
        })
        .collect()
}

/// FIPS 180-4 / NIST CAVS: the three canonical vectors, plus the empty string.
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
    for (msg, want) in cases {
        assert_eq!(hex(&sha256(msg.as_bytes())), *want, "SHA-256({msg:?})");
    }
}

/// A million `a`s — the long-message vector. Exercises multi-block padding and
/// the 64-bit length field, which the short vectors do not.
#[test]
fn the_million_a_vector() {
    let mut h = Sha256::new();
    for _ in 0..1000 {
        h.update(&[b'a'; 1000]);
    }
    assert_eq!(
        hex(&h.finish()),
        "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
    );
}

/// Chunking must not change the digest: the streaming path is how a term
/// reaches this hasher, and `write_exact` chooses its own fragment sizes.
#[test]
fn chunking_does_not_change_the_digest() {
    let msg: Vec<u8> = (0u32..5000).map(|i| (i % 251) as u8).collect();
    let one = sha256(&msg);
    for chunk in [1usize, 7, 63, 64, 65, 127, 4096] {
        let mut h = Sha256::new();
        for c in msg.chunks(chunk) {
            h.update(c);
        }
        assert_eq!(h.finish(), one, "chunked by {chunk}");
    }
}

/// Every length from 0 to 300 bytes, against the oracle.
///
/// This is the test the published vectors could not be: it sweeps *every*
/// padding boundary — 55/56 (the length field no longer fits, so padding
/// spills into a second block), 63/64 (block full), 119/120 and 127/128 (the
/// same two, one block along) — rather than the handful of lengths FIPS
/// happens to name. Two contents per length, so a bug conditioned on the data
/// rather than the length has two chances to show.
#[test]
fn differential_every_length_to_300() {
    for n in 0..=300usize {
        for (label, msg) in [
            ("counting", (0..n).map(|i| (i % 256) as u8).collect::<Vec<u8>>()),
            ("lcg", lcg_bytes(n as u64, n)),
        ] {
            assert_eq!(
                sha256(&msg),
                oracle(&msg),
                "length {n} ({label}): first-party SHA-256 disagrees with `sha2`"
            );
        }
    }
}

/// Multi-block inputs up to ~1 MiB, at sizes on and off block boundaries.
///
/// The vectors' one long message is a million identical bytes; these are
/// varied content at lengths chosen to straddle 64-byte blocks (`±1` around
/// powers of two) so that the final partial block differs each time.
#[test]
fn differential_multi_block() {
    for n in [
        1_000usize, 4_095, 4_096, 4_097, 65_535, 65_536, 65_537, 100_000, 262_144, 1_048_575,
        1_048_576,
    ] {
        let msg = lcg_bytes(n as u64, n);
        assert_eq!(sha256(&msg), oracle(&msg), "length {n}: disagrees with `sha2`");
    }
}

/// Chunked feeding must equal one-shot, and both must equal the oracle.
///
/// This is the path the walker actually uses — bytes arrive from a staging
/// buffer in whatever sizes the tree produces — so the adversarial chunk sizes
/// are the ones that leave the internal buffer in every possible state: 1
/// (always partial), 63 (one short of a block, so the offset walks), 64
/// (exact), 65 (one over, so the carry is always 1 byte), 3 and 1000 (coprime
/// and much larger than a block).
#[test]
fn differential_chunked_feeding() {
    for total in [0usize, 1, 55, 56, 64, 65, 119, 120, 200, 4_096, 10_000] {
        let msg = lcg_bytes(total as u64 ^ 0xabcd, total);
        let want = oracle(&msg);
        assert_eq!(sha256(&msg), want, "one-shot, length {total}");
        for chunk in [1usize, 3, 63, 64, 65, 1000] {
            let mut h = Sha256::new();
            for c in msg.chunks(chunk) {
                h.update(c);
            }
            assert_eq!(h.finish(), want, "length {total} fed in {chunk}-byte chunks");
        }
        // And the degenerate feeding an interleaved walker can produce: an
        // empty update between every byte.
        let mut h = Sha256::new();
        for b in &msg {
            h.update(&[]);
            h.update(std::slice::from_ref(b));
        }
        assert_eq!(h.finish(), want, "length {total} fed byte-by-byte around empty updates");
    }
}

/// `hex`/`unhex` round-trip, and `unhex` rejects everything a corrupted cache
/// line could put in a hash column.
#[test]
fn hex_round_trips_and_rejects_junk() {
    let h = sha256(b"heather");
    assert_eq!(unhex(&hex(&h)), Some(h));
    assert_eq!(unhex(""), None);
    assert_eq!(unhex(&hex(&h)[..63]), None, "short");
    assert_eq!(unhex(&format!("{}0", hex(&h))), None, "long");
    assert_eq!(unhex(&hex(&h).to_uppercase()), None, "one spelling only");
    let mut bad = hex(&h);
    bad.replace_range(0..1, "z");
    assert_eq!(unhex(&bad), None, "not hex");
}

/// The `fmt::Write` impl is the whole point of the streaming design: the
/// hasher *is* the sink a term is rendered into.
#[test]
fn the_hasher_is_a_format_sink() {
    use std::fmt::Write;
    let mut h = Sha256::new();
    write!(h, "ab{}", 'c').expect("infallible");
    assert_eq!(hex(&h.finish()), hex(&sha256(b"abc")));
}
