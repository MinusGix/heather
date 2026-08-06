//! SHA-256 against its published vectors.
//!
//! The whole argument for a first-party hash (`docs/cache-v1-design.md` §2) is
//! that SHA-256 is a frozen specification with a *checkable* correctness
//! criterion rather than an arguable one. This file is that check; without it
//! the argument does not hold.

use heather_cache::sha256::{Sha256, hex, sha256, unhex};

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
