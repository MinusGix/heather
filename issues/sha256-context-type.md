---
title: SHA-256's context as a type with its functions as methods, and what stands in the way
status: open
labels: [native,crypto,design,ergonomics]
area: heather-in-heather
milestone: [crypto-hash]
created: 2026-11-12
updated: 2026-11-12
---

SHA-256's state is a `List<u8>` and a length word passed side by side through every function of `lib/native/crypto/sha256_block.hthr` and `sha256_stream.hthr`, with its layout (hash value at byte 0, working variables at 32, schedule or block at 64, count at 320) as numbers in the bodies. Minus's question (2026-11-12): should the context be its own type with these as functions on it. Yes, and what stands between is listed here so each part can be done where it belongs.

What the source should read as:

```heather
record Sha256 { hash: Array<u32, 8>, block: Array<u8, 64>, fill: u64, count: u64 }

runtime fn Sha256::update(mut self, message: Bytes) { for byte in message { self.push(byte) } }
```

What is in the way, each its own issue:

1. **A record has no runtime layout** unless it is one word (`datarepr`, [[runtime-repr-narrow-words]]): "`P` has no runtime layout under the reflected fragment". The context needs a record laid out over a span of bytes, which is the views work ([[source-buffers-as-views]], [[rt-fixed-arrays-and-tables]]).
2. **A span is two parameters.** `Bytes` as one value that carries its length would halve every signature here and in the lexer, and is what makes "a span is two of six words" ([[function-call-past-six-words]]) bite less.
3. **A measured recursion cannot be a method** ([[decreases-self-parameter]]), so the loops could not be `Sha256::…` even with the type.
4. **Words are 64-bit only.** The round functions mask to 32 bits by hand; with `u32` values they would be `Sha2`'s own `big_sigma0` and the rest, and "the compiled function is the specification" would be nearer a statement than a proof ([[runtime-repr-narrow-words]], [[bitvec-rotates-and-wide-ops]]).
5. **The round constants are a tree of sixty-four leaves** because compiled code has no table ([[rt-fixed-arrays-and-tables]]): 190 of the block module's lines.
6. **Eight working variables do not fit a call**, so they live in the span and a round is three functions ([[function-call-past-six-words]]).

A step that needs none of these, taken first: the two modules respelled with what the language already has (`u64`/`u8`, numerals, `+ - << >> & |`, `if a < b` outside the loops, `mut self` methods for the stores), which a probe shows the generator takes. The loops' hand proofs go with [[decreases-word-measures-by-hand]], exclusive or with [[bitvec-xor-complement-symbols]].

Done when: `crates/linked`'s SHA-256 is compiled from a module whose functions are methods of a context type, with no layout offsets in their bodies.
