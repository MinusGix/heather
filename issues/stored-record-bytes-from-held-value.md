---
title: A span that holds a record says nothing about its bytes: no law from the value back to the span
status: closed
labels: [native,layout]
area: heather-in-heather
milestone: [crypto-hash]
created: 2026-11-14
updated: 2026-11-14
---

`Stored<A>` has `round: read(write(a)) = a` and no converse, and
`Stored::Holds(span, n, a)` is `get(span, 0) = a` with two bounds. So a
theorem about the record a function leaves does not reach the bytes a
caller reads out of the span afterwards.

Met at the end of SHA-256's agreement
(`lib/native/crypto/sha256_stream_agreement.hthr`). `Sha256::digest_spec`
says `Sha256::digest(finish(...).after) = Sha2::digest(message)`, where
`Sha256::digest(s)` is the hash value's words spelled most significant
byte first. The Rust wrapper (`crates/linked/src/sha256.rs`) copies thirty-two
bytes of the span at `SHA256_DIGEST_AT`. That those bytes are
`Sha256::digest(s)` where the span holds `s` is true for this layout, and
nothing states it.

**Wanted:** for a codec whose reader loses nothing (every `laid` record of
fixed-width words is one), the law `write(read(bytes)) = bytes` at the
layout's size, carried by `Stored` or by a class beside it, and from it

```
s.Holds(span, n, a) → span.window(part.offset, part.layout.size + part.offset) = part.codec.write(part.get(a))
```

for a `Part` of the record. `laid` can prove the first per declaration
from its fields'. With it the SHA-256 statement ends at the span's bytes:
`span.window(SHA256_DIGEST_AT, 32 + SHA256_DIGEST_AT) = Sha2::digest(message)`.

## Log

- 2026-11-14: Built the part of it SHA-256 needs. `Stored::Exact` (`stored.hthr`) is the converse of `round` as a property beside the record, with `exact_be_bytes`, `exact_aligned` and `exact_array` (elements a size apart); `Stored::window_get` and `Part::window_of` (`part.hthr`) take it to the bytes where a part of a held value lies. `Sha256::digest_bytes` and `Sha256::linked_digest` (`sha256_stream_agreement.hthr`) are the statement on the span. Not built: exactness of `then`, `map`, `record` and little-endian words, and `laid` proving it per declaration; a part's own codec was enough here, so those wait for a customer.
