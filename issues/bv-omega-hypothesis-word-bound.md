---
title: bv_omega does not bound a word that appears only in a toNat hypothesis
status: closed
labels: [tactics,bitvec]
area: tactics
created: 2026-11-14
updated: 2026-11-14
---

With `inside: j.toNat() < mn.toNat()` in scope, `bv_omega` does not prove
`(j + 1).toNat() = j.toNat() + 1`: its overflow side goal is
`j.toNat() + 1 < 2^64`, and the counter-model it reports sets
`mn.toNat() = 2^64`. The word `mn` occurs only inside the hypothesis, so
the tactic never gives Omega `mn.toNat() < 2^64`.

Met in `Sha256::absorb_from`
(`lib/native/crypto/sha256_stream_agreement.hthr`), where the loop's bound
is the last value the counter may reach, so `BitVec::toNat_add_below`
(which wants the sum strictly below the bound) does not apply either. The
proof binds the fact by hand:

```
let inside: (j.toNat() < mn.toNat()) = omega;
let top = BitVec::toNat_lt_pow(64, mn);
let next: ((j + 1).toNat() = j.toNat() + 1) = bv_omega;
```

**Wanted:** every `toNat` atom of a fixed-width word that reaches Omega,
from the goal or from a hypothesis it reads, carries its bound. The
`top` line then goes.

## Log

- 2026-11-14: 2026-11-14: fixed by PR #632: omega states every word atom's range at a literal width, from the goal or a fact, so bv_omega's side condition gets mn.toNat() < 2^64. The top line in Sha256::absorb_from is gone ([[omega-opens-closed-terms]]).
