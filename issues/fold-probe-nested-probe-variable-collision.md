---
title: Give each fold probe fresh variables (nested probes prove False)
status: open
labels: [kernel, soundness]
area: kernel
code: crates/kernel/src/eval/probe.rs:68 @ 01de61c
created: 2026-11-15
updated: 2026-11-15
---

The fold classifier probes a step closure by applying it to neutral
variables at fixed reserved levels (`eval/probe.rs`: `PROBE_IH = u32::MAX - 8`,
`PROBE_K`, `PROBE_X`; `eval/transduce.rs` defines the same `PROBE_IH` and
`PROBE_K` values again). The comment's argument, "Γ is never this deep",
covers real contexts but not a probe running inside another probe. When the
outer probe's evaluation reaches a fold over a run, `classify_step` probes the
inner step, whose environment captured the outer probe's `ih`. That variable
sits at the inner probe's own `PROBE_IH`, so the inner probe reads it as its
own induction hypothesis and classifies the fold wrongly.

Proof of `False` with `heather check --deny-axioms` on master 01de61c:

```
import logic; import bool; import nat; import list;

fn const2(a: Nat, b: Nat) → Nat { a }
fn inner(o: Nat, n: Nat) → Nat {
    match n { Zero => Zero, Succ(k) => const2(o, inner(o, k)) }
}
fn outer(n: Nat) → Nat {
    match n { Zero => 7, Succ(k) => inner(outer(k), 5) }
}

theorem inner_succ(o: Nat, k: Nat): inner(o, Succ(k)) = o { refl }
theorem outer_seven(n: Nat): outer(n) = 7 {
    match n {
        Zero => refl,
        Succ(k) => trans(inner_succ(outer(k), 4), outer_seven(k)),
    }
}
theorem wrong(): outer(3) = 0 { refl }   // accepted
fn is_zero(n: Nat) → Bool { match n { Zero => True, Succ(_) => False } }
theorem boom(): False {
    let seven_zero: (7 = 0) = trans(sym(outer_seven(3)), wrong());
    let no: (False = True) = cong_fn<Nat, Bool>(λ n => is_zero(n), seven_zero);
    absurd(sym(no))
}
```

The kernel also refuses the true `outer(3) = 7` by `refl`.

Confirmed as the cause by a local experiment (not committed): offsetting the
reserved levels by the probe nesting depth makes `wrong` refused and
`outer(3) = 7` accepted.

Fix direction: a probe variable no context and no other probe can hold, e.g.
a `Head::Probe(id)` with a fresh id per probe (or per arena counter), read
back only by the probe that made it. `eval/transduce.rs`'s `probe_scaled`
calls `classify_step` from inside a transducer probe and needs the same
treatment. Add the repro to `lib/_tests` as an `expect-error` probe on
`wrong`.

Found by the kernel comment audit (2026-11-15).

## Log

- 2026-11-15: filed.
