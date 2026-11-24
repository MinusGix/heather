---
title: A hash table runtime fn proved to be a finite map
status: closed
labels: [native,runtime,data]
area: heather-in-heather
milestone: [nh-heap]
created: 2026-11-24
updated: 2026-11-24
---

The ledger's fixed-capacity word map (`PortMap`,
`lib/_tests/native/runtime/runtime_ports_tests.hthr`) is compiled with its
agreement, but nothing says it is a map. docs/native/rung2-spans-design.md
§7: since a `runtime fn` is the Heather function its agreement certifies,
its specification is a theorem about that function, against `assoc.hthr`'s
laws, with no `datarepr` between.

## Scope

- `abs(m)`: the association list of the occupied slots; `inv(m)`: every key
  reachable from its home slot without passing an empty one, distinct keys,
  `count` the occupied slots.
- `insert` keeps `inv` and, on its success arm, agrees with `assoc_set` at
  every key's lookup (not as lists: `assoc_set` shadows by consing); `Full`
  only when `count = cap`. `get` is `assoc_get` under `inv`.
- Deletion by backward shifting, keeping `inv`.
- Then, over [[runtime-arena-in-span]], a table that rehashes into a window
  of twice the capacity.

The table belongs in the library (a module under `lib/native/runtime/` or
`lib/std/data/`), with the ledger's rows citing it.

## Done when

The three laws (`get` after `insert` at the key and at another, `get` after
`remove`) are theorems at every table satisfying `inv`, over the compiled
functions; a negative control (a probe that skips the home slot) is refuted
by a `¬` theorem at a closed table.

## Log

- 2026-11-24: Done at the ledger's capacity (four slots). The table moved to
  `lib/native/runtime/word_map.hthr` (`WordMap`, from the ledger's
  `PortMap`: `insert_at`/`insert`, `find_at`/`get`, and new
  `shift_at`/`remove_at`/`remove`, deletion by backward shifting); its
  specification is `lib/native/runtime/word_map_laws.hthr`, every theorem
  over the compiled functions themselves. The ledger's rows run the library's
  table (plus a removal run) and cite the laws (`port_map_get_meant`: the
  bytes' lookup at a table with the invariant is `assoc_get`).

  Proved (`WordMap::`): `get_is` (under `WordMapInv`, `get` is
  `abs().assoc_get(k).unwrap_or(0)`); `insert_inv`, `insert_full`,
  `insert_get` (every lookup is `assoc_set`'s), `get_insert_same`,
  `get_insert_other`; `remove_spec` (invariant kept, every lookup
  `assoc_remove`'s), `get_remove_same`, `get_remove_other`; `empty_inv`.
  Negative controls: `skipping_home_is_wrong` (a probe from the slot after
  home is refuted at the closed table holding key 9) and
  `shift_at_full_is_wrong`.

  **A decision this round made: the table keeps one slot empty.** Insert
  answers full when three of the four slots are taken, not four (the issue
  said "`Full` only when `count = cap`"). Backward shifting (Knuth's Algorithm
  R) stops at an empty slot; at a full table it runs out of slots first, and
  `shift_at_full_is_wrong` shows a closed full table where removing key 2
  leaves key 4 stored twice. The invariant's `room` (`count < 4`) is what
  every probe's termination and the shift's proof use. With rehashing the
  full answer goes, and the load factor keeps the slot
  ([[runtime-hash-map-rehash]]).

  Cost (dogfooding-plan §5.6): 59 program lines, about 1,160 proof lines
  (twenty to one); removal alone about 450 for its 25. Where it went:
  - every probe is an induction applied by hand, one stated lemma per case,
    because the principle's binders carry no test names
    ([[runtime-fn-induct-test-names]]);
  - the slot word arithmetic `bv_omega` did not read: `band(3)` as `% 4`, a
    borrowing `j - i` modulo four, `omega`'s overflow at `2^64`
    ([[bv-omega-word-arithmetic-modulo]]);
  - the module first had no branch equations at all, silently, for want of
    `import logic;` ([[branch-equations-silent-without-logic]]);
  - one inline `omega` in `adds_next`'s nested λ took four minutes to check
    (2·10⁹ substitution nodes); the same facts in a lemma over bare numbers,
    milliseconds (proof-patterns §3's rule, met again);
  - a defined distance was an atom to `omega` and cost the kernel its fuel
    against its unfolding, and `refl` between `insert` and its probe ran out
    of fuel ([[arithmetic-definition-opaque-at-open-arguments]]);
  - `omega` refused a context holding a generated name
    ([[omega-unspellable-local-in-scope]]).
  The slot-level framing paid off: a table's lookups are read off its slots
  (`abs_get_at`, `abs_get_none`, `abs_get_same` over `Moves`), so each
  operation's agreement with `assoc.hthr` is a statement about which slots
  changed, and the invariant proofs mostly passed first time.

  Residue: the capacity as a parameter and rehashing,
  [[runtime-hash-map-rehash]].
