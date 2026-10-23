---
title: The u^δ rule rescopes a binding's Δ and type once per occurrence: what is left of shift_global after the lazy bodies
status: closed
labels: [kernel,conversion,performance]
created: 2026-09-18
updated: 2026-09-19
---

The `u^δ` / `U^δ` conversion rule rescopes the binding's declared Δ and its type into the ambient Ψ **once per occurrence** (`conv.rs`, counted by `global_ref_rescopes`), and since [[refl-theorem-step-cost]] made definition *bodies* lazy that is the whole of what `shift_global` still costs: 38.2 M of the showcase's 47 M remaining rescoped nodes, over 4.77 M occurrences, in a cold width-one `heather check docs/showcase/calc_parser.hthr` (2026-09-18). The heaviest items after that round are exactly the ones with no body unfolds at all: `parser_primitives::complete_post` 6.74 M nodes at 929,580 refs, `calc_parser::Grammar` 2.23 M at 209,370 refs and no unfolds, `parser_contracts::Certified` 1.96 M at 94,025, `calc_parser::close_body` 2.57 M at 528,714.

Unlike a body, this rescoping *is* cacheable as it stands: it is `shift_global(v + 1)` of a **binding's** ctx and type — a function of the index and the ambient Ψ alone, not of the occurrence or of the δ that occurrence carries, which is exactly the argument `reduce::BodyCache` already rests on. So the first candidate is a second slot in that cache (or a sibling of it) keyed by `GlobalVar`, owned beside the Ψ it belongs to and rebuilt when a telescope push changes Ψ. The second candidate is the same trick the bodies got: compare the substitutions without materializing the declared context at all, since only its length and entry types are read. Measure before choosing; the memo is the cheap one and the round should say what it bought. Related: [[refl-theorem-step-cost]], [[simulate-conversion-cost]].

## Log

- 2026-09-19: Premise re-measured on the current tree (7b03df9, desktop, release,
  width one, `HEATHER_VALUE_METRICS=1`, cold `--cache` over
  `docs/showcase/calc_parser.hthr` with `-L lib/std -L lib/std/parser`; 59 s wall,
  34.2 s gate), because the issue's numbers came from a dirty tree two commits
  back. It holds, and the shape is better than the issue knew.

  Whole run: **38,815,029 rescoped nodes over 4,772,510 occurrences**, 8.13 nodes
  per occurrence, against 3,161 body unfolds — so the bodies really are gone and
  this is the remainder. Heaviest, with the column that decides the design:

  | item | gate ms | rescope | refs | unfolds | nodes/ref | check_terms |
  |---|---|---|---|---|---|---|
  | parser_primitives::complete_post | 8367.7 | 6,740,031 | 929,580 | 42 | 7.3 | **1** |
  | calc_parser::close_body | 2661.2 | 2,571,586 | 528,714 | 6 | 4.9 | **1** |
  | calc_parser::number_grammar | 2241.3 | 2,270,148 | 410,587 | 4 | 5.5 | — |
  | calc_parser::Grammar | 1019.8 | 2,234,390 | 209,370 | **0** | 10.7 | 17 |
  | parser_contracts::Certified | 666.4 | 1,959,955 | 94,025 | **0** | 20.8 | 14 |
  | calc_parser::factor_body | 868.9 | 1,508,272 | 217,069 | 6 | 6.9 | — |
  | calc_parser::expr_body | 895.7 | 1,508,252 | 217,005 | 6 | 7.0 | — |

  `check_terms` is the one the issue did not have: the two heaviest items make
  929,580 and 528,714 of these rescopes inside a **single** `check_term`, and the
  whole run's 4.77 M occurrences fall in 2,336 gate calls — ~2,043 per call. So a
  memo keyed by `GlobalVar` and living for one gate call hits ~99.99 %, and the
  issue's first candidate is the right one to price first. It is also nearly free
  to build: `reduce::BodyCache` is already a `GlobalVar`-indexed `Vec` owned beside
  its Ψ, rebuilt by `push_tele` under the soundness argument this rescoping shares
  (`typing.rs`'s `a_telescope_push_rebuilds_the_body_cache`), and all four sites —
  `conv.rs:1133`/`:1774`, `typing.rs:1121`/`:1313` — already carry that field.

  What is *not* yet measured is the price per node at these sites. The ~150 ns/node
  figure in [[refl-theorem-step-cost]] came from rescoping large shared body
  graphs; these are 8-node walks where the per-call overhead (the `LocalCtx`
  rebuild, the `Rc::new` for the type, the bounds-memo skip checks) may dominate
  instead. The memo is ~40 lines, so building it *is* the price experiment, and its
  result is what should decide whether the second candidate — never materialising Δ
  at all, by threading `value::Env::gshift` through `Conv::subst`/`apply_subst_ty`
  the way `docs/lazy-global-offset-design.md` threads it through bodies — is still
  worth a round. Round in flight against this entry.
- 2026-09-19: Fixed, by memoizing the signature. `reduce::BodyCache` became
  `reduce::GlobalCache` — same owner, same Ψ lifetime, same `push_tele` rebuild —
  with a second `GlobalVar`-indexed slot holding the rescoped **signature**
  (`Sig { ctx: LocalCtx, ty: Option<Rc<Type>> }`), read by all four sites
  (`conv.rs` `ty_ne`/`tm_ne`, `typing.rs` `Type::GlobalTy`/`Term::GlobalTm`). The
  two kinds share one key space safely because the binding form at an index is
  fixed and every site checks it before filling, so a `Ty` binding's `ty: None`
  can never be read as a `Tm`'s. New counter `global_sig_rescopes` (`sigs` in
  `scripts/timings`) counts **fills**; `global_ref_rescopes` still counts
  occurrences, so the pair is the memo's hit rate.

  Measured on furnace (quiet box, 8 OCPU, release, width one,
  `HEATHER_VALUE_METRICS=1`, cold `--cache` over `docs/showcase/calc_parser.hthr`
  with `-L lib/std -L lib/std/parser`), three **interleaved** before/after samples
  from two binaries built in the same script, whose provenance the script asserts
  behaviourally — each binary is run on `lib/std/num/nat.hthr` and its `--timings`
  header checked for the new column, and the two md5s compared:

  | | before (3 samples) | after (3 samples) | delta |
  |---|---|---|---|
  | total | **43.50 s** (43.75, 43.25, 43.50) | **41.12 s** (40.49, 41.12, 41.65) | −5.5 % |
  | kernel gate | **26.70 s** (26.71, 26.53, 26.70) | **24.32 s** (24.11, 24.32, 24.73) | **−8.9 %** |
  | `shift_global_nodes` | 38,815,029 | **17,551,478** | −54.8 % |
  | `global_sig_rescopes` | 0 | **12,263** | — |

  The before and after ranges are disjoint on both rows. Every other counter is
  identical to the unit across all six runs: `global_ref_rescopes` 4,772,510 (so
  demand is unchanged and the 12,263 fills are a **99.74 % hit rate**),
  `delta_body_rescopes` 3,161, `conv_misses` 206,980, queries 14,738,460,
  `eval_steps` 4,802,145, `eval_delta_steps` 232,525, `check_terms` 1,174. The
  secondary effect [[refl-theorem-step-cost]] saw — better `Rc` sharing sending the
  identity-sensitive shortcuts down a different route — did **not** happen here;
  nothing moved, so nothing needed locating.

  Per item (median gate ms, rescoped nodes, fills against occurrences):

  | item | gate before → after | rescope | sigs | refs |
  |---|---|---|---|---|
  | parser_primitives::complete_post | 6594 → **5547** (−15.9 %) | 6,740,031 → 97,813 | 34 | 929,580 |
  | calc_parser::close_body | 2188 → **1771** (−19.1 %) | 2,571,586 → 168,053 | 49 | 528,714 |
  | calc_parser::whole_grammar | 125 → 110 (−12.0 %) | 473,843 → 336,689 | 26 | 36,126 |
  | calc_parser::Grammar | 820 → 727 (−11.3 %) | 2,234,390 → 1,290,053 | 375 | 209,370 |
  | calc_parser::checked_expr | 857 → 793 (−7.5 %) | 1,256,067 → 817,137 | 396 | 186,239 |
  | calc_parser::factor_body | 726 → 698 (−3.9 %) | 1,508,272 → 499,964 | 46 | 217,069 |
  | calc_parser::number_grammar | 1830 → 1787 (−2.3 %) | 2,270,148 → 691,883 | 35 | 410,587 |
  | parser_contracts::Certified | 503 → **517 (+2.8 %)** | 1,959,955 → 1,288,658 | 174 | 94,025 |

  `Certified` is the only item that got slower, by ~14 ms on a 24 s run, and it is
  one of the two with the worst fills-per-occurrence ratio — 174 fills for 94,025
  refs, i.e. the memo has the least to amortize exactly where a fill is largest
  (~7,400 nodes). Not chased.

  **A note on how these numbers were obtained, because two earlier attempts were
  wrong and both failure modes are cheap to repeat.** (1) A desktop measurement of
  the same pair, taken while a game held ~254 % CPU, read the gate win as −2.9 %
  and reported `calc_parser::expr_body` at **+35 %** over three interleaved samples;
  on the quiet box `expr_body` is −1.3 % and the win is three times larger. A
  consistent multi-sample anomaly with every work counter identical was load, not
  locality. (2) On furnace, `cargo build` reused a **stale** binary: the checkout is
  an rsync of the working tree, so source mtimes are the local ones, and against a
  `target/` persisted on the `/work` volume cargo judged the tree fresh — two
  successive builds across a `patch -R` produced byte-identical binaries and a
  before/after pair that differed by noise alone. `find crates -name '*.rs' -exec
  touch {} +` before each build fixes it, and the behavioural provenance assertion
  above is what caught it. A furnace before/after pair without both is worthless.

  **Where the remaining 17.55 M nodes are, and what that says about the second
  candidate.** The occurrence axis is now closed — 4.77 M occurrences collapse to
  12,263 fills — so what is left is **Ψ-multiplicity × signature size**. A fill is
  large because these declared Δ/types are large (`Grammar` ~3,440 nodes per fill,
  `Certified` ~7,400), and a binding fills more than once only because conversion's
  `push_tele` (layer-m `CtxPi`/`TyPi`, recursor specs) must rebuild the cache:
  `checked_expr` 396 fills, `Grammar` 375, `Certified` 174. Those are exactly the
  items whose rescope column fell only 34–42 %, and for `Grammar` the arithmetic
  closes exactly (375 × 3,440 ≈ its remaining 1,290,053). Splitting the remainder:
  ~12 M nodes of signature, ~5.5 M of body (the 3,161 eager rescopes of the
  rewriter path, which the second candidate does not touch).

  So the ceiling for threading `value::Env::gshift` through
  `Conv::subst`/`apply_subst_ty` is ~12 M nodes. This round priced a node at
  **~112 ns** (21.26 M nodes bought 2.38 s of gate) — not the 40–45 ns a
  load-contaminated desktop run suggested — which puts that ceiling at **~1.3 s of
  a 24.3 s gate, about 5 %**: the same order as what this round just delivered, not
  the under-2 % the first estimate implied. It is therefore still a live lever, but
  a modest one that reaches only the value-domain sites (both `typing.rs` sites stay
  on the memo regardless) and needs its own adequacy argument. The remainder — that
  candidate, and a cheaper second one that attacks the **multiplicity** rather than
  the walk, since 375 fills for one binding is the surprising number and not 3,440
  nodes per fill — is filed as [[signature-rescope-multiplicity]], where
  [[kernel-acceleration-policy]] says the reason to spend the round should be the
  design one: that the kernel never copies a declared context. This issue's own
  defect, the per-occurrence rescoping, is fixed, so it closes here.

  Soundness: the cache's whole correctness rests on `push_tele` rebuilding it, so
  `typing.rs` gained `a_telescope_push_rebuilds_the_signature_cache` beside the body
  one, pinning both halves of a signature — the declared type (index 1 is `Nat`
  before a push and `Unit⁰` after) and the declared Δ (`·` before, `(·, x : Nat)`
  after, so a length-zero substitution must stop being accepted). Verified as a
  mutation, independently of the implementer: making `push_tele` share the parent
  cache reddens **both** tests, and restoring it greens them.
