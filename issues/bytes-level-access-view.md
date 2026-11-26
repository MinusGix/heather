---
title: The bytes level's loads and stores name the view they use; the loop's back edge; the comparison again
status: open
labels: [native,function-ir,memory,ownership]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-26
updated: 2026-11-26
---

The bytes level's word ids have a view at every width (FunctionIR's valuation inside `Compute`), and views at different widths are independent in general. The lowering holds an id at one kind. Before this round a `Store` and a `Load` silently meant the 64-bit view and the kind `Word`. So a `ByteSwap(32)` result could not be stored by a four-byte store, and a four-byte load could not feed a `ByteSwap(32)`. That refused the four SHA-256 buffer rows and `scan_tokens` ([[bytes-level-translation]], item 4, cause 3; `docs/language/ownership-design.md` §17.8).

The coordinator's ruling, built here:
- `Store(bytes, view, place, value)` writes the low `bytes` bytes of the value's view at width `view`. The lowering asks for the value at that view's kind (`Word` at 64, `Narrow(32)` at 32).
- `Load(bytes, view, output, place)` binds the output at every width, as before, and the lowering records the stated kind.
- Validity refuses a view narrower than the access, and any view but 64 and 32.

Beside it:
- The plain loop's back edge jumps straight to the head where the continuing arm moves nothing.
- The translation drops a dead reference `Move`.
- The comparison is re-run over every export row and the gates.

## Log

- 2026-11-26: **The check the coordinator asked for first.** Do narrow-held values cross a call, a loop's state or an answer? No, by construction, in both pipelines:
  - In FunctionIR, every boundary is a 64-bit word port: `Call` (`word_ports`), `Loop` inputs/next/outputs and the bound, `Lend`, `Function.parameters` and `result`.
  - The old lowering moves a port with `File::move_outputs` → `file.place(Held(id, Kind::of_width(64)))`, an exact kind lookup with no widening from `Narrow(32)`.
  - At the bytes level, `Typed` appears only at calls, loops and a routine's parameters and results, all taken at width 64.
  - A `Branch` joins by `File::meet`, per register, which keeps a narrow kind only where both arms agree.
  So `Typed` carries no width; the per-access statement suffices.

  **Item 1, the access view, landed** (ffbebd2).
  - The language (`bytes_level`):
    - `Store(bytes, view, place, value)` writes `low_bytes(bytes, view_word(words, view, value))`, where `view_word` is the 64-bit word at 64 and the `view`-bit view resized otherwise.
    - `Load(bytes, view, output, place)` keeps its meaning: it binds every width.
    - `Instr::check` asks `access_ok = width_ok ∧ view_ok`. `view_ok` is the 64-bit view at any width, or the 32-bit one at four bytes or fewer. So it refuses a store from a view narrower than its bytes, a load held narrower than what it read, and any other width.
  - The lowering (`bytes_level_lower`):
    - `view_kind(view)` is `Word` at 64 and `Narrow(view)` otherwise.
    - The store emitters look the value up at `view_kind(view)`; `view_word_held` turns its `Rep` into the view's word.
    - The load emitters record `Held(output, view_kind(view))`. `Loads` states the output's `Rep` at that kind, and `written_leaves` takes the kind.
    - `load_holds` goes through a new stage lemma `load_view_held`: at 32, the word read from four bytes or fewer is its 32-bit view widened (`word_of_bytes_round`, from `word_of_few`). `store_holds` uses `view_word_agrees`.
  - Restated with the view: the scope lemmas, the canonical form, renaming, the routines' walk (`Instr::emit_grows`) and the compare's `instr_shown`.
  - The translation: byte accesses at the 64-bit view, and a wide access of n bytes at its `8n`-bit view (`wide_view`), which is `Narrow(32)` at four bytes and `Word` at eight, as the old lowering's `StoreSize::kind` and `WideLeaf`.
  - The theorem's node level (`byte_store_runs` and the leaf lemmas) needed only the new constructor arity: `view_word(_, 64, _)` reduces to the word.
  - Probes:
    - `swap_store_*` and `load_swap_*` (lower_tests): the two smallest programs, each valid, lowered, and with its `emit_emits` theorem.
    - The control `swap_store_wide_refused`: the same store from the 64-bit view is refused by the lowering, since only `Narrow(32)` holds the swap's result. Validity accepts it.
    - The views validity refuses (bytes_level_tests): `store_past_view_invalid`, `load_past_view_invalid`, `store_other_view_invalid`.
    - A narrow-held load answering its word.
    - Every existing probe keeps its answer at the 64-bit view.
  - Not in the handoff's list: `written_leaves`, `word_of_four` (now `word_of_few`), the canonical and renaming step lemmas, the compare's instruction encoding, and `cut_store_unprovable`'s `Stores`.
  - Verification:
    - `scripts/fmt --check` and `scripts/lib-closures` are clean, and `scripts/linked --check` is unchanged.
    - `HEATHER_PR_NATIVE=all scripts/test --pr`: `== suite: 4139 passed, 0 failed, 3 ignored ==`.
    - The inherited head's baseline run reported 4138/1. Its one failure was the library gate, which read these modules while they were being edited; every other target passed.
