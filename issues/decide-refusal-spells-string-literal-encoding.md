---
title: A decide refusal at a string goal spells the literal's encoding
status: closed
labels: [elaborator,diagnostics]
area: language
created: 2026-10-25
updated: 2026-10-26
---

Found while giving the string refusals their reasons
([[library-tests-as-theorems]], round 3). `decide` at a goal it has no closed
decision for names the resolved goal, and at a string literal that name is
the literal's kernel encoding, not its source spelling:

```heather
import logic; import bool; import nat; import list; import char; import string;
theorem bad(s: String): s = "hi" { decide }
```

is refused with `the kernel rejected `bad`: NotConvertible. `decide` resolved
`Decide<s = String(Cons(fst[0,0](El[0](«Σ[0,0](«sEq»[0](«Nat»; 14; 14)). …`
to `string::String::Decide#Eq`, whose decision here is not `Inl` …`. The same
refusal at `List<Nat>` (`theorem bad(xs: List<Nat>): xs = Cons(1, Nil) {
decide }`) spells the goal as written, so the gap is the character literal's
encoding (a `Char` carries its `scalar` witness) reaching the goal printer
without a surface spelling.

The refusal is right; only the message is unreadable. A fix would spell the
goal from the elaborated surface term, or render a `Char`/`String` value as
its literal. `crates/elab/tests/lib_std_string.rs`'s
`decide_proves_only_closed_true_goals` pins the reason, not the spelling, so
it keeps passing either way; tighten it to the goal text once fixed.

## Log

- 2026-10-26: Fixed. The diagnosis above was half right: the character literal spelled as `ofNat(104, decide_yes(refl))`, but the wall was the *list literal*. `[…]` elaborated to the weak head of the protocol's conversion, `Cons(fst(v), fold(snd(v)))` over the literal's vector, so any list literal in a goal — `xs = [1, 2]` at `List<Nat>` too — printed the vector and the unreduced fold, and the display path may not reduce to recover it. `check_collection_literal` now builds the constructor spine out once, at elaboration (`collection_literal_spine` in `crates/elab/src/literals.rs`): each `Wf` child reduced to its weak head, element projections read off the literal vector, nothing keyed on the container, bounded per element, iterative. The speller then writes a `char::ofNat(n, bool::decide_yes(…))` call as `'h'`, a `string::String` over those as `"hi"` with the lexer's escapes, and a standard `List` spine as `[1, 2]` (reading flavour only: `[…]` never infers, so the source flavour keeps `Cons`). `decide_proves_only_closed_true_goals` now pins `Decide<s = "hi">`; `a_spelled_literal_keeps_its_escapes` and `lib_std_list`'s `a_refused_goal_spells_its_list_literal` cover escapes, empty literals, open elements and an open tail.
- 2026-10-26: The readable spellings exposed one `omega` hole: its source spelling qualified a global by a module the file does not import (`x86_64_layout::near_rel` in `native_compile_calls`), which did not re-parse. The speller's qualified flavour now declines such a node, so `omega` abstracts it as before.
