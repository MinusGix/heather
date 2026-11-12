---
title: A sequence's join has the kernel work out the liveness of everything after it
status: open
labels: [performance,native,compiler]
area: heather-in-heather
created: 2026-11-11
updated: 2026-11-11
---

Found after [[native-certificate-layout-per-item]] took the layout out of the emission statements of a native tool's certificate. What was left of them on `sort_tool` (14.3 M evaluator steps over 260 statements) split evenly: the parts stated by one `refl` (127, 7.7 M), and the joins of a sequence's two parts (106 `Stmt::emits_then_of`, 6.5 M). The joins of a branch or a loop are about 5 thousand steps each; a sequence's averaged 60 thousand.

## Why a sequence's join is dear

`Stmt::emits` hands a sequence's first part the set live after it, which it computes: `rest.live_with(homes, first.carried(rest, homes, out), out)`. The certificate states the first part over that set as a literal (`{p}_o_#`), so to accept the join the kernel evaluates the computed one, which is the liveness of everything after the first part: a walk of the rest with a union and a difference of id lists at every node. `carried` asks for the same set up to twice more where the rest starts with a call (`Stmt::pair_known`).

So a join costs as the length of what follows it, up to the next loop (a loop's live set is read from the homes): on `sort_tool`, measured with every leaf its own part, 18 thousand steps with one leaf after it, 28 thousand with five, 60 to 80 thousand with twenty to thirty. A straight run of n statements costs as n squared. This, and not the size of the live sets, is the term that grows with real programs: the sets themselves are small (`sort_tool`'s 260 live-out sets have a median of 14 ids and a largest of 23; `head_n_tool`'s a median of 5).

The allocation's check has already found every one of those sets. `Stmt::checked` returns the set live before a statement, the certificate states it a part at a time (`{p}_ck_#`), and `Stmt::checked_sound` says it is `live_in`.

## Done here

`Stmt::emits_then_checked` (native_compile_correct): a sequence's join that takes the set live between its parts from the check's verdict on the rest, where the rest does not start with a call or an exit (`reads_known` is `False`, so `live_with` is `live_in` whatever is known: `Stmt::live_with_plain`). `write-elf` reads which rests those are (`{p}_plain`, one read) and states the allocation's check before the main statement's emission, so its joins can cite it. A join whose rest reads known words, and the joins inside a procedure's body (whose check is not stated a part at a time), stay on `emits_then_of`.

Evaluator steps, cold `write-elf`, after the layout fix and with this: `sort_tool` 49.03 M to 44.17 M, `tac_tool` 31.98 M to 28.64 M, `head_n_tool` 16.59 M to 15.99 M. `sort_tool`'s emission statements go from 14.35 M to 9.48 M, their time in the kernel from 4.66 s to 3.65 s.

## Left

1. **Joins whose rest starts with a call or an exit.** `live_with` there is `live_head` of the rest's first statement over the set live after that statement, which the check also has (the verdict on the rest's own rest). It needs a second lemma and `carried` stated from the check's sets (`pair_known` asks for `rest.live_in` and `rest.live_with`).
2. **Inside a part.** A part of up to eight leaves is one `refl`, and `emits` computes the set between each pair of its statements the same way. Measured by stating every leaf alone, this is about 1.2 M of the parts' 7.7 M steps on `sort_tool`: small now, quadratic in the part size, which is why the part size cannot grow.
3. **What a part knows as it starts** (`{p}_kn_#`) is spelled `left().carried(right(), …)` from its parent, and worked out in each statement that names it.
4. **The fork's reads** evaluate `emits` for each part too, and each live-out set from its parent's (`live_with` again). They share sessions, so a parent's set is kept, but a session ends every two million steps.

## The shape that would retire all four

Emission that reads its sets and does not compute them: the sets live between statements, and what is known where each starts, as notes beside the statement tree (one entry a sequence), supplied by the untrusted side. `Stmt::emits` becomes the notes' reader, and one theorem says the reader over the notes the check computes is today's `emits` (the pattern of `Stmt::checked` and `Stmt::checked_sound`). The check already makes one pass that finds every set; it would return them as the notes. Then a part of any size evaluates no liveness, the joins are all as cheap as a branch's, and the fork's reads read the same notes. It is a change to `emits`' signature, so to `native_compile_correct` and the files around it, which the one-compiler round's open pull request (#551) is rewriting: to be done on top of that.
