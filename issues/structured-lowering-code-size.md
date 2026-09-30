---
title: Tighten the structured x86 lowering's code size
status: closed
labels: [compiler,x86,native,perf]
created: 2026-09-29
updated: 2026-09-30
---

The structured x86 lowering emits code about three times larger than it
needs to be. Measured on `field_line` (docs/native-wc-design.md §5.1): a
restoring step or a mark is 68–84 bytes where about 20–30 would do, so
`field_low` is 1,911 bytes and `field_high` 2,792. What costs the bytes:

- a comparison materialises its bit (`movabs 0` into a register, `setb`,
  `mov`, `test`) and branches on the test, instead of branching on the
  flags the `cmp` set;
- a copy is `movabs 0; or` (13 bytes) instead of `mov` (3);
- every immediate is a 10-byte `movabs`, including zero and small weights;
- a doubling is `mov`/`add`/`mov` through RAX (9 bytes) rather than one
  `add r, r`, so `raise32` is 288 bytes.

Certificate cost follows the node count, so a tighter lowering also makes
certification cheaper (field_low 36 s, field_high 65 s at width one).

Not blocking: [[native-wc]] lifted the one-page program limit instead
(design §8.4). The fix is a set of new certified lowering shapes (flag
branches, register copies, sign-extended immediates, in-place two-operand
arithmetic), each with its own execution lemma.

## Log

- 2026-09-29: Design drafted: docs/structured-lowering-code-size-design.md (decisions open, §6). V1 measured the words as they lower today: field_low 424 instructions (97 movabs, 138 mov), field_high 603. A mark is 68 bytes where 19 would do, a place 84 where 18–25 would. Three capabilities, each one cause: F branches on the comparison's flags through a condition-code family (JumpIf/JumpIfNear over the manual's 16 cc's, absorbing JumpZero/JumpZeroNear/JumpSignNear) and a CodeBranch generalised over a BranchTest, with CMP inside the branch; P lets a result take a dead unprotected input's register and makes the passthrough arm empty (CodeWhen); I adds sign-extended short immediates (83/81 /0 /5, B8+r imm32) and xor for zero. Estimate: field_low about 600 bytes, field_high about 800. Shifts, a shared formatter copy and constant folding are out of scope.
- 2026-09-29: Decisions taken with the user, all as recommended (design §6). Probes V2–V5 done (§7.1). V2: CF/SF/OF after CMP are the library's comparisons by refl at open operands; the 16-code table and negation lemma check. V3: the condition-code family is definitionally JumpZero/JumpZeroNear/JumpSignNear at E and S (bytes and RIP, refl). Clients only construct these forms, so they become functions over the family and no client changes. V4: in-place results need a selector change only (consumable inputs), no new lemma kind. V5: a helper's constant arguments are propagated as Const nodes into every region that uses them, so a place's false arm reloads its threshold. That is new slice F′, after F. Slice F is next.
- 2026-09-29: Slice F landed (design §2.4): the condition-code family (b71da604), CodeBranch over BranchTest (60958932), and the fused lowering. field_low 1,911 → 1,534 bytes, field_high 2,792 → 2,225. F′ (a threshold loaded once, carried into the arm) is next, then P, then I.
- 2026-09-30: Slice F′ landed (design §2.5): where a fused comparison's constant is loaded again by an arm, the reflector passes the prefix's port to the arms instead (share_compared_constant), so the place's false arm reads the threshold's register. field_low 1,534 → 1,374 bytes, field_high 2,225 → 1,945. P is next, then I.
- 2026-09-30: P, first half (design §3.1): results in place. select threads a consumable set (input registers dead after a region and unprotected); lower_dag_consuming owns them like temporaries until their last use; a Compose places a lone result where the region's goes. field_low 1,374 → 1,038 bytes, field_high 1,945 → 1,507. The passthrough arm is still a BitOr(Const 0, x) copy; decided with the user (design §6 Q6, reopening Q3): a FunctionIR Move node, which lowers to nothing in place. That and CodeWhen are P's second half.
- 2026-09-30: P, Move node landed (design §3.2): FunctionIR Move(width, output, source); an input returned unchanged is a Move, lowered to nothing where its source dies in the join's register. field_low 1,038 → 778 bytes, field_high 1,507 → 1,117. CodeWhen deferred until after I, to be weighed against the acceptance numbers.
- 2026-09-30: Round closed. Slice I landed (85d9f4d4, design §4.1): AddRI8/AddRI32 and constant folding into ADD. field_low 637 bytes and field_high 868, 33% and 31% of 1,911 and 2,792 (acceptance ≤40%). scripts/perf ab --base 08d77938 --whole-tree (new mode, 82ae72b1) on the wc build: counters down 14–21% (decls_gated −16.8%, eval_steps −16.9%, conv_misses −18.4%), max RSS −12%; seconds −15% wall, −17% gate with samples separate, but the box was loaded (loadavg 7.6), so the seconds are indicative only. One item regressed: field-prints-gate-after-lowering-round. Deferred: structured-lowering-codewhen, helper-body-interface-trim.
