---
title: Claims about emitted code compose without naming positions in the program
status: open
thread: Make compiler correctness proofs elegant
labels: [native,design,proofs,program-logic]
area: heather-in-heather
milestone: [hih-program-logic]
created: 2026-11-16
updated: 2026-11-17
---

Every lemma about emitted code (`Target::goes_*`, `lib/native/native_compile_*.hthr`) is a weakest-precondition step written against positions in the whole program: it takes `within: <the code after this piece>.Within(t.program)` and `next: t.GoesR(prog_len(<end>), tree, q)` and answers `t.GoesR(prog_len(p), tree, <pre>)`. A proof that composes three pieces rebuilds each intermediate program, derives where each one sits, and names both predicates of every weakening with their binder types. `Target::goes_closes` (`native_compile_opens.hthr`), for `mov rax, 3; <fd to rdi>; syscall; <rax to result>`:

```
let w0 = then(p, Block([MovRI(Rax, BitVec::ofNat(3))]));
let w1 = w0.known_to(layout, known, fd, Rdi);
let asked = then(w1, Syscall);
let w_asked = asked.word_from_within(layout, out, result, Rax, t.program, within);
let w_w1 = w1.within_before(0, Syscall, t.program, w_asked);
let w_w0 = w0.known_to_within(layout, known, fd, Rdi, t.program, w_w1);
…
t.goes_weaken(prog_len(p), Vis(c, tree), λ (s: MachineState<X86Memory(t.r.profile)>) => post0(execute_block_normal([…], s)),
    λ (s: MachineState<X86Memory(t.r.profile)>) => t.Held(live, env, s.gprs, s.memory), t.goes_block(p, 0, […], w_w0, Vis(c, tree), post0, at_w0), …)
```

Counted over `native_compile*.hthr` and `native_structured*.hthr` (2026-11-16): 147 `within_trans`, 166 `within_before`, 53 `Exists(k, refl)` (a count of items, which moves when the emitter changes), about thirty `within_<builder>` lemmas restating a builder's body in `let`s, 73 `goes_weaken`. None of it is about what the code does. The computed `Wp` (`lib/std/os/linux/linux_x86_64_wp.hthr`, `docs/native/native-program-logic-design.md` §6) removes this for closed code; the compiler's lemmas are about code that depends on its inputs (`p.known_to(layout, known, fd, Rdi)`), so they compose rules by hand.

## Direction (to be designed with Minus before anything is built)

State a piece's claim about the emitter, not about a position:

```
// `f` appends its code to any program; run from its start to its end, `q` after it needs `wp(q)` before it.
fn Target::Emits(self t: Target, f: Prog → Prog, wp: (Gprs → Memory → Type) → Gprs → Memory → Type) → Type {
    (p: Prog) → (tree) → (q) → f(p).Within(t.program) → t.GoesR(prog_len(f(p)), tree, q) → t.GoesR(prog_len(p), tree, wp(q))
}
```

- **One sequence rule**, `Emits(f, wf) → Emits(g, wg) → Emits(λ p => g(f(p)), λ q => wf(wg(q)))`, which needs `p.Within(f(p))` for the first emitter: a class `Extends(f)` each builder registers once (the thirty `within_<builder>` lemmas become its instances, found by resolution, and a builder that is a composition gets its instance from its parts).
- **One consequence rule** with the predicates implicit.
- Leaf rules for a block, a load, a store, a syscall; a `Jcc`/`Jmp` rule whose premise is the claim at the label, which is where positions and `laid_out` are still named, once.
- Statements (`Target::Runs`) and the ITree side stay as they are: `Runs` is already position-free up to `prog_len(p)` and `prog_len(q)`.

Questions for the design: whether the tree a syscall consumes fits the `wp` transformer (it changes between `pre` and `post`), whether labels and `names` thread through `f` or stay outside, the kernel cost of a composed transformer against today's `let` chain (`docs/proof-patterns.md` §2), and how this meets U5 of [[native-one-compiler]], which moves procedures onto the function compiler and may delete part of what this would rewrite.

## Done when

A design note is agreed. Then: `Target::goes_closes` and `goes_clamp` contain no `Within` term and no `prog_len`, and a builder's `within_` lemma is an instance nobody cites.

Related: [[wp-obligation-tactic]] (the closed-code side), [[transition-run-tactics]], [[native-compile-correct-proof-forms]].

## Log

- 2026-11-17: Minus's review (docs/library/program-and-proof-style.md §3) adds a simpler reading to weigh in the design: an emitter returns the code it adds and sequencing appends, so that an emitter only appends holds by construction and the within_<builder> lemmas are not instances but gone. Related: native-assembler-builder, native-emission-context.
- 2026-11-17: built as `lib/native/native_compile_claims.hthr` (Minus: "take the changes and let's implement"). Code is a value (`Fragment`: a placed item, a fetch of a word, a sequence, a skip under a condition), `Fragment::onto` lays it out, and `Fragment::before(r, post)` computes what must hold before it; `Fragment::goes` is the one soundness theorem and `Fragment::extends` the one "only appends" fact. `Run::goes_asked` is the rule for code, SYSCALL, answer kept; `Fragment::window`/`Run::window_before` (`native_compile_calls.hthr`) the buffer window reads and writes share. Ported: `Target::goes_writes`, `goes_closes`, `goes_reads` and the head of `goes_opens`, statements unchanged; none of the ported parts names a `Within` or a `prog_len` before its SYSCALL. Left: fragment forms for a loop, a kept word and the SYSCALL itself (what remains of the `Within` chains in `goes_reads` and `goes_opens` is after those), `native_compile_args.hthr`, and a rule per form so a use does not spell the nested pairs of a fetch.
- 2026-11-17: loops. `Fragment::before` is `Fragment::inside` outside any loop; inside one a `Leave` needs the loop's `leave` claim where taken, and byte loads and stores have their cases. `Fragment::goes_loop` is the rule: an invariant indexed by a number, a round of the body that leaves or comes back with a smaller one, positions and both jumps' landings inside the rule. The open's path copy is on it (`Run::path_round`, which is the invariant's step and names no position): `goes_path_head`, `goes_path_body`, `goes_path_loop`, `Prog::path_counted`, `Prog::path_tested` are gone, `native_compile_opens.hthr` 686 lines to 583. Left: the read's copy (`goes_copy_head/body/loop`, `goes_read_back_ok/failed`) and `Prog::args`; a `Cycle` inside a sequence still splits the sequence by hand, since its precondition needs the invariant.
