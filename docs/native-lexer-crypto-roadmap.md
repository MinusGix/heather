# Native roadmap: a linked lexer, and cryptography

Status: **a roadmap, 2026-11-10**, written at Minus's request: where native
compilation has to get for (1) Heather's lexer, written in Heather, linked
directly into the compiler, and (2) cryptography that is verified and runs
natively; the likely issues; and the enhancements and generalizations worth
doing on the way. It is not a minimal route. It extends
`docs/compilation-vision.md` and reopens none of its settled principles; §7
lists the documents it does ask to reconsider, and §9 the decisions that are
Minus's. Probes are in the project folder's `native-roadmap/`; their numbers
are in the issues this note files, not here.

Read on master `b2fb02b`. §10 records what has landed since and what Minus
has answered.

---

## 0. The two targets

Both end the same way: proved Heather code linked into the `heather` binary,
replacing a Rust component the compiler trusts today.

**The reading taken.** "Lexer linked directly" is the Heather lexer compiled
to an object and linked into the Rust `heather` binary in place of
`crates/syntax/src/lexer.rs`. That is a different target from the
`self-lexer` milestone, which is a `heather-lex` process streaming tokens to
stdout. "Cryptography" is primitives with a specification, a proof that the
compiled code implements it, and a native run.

| | lexer | cryptography, first primitive SHA-256 |
|---|---|---|
| meaning (never run) | `lex`, a pure function over bytes, which becomes the definition of the lexical grammar | the hash as a pure function in FIPS 180-4's shape |
| code | a scanner `runtime fn` under the default setup | `compress` and the streaming `update` as `runtime fn`s |
| theorem | at any source held in the caller's memory, the export returns the next token of `lex`, reads only the source span and writes only its frame | the exported `compress` leaves the specification's next state in the caller's state buffer, reads only the block, writes only the state, and leaks nothing that depends on the data |
| where it runs | linked into `heather` behind a switch; the Rust lexer stays as bootstrap and oracle | linked into `crates/cache`, replacing the scalar path of `crates/cache/src/sha256.rs` |
| the test | token streams equal on every file under `lib/` | NIST vectors by kernel evaluation and by native run; every cache key unchanged |

**A third target, later: the numeral crate** (Minus, 2026-11-10).
`crates/numeral`, the arbitrary-precision natural the lexer, the elaborator
and the kernel share, is small, in the trusted base, and specified by `Nat`
in a line per operation. It needs what the first two do not (a wide multiply
and divide, a buffer whose length changes) and nothing they do not have a
plan for, so it follows them (`issues/numeral-linked.md`). Linked code will
be slower than rustc's until there is an optimizer; that is accepted.

**Why SHA-256 first.** The compiler already has a first-party SHA-256, and
its header calls it "the one place above the kernel with a trust story to
protect": a collision is a wrongly accepted proof. Cryptography therefore has
a customer inside Heather from the first round, and that customer is in the
trust base.

**What "verified" means for a primitive** is a ladder of separate theorems:

1. *Functional*: the code implements the specification. The compiler's
   theorem gives agreement with the `runtime fn`; a Heather proof takes the
   implementation-shaped function to the specification-shaped one.
2. *Memory*: the code reads and writes only the spans its contract names.
   This comes with the export contract, not with each primitive.
3. *Constant time* under a named leakage contract
   (`docs/constant-time-survey.md`).
4. *Secret erasure* at return (`docs/zeroization-survey.md`).
5. *Specification validity*: known-answer vectors by evaluation and
   cross-checks against an independent implementation. Collision resistance
   and the like stay stated assumptions.

---

## 1. Where the stack stands

The stack compiles pure word functions and closed programs with proofs. It
does not yet compile a function over memory it was handed, which is what
both targets are.

| layer | works | the limit the targets meet |
|---|---|---|
| `runtime fn`, default setup (pure) | generator in Heather; soundness once for word arithmetic and comparisons at any width, literal shifts, extensions, `Bool`, flat records, calls at word signatures, fuel and measured loops | no multiply, divide, rotate or variable shift; `Get`/`Set`/`Fold` unproved; one result word |
| `compile-x86` | certified bytes for a word function and its callees, run from C | at most six 64-bit parameters; widths 64 and 1 only (`word_only`); the ABI is outside the proof |
| effects (`Io`, `rt` to `Source`) | straight-line calls and `while` over the world lowered, sound as `Io::Reads` | no branch over the world, no `while` reflector, no `runtime fn main`, no effectful callee; no tool rewritten in it |
| `write-elf` | `Source` to x86 to a static ELF, proved once against the Linux model; nine tools; procedures; an arena through the builder | buffers are static slots; programs only, no library |
| machine model | 64-bit `MOV ADD SUB AND OR XOR CMP TEST`, three `SETcc`, shifts by one and by an immediate, `Jcc`, `JMP`, `CALL`, `RET`, word and byte load and store pieces, `SYSCALL`; the undefined-flags mask | no 32-bit forms, rotates, `BSWAP`, multiply, carry chain, `CMOV`, `LEA`, vectors |
| proof support | words as the ring ℤ/2ⁿ, `sets`, one transition-system library with simulation diagrams, span sets, sorting; `grind` on native chains | no bit-vector decision procedure, no loop-invariant rule |

What the probes found, as shapes:

- SHA-512's Σ0 as a `runtime fn` certifies through `compile-x86`; a rotate is
  five instructions and the leaf reserves a frame it never uses.
- SHA-256's 32-bit Σ1 and T1 reflect and agree as `runtime fn`s, and the
  verified lowering then refuses them.
- By kernel evaluation, one SHA-256 block by a single `refl` is past one
  declaration's fuel; a group of sixteen rounds is well inside it.
- A rotate written as two shifts and an OR evaluates several times more
  expensively than the same rotate as `drop_low` and `concat`, because a
  shift by `k` is `k` one-bit shifts. `lib/std/bitvec` has no rotate.
- `program_scan`'s cost grows with the square of a function's size
  (`issues/function-ir-scan-id-cost.md`), and the generator's per-function
  cost is what a tool-sized program meets first
  (`issues/runtime-generator-link-cost.md`).

---

## 2. The shared spine

Seven pieces serve both targets. Pieces 2, 3 and 7 had no milestone, and
they are what "linked directly" adds to the plan.

| # | piece | the lexer needs | cryptography needs | owner |
|---|---|---|---|---|
| 1 | bytes and arrays in the pure fragment | a byte at an index, a loop over a span | an 8-word state, a 16-word schedule, the table `K` | `runtime-default-setup-soundness`, `rt-fixed-arrays-and-tables` |
| 2 | memory the caller owns | the source span, read only | the state written in place, the block read | `source-buffers-as-views`, `x86-call-memory-footprints`, `wp-proved-memory-contracts` |
| 3 | an export contract | System V entry, registers, stack, and piece 2's footprint | the same | `native-library-exports-design`, `runtime-extern-c-abi`, `named-abi-contracts` |
| 4 | calls at real signatures | two result words, records across calls | eight words in and out | `function-ir-multi-word-calls`, `native-procedure-contracts` |
| 5 | certificate and generator cost | a full step several times the probe's | a 64-round compress | `function-ir-scan-id-cost`, `runtime-generator-link-cost` |
| 6 | instructions | byte loads, a table index | 32-bit forms, rotates, `BSWAP`; later `MUL`, `ADC`, `CMOV` | `x86-narrow-and-rotate-forms`, `x86-wide-multiply-and-carry`, `function-ir-narrow-arithmetic` |
| 7 | linking into the Rust build | bootstrap, fallback, a regeneration gate | the same, plus `build.rs` in `crates/cache` hashing with it | `native-library-exports-design` |

**One notion of buffer.** Pieces 1, 2 and 4 are one design question asked
three times. A buffer is a numbered static slot today. The arena round found
that a line is a span of the arena buffer, so `Bytes` must lower as a view
(buffer, offset, length). A borrowed source span is a view whose base is a
word the caller passed. A procedure-local scratch block is a view into its
frame. The recommendation: one round that makes a buffer an address held in
a word plus a capacity, with static, borrowed, arena and frame buffers as
its instances, and footprints taken from `lib/std/data/set/span_set.hthr`.

**The unit of export is a procedure.** `Source` procedures already own
their words and share buffers (`docs/native-procedures-design.md`). An
exported function is then a procedure whose shared buffers are the caller's,
entered through a System V shim. That keeps a library from becoming a third
pipeline beside `compile-x86`'s word functions and `write-elf`'s programs.
This has not been checked against the proofs, so it opens with a design
round (`issues/native-library-exports-design.md`).

**Not on the spine.** The effects surface is needed only for standalone
tools. The heap is needed by a parser, not by a scanner or a hash. The
ownership setup matters in one place: an in-place state update is a `Set`
that needs `Unique` to avoid a copy (`issues/unique-fact.md`).

---

## 3. The route to the lexer

A linked lexer needs bytes, borrowed memory and an export contract. It does
not need the effects surface or the heap, which reverses the 2026-10-31
assumption that the lexer waits on `nh-effects`
(`docs/compiler-milestones-proposal.md` §5).

| stage | result | needs | test |
|---|---|---|---|
| L0 pure lexer | `lex` mirrors the Rust lexer; line-locality, lossless spans and maximal munch proved | nothing (`heather-lexer-evaluated`) | per-line `refl` theorems written from the Rust lexer |
| L1 step natively | the full per-byte step and classifier certified as word functions | piece 5 | a C harness against the Rust lexer's kinds |
| L2 scanner over a buffer | `next_token(src, len, pos)` returns (kind, end) from a read-only span | pieces 1, 2 (read half), 4 | the harness on whole files |
| L3 linked | exported with a contract and linked into `heather` behind a switch (`self-lexer-linked`) | pieces 3, 7 | token streams equal on every file under `lib/`; the suite green with the switch on |
| L4 values in Heather | numerals that fit a word, escapes and UTF-8 validation move across | piece 2 (write half) | the same |
| L5 grammar as data | token classes are `regex def`s, the DFA is generated and proved, the scanner is longest match over them by theorem (`lexical-grammar-as-data`) | `regex-dfa-compiler`, constant tables | the generated scanner equals L0's by theorem |

**Where the stages stand** (2026-11-10, §10's second round). L0's scanner
and L1 are built, and L3's comparison runs with the loop still in Rust:

- The scanner is a deterministic automaton over bytes, not a hand-written
  step: `lib/lang/lexer/lexer_scan.hthr`. A state is a word (its number,
  with the kind it accepts above), a token is the longest run the automaton
  accepts with the last accepting position remembered, and the lookahead
  the Rust lexer does by peeking is states. Two things a textbook automaton
  lacks and this one needs: a refusal that no earlier accept excuses
  (`12abc`, an unterminated literal), and a start state chosen by the
  previous token's kind (`>>` is a shift only after a gap).
- Each family of states is a certified word function and `crates/linked`
  links all of them; `crates/linked/src/scanner.rs` is the loop. It is held
  to `heather_syntax::lex` on every Heather source in the repository, on
  every edge of the automaton, on generated strings and on library lines
  with one character changed.
- `lib/lang/lexer/lexer_tokens.hthr` is the same loop as a function the
  kernel evaluates, the specification the compiled loop will be proved
  against; probes hold it to the linked scanner today.
- Not built: the values (L0's other half), the loop compiled (L2), the
  switch (L3). The automaton is also not one program yet: Rust picks the
  family for each byte, because a program holding every family is past
  what a linked program's proof is checked for
  (`issues/runtime-generator-program-size.md`).

- **A scanner plus values.** The Rust lexer's tokens hold values: numerals
  past a machine word, scaled literals, unescaped strings. A scanner that
  returns only (kind, start, end) never allocates, and a token's value is a
  pure function of its span. L0 is written that way so L2 compiles the
  scanner unchanged.
- **One byte at a time, lookahead in the state.** `next_token` is then the
  step iterated until a token finishes, and the same step serves a process
  that reads in chunks.
- **Errors stay in Rust at first.** The native scanner returns an error kind
  and an offset, and Rust re-lexes that file with its own lexer for the
  message, so diagnostics stay byte-identical and no string is built
  natively.
- **Bootstrap.** The Rust lexer stays as stage 0 and as the oracle. The
  compiled scanner is a build input, which `build.rs` cannot produce. The
  lean: check in the generated assembly and a digest of its certificate,
  with a gate that regenerates both and compares bytes whenever the lexer
  module or the compiler changes. Hosts that are not x86-64 Linux keep the
  Rust lexer.
- **What the theorem says.** The native scanner equals `lex`. That `lex`
  equals the Rust lexer is only tested. Once the switch is the default,
  `lex` is the definition and the Rust lexer the legacy copy.
- **The process.** `heather-lex` as a standalone executable is a side branch
  after `runtime fn main`: it reuses the scanner and tests state carried
  across read boundaries (`self-hosted-lexer`).
- **After the lexer.** The parser needs somewhere to put a tree: `nh-heap`,
  or an arena the caller lends. The cache's Merkle walk and the tree-sitter
  inventory check are smaller next components.

---

## 4. The route to cryptography

| stage | result | needs | test |
|---|---|---|---|
| C0 specifications | `lib/std/crypto/`: SHA-2 as pure functions in FIPS 180-4's shape; rotates and wide word operations in `lib/std/bitvec` (`sha2-specification`, `bitvec-rotates-and-wide-ops`) | nothing | NIST short vectors by `refl` |
| C1 compress natively | the compression function as a `runtime fn` over word arrays, proved equal to the specification's (`sha2-compress-native`) | pieces 1, 4, 5; narrow arithmetic for the 32-bit variants | a C harness over random blocks |
| C2 hash over memory, linked | exported `compress`, streaming `update` and `finish`, linked into `crates/cache` (`sha256-linked-into-cache`); `sha256sum` as a `write-elf` tool once `runtime fn main` exists | pieces 2, 3, 7 | every cache key unchanged over the suite; GNU's `sha256sum` tests |
| C3 constant time | the leakage statement and its transfer lemma, a leakage transformer for the compiler, a `ct fn` setup, `Select`, a constant-time tag compare (`native-constant-time`) | a leakage clause in the export contract | a secret-dependent branch refused by the judgment |
| C4 ChaCha20-Poly1305 | RFC 8439; HMAC and HKDF as compositions over C2 | `MUL` and `ADC` in the model, a limb lemma kit over `ModEq` | RFC vectors, Wycheproof |
| C5 X25519 | field arithmetic mod 2²⁵⁵ − 19 from a small language with its own compiler (`field-arithmetic-language`); the Montgomery ladder with a constant-time swap | C3, C4's arithmetic | RFC 7748 vectors |
| C6 Ed25519 verification | SHA-512 plus the curve; a signature check as a function and as a tool | C5 | RFC 8032 vectors |
| C7 fast paths | hand-written machine-level `Compile` instances for SHA-NI, AES-NI and vectors, chosen by a fact about the target | the extension's instructions in the machine model | equal output to the scalar path, by theorem |

- **Write SHA-2 once.** SHA-256 and SHA-512 are one construction at two
  word widths with different constants. One specification generic in the
  width, one implementation and one proof give SHA-224, 256, 384 and 512,
  and the 64-bit instance can go through the whole pipeline while narrow
  arithmetic is being built.
- **Refinement in stages.** The specification builds a 64-word schedule as
  a list; real code keeps a rolling 16-word window and updates a state in
  place. That step is a Heather proof between two pure functions, and the
  compiler's theorem covers only the step after it. It needs loop-invariant
  rules (`loop-invariant-rules`) and a decision procedure for bit-vector
  identities (`lrat-certified-bitvector-decision`), or these proofs become
  the hand towers that were burned once already.
- **Streaming is one theorem for every hash.** `update(update(s, a), b) =
  update(s, a ++ b)` and the padding lemma hold for any block function.
- **Field arithmetic is the second language.** X25519 and Poly1305 want
  limb code nobody should write or prove by hand. The known answer is Fiat
  Cryptography's: a prime and a limb layout in, straight-line code and its
  proof out. In the vision's terms it is a DSL with its own compiler, or
  equally a `datarepr` of ℤ/p as limbs. That the ladder computes scalar
  multiplication on the curve is mathematics-area work and can follow the
  RFC-level specification.
- **Constant time enters the compiler's theorem early.** Every pass written
  before the leakage transformer exists must be reopened to produce one.
  The statement and the transfer lemma are cheap now
  (`docs/constant-time-survey.md` §11, step 1).

---

## 5. Likely issues

The risk that decides the schedule is cost at ten times today's function
size. The risk that decides the design is memory at the boundary.

| # | risk | how to see it early | lean |
|---|---|---|---|
| 1 | certificate and generator cost: a compress loop body and a full lexer step are each several times the largest function certified so far, and the costs are superlinear | `scripts/bench-probes` cases for both shapes, added before the code that needs them | logarithmic marks in `program_scan`; a loop instead of unrolled rounds; each function's agreement moved from a checked proof toward an instance of `Setup.sound` |
| 2 | borrowed memory built twice: `Io` buffers, arena views and exported spans each want a footprint | the design round shows one footprint notion serving `Source`, `Callee` contracts and the export | one buffer notion (§2) |
| 3 | the export claims more of System V than it models (callee-saved registers, stack alignment, the red zone, the direction flag, upper register halves) | the contract is a named subset with each unmodelled item listed | allocate only caller-saved registers, as the bootstrap export does; Rust's obligations (valid, disjoint spans) are the precondition |
| 4 | position-independent code: Rust links position-independent executables, and a constant table needs an address | the first table-driven function | the table's base as a hidden argument from the shim first; RIP-relative `LEA` later |
| 5 | checked-in artifacts drift from their source | a gate that regenerates and compares bytes | the certificate's digest travels with the artifact |
| 6 | evaluation fuel for specifications | measured (§1) | cheap rotates, stage theorems per group of rounds, long vectors by native run; a kernel fast path for words is a kernel decision |
| 7 | 32-bit and flag semantics: 32-bit forms zero the upper half; rotates and multiplies leave flags undefined | each new form cross-checked against `docs/x86-64-reference-materials.md` | the undefined-flags mask already carries it |
| 8 | constant time retrofitted | count the passes when the statement lands | land the statement before the next pass |
| 9 | implementation-to-specification proofs by hand | the first rolling-schedule proof | bit-vector decisions and loop-invariant rules before C4 |
| 10 | the effects surface has no stated end | tools stay on the builder | its done-when fixed at `runtime fn main` plus one tool rewritten |
| 11 | lexer parity drifts with the language: a new symbol changes the Rust lexer, the Heather lexer and the tree-sitter grammar | the tree-sitter check is not in CI | L5 makes the token grammar one piece of data all three read |
| 12 | the backlog keeps growing | the daily review's count | the export design round closes or supersedes the x86 call issues it absorbs |

---

## 6. Enhancements and generalizations

Taken together, the two targets give each producer kind of
`docs/compilation-vision.md` §2.2 its first real customer:

| producer kind | first customer |
|---|---|
| `rt` setups | the scanner loop; SHA-2's compress |
| a DSL with its own compiler | token regexes to a DFA; field arithmetic from a prime and a limb layout |
| a restricted dialect | `ct fn` |
| a hand-written instance | SHA-NI's compress, proved against the machine model |

Each generalization below is wider than the target that asks for it, and the
wide version is the one to build.

| generalization | what it is | first consumer | also serves |
|---|---|---|---|
| buffers as views | an address in a word plus a capacity; static, borrowed, arena and frame buffers are instances | the borrowed source span | arena lines, procedure-local scratch, `Io` buffers |
| fixed arrays and tables in `rt` | `[BitVec(w); n]` with element reads and writes at the element's width, byte order as a codec, constant tables as read-only data | the SHA state and `K`; DFA tables | `Bytes(cap)` as the `w = 8` instance |
| machine words at every width | the lowering accepts 8, 16 and 32 with native forms | SHA-256, ChaCha20 | `u32` and `i32` in ordinary code (`runtime-repr-narrow-words`) |
| a complete word library | rotates, byte swap, widening multiply, add with carry, population count, leading zeros: each with laws, a cheap kernel definition, a FunctionIR node and an instruction | rotates in SHA-2 | hashing, bit sets, the decimal printer |
| idiom recognition as a certified pass | `(x >> k) \| (x << (w − k))` becomes one rotate by one proved rewrite, the e-graph library as the search (`rotate-idiom-pass`) | a rotate's instruction count | later peepholes; instruction selection by equality saturation |
| facts with consumers | `InBounds` drops the scanner's per-byte bound check; `Unique` makes a state update in place; `ConstantTime` is published by a `ct fn` and required by a caller | the scanner loop; `compress` | `facts-on-demand`'s first non-prototype use |
| libraries, not only programs | exports with a contract now; imports under an assumed contract later | both targets | a Heather parser calling Rust's allocator |
| one observation per machine step | leakage, cost and allocation metering are one instrumentation of the step relation | constant time | `cost-aware-semantics`, `hih-alloc-metering` |
| a differential harness | one script runs an exported function against a Rust reference over a corpus and random inputs (`native-differential-harness`) | lexer against `lexer.rs`; hash against `sha256.rs` | the parser |
| vector importers | NIST response files and Wycheproof JSON become theorems, written by a Rust test | SHA-2 | the per-line lexer gate's pattern |
| the target as a description | "this machine has SHA-NI" is a fact an instance may require | C7 | vision question 6; a second architecture |
| refinement in stages as a proof pattern | specification, low-level functional form, `rt`; loop-invariant rules over arrays | the rolling schedule | a section of `docs/proof-patterns.md` once done once |

---

## 7. Documents to reconsider

The written plan assumes Heather compiles programs. Both targets are
libraries.

| document | what it says | the change |
|---|---|---|
| `docs/roadmap.md`, `self-lexer` | done when a `heather-lex` executable matches the Rust lexer on `lib/` | done when the linked scanner does; the executable a customer of `nh-effects`. This note's PR adds `nh-library`, `hih-crypto` and `crypto-hash` and leaves `self-lexer`'s wording for Minus |
| `docs/compiler-milestones-proposal.md` §5, §7 | the lexer is round R7, after the effects round R6, because it streams to stdout | the lexer follows bytes and the export contract |
| `docs/compilation-vision.md` | question 5 fixes a calling contract between producers inside Heather; nothing covers code called from outside, or what a compiled library is | a section on programs and libraries, with the export as the same contract met by a System V shim; question 6 gets its first concrete need from SHA-NI |
| `docs/constant-time-survey.md` | "Not scheduled: no current milestone needs it" | scheduled under `hih-crypto`, its §11 step 1 before the next compiler pass |
| `docs/runtime-fn-setups-design.md` | fifteen sections of plan and a sixteenth with thirteen rounds of findings | split into a current-state reference and an archive of the rounds; threads start from it and its plan half no longer matches the code |
| `issues/verified-lowering-instruction-coverage.md`, `issues/x86-64-machine-model.md` | "order the list by first consumer", the consumers then unknown | the order is knowable: byte loads, 32-bit forms, rotates, `BSWAP`, `LEA`, `CMOV`, `MUL`, `ADC` and `SBB`, then SHA-NI |
| `docs/native-procedures-design.md` | a procedure shares the program's numbered buffers | check that a procedure can take a buffer as a parameter |
| `docs/datarepr-design.md` | representations of inductive specification types | check that ℤ/p as limbs fits, the specification type being a quotient |

---

## 8. The order

| phase | lexer | shared spine | cryptography | gate to the next |
|---|---|---|---|---|
| 1 start now | L0 pure lexer, scanner plus values | `Get`/`Set`/`Fold` proved; scan and generator cost; the export design round | C0 specifications; rotates in the library; 32-bit forms lowered | a function twice `step_full` certifies, and byte reads are proved sound |
| 2 over memory | L1, L2: the full step certified, `next_token` over a span | buffers as views; several result words; the export contract | C1 compress natively, 64-bit first; the constant-time statement | C harnesses pass on whole files and on random blocks |
| 3 linked | L3 linked into `heather` | linking, the regeneration gate | C2 linked into the cache | the suite is green with both switched on |
| 4 wider | L4, L5, the process | idiom recognition; `InBounds`, `Unique`; the effects surface closed | C3 to C7 | |

Rounds that can start now, none waiting on another:

1. `heather-lexer-evaluated`, written as a scanner plus values.
2. `runtime-default-setup-soundness`: the `Get`, `Set` and `Fold` cases over
   `function_ir_state`'s run.
3. `function-ir-scan-id-cost` and `runtime-generator-link-cost`, with
   `scripts/bench-probes` cases for a full lexer step and a hash round body
   added first.
4. `native-library-exports-design`.
5. `sha2-specification` with `bitvec-rotates-and-wide-ops`.
6. `function-ir-narrow-arithmetic` with `x86-narrow-and-rotate-forms`.
7. `native-constant-time`'s statement and transfer lemma.

What to stop: further rounds on signed 64-bit arithmetic (`IDIV`, signed
division, narrow signed words at the boundary), which neither target needs;
and effects slices past `runtime fn main` and one rewritten tool.

---

## 9. Decisions for Minus

1. Is "linked into the `heather` binary" the right reading of "linked
   directly"? If the process was meant, phases 2 and 3 of the lexer lane
   swap the export contract for `runtime fn main`. **Answered 2026-11-10:
   yes, direct linking**, "a better test and method", with good tests
   around it.
2. SHA-256 in `crates/cache` as the first cryptography target. Turning it on
   by default changes the trust base.
3. The milestones this note's PR adds (`nh-library`, `hih-crypto`,
   `crypto-hash`), and whether `self-lexer`'s done-when moves to the linked
   scanner.
4. Checked-in generated assembly with a regeneration gate as the bootstrap
   route.
5. Stopping the signed-word rounds and capping the effects slices.
6. A kernel fast path for word operations is not proposed. Cheap rotates
   and stage theorems cover evaluation for now.

---

## 10. What has landed

**2026-11-10, the first round** (Minus: "iterate on several of the highest
value pieces, in one PR"). Five of the seven startable rounds of §8 moved,
each far enough that the next consumer is real:

- **Linking, end to end** (§2's last piece, taken first because Minus named
  it the better test). `crates/linked` links `compile-x86`'s output into a
  Rust crate with `global_asm!` and calls it as a `safe fn`. The assembly is
  checked in (`generated/`, listed in `EXPORTS.tsv`), a native gate
  recompiles every export and compares (`crates/cli/tests/native_linked.rs`),
  and `scripts/linked` rewrites it. That is decision 4's route, built; what
  is not built is the export *contract* over caller-owned memory, since the
  exports so far are functions of words
  (`issues/native-library-exports-design.md`).
- **The SHA-2 specification** (C0): `lib/std/crypto/sha2.hthr`, one family
  for both widths, with "abc" proved at SHA-256 and SHA-512 by evaluation
  through stage theorems (`lib/_tests/std/crypto/sha2_tests.hthr`), and
  rotates as the standard's shift pair (`bitvec_rotate.hthr`).
- **Narrow widths in the verified lowering**
  (`issues/function-ir-narrow-arithmetic.md`). A value of any width up to
  64 is held zero-extended; ADD, SUB and a left shift settle by a shift
  left and back; resizes in both directions. The route is not the one §2
  expected: no 32-bit instruction forms were added to the machine model.
  Two 64-bit shifts after each carrying operation cost code size, not
  proof, and the 32-bit forms become an optimization with a consumer
  (`issues/x86-narrow-and-rotate-forms.md`,
  `issues/function-ir-narrow-settle-lazily.md`).
- **The word functions of both compression functions** (the arithmetic of
  C1): `T1`, `T2` and a schedule word, for SHA-512 at the machine's width
  and for SHA-256 through the narrow lowering, each a certified
  `runtime fn` proved to be the specification's function
  (`lib/native/crypto/`). The state, the schedule and the constants are
  still the Rust caller's, which is what `rt-fixed-arrays-and-tables` and
  the export contract remove.
- **A differential harness in its first form**: `crates/linked/tests` runs
  each export against plain Rust at the corners and over varied words,
  and the whole hashes against the `sha2` crate over every length through
  the padding boundaries and the NIST vectors. For SHA-256 it also calls
  the exports with garbage above their 32-bit arguments.

The first thing direct linking found was in the emitter: a program whose
exported function comes first had its label written twice, which no test
had assembled.

**2026-11-10, the second round** (Minus: "pull master and continue
iterating"). The lexer's lane, taken to where memory stops it:

- **The scanner as an automaton** (L0's scanner, L1):
  `lib/lang/lexer/lexer_scan.hthr`, about ninety states in twenty-three
  families, with `scan_family`, `scan_accept` and `scan_begin`; every one a
  `runtime fn` certified by `compile-x86` and linked
  (`crates/linked/generated/`, the same table and gate as the hashes).
- **The scanner in Rust over the linked automaton**:
  `heather_linked::scanner::Scanner`, an iterator of kinds and spans or
  the offset refused. Nothing in it decides what a token is.
- **The comparison with the Rust lexer** (L3's test, ahead of its switch):
  `crates/linked/tests/scanner.rs`. Every Heather source in the repository
  gives the same kinds and spans; so does every edge of the automaton
  reached from every resting state, a corpus of generated strings, and
  library lines with one character changed. A token's value is still the
  Rust lexer's, read from the span, and only the three refusals that are
  about a value may differ. A perturbed edge in the model is caught (the
  negative control that shaped the tests: random strings alone missed it).
- **The loop as an evaluated specification**:
  `lib/lang/lexer/lexer_tokens.hthr`, `Scanned::of`, with theorems by
  evaluation that every state stops at the end of a source and accepts the
  kind its word says, and probes equal to the linked scanner's output
  (`lib/_tests/lang/lexer`, written by `scripts/lexer-probes`).
- **Found on the way.** The Rust lexer panicked on a malformed `\u{…}`
  followed by a multi-byte character (fixed). The runtime generator's reply
  grew with the square of a program's function count (fixed by holding the
  program and its sources once; eight callees were refused before).

What the round could not do is as much its result. The automaton is one
function of the state and the byte, and it is linked as twenty-three
programs with Rust picking between them, for three reasons that are now
issues: a function past about sixteen arms runs the certificate's scan out
of fuel (`issues/function-ir-scan-id-cost.md`) or the compiler out of
memory (`issues/compile-x86-certificate-memory.md`); a program's agreement
is one declaration that evaluates every function's lowering
(`issues/runtime-generator-program-size.md`); and compiled code has no
table to index (`issues/rt-fixed-arrays-and-tables.md`). The loop is Rust
because a compiled function cannot read a span it is lent, which the
survey for this round found to be three layers and not one
(`issues/native-library-exports-design.md`, the log of 2026-11-10): reads
in the verified lowering, a memory law in the function compiler beside the
frame's, and the contract. The scanner only reads, so it is the cheapest
first customer of all three.

Next, in order of what they unblock: the read half of caller-owned memory
(a borrowed read-only span through the lowering and the function compiler,
which compiles the scanner's loop and is the smaller half of the export
contract); compositional linking, so a program's proof costs its largest
function and the automaton is one export; fixed arrays and tables in the
pure fragment (the whole of `compress` in Heather, and the automaton as a
table); then the write half and SHA-256 behind a switch in `crates/cache`.

