# A Heather function in a native executable

From the repository root on x86_64 Linux with a C compiler/linker:

```sh
cargo build -p heather-cli
mkdir -p target/x86-native
(ulimit -v 8388608 -t 300; target/debug/heather compile-x86 \
  examples/x86-native/word_mix.hthr mix -o target/x86-native/mix.s \
  --cache-dir target/native-images)
cc -std=c11 -Wall -Wextra -Werror examples/x86-native/main.c \
  target/x86-native/mix.s -o target/x86-native/mix
./target/x86-native/mix
```

Expected output:

```text
mix(20, 22) = 81985529216486963; 10005 native cases passed
```

The command refuses existing assembly or certificate outputs. Remove those
outputs deliberately before rebuilding, or choose a fresh output name.

`word_mix.hthr` is the compiled program, marked `runtime fn mix`: it shares an addition, adds a full-width
constant, and XORs the results. The C file supplies `main` and checks boundary values and
10,000 deterministic pseudorandom pairs against unsigned C arithmetic.

## Runtime fns

A function runs only when it is marked: `runtime fn f` (with `import
bitvec; import runtime;`, which since 2026-11-19 is enough: the generator's
own names resolve through the import closure, docs/language/modules-design.md
§3.6) publishes `f::program`, a FunctionIR program of `f` and every runtime fn it
calls, each from its `Compile` instance, and `f::agrees`, that the program
evaluates to `f` ([design §16.9](../../docs/native/runtime-fn-setups-design.md)).
`compile-x86` compiles a marked function through those: its certificate's
`_agrees` is `f::agrees`, and nothing about the program is proved by the
compiler. Loops are runtime fns too (design §16.11). An unmarked function
is refused, naming the marker, unless its program has a test through a
`Bool` helper, which the default setup does not compile yet; those go
through the older Rust reflector the rest of this page describes. Every
file here is marked but `branches.hthr`'s `composed`, `either` and
`calls_either`, which call the `Bool` helper `unequal`.

## What `compile-x86` certifies

`compile-x86` compiles a function with `BitVec(64)` parameters (at most
eight: six in registers and two on the stack)
and a `BitVec(64)` result, together with the word functions it calls,
through the verified lowering ([round 4 of the issue](../../issues/function-ir-verified-lowering.md)).
The body may use Add, Sub, AND, OR, XOR, `bitvec::ofNat` literals of any
size, `let`, calls, and tail-position matches on a test. A test is
`unsigned_lt_bit`, `signed_lt_bit` or `eq_bit` of words, `||`, `&&` and `!`
of tests, or a call of a `Bool` helper of words whose body is a test
(`branches.hthr`'s `composed` and `either`). Connectives and helpers become
conditionals on plain comparisons, each operand tested only where its
connective needs it. A source outside that fragment is refused, with a
message naming what it does not support.

The certificate does not reason about this particular program's
instructions. For a function the Rust reflector compiles, it reflects the
source into a FunctionIR program and states:

- the program's lowering by `lower_program`, with the planner's placement,
  as a literal (`_lowers`, checked by evaluation);
- that the program evaluates to the source function at any arguments
  (`_agrees`), proved a function at a time: each function's region,
  evaluated with its calls answered by the source functions called, is its
  own source function, and `program_eval_sources` composes them. A
  function's agreement is by `refl` when every match is on a comparison and
  it calls nothing. Otherwise the certificate states the function's
  decision tree in source operations, each call spelled as the call it
  answers (`_expansion`), equal to the function's region by `refl`
  (`_expanded`) and to the source by `split_all` (`_expands`): a test
  through a connective or a helper has no conversion that commutes the
  source's `match` with the program's conditionals, and a callee's source
  is never unfolded into its caller's proof;
- the published bytes, a piece at a time (`_bytes`), and the exported
  function's offset (`_entry_at`);
- and `_returns`, which instantiates the theorem `compiled_returns`. Called
  at its label with its arguments in RDI, RSI, … and past the sixth on the
  stack above the return address at RSP (`Stack::Passed`), and room on the
  stack below it, the code returns the source's value in
  RAX, keeps the callee-saved registers and RSP, and leaves memory as it
  was but for stores into its own room below the return address
  (`Stack::Wrote`). The caller's stack words follow from that
  (`compiled_returns_keeps`), and so does anything else of the caller's
  that such stores cannot reach.

The assembly is the whole program: each function's frame, body and RET,
with the exported symbol at its function's label. The platform ABI around
it (stack alignment, the C caller, the loader) is outside the proof.
`levels.hthr` is a three-level example with calls in both arms of a
branch:

```sh
(ulimit -v 8388608 -t 300; target/debug/heather compile-x86 \
  examples/x86-native/levels.hthr program -o target/x86-native/levels.s \
  --cache-dir target/native-images)
```

Arguments arrive in RDI/RSI and the result leaves in RAX.

Proof support modules are bundled into the compiler. Source imports use the
normal loader with `lib/std`, `lib`, and additional `-L` directories. A source
module with a bundled library name must have identical contents. Optional
`--cache-dir` uses kernel-rechecked semantic images with exact build identity;
it does not enable the trusted declaration cache or stale-image replay.

## The other examples

Every `.hthr` here compiles the same way. `branches.hthr` holds nested
comparisons (`nested_true`, `nested_false`), connectives (`composed`) and a
`Bool` helper (`either`), called by `calls_either`; the rest are call shapes: a call's result as the
next call's argument (`composition.hthr`), values live across calls
(`sharing.hthr`, `stack_save.hthr`, `multi_stack_save.hthr`,
`stack_local.hthr`), a leaf that writes several registers
(`multi_register.hthr`) and one callee called twice (`reused_callee.hthr`).
`crates/cli/tests/native_program.rs` and `native_branches.rs` compile each,
link it against a C reference and compare them on boundary and pseudorandom
inputs. `stack_words.hthr` is a function of eight words that passes eight
to another; `native_program.rs` calls it from Rust, the seventh and eighth
on the stack.

## Narrow words

A function's parameters and result are 64-bit words, and inside it a value
may be any width up to 64: `a.truncate(32, 32)` is the low half of `a`, and
`x.zero_extend(32)` brings a 32-bit result back. The compiler keeps a
narrow value zero-extended in its 64-bit register. AND, OR, XOR, a right
shift, an unsigned comparison and an equality read it as it is; an ADD, a
SUB or a left shift, which can carry past the top, is followed by a shift
left and back by 64 minus the width; narrowing is that pair of shifts and
widening is free. `narrow_bytes.hthr` tests a byte's carry and borrow,
`narrow_words.hthr` rotates a 32-bit word and adds a constant with its top
bit set, and `narrow_widths.hthr` takes one value through 64, 32, 16, 27,
32 and 64 bits. A narrow signed comparison, a narrow arithmetic shift and a
sign extension are refused (`narrow_signed_operations_are_refused` in
`native_program.rs`): zero extension does not keep a sign.

## Two words back

`two_words.hthr`'s `add_wide` returns a record of two 64-bit words, the sum
of its arguments as a 128-bit number. It comes back the way System V returns
a C structure of two integer words, the first field in RAX and the second in
RDX, and the certificate states both (`Prog::ComputesBoth`). A C caller
declares `typedef struct { uint64_t low, high; } Wide;` and reads it
(`a_record_of_two_words_is_returned_in_rax_and_rdx` in `native_program.rs`).
Inside a program a call reads back every word of its callee's result, and
passes a record or an enum in its words.

`add_wides` takes two `Wide`s and returns one: a record of words is passed
a word a field, as System V passes a C structure of integer words by value,
so C calls it as `Wide add_wides(Wide, Wide)`
(`records_of_two_words_are_passed_and_returned`).

## Bools

`bools.hthr`'s `in_range` takes and returns `Bool`s: a parameter is the
lowest bit of its word and the result is 0 or 1, which is what System V
asks of a C `bool`, so C declares it `bool in_range(uint64_t, uint64_t,
uint64_t, bool)` (`bools_cross_as_c_bools`).

## Narrow fields

`narrow_fields.hthr`'s `tagged_next` takes and returns a record of a `u8` and
a 64-bit word. C lays `{ uint8_t; uint64_t }` in two eightbytes, so System V
passes it in two registers, the byte in the low bits of the first: a word a
field, as a record crosses here. The byte is read from the low bits of its
word and returned zero-extended, so C declares `Tagged tagged_next(Tagged)`
(`a_record_with_a_byte_field_crosses_as_a_c_structure`). Two narrow fields
side by side share one eightbyte in C, so `compile-x86` refuses
`flagged_sum`'s record at a C boundary
(`a_record_of_two_packed_narrow_fields_is_refused_at_c`); inside a program
such a record crosses calls like any other.

## Linked into Rust

`crates/linked` links compiled functions into a Rust crate and calls them
directly: `generated/*.s` is `compile-x86`'s output for each line of
`generated/EXPORTS.tsv`, checked in, and `crates/cli/tests/native_linked.rs`
recompiles every export and compares. `scripts/linked` rewrites the files
after a change to a linked module or to the lowering (`--check` only
compares). Exports that share callees are one program: `compile-x86 … --entry
<module>::<function>` exports another function of the program at a label of
its own in the same file, under the same certificate, and a table row's
fourth column asks for that. The exports today are the word functions of SHA-512 and SHA-256
(`lib/native/crypto/`), each proved to be the specification's
(`lib/std/crypto/sha2.hthr`).

## Loops

A recursion on a fuel compiles to a verified loop. The function is
`runtime fn h(fuel: Nat, x…: BitVec(64)) → BitVec(64)`, matching its fuel
`Zero`/`Succ(k)`; the `Succ` arm's tail positions either return a word or
recurse as `h(k, …)`. It is a native function of its own, its body the
loop, and a caller passes its fuel as a word's count, `h(w.toNat(), e…)`
(the fuel crosses the call in a word) — under a branch, followed by more
work, in a called function, or inside another loop's pass. The loop runs
at most `w` passes; out of fuel it computes the `Zero` arm. The arm may not
read the recursion as a value. `loop_triangle.hthr` counts down,
`loop_multiply.hthr` keeps an invariant word out of the recursion,
`loop_settle.hthr` calls a function in each pass and decides on several
comparisons, and `loop_anywhere.hthr` puts loops in each of those places.

A `runtime fn` that `decreases` a measure `w.toNat()` of a word `w`
compiles to a loop too, with no fuel to write: its native function takes
the words and runs at most `2^64 - 1` passes of its step, a recursion going
round and an answer leaving. The passes cannot run out first, since each
lowers the measure, which is below `2^64`. `loop_measure.hthr` counts a word
down, `decreases n.toNat()`, and `loop_climb.hthr` climbs to a bound,
`decreases hi.sub(lo).toNat()`.

Nothing about a particular loop is proved in its certificate. Each shape's
lowering is proved once (`lib/native/runtime/rt_loop.hthr`), and the
`runtime fn` generator proves what the function supplies: for a fuel, its
two equations, one `refl` per word; for a measure, that the step with its
recursion answered by anything agreeing below the measure is the function,
from the function's own `f::ext` and `f::irrel` (design §16.10–§16.11).

The Rust reflector's certificates, for the `Bool`-helper programs, prove
the program a function at a time. Each function's `_agrees` says that its
region, evaluated with every call answered by the source function called
(`_sources`), is its source function, and the library's
`program_eval_sources` composes them into the program's. A function that calls another agrees
through an *expansion* that spells each call as the call it answers, so its
proof never unfolds a callee; that is also what lets a caller call a
function deciding through a connective (`calls_either` in
`branches.hthr`).

## A program's own optimizer rule

`own_rule.hthr` declares a rule beside the function it compiles:

```heather
rule theorem sub_self({w: Nat}, a: BitVec(w)): a - a = 0 { … }
```

It is an ordinary theorem about words. The `rule` prefix reads the
statement as what the optimizer may do (a word less itself is the
constant zero), proves that sound from the theorem, and
registers it. `compile-x86` then uses the rules registered in the
program's modules beside the library's own, and the certificate's replay
is over both, so nothing about the rule is trusted beyond the theorem the
kernel checked. `first_and_nothing` compiles to 39 bytes with the rule and
48 without: the subtraction and the add are gone
(`crates/cli/tests/native_own_rule.rs`; `docs/native/optimizer-rules-design.md`).

`own_learner.hthr` goes one step further. Its rule says a mask of the low
`k` bits does nothing to a word below `2^k`:

```heather
rule theorem mask_low(x: u64, k, high: Nat, small: x.within(0, high), fits: Succ(high) <= Nat::pow(2, k)):
    x & BitVec::ofNat(Nat::pow(2, k) - 1) = x { … }
```

The search finds a rule's instance by reading its statement against the
code, and here nothing in the code is `k`: the mask is one constant. So the
program also registers a *learner*, a function the search asks at every
node no statement rewrote, which reads the constant, finds `k` and names
the rule and its numbers:

```heather
register def mask_learner: Learner = Learner(λ had at => match at {
    BitAnd(_, o, x, c) => … Some(Proposed(mask_low_entry, [x, k, range_known(had.range, x).high, o, c])) …
});
```

A learner is as untrusted as the rest of the search. What it proposes is
the rule's own clause at those numbers, checked against what the search
knows and then by the certificate's replay, which uses the rule's
soundness and nothing of the learner. `first_masked` compiles to 39 bytes
with the learner and 48 without; without it `--explain-optimizer=all`
says `not applied at t10 = t6 & t9: mask_low   (known: t6 within 0 ..= 255)`.

A set of rules is a module. `lib/native/function_ir/function_ir_identities.hthr`
is the standard set: the plain identities of words (`x | 0 = x`,
`(a + b) - b = a`, `x.bxor(x) = 0` and the like), each a one-line
`rule theorem`. `compile-x86` registers it in every compilation, so
`rule_set.hthr` names no rule and its `tangled` is compiled with them, one
rule's result read by the next:

```console
  t9 = t1 + t8 = t8 + t1   by add_comm
  t10 = (t8 + t1) - t1 = t8   by add_sub
  t11 = t1 ^ t1 = 0   by xor_self
  t12 = t10 | 0 = t10   by or_zero
```

The first line is the optimizer searching. `tangled` writes its sum with
the length first, and `add_sub`, `(a + b) - b = a`, does not fit
`(n + x) - n` as it stands. At each node the search follows the rules
through the other ways the word, and each word it reads, can be spelled
(`add_comm` turns a sum round) and writes the cheapest it reaches, so a
rule is stated once and found either way round.

A rule may also need a word the code does not have. `stepped` in the same
file returns `(x + 3) + 4`; `add_assoc`, `(x + a) + b = x + (a + b)`, reads
the sum `3 + 4`, which nothing computes. The search asks for it because
another rule, `add_consts`, makes it a constant; a stage puts the node;
and the report says both:

```console
  t15 = 3 + 4 = 7   by add_consts
  t12 = (t6 + t9) + t11 = t6 + (t9 + t11)   by add_assoc
```

`--explain-optimizer` prints what the optimizer did with the rules, a line
for each one used, in the rule's own words and by its name:

```console
$ heather compile-x86 examples/x86-native/own_rule.hthr first_and_nothing \
    -o target/x86-native/first_and_nothing.s --explain-optimizer
function 0: 7 rules used
  …
  t8 = t6.resize(8).resize(64) = t6   by narrow_back   (t6 within 0 ..= 255)
  t9 = t1 - t1 = 0   by sub_self
  t10 = t8 + 0 = t8   by add_zero
```

`t9` is the word the subtraction computed; the line says what it was,
what the rule makes it, and (in brackets, for `narrow_back`) the facts a
rule needed.

`--explain-optimizer=all` also says where a rule was not applied though
the nodes it states were there, which is what to read where a rule was
expected and the code shows it was not used. A line names the node, the
rules, and what was known of the words whose ranges they read:

```console
$ heather compile-x86 examples/binary-search/search.hthr lower_bound \
    -o target/x86-native/lower_bound.s --explain-optimizer=all
function 0: no rule used
  not applied at t17 = t10 - t9: within_sub   (known: t10 within 1 ..= u64::MAX, t9 within 0 ..= 18446744073709551614)
  not applied at t24 = t23 < t8: below_yes, below_no   (known: t23 within 0 ..= 255)
  …
```

The ranges do not say `t9` is at most `t10`, so `within_sub` gives the
difference no range. Every test the program really makes has such a line,
which is why they are asked for apart.

## Per-function certificates and `build-x86`: burned

Before the verified lowering, each function got a certificate generated for
its own instructions (structured, call and composition certificates over
`lib/certgen/ir_v1.hthr`), and `build-x86` wrote a static ELF executable
for a fixed fragment with a callee summary per call. Both were deleted in B2
(docs/native/native-program-logic-design.md §3.2). The last commit with them, their
recipes and this section's old text is `82521ea`. A direct executable comes
back on the verified path, as the compiled program inside a proved process
image (`issues/native-first-compiled-program.md`).

## Programs with input: burned

The programs that read stdin (`wc -l`, `wc` as a command, `tr`, `tr -s`,
`tr -d`) were proved by hand, a process library per program shape, and were
deleted in B1 (docs/native/native-program-logic-design.md §3.1). The last commit
with them, their build recipe and this section's old text is `189659d` (tag
`native-v0`). They come back as programs of an effectful source whose meaning
is an interaction tree, compiled by a compiler proved correct once
(`issues/native-first-compiled-program.md`). Their specs survive:
`lib/std/text/decimal.hthr` (what `%d` and `%7d` print) and `lib/native/stream_filter.hthr`
(a filter's fold and the counting lemmas).
