//! Whole programs through `compile-x86`'s verified lowering: a function and
//! the functions it calls, compiled by `lower_program` and certified by
//! `compiled_computes`, linked against C references and run. The call
//! examples the per-function path built as executables before burn B2 are
//! here too (docs/native/native-program-logic-design.md §3.2).
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
use std::process::Command;

type Case = (&'static str, &'static str, &'static str);

// Three levels, a call in each arm of a branch, arguments swapped; values
// live across two calls of a two-argument leaf; one call.
const LEVELS: [Case; 3] = [
    ("levels", "program", r#"
static uint64_t twist(uint64_t a, uint64_t b) { return (a - b) ^ b; }
static uint64_t middle(uint64_t a, uint64_t b) { return a < b ? twist(a, b) + a : twist(b, a); }
static uint64_t reference(uint64_t a, uint64_t b) { uint64_t m = middle(b, a); return middle(m, a + b) | twist(a, m); }
"#),
    ("sharing", "caller", r#"
static uint64_t reference(uint64_t left, uint64_t right) {
    uint64_t saved = left | right, first = right - left, second = left - right, shared = first + saved;
    return (shared + shared) + (first + (first + second));
}
"#),
    ("calls", "caller", r#"
static uint64_t reference(uint64_t a, uint64_t b) { return (a + b) ^ UINT64_C(0x0123456789abcdef); }
"#),
];
// A call's result as the next call's argument, and leaves that write
// several registers.
const COMPOSED: [Case; 3] = [
    ("composition", "caller", r#"
static uint64_t reference(uint64_t a, uint64_t b) { uint64_t first = b - a; return (a | b) ^ (first + b - 3); }
"#),
    ("multi_register", "caller", r#"
static uint64_t leaf(uint64_t a, uint64_t b) { return (a + b) ^ (a - b); }
static uint64_t reference(uint64_t a, uint64_t b) { uint64_t first = leaf(b, a); return (a | b) ^ leaf(first + b, 3); }
"#),
    ("reused_callee", "caller", r#"
static uint64_t reference(uint64_t a, uint64_t b) { return (a + b + b) ^ (a ^ b); }
"#),
];
// Values live across calls, saved by the caller.
const SAVED: [Case; 3] = [
    ("multi_stack_save", "caller", r#"
static uint64_t leaf(uint64_t a, uint64_t b) { return (a ^ b) | ((a & b) ^ (a | b)); }
static uint64_t reference(uint64_t a, uint64_t b) { return (a | b) - ((a & b) + ((a - b) ^ leaf(a + b, a))); }
"#),
    ("stack_local", "caller", r#"
static uint64_t reference(uint64_t a, uint64_t b) { return (a + b) ^ (a ^ b); }
"#),
    ("stack_save", "caller", r#"
static uint64_t leaf(uint64_t a, uint64_t b) { return (a + b) ^ (a - b); }
static uint64_t reference(uint64_t a, uint64_t b) {
    uint64_t first = leaf(a + b, a), updated = (a | b) ^ first;
    return updated - ((a & b) + ((a - b) ^ leaf(first, b)));
}
"#),
];

// Loops (issues/function-ir-verified-loop-planning.md): a recursion on a
// fuel compiled to a loop. One runs out of passes, one leaves at a test in
// its pass's tree, one calls a function in its pass, and one has loops
// under a branch, followed by more work, in a callee, and in a loop's pass
// (issues/function-ir-loops-anywhere.md).
const LOOPS: [Case; 4] = [
    ("loop_triangle", "triangle", r#"
static uint64_t reference(uint64_t a, uint64_t b) { for (uint64_t n = a & 1023; n != 0; --n) b += n; return b; }
"#),
    ("loop_multiply", "multiply", r#"
static uint64_t reference(uint64_t a, uint64_t b) { return a * b; }
"#),
    ("loop_settle", "settle", r#"
static uint64_t reference(uint64_t x, uint64_t y) {
    for (unsigned i = 0; i < 100; ++i) { if ((x & 7) == 0) return x; x = (x + y) ^ (x - y); y += 1; }
    return x ^ y;
}
"#),
    ("loop_anywhere", "anywhere", r#"
static uint64_t sum_down(uint64_t fuel, uint64_t n, uint64_t acc) {
    for (; fuel != 0; --fuel) { if (n == 0) return acc; acc += n; n -= 1; }
    return acc;
}
static uint64_t triangle(uint64_t a) { uint64_t n = a & 255; return sum_down(n, n, 0); }
static uint64_t nested(uint64_t fuel, uint64_t n, uint64_t acc) {
    for (; fuel != 0; --fuel) { if (n == 0) return acc; acc += triangle(n); n -= 1; }
    return acc;
}
static uint64_t reference(uint64_t a, uint64_t b) {
    uint64_t m = a & 63;
    if (a < b) { uint64_t t = sum_down(m, m, b); return t + triangle(b + t); }
    return nested(m, m, b) ^ a;
}
"#),
];

// Loops bounded by a measure (issues/function-ir-loop-measure-recursion.md):
// a `decreases` function compiled to a loop of at most its measure's
// passes, the bound a parameter or computed first.
const MEASURED: [Case; 3] = [
    ("loop_measure", "triangle", r#"
static uint64_t reference(uint64_t a, uint64_t b) { for (uint64_t n = a & 1023; n != 0; --n) b += n; return b; }
"#),
    ("loop_climb", "climbing", r#"
static uint64_t reference(uint64_t a, uint64_t b) {
    uint64_t lo = a & 255, hi = b & 1023, acc = b;
    for (; lo < hi; ++lo) acc = acc + acc + lo;
    return acc ^ lo;
}
"#),
    // A measured loop whose state is an `i64` (§16.13, round 4): signed
    // compare, arithmetic shift and the word's add/sub on the record's word.
    ("loop_signed", "signed_loop", r#"
static uint64_t reference(uint64_t a, uint64_t b) {
    int64_t x = (int64_t)b;
    for (uint64_t n = a & 1023; n != 0; --n) {
        int64_t s = (int64_t)n;
        x = x < s ? (int64_t)((uint64_t)x + (uint64_t)s) : (int64_t)((uint64_t)(x >> 1) - (uint64_t)s);
    }
    return (uint64_t)x;
}
"#),
];

// Shifts by constants (docs/native/runtime-fn-setups-design.md §16.13, round 3):
// one-bit SHL/SHR/SAR chains, a count of 64 or more legalized (zero, or
// SAR by 63), and an `i64`'s arithmetic shift. C's shifts by the width or
// more are undefined, so the references spell the legalized result.
const SHIFTS: [Case; 3] = [
    ("shifts", "shifted", r#"
static uint64_t reference(uint64_t a, uint64_t b) {
    uint64_t left = (a << 5) ^ b, right = (a >> 63) + (b >> 1), rotated = (a << 40) | (a >> 24);
    return (left + right) ^ rotated;
}
"#),
    ("shifts_past", "past", r#"
static uint64_t reference(uint64_t a, uint64_t b) { (void)a; return b; }
"#),
    ("shifts_signed", "signed_shifts", r#"
static uint64_t reference(uint64_t a, uint64_t b) { return (uint64_t)((int64_t)a >> 7) + (uint64_t)((int64_t)b >> 63); }
"#),
];

// Narrow words in 64-bit registers (issues/function-ir-narrow-arithmetic.md):
// a value of width n is kept zero-extended, and an ADD, a SUB or a left
// shift is followed by a shift left and back by 64 − n. Bytes whose carry
// and borrow are then tested, 32-bit words through a rotation and a
// constant with its top bit set, and one value through 64, 32, 16, 27, 32
// and 64 bits. The references compute at C's own narrow types, so an upper
// bit the compiled code let through shows in the result.
const NARROW: [Case; 3] = [
    ("narrow_bytes", "bytes", r#"
static uint64_t reference(uint64_t a, uint64_t b) {
    uint8_t x = (uint8_t)a, y = (uint8_t)b, sum = (uint8_t)(x + y), difference = (uint8_t)(x - y);
    uint8_t spread = (uint8_t)((uint8_t)(sum << 3) ^ (difference >> 2));
    uint8_t mixed = (uint8_t)((uint8_t)(spread + 167) | (x & y));
    if (sum < x) return (uint8_t)(mixed - 1);
    if (difference == 0) return x;
    return mixed;
}
"#),
    ("narrow_words", "words", r#"
static uint64_t reference(uint64_t a, uint64_t b) {
    uint32_t x = (uint32_t)a, y = (uint32_t)b, rotated = (x << 7) | (x >> 25);
    uint32_t sum = rotated + y + UINT32_C(2654435769);
    return y < UINT32_C(2147483648) ? (uint32_t)(sum - x) : (uint32_t)((sum ^ (y >> 31)) << 1);
}
"#),
    ("narrow_widths", "widths", r#"
static uint64_t reference(uint64_t a, uint64_t b) {
    uint32_t half = (uint32_t)a, odd = (uint32_t)b & UINT32_C(0x7ffffff);
    uint16_t narrow = (uint16_t)half;
    uint32_t grown = (uint16_t)(narrow + 65521);
    uint32_t joined = ((grown + odd) << 9) & UINT32_C(0x7ffffff);
    uint32_t back = joined + half;
    return (uint64_t)((back >> 3) ^ half) + a;
}
"#),
];

const CALLS: &[&str] = &["CallTo("];
// A loop is a `runtime fn`'s: its program and agreement are its generator's,
// from the `Compile` instances (docs/native/runtime-fn-setups-design.md §16.11),
// with nothing proved per loop in the certificate.
const LOOPED: &[&str] = &["::agrees(", "::program"];

#[test]
fn programs_with_calls_execute_levels() { execute("levels", &LEVELS, CALLS); }

#[test]
fn programs_with_calls_execute_composed() { execute("composed", &COMPOSED, CALLS); }

#[test]
fn programs_with_calls_execute_saved() { execute("saved", &SAVED, CALLS); }

#[test]
fn programs_with_shifts_execute() { execute("shifts", &SHIFTS, &[]); }

#[test]
fn programs_with_narrow_words_execute() { execute("narrow", &NARROW, &[]); }

#[test]
fn programs_with_loops_execute() { execute("loops", &LOOPS, LOOPED); }

#[test]
fn programs_with_measured_loops_execute() { execute("measured", &MEASURED, LOOPED); }

fn execute(group: &str, cases: &[Case], claims: &[&str]) {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let dir = root.join(format!("target/native-program-{group}-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    for &(file, symbol, reference) in cases {
        let assembly = dir.join(format!("{file}.s"));
        let result = Command::new(env!("CARGO_BIN_EXE_heather")).current_dir(&root)
            .args(["compile-x86", &format!("examples/x86-native/{file}.hthr"), symbol, "-o"]).arg(&assembly)
            .args(heather_cli::showcase::native_image_args()).args(["--kernel-workers", "1"])
            .output().unwrap();
        assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
        assert!(String::from_utf8_lossy(&result.stdout).contains("certified program bytes"), "{file} took the verified lowering");
        let certificate = std::fs::read_to_string(dir.join(format!("{file}.certificate.hthr"))).unwrap();
        for claim in ["_lowers()", "_agrees(", "_bytes()", "_entry_at()", "_returns<M>", "compiled_computes<M>("].iter().chain(claims) {
            assert!(certificate.contains(claim), "{file}: missing {claim}");
        }
        let driver = dir.join(format!("{file}.c"));
        std::fs::write(&driver, format!(r#"
#include <stdint.h>
#include <stdio.h>
extern uint64_t {symbol}(uint64_t, uint64_t);
{reference}
int main(void) {{
    uint64_t edges[] = {{0, 1, 2, 9, 10, (UINT64_C(1) << 32) - 1, UINT64_C(1) << 32, UINT64_C(1) << 63, UINT64_MAX}};
    for (unsigned i = 0; i < 9; ++i) for (unsigned j = 0; j < 9; ++j)
        if ({symbol}(edges[i], edges[j]) != reference(edges[i], edges[j])) return 1;
    uint64_t state = 1;
    for (unsigned i = 0; i < 10000; ++i) {{
        state = state * UINT64_C(6364136223846793005) + 1;
        uint64_t a = state;
        state = state * UINT64_C(6364136223846793005) + 1;
        uint64_t b = i & 1 ? state : state >> (i % 64);
        if ({symbol}(a, b) != reference(a, b)) return 2;
    }}
    puts("10081 pairs passed");
    return 0;
}}
"#)).unwrap();
        let binary = dir.join(file);
        let linked = Command::new("cc").args(["-std=c11", "-Wall", "-Wextra", "-Werror"])
            .arg(&driver).arg(&assembly).arg("-o").arg(&binary).output().unwrap();
        assert!(linked.status.success(), "{}", String::from_utf8_lossy(&linked.stderr));
        let run = Command::new(&binary).output().unwrap();
        assert!(run.status.success(), "{file}: {}", String::from_utf8_lossy(&run.stdout));
    }
    std::fs::remove_dir_all(dir).unwrap();
}

// A record of two words as a result (docs/native/runtime-fn-setups-design.md
// §16.16): `add_wide` returns a `Wide`, its first field in RAX and its
// second in RDX, which is how System V returns a C structure of two
// integer words. The certificate states both (`Prog::ComputesBoth`), and C
// reads the structure against a 128-bit reference.
#[test]
fn a_record_of_two_words_is_returned_in_rax_and_rdx() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let dir = root.join(format!("target/native-two-words-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let assembly = dir.join("two_words.s");
    let result = Command::new(env!("CARGO_BIN_EXE_heather")).current_dir(&root)
        .args(["compile-x86", "examples/x86-native/two_words.hthr", "add_wide", "-o"]).arg(&assembly)
        .args(heather_cli::showcase::native_image_args()).args(["--kernel-workers", "1"])
        .output().unwrap();
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    let text = std::fs::read_to_string(&assembly).unwrap();
    assert!(text.contains("# signature: add_wide(word, word) -> word, word"), "{text}");
    let certificate = std::fs::read_to_string(dir.join("two_words.certificate.hthr")).unwrap();
    for claim in ["_code().ComputesBoth(machine, ", "compiled_computes_both<M>(", "::agrees_also(", ".low, [", ".high])"] {
        assert!(certificate.contains(claim), "missing {claim}");
    }
    let driver = dir.join("main.c");
    std::fs::write(&driver, r#"
#include <stdint.h>
#include <stdio.h>
typedef struct { uint64_t low, high; } Wide;
extern Wide add_wide(uint64_t, uint64_t);
static int check(uint64_t a, uint64_t b) {
    unsigned __int128 sum = (unsigned __int128)a + b;
    Wide w = add_wide(a, b);
    return w.low == (uint64_t)sum && w.high == (uint64_t)(sum >> 64);
}
int main(void) {
    uint64_t edges[] = {0, 1, 2, (UINT64_C(1) << 32) - 1, UINT64_C(1) << 63, UINT64_MAX - 1, UINT64_MAX};
    for (unsigned i = 0; i < 7; ++i) for (unsigned j = 0; j < 7; ++j) if (!check(edges[i], edges[j])) return 1;
    uint64_t state = 1;
    for (unsigned i = 0; i < 10000; ++i) {
        state = state * UINT64_C(6364136223846793005) + 1;
        uint64_t a = state;
        state = state * UINT64_C(6364136223846793005) + 1;
        if (!check(a, state)) return 2;
    }
    puts("10049 pairs passed");
    return 0;
}
"#).unwrap();
    let binary = dir.join("two_words");
    let linked = Command::new("cc").args(["-std=c11", "-Wall", "-Wextra", "-Werror"])
        .arg(&driver).arg(&assembly).arg("-o").arg(&binary).output().unwrap();
    assert!(linked.status.success(), "{}", String::from_utf8_lossy(&linked.stderr));
    let run = Command::new(&binary).output().unwrap();
    assert!(run.status.success(), "{}", String::from_utf8_lossy(&run.stdout));
    std::fs::remove_dir_all(dir).unwrap();
}

// An enum as a parameter (docs/native/runtime-fn-setups-design.md §16.16):
// `tok_weight` takes a `TokKind`, passed as its tag word, the constructor's
// index, which is how C passes a C enum of the same constructors in the
// same order. The certificate states the code at every real value of the
// enum, its tag word passed (`RecInfo::enum_word`), and states no
// `Prog::Implements`, which would be over every word. C calls it at every
// constructor against a reference.
#[test]
fn an_enum_is_passed_as_its_tag_word() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let dir = root.join(format!("target/native-enum-tag-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let assembly = dir.join("enum_tag.s");
    let result = Command::new(env!("CARGO_BIN_EXE_heather")).current_dir(&root)
        .args(["compile-x86", "examples/x86-native/enum_tag.hthr", "tok_weight", "-o"]).arg(&assembly)
        .args(heather_cli::showcase::native_image_args()).args(["--kernel-workers", "1"])
        .output().unwrap();
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    let text = std::fs::read_to_string(&assembly).unwrap();
    assert!(text.contains("# signature: tok_weight(word, word) -> word"), "{text}");
    let certificate = std::fs::read_to_string(dir.join("enum_tag.certificate.hthr")).unwrap();
    for claim in ["a0: RecInfo::enum_at(enum_tag::tok_weight::world.tys, 0)", "[RecInfo::enum_word(enum_tag::tok_weight::world.tys, 0, a0), a1]",
        "_code().Computes(machine, "] {
        assert!(certificate.contains(claim), "missing {claim}");
    }
    assert!(!certificate.contains("_implements"), "an enum's function is stated at its real values only");
    let driver = dir.join("main.c");
    std::fs::write(&driver, r#"
#include <stdint.h>
#include <stdio.h>
enum TokKind { Ident, Number, Space, Punct, Other };
extern uint64_t tok_weight(enum TokKind, uint64_t);
static uint64_t reference(enum TokKind k, uint64_t n) {
    switch (k) { case Ident: return n + 3; case Number: return n + n; case Space: return 0; case Punct: return n; default: return 1; }
}
int main(void) {
    uint64_t ns[] = {0, 1, 2, 41, UINT64_C(1) << 63, UINT64_MAX - 2, UINT64_MAX};
    for (int k = Ident; k <= Other; ++k)
        for (unsigned i = 0; i < 7; ++i)
            if (tok_weight((enum TokKind)k, ns[i]) != reference((enum TokKind)k, ns[i])) return 1;
    puts("35 calls passed");
    return 0;
}
"#).unwrap();
    let binary = dir.join("enum_tag");
    let linked = Command::new("cc").args(["-std=c11", "-Wall", "-Wextra", "-Werror"])
        .arg(&driver).arg(&assembly).arg("-o").arg(&binary).output().unwrap();
    assert!(linked.status.success(), "{}", String::from_utf8_lossy(&linked.stderr));
    let run = Command::new(&binary).output().unwrap();
    assert!(run.status.success(), "{}", String::from_utf8_lossy(&run.stdout));
    std::fs::remove_dir_all(dir).unwrap();
}

// A function of eight words called from Rust (issues/function-call-past-six-words.md):
// `eight` passes its seventh and eighth on the stack to `spread` twice, and
// Rust passes its own the same way, `extern "sysv64"` with the certified
// bytes linked by `global_asm!`. The contract's `Stack::Passed` is what
// both callers meet.
#[test]
fn eight_words_are_called_from_rust() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let dir = root.join(format!("target/native-stack-words-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let assembly = dir.join("eight.s");
    let result = Command::new(env!("CARGO_BIN_EXE_heather")).current_dir(&root)
        .args(["compile-x86", "examples/x86-native/stack_words.hthr", "eight", "-o"]).arg(&assembly)
        .args(heather_cli::showcase::native_image_args()).args(["--kernel-workers", "1"])
        .output().unwrap();
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    let text = std::fs::read_to_string(&assembly).unwrap();
    assert!(text.contains("# signature: eight(word, word, word, word, word, word, word, word) -> word"), "{text}");
    let certificate = std::fs::read_to_string(dir.join("eight.certificate.hthr")).unwrap();
    // `Prog::Computes` at the eight words: its `Stack::Passed` is the contract's.
    assert!(certificate.contains("_code().Computes(machine, ") && certificate.contains(", [a0, a1, a2, a3, a4, a5, a6, a7], "),
        "the contract passes eight words");
    let driver = dir.join("driver.rs");
    std::fs::write(&driver, r#"
std::arch::global_asm!(include_str!("eight.s"), options(att_syntax));
extern "sysv64" { fn eight(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64) -> u64; }
fn spread(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64) -> u64 {
    ((a.wrapping_add(b) ^ c).wrapping_sub(d).wrapping_add(e ^ f).wrapping_sub(g)) ^ h
}
fn reference([a, b, c, d, e, f, g, h]: [u64; 8]) -> u64 {
    spread(h, g, f, e, d, c, b, a).wrapping_add(spread(a, b, c, d, e, f, g, h))
}
fn main() {
    let mut state: u64 = 1;
    for i in 0..10000u64 {
        let mut w = [0u64; 8];
        for x in w.iter_mut() {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            *x = if i % 3 == 0 { state >> (i % 64) } else { state };
        }
        let got = unsafe { eight(w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]) };
        if got != reference(w) { eprintln!("{w:?}: {got} is not {}", reference(w)); std::process::exit(1); }
    }
    println!("10000 calls of eight words passed");
}
"#).unwrap();
    let binary = dir.join("driver");
    let built = Command::new("rustc").args(["--edition", "2021", "-O"]).arg(&driver).arg("-o").arg(&binary).output().unwrap();
    assert!(built.status.success(), "{}", String::from_utf8_lossy(&built.stderr));
    let run = Command::new(&binary).output().unwrap();
    assert!(run.status.success() && String::from_utf8_lossy(&run.stdout).contains("10000 calls of eight words passed"),
        "{}{}", String::from_utf8_lossy(&run.stdout), String::from_utf8_lossy(&run.stderr));
    std::fs::remove_dir_all(dir).unwrap();
}

// A loop that is not a `runtime fn` is refused, naming the marker: the Rust
// reflector no longer compiles loops (what a `runtime fn` loop refuses is
// `lib/_tests/native/runtime/runtime_tests.hthr`'s to probe).
#[test]
fn unmarked_loops_are_refused() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let dir = root.join(format!("target/native-loop-refusals-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let source = "import bitvec;\nfn count(fuel: Nat, n, acc: BitVec(64)) → BitVec(64) {\n\
        match fuel { Zero => acc, Succ(k) => count(k, n.sub(BitVec::ofNat(1)), acc.add(n)) }\n}\n\
        fn unmarked(a, b: BitVec(64)) → BitVec(64) { count(a.toNat(), a, b) }\n";
    std::fs::write(dir.join("unmarked.hthr"), source).unwrap();
    let result = Command::new(env!("CARGO_BIN_EXE_heather")).current_dir(&root)
        .arg("compile-x86").arg(dir.join("unmarked.hthr")).args(["unmarked", "-o"]).arg(dir.join("unmarked.s"))
        .args(heather_cli::showcase::native_image_args()).args(["--kernel-workers", "1"])
        .output().unwrap();
    let stderr = String::from_utf8_lossy(&result.stderr);
    assert!(!result.status.success() && stderr.contains("mark it `runtime fn count`"), "{stderr}");
    std::fs::remove_dir_all(dir).unwrap();
}

// What the narrow lowering does not take yet is refused, not compiled as
// the 64-bit operation (issues/function-ir-narrow-arithmetic.md): zero
// extension does not keep the signed order or the sign an arithmetic shift
// copies (`lib/_tests/std/bitvec/bitvec_resize_tests.hthr`,
// `signed_wide_above`), so a narrow signed comparison, a narrow arithmetic
// shift and a sign extension have no code. Each reflects and agrees with
// its source; the refusal is the lowering's.
#[test]
fn narrow_signed_operations_are_refused() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let dir = root.join(format!("target/native-narrow-refusals-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let source = "import logic;\nimport bool;\nimport nat;\nimport list;\nimport option;\nimport pair;\n\
        import bitvec;\nimport bitvec_nat;\nimport tactic;\nimport char;\nimport string;\nimport rt;\n\
        import rt_lower;\nimport function_ir;\nimport function_ir_eval;\nimport runtime;\n\
        runtime fn signed_below(a, b: BitVec(64)) → BitVec(64) {\n\
            match a.truncate(32, 32).signed_lt_bit(b.truncate(32, 32)) { True => a, False => b }\n}\n\
        runtime fn signed_shift(a, b: BitVec(64)) → BitVec(64) {\n\
            a.truncate(32, 32).arithmetic_shift_right(3).zero_extend(32).add(b)\n}\n\
        runtime fn signed_widen(a, b: BitVec(64)) → BitVec(64) {\n\
            a.truncate(32, 32).sign_extend(32).add(b)\n}\n";
    std::fs::write(dir.join("signed.hthr"), source).unwrap();
    // The refusal says where: the node the lowering has no code for, as the
    // library's mirror of the emitter finds it (`function_ir_refusal`).
    for (function, node) in [("signed_below", "the node `4 = less32 2, 3`"), ("signed_shift", "= sar32 "),
        ("signed_widen", "the node `3 = sign_resize32to64 2`, placed in rax")] {
        let output = dir.join(format!("{function}.s"));
        let result = Command::new(env!("CARGO_BIN_EXE_heather")).current_dir(&root)
            .arg("compile-x86").arg(dir.join("signed.hthr")).args([function, "-o"]).arg(&output)
            .args(heather_cli::showcase::native_image_args()).args(["--kernel-workers", "1"])
            .output().unwrap();
        let stderr = String::from_utf8_lossy(&result.stderr);
        assert!(!result.status.success() && stderr.contains("the verified lowering refused this program"),
            "{function}: {stderr}");
        assert!(stderr.contains(node) && stderr.contains("the function's nodes, values by their ids:"), "{function}: {stderr}");
        assert!(!output.exists(), "{function}: a refused function wrote assembly");
    }
    std::fs::remove_dir_all(dir).unwrap();
}
