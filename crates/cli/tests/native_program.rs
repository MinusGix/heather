//! Whole programs through `compile-x86`'s verified lowering: a function and
//! the functions it calls, compiled by `lower_program` and certified by
//! `compiled_returns`, linked against C references and run. The call
//! examples the per-function path built as executables before burn B2 are
//! here too (docs/native-program-logic-design.md §3.2).
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
static uint64_t settling(unsigned fuel, uint64_t x, uint64_t y) {
    for (; fuel != 0; --fuel) { if ((x & 7) == 0) return x; x = (x + y) ^ (x - y); y += 1; }
    return x ^ y;
}
static uint64_t triangle(uint64_t a) { uint64_t n = a & 255; return sum_down(n, n, 0); }
static uint64_t nested(uint64_t fuel, uint64_t n, uint64_t acc) {
    for (; fuel != 0; --fuel) { if (n == 0) return acc; acc += triangle(n); n -= 1; }
    return acc;
}
static uint64_t either(uint64_t a, uint64_t b) { return a < b || a == 5 ? a : b; }
static uint64_t reference(uint64_t a, uint64_t b) {
    uint64_t m = a & 63;
    if (a < b) { uint64_t t = sum_down(m, m, b); return settling(100, t, a) + t + triangle(b); }
    return either(nested(m, m, b), a);
}
"#),
];

// Loops bounded by a measure (issues/function-ir-loop-measure-recursion.md):
// a `decreases` function compiled to a loop of at most its measure's
// passes, the bound a parameter or computed first.
const MEASURED: [Case; 2] = [
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
];

const CALLS: &[&str] = &["CallTo("];
// A loop is a `runtime fn`'s: its program and agreement are its generator's,
// from the `Compile` instances (docs/runtime-fn-setups-design.md §16.11),
// with nothing proved per loop in the certificate.
const LOOPED: &[&str] = &["::agrees(", "::program"];

#[test]
fn programs_with_calls_execute_levels() { execute("levels", &LEVELS, CALLS); }

#[test]
fn programs_with_calls_execute_composed() { execute("composed", &COMPOSED, CALLS); }

#[test]
fn programs_with_calls_execute_saved() { execute("saved", &SAVED, CALLS); }

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
            .arg("--cache-dir").arg(heather_cli::showcase::native_test_images()).args(["--kernel-workers", "1"])
            .output().unwrap();
        assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
        assert!(String::from_utf8_lossy(&result.stdout).contains("certified program bytes"), "{file} took the verified lowering");
        let certificate = std::fs::read_to_string(dir.join(format!("{file}.certificate.hthr"))).unwrap();
        for claim in ["_lowers()", "_agrees(", "_bytes()", "_entry_at()", "_returns<M>", "compiled_returns<M>("].iter().chain(claims) {
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
        .arg("--cache-dir").arg(heather_cli::showcase::native_test_images()).args(["--kernel-workers", "1"])
        .output().unwrap();
    let stderr = String::from_utf8_lossy(&result.stderr);
    assert!(!result.status.success() && stderr.contains("mark it `runtime fn count`"), "{stderr}");
    std::fs::remove_dir_all(dir).unwrap();
}
