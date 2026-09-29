use crate::common;
use heather_elab::function_ir_source::{generate_elaborated_loop_x86, generate_elaborated_record_loop_x86, generate_elaborated_typed_x86, NativeLoopPlacement, RecordLoopPlacement};
use heather_elab::function_ir_x86_lower::{Gpr, Placements};

fn checker() -> heather_elab::Elaborator {
    let mut elab = common::base_image(common::MODULES.len());
    for (name, source) in [
        ("x86_64_structured_block", include_str!("../../../lib/std/arch/x86_64/structured_block.hthr")),
        ("x86_64_data_read", include_str!("../../../lib/std/arch/x86_64/data_read.hthr")),
        ("x86_64_access_code", include_str!("../../../lib/std/arch/x86_64/access_code.hthr")),
        ("x86_64_access_memory", include_str!("../../../lib/std/arch/x86_64/access_memory.hthr")),
        ("bitvec_nat", include_str!("../../../lib/std/bitvec/nat.hthr")),
        ("function_ir_loop", include_str!("../../../lib/function_ir_loop.hthr")),
        ("function_ir_loop_x86", include_str!("../../../lib/function_ir_loop_x86.hthr")),
        ("function_ir_loop_trace", include_str!("../../../lib/function_ir_loop_trace.hthr")),
    ] { elab.elab_module_source(name, source).unwrap_or_else(|e| panic!("{}", e.render(source))); }
    elab
}

// The loop's own steps go through the ordinary typed generator: no loop
// instruction is templated in Rust (docs/native-bounded-loops-design.md §5).
#[test]
fn loop_steps_select_through_the_shared_generator() {
    let mut elab = checker();
    elab.elab_module_source("loop_steps", "import function_ir_loop_x86; import bitvec; import bool;").unwrap();
    let mut text = String::new();
    for (prefix, source, inputs, temporaries, output) in [
        ("guard", "function_ir_loop_x86::loop_guard", vec![(0, Gpr::Rsi), (1, Gpr::Rdx), (2, Gpr::R12)],
            vec![Gpr::R13, Gpr::Rax, Gpr::Rbx, Gpr::R10, Gpr::R14], (3, Gpr::R13)),
        ("next_cursor", "function_ir_loop_x86::loop_next_cursor", vec![(0, Gpr::Rsi)], vec![Gpr::R10, Gpr::Rax], (1, Gpr::R10)),
        ("next_budget", "function_ir_loop_x86::loop_next_budget", vec![(0, Gpr::R12)], vec![Gpr::R14, Gpr::Rax], (1, Gpr::R14)),
        ("copy", "function_ir_loop_x86::loop_copy", vec![(0, Gpr::R10)], vec![Gpr::Rsi], (1, Gpr::Rsi)),
    ] {
        let emission = generate_elaborated_typed_x86(&elab, prefix, source, &Placements::from_iter(inputs), &temporaries,
            &Placements::from([output])).unwrap_or_else(|e| panic!("{prefix}: {e:?}"));
        text.push_str(&emission.text);
        text.push('\n');
    }
    let text = stitch(&text);
    elab.elab_module_source("loop_step_certificates", &text).unwrap_or_else(|e| panic!("{}", e.render(&text)));
}

fn search_placement() -> NativeLoopPlacement {
    NativeLoopPlacement {
        base: Gpr::Rdi, length: Gpr::Rbp, needle: Gpr::Rcx, cursor: Gpr::Rsi, budget: Gpr::R12,
        carry: Gpr::R11, flag: Gpr::R13, step: Gpr::Rbx,
        address: Gpr::R8, byte: Gpr::R9, payload: Gpr::Rax, next_cursor: Gpr::R10, next_budget: Gpr::R14,
        extra: vec![Gpr::Rdx, Gpr::R15],
    }
}

// The library prefix, and the same prefix with the clients loaded.
fn with_clients() -> (heather_elab::Elaborator, heather_elab::Elaborator) {
    let library = checker();
    let mut elab = library.semantic_image().elaborator();
    let source = include_str!("../../../examples/function-ir/readonly-loops.hthr");
    elab.elab_module_source("readonly_loops", source).unwrap_or_else(|e| panic!("{}", e.render(source)));
    elab.elab_module_source("loop_clients", CLIENT_CONTEXT).unwrap();
    (library, elab)
}
const CLIENT_CONTEXT: &str = "import function_ir_loop; import function_ir_loop_x86; import readonly_loops; import bitvec; import bool;";

fn search_certificate() -> (heather_elab::Elaborator, heather_elab::Elaborator, heather_elab::function_ir_source::LoopX86Emission) {
    let (library, mut elab) = with_clients();
    let emission = generate_elaborated_loop_x86(&elab, "search", "readonly_loops::first_match", &search_placement(), None)
        .unwrap_or_else(|e| panic!("{e:?}"));
    elab.elab_module_source("search_pieces", &emission.pieces).unwrap_or_else(|e| panic!("{}", e.render(&emission.pieces)));
    (library, elab, emission)
}

// First-match search compiled as a whole loop: every iteration's pieces come
// from the shared generators, and the certificate states the machine exit
// against the source function itself.
#[test]
fn search_loop_certificate_checks() {
    let (_, mut elab, emission) = search_certificate();
    elab.elab_module_source("search_native", &emission.text).unwrap_or_else(|e| panic!("{}", e.render(&emission.text)));
    #[cfg(all(target_arch = "x86_64", target_os = "linux"))]
    native_loop(&emission.bytes, false);
}

// The second client: counting, through the same generator and placement. It
// adds its source, and one fact about its step (count_body_advances), and no
// machine model (docs/native-shared-lowering-milestone).
#[test]
fn count_loop_certificate_checks() {
    let (_, mut elab) = with_clients();
    let emission = generate_elaborated_loop_x86(&elab, "count", "readonly_loops::count_occurrences", &search_placement(),
        Some("readonly_loops::count_body_advances")).unwrap_or_else(|e| panic!("{e:?}"));
    elab.elab_module_source("count_pieces", &emission.pieces).unwrap_or_else(|e| panic!("{}", e.render(&emission.pieces)));
    elab.elab_module_source("count_native", &emission.text).unwrap_or_else(|e| panic!("{}", e.render(&emission.text)));
    assert!(generate_elaborated_loop_x86(&elab, "count", "readonly_loops::count_occurrences", &search_placement(), None).is_err());
    #[cfg(all(target_arch = "x86_64", target_os = "linux"))]
    native_loop(&emission.bytes, true);
}

#[test]
fn slow_acceptance_loop_refusals() {
    let (library, elab, emission) = search_certificate();
    let back = u32::from_le_bytes(emission.bytes[emission.bytes.len() - 4..].try_into().unwrap());
    let exit = {
        let at = emission.bytes.windows(2).position(|w| w == [0x0f, 0x84]).unwrap() + 2;
        u32::from_le_bytes(emission.bytes[at..at + 4].try_into().unwrap())
    };
    // Each mutation must be refused where it is wrong, not by a missing name.
    for (name, from, to) in [
        ("back_edge", format!("ofNat(32, {back})"), format!("ofNat(32, {})", back + 1)),
        ("exit_edge", format!("ofNat(32, {exit})"), format!("ofNat(32, {})", exit - 1)),
        ("flag_placement", "flag := R13".to_string(), "flag := Rbx".to_string()),
        ("swapped_counters", "cursor := Rsi, budget := R12".to_string(), "cursor := R12, budget := Rsi".to_string()),
        ("carry_placement", "loop_in(R11, ".to_string(), "loop_in(Rax, ".to_string()),
    ] {
        let bad = emission.text.replace(&from, &to);
        assert_ne!(bad, emission.text, "{name}");
        let error = elab.semantic_image().elaborator().elab_module_source(name, &bad).expect_err(name).render(&bad);
        assert!(!error.contains("unbound") && !error.contains("ambiguous"), "{name}: {error}");
    }
    // A step function edited after compilation: the pieces name the source,
    // so they no longer check against it.
    let mut stale = library.semantic_image().elaborator();
    let source = include_str!("../../../examples/function-ir/readonly-loops.hthr").replace("True => Break(True)", "True => Break(False)");
    assert_ne!(source, include_str!("../../../examples/function-ir/readonly-loops.hthr"));
    stale.elab_module_source("readonly_loops", &source).unwrap_or_else(|e| panic!("{}", e.render(&source)));
    stale.elab_module_source("loop_clients", CLIENT_CONTEXT).unwrap();
    let error = stale.elab_module_source("search_pieces", &emission.pieces).expect_err("stale source").render(&emission.pieces);
    assert!(!error.contains("unbound") && !error.contains("ambiguous"), "stale: {error}");
    // Counting's one obligation is about its own step: the same fact proved
    // of another step does not stand in for it.
    let (_, mut elab) = with_clients();
    let other = "import function_ir_loop; import readonly_loops; import bitvec; import nat; \
        fn keep_body(needle: BitVec(8), cursor: Nat, byte: BitVec(8), count: Nat) → LoopStep<Nat> { Continue(count) } \
        theorem keep_advances(): LoopAdvancesByAtMostOne(ReadonlyLoop<Nat>(keep_body)) { λ needle cursor byte count => count.le_succ_r(count, count.le_refl()) }";
    elab.elab_module_source("other_step", other).unwrap_or_else(|e| panic!("{}", e.render(other)));
    elab.elab_module_source("loop_clients", &format!("{CLIENT_CONTEXT} import other_step;")).unwrap();
    let emission = generate_elaborated_loop_x86(&elab, "count", "readonly_loops::count_occurrences", &search_placement(),
        Some("other_step::keep_advances")).unwrap_or_else(|e| panic!("{e:?}"));
    elab.elab_module_source("count_pieces", &emission.pieces).unwrap_or_else(|e| panic!("{}", e.render(&emission.pieces)));
    let error = elab.elab_module_source("count_native", &emission.text).expect_err("another step's advance").render(&emission.text);
    assert!(!error.contains("unbound") && !error.contains("ambiguous"), "advance: {error}");
}

// The published bytes against the source loop's outcomes, through a test-only
// trampoline that loads the head registers from a struct and stores the exit
// registers back (not an ABI; design §7). A guard page follows the buffer.
#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
fn native_loop(bytes: &[u8], counting: bool) {
    use std::process::Command;
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let dir = std::env::temp_dir().join(format!("heather-loop-{}-{nonce}", std::process::id()));
    std::fs::create_dir(&dir).unwrap();
    let loop_bytes = bytes.iter().map(u8::to_string).collect::<Vec<_>>().join(",");
    std::fs::write(dir.join("code.s"), format!(".intel_syntax noprefix
.text
.global search_run
search_run:
    push rbx
    push rbp
    push r12
    push r13
    push r14
    push r15
    push rdi
    mov rbp, [rdi+8]
    mov rcx, [rdi+16]
    mov rsi, [rdi+24]
    mov r12, [rdi+32]
    mov r11, [rdi+40]
    mov rdi, [rdi]
    .byte {loop_bytes}
    pop rax
    mov [rax+24], rsi
    mov [rax+32], r12
    mov [rax+40], r11
    mov [rax+48], r13
    pop r15
    pop r14
    pop r13
    pop r12
    pop rbp
    pop rbx
    ret
.section .note.GNU-stack,\"\",@progbits
")).unwrap();
    std::fs::write(dir.join("driver.c"), r#"
#include <stdint.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>
#include <assert.h>
typedef struct { const uint8_t *base; uint64_t length, needle, cursor, budget, carry, flag; } Loop;
extern void search_run(Loop *);
// loop_run for first_match or count_occurrences: end first, then budget,
// then the read.
static void expect(const uint8_t *p, uint64_t len, uint64_t needle, uint64_t c, uint64_t b, uint64_t k) {
    Loop run = { p, len, needle, c, b, k, 7 };
    uint64_t flag = 0;
    for (;;) {
        if (c >= len) break;
        if (b == 0) break;
        uint8_t byte = p[c];
        c++; b--;
#ifdef COUNTING
        if (byte == needle) k++;
#else
        if (byte == needle) { k = 1; flag = 1; break; }
#endif
    }
    search_run(&run);
    assert(run.flag == flag && run.cursor == c && run.budget == b && run.carry == k);
    // The exit interface reads the outcome back without the reference.
    if (flag == 0 && c < len) assert(b == 0);
}
int main(void) {
    long page = sysconf(_SC_PAGESIZE);
    uint8_t *m = mmap(0, page*2, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
    assert(m != MAP_FAILED);
    assert(mprotect(m+page, page, PROT_NONE) == 0);
    enum { N = 48 };
    uint8_t *p = m + page - N;
    for (unsigned i = 0; i < N; i++) p[i] = (uint8_t)(i * 37 + 11);
    p[N-1] = p[5];
    const uint64_t budgets[] = {0, 1, 2, 3, 47, 48, 49, UINT64_C(1)<<40};
    for (unsigned needle = 0; needle < 256; needle++)
        for (uint64_t len = 0; len <= N; len += (len < 4 ? 1 : 11))
            for (uint64_t c = 0; c <= len; c++)
                for (unsigned bi = 0; bi < sizeof budgets / sizeof *budgets; bi++)
                    for (unsigned ki = 0; ki < 3; ki++)
                        expect(p + (N - len), len, needle, c, budgets[bi], ki < 2 ? ki : 1000);
    assert(munmap(m, page*2) == 0);
}
"#).unwrap();
    let output = Command::new("cc").args(["-O1", "-Wall", "-Wextra", "-Werror"]).args(counting.then_some("-DCOUNTING"))
        .arg(dir.join("driver.c")).arg(dir.join("code.s"))
        .arg("-o").arg(dir.join("run")).output().unwrap();
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    assert!(Command::new(dir.join("run")).status().unwrap().success());
    std::fs::remove_dir_all(dir).unwrap();
}

// A consumed Nat: the count is a word port, Succ is an add, and the typed
// certificate states both results against count_body itself.
#[test]
fn count_body_carries_its_count_as_a_word() {
    let (_, mut elab) = with_clients();
    let emission = generate_elaborated_typed_x86(&elab, "count", "readonly_loops::count_body",
        &Placements::from([(0, Gpr::Rcx), (2, Gpr::R9), (3, Gpr::R11)]),
        &[Gpr::Rax, Gpr::Rbx, Gpr::Rdx, Gpr::R8, Gpr::R10, Gpr::R14, Gpr::R15],
        &Placements::from([(4, Gpr::Rax), (5, Gpr::Rbx)])).unwrap_or_else(|e| panic!("{e:?}"));
    elab.elab_module_source("count_typed", &emission.text).unwrap_or_else(|e| panic!("{}", e.render(&emission.text)));
}

// Controls for the word bridges: each must refuse the wrapping or reversed case.
#[test]
fn loop_word_lemmas_refuse_what_they_must() {
    let mut elab = checker();
    let imports = "import function_ir_loop; import function_ir_loop_x86; import function_ir_loop_trace; import bitvec; import bool; import nat; import logic;";
    let positive = format!("{imports} theorem guard_ends(c, l, b: BitVec(64)): function_ir_loop_x86::loop_guard(c, l, b) = function_ir_loop_x86::loop_guard(c, l, b) {{ refl }}");
    elab.elab_module_source("positive", &positive).unwrap_or_else(|e| panic!("{}", e.render(&positive)));
    for (name, body) in [
        // An empty budget has no predecessor to decrement to.
        ("budget_wrap", "theorem bad(word: BitVec(64), placed: LoopWord(64, word, 0)): LoopWord(64, function_ir_loop_x86::loop_next_budget(word), 0) { loop_budget_decrement(word, 0, placed) }"),
        // The guard never continues at the end of input, whatever the budget.
        ("guard_polarity", "theorem bad(cw, lw, bw: BitVec(64), c, l, b: Nat, pc: LoopWord(64, cw, c), pl: LoopWord(64, lw, l), pb: LoopWord(64, bw, b), ended: nat::Nat::leb(l, c) = True): function_ir_loop_x86::loop_guard(cw, lw, bw) = True { trans(loop_guard_word(cw, lw, bw, c, l, b, pc, pl, pb), j(sym(ended), λ e _ => match e { True => False, False => nat::Nat::leb(1, b) } = True, refl)) }"),
        // 2^48 is not a low-canonical bound.
        ("canonical_bound", "theorem bad(buffer: ReadonlyBytes, c: Nat, address: BitVec(64), placed: LoopWord(64, address, buffer.base + c), open: nat::Nat::leb(buffer.length, c) = False, low: buffer.base + buffer.length <= nat::Nat::pow(2, 48)): @bitvec::BitVec::drop_low(47, 17, address) = @bitvec::BitVec::zero(17) { loop_address_canonical(buffer, c, address, placed, open, low) }"),
    ] {
        let text = format!("{imports} {body}");
        heather_syntax::parse_file(&text).unwrap();
        let error = elab.semantic_image().elaborator().elab_module_source(name, &text).expect_err(name).render(&text);
        assert!(!error.contains("unbound") && !error.contains("ambiguous"), "{name}: {error}");
    }
}

fn stitch(text: &str) -> String {
    let mut imports = std::collections::BTreeSet::new();
    let mut body = String::new();
    for line in text.lines() {
        if line.starts_with("import ") { imports.insert(line); }
        else { body.push_str(line); body.push('\n'); }
    }
    format!("{}\n{body}", imports.into_iter().collect::<Vec<_>>().join("\n"))
}

// A loop over a record state (docs/native-wc-design.md §4): `wc`'s step over
// { lines, words, bytes, inside }. The fields sit in registers of their own
// and one iteration updates them in place, one at a time.
const WC_SOURCE: &str = r#"
import bitvec; import bool; import logic; import nat; import function_ir_loop;
record WcState { lines: Nat, words: Nat, bytes: Nat, inside: Bool }
fn newline_byte(b: BitVec(8)) → Bool {
    match b.unsigned_lt_bit(BitVec::ofNat(10)) { True => False, False => b.unsigned_lt_bit(BitVec::ofNat(11)) }
}
fn space_byte(b: BitVec(8)) → Bool {
    match b.unsigned_lt_bit(BitVec::ofNat(14)) {
        True => match b.unsigned_lt_bit(BitVec::ofNat(9)) { True => False, False => True },
        False => match b.unsigned_lt_bit(BitVec::ofNat(32)) { True => False, False => b.unsigned_lt_bit(BitVec::ofNat(33)) },
    }
}
fn wc_body(needle: BitVec(8), cursor: Nat, byte: BitVec(8), s: WcState) → LoopStep<WcState> {
    match space_byte(byte) {
        True => match newline_byte(byte) {
            True => Continue(WcState(Succ(s.lines), s.words, Succ(s.bytes), False)),
            False => Continue(WcState(s.lines, s.words, Succ(s.bytes), False)),
        },
        False => match s.inside {
            True => Continue(WcState(s.lines, s.words, Succ(s.bytes), True)),
            False => Continue(WcState(s.lines, Succ(s.words), Succ(s.bytes), True)),
        },
    }
}
fn count_wc(buffer: ReadonlyBytes, needle: BitVec(8), budget: Nat, cursor: Nat, carry: WcState) → LoopOutcome<WcState> {
    bounded_readonly<WcState>(buffer, needle, budget, cursor, carry, wc_body)
}
fn WcAdvances(step: LoopStep<WcState>, s: WcState) → Type {
    (loop_step_payload(step).lines <= Succ(s.lines)) ∧ ((loop_step_payload(step).words <= Succ(s.words)) ∧
        (loop_step_payload(step).bytes <= Succ(s.bytes)))
}
theorem wc_inside_advances(s: WcState): WcAdvances(match s.inside {
        True => Continue(WcState(s.lines, s.words, Succ(s.bytes), True)),
        False => Continue(WcState(s.lines, Succ(s.words), Succ(s.bytes), True)),
    }, s) {
    match s.inside as λ i => WcAdvances(match i {
            True => Continue(WcState(s.lines, s.words, Succ(s.bytes), True)),
            False => Continue(WcState(s.lines, Succ(s.words), Succ(s.bytes), True)),
        }, s) {
        True => ⟨s.lines.le_succ_r(s.lines, s.lines.le_refl()), ⟨s.words.le_succ_r(s.words, s.words.le_refl()), Succ(s.bytes).le_refl()⟩⟩,
        False => ⟨s.lines.le_succ_r(s.lines, s.lines.le_refl()), ⟨Succ(s.words).le_refl(), Succ(s.bytes).le_refl()⟩⟩,
    }
}
theorem wc_newline_advances(byte: BitVec(8), s: WcState): WcAdvances(match newline_byte(byte) {
        True => Continue(WcState(Succ(s.lines), s.words, Succ(s.bytes), False)),
        False => Continue(WcState(s.lines, s.words, Succ(s.bytes), False)),
    }, s) {
    match newline_byte(byte) as λ n => WcAdvances(match n {
            True => Continue(WcState(Succ(s.lines), s.words, Succ(s.bytes), False)),
            False => Continue(WcState(s.lines, s.words, Succ(s.bytes), False)),
        }, s) {
        True => ⟨Succ(s.lines).le_refl(), ⟨s.words.le_succ_r(s.words, s.words.le_refl()), Succ(s.bytes).le_refl()⟩⟩,
        False => ⟨s.lines.le_succ_r(s.lines, s.lines.le_refl()), ⟨s.words.le_succ_r(s.words, s.words.le_refl()), Succ(s.bytes).le_refl()⟩⟩,
    }
}
// Every Nat field grows by at most one per byte, in declaration order: the
// shape the record loop's invariant reads.
theorem wc_body_advances(): (needle: BitVec(8)) → (cursor: Nat) → (byte: BitVec(8)) → (s: WcState) →
    (loop_step_payload(wc_body(needle, cursor, byte, s)).lines <= Succ(s.lines)) ∧
    ((loop_step_payload(wc_body(needle, cursor, byte, s)).words <= Succ(s.words)) ∧
        (loop_step_payload(wc_body(needle, cursor, byte, s)).bytes <= Succ(s.bytes))) {
    λ needle cursor byte s => match space_byte(byte) as λ sp => WcAdvances(match sp {
            True => match newline_byte(byte) {
                True => Continue(WcState(Succ(s.lines), s.words, Succ(s.bytes), False)),
                False => Continue(WcState(s.lines, s.words, Succ(s.bytes), False)),
            },
            False => match s.inside {
                True => Continue(WcState(s.lines, s.words, Succ(s.bytes), True)),
                False => Continue(WcState(s.lines, Succ(s.words), Succ(s.bytes), True)),
            },
        }, s) {
        True => wc_newline_advances(byte, s),
        False => wc_inside_advances(s),
    }
}
"#;

fn wc_placement() -> RecordLoopPlacement {
    RecordLoopPlacement {
        base: Gpr::Rdi, length: Gpr::Rbp, needle: Gpr::Rcx, cursor: Gpr::Rsi, budget: Gpr::R12,
        flag: Gpr::R10, step: Gpr::Rbx, byte: Gpr::R9,
        fields: vec![Gpr::R13, Gpr::R14, Gpr::R15, Gpr::R8],
        scratch: vec![Gpr::R11, Gpr::Rax, Gpr::Rdx],
    }
}

#[test]
fn record_state_loop_certificate_checks() {
    let mut elab = checker().semantic_image().elaborator();
    elab.elab_module_source("wc_loop", WC_SOURCE).unwrap_or_else(|e| panic!("{}", e.render(WC_SOURCE)));
    elab.elab_module_source("wc_context", "import function_ir_loop; import function_ir_loop_x86; import wc_loop; import bitvec; import bool;").unwrap();
    let emission = generate_elaborated_record_loop_x86(&elab, "wc", "wc_loop::count_wc", &wc_placement(), "wc_loop::wc_body_advances")
        .unwrap_or_else(|e| panic!("{e:?}"));
    elab.elab_module_source("wc_pieces", &emission.pieces).unwrap_or_else(|e| panic!("{}", e.render(&emission.pieces)));
    elab.elab_module_source("wc_native", &emission.text).unwrap_or_else(|e| panic!("{}", e.render(&emission.text)));
}
