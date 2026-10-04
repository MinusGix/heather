//! The read profile's shared pieces (docs/native-read-until-eof-design.md,
//! docs/native-stream-filter-design.md §6): the support library every program
//! that reads stdin stands on, the read head, the failure tail and the write
//! loop as layouts, the written file's facts, the claims' shape, and the
//! decimal line's formatter. The one process that uses them is the stream
//! filter (`read_filter`).
use heather_elab::function_ir_source::generate_elaborated_piece_x86;
use heather_elab::function_ir_x86_lower::{encode_structured, Gpr, Instruction, Placements};
use heather_elab::heather_emit::Module;
use heather_elab::Elaborator;

use super::layout::{Layout, JMP, JS, JZ};

// Bundled after the base support for a program that reads stdin: the loop
// contract and its native certificates, fetched execution, the Linux trace
// and its determinism, the profile's memory view and the read's pieces.
pub(super) const SUPPORT: &[(&str, &str)] = &[
    ("omega", include_str!("../../../../lib/std/omega.hthr")),
    ("bitvec_nat", include_str!("../../../../lib/std/bitvec/bitvec_nat.hthr")),
    ("x86_64_data_read", include_str!("../../../../lib/std/arch/x86_64/x86_64_data_read.hthr")),
    ("x86_64_access_code", include_str!("../../../../lib/std/arch/x86_64/x86_64_access_code.hthr")),
    ("x86_64_access_memory", include_str!("../../../../lib/std/arch/x86_64/x86_64_access_memory.hthr")),
    ("x86_64_fetched_code", include_str!("../../../../lib/std/arch/x86_64/x86_64_fetched_code.hthr")),
    ("x86_64_layout", include_str!("../../../../lib/std/arch/x86_64/x86_64_layout.hthr")),
    ("function_ir_loop", include_str!("../../../../lib/function_ir_loop.hthr")),
    ("function_ir_loop_x86", include_str!("../../../../lib/function_ir_loop_x86.hthr")),
    ("function_ir_loop_trace", include_str!("../../../../lib/function_ir_loop_trace.hthr")),
    ("x86_64_store", include_str!("../../../../lib/std/arch/x86_64/x86_64_store.hthr")),
    ("x86_64_step_forms", include_str!("../../../../lib/std/arch/x86_64/x86_64_step_forms.hthr")),
    ("linux_x86_64_io", include_str!("../../../../lib/linux_x86_64_io.hthr")),
    ("linux_x86_64_determinism", include_str!("../../../../lib/linux_x86_64_determinism.hthr")),
    ("elf64_io", include_str!("../../../../lib/elf64_io.hthr")),
    ("elf64_read_pieces", include_str!("../../../../lib/elf64_read_pieces.hthr")),
];

// The formatter's source and meaning, and the write loop: a printed count
// and printed fields both write a line through it.
pub(super) const WRITE_SUPPORT: &[(&str, &str)] = &[
    ("bitvec_omega", include_str!("../../../../lib/std/bitvec/bitvec_omega.hthr")),
    ("decimal_line", include_str!("../../../../lib/decimal_line.hthr")),
    ("elf64_print_pieces", include_str!("../../../../lib/elf64_print_pieces.hthr")),
    ("elf64_write_loop", include_str!("../../../../lib/elf64_write_loop.hthr")),
];
// The tail that prints a count as a decimal line (docs/native-first-program-design.md §10).
pub(super) const PRINT_SUPPORT: &[(&str, &str)] = &[
    ("elf64_count_print", include_str!("../../../../lib/elf64_count_print.hthr")),
];

/// A right-nested conjunction's component `i` of `count`.
pub(super) fn component(value: &str, i: usize, count: usize) -> String {
    let mut path = value.to_string();
    for _ in 0..i { path.push_str(".right"); }
    if i + 1 < count { path.push_str(".left"); }
    path
}
/// A right-nested pair of the items, `trivial` for none.
pub(super) fn tuple(items: &[String]) -> String {
    match items {
        [only] => only.clone(),
        [first, rest @ ..] => format!("⟨{first}, {}⟩", tuple(rest)),
        [] => "trivial".into(),
    }
}

// TEST RAX, RAX: the lowering's encoder has no TEST of its own; the
// certificate checks these bytes against the model's encoding.
pub(super) const TEST: [u8; 3] = [0x48, 0x85, 0xc0];
pub(super) const SYSCALL: [u8; 2] = [0x0f, 0x05];

pub(super) fn mov(destination: Gpr, immediate: u64) -> Instruction { Instruction::MovRI { destination, immediate } }
pub(super) fn copy(destination: Gpr, source: Gpr) -> Instruction { Instruction::MovRR { destination, source } }

pub(super) fn literal(bytes: &[u8]) -> String {
    format!("[{}]", bytes.iter().map(|b| format!("@bitvec::BitVec::ofNat(8, {b})")).collect::<Vec<_>>().join(", "))
}

/// `a ++ (b ++ (… ++ z))`.
pub(super) fn nested(parts: &[String]) -> String {
    match parts {
        [only] => only.clone(),
        [first, rest @ ..] => format!("{first} ++ ({})", nested(rest)),
        [] => "[]".into(),
    }
}

/// elf64_read_pieces's read head at `read`: read(0, page, 4096) (the fd set first), TEST, JZ to
/// `end` at end of file, JS to `failed` at a failed read.
pub(super) fn read_head(end: &'static str, failed: &'static str) -> Layout {
    use Gpr::*;
    Layout::default().label("read").fixed("entry", super::encode(&[mov(Rdi, 0), mov(Rax, 0), mov(Rsi, 0x410000), mov(Rdx, 4096)])).syscall()
        .fixed("test", TEST.to_vec()).jump("jz", JZ, end).jump("js", JS, failed)
}

/// elf64_read_pieces's failure tail at `at` (docs/native-syscall-failures-design.md
/// §4): RAX + 4 is zero exactly at -EINTR, whose JZ (`jump`) goes back to
/// `retry`; otherwise exit(1).
pub(super) fn fail_tail(at: &'static str, jump: &'static str, retry: &'static str) -> Layout {
    use Gpr::*;
    Layout::default().label(at).fixed("retry", super::encode(&[mov(Rbx, 4), Instruction::AddRR { destination: Rax, source: Rbx }]))
        .jump(jump, JZ, retry).fixed("fail", super::encode(&[mov(Rdi, 1), mov(Rax, 60)])).syscall()
}

/// elf64_write_loop's `write_loop_parts`: write(1, R9, R10) until nothing is
/// left, EINTR retried, any other failure exit 1; the all-sent JZ goes to
/// `done`, the loop's own exit(0) at `wexit` for a program's last write.
pub(super) fn write_loop(done: &'static str) -> Layout {
    use Gpr::*;
    let encode = super::encode;
    Layout::default().label("write").fixed("write", encode(&[copy(Rsi, R9), copy(Rdx, R10), mov(Rdi, 1), mov(Rax, 1)])).syscall()
        .fixed("test", TEST.to_vec()).jump("wjs", JS, "wfailed")
        .fixed("advance", encode(&[Instruction::AddRR { destination: R9, source: Rax }, Instruction::SubRR { destination: R10, source: Rax }]))
        .jump("wjz", JZ, done).jump("wjmp", JMP, "write")
        .then(fail_tail("wfailed", "wrjz", "write"))
        .label("wexit").fixed("exit", encode(&[mov(Rdi, 0), mov(Rax, 60)])).syscall()
}

/// The write loop's jumps, `{prefix}_print_jumps()`.
pub(super) fn print_jumps(module: &mut Module, prefix: &str, layout: &Layout) {
    let d = |jump| format!("@bitvec::BitVec::ofNat(32, {})", layout.displacement(jump));
    module.raw(format!("fn {prefix}_print_jumps() → PrintJumps {{ PrintJumps({}, {}, {}, {}) }}", d("wjs"), d("wjz"), d("wjmp"), d("wrjz")));
}
/// The written file's facts, for any layout of the read profile: the header
/// the producer wrote, the code as written (`chain` proves `code_term =
/// spelled`), its length (`length` proves `code_term.len() = total` over open
/// parts: evaluating the code's length would walk every generated byte), that
/// it fits the file's window, the image, and residency.
pub(super) fn image_facts(module: &mut Module, prefix: &str, code_term: &str, spelled: &str, chain: &str, file: &[u8],
    total: usize, length: &str) {
    let size = file.len();
    super::byte_chain(module, &format!("{prefix}_header"), &file[..232]);
    let measured = format!("theorem {prefix}_code_len(): {code_term}.len() = {total} {{ {length} }}\n");
    let fits = format!("j(sym({prefix}_code_len()), λ n _ => 232 + n <= 65536, Nat::leb_sound(232 + {total}, 65536, trivial))");
    let nonempty = format!("j(sym({prefix}_code_len()), λ n _ => 0 < n, Nat::leb_sound(1, {total}, trivial))");
    let sized = format!("j(sym({prefix}_code_len()), λ n _ => 232 + n = elf_size16(elf_byte({}), elf_byte({})), refl)", size & 255, size >> 8);
    module.raw(format!("\
theorem {prefix}_header_length(): {prefix}_header().len() = 232 {{ refl }}
// The code as the producer wrote it: each fixed piece's encoding, and the
// published bytes of what it generated.
theorem {prefix}_code_written(): {code_term} = {spelled} {{ {chain} }}
{measured}theorem {prefix}_code_fits(): 232 + {code_term}.len() <= 65536 {{
    {fits}
}}
// The file is the read profile's header, then the program.
fn {prefix}_file() → List<BitVec(8)> {{ {prefix}_header() ++ {code_term} }}
fn {prefix}_image() → IoElfImage({code_term}) {{
    IoElfImage({nonempty},
        elf_byte({low}), elf_byte({high}),
        {sized})
}}
theorem {prefix}_file_correct(): {prefix}_file() = io_elf_bytes({code_term}, {prefix}_image()) {{ refl }}
theorem {prefix}_written(): {prefix}_file() = {prefix}_header() ++ ({spelled}) {{
    cong_fn<List<BitVec(8)>, List<BitVec(8)>>(λ code => {prefix}_header() ++ code, {prefix}_code_written())
}}
// The memory the file is loaded into, whatever its frame and the rest of
// the address space hold.
fn {prefix}_io_image(frame: Nat → BitVec(8), rest: BitVec(64) → Option<BitVec(8)>) → IoImage {{ IoImage({prefix}_file(), frame, rest) }}
theorem {prefix}_resident(): (frame: Nat → BitVec(8)) → (rest: BitVec(64) → Option<BitVec(8)>) → (page: Nat → BitVec(8)) →
    CodeResident(io_fetch_access(), IoMemory({prefix}_io_image(frame, rest), page), {code_term},
    @bitvec::BitVec::ofNat(64, 0x4000e8)) {{
    eof_file_resident({prefix}_header(), {code_term}, {prefix}_header_length(), {prefix}_code_fits())
}}
", low = size & 255, high = size >> 8));
}

// A claim and its `_runs_every`: every run of the file from that start which
// got the same answers from Linux, whatever Linux left in RCX, R11 and a
// failed read's buffer, made exactly those events (linux_x86_64_determinism).
// The claim is proved again there, not named, so a refused claim is reported
// once.
pub(super) fn claims(module: &mut Module, prefix: &str, comment: &str, premises: &str, events: &str, proof: &str) {
    module.raw(format!("\
{comment}
theorem {prefix}_runs({premises}):
    LinuxRuns(io_linux(), {events}, io_initial({prefix}_io_image(frame, rest), page, gprs, flags)) {{
    {proof}
}}

// And that run is the run (linux_x86_64_determinism).
theorem {prefix}_runs_every({premises},
    run: List<LinuxEvent>, ran: LinuxRun(io_linux(), run, io_initial({prefix}_io_image(frame, rest), page, gprs, flags)),
    answers: SameResponses({events}, run)):
    run = {events} {{
    linux_runs_every(io_linux(), {events}, run, io_initial({prefix}_io_image(frame, rest), page, gprs, flags), {proof}, ran, answers)
}}
"));
}

/// The formatter certificates' prefix. Program prefixes end in `_native`, so
/// no program's declarations can share it.
pub(super) const FORMAT_PREFIX: &str = "print_format";

/// One of the formatter's certificates: a module of its own, and its bytes.
pub(super) struct FormatPart { pub module: String, pub prefix: String, pub text: String, pub bytes: Vec<u8> }

// The formatter at the profile's registers (elf64_print_pieces): the count in
// R11 and the page's base in R8 are read, never written; the word goes to
// RAX, the start to R9, the length to R10, each over the scratch the library
// fixes for it (`print_word_scratch` …), so what runs after it keeps it.
pub(super) fn generate_format(elab: &Elaborator, prefix: &str) -> Result<Vec<FormatPart>, String> {
    use Gpr::*;
    let parts: [(&str, Placements, Vec<Gpr>, Gpr); 3] = [
        ("line_word", Placements::from([(0, R11)]), vec![Rax, Rcx, Rdx, Rbx, R9, R10, R12, R13, R14, R15], Rax),
        ("line_start", Placements::from([(0, R8), (1, R11)]), vec![R9, Rcx, Rdx, Rbx, R10, R12, R13, R14, R15], R9),
        ("line_length", Placements::from([(0, R11)]), vec![R10, Rcx, Rdx, Rbx, R12, R13, R14, R15], R10),
    ];
    // Read the formatter in its checked declaration scope, independently of
    // the last generated module checked by the native producer.
    elab.with_module_scope("decimal_line", |elab| {
        parts.into_iter().map(|(function, inputs, temporaries, output)| {
            let part = format!("{prefix}_{function}");
            let emission = generate_elaborated_piece_x86(elab, &part, &format!("decimal_line::{function}"), &inputs, &temporaries, output)
                .map_err(|e| format!("{function}: {e:?}"))?;
            Ok(FormatPart { module: format!("{part}_format"), prefix: part, bytes: encode_structured(&emission.lowered), text: emission.text })
        }).collect()
    })?
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn formatter_generation_uses_its_checked_scope_after_an_unrelated_module() {
        let mut elab = super::super::native_test_base();
        let mut session = heather_cli::semantic::SemanticSession::new(Some(std::path::PathBuf::from(
            concat!(env!("CARGO_MANIFEST_DIR"), "/../../target/native-test-images"),
        )));
        for &(name, src) in SUPPORT.iter().chain(WRITE_SUPPORT).filter(|(name, _)|
            matches!(*name, "omega" | "bitvec_nat" | "x86_64_store" | "bitvec_omega" | "decimal_line"))
        {
            super::super::check_module(&mut elab, &mut session, &heather_cli::loader::Module {
                name: name.into(), path: name.into(), src: src.into(),
            }).unwrap();
        }
        let before = generate_format(&elab, "scope_probe").unwrap();
        elab.elab_module_source("unrelated", "fn line_word(n: Nat) -> Nat { n }").unwrap();
        // The current module has no import of decimal_line; qualification
        // cannot bypass that restriction in ordinary source/reflection.
        assert!(elab.fn_body_code("decimal_line::line_word").is_err());
        let after = generate_format(&elab, "scope_probe").unwrap();
        assert_eq!(before.len(), 3);
        assert_eq!(after.len(), before.len());
        for (a, b) in before.iter().zip(&after) {
            assert_eq!(a.module, b.module);
            assert_eq!(a.prefix, b.prefix);
            assert_eq!(a.text, b.text);
            assert_eq!(a.bytes, b.bytes);
        }
        assert!(elab.fn_body_code("decimal_line::line_word").is_err(), "generation must restore the caller's scope");
    }
}
