//! The read-until-end-of-file profile (docs/native-read-until-eof-design.md):
//! read stdin a page at a time into the call profile's RW page, count each
//! chunk with a certified counting loop into a running total, and at the empty
//! read exit with the total or print it. The process shape and its proof are
//! the library's (`lib/elf64_read_loop.hthr`, `lib/elf64_read_print.hthr`);
//! this producer generates the loop through the shared loop generator, lays
//! out the code, and instantiates the library theorem at the written file.
//! Nothing in it is about any one program.
use heather_elab::function_ir_source::{generate_elaborated_loop_x86, generate_elaborated_typed_x86, LoopX86Emission, NativeLoopPlacement};
use heather_elab::function_ir_x86_lower::{encode_structured, Gpr, Instruction, Placements};
use heather_elab::heather_emit::Module;
use heather_elab::Elaborator;

// Bundled after the base support, only for this profile: the loop contract and
// its native certificates, fetched execution, the Linux trace and the
// profile's memory view.
pub(super) const SUPPORT: &[(&str, &str)] = &[
    ("omega", include_str!("../../../../lib/std/omega.hthr")),
    ("bitvec_nat", include_str!("../../../../lib/std/bitvec/nat.hthr")),
    ("x86_64_data_read", include_str!("../../../../lib/std/arch/x86_64/data_read.hthr")),
    ("x86_64_access_code", include_str!("../../../../lib/std/arch/x86_64/access_code.hthr")),
    ("x86_64_access_memory", include_str!("../../../../lib/std/arch/x86_64/access_memory.hthr")),
    ("x86_64_fetched_code", include_str!("../../../../lib/std/arch/x86_64/fetched_code.hthr")),
    ("function_ir_loop", include_str!("../../../../lib/function_ir_loop.hthr")),
    ("function_ir_loop_x86", include_str!("../../../../lib/function_ir_loop_x86.hthr")),
    ("function_ir_loop_trace", include_str!("../../../../lib/function_ir_loop_trace.hthr")),
    ("x86_64_store", include_str!("../../../../lib/std/arch/x86_64/store.hthr")),
    ("linux_x86_64_io", include_str!("../../../../lib/linux_x86_64_io.hthr")),
    ("elf64_io", include_str!("../../../../lib/elf64_io.hthr")),
    ("elf64_read_loop", include_str!("../../../../lib/elf64_read_loop.hthr")),
];

// For `--print`: the formatter's source and meaning, and the process shape
// that writes the line (docs/native-first-program-design.md §10).
pub(super) const PRINT_SUPPORT: &[(&str, &str)] = &[
    ("bitvec_omega", include_str!("../../../../lib/std/bitvec/omega.hthr")),
    ("decimal_line", include_str!("../../../../lib/decimal_line.hthr")),
    ("elf64_read_print", include_str!("../../../../lib/elf64_read_print.hthr")),
];
pub(super) const PRINT_IMPORTS: &[&str] = &["elf64_read_print", "decimal_line", "x86_64_structured_block"];

// The profile's head registers are fixed (elf64_read_loop's ReadLoopPlacement);
// the rest is the loop's own scratch.
pub(super) fn placement() -> NativeLoopPlacement {
    NativeLoopPlacement {
        base: Gpr::Rdi, length: Gpr::Rbp, needle: Gpr::Rcx, cursor: Gpr::Rsi, budget: Gpr::R12,
        carry: Gpr::R11, flag: Gpr::R13, step: Gpr::Rbx,
        address: Gpr::R8, byte: Gpr::R9, payload: Gpr::Rax, next_cursor: Gpr::R10, next_budget: Gpr::R14,
        extra: vec![Gpr::Rdx, Gpr::R15],
    }
}

/// What a program names: its loop's source function and step-advance theorem,
/// the byte the loop is given, its specification, its `ReadEofComputes` fact
/// and the specification's additivity. Names are relative to the program's
/// module.
pub(super) struct Program<'a> {
    pub root: &'a str,
    pub source: &'a str,
    pub advance: &'a str,
    pub needle: u8,
    pub spec: &'a str,
    pub computes: &'a str,
    pub adds: &'a str,
    /// Write the count as a decimal line rather than exit with it.
    pub print: bool,
}

// The context the loop generator resolves names in, elaborated before it runs.
pub(super) fn context(program: &Program) -> String {
    let format = if program.print { " import decimal_line;" } else { "" };
    format!("import {}; import function_ir_loop; import function_ir_loop_x86; import bitvec; import bool;{format}", program.root)
}

pub(super) fn generate_loop(elab: &Elaborator, prefix: &str, program: &Program) -> Result<LoopX86Emission, String> {
    generate_elaborated_loop_x86(elab, prefix, &format!("{}::{}", program.root, program.source), &placement(),
        Some(&format!("{}::{}", program.root, program.advance))).map_err(|e| format!("{e:?}"))
}

// A near jump's bytes: JZ (0F 84), JS (0F 88) or JMP (E9), then rel32.
fn near(opcode: &[u8], displacement: u32) -> Vec<u8> { [opcode, &displacement.to_le_bytes()[..]].concat() }
fn forward(distance: usize) -> u32 { u32::try_from(distance).expect("the program fits a page") }
fn backward(distance: usize) -> u32 { 0u32.wrapping_sub(forward(distance)) }

// TEST RAX, RAX: the lowering's encoder has no TEST of its own; the
// certificate checks these bytes against the model's encoding.
const TEST: [u8; 3] = [0x48, 0x85, 0xc0];

// A failed syscall's path (docs/native-syscall-failures-design.md §4):
// RAX + 4 is zero exactly at -EINTR, which retries; otherwise exit(1).
fn retry_block() -> Vec<u8> {
    super::encode(&[Instruction::MovRI { destination: Gpr::Rbx, immediate: 4 }, Instruction::AddRR { destination: Gpr::Rax, source: Gpr::Rbx }])
}
fn fail_block() -> Vec<u8> {
    super::encode(&[Instruction::MovRI { destination: Gpr::Rdi, immediate: 1 }, Instruction::MovRI { destination: Gpr::Rax, immediate: 60 }])
}

// The outer loop's fixed pieces, in `eof_code`'s order, and its four jumps'
// displacements from the loop's length.
struct Pieces {
    init: Vec<u8>, entry: Vec<u8>, jz: Vec<u8>, js: Vec<u8>, setup: Vec<u8>, save: Vec<u8>, jmp: Vec<u8>,
    retry: Vec<u8>, rjz: Vec<u8>, fail: Vec<u8>, ed: u32, sd: u32, bd: u32, rd: u32,
}
fn pieces(needle: u8, loop_len: usize) -> Pieces {
    use Gpr::*;
    let mov = |destination, immediate| Instruction::MovRI { destination, immediate };
    let rr = |destination, source| Instruction::MovRR { destination, source };
    let init = super::encode(&[mov(R13, 0)]);
    let entry = super::encode(&[mov(Rax, 0), mov(Rdi, 0), mov(Rsi, 0x401000), mov(Rdx, 4096)]);
    let setup = super::encode(&[rr(Rbp, Rax), rr(R12, Rax), mov(Rdi, 0x401000), mov(Rcx, u64::from(needle)), mov(Rsi, 0), rr(R11, R13)]);
    let save = super::encode(&[rr(R13, R11)]);
    let (retry, fail) = (retry_block(), fail_block());
    // JS skips the chunk's setup, loop, save and jump back to the failure
    // path; JZ skips that and the failure path too. The jump back and the
    // retry's JZ return to the read, each from its own end.
    let chunk = setup.len() + loop_len + save.len() + 5;
    let sd = forward(chunk);
    let ed = forward(6 + chunk + retry.len() + 6 + fail.len() + 2);
    let span = entry.len() + 2 + TEST.len() + 6 + 6 + setup.len() + loop_len + save.len();
    let bd = backward(span + 5);
    let rd = backward(span + 5 + retry.len() + 6);
    Pieces { init, entry, jz: near(&[0x0f, 0x84], ed), js: near(&[0x0f, 0x88], sd), setup, save, jmp: near(&[0xe9], bd),
        retry, rjz: near(&[0x0f, 0x84], rd), fail, ed, sd, bd, rd }
}

fn literal(bytes: &[u8]) -> String {
    format!("[{}]", bytes.iter().map(|b| format!("@bitvec::BitVec::ofNat(8, {b})")).collect::<Vec<_>>().join(", "))
}

// The written code, spelled as the pieces: `looped` for the loop's bytes and
// `tail` for what follows the jump back.
fn spell(prefix: &str, looped: &str, tail: &str) -> String {
    format!("{prefix}_init_written() ++ ({prefix}_entry_written() ++ (linux_syscall_bytes() ++ ({prefix}_test_written() ++ \
        ({prefix}_jz_written() ++ ({prefix}_js_written() ++ ({prefix}_setup_written() ++ ({looped} ++ ({prefix}_save_written() ++ \
        ({prefix}_jmp_written() ++ ({prefix}_retry_written() ++ ({prefix}_rjz_written() ++ ({prefix}_fail_written() ++ \
        (linux_syscall_bytes() ++ {tail})))))))))))))")
}

/// What both profiles state about the written file: its pieces, the code as
/// written, the header and image, and the facts the two jumps need. `chain`
/// proves `code_term = spelled` from `refl` over the fixed pieces.
fn certify_file(module: &mut Module, prefix: &str, program: &Program, parts: &Pieces, loop_bytes: &[u8],
    tail: &[(&str, &[u8])], code_term: &str, spelled: &str, chain: &str, file: &[u8]) {
    let needle = format!("@bitvec::BitVec::ofNat(8, {})", program.needle);
    let fixed = [("init", &parts.init), ("entry", &parts.entry), ("test", &TEST.to_vec()), ("jz", &parts.jz), ("js", &parts.js),
        ("setup", &parts.setup), ("loop_bytes", &loop_bytes.to_vec()), ("save", &parts.save), ("jmp", &parts.jmp),
        ("retry", &parts.retry), ("rjz", &parts.rjz), ("fail", &parts.fail)];
    for (name, bytes) in fixed.iter().map(|(n, b)| (*n, b.as_slice())).chain(tail.iter().copied()) {
        module.raw(format!("fn {prefix}_{name}_written() → List<BitVec(8)> {{ {} }}", literal(bytes)));
    }
    let size = file.len();
    super::byte_chain(module, &format!("{prefix}_header"), &file[..232]);
    module.raw(format!("\
fn {prefix}_jumps() → EofJumps {{ EofJumps(@bitvec::BitVec::ofNat(32, {ed}), @bitvec::BitVec::ofNat(32, {sd}),
    @bitvec::BitVec::ofNat(32, {bd}), @bitvec::BitVec::ofNat(32, {rd})) }}
theorem {prefix}_header_length(): {prefix}_header().len() = 232 {{ refl }}
theorem {prefix}_loop_written(): {prefix}_bytes() = {prefix}_loop_bytes_written() {{ refl }}
// The code as the producer wrote it: each fixed piece's encoding, and the
// published bytes of what it generated.
theorem {prefix}_code_written(): {code_term} = {spelled} {{ {chain} }}
theorem {prefix}_fits(): 232 + {code_term}.len() <= 4096 {{
    j(sym({prefix}_code_written()), λ code _ => 232 + code.len() <= 4096, Nat::leb_sound(232 + ({spelled}).len(), 4096, trivial))
}}
// The file is the call profile's header, then the program.
fn {prefix}_file() → List<BitVec(8)> {{ {prefix}_header() ++ {code_term} }}
fn {prefix}_image() → CallElfImage({code_term}) {{
    CallElfImage(j(sym({prefix}_code_written()), λ code _ => 0 < code.len(), Nat::leb_sound(1, ({spelled}).len(), trivial)),
        elf_byte({low}), elf_byte({high}),
        refl, trivial)
}}
theorem {prefix}_file_correct(): {prefix}_file() = call_elf_bytes({code_term}, {prefix}_image()) {{ refl }}
theorem {prefix}_written(): {prefix}_file() = {prefix}_header() ++ ({spelled}) {{
    cong_fn<List<BitVec(8)>, List<BitVec(8)>>(λ code => {prefix}_header() ++ code, {prefix}_code_written())
}}
theorem {prefix}_resident(): (page: Nat → BitVec(8)) → CodeResident(io_fetch_access(), IoMemory({prefix}_file(), page), {code_term},
    @bitvec::BitVec::ofNat(64, 0x4000e8)) {{
    eof_file_resident({prefix}_header(), {code_term}, {prefix}_header_length(), {prefix}_fits())
}}

// Where the jumps land: JZ past the chunk's code and the failure path to the
// tail, JS past the chunk's code to the failure path, JMP and the retry's JZ
// back to the read. Closed facts about the written displacements.
theorem {prefix}_exit_reads(): {prefix}_jumps().ed.sign_extend(32).toNat() = eof_exit_skip({needle}, {prefix}_bytes()) {{
    j(sym({prefix}_loop_written()), λ b _ => {prefix}_jumps().ed.sign_extend(32).toNat() = eof_exit_skip({needle}, b),
        refl)
}}
theorem {prefix}_fail_reads(): {prefix}_jumps().sd.sign_extend(32).toNat() = eof_fail_skip({needle}, {prefix}_bytes()) {{
    j(sym({prefix}_loop_written()), λ b _ => {prefix}_jumps().sd.sign_extend(32).toNat() = eof_fail_skip({needle}, b),
        refl)
}}
theorem {prefix}_back_closes(): eof_loop_span({needle}, {prefix}_bytes()) + 5 + {prefix}_jumps().bd.sign_extend(32).toNat() = Nat::pow(2, 64) {{
    j(sym({prefix}_loop_written()), λ b _ => eof_loop_span({needle}, b) + 5 + {prefix}_jumps().bd.sign_extend(32).toNat() = Nat::pow(2, 64),
        refl)
}}
theorem {prefix}_retry_closes(): eof_retry_span({needle}, {prefix}_bytes()) + 6 + {prefix}_jumps().rd.sign_extend(32).toNat() = Nat::pow(2, 64) {{
    j(sym({prefix}_loop_written()), λ b _ => eof_retry_span({needle}, b) + 6 + {prefix}_jumps().rd.sign_extend(32).toNat() = Nat::pow(2, 64),
        refl)
}}
", low = size & 255, high = size >> 8, ed = parts.ed, sd = parts.sd, bd = parts.bd, rd = parts.rd));
}

// The arguments both claims pass the library, up to the program's facts.
fn common_arguments(prefix: &str, program: &Program) -> String {
    let (root, needle) = (program.root, format!("@bitvec::BitVec::ofNat(8, {})", program.needle));
    format!("{prefix}_file(), {prefix}_placement(), ReadLoopPlacement(refl, refl, refl, refl, refl, refl),
        {prefix}_loop_region(), {prefix}_code(), {prefix}_bytes(), {root}::{source}, {needle}, {root}::{spec},
        λ buffer needle budget cursor carry => {prefix}_loop_source_agreement(buffer, needle, budget, cursor, carry),
        λ access before buffer needle budget cursor carry bounded low head readable fits =>
            {prefix}_native(access, before, buffer, needle, budget, cursor, carry, bounded, low, head, readable, fits),
        {root}::{computes}, {root}::{adds}", source = program.source, spec = program.spec, computes = program.computes, adds = program.adds)
}

/// Lay out the program and write its certificate after the loop's (which the
/// caller has already put in `module`). Returns the file to publish.
pub(super) fn certify(module: &mut Module, prefix: &str, program: &Program, emission: &LoopX86Emission) -> Result<Vec<u8>, String> {
    let parts = pieces(program.needle, emission.bytes.len());
    let exit = super::encode(&[Instruction::MovRR { destination: Gpr::Rdi, source: Gpr::R13 }, Instruction::MovRI { destination: Gpr::Rax, immediate: 60 }]);
    let code = [parts.init.as_slice(), &parts.entry, &[0x0f, 0x05], &TEST, &parts.jz, &parts.js, &parts.setup, &emission.bytes, &parts.save,
        &parts.jmp, &parts.retry, &parts.rjz, &parts.fail, &[0x0f, 0x05], &exit, &[0x0f, 0x05]].concat();
    let file = super::calls::image(&code)?;
    let needle = format!("@bitvec::BitVec::ofNat(8, {})", program.needle);
    let root = program.root;
    let code_term = format!("read_loop_code({needle}, {prefix}_bytes(), {prefix}_jumps())");
    let tail = format!("({prefix}_exit_written() ++ linux_syscall_bytes())");
    let spelled = spell(prefix, &format!("{prefix}_loop_bytes_written()"), &tail);
    let chain = format!("j({prefix}_loop_written(), λ y _ => {code_term} = {}, refl)", spell(prefix, "y", &tail));
    certify_file(module, prefix, program, &parts, &emission.bytes, &[("exit", &exit)], &code_term, &spelled, &chain, &file);
    module.raw(format!("\
// The process claim for the written file: for every way the reads may split
// stdin into non-empty chunks, with EINTRs between them, ending at the empty
// read or at a failed read, a run that reads them all and exits with
// `{root}::{spec}` of their concatenation, or with 1 after the failure.
theorem {prefix}_runs(chunks: List<ReadStep>, ok: EofChunks(chunks), ending: ReadEnding, ending_ok: EofEnding(ending),
    room: {root}::{spec}(eof_input(chunks)) + 4096 < Nat::pow(2, 64), page: Nat → BitVec(8), gprs: Gprs, flags: Flags):
    LinuxRuns(io_linux(), eof_events(chunks, ending, [ExitEvent(bitvec_nat::word_of_nat(64, {root}::{spec}(eof_input(chunks))))]),
        io_initial({prefix}_file(), page, gprs, flags)) {{
    read_loop_runs({common}, {prefix}_jumps(), {prefix}_exit_reads(), {prefix}_fail_reads(), {prefix}_back_closes(),
        {prefix}_retry_closes(), {prefix}_resident(), chunks, ok, ending, ending_ok, room, page, gprs, flags)
}}
", spec = program.spec, common = common_arguments(prefix, program)));
    Ok(file)
}

pub(super) const IMPORTS: &[&str] = &["elf64_read_loop", "elf64_io", "elf64_calls", "elf64", "linux_x86_64_entry", "linux_x86_64_io", "function_ir_loop",
    "function_ir_loop_trace", "x86_64_fetched_code", "x86_64_fetch", "bitvec_nat", "x86_64", "bitvec", "list", "logic", "nat"];

/// One of the formatter's certificates: a module of its own, and its bytes.
pub(super) struct FormatPart { pub module: String, pub prefix: String, pub text: String, pub bytes: Vec<u8> }

// The formatter at the profile's registers (elf64_read_print): the count in
// R11 and the page's base in R8 are read, never written; the word goes to
// RAX, the start to R9, the length to R10, each kept by what runs after it.
pub(super) fn generate_format(elab: &Elaborator, prefix: &str) -> Result<Vec<FormatPart>, String> {
    use Gpr::*;
    let parts: [(&str, Placements, Vec<Gpr>, Placements); 3] = [
        ("line_word", Placements::from([(0, R11)]), vec![Rax, Rcx, Rdx, Rbx, R9, R10, R12, R13, R14, R15], Placements::from([(1, Rax)])),
        ("line_start", Placements::from([(0, R8), (1, R11)]), vec![R9, Rcx, Rdx, Rbx, R10, R12, R13, R14, R15], Placements::from([(2, R9)])),
        ("line_length", Placements::from([(0, R11)]), vec![R10, Rcx, Rdx, Rbx, R12, R13, R14, R15], Placements::from([(1, R10)])),
    ];
    parts.into_iter().map(|(function, inputs, temporaries, outputs)| {
        let part = format!("{prefix}_{function}");
        let emission = generate_elaborated_typed_x86(elab, &part, &format!("decimal_line::{function}"), &inputs, &temporaries, &outputs)
            .map_err(|e| format!("{function}: {e:?}"))?;
        Ok(FormatPart { module: format!("{part}_format"), prefix: part, bytes: encode_structured(&emission.lowered), text: emission.text })
    }).collect()
}

/// The printing profile's certificate: read to the end, count, write the count
/// as a decimal line, exit 0. As `certify`, after the loop's text.
pub(super) fn certify_print(module: &mut Module, prefix: &str, program: &Program, emission: &LoopX86Emission, format: &[FormatPart]) -> Result<Vec<u8>, String> {
    use Gpr::*;
    let parts = pieces(program.needle, emission.bytes.len());
    let mov = |destination, immediate| Instruction::MovRI { destination, immediate };
    let base = super::encode(&[Instruction::MovRR { destination: R11, source: R13 }, mov(R8, 0x401000)]);
    let store = vec![0x49, 0x89, 0x00];
    let write = super::encode(&[Instruction::MovRR { destination: Rsi, source: R9 }, Instruction::MovRR { destination: Rdx, source: R10 },
        mov(Rdi, 1), mov(Rax, 1)]);
    let advance = super::encode(&[Instruction::AddRR { destination: R9, source: Rax }, Instruction::SubRR { destination: R10, source: Rax }]);
    let exit = super::encode(&[mov(Rdi, 0), mov(Rax, 60)]);
    let (retry, fail) = (retry_block(), fail_block());
    // The write loop's jumps (elf64_read_print's `PrintJumps`): JS to its
    // failure path, JZ to exit(0) past it, JMP and the retry's JZ back to the
    // write.
    let psd = forward(advance.len() + 6 + 5);
    let pzd = forward(5 + retry.len() + 6 + fail.len() + 2);
    let span = write.len() + 2 + TEST.len() + 6 + advance.len() + 6;
    let pbd = backward(span + 5);
    let prd = backward(span + 5 + retry.len() + 6);
    let (wjs, wjz, wjmp, wrjz) = (near(&[0x0f, 0x88], psd), near(&[0x0f, 0x84], pzd), near(&[0xe9], pbd), near(&[0x0f, 0x84], prd));
    let [word, start, length] = format else { return Err("the formatter has three parts".into()) };
    let code = [parts.init.as_slice(), &parts.entry, &[0x0f, 0x05], &TEST, &parts.jz, &parts.js, &parts.setup, &emission.bytes, &parts.save,
        &parts.jmp, &parts.retry, &parts.rjz, &parts.fail, &[0x0f, 0x05],
        &base, &word.bytes, &start.bytes, &length.bytes, &store, &write, &[0x0f, 0x05], &TEST, &wjs, &advance, &wjz, &wjmp,
        &retry, &wrjz, &fail, &[0x0f, 0x05], &exit, &[0x0f, 0x05]].concat();
    let file = super::calls::image(&code)?;
    let needle = format!("@bitvec::BitVec::ofNat(8, {})", program.needle);
    let root = program.root;
    let (w, st, ln) = (&word.prefix, &start.prefix, &length.prefix);
    let code_term = format!("read_print_code({needle}, {prefix}_bytes(), {prefix}_jumps(), {w}_code(), {st}_code(), {ln}_code(), {prefix}_print_jumps())");
    let tail = |w: &str, st: &str, ln: &str| format!(
        "({prefix}_base_written() ++ ({w} ++ ({st} ++ ({ln} ++ ({prefix}_store_written() ++ ({prefix}_write_written() ++ \
        (linux_syscall_bytes() ++ ({prefix}_test_written() ++ ({prefix}_wjs_written() ++ ({prefix}_advance_written() ++ \
        ({prefix}_wjz_written() ++ ({prefix}_wjmp_written() ++ ({prefix}_retry_written() ++ ({prefix}_wrjz_written() ++ \
        ({prefix}_fail_written() ++ (linux_syscall_bytes() ++ ({prefix}_exit_written() ++ linux_syscall_bytes())))))))))))))))))");
    let layout = |looped: &str, w: &str, st: &str, ln: &str| spell(prefix, looped, &tail(w, st, ln));
    let original = (format!("{prefix}_bytes()"), format!("{w}_bytes()"), format!("{st}_bytes()"), format!("{ln}_bytes()"));
    let written = (format!("{prefix}_loop_bytes_written()"), format!("{w}_lit()"), format!("{st}_lit()"), format!("{ln}_lit()"));
    // The code, spelled as the pieces the producer wrote: fixed pieces by
    // evaluation, the loop's and the formatter's bytes by their lemmas.
    let mut chain = "refl".to_string();
    let steps = [
        (format!("{prefix}_loop_written()"), layout("y", &original.1, &original.2, &original.3)),
        (format!("{w}_bytes_are()"), layout(&written.0, "y", &original.2, &original.3)),
        (format!("{st}_bytes_are()"), layout(&written.0, &written.1, "y", &original.3)),
        (format!("{ln}_bytes_are()"), layout(&written.0, &written.1, &written.2, "y")),
    ];
    for (lemma, motive) in steps {
        chain = format!("j({lemma}, λ y _ => {code_term} = {motive}, {chain})");
    }
    let spelled = layout(&written.0, &written.1, &written.2, &written.3);
    module.raw(format!("fn {prefix}_print_jumps() → PrintJumps {{ PrintJumps(@bitvec::BitVec::ofNat(32, {psd}), \
        @bitvec::BitVec::ofNat(32, {pzd}), @bitvec::BitVec::ofNat(32, {pbd}), @bitvec::BitVec::ofNat(32, {prd})) }}"));
    certify_file(module, prefix, program, &parts, &emission.bytes, &[("base", &base), ("store", &store), ("write", &write),
        ("wjs", &wjs), ("advance", &advance), ("wjz", &wjz), ("wjmp", &wjmp), ("wrjz", &wrjz), ("exit", &exit)],
        &code_term, &spelled, &chain, &file);
    let pj = format!("{prefix}_print_jumps()");
    module.raw(format!("\
theorem {prefix}_write_fail_reads(): {pj}.sd.sign_extend(32).toNat() = print_fail_skip() {{ refl }}
theorem {prefix}_write_exit_reads(): {pj}.zd.sign_extend(32).toNat() = print_exit_skip() {{ refl }}
theorem {prefix}_write_back_closes(): print_loop_span() + 5 + {pj}.bd.sign_extend(32).toNat() = Nat::pow(2, 64) {{ refl }}
theorem {prefix}_write_retry_closes(): print_retry_span() + 6 + {pj}.rd.sign_extend(32).toNat() = Nat::pow(2, 64) {{ refl }}
"));
    module.raw(format!("\
// The process claim for the written file: for every way the reads may split
// stdin into non-empty chunks, with EINTRs between them, ending at the empty
// read or at a failed read, and every way the writes may return (short counts
// and EINTRs, then the rest or a failure), a run that reads them all, writes
// `{root}::{spec}` of their concatenation to stdout as a decimal line and
// exits 0, or exits 1 at the failure. The formatter covers counts below 10000.
theorem {prefix}_runs(chunks: List<ReadStep>, ok: EofChunks(chunks), ending: ReadEnding, ending_ok: EofEnding(ending),
    small: {root}::{spec}(eof_input(chunks)) < 10000,
    writes: List<WriteStep>, writes_ok: WriteSteps(writes)(decimal_line({root}::{spec}(eof_input(chunks)))),
    written: WriteEnding, written_ok: WriteEndingOk(written),
    page: Nat → BitVec(8), gprs: Gprs, flags: Flags):
    LinuxRuns(io_linux(), eof_events(chunks, ending, write_events(decimal_line({root}::{spec}(eof_input(chunks))), writes, written)),
        io_initial({prefix}_file(), page, gprs, flags)) {{
    read_print_runs({common},
        {w}_code(), {st}_code(), {ln}_code(), {w}_Protected, {st}_Protected, {ln}_Protected,
        ReadPrintFormat(λ before n placed => {w}_typed_artifact(n, before, placed),
            λ before base n at_base at_n => {st}_typed_artifact(base, n, before, at_base, at_n),
            λ before n placed => {ln}_typed_artifact(n, before, placed),
            trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial),
        {prefix}_jumps(), {prefix}_exit_reads(), {prefix}_fail_reads(), {prefix}_back_closes(), {prefix}_retry_closes(),
        {prefix}_print_jumps(), {prefix}_write_fail_reads(), {prefix}_write_exit_reads(), {prefix}_write_back_closes(),
        {prefix}_write_retry_closes(), {prefix}_resident(),
        chunks, ok, ending, ending_ok, small, writes, writes_ok, written, written_ok, page, gprs, flags)
}}
", spec = program.spec, common = common_arguments(prefix, program)));
    Ok(file)
}
