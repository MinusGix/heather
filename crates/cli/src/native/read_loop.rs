//! The read-once profile (docs/native-first-program-design.md §5): read stdin
//! once into the call profile's RW page, run a certified counting loop over
//! it, exit with the count. The process shape and its proof are the library's
//! (`lib/elf64_read_loop.hthr`); this producer generates the loop through the
//! shared loop generator, lays out the code, and instantiates the library
//! theorem at the written file. Nothing in it is about any one program.
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
/// the byte the loop is given, its specification, and its `ReadLoopComputes`
/// fact. Names are relative to the program's module.
pub(super) struct Program<'a> {
    pub root: &'a str,
    pub source: &'a str,
    pub advance: &'a str,
    pub needle: u8,
    pub spec: &'a str,
    pub computes: &'a str,
    /// With `--print`: the theorem that the count stays below 10000.
    pub bound: Option<&'a str>,
}

// The context the loop generator resolves names in, elaborated before it runs.
pub(super) fn context(program: &Program) -> String {
    let format = if program.bound.is_some() { " import decimal_line;" } else { "" };
    format!("import {}; import function_ir_loop; import function_ir_loop_x86; import bitvec; import bool;{format}", program.root)
}

pub(super) fn generate_loop(elab: &Elaborator, prefix: &str, program: &Program) -> Result<LoopX86Emission, String> {
    generate_elaborated_loop_x86(elab, prefix, &format!("{}::{}", program.root, program.source), &placement(),
        Some(&format!("{}::{}", program.root, program.advance))).map_err(|e| format!("{e:?}"))
}

// The code, in `read_loop_code`'s order: read, setup, loop, exit. Returned
// as its pieces, so the certificate can state the written bytes piece by piece.
struct Pieces { entry: Vec<u8>, setup: Vec<u8>, exit: Vec<u8> }
fn pieces(needle: u8) -> Pieces {
    let mov = |destination, immediate| Instruction::MovRI { destination, immediate };
    Pieces {
        entry: super::encode(&[mov(Gpr::Rax, 0), mov(Gpr::Rdi, 0), mov(Gpr::Rsi, 0x401000), mov(Gpr::Rdx, 4096)]),
        setup: super::encode(&[
            Instruction::MovRR { destination: Gpr::Rbp, source: Gpr::Rax },
            Instruction::MovRR { destination: Gpr::R12, source: Gpr::Rax },
            mov(Gpr::Rdi, 0x401000), mov(Gpr::Rcx, u64::from(needle)), mov(Gpr::Rsi, 0), mov(Gpr::R11, 0),
        ]),
        exit: super::encode(&[Instruction::MovRR { destination: Gpr::Rdi, source: Gpr::R11 }, mov(Gpr::Rax, 60)]),
    }
}

fn literal(bytes: &[u8]) -> String {
    format!("[{}]", bytes.iter().map(|b| format!("@bitvec::BitVec::ofNat(8, {b})")).collect::<Vec<_>>().join(", "))
}

/// Lay out the program and write its certificate after the loop's (which the
/// caller has already put in `module`). Returns the file to publish.
pub(super) fn certify(module: &mut Module, prefix: &str, program: &Program, emission: &LoopX86Emission) -> Result<Vec<u8>, String> {
    let parts = pieces(program.needle);
    let code = [parts.entry.as_slice(), &[0x0f, 0x05], &parts.setup, &emission.bytes, &parts.exit, &[0x0f, 0x05]].concat();
    let file = super::calls::image(&code)?;
    let size = file.len();
    let needle = format!("@bitvec::BitVec::ofNat(8, {})", program.needle);
    let root = program.root;
    let loop_code = format!("read_loop_code({needle}, {prefix}_bytes())");
    let (entry, setup, exit, loop_bytes) = (format!("{prefix}_entry_written()"), format!("{prefix}_setup_written()"),
        format!("{prefix}_exit_written()"), format!("{prefix}_loop_bytes_written()"));
    for (name, bytes) in [("entry", &parts.entry), ("setup", &parts.setup), ("exit", &parts.exit), ("loop_bytes", &emission.bytes)] {
        module.raw(format!("fn {prefix}_{name}_written() → List<BitVec(8)> {{ {} }}", literal(bytes)));
    }
    let written = format!("{entry} ++ (linux_syscall_bytes() ++ ({setup} ++ ({loop_bytes} ++ ({exit} ++ linux_syscall_bytes()))))");
    super::byte_chain(module, &format!("{prefix}_header"), &file[..232]);
    module.raw(format!("\
theorem {prefix}_header_length(): {prefix}_header().len() = 232 {{ refl }}
// The file is the call profile's header, then the read-once program.
fn {prefix}_file() → List<BitVec(8)> {{ {prefix}_header() ++ {loop_code} }}
fn {prefix}_image() → CallElfImage({loop_code}) {{
    CallElfImage(trivial, elf_byte({low}), elf_byte({high}), refl, trivial)
}}
theorem {prefix}_file_correct(): {prefix}_file() = call_elf_bytes({loop_code}, {prefix}_image()) {{ refl }}

// The bytes written after the header, piece by piece as the producer wrote
// them: each fixed block's encoding, and the loop's published bytes.
theorem {prefix}_loop_written(): {prefix}_bytes() = {loop_bytes} {{ refl }}
theorem {prefix}_written(): {prefix}_file() = {prefix}_header() ++ ({written}) {{
    cong_fn<List<BitVec(8)>, List<BitVec(8)>>(λ code => {prefix}_header() ++ code,
        trans(read_loop_code_spelled({needle}, {prefix}_bytes(), {entry}, {setup}, {exit}, refl, refl, refl),
            cong_fn<List<BitVec(8)>, List<BitVec(8)>>(λ looped => {entry} ++ (linux_syscall_bytes() ++ ({setup} ++ (looped ++ ({exit} ++ linux_syscall_bytes())))),
                {prefix}_loop_written())))
}}

// The process claim for the written file: for every input one successful read
// of stdin may return (at most read_capacity() bytes), a run that reads it and exits with `{root}::{spec}` of it.
theorem {prefix}_runs(bytes: List<BitVec(8)>, fits: bytes.len() <= read_capacity(), page: Nat → BitVec(8), gprs: Gprs, flags: Flags):
    LinuxRuns(io_linux(), [ReadEvent(@bitvec::BitVec::ofNat(64, 0), bytes),
        ExitEvent(bitvec_nat::word_of_nat(64, {root}::{spec}(bytes)))], io_initial({prefix}_file(), page, gprs, flags)) {{
    read_loop_runs({prefix}_file(), {prefix}_placement(), ReadLoopPlacement(refl, refl, refl, refl, refl, refl),
        {prefix}_loop_region(), {prefix}_code(), {prefix}_bytes(), {root}::{source}, {needle}, {root}::{spec},
        λ buffer needle budget cursor carry => {prefix}_loop_source_agreement(buffer, needle, budget, cursor, carry),
        λ access before buffer needle budget cursor carry bounded low head readable fits =>
            {prefix}_native(access, before, buffer, needle, budget, cursor, carry, bounded, low, head, readable, fits),
        {root}::{computes},
        read_loop_file_resident({prefix}_header(), {needle}, {prefix}_bytes(), {prefix}_header_length(),
            Nat::leb_sound(232 + {loop_code}.len(), 4096, trivial)),
        bytes, fits, page, gprs, flags)
}}
", low = size & 255, high = size >> 8, source = program.source, spec = program.spec, computes = program.computes));
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

/// The printing profile's certificate: read, count, write the count as a
/// decimal line, exit 0. As `certify`, after the loop's text.
pub(super) fn certify_print(module: &mut Module, prefix: &str, program: &Program, emission: &LoopX86Emission, format: &[FormatPart]) -> Result<Vec<u8>, String> {
    use Gpr::*;
    let parts = pieces(program.needle);
    let mov = |destination, immediate| Instruction::MovRI { destination, immediate };
    let base = super::encode(&[mov(R8, 0x401000)]);
    let store = vec![0x49, 0x89, 0x00];
    let write = super::encode(&[Instruction::MovRR { destination: Rsi, source: R9 }, Instruction::MovRR { destination: Rdx, source: R10 },
        mov(Rdi, 1), mov(Rax, 1)]);
    let exit = super::encode(&[mov(Rdi, 0), mov(Rax, 60)]);
    let [word, start, length] = format else { return Err("the formatter has three parts".into()) };
    let code = [parts.entry.as_slice(), &[0x0f, 0x05], &parts.setup, &emission.bytes, &base, &word.bytes, &start.bytes, &length.bytes,
        &store, &write, &[0x0f, 0x05], &exit, &[0x0f, 0x05]].concat();
    let file = super::calls::image(&code)?;
    let size = file.len();
    let needle = format!("@bitvec::BitVec::ofNat(8, {})", program.needle);
    let root = program.root;
    let (w, st, ln) = (&word.prefix, &start.prefix, &length.prefix);
    let code_term = format!("read_print_code({needle}, {prefix}_bytes(), {w}_code(), {st}_code(), {ln}_code())");
    for (name, bytes) in [("entry", &parts.entry), ("setup", &parts.setup), ("loop_bytes", &emission.bytes), ("base", &base),
        ("store", &store), ("write", &write), ("exit", &exit)] {
        module.raw(format!("fn {prefix}_{name}_written() → List<BitVec(8)> {{ {} }}", literal(bytes)));
    }
    let layout = |looped: &str, w: &str, st: &str, ln: &str| format!(
        "{prefix}_entry_written() ++ (linux_syscall_bytes() ++ ({prefix}_setup_written() ++ ({looped} ++ ({prefix}_base_written() ++ \
        ({w} ++ ({st} ++ ({ln} ++ ({prefix}_store_written() ++ ({prefix}_write_written() ++ (linux_syscall_bytes() ++ \
        ({prefix}_exit_written() ++ linux_syscall_bytes())))))))))))");
    let original = (format!("{prefix}_bytes()"), format!("{w}_bytes()"), format!("{st}_bytes()"), format!("{ln}_bytes()"));
    let written = (format!("{prefix}_loop_bytes_written()"), format!("{w}_lit()"), format!("{st}_lit()"), format!("{ln}_lit()"));
    // The code, spelled as the pieces the producer wrote: fixed blocks by
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
    super::byte_chain(module, &format!("{prefix}_header"), &file[..232]);
    module.raw(format!("\
theorem {prefix}_header_length(): {prefix}_header().len() = 232 {{ refl }}
theorem {prefix}_loop_written(): {prefix}_bytes() = {prefix}_loop_bytes_written() {{ refl }}
// The code as the producer wrote it: each fixed block's encoding, and the
// loop's and the formatter's published bytes.
theorem {prefix}_code_written(): {code_term} = {spelled} {{ {chain} }}
theorem {prefix}_fits(): 232 + {code_term}.len() <= 4096 {{
    j(sym({prefix}_code_written()), λ code _ => 232 + code.len() <= 4096, Nat::leb_sound(232 + ({spelled}).len(), 4096, trivial))
}}
// The file is the call profile's header, then the read-print program.
fn {prefix}_file() → List<BitVec(8)> {{ {prefix}_header() ++ {code_term} }}
fn {prefix}_image() → CallElfImage({code_term}) {{
    // By `leb` both ways, not `refl`: comparing a length in the thousands
    // successor by successor runs past the kernel's depth budget.
    CallElfImage(j(sym({prefix}_code_written()), λ code _ => 0 < code.len(), Nat::leb_sound(1, ({spelled}).len(), trivial)),
        elf_byte({low}), elf_byte({high}),
        j(sym({prefix}_code_written()), λ code _ => 232 + code.len() = elf_size16(elf_byte({low}), elf_byte({high})),
            Nat::le_antisym(232 + ({spelled}).len(), elf_size16(elf_byte({low}), elf_byte({high})),
                Nat::leb_sound(232 + ({spelled}).len(), elf_size16(elf_byte({low}), elf_byte({high})), trivial),
                Nat::leb_sound(elf_size16(elf_byte({low}), elf_byte({high})), 232 + ({spelled}).len(), trivial))), trivial)
}}
theorem {prefix}_file_correct(): {prefix}_file() = call_elf_bytes({code_term}, {prefix}_image()) {{ refl }}
theorem {prefix}_written(): {prefix}_file() = {prefix}_header() ++ ({spelled}) {{
    cong_fn<List<BitVec(8)>, List<BitVec(8)>>(λ code => {prefix}_header() ++ code, {prefix}_code_written())
}}

// The process claim for the written file: for every input one successful read
// of stdin may return (at most read_capacity() bytes), a run that reads it,
// writes `{root}::{spec}` of it to stdout as a decimal line, and exits 0.
theorem {prefix}_runs(bytes: List<BitVec(8)>, fits: bytes.len() <= read_capacity(), page: Nat → BitVec(8), gprs: Gprs, flags: Flags):
    LinuxRuns(io_linux(), [ReadEvent(@bitvec::BitVec::ofNat(64, 0), bytes),
        WriteEvent(@bitvec::BitVec::ofNat(64, 1), decimal_line({root}::{spec}(bytes))),
        ExitEvent(@bitvec::BitVec::ofNat(64, 0))], io_initial({prefix}_file(), page, gprs, flags)) {{
    read_print_runs({prefix}_file(), {prefix}_placement(), ReadLoopPlacement(refl, refl, refl, refl, refl, refl),
        {prefix}_loop_region(), {prefix}_code(), {prefix}_bytes(), {root}::{source}, {needle}, {root}::{spec},
        λ buffer needle budget cursor carry => {prefix}_loop_source_agreement(buffer, needle, budget, cursor, carry),
        λ access before buffer needle budget cursor carry bounded low head readable fits =>
            {prefix}_native(access, before, buffer, needle, budget, cursor, carry, bounded, low, head, readable, fits),
        {root}::{computes}, λ input small => {root}::{bound}(input, small),
        {w}_code(), {st}_code(), {ln}_code(), {w}_Protected, {st}_Protected, {ln}_Protected,
        ReadPrintFormat(λ before n placed => {w}_typed_artifact(n, before, placed),
            λ before base n at_base at_n => {st}_typed_artifact(base, n, before, at_base, at_n),
            λ before n placed => {ln}_typed_artifact(n, before, placed),
            trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial),
        read_print_file_resident({prefix}_header(), {needle}, {prefix}_bytes(), {w}_code(), {st}_code(), {ln}_code(),
            {prefix}_header_length(), {prefix}_fits()),
        bytes, fits, page, gprs, flags)
}}
", low = size & 255, high = size >> 8, source = program.source, spec = program.spec, computes = program.computes,
        bound = program.bound.ok_or("--print needs --bound")?));
    Ok(file)
}

