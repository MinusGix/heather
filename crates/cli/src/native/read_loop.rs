//! The read-until-end-of-file profile (docs/native-read-until-eof-design.md,
//! docs/native-wc-design.md §9): read stdin a page at a time into the call
//! profile's RW page, fold a certified counting loop over each chunk with the
//! count kept in R13 across the reads (elf64_read_state's process), and at the
//! empty read exit with the count or print it. The process shape and its
//! proof are the library's (`lib/elf64_read_state.hthr`,
//! `lib/elf64_count_print.hthr`); this producer generates the loop through the
//! loop generator, lays out the code, and instantiates the library theorem at
//! the written file. The program is a `CountProgram` or a `FieldsProgram`
//! (function_ir_loop), read off its bundle's type (`Program`) and restated
//! where the generator and the claim read it (`context`). The state process's
//! head, the write loop, the facts a state gives the process, the image's
//! facts and the claims are laid out here for the three-field profile too.
//! Nothing in it is about any one program.
use heather_elab::function_ir_source::{generate_elaborated_loop_x86, generate_elaborated_piece_x86, LoopCarry, LoopX86Emission, NativeLoopPlacement,
    ReflectedReadProgram, StructuredSourceType};
use heather_elab::function_ir_x86_lower::{encode_structured, Gpr, Instruction, Placements};
use heather_elab::heather_emit::Module;
use heather_elab::Elaborator;

use super::layout::{Layout, JMP, JS, JZ};

// Bundled after the base support, only for this profile: the loop contract and
// its native certificates, fetched execution, the Linux trace and its
// determinism, the profile's memory view and the state process.
pub(super) const SUPPORT: &[(&str, &str)] = &[
    ("omega", include_str!("../../../../lib/std/omega.hthr")),
    ("bitvec_nat", include_str!("../../../../lib/std/bitvec/bitvec_nat.hthr")),
    ("x86_64_data_read", include_str!("../../../../lib/std/arch/x86_64/x86_64_data_read.hthr")),
    ("x86_64_access_code", include_str!("../../../../lib/std/arch/x86_64/x86_64_access_code.hthr")),
    ("x86_64_access_memory", include_str!("../../../../lib/std/arch/x86_64/x86_64_access_memory.hthr")),
    ("x86_64_fetched_code", include_str!("../../../../lib/std/arch/x86_64/x86_64_fetched_code.hthr")),
    ("x86_64_layout", include_str!("../../../../lib/std/arch/x86_64/x86_64_layout.hthr")),
    ("function_ir_loop", include_str!("../../../../lib/function_ir_loop.hthr")),
    ("read_program", include_str!("../../../../lib/read_program.hthr")),
    ("function_ir_loop_x86", include_str!("../../../../lib/function_ir_loop_x86.hthr")),
    ("function_ir_loop_trace", include_str!("../../../../lib/function_ir_loop_trace.hthr")),
    ("x86_64_store", include_str!("../../../../lib/std/arch/x86_64/x86_64_store.hthr")),
    ("x86_64_step_forms", include_str!("../../../../lib/std/arch/x86_64/x86_64_step_forms.hthr")),
    ("linux_x86_64_io", include_str!("../../../../lib/linux_x86_64_io.hthr")),
    ("linux_x86_64_determinism", include_str!("../../../../lib/linux_x86_64_determinism.hthr")),
    ("elf64_io", include_str!("../../../../lib/elf64_io.hthr")),
    ("elf64_read_pieces", include_str!("../../../../lib/elf64_read_pieces.hthr")),
    ("elf64_read_state", include_str!("../../../../lib/elf64_read_state.hthr")),
];

// The formatter's source and meaning, and the write loop: a printed count
// and printed fields both write a line through it.
pub(super) const WRITE_SUPPORT: &[(&str, &str)] = &[
    ("bitvec_omega", include_str!("../../../../lib/std/bitvec/bitvec_omega.hthr")),
    ("decimal_line", include_str!("../../../../lib/decimal_line.hthr")),
    ("elf64_print_pieces", include_str!("../../../../lib/elf64_print_pieces.hthr")),
    ("elf64_write_loop", include_str!("../../../../lib/elf64_write_loop.hthr")),
];
// For `--print`: the tail that prints the count (docs/native-first-program-design.md §10).
pub(super) const PRINT_SUPPORT: &[(&str, &str)] = &[
    ("elf64_count_print", include_str!("../../../../lib/elf64_count_print.hthr")),
];
pub(super) const PRINT_IMPORTS: &[&str] = &["elf64_count_print", "elf64_write_loop", "elf64_print_pieces", "decimal_line", "x86_64_structured_block"];

// The profile's head registers are fixed (elf64_read_state's
// ReadStatePlacement); the state's fields are the process's state registers
// (`state_init_block` zeroes R13, R14, R15 and R8), a count being one field
// in R13; the rest is the loop's own scratch.
const STATE: [Gpr; 4] = [Gpr::R13, Gpr::R14, Gpr::R15, Gpr::R8];
pub(super) fn placement(fields: usize) -> NativeLoopPlacement {
    NativeLoopPlacement {
        base: Gpr::Rdi, length: Gpr::Rbp, needle: Gpr::Rcx, cursor: Gpr::Rsi, budget: Gpr::R12,
        flag: Gpr::R10, step: Gpr::Rbx, byte: Gpr::R9,
        fields: STATE[..fields].to_vec(),
        scratch: vec![Gpr::R11, Gpr::Rax, Gpr::Rdx],
    }
}

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

/// A loop's state as the process sees it: a record's fields, or a count as
/// one field that is the state itself.
pub(super) struct StateShape<'a> {
    pub type_name: &'a str,
    /// The record's constructor; `None` for a count.
    pub constructor: Option<&'a str>,
    pub fields: &'a [(String, StructuredSourceType)],
}

/// The facts every state gives the process (elf64_read_state), from the loop
/// generator's `_rep_moves`: it reads only its registers (`_framed`), init's
/// zeros place the zero state (`_init`, `_initialised`), and each Nat field
/// is its word in its register (`_word_{i}`).
pub(super) fn state_facts(module: &mut Module, prefix: &str, state: &StateShape) {
    let k = state.fields.len();
    // StateKept is over the four state registers; the fields hold the first k.
    let kept = (0..k).map(|i| component("kept", i, STATE.len())).collect::<Vec<_>>().join(", ");
    let ty = state.type_name;
    let zeros = state.fields.iter().map(|(_, ty)| if *ty == StructuredSourceType::Boolean { "False" } else { "0" }).collect::<Vec<_>>().join(", ");
    let init = match state.constructor { Some(ctor) => format!("{ctor}({zeros})"), None => zeros };
    module.raw(format!("\
theorem {prefix}_framed(): StateFramed({prefix}_rep) {{
    λ before after carry kept placed => {prefix}_rep_moves(before, after, carry, {kept}, placed)
}}
fn {prefix}_init() → {ty} {{ {init} }}
theorem {prefix}_initialised(): StateInitialised({prefix}_rep, {prefix}_init()) {{ λ state => {} }}
", tuple(&vec!["refl".to_string(); k])));
    for (i, (name, kind)) in state.fields.iter().enumerate() {
        if *kind != StructuredSourceType::NatWord { continue; }
        let r = STATE[i].heather_name();
        let value = match state.constructor { Some(_) => format!("carry.{name}"), None => "carry".into() };
        module.raw(format!("\
theorem {prefix}_word_{i}(gprs: Gprs, carry: {ty}, placed: {prefix}_rep(gprs, carry)): read_gpr({r}, gprs) = bitvec_nat::word_of_nat(64, {value}) {{
    sym(loop_nat_placed(read_gpr({r}, gprs), {value}, {}))
}}
", component("placed", i, k)));
    }
}

/// A program as its bundle states it (function_ir_loop's `CountProgram` or
/// `FieldsProgram`), read off the bundle's type: the root module it is in,
/// and its step, byte, specifications and state, by resolved name.
pub(super) struct Program<'a> {
    pub root: &'a str,
    pub bundle: &'a ReflectedReadProgram,
}

/// `(a) ∧ ((b) ∧ …)`.
pub(super) fn conjunction(parts: &[String]) -> String {
    match parts {
        [only] => only.clone(),
        [first, rest @ ..] => format!("({first}) ∧ ({})", conjunction(rest)),
        [] => "True".into(),
    }
}

/// The module the loop generator and the claim read the program through,
/// checked before either is generated: its step as the loop over one chunk,
/// and its facts restated at the shapes they read. A program whose facts are
/// not these (counts that are not its Nat fields in order, a state that does
/// not start at zeros) is refused here, before anything is generated.
pub(super) fn context(prefix: &str, program: &Program) -> String {
    let bundle = program.bundle;
    let (name, step) = (&bundle.name, &bundle.step);
    let needle = format!("@bitvec::BitVec::ofNat(8, {})", bundle.needle);
    let ty = bundle.carry.name();
    let body = format!("fold_body<{ty}>({step})");
    let fold = |init: &str| format!("step_fold(ReadonlyLoop<{ty}>({body}), {needle}, bytes, {init})");
    let (advances, computes, advanced, computed) = match &bundle.carry {
        LoopCarry::Record(record) => {
            let counts: Vec<String> = record.fields.iter().filter(|(_, kind)| *kind == StructuredSourceType::NatWord)
                .map(|(field, _)| format!("loop_step_payload({body}(needle, cursor, byte, s)).{field} <= Succ(s.{field})")).collect();
            let zeros = record.fields.iter().map(|(_, kind)| if *kind == StructuredSourceType::Boolean { "False" } else { "0" }).collect::<Vec<_>>().join(", ");
            let init = format!("{}({zeros})", record.constructor);
            let printed: Vec<String> = bundle.specs.iter().zip(&record.fields).map(|(spec, (field, _))| format!("{spec}(bytes) = {}.{field}", fold(&init))).collect();
            let state: Vec<String> = bundle.specs.iter().zip(&record.fields).map(|(spec, (field, _))| format!("{spec}(bytes) = state.{field}")).collect();
            (format!("(needle: BitVec(8)) → (cursor: Nat) → (byte: BitVec(8)) → (s: {ty}) → {}", conjunction(&counts)), conjunction(&printed),
                format!("λ needle cursor byte s => {name}().advances(s, byte)"),
                format!("j(sym(fold_body_fold<{ty}>({step}, {needle}, bytes, {init})), λ state _ => {}, {name}().computes(bytes))", conjunction(&state)))
        }
        _ => (format!("LoopAdvancesByAtMostOne(ReadonlyLoop<Nat>({body}))"), format!("{}(bytes) = {}", bundle.specs[0], fold("0")),
            format!("λ needle cursor byte count => {name}().advances(count, byte)"),
            format!("trans({name}().computes(bytes), sym(fold_body_fold<Nat>({step}, {needle}, bytes, 0)))")),
    };
    format!("\
import {root}; import function_ir_loop; import read_program; import function_ir_loop_x86; import bitvec; import bool; import list; import logic; import nat;
// `{name}` as the read profile builds it (docs/native-architecture-review.md
// R6): its step as the loop over one chunk, and its facts where the loop
// generator and the process claim read them.
fn {prefix}_program_source(buffer: ReadonlyBytes, needle: BitVec(8), budget: Nat, cursor: Nat, carry: {ty}) → LoopOutcome<{ty}> {{
    bounded_readonly<{ty}>(buffer, needle, budget, cursor, carry, {body})
}}
theorem {prefix}_program_advances(): {advances} {{ {advanced} }}
theorem {prefix}_program_folds(): LoopFolds(ReadonlyLoop<{ty}>({body})) {{ fold_body_folds<{ty}>({step}) }}
theorem {prefix}_program_computes(bytes: List<BitVec(8)>): {computes} {{ {computed} }}
", root = program.root)
}

pub(super) fn generate_loop(elab: &Elaborator, scope: &str, prefix: &str, fields: usize) -> Result<LoopX86Emission, String> {
    elab.with_module_scope(scope, |elab| {
        generate_elaborated_loop_x86(elab, prefix, &format!("{scope}::{prefix}_program_source"), &placement(fields),
            Some(&format!("{scope}::{prefix}_program_advances"))).map_err(|e| format!("{e:?}"))
    })?
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

/// elf64_read_pieces's read head at `read`: read(0, page, 4096), TEST, JZ to
/// `end` at end of file, JS to `failed` at a failed read.
pub(super) fn read_head(end: &'static str, failed: &'static str) -> Layout {
    use Gpr::*;
    Layout::default().label("read").fixed("entry", super::encode(&[mov(Rax, 0), mov(Rdi, 0), mov(Rsi, 0x410000), mov(Rdx, 4096)])).syscall()
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

/// elf64_read_state's `state_parts`: init, the read head, the chunk's setup,
/// loop and jump back, the failure tail; the tail goes at `done`.
pub(super) fn state_layout(prefix: &str, needle: u8, loop_bytes: &[u8]) -> Layout {
    use Gpr::*;
    let encode = super::encode;
    Layout::default().fixed("init", encode(&[mov(R13, 0), mov(R14, 0), mov(R15, 0), mov(R8, 0)]))
        .then(read_head("done", "failed"))
        .fixed("setup", encode(&[copy(Rbp, Rax), copy(R12, Rax), mov(Rdi, 0x410000), mov(Rcx, u64::from(needle)), mov(Rsi, 0)]))
        // The loop's bytes are its published literal tree (a flat literal
        // compared against that tree recurses once per byte, past the
        // kernel's depth budget).
        .generated("loop", format!("{prefix}_bytes()"), loop_bytes.to_vec())
        .jump("jmp", JMP, "read")
        .then(fail_tail("failed", "rjz", "read"))
        .label("done")
}

/// The state process's jumps and the facts that they land where
/// elf64_read_state's layout says, each by evaluation at the written bytes.
pub(super) fn state_jumps(module: &mut Module, prefix: &str, layout: &Layout, needle: &str) {
    let d = |jump| format!("@bitvec::BitVec::ofNat(32, {})", layout.displacement(jump));
    module.raw(format!("\
fn {prefix}_jumps() → EofJumps {{ EofJumps({}, {}, {}, {}) }}
fn {prefix}_jump_facts() → StateJumpFacts({needle}, {prefix}_bytes(), {prefix}_jumps()) {{ StateJumpFacts(refl, refl, refl, refl) }}
", d("jz"), d("js"), d("jmp"), d("rjz")));
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
/// And, for a program's last write, that they land where elf64_write_loop
/// says: closed facts about its offsets from its start.
pub(super) fn print_facts(module: &mut Module, prefix: &str) {
    module.raw(format!("\
fn {prefix}_print_facts() → PrintJumpFacts({prefix}_print_jumps()) {{ PrintJumpFacts(WriteJumpFacts(refl, refl, refl), refl) }}
"));
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
theorem {prefix}_resident(): (page: Nat → BitVec(8)) → CodeResident(io_fetch_access(), IoMemory({prefix}_file(), page), {code_term},
    @bitvec::BitVec::ofNat(64, 0x4000e8)) {{
    eof_file_resident({prefix}_header(), {code_term}, {prefix}_header_length(), {prefix}_code_fits())
}}
", low = size & 255, high = size >> 8));
}

/// The loop's data, what is proved about it, and the state's start
/// (elf64_read_state's `StateShape`, `StateLoop` and `StateStart`), as
/// `{prefix}_state_shape()`, `{prefix}_state_loop(folds)` and
/// `{prefix}_state_start()`; `init` is the initial state and `zeros` proves
/// it is init's zeros in the room fact. What the generator proved is here;
/// the program's own fact, that its step folds, is a parameter the claim
/// supplies.
pub(super) fn state_bundle(module: &mut Module, prefix: &str, ty: &str, needle: &str, init: &str, zeros: &str) {
    module.raw(format!("\
fn {prefix}_state_shape() → StateShape<{ty}> {{
    StateShape({prefix}_placement(), {prefix}_rep, {prefix}_fits, {prefix}_loop_region(), {prefix}_code(), {prefix}_bytes(),
        {prefix}_program_source, {needle})
}}
fn {prefix}_state_loop(folds: LoopFolds({prefix}_loop_region())) → StateLoop<{ty}>({prefix}_state_shape()) {{
    StateLoop(ReadStatePlacement(refl, refl, refl, refl, refl), {prefix}_framed(),
        λ buffer needle budget cursor carry => {prefix}_loop_source_agreement(buffer, needle, budget, cursor, carry),
        λ access before buffer needle budget cursor carry bounded low head readable fits =>
            {prefix}_native(access, before, buffer, needle, budget, cursor, carry, bounded, low, head, readable, fits),
        folds)
}}
fn {prefix}_state_start() → StateStart<{ty}>({prefix}_state_shape(), {init}) {{
    StateStart({prefix}_initialised(), λ seen budget fits => {prefix}_room({needle}, {prefix}_init(), {zeros}, seen, budget, fits))
}}
"));
}

// The count's facts (`state_facts`) and bundles, and the arguments both
// claims pass the library before their format.
fn common_arguments(module: &mut Module, prefix: &str, program: &Program) -> String {
    let needle = format!("@bitvec::BitVec::ofNat(8, {})", program.bundle.needle);
    state_facts(module, prefix, &StateShape { type_name: "Nat", constructor: None, fields: &[("count".into(), StructuredSourceType::NatWord)] });
    state_bundle(module, prefix, "Nat", &needle, "0", "refl");
    format!("{prefix}_file(), {prefix}_state_shape(), {prefix}_state_loop({prefix}_program_folds()), {spec}, {prefix}_program_computes,
        {prefix}_state_start(), {prefix}_word_0", spec = program.bundle.specs[0])
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
    LinuxRuns(io_linux(), {events}, io_initial({prefix}_file(), page, gprs, flags)) {{
    {proof}
}}

// And that run is the run (linux_x86_64_determinism).
theorem {prefix}_runs_every({premises},
    run: List<LinuxEvent>, ran: LinuxRun(io_linux(), run, io_initial({prefix}_file(), page, gprs, flags)),
    answers: SameResponses({events}, run)):
    run = {events} {{
    linux_runs_every(io_linux(), {events}, run, io_initial({prefix}_file(), page, gprs, flags), {proof}, ran, answers)
}}
"));
}

/// Lay out the program and write its certificate after the loop's (which the
/// caller has already put in `module`). Returns the file to publish.
pub(super) fn certify(module: &mut Module, prefix: &str, program: &Program, emission: &LoopX86Emission) -> Result<Vec<u8>, String> {
    let exit = super::encode(&[copy(Gpr::Rdi, Gpr::R13), mov(Gpr::Rax, 60)]);
    let layout = state_layout(prefix, program.bundle.needle, &emission.bytes).fixed("exit", exit.clone()).syscall();
    let code = layout.code();
    let file = super::calls::io_image(&code)?;
    let needle = format!("@bitvec::BitVec::ofNat(8, {})", program.bundle.needle);
    let spec = &program.bundle.specs[0];
    layout.declare(module, prefix);
    state_jumps(module, prefix, &layout, &needle);
    let code_term = format!("read_state_code({needle}, {prefix}_bytes(), {prefix}_jumps())");
    let spelled = nested(&layout.spelled(prefix));
    // The loop's length by evaluating its bytes alone; the exit's too.
    let length = format!("state_code_len({needle}, {prefix}_bytes(), {prefix}_jumps(), eof_exit_code(), {}, {}, refl, refl)",
        emission.bytes.len(), exit.len() + SYSCALL.len());
    image_facts(module, prefix, &code_term, &spelled, "refl", &file, code.len(), &length);
    let premises = "chunks: List<EofStep<True>>, ok: EofChunks(chunks), ending: EofEnd<False>, ending_ok: EofEnding(ending),
    room: eof_input(chunks).len() + 4096 < Nat::pow(2, 64), page: Nat → BitVec(8), gprs: Gprs, flags: Flags";
    let events = format!("eof_events(chunks, ending, [ExitEvent(bitvec_nat::word_of_nat(64, {spec}(eof_input(chunks))))])");
    let proof = format!("read_count_runs({common}, {prefix}_jumps(), {prefix}_jump_facts(), {prefix}_resident(),
        chunks, ok, ending, ending_ok, room, page, gprs, flags)", common = common_arguments(module, prefix, program));
    claims(module, prefix, &format!("\
// The process claim for the written file: for every way the reads may split
// stdin into non-empty chunks, with EINTRs between them, ending at the empty
// read or at a failed read, a run that reads them all and exits with
// `{spec}` of their concatenation, or with 1 after the failure."), premises, &events, &proof);
    Ok(file)
}

pub(super) const IMPORTS: &[&str] = &["elf64_read_state", "elf64_read_pieces", "elf64_io", "elf64_calls", "elf64", "linux_x86_64_entry",
    "linux_x86_64_io", "linux_x86_64_determinism", "function_ir_loop", "read_program",
    "function_ir_loop_trace", "x86_64_fetched_code", "x86_64_fetch", "bitvec_nat", "x86_64", "x86_64_block", "bitvec", "list", "logic", "nat"];

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

/// The printing profile's certificate: read to the end, count, write the count
/// as a decimal line, exit 0. As `certify`, after the loop's text.
pub(super) fn certify_print(module: &mut Module, prefix: &str, program: &Program, emission: &LoopX86Emission, format: &[FormatPart]) -> Result<Vec<u8>, String> {
    use Gpr::*;
    let [word, start, length] = format else { return Err("the formatter has three parts".into()) };
    // The tail (elf64_count_print's `count_tail`): the count to R11 and the
    // page to R8, the formatter, the store, then the write loop.
    let (w, st, ln) = (&word.prefix, &start.prefix, &length.prefix);
    let layout = state_layout(prefix, program.bundle.needle, &emission.bytes)
        .fixed("base", super::encode(&[copy(R11, R13), mov(R8, 0x410000)]))
        .generated("word", format!("{w}_bytes()"), word.bytes.clone())
        .generated("start", format!("{st}_bytes()"), start.bytes.clone())
        .generated("length", format!("{ln}_bytes()"), length.bytes.clone())
        .fixed("store", vec![0x49, 0x89, 0x00])
        .then(write_loop("wexit"));
    let code = layout.code();
    let file = super::calls::io_image(&code)?;
    let needle = format!("@bitvec::BitVec::ofNat(8, {})", program.bundle.needle);
    let spec = &program.bundle.specs[0];
    layout.declare(module, prefix);
    state_jumps(module, prefix, &layout, &needle);
    print_jumps(module, prefix, &layout);
    print_facts(module, prefix);
    let pj = format!("{prefix}_print_jumps()");
    let code_term = format!("read_count_code({needle}, {prefix}_bytes(), {prefix}_jumps(), {w}_code(), {st}_code(), {ln}_code(), {pj})");
    let spelled = |a: &str, b: &str, c: &str| nested(&layout.spelled_with(prefix, &[("word", a), ("start", b), ("length", c)]));
    // The code, spelled as the pieces the producer wrote: fixed pieces by
    // evaluation, the formatter's bytes by their lemmas.
    let (ost, oln) = (format!("{st}_bytes()"), format!("{ln}_bytes()"));
    let (lw, lst, lln) = (format!("{w}_lit()"), format!("{st}_lit()"), format!("{ln}_lit()"));
    let mut chain = "refl".to_string();
    for (lemma, motive) in [(format!("{w}_bytes_are()"), spelled("y", &ost, &oln)), (format!("{st}_bytes_are()"), spelled(&lw, "y", &oln)),
        (format!("{ln}_bytes_are()"), spelled(&lw, &lst, "y"))] {
        chain = format!("j({lemma}, λ y _ => {code_term} = {motive}, {chain})");
    }
    // The loop's length by evaluating its bytes alone, the formatter's by its
    // lemmas.
    let measure = format!("read_count_code_len({needle}, {prefix}_bytes(), {prefix}_jumps(), {w}_code(), {st}_code(), {ln}_code(), {pj}, \
        {}, {}, {}, {}, refl, {w}_byte_length(), {st}_byte_length(), {ln}_byte_length())",
        emission.bytes.len(), word.bytes.len(), start.bytes.len(), length.bytes.len());
    image_facts(module, prefix, &code_term, &spelled(&lw, &lst, &lln), &chain, &file, code.len(), &measure);
    let premises = format!("chunks: List<EofStep<True>>, ok: EofChunks(chunks), ending: EofEnd<False>, ending_ok: EofEnding(ending),
    room: eof_input(chunks).len() + 4096 < Nat::pow(2, 64), small: {spec}(eof_input(chunks)) < 10000,
    writes: List<WriteStep>, writes_ok: WriteSteps(writes)(decimal_line({spec}(eof_input(chunks)))),
    written: WriteEnding, written_ok: WriteEndingOk(written),
    page: Nat → BitVec(8), gprs: Gprs, flags: Flags");
    let events = format!("eof_events(chunks, ending, write_events(decimal_line({spec}(eof_input(chunks))), writes, written))");
    // The formatter's codes and certificates (elf64_print_pieces's
    // `PrintCodes` and `PrintFormat`).
    module.raw(format!("\
fn {prefix}_print_codes() → PrintCodes {{ PrintCodes({w}_code(), {st}_code(), {ln}_code()) }}
fn {prefix}_print_format() → PrintFormat({prefix}_print_codes()) {{ PrintFormat({w}_computes<IoMemory>(), {st}_computes<IoMemory>(), {ln}_computes<IoMemory>()) }}
"));
    let proof = format!("read_count_print_runs({common}, {prefix}_print_codes(), {prefix}_print_format(), {prefix}_jumps(), {prefix}_jump_facts(),
        {pj}, {prefix}_print_facts(), {prefix}_resident(),
        chunks, ok, ending, ending_ok, room, small, writes, writes_ok, written, written_ok, page, gprs, flags)", common = common_arguments(module, prefix, program));
    claims(module, prefix, &format!("\
// The process claim for the written file: for every way the reads may split
// stdin into non-empty chunks, with EINTRs between them, ending at the empty
// read or at a failed read, and every way the writes may return (short counts
// and EINTRs, then the rest or a failure), a run that reads them all, writes
// `{spec}` of their concatenation to stdout as a decimal line and
// exits 0, or exits 1 at the failure. The formatter covers counts below 10000."), &premises, &events, &proof);
    Ok(file)
}

#[cfg(test)]
mod tests {
    use super::*;

    // The producer's layout against the library's (docs/native-architecture-review.md
    // R4): the state process's jump facts, proved by evaluation at the
    // displacements the table computes, hold for the table as written, and are
    // refused for one whose jump back lands on the failure tail or whose setup
    // is a byte longer than the library's.
    #[test]
    fn state_layout_agrees_with_the_library_and_mutations_are_refused() {
        let mut elab = super::super::native_test_base();
        let mut session = heather_cli::semantic::SemanticSession::new(Some(std::path::PathBuf::from(
            concat!(env!("CARGO_MANIFEST_DIR"), "/../../target/native-test-images"),
        )));
        for &(name, src) in SUPPORT {
            super::super::check_module(&mut elab, &mut session, &heather_cli::loader::Module {
                name: name.into(), path: name.into(), src: src.into(),
            }).unwrap();
        }
        let library = elab.semantic_image();
        let loop_bytes = vec![0u8; 40];
        let needle = "@bitvec::BitVec::ofNat(8, 10)";
        for (name, layout, holds) in [
            ("as written", state_layout("t", 10, &loop_bytes), true),
            ("jump back to the failure tail", state_layout("t", 10, &loop_bytes).retarget("jmp", "failed"), false),
            ("setup a byte longer", state_layout("t", 10, &loop_bytes).pad("setup"), false),
        ] {
            let mut module = Module::default();
            module.raw("import elf64_read_state; import elf64_read_pieces; import bitvec; import list; import logic; import nat;");
            module.raw(format!("fn t_bytes() → List<BitVec(8)> {{ {} }}", literal(&loop_bytes)));
            state_jumps(&mut module, "t", &layout, needle);
            let text = module.render();
            let result = library.elaborator().elab_module_source("layout_control", &text);
            if holds {
                result.unwrap_or_else(|e| panic!("{name}: {}", e.render(&text)));
            } else {
                let error = result.expect_err(name).render(&text);
                assert!(error.contains("t_jump_facts") && !error.contains("unbound"), "{name}: {error}");
            }
        }
    }

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
