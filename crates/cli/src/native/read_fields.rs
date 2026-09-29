//! The three-field profile (docs/native-wc-design.md §4.8, §5, §6): read stdin
//! a page at a time, fold a record step over each chunk with the state kept
//! in registers across the reads, and at the empty read print the record's
//! first three fields as GNU `wc` prints them on a pipe (`%7d %7d %7d\n`).
//! The process shape and its proof are the library's
//! (`lib/elf64_read_state.hthr`, `lib/elf64_read_fields.hthr`); this producer
//! generates the loop through the record loop generator and the field
//! formatter's two words, lays out the code, states the program-facing facts
//! every record needs, and instantiates the library theorem at the written
//! file. Nothing in it is about any one program.
use heather_elab::function_ir_source::{generate_elaborated_record_loop_x86, generate_elaborated_typed_x86, reflect_elaborated_readonly_loop,
    LoopCarry, LoopX86Emission, RecordLoopPlacement, StructuredSourceRecord, StructuredSourceType};
use heather_elab::function_ir_x86_lower::{encode_structured, Gpr, Instruction, Placements};
use heather_elab::heather_emit::Module;
use heather_elab::Elaborator;

use super::read_loop::{image_facts, literal, nested, state_head, write_loop, FormatPart};

// Bundled after the read profile's and the write loop's, only for this one:
// the field formatter and the three-field tail.
pub(super) const SUPPORT: &[(&str, &str)] = &[
    ("field_line", include_str!("../../../../lib/field_line.hthr")),
    ("elf64_read_fields", include_str!("../../../../lib/elf64_read_fields.hthr")),
];
pub(super) const IMPORTS: &[&str] = &["elf64_read_fields", "elf64_write_loop", "elf64_print_pieces", "field_line",
    "x86_64_structured_block"];

/// The formatter certificates' prefix, as `read_loop::FORMAT_PREFIX`.
pub(super) const FORMAT_PREFIX: &str = "fields_format";

/// The state's registers are the process's (elf64_read_state's `state_init_block`
/// zeroes R13, R14, R15 and R8); the head's are the read profile's.
fn placement(fields: usize) -> RecordLoopPlacement {
    RecordLoopPlacement {
        base: Gpr::Rdi, length: Gpr::Rbp, needle: Gpr::Rcx, cursor: Gpr::Rsi, budget: Gpr::R12,
        flag: Gpr::R10, step: Gpr::Rbx, byte: Gpr::R9,
        fields: [Gpr::R13, Gpr::R14, Gpr::R15, Gpr::R8][..fields].to_vec(),
        scratch: vec![Gpr::R11, Gpr::Rax, Gpr::Rdx],
    }
}

/// What a program names: its loop's source function and step-advance theorem,
/// the byte the loop is given, the three specifications printed, its fact that
/// they are the first three fields folded from the zero state, and its step's
/// `LoopFolds` fact. Names are relative to the program's module.
pub(super) struct Program<'a> {
    pub root: &'a str,
    pub source: &'a str,
    pub advance: &'a str,
    pub needle: u8,
    pub specs: [&'a str; 3],
    pub computes: &'a str,
    pub folds: &'a str,
}

// The context the loop generator resolves names in, elaborated before it runs.
pub(super) fn context(program: &Program) -> String {
    format!("import {}; import function_ir_loop; import function_ir_loop_x86; import bitvec; import bool;", program.root)
}

/// The loop's state: a record of three counts, printed, and at most one more
/// field, each in one of the process's state registers.
pub(super) fn record(elab: &Elaborator, scope: &str, program: &Program) -> Result<StructuredSourceRecord, String> {
    let reflected = elab.with_module_scope(scope, |elab| {
        reflect_elaborated_readonly_loop(elab, &format!("{}::{}", program.root, program.source)).map_err(|e| format!("{e:?}"))
    })??;
    let LoopCarry::Record(record) = reflected.carry else {
        return Err("--fields needs a loop whose state is a record".into());
    };
    if !(3..=4).contains(&record.fields.len()) {
        return Err("--fields keeps a record of three or four fields in R13, R14, R15 and R8".into());
    }
    if record.fields[..3].iter().any(|(_, ty)| *ty != StructuredSourceType::NatWord) {
        return Err("--fields prints the record's first three fields, which must be Nat".into());
    }
    Ok(record)
}

pub(super) fn generate_loop(elab: &Elaborator, scope: &str, prefix: &str, program: &Program, record: &StructuredSourceRecord)
    -> Result<LoopX86Emission, String>
{
    elab.with_module_scope(scope, |elab| {
        generate_elaborated_record_loop_x86(elab, prefix, &format!("{}::{}", program.root, program.source), &placement(record.fields.len()),
            &format!("{}::{}", program.root, program.advance)).map_err(|e| format!("{e:?}"))
    })?
}

// The formatter's two words at the tail's registers (elf64_read_fields'
// `FieldsFormat`): the count in R11, the high word's tail in R10, the word to
// RAX; R11 and R13–R15 are never written.
pub(super) fn generate_format(elab: &Elaborator, prefix: &str) -> Result<Vec<FormatPart>, String> {
    use Gpr::*;
    let parts: [(&str, Placements, Vec<Gpr>); 2] = [
        ("field_low", Placements::from([(0, R11)]), vec![Rax, Rcx, Rdx, Rbx, R8, R9, R10, R12, Rsi, Rdi, Rbp]),
        ("field_high", Placements::from([(0, R11), (1, R10)]), vec![Rax, Rcx, Rdx, Rbx, R8, R9, R12, Rsi, Rdi, Rbp]),
    ];
    elab.with_module_scope("field_line", |elab| {
        parts.into_iter().map(|(function, inputs, temporaries)| {
            let part = format!("{prefix}_{function}");
            let outputs = Placements::from([(inputs.len() as u64, Rax)]);
            let emission = generate_elaborated_typed_x86(elab, &part, &format!("field_line::{function}"), &inputs, &temporaries, &outputs)
                .map_err(|e| format!("{function}: {e:?}"))?;
            Ok(FormatPart { module: format!("{part}_format"), prefix: part, bytes: encode_structured(&emission.lowered), text: emission.text })
        }).collect()
    })?
}

/// A right-nested conjunction's component `i` of `count`.
fn component(value: &str, i: usize, count: usize) -> String {
    let mut path = value.to_string();
    for _ in 0..i { path.push_str(".right"); }
    if i + 1 < count { path.push_str(".left"); }
    path
}
fn tuple(items: &[String]) -> String {
    match items {
        [only] => only.clone(),
        [first, rest @ ..] => format!("⟨{first}, {}⟩", tuple(rest)),
        [] => "trivial".into(),
    }
}

/// Lay out the program and write its certificate after the loop's (which the
/// caller has already put in `module`). Returns the file to publish.
pub(super) fn certify(module: &mut Module, prefix: &str, program: &Program, record: &StructuredSourceRecord, emission: &LoopX86Emission,
    format: &[FormatPart]) -> Result<Vec<u8>, String>
{
    use Gpr::*;
    let [low, high] = format else { return Err("the field formatter has two words".into()) };
    let mov = |destination, immediate| Instruction::MovRI { destination, immediate };
    let rr = |destination, source| Instruction::MovRR { destination, source };
    let encode = super::encode;

    let head = state_head(program.needle, emission.bytes.len());
    let writes = write_loop(&head);

    // The tail (elf64_read_fields' `fields_tail`): each count formatted and
    // stored as two words at 8k, then the 24-byte line's registers and the
    // write loop (elf64_write_loop).
    let fields = [(R13, 0u64, 32u64), (R14, 8, 32), (R15, 16, 10)];
    let store = vec![0x49, 0x89, 0x01];
    let counts: Vec<Vec<u8>> = fields.iter().map(|&(count, _, _)| encode(&[rr(R11, count)])).collect();
    let lows: Vec<Vec<u8>> = fields.iter().map(|&(_, offset, separator)| encode(&[mov(R9, 0x410000 + offset), mov(R10, 16777216 * separator)])).collect();
    let highs: Vec<Vec<u8>> = fields.iter().map(|&(_, offset, _)| encode(&[mov(R9, 0x410000 + offset + 4)])).collect();
    let line = encode(&[mov(R9, 0x410000), mov(R10, 24)]);

    let mut code = head.code(&emission.bytes);
    for k in 0..3 {
        code.extend([counts[k].as_slice(), &low.bytes, &lows[k], &store, &high.bytes, &highs[k], &store].concat());
    }
    code.extend([line.clone(), writes.code(&head)].concat());
    let file = super::calls::io_image(&code)?;

    let needle = format!("@bitvec::BitVec::ofNat(8, {})", program.needle);
    let root = program.root;
    let (lo, hi) = (&low.prefix, &high.prefix);
    let written = |name: &str| format!("{prefix}_{name}_written()");
    head.declare(module, prefix);
    writes.declare(module, prefix);
    for (name, bytes) in [("store", &store), ("line", &line)] {
        module.raw(format!("fn {} → List<BitVec(8)> {{ {} }}", written(name), literal(bytes)));
    }
    for k in 0..3 {
        for (name, bytes) in [("count", &counts[k]), ("low", &lows[k]), ("high", &highs[k])] {
            module.raw(format!("fn {prefix}_field{k}_{name}_written() → List<BitVec(8)> {{ {} }}", literal(bytes)));
        }
    }

    let pj = format!("{prefix}_print_jumps()");
    let code_term = format!("read_fields_code({needle}, {prefix}_bytes(), {prefix}_jumps(), {lo}_code(), {hi}_code(), {prefix}_print_jumps())");
    // The code's pieces in order, right-nested as `read_fields_code` unfolds.
    let pieces = |l: &str, h: &str| -> Vec<String> {
        let mut all = head.spelled(prefix);
        for k in 0..3 {
            all.extend([format!("{prefix}_field{k}_count_written()"), l.to_string(), format!("{prefix}_field{k}_low_written()"),
                written("store"), h.to_string(), format!("{prefix}_field{k}_high_written()"), written("store")]);
        }
        all.push(written("line"));
        all.extend(writes.spelled(prefix));
        all
    };
    let layout = |l: &str, h: &str| nested(&pieces(l, h));
    let hi_bytes = format!("{hi}_bytes()");
    let (lo_lit, hi_lit) = (format!("{lo}_lit()"), format!("{hi}_lit()"));
    let chain = format!("j({hi}_bytes_are(), λ y _ => {code_term} = {}, j({lo}_bytes_are(), λ y _ => {code_term} = {}, refl))",
        layout(&lo_lit, "y"), layout("y", &hi_bytes));
    let spelled = layout(&lo_lit, &hi_lit);
    // The code's length, from the library's lemma over its parts: the
    // formatter's words by their `_byte_length` lemmas, the loop's by
    // evaluation. Evaluating the whole code walks the formatter's encoding.
    let total = code.len();
    let length = format!("read_fields_code_len({needle}, {prefix}_bytes(), {prefix}_jumps(), {lo}_code(), {hi}_code(), {pj}, {}, {}, {}, \
        refl, {lo}_byte_length(), {hi}_byte_length())", emission.bytes.len(), low.bytes.len(), high.bytes.len());
    image_facts(module, prefix, &code_term, &spelled, &chain, &file, Some((total, length)));

    head.jump_facts(module, prefix, &needle);

    // The facts every record state gives the process: it reads only its
    // registers, init's zeros place the zero state, and the three counts are
    // the words in R13, R14 and R15.
    let k = record.fields.len();
    let ty = &record.type_name;
    let name = |i: usize| &record.fields[i].0;
    let kept = ["kept.left", "kept.right.left", "kept.right.right.left", "kept.right.right.right"][..k].join(", ");
    let zeros = record.fields.iter().map(|(_, ty)| if *ty == StructuredSourceType::Boolean { "False" } else { "0" }).collect::<Vec<_>>().join(", ");
    let counted = |i: usize, r: &str| format!("sym(loop_nat_placed(read_gpr({r}, gprs), carry.{}, {}))", name(i), component("placed", i, k));
    module.raw(format!("\
theorem {prefix}_framed(): StateFramed({prefix}_rep) {{
    λ before after carry kept placed => {prefix}_rep_moves(before, after, carry, {kept}, placed)
}}
fn {prefix}_init() → {ty} {{ {ctor}({zeros}) }}
theorem {prefix}_initialised(): StateInitialised({prefix}_rep, {prefix}_init()) {{ λ state => {refls} }}
theorem {prefix}_counts(gprs: Gprs, carry: {ty}, placed: {prefix}_rep(gprs, carry)):
    (read_gpr(R13, gprs) = bitvec_nat::word_of_nat(64, carry.{f0})) ∧ ((read_gpr(R14, gprs) = bitvec_nat::word_of_nat(64, carry.{f1})) ∧
    (read_gpr(R15, gprs) = bitvec_nat::word_of_nat(64, carry.{f2}))) {{
    ⟨{c0}, ⟨{c1}, {c2}⟩⟩
}}
", ctor = record.constructor, refls = tuple(&vec!["refl".to_string(); k]), f0 = name(0), f1 = name(1), f2 = name(2),
        c0 = counted(0, "R13"), c1 = counted(1, "R14"), c2 = counted(2, "R15")));

    let [s0, s1, s2] = program.specs.map(|spec| format!("{root}::{spec}"));
    let input = "eof_input(chunks)";
    let printed = format!("three_fields_line({s0}({input}), {s1}({input}), {s2}({input}))");
    let nat_zero = tuple(&vec!["refl".to_string(); 3]);
    let arguments = format!("{prefix}_file(), {prefix}_placement(), ReadStatePlacement(refl, refl, refl, refl, refl),
        {prefix}_rep, {prefix}_fits, {prefix}_framed(), {prefix}_loop_region(), {prefix}_code(), {prefix}_bytes(), {root}::{source}, {needle},
        λ buffer needle budget cursor carry => {prefix}_loop_source_agreement(buffer, needle, budget, cursor, carry),
        λ access before buffer needle budget cursor carry bounded low head readable fits =>
            {prefix}_native(access, before, buffer, needle, budget, cursor, carry, bounded, low, head, readable, fits),
        {root}::{folds}, {prefix}_init(), {prefix}_initialised(),
        λ seen budget fits => {prefix}_room({needle}, {prefix}_init(), {nat_zero}, seen, budget, fits),
        λ (s: {ty}) => s.{f0}, λ (s: {ty}) => s.{f1}, λ (s: {ty}) => s.{f2}, {prefix}_counts,
        {s0}, {s1}, {s2}, {root}::{computes},
        {lo}_code(), {hi}_code(), {lo}_Protected, {hi}_Protected,
        FieldsFormat(λ before n placed => {lo}_typed_artifact(n, before, placed),
            λ before n tail at_n at_tail => {hi}_typed_artifact(n, tail, before, at_n, at_tail),
            trivial, trivial, trivial, trivial, trivial, trivial, trivial),
        {prefix}_jumps(), {prefix}_exit_reads(), {prefix}_fail_reads(), {prefix}_back_closes(), {prefix}_retry_closes(),
        {pj}, {prefix}_write_fail_reads(), {prefix}_write_exit_reads(), {prefix}_write_back_closes(), {prefix}_write_retry_closes(),
        {prefix}_resident(), chunks, ok, ending, ending_ok, room, small, writes, writes_ok, written, written_ok, page, gprs, flags",
        source = program.source, folds = program.folds, computes = program.computes, f0 = name(0), f1 = name(1), f2 = name(2));
    let premises = format!("chunks: List<ReadStep>, ok: EofChunks(chunks), ending: ReadEnding, ending_ok: EofEnding(ending),
    room: {input}.len() + 4096 < Nat::pow(2, 64),
    small: ({s0}({input}) < 10000000) ∧ (({s1}({input}) < 10000000) ∧ ({s2}({input}) < 10000000)),
    writes: List<WriteStep>, writes_ok: WriteSteps(writes)({printed}), written: WriteEnding, written_ok: WriteEndingOk(written),
    page: Nat → BitVec(8), gprs: Gprs, flags: Flags");
    let events = format!("eof_events(chunks, ending, write_events({printed}, writes, written))");
    module.raw(format!("\
// The process claim for the written file: for every way the reads may split
// stdin into non-empty chunks, with EINTRs between them, ending at the empty
// read or at a failed read, and every way the writes may return (short counts
// and EINTRs, then the rest or a failure), a run that reads them all, writes
// `{s0}`, `{s1}` and `{s2}` of their concatenation to stdout as a
// `%7d %7d %7d` line and exits 0, or exits 1 at the failure. The line covers
// counts below 10^7.
theorem {prefix}_runs({premises}):
    LinuxRuns(io_linux(), {events}, io_initial({prefix}_file(), page, gprs, flags)) {{
    read_fields_spec_runs({arguments})
}}

// And that run is the run: every run of the file from that start which got
// the same answers from Linux, whatever Linux left in RCX, R11 and a failed
// read's buffer, made exactly those events (linux_x86_64_determinism). The
// claim is proved again here, not named, so a refused claim is reported once.
theorem {prefix}_runs_every({premises},
    run: List<LinuxEvent>, ran: LinuxRun(io_linux(), run, io_initial({prefix}_file(), page, gprs, flags)),
    answers: SameResponses({events}, run)):
    run = {events} {{
    linux_runs_every(io_linux(), {events}, run, io_initial({prefix}_file(), page, gprs, flags),
        read_fields_spec_runs({arguments}), ran, answers)
}}
"));
    Ok(file)
}
