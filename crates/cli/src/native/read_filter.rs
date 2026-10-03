//! The read profile's one program shape (docs/native-stream-filter-design.md
//! §6): a stream filter. Read stdin a page at a time, run the program's step
//! over each byte with its state in R13, R14, R15 and R8, store what it emits
//! behind the read, write each chunk's output, and at end of file run the
//! program's finish. The process and its proof are the library's
//! (`lib/elf64_read_filter.hthr`, `lib/elf64_filter_finish.hthr`); this
//! producer reads the program off its bundle's type, restates it where the
//! generator and the claim read it (`context`), generates the step piece,
//! lays out the code and instantiates the library theorem at the written
//! file. Nothing in it is about any one program.
use heather_elab::function_ir_source::{generate_elaborated_filter_step_x86, reflect_elaborated_structured, reflect_filter_step, FilterStep,
    FilterStepEmission, StructuredSourceType};
use heather_elab::function_ir_x86_lower::{Gpr, Instruction};
use heather_elab::heather_emit::Module;
use heather_elab::Elaborator;

use super::layout::{Layout, JNZ, JS, JZ, JMP};
use super::read_loop::{claims, component, copy, fail_tail, image_facts, mov, nested, print_jumps, read_head, tuple, write_loop, FormatPart, TEST};

// Bundled after the read profile's, the write loop's and the formatters':
// what a filter computes, its step's contract, its bundle, its process and
// its finishes.
pub(super) const SUPPORT: &[(&str, &str)] = &[
    ("stream_filter", include_str!("../../../../lib/stream_filter.hthr")),
    ("filter_step_piece", include_str!("../../../../lib/filter_step_piece.hthr")),
    ("filter_program", include_str!("../../../../lib/filter_program.hthr")),
    ("elf64_read_filter", include_str!("../../../../lib/elf64_read_filter.hthr")),
    ("elf64_filter_finish", include_str!("../../../../lib/elf64_filter_finish.hthr")),
];
pub(super) const IMPORTS: &[&str] = &["elf64_filter_finish", "elf64_read_filter", "filter_program", "filter_step_piece", "stream_filter",
    "elf64_count_print", "elf64_read_fields", "field_line", "decimal_line", "elf64_write_loop", "elf64_print_pieces", "elf64_read_pieces", "elf64_io",
    "elf64_calls", "elf64", "linux_x86_64_entry", "linux_x86_64_io", "linux_x86_64_determinism", "x86_64_structured_block", "x86_64_layout",
    "function_ir_loop", "function_ir_loop_trace", "x86_64_fetched_code", "x86_64_fetch", "bitvec_nat", "x86_64", "x86_64_block", "bitvec", "bool", "list",
    "logic", "nat", "option"];

/// What a program prints after end of file (filter_program's `Finish`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Finish { Quiet, Line, Fields }

/// A program's state: a record's fields, or a scalar as one field that is
/// the state itself.
pub(super) struct State {
    pub type_name: String,
    pub constructor: Option<String>,
    pub fields: Vec<(String, StructuredSourceType)>,
}
impl State {
    fn field(&self, value: &str, i: usize) -> String {
        if self.constructor.is_some() { format!("{value}.{}", self.fields[i].0) } else { value.to_string() }
    }
    /// `λ (s: T) => s.f` for field `i`.
    fn count(&self, i: usize) -> String { format!("λ (s: {}) => {}", self.type_name, self.field("s", i)) }
}

/// A program as its bundle states it, read off the bundle's written type
/// (`Filter<C>(step, init, counts, finish, spec)`): its step, its state, its
/// finish and its specification, by resolved name.
pub(super) struct Program {
    pub name: String,
    pub step: FilterStep,
    pub state: State,
    pub finish: Finish,
    pub spec: String,
}

/// The finish a bundle's written arguments name, before anything is checked:
/// it chooses the formatter to generate.
pub(super) fn finish_written(args: &[heather_syntax::ast::Expr]) -> Option<Finish> {
    use heather_syntax::ast::ExprKind;
    let head = match &args.get(3)?.kind {
        ExprKind::Var(written) => written,
        ExprKind::App { head, .. } => match &head.kind { ExprKind::Var(written) => written, _ => return None },
        _ => return None,
    };
    match head.rsplit("::").next().unwrap_or(head) { "Quiet" => Some(Finish::Quiet), "Line" => Some(Finish::Line), "Fields" => Some(Finish::Fields), _ => None }
}

/// The bundle's data from its written arguments, each name resolved where
/// the program's module resolves it. `init` and `counts` are not read: the
/// context module restates them as the profile needs them (zeros, the Nat
/// fields in order), so a program whose own are otherwise is refused there.
pub(super) fn read_program(elab: &Elaborator, root: &str, symbol: &str, args: &[heather_syntax::ast::Expr]) -> Result<Program, String> {
    use heather_syntax::ast::ExprKind;
    if args.len() != 5 { return Err(format!("`{symbol}`: a Filter takes its step, init, counts, finish and specification as arguments of its type")); }
    let resolve = |written: &str| elab.with_module_scope(root, |elab| elab.qualified_global(written)).ok().flatten();
    let name = |expr: &heather_syntax::ast::Expr, what: &str| match &expr.kind {
        ExprKind::Var(written) => resolve(written).ok_or_else(|| format!("`{symbol}`'s {what} `{written}` is not a function `{root}` sees")),
        _ => Err(format!("`{symbol}`'s {what} is written as a function's name")),
    };
    // The written head of an application, and its arguments.
    let applied = |expr: &heather_syntax::ast::Expr| match &expr.kind {
        ExprKind::Var(written) => Some((written.rsplit("::").next().unwrap_or(written).to_string(), Vec::new())),
        ExprKind::App { head, args, .. } => match &head.kind {
            ExprKind::Var(written) => Some((written.rsplit("::").next().unwrap_or(written).to_string(), args.clone())),
            _ => None,
        },
        _ => None,
    };
    let step = match applied(&args[0]) {
        Some((head, inner)) if head == "counting" && inner.len() == 1 => FilterStep::Counting(name(&inner[0], "counting step")?),
        Some((head, inner)) if head == "mapping" && inner.len() == 1 => FilterStep::Mapping(name(&inner[0], "byte map")?),
        _ => {
            let step = name(&args[0], "step")?;
            reflect_filter_step(elab, &step).map_err(|e| format!("`{symbol}`'s step: {e}"))?
        }
    };
    let finish = match applied(&args[3]).map(|(head, _)| head) {
        Some(head) if head == "Quiet" => Finish::Quiet,
        Some(head) if head == "Line" => Finish::Line,
        Some(head) if head == "Fields" => Finish::Fields,
        _ => return Err(format!("`{symbol}`'s finish is written as `Quiet`, `Line` or `Fields`")),
    };
    let state = state_of(elab, &step)?;
    let nats = state.fields.iter().take_while(|(_, ty)| *ty == StructuredSourceType::NatWord).count();
    match finish {
        Finish::Line if nats < 1 => return Err(format!("`{symbol}` prints a line of its state's first field, which must be a Nat")),
        Finish::Fields if nats < 3 => return Err(format!("`{symbol}` prints its state's first three fields, which must be Nats")),
        _ => {}
    }
    if state.fields.len() > 4 { return Err(format!("`{symbol}`'s state keeps at most four fields, in R13, R14, R15 and R8")); }
    Ok(Program { name: format!("{root}::{symbol}"), step, state, finish, spec: name(&args[4], "specification")? })
}

// The state a step folds: its first parameter's type (a mapping's is
// Stateless).
fn state_of(elab: &Elaborator, step: &FilterStep) -> Result<State, String> {
    let source = match step {
        FilterStep::Mapping(_) => return Ok(State { type_name: "stream_filter::Stateless".into(),
            constructor: Some("stream_filter::Stateless".into()), fields: Vec::new() }),
        FilterStep::Step(name) | FilterStep::Counting(name) => name,
    };
    let reflected = reflect_elaborated_structured(elab, source).map_err(|e| format!("`{source}`: {e}"))?;
    match reflected.signature.first() {
        Some(Some(record)) => Ok(State { type_name: record.type_name.clone(), constructor: Some(record.constructor.clone()), fields: record.fields.clone() }),
        Some(None) => {
            let ty = reflected.parameters.first().copied().ok_or("a step's state is its first parameter")?;
            let ty = if ty == StructuredSourceType::Natural { StructuredSourceType::NatWord } else { ty };
            let type_name = match ty {
                StructuredSourceType::NatWord => "Nat".to_string(),
                StructuredSourceType::Boolean => "Bool".to_string(),
                StructuredSourceType::Word(width) => format!("BitVec({width})"),
                _ => return Err(format!("`{source}`'s state must be Nat, Bool, BitVec(w) or a record of those")),
            };
            Ok(State { type_name, constructor: None, fields: vec![("value".into(), ty)] })
        }
        None => Err(format!("`{source}` takes its state first")),
    }
}

/// The module the generator and the claim read the program through,
/// checked before either is generated: the program's data as the profile
/// needs it, and its facts restated over them. A program whose data are not
/// these (a state that does not start at zeros, counts that are not its Nat
/// fields in order, a finish that prints other fields) is refused here.
pub(super) fn context(prefix: &str, root: &str, program: &Program) -> String {
    let state = &program.state;
    let ty = &state.type_name;
    let step = match &program.step {
        FilterStep::Step(name) => name.clone(),
        FilterStep::Counting(g) => format!("counting<{ty}>({g})"),
        FilterStep::Mapping(f) => format!("mapping({f})"),
    };
    let zero = |kind: &StructuredSourceType| match kind {
        StructuredSourceType::Boolean => "False".to_string(),
        StructuredSourceType::Word(width) => format!("@bitvec::BitVec::ofNat({width}, 0)"),
        _ => "0".to_string(),
    };
    let init = match &state.constructor {
        Some(ctor) => format!("{ctor}({})", state.fields.iter().map(|(_, kind)| zero(kind)).collect::<Vec<_>>().join(", ")),
        None => zero(&state.fields[0].1),
    };
    let nats: Vec<usize> = (0..state.fields.len()).filter(|&i| state.fields[i].1 == StructuredSourceType::NatWord).collect();
    let counts = if nats.is_empty() { "Nil".to_string() } else { format!("[{}]", nats.iter().map(|&i| state.count(i)).collect::<Vec<_>>().join(", ")) };
    let finish = match program.finish {
        Finish::Quiet => "Quiet".to_string(),
        Finish::Line => "Line".to_string(),
        Finish::Fields => "Fields".to_string(),
    };
    // Each count of the zero state is at most 0: one `0 <= 0` per count, then
    // the list's end.
    let zero_counts = nats.iter().rev().fold("trivial".to_string(), |rest, _| format!("⟨Nat::le_refl(0), {rest}⟩"));
    let (name, spec) = (&program.name, &program.spec);
    format!("\
import {root}; import filter_program; import stream_filter; import filter_step_piece; import elf64_read_filter; import function_ir_loop; import bitvec; import bool;
import list; import logic; import nat; import option; import omega;
// `{name}` as the read profile builds it (docs/native-stream-filter-design.md
// §6): its data, as the profile needs them, and its facts over them.
fn {prefix}_step() → {ty} → BitVec(8) → Filtered<{ty}> {{ {step} }}
fn {prefix}_init() → {ty} {{ {init} }}
fn {prefix}_counts() → List<{ty} → Nat> {{ {counts} }}
fn {prefix}_finish() → Finish {{ {finish} }}
// The program is a filter of these: its state starts at zeros, its counts are
// its Nat fields in order, and its finish prints its first fields.
fn {prefix}_program() → Filter<{ty}>({prefix}_step(), {prefix}_init(), {prefix}_counts(), {prefix}_finish(), {spec}) {{ {name}() }}
theorem {prefix}_advances(): (state: {ty}) → (byte: BitVec(8)) → counts_advance({prefix}_counts(), {prefix}_step()(state, byte).next, state) {{
    λ state byte => {prefix}_program().advances(state, byte)
}}
theorem {prefix}_computes(bytes: List<BitVec(8)>): {spec}(bytes) = filter_output({prefix}_step(), {prefix}_init(), {prefix}_counts(), {prefix}_finish(), bytes) {{
    {prefix}_program().computes(bytes)
}}
theorem {prefix}_zero(): CountsAtMost({prefix}_counts(), {prefix}_init(), 0) {{ {zero} }}
", zero = zero_counts)
}

/// The step piece, generated over the context's step as `{prefix}_piece`:
/// its typed pieces as module `{prefix}_piece_pieces`, the piece itself as
/// `{prefix}_piece_step`.
pub(super) fn generate_step(elab: &Elaborator, scope: &str, prefix: &str) -> Result<FilterStepEmission, String> {
    elab.with_module_scope(scope, |elab| {
        let step = reflect_filter_step(elab, &format!("{scope}::{prefix}_step")).map_err(|e| format!("{e}"))?;
        generate_elaborated_filter_step_x86(elab, &format!("{prefix}_piece"), &step, None).map_err(|e| format!("{e}"))
    })?
}

/// elf64_write_loop's loop once more, for a finish's own last write: the same
/// pieces under other names, so one layout holds both.
fn finish_write_loop() -> Layout {
    use Gpr::*;
    let encode = super::encode;
    Layout::default().label("twrite").fixed("write", encode(&[copy(Rsi, R9), copy(Rdx, R10), mov(Rdi, 1), mov(Rax, 1)])).syscall()
        .fixed("test", TEST.to_vec()).jump("twjs", JS, "twfailed")
        .fixed("advance", encode(&[Instruction::AddRR { destination: R9, source: Rax }, Instruction::SubRR { destination: R10, source: Rax }]))
        .jump("twjz", JZ, "twexit").jump("twjmp", JMP, "twrite")
        .then(fail_tail("twfailed", "twrjz", "twrite"))
        .label("twexit").fixed("exit", encode(&[mov(Rdi, 0), mov(Rax, 60)])).syscall()
}

/// elf64_read_filter's `filter_parts`: init, the read head (its JZ at end of
/// file to `end`), the chunk's setup, the loop over its bytes (MOVZX RAX,
/// byte [RSI]; the step; MOV byte [RDI], DL; the cursors on; JNZ), the close
/// and its JZ back to the read when nothing was emitted, the write loop back
/// to the read, the failure tail; the finish goes at `finish`.
fn process_layout(step: &str, bytes: &[u8], end: &'static str) -> Layout {
    use Gpr::*;
    let encode = super::encode;
    Layout::default().fixed("init", encode(&[mov(R13, 0), mov(R14, 0), mov(R15, 0), mov(R8, 0)]))
        .then(read_head(end, "failed"))
        .fixed("setup", encode(&[mov(Rsi, 0x410000), copy(Rcx, Rax), mov(Rdi, 0x410000), mov(R12, 1)]))
        .label("load").fixed("load", vec![0x48, 0x0f, 0xb6, 0x06])
        .generated("step", format!("{step}_lit()"), bytes.to_vec())
        .fixed("store", vec![0x40, 0x88, 0x17])
        .fixed("cursors", encode(&[Instruction::AddRR { destination: Rdi, source: Rbx }, Instruction::AddRR { destination: Rsi, source: R12 },
            Instruction::SubRR { destination: Rcx, source: R12 }]))
        .jump("jnz", JNZ, "load")
        .fixed("close", encode(&[copy(R10, Rdi), mov(R9, 0x410000), Instruction::SubRR { destination: R10, source: R9 }]))
        .jump("cjz", JZ, "read")
        .then(write_loop("read"))
        .then(fail_tail("failed", "rjz", "read"))
        .label("finish")
}

/// The process's jumps, `{prefix}_jumps()`.
fn filter_jumps(module: &mut Module, prefix: &str, layout: &Layout) {
    let d = |jump| format!("@bitvec::BitVec::ofNat(32, {})", layout.displacement(jump));
    module.raw(format!("fn {prefix}_jumps() → FilterJumps {{ FilterJumps({}, {}, {}, {}, {}) }}", d("jz"), d("js"), d("jnz"), d("cjz"), d("rjz")));
}

/// Lay out the program and write its certificate after the step piece's
/// (whose modules the caller has checked). Returns the file to publish.
pub(super) fn certify(module: &mut Module, prefix: &str, program: &Program, step: &FilterStepEmission, format: Option<&[FormatPart]>)
    -> Result<Vec<u8>, String>
{
    use Gpr::*;
    let encode = super::encode;
    let s = format!("{prefix}_piece");
    let state = &program.state;
    let ty = &state.type_name;
    // init, the read head (its JZ at end of file to the finish), the chunk's
    // setup, the loop over its bytes (MOVZX RAX, byte [RSI]; the step; MOV
    // byte [RDI], DL; the cursors on; JNZ), the close and its JZ back to the
    // read when nothing was emitted, the write loop back to the read, the
    // failure tail, then the finish. A program that prints nothing more
    // finishes at the write loop's own exit(0).
    let end = if program.finish == Finish::Quiet { "wexit" } else { "finish" };
    let mut layout = process_layout(&s, &step.bytes, end);
    // The finish's code, how the certificate spells it, its length's lemma,
    // and its generated parts' terms.
    let (finish_code, finish_len, finish_measure) = match (program.finish, format) {
        (Finish::Quiet, _) => ("Nil".to_string(), "0".to_string(), "refl".to_string()),
        (Finish::Line, Some([word, start, length])) => {
            let (w, st, ln) = (&word.prefix, &start.prefix, &length.prefix);
            layout = layout.fixed("base", encode(&[copy(R11, R13), mov(R8, 0x410000)]))
                .generated("word", format!("{w}_lit()"), word.bytes.clone())
                .generated("start", format!("{st}_lit()"), start.bytes.clone())
                .generated("length", format!("{ln}_lit()"), length.bytes.clone())
                .fixed("line_store", vec![0x49, 0x89, 0x00])
                .then(finish_write_loop());
            let (wl, sl, ll) = (word.bytes.len(), start.bytes.len(), length.bytes.len());
            (format!("count_tail({w}_code(), {st}_code(), {ln}_code(), {prefix}_tail_jumps())"),
             format!("layout_end(0, count_tail_lens({wl}, {sl}, {ll})) + write_loop_len()"),
             format!("count_tail_code_len({w}_code(), {st}_code(), {ln}_code(), {prefix}_tail_jumps(), {wl}, {sl}, {ll}, \
                {w}_byte_length(), {st}_byte_length(), {ln}_byte_length())"))
        }
        (Finish::Fields, Some([low, high])) => {
            let (lo, hi) = (&low.prefix, &high.prefix);
            let mov8 = |destination, immediate| Instruction::MovRI { destination, immediate };
            for (k, (count, offset, separator)) in [(R13, 0u64, 32u64), (R14, 8, 32), (R15, 16, 10)].into_iter().enumerate() {
                layout = layout.fixed(format!("field{k}_count"), encode(&[copy(R11, count)]))
                    .generated("low", format!("{lo}_lit()"), low.bytes.clone())
                    .fixed(format!("field{k}_low"), encode(&[mov8(R9, 0x410000 + offset), mov8(R10, 16777216 * separator)]))
                    .fixed("field_store", vec![0x49, 0x89, 0x01])
                    .generated("high", format!("{hi}_lit()"), high.bytes.clone())
                    .fixed(format!("field{k}_high"), encode(&[mov8(R9, 0x410000 + offset + 4)]))
                    .fixed("field_store", vec![0x49, 0x89, 0x01]);
            }
            layout = layout.fixed("line", encode(&[mov(R9, 0x410000), mov(R10, 24)])).then(finish_write_loop());
            let (ll, hl) = (low.bytes.len(), high.bytes.len());
            (format!("fields_tail({lo}_code(), {hi}_code(), {prefix}_tail_jumps())"),
             format!("fields_tail_len({ll}, {hl})"),
             format!("fields_tail_code_len({lo}_code(), {hi}_code(), {prefix}_tail_jumps(), {ll}, {hl}, {lo}_byte_length(), {hi}_byte_length())"))
        }
        _ => return Err("the finish's formatter has the wrong number of parts".into()),
    };
    let code = layout.code();
    let file = super::calls::io_image(&code)?;

    layout.declare(module, prefix);
    let d = |jump| format!("@bitvec::BitVec::ofNat(32, {})", layout.displacement(jump));
    filter_jumps(module, prefix, &layout);
    print_jumps(module, prefix, &layout);
    if program.finish != Finish::Quiet {
        module.raw(format!("\
fn {prefix}_tail_jumps() → PrintJumps {{ PrintJumps({}, {}, {}, {}) }}
fn {prefix}_tail_facts() → PrintJumpFacts({prefix}_tail_jumps()) {{ PrintJumpFacts(WriteJumpFacts(refl, refl, refl), refl) }}
", d("twjs"), d("twjz"), d("twjmp"), d("twrjz")));
    }

    let (jumps, pj) = (format!("{prefix}_jumps()"), format!("{prefix}_print_jumps()"));
    let code_term = format!("filter_code({s}_code(), {jumps}, {pj}, {finish_code})");
    // The code as written: fixed pieces by evaluation, generated ones (the
    // step, the formatter's words) by their lemmas; its length over open
    // parts, each generated part by its own length lemma.
    let generated: Vec<(&str, String)> = std::iter::once(("step", s.clone())).chain(match (program.finish, format) {
        (Finish::Line, Some([word, start, length])) => vec![("word", word.prefix.clone()), ("start", start.prefix.clone()), ("length", length.prefix.clone())],
        (Finish::Fields, Some([low, high])) => vec![("low", low.prefix.clone()), ("high", high.prefix.clone())],
        _ => Vec::new(),
    }).collect();
    let spelled = |upto: usize, with: &str| {
        let terms: Vec<(&str, String)> = generated.iter().enumerate().map(|(i, (key, p))| {
            (*key, if i < upto { format!("{p}_lit()") } else if i == upto { with.to_string() } else { format!("{p}_bytes()") })
        }).collect();
        let terms: Vec<(&str, &str)> = terms.iter().map(|(k, t)| (*k, t.as_str())).collect();
        nested(&layout.spelled_with(prefix, &terms))
    };
    let mut chain = "refl".to_string();
    // The innermost rewrite is the first part's; each spells the parts
    // before it by their literals and the ones after by their bytes.
    for (i, (_, p)) in generated.iter().enumerate() {
        chain = format!("j({p}_bytes_are(), λ y _ => {code_term} = {}, {chain})", spelled(i, "y"));
    }
    let length = format!("filter_code_len({s}_code(), {jumps}, {pj}, {finish_code}, {}, {finish_len}, {s}_byte_length(), {finish_measure})", step.bytes.len());
    image_facts(module, prefix, &code_term, &spelled(generated.len(), ""), &chain, &file, code.len(), &length);

    // Where the finish starts, for a step `n` bytes long.
    let done = |n: &str| if program.finish == Finish::Quiet { format!("wl_at_exit(fl_at_write({n}))") } else { format!("fl_at_finish({n})") };
    let p = format!("structured_bytes({s}_code()).len()");
    let shape = format!("{prefix}_shape()");
    let final_state = format!("filter_state({prefix}_step(), eof_input(steps), {prefix}_init())");
    let pieces = format!("λ (pg: Nat → BitVec(8)) => filter_pieces(IoMemory({prefix}_file(), pg), {s}_code(), {jumps}, {pj}, {finish_code}, {prefix}_resident()(pg))");
    module.raw(format!("\
// The program as the process takes it (elf64_read_filter's `FilterShape` and
// `FilterFacts`): the context's data, the generated piece and placement.
fn {shape} → FilterShape<{ty}> {{ FilterShape({prefix}_step(), {prefix}_init(), {prefix}_counts(), {s}_rep, {s}_code()) }}
fn {prefix}_facts() → FilterFacts<{ty}>({shape}) {{
    FilterFacts({s}_step_piece<IoMemory>(), {s}_framed(), {s}_initialised(), {prefix}_advances(), {prefix}_zero())
}}
// Where the jumps land, from the written displacements: closed facts once
// the step's length is its lemma's.
fn {prefix}_jump_facts() → FilterJumpFacts({p}, {done_p}, {jumps}, {pj}) {{
    j(sym({s}_byte_length()), λ n _ => FilterJumpFacts(n, {done_n}, {jumps}, {pj}),
        FilterJumpFacts(refl, refl, refl, refl, refl, WriteJumpFacts(refl, refl, refl), refl))
}}
", done_p = done(&p), done_n = done("n")));

    // The state's counts as the finishes read them: each Nat field its word.
    let k = state.fields.len();
    let word = |i: usize| format!("sym(loop_nat_placed(read_gpr({r}, gprs), {v}, {c}))",
        r = [R13, R14, R15, R8][i].heather_name(), v = state.field("s", i), c = component("placed", i, k));
    let common = "steps: List<EofStep<List<WriteStep>>>, ok: FilterSteps({S}, steps), ending: EofEnd<WriteFailure>, \
        ending_ok: FilterEndingOk({S}, steps, ending),\n    room: FilterRoom({C}, eof_input(steps))"
        .replace("{S}", &shape).replace("{C}", &format!("{prefix}_counts()"));
    let spec = &program.spec;
    let (premises, tail_events, tail, finished, sends_premises) = match program.finish {
        Finish::Quiet => (format!("{common}, page: Nat → BitVec(8), gprs: Gprs, flags: Flags"),
            "[ExitEvent(@bitvec::BitVec::ofNat(64, 0))]".to_string(),
            format!("filter_quiet_tail({shape}, {jumps}, {pj}, {prefix}_file(), {pieces}, {final_state})"),
            "refl".to_string(), String::new()),
        _ => {
            let printed = format!("finish_bytes({prefix}_finish(), {prefix}_counts(), {final_state})");
            let tail = match program.finish {
                Finish::Line => {
                    module.raw(format!("\
theorem {prefix}_line_word(): LineWord({s}_rep, {count}) {{ λ gprs s placed => {w} }}
fn {prefix}_print_codes() → PrintCodes {{ PrintCodes({a}_code(), {b}_code(), {c}_code()) }}
fn {prefix}_print_format() → PrintFormat({prefix}_print_codes()) {{ PrintFormat({a}_computes<IoMemory>(), {b}_computes<IoMemory>(), {c}_computes<IoMemory>()) }}
", count = state.count(0), w = word(0), a = generated[1].1, b = generated[2].1, c = generated[3].1));
                    format!("filter_line_tail({shape}, {count}, {prefix}_line_word(), {prefix}_file(), fl_at_finish({p}), {prefix}_print_codes(), \
                        {prefix}_print_format(), {prefix}_tail_jumps(), {prefix}_tail_facts(), λ pg => ({pieces})(pg).finish_at, {final_state}, small, \
                        written, written_ok, writes, writes_ok)", count = state.count(0))
                }
                _ => {
                    module.raw(format!("\
theorem {prefix}_counts_placed(gprs: Gprs, s: {ty}, placed: {s}_rep(gprs, s)):
    (read_gpr(R13, gprs) = bitvec_nat::word_of_nat(64, {f0})) ∧ ((read_gpr(R14, gprs) = bitvec_nat::word_of_nat(64, {f1})) ∧
    (read_gpr(R15, gprs) = bitvec_nat::word_of_nat(64, {f2}))) {{
    {words}
}}
fn {prefix}_three() → ThreeCounts<{ty}>({s}_rep) {{ ThreeCounts({c0}, {c1}, {c2}, {prefix}_counts_placed) }}
fn {prefix}_fields_codes() → FieldsCodes {{ FieldsCodes({lo}_code(), {hi}_code()) }}
fn {prefix}_fields_format() → FieldsFormat({prefix}_fields_codes()) {{ FieldsFormat({lo}_computes<IoMemory>(), {hi}_computes<IoMemory>()) }}
", f0 = state.field("s", 0), f1 = state.field("s", 1), f2 = state.field("s", 2), words = tuple(&[word(0), word(1), word(2)]),
                        c0 = state.count(0), c1 = state.count(1), c2 = state.count(2), lo = generated[1].1, hi = generated[2].1));
                    format!("fields_tail_runs({prefix}_file(), fl_at_finish({p}), {s}_rep, {prefix}_three(), {prefix}_fields_codes(), \
                        {prefix}_fields_format(), {prefix}_tail_jumps(), λ pg => ({pieces})(pg).finish_at, \
                        write_targets(fields_at_write(fl_at_finish({p}), {lo}_code(), {hi}_code()), {prefix}_tail_jumps(), {prefix}_tail_facts()), \
                        {final_state}, small, written, written_ok, writes, writes_ok)", lo = generated[1].1, hi = generated[2].1)
                }
            };
            (format!("{common}, small: FinishFits({prefix}_finish(), {prefix}_counts(), {final_state}),
    writes: List<WriteStep>, writes_ok: WriteSteps(writes)({printed}), written: WriteEnding, written_ok: WriteEndingOk(written),
    page: Nat → BitVec(8), gprs: Gprs, flags: Flags"),
                format!("write_events({printed}, writes, written)"), tail,
                format!("stdout_is_bytes(writes, {printed}, writes_ok)"),
                format!(", writes: List<WriteStep>, writes_ok: WriteSteps(writes)({printed})"))
        }
    };
    let events = format!("filter_events({shape}, steps, ending, {tail_events})");
    let proof = format!("read_filter_runs({prefix}_file(), {shape}, {prefix}_facts(), {jumps}, {pj}, {finish_code}, {done_p}, {prefix}_jump_facts(),
        {prefix}_resident(), steps, ok, ending, ending_ok, room, {tail_events}, {tail}, page, gprs, flags)", done_p = done(&p));
    claims(module, prefix, &format!("\
// The process claim for the written file: for every way the reads may split
// stdin into non-empty chunks, with EINTRs between them, and every way each
// write may return (short counts and EINTRs), ending at the empty read or at
// a failed read or write, a run that reads each chunk, writes what
// `{name}`'s step emits for it, then finishes, or exits 1 at the failure.",
        name = program.name), &premises, &events, &proof);
    // On a run that ends well, stdout received the program's specification.
    let finished_tail = tail_events.replace("written)", "Finished)");
    module.raw(format!("\
// What stdout receives on a run that ends at the empty read: `{spec}` of
// stdin.
theorem {prefix}_sends(steps: List<EofStep<List<WriteStep>>>, ok: FilterSteps({shape}, steps){sends_premises}):
    sent_to(@bitvec::BitVec::ofNat(64, 1), filter_events({shape}, steps, AtEnd, {finished_tail})) = {spec}(eof_input(steps)) {{
    filter_prints({shape}, {prefix}_finish(), {spec}, {prefix}_computes, {finished_tail}, steps, ok, {finished})
}}
"));
    Ok(file)
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::read_loop::{literal, SUPPORT as READ_SUPPORT, WRITE_SUPPORT};

    // The producer's layout against the library's (docs/native-architecture-review.md
    // R4): the filter's jump facts, proved by evaluation at the displacements
    // the table computes, hold for the table as written, and are refused for
    // one whose empty-chunk JZ lands on the write loop or whose setup is a
    // byte longer than the library's.
    #[test]
    fn filter_layout_agrees_with_the_library_and_mutations_are_refused() {
        let mut elab = super::super::native_test_base();
        let mut session = heather_cli::semantic::SemanticSession::new(Some(std::path::PathBuf::from(
            concat!(env!("CARGO_MANIFEST_DIR"), "/../../target/native-test-images"),
        )));
        let filter: Vec<(&str, &str)> = SUPPORT.iter().copied().filter(|(name, _)| matches!(*name, "stream_filter" | "filter_step_piece" | "elf64_read_filter")).collect();
        for &(name, src) in READ_SUPPORT.iter().chain(WRITE_SUPPORT).chain(filter.iter()) {
            super::super::check_module(&mut elab, &mut session, &heather_cli::loader::Module {
                name: name.into(), path: name.into(), src: src.into(),
            }).unwrap();
        }
        let library = elab.semantic_image();
        let step = vec![0u8; 40];
        for (name, layout, holds) in [
            ("as written", process_layout("t", &step, "wexit"), true),
            ("empty chunk into the write loop", process_layout("t", &step, "wexit").retarget("cjz", "write"), false),
            ("setup a byte longer", process_layout("t", &step, "wexit").pad("setup"), false),
        ] {
            let mut module = Module::default();
            module.raw("import elf64_read_filter; import elf64_write_loop; import elf64_print_pieces; import elf64_read_pieces; import bitvec; import list; import logic; import nat;");
            module.raw(format!("fn t_bytes() → List<BitVec(8)> {{ {} }}", literal(&step)));
            filter_jumps(&mut module, "t", &layout);
            print_jumps(&mut module, "t", &layout);
            module.raw("fn t_jump_facts() → FilterJumpFacts(40, wl_at_exit(fl_at_write(40)), t_jumps(), t_print_jumps()) {
    FilterJumpFacts(refl, refl, refl, refl, refl, WriteJumpFacts(refl, refl, refl), refl)
}");
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
}
