//! The read profile's one program shape (docs/native-stream-filter-design.md
//! §6): a stream filter. Read stdin a page at a time, run the program's step
//! over each byte with its state in R13, R14, R15 and R8, store what it emits
//! behind the read, write each chunk's output, and at end of file run the
//! program's finish. The process and its proof are the library's
//! (`lib/elf64_read_filter.hthr`, `lib/elf64_filter_finish.hthr`); this
//! producer reads the program off its bundle's type, restates it where the
//! generator and the claim read it (`context`), generates the step piece,
//! reads the code back from the library's layout (`filter_code`, its jumps
//! by `filter_jumps`) and instantiates the library theorem at the written
//! file. Nothing in it is about any one program, or about where any piece
//! of the code is.
use heather_elab::function_ir_source::{generate_elaborated_filter_step_x86, reflect_elaborated_structured, reflect_filter_step, FilterStep,
    FilterStepEmission, StructuredSourceType};
use heather_elab::function_ir_x86_lower::Gpr;
use heather_elab::heather_emit::Module;
use heather_elab::Elaborator;

use super::evaluate::evaluate_bytes;
use super::read_loop::{claims, component, image_facts, literal, spell, FormatPart};

// Bundled after the read profile's, the write loop's and the formatters':
// the labelled program and its stretches (the chunk loop's byte loop is
// one), what a filter computes, its step's contract, its bundle, its
// process and its finishes.
pub(super) const SUPPORT: &[(&str, &str)] = &[
    ("x86_64_asm", include_str!("../../../../lib/std/arch/x86_64/x86_64_asm.hthr")),
    ("elf64_runs", include_str!("../../../../lib/elf64_runs.hthr")),
    ("elf64_stretch", include_str!("../../../../lib/elf64_stretch.hthr")),
    ("stream_filter", include_str!("../../../../lib/stream_filter.hthr")),
    ("filter_step_piece", include_str!("../../../../lib/filter_step_piece.hthr")),
    ("filter_program", include_str!("../../../../lib/filter_program.hthr")),
    ("elf64_read_filter", include_str!("../../../../lib/elf64_read_filter.hthr")),
    ("elf64_filter_finish", include_str!("../../../../lib/elf64_filter_finish.hthr")),
];
// What a command stands on of the filter's library: the labelled program
// and its stretches, the step contract, the bundle and the chunk loop, not
// the finishes.
pub(super) const COMMAND_SUPPORT: &[(&str, &str)] = &[
    ("x86_64_asm", include_str!("../../../../lib/std/arch/x86_64/x86_64_asm.hthr")),
    ("elf64_runs", include_str!("../../../../lib/elf64_runs.hthr")),
    ("elf64_stretch", include_str!("../../../../lib/elf64_stretch.hthr")),
    ("stream_filter", include_str!("../../../../lib/stream_filter.hthr")),
    ("filter_step_piece", include_str!("../../../../lib/filter_step_piece.hthr")),
    ("filter_program", include_str!("../../../../lib/filter_program.hthr")),
    ("elf64_read_filter", include_str!("../../../../lib/elf64_read_filter.hthr")),
];
pub(super) const IMPORTS: &[&str] = &["elf64_filter_finish", "elf64_read_filter", "filter_program", "filter_step_piece", "stream_filter",
    "elf64_count_print", "decimal_line", "elf64_write_loop", "elf64_print_pieces", "elf64_read_pieces", "elf64_io",
    "elf64_calls", "elf64", "linux_x86_64_entry", "linux_x86_64_io", "linux_x86_64_determinism", "x86_64_structured_block", "x86_64_layout",
    "function_ir_loop", "function_ir_loop_trace", "x86_64_fetched_code", "x86_64_fetch", "bitvec_nat", "x86_64", "x86_64_block", "bitvec", "bool", "list",
    "logic", "nat", "option"];

/// What a program prints after end of file (filter_program's `Finish`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Finish { Quiet, Line }

/// A program's state: a record's fields, or a scalar as one field that is
/// the state itself.
pub(super) struct State {
    pub type_name: String,
    pub constructor: Option<String>,
    pub fields: Vec<(String, StructuredSourceType)>,
}
impl State {
    pub(super) fn field(&self, value: &str, i: usize) -> String {
        if self.constructor.is_some() { format!("{value}.{}", self.fields[i].0) } else { value.to_string() }
    }
    /// `λ (s: T) => s.f` for field `i`.
    pub(super) fn count(&self, i: usize) -> String { format!("λ (s: {}) => {}", self.type_name, self.field("s", i)) }
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
    match head.rsplit("::").next().unwrap_or(head) { "Quiet" => Some(Finish::Quiet), "Line" => Some(Finish::Line), _ => None }
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
        _ => return Err(format!("`{symbol}`'s finish is written as `Quiet` or `Line`")),
    };
    let state = state_of(elab, &step)?;
    let nats = state.fields.iter().take_while(|(_, ty)| *ty == StructuredSourceType::NatWord).count();
    match finish {
        Finish::Line if nats < 1 => return Err(format!("`{symbol}` prints a line of its state's first field, which must be a Nat")),
        _ => {}
    }
    if state.fields.len() > 4 { return Err(format!("`{symbol}`'s state keeps at most four fields, in R13, R14, R15 and R8")); }
    Ok(Program { name: format!("{root}::{symbol}"), step, state, finish, spec: name(&args[4], "specification")? })
}

// The state a step folds: its first parameter's type (a mapping's is
// Stateless).
pub(super) fn state_of(elab: &Elaborator, step: &FilterStep) -> Result<State, String> {
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

/// Read the program's code back from the library and write its certificate
/// after the step piece's (whose modules the caller has checked). Returns
/// the file to publish.
pub(super) fn certify(elab: &Elaborator, module: &mut Module, prefix: &str, program: &Program, step: &FilterStepEmission,
    format: Option<&[FormatPart]>) -> Result<Vec<u8>, String>
{
    use Gpr::*;
    let s = format!("{prefix}_piece");
    let state = &program.state;
    let ty = &state.type_name;
    let p = step.bytes.len();
    // The library's layout (elf64_read_filter's `filter_code`): init, the
    // read head (its JZ at end of file to the finish), the chunk loop, the
    // failure tail, then the finish, with the jumps that layout places for a
    // step this long (`filter_jumps`). A program that prints nothing more
    // finishes at the write loop's own exit(0); one that prints a line, at
    // the count tail (elf64_count_print), whose write loop is a last write
    // (`last_jumps`).
    let done = |n: &str| if program.finish == Finish::Quiet { format!("wl_at_exit(fl_at_write({n}))") } else { format!("fl_at_finish({n})") };
    let formatter: Vec<&FormatPart> = match (program.finish, format) {
        (Finish::Quiet, _) => Vec::new(),
        (Finish::Line, Some(parts @ [_, _, _])) => parts.iter().collect(),
        _ => return Err("the finish's formatter has the wrong number of parts".into()),
    };
    let (jumps, pj) = (format!("{prefix}_jumps()"), format!("{prefix}_print_jumps()"));
    // The code over its generated parts' bytes: the step's, then the
    // formatter's three words'.
    let laid = |parts: &[String]| match parts {
        [step] => format!("filter_bytes({step}, {jumps}, {pj}, Nil)"),
        [step, word, start, length] => format!("filter_bytes({step}, {jumps}, {pj}, count_tail_bytes({word}, {start}, {length}, last_jumps()))"),
        _ => unreachable!("a step and its finish's formatter"),
    };
    let generated: Vec<(&str, &[u8])> = std::iter::once((s.as_str(), &step.bytes[..]))
        .chain(formatter.iter().map(|part| (part.prefix.as_str(), &part.bytes[..]))).collect();
    let decls = format!("\
// The program's jumps, where the library's layout places them for this step.
fn {prefix}_jumps() → FilterJumps {{ filter_jumps({p}, {}) }}
fn {prefix}_print_jumps() → PrintJumps {{ filter_print_jumps({p}) }}
", done(&p.to_string()));
    let imports = "import elf64_read_filter; import elf64_count_print; import elf64_write_loop; import elf64_print_pieces; import elf64_read_pieces; \
        import x86_64_layout; import bitvec; import list; import nat;";
    let code = evaluate_bytes(elab, imports, &decls, &laid(&generated.iter().map(|(_, bytes)| literal(bytes)).collect::<Vec<_>>()))?;
    let file = super::calls::io_image(&code)?;
    module.raw(decls);

    let (finish_code, finish_len, finish_measure) = match &formatter[..] {
        [] => ("Nil".to_string(), "0".to_string(), "refl".to_string()),
        [word, start, length] => {
            let (w, st, ln) = (&word.prefix, &start.prefix, &length.prefix);
            let (wl, sl, ll) = (word.bytes.len(), start.bytes.len(), length.bytes.len());
            (format!("count_tail({w}_code(), {st}_code(), {ln}_code(), last_jumps())"),
             format!("layout_end(0, count_tail_lens({wl}, {sl}, {ll})) + write_loop_len()"),
             format!("count_tail_code_len({w}_code(), {st}_code(), {ln}_code(), last_jumps(), {wl}, {sl}, {ll}, \
                {w}_byte_length(), {st}_byte_length(), {ln}_byte_length())"))
        }
        _ => unreachable!("matched above"),
    };
    let code_term = format!("filter_code({s}_code(), {jumps}, {pj}, {finish_code})");
    // The code as written, chunk by chunk, from the layout over the generated
    // parts' literals; that layout from the code by each part's lemma, the
    // first part's innermost, each spelling the parts before it by their
    // literals and the ones after by their bytes.
    let spelled = spell(module, &format!("{prefix}_laid"), &laid(&generated.iter().map(|(p, _)| format!("{p}_lit()")).collect::<Vec<_>>()), &code);
    let with = |upto: usize, y: &str| laid(&generated.iter().enumerate().map(|(i, (p, _))|
        if i < upto { format!("{p}_lit()") } else if i == upto { y.to_string() } else { format!("{p}_bytes()") }).collect::<Vec<_>>());
    let mut chain = "refl".to_string();
    for (i, (p, _)) in generated.iter().enumerate() {
        chain = format!("j({p}_bytes_are(), λ y _ => {code_term} = {}, {chain})", with(i, "y"));
    }
    let chain = format!("trans({chain}, {prefix}_laid())");
    let length = format!("filter_code_len({s}_code(), {jumps}, {pj}, {finish_code}, {p}, {finish_len}, {s}_byte_length(), {finish_measure})");
    image_facts(module, prefix, &code_term, &spelled, &chain, &file, code.len(), &length);

    // The step's length, as the library states it.
    let pp = format!("structured_bytes({s}_code()).len()");
    let shape = format!("{prefix}_shape()");
    let final_state = format!("filter_state({prefix}_step(), eof_input(steps), {prefix}_init())");
    let pieces = format!("λ (pg: Nat → BitVec(8)) => filter_pieces(IoMemory({prefix}_io_image(frame, rest), pg), {s}_code(), {jumps}, {pj}, {finish_code}, {prefix}_resident()(frame, rest, pg))");
    module.raw(format!("\
// The program as the process takes it (elf64_read_filter's `FilterShape` and
// `FilterFacts`): the context's data, the generated piece and placement.
fn {shape} → FilterShape<{ty}> {{ FilterShape({prefix}_step(), {prefix}_init(), {prefix}_counts(), {s}_rep, {s}_code()) }}
fn {prefix}_facts() → FilterFacts<{ty}>({shape}) {{
    FilterFacts({s}_step_piece<IoMemory>(), {s}_framed(), {s}_initialised(), {prefix}_advances(), {prefix}_zero())
}}
// Where the jumps land: closed facts once the step's length is its lemma's,
// proved by evaluation (elf64_read_filter's `filter_jumps_land`).
fn {prefix}_jump_facts() → FilterJumpFacts({pp}, {done_p}, {jumps}, {pj}) {{
    j(sym({s}_byte_length()), λ n _ => FilterJumpFacts(n, {done_n}, {jumps}, {pj}),
        filter_jumps_land({p}, {done_lit}, refl, refl, refl, refl, refl, refl))
}}
", done_p = done(&pp), done_n = done("n"), done_lit = done(&p.to_string())));

    // The state's counts as the finishes read them: each Nat field its word.
    let k = state.fields.len();
    let word = |i: usize| format!("sym(loop_nat_placed(read_gpr({r}, gprs), {v}, {c}))",
        r = [R13, R14, R15, R8][i].heather_name(), v = state.field("s", i), c = component("placed", i, k));
    let common = "steps: List<EofStep<List<WriteStep>>>, ok: FilterSteps({S}, steps), ending: EofEnd<WriteFailure>, \
        ending_ok: FilterEndingOk({S}, steps, ending),\n    room: FilterRoom({C}, eof_input(steps))"
        .replace("{S}", &shape).replace("{C}", &format!("{prefix}_counts()"));
    let spec = &program.spec;
    let (premises, tail_events, tail, finished, sends_premises) = match program.finish {
        Finish::Quiet => (format!("{common}, frame: Nat → BitVec(8), rest: BitVec(64) → Option<BitVec(8)>, page: Nat → BitVec(8), gprs: Gprs, flags: Flags"),
            "[ExitEvent(@bitvec::BitVec::ofNat(64, 0))]".to_string(),
            format!("filter_quiet_tail({shape}, {jumps}, {pj}, {prefix}_io_image(frame, rest), {pieces}, {final_state})"),
            "refl".to_string(), String::new()),
        Finish::Line => {
            let printed = format!("finish_bytes({prefix}_finish(), {prefix}_counts(), {final_state})");
            module.raw(format!("\
theorem {prefix}_line_word(): LineWord({s}_rep, {count}) {{ λ gprs s placed => {w} }}
fn {prefix}_print_codes() → PrintCodes {{ PrintCodes({a}_code(), {b}_code(), {c}_code()) }}
fn {prefix}_print_format() → PrintFormat({prefix}_print_codes()) {{ PrintFormat({a}_computes<IoMemory>(), {b}_computes<IoMemory>(), {c}_computes<IoMemory>()) }}
", count = state.count(0), w = word(0), a = generated[1].0, b = generated[2].0, c = generated[3].0));
            let tail = format!("filter_line_tail({shape}, {count}, {prefix}_line_word(), {prefix}_io_image(frame, rest), fl_at_finish({pp}), \
                {prefix}_print_codes(), {prefix}_print_format(), last_jumps(), last_jumps_land(), λ pg => ({pieces})(pg).finish_at, \
                {final_state}, small, written, written_ok, writes, writes_ok)", count = state.count(0));
            (format!("{common}, small: FinishFits({prefix}_finish(), {prefix}_counts(), {final_state}),
    writes: List<WriteStep>, writes_ok: WriteSteps(writes)({printed}), written: WriteEnding, written_ok: WriteEndingOk(written),
    frame: Nat → BitVec(8), rest: BitVec(64) → Option<BitVec(8)>, page: Nat → BitVec(8), gprs: Gprs, flags: Flags"),
                format!("write_events({printed}, writes, written)"), tail,
                format!("stdout_is_bytes(writes, {printed}, writes_ok)"),
                format!(", writes: List<WriteStep>, writes_ok: WriteSteps(writes)({printed})"))
        }
    };
    let events = format!("filter_events({shape}, steps, ending, {tail_events})");
    let proof = format!("read_filter_runs({prefix}_io_image(frame, rest), {shape}, {prefix}_facts(), {jumps}, {pj}, {finish_code}, {done_p}, {prefix}_jump_facts(),
        {prefix}_resident()(frame, rest), steps, ok, ending, ending_ok, room, {tail_events}, {tail}, page, gprs, flags)", done_p = done(&pp));
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
    use super::super::read_loop::{SUPPORT as READ_SUPPORT, WRITE_SUPPORT};

    // The library's layout places its own jumps (docs/native-architecture-review.md
    // R4): at a step's length, each lands where the library says, proved by
    // evaluation; and the evaluation is not vacuous: an empty-chunk JZ
    // claimed to land on the write loop, or a byte loop laid out for a step
    // a byte longer, is refused.
    #[test]
    fn filter_jumps_land_and_mutations_are_refused() {
        let mut elab = super::super::native_test_base();
        let mut session = heather_cli::semantic::SemanticSession::new(Some(std::path::PathBuf::from(
            concat!(env!("CARGO_MANIFEST_DIR"), "/../../target/native-test-images"),
        )));
        let filter: Vec<(&str, &str)> = SUPPORT.iter().copied().filter(|(name, _)| matches!(*name, "x86_64_asm" | "elf64_runs" | "elf64_stretch" | "stream_filter" | "filter_step_piece" | "elf64_read_filter")).collect();
        for &(name, src) in READ_SUPPORT.iter().chain(WRITE_SUPPORT).chain(filter.iter()) {
            super::super::check_module(&mut elab, &mut session, &heather_cli::loader::Module {
                name: name.into(), path: name.into(), src: src.into(),
            }).unwrap();
        }
        let library = elab.semantic_image();
        let done = |p: usize| format!("wl_at_exit(fl_at_write({p}))");
        for (name, declaration, holds) in [
            ("as laid out", format!("fn t_jump_facts() → FilterJumpFacts(40, {d}, filter_jumps(40, {d}), filter_print_jumps(40)) {{
    filter_jumps_land(40, {d}, refl, refl, refl, refl, refl, refl)
}}", d = done(40)), true),
            ("empty chunk into the write loop", format!("theorem t_jump_facts(): JumpsBack(fl_at_cjz(40), 6, filter_jumps(40, {d}).cd, fl_at_write(40)) {{
    asm_lands_back(fl_at_cjz(40), 6, filter_jumps(40, {d}).cd, fl_at_write(40), refl)
}}", d = done(40)), false),
            ("laid out for a step a byte longer", "theorem t_jump_facts(): JumpsBack(prog_len(lf_advance(40)), 6, near_rel(prog_len(lf_advance(41)) + 6, loop_labels(41, tf_load())), asm_at(lf_load())) {
    asm_lands_back(prog_len(lf_advance(40)), 6, near_rel(prog_len(lf_advance(41)) + 6, loop_labels(41, tf_load())), asm_at(lf_load()), refl)
}".to_string(), false),
        ] {
            let text = format!("import elf64_read_filter; import elf64_write_loop; import elf64_print_pieces; import elf64_read_pieces; import x86_64_layout; import x86_64_asm; \
                import bitvec; import list; import logic; import nat;\n{declaration}\n");
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
