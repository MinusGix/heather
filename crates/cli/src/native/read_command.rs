//! The read profile's command (docs/native-wc-command-design.md §8): a
//! filter's step folded over each operand the command line names, printing
//! a row of the columns its options select. The process and its proof are the
//! library's (`lib/elf64_command.hthr`); this producer reads the command off
//! its bundle's type, restates it where the generator and the claim read it
//! (`context`), maps each column onto the state register its count lives in,
//! lays the filter's chunk loop after the library's code and instantiates the
//! library's claim at the written file. Nothing in it is about any one
//! command.
//!
//! The library's own code, everything before the chunk loop, is a program
//! (x86_64_asm) of the command's letters, default and spill table
//! (`cmd_prog`). Its bytes and its items' lengths are read back from the
//! kernel's evaluator (`evaluate`) rather than re-encoded here, and the
//! certificate states them as literals, an item at a time (a long one a
//! chunk at a time), that the kernel re-checks against `command_code`, so a
//! misread byte is refused. Nothing here names an item.
use heather_elab::function_ir_source::{FilterStep, FilterStepEmission, StructuredSourceType};
use heather_elab::heather_emit::Module;
use heather_elab::Elaborator;

use super::evaluate::last_nat_list;
use super::layout::Layout;
use super::read_filter::{core_layout, state_of, State};
use super::read_loop::{claims, component, image_facts, literal, nested, print_jumps};

// Bundled after the filter's library (its step contract, bundle and chunk
// loop): what a command does with its command line, the formatter, the
// operand cursor, the stat pass, the events and what they print, the frame,
// the row, and the process.
pub(super) const SUPPORT: &[(&str, &str)] = &[
    ("x86_64_asm", include_str!("../../../../lib/std/arch/x86_64/x86_64_asm.hthr")),
    ("command_program", include_str!("../../../../lib/command_program.hthr")),
    ("elf64_format_width", include_str!("../../../../lib/elf64_format_width.hthr")),
    ("elf64_arg_scan", include_str!("../../../../lib/elf64_arg_scan.hthr")),
    ("elf64_operand_cursor", include_str!("../../../../lib/elf64_operand_cursor.hthr")),
    ("elf64_stat_width", include_str!("../../../../lib/elf64_stat_width.hthr")),
    ("elf64_command_events", include_str!("../../../../lib/elf64_command_events.hthr")),
    ("elf64_command_output", include_str!("../../../../lib/elf64_command_output.hthr")),
    ("elf64_frame", include_str!("../../../../lib/elf64_frame.hthr")),
    ("elf64_row_fields", include_str!("../../../../lib/elf64_row_fields.hthr")),
    ("elf64_command", include_str!("../../../../lib/elf64_command.hthr")),
];
pub(super) const IMPORTS: &[&str] = &["elf64_command", "x86_64_asm", "elf64_command_output", "elf64_command_events", "elf64_row_fields", "elf64_frame",
    "elf64_stat_width", "elf64_operand_cursor", "elf64_arg_scan", "elf64_format_width", "command_program", "elf64_read_filter", "filter_program",
    "filter_step_piece", "stream_filter", "decimal_line", "elf64_write_loop", "elf64_print_pieces", "elf64_read_pieces", "elf64_io", "elf64_calls",
    "elf64", "linux_x86_64_entry", "linux_x86_64_io", "linux_x86_64_determinism", "x86_64_structured_block", "x86_64_layout", "function_ir_loop",
    "function_ir_loop_trace", "x86_64_fetched_code", "x86_64_fetch", "bitvec_nat", "x86_64", "x86_64_block", "bitvec", "bool", "list", "logic",
    "nat", "option"];

/// An item longer than this is stated a chunk this long at a time: one
/// declaration's fuel evaluates a few hundred bytes.
const CHUNK: usize = 400;
/// The process's slots: at most eight columns (command_program's `column_slots`).
const SLOTS: usize = 8;
/// The state registers, in field order (elf64_command's `StateReg`).
const REGISTERS: [(&str, &str); 4] = [("SR13", "R13"), ("SR14", "R14"), ("SR15", "R15"), ("SR8", "R8")];

/// A command as its bundle states it, read off the bundle's written type
/// (`Command<C>(step, init, counts, columns, default)`).
pub(super) struct Command {
    pub root: String,
    pub name: String,
    pub step: FilterStep,
    pub state: State,
    /// The nullary function that lists the columns, by resolved name.
    pub columns: String,
    pub default: Vec<bool>,
}

/// The bundle's data from its written arguments, each name resolved where
/// the command's module resolves it. As for a filter, `init` and `counts`
/// are restated by the context module (zeros, the Nat fields in order), so a
/// command whose own are otherwise is refused there.
pub(super) fn read_program(elab: &Elaborator, root: &str, symbol: &str, args: &[heather_syntax::ast::Expr]) -> Result<Command, String> {
    use heather_syntax::ast::ExprKind;
    if args.len() != 5 { return Err(format!("`{symbol}`: a Command takes its step, init, counts, columns and default as arguments of its type")); }
    let resolve = |written: &str| elab.with_module_scope(root, |elab| elab.qualified_global(written)).ok().flatten();
    // The written head of an application, and its arguments.
    let applied = |expr: &heather_syntax::ast::Expr| match &expr.kind {
        ExprKind::Var(written) => Some((written.clone(), Vec::new())),
        ExprKind::App { head, args, .. } => match &head.kind {
            ExprKind::Var(written) => Some((written.clone(), args.clone())),
            _ => None,
        },
        _ => None,
    };
    let name = |expr: &heather_syntax::ast::Expr, what: &str| match &expr.kind {
        ExprKind::Var(written) => resolve(written).ok_or_else(|| format!("`{symbol}`'s {what} `{written}` is not a function `{root}` sees")),
        _ => Err(format!("`{symbol}`'s {what} is written as a function's name")),
    };
    let short = |written: &str| written.rsplit("::").next().unwrap_or(written).to_string();
    let step = match applied(&args[0]) {
        Some((head, inner)) if short(&head) == "counting" && inner.len() == 1 => FilterStep::Counting(name(&inner[0], "counting step")?),
        Some((head, inner)) if short(&head) == "mapping" && inner.len() == 1 => FilterStep::Mapping(name(&inner[0], "byte map")?),
        _ => {
            let step = name(&args[0], "step")?;
            heather_elab::function_ir_source::reflect_filter_step(elab, &step).map_err(|e| format!("`{symbol}`'s step: {e}"))?
        }
    };
    let columns = match applied(&args[3]) {
        Some((head, inner)) if inner.is_empty() => resolve(&head)
            .ok_or_else(|| format!("`{symbol}`'s columns `{head}` is not a function `{root}` sees"))?,
        _ => return Err(format!("`{symbol}`'s columns are written as a call of a function of no arguments, `columns()`")),
    };
    let flag = |expr: &heather_syntax::ast::Expr| match &expr.kind {
        ExprKind::Var(written) if short(written) == "True" => Some(true),
        ExprKind::Var(written) if short(written) == "False" => Some(false),
        _ => None,
    };
    let default = match &args[4].kind {
        ExprKind::CollectionLit(items) => items.iter().map(flag).collect::<Option<Vec<bool>>>(),
        _ => None,
    }.ok_or_else(|| format!("`{symbol}`'s default is written as a list of `True` and `False`, one per column"))?;
    let state = state_of(elab, &step)?;
    if state.fields.len() > 4 { return Err(format!("`{symbol}`'s state keeps at most four fields, in R13, R14, R15 and R8")); }
    Ok(Command { root: root.to_string(), name: format!("{root}::{symbol}"), step, state, columns, default })
}

fn zero(kind: &StructuredSourceType) -> String {
    match kind {
        StructuredSourceType::Boolean => "False".to_string(),
        StructuredSourceType::Word(width) => format!("@bitvec::BitVec::ofNat({width}, 0)"),
        _ => "0".to_string(),
    }
}
fn nats(state: &State) -> Vec<usize> {
    (0..state.fields.len()).filter(|&i| state.fields[i].1 == StructuredSourceType::NatWord).collect()
}

/// The module the generator and the claim read the command through, checked
/// before either is generated: its data as the profile needs them, its
/// filter's facts, and its letters and default as the process reads them.
pub(super) fn context(prefix: &str, root: &str, command: &Command) -> String {
    let state = &command.state;
    let ty = &state.type_name;
    let step = match &command.step {
        FilterStep::Step(name) => name.clone(),
        FilterStep::Counting(g) => format!("counting<{ty}>({g})"),
        FilterStep::Mapping(f) => format!("mapping({f})"),
    };
    let init = match &state.constructor {
        Some(ctor) => format!("{ctor}({})", state.fields.iter().map(|(_, kind)| zero(kind)).collect::<Vec<_>>().join(", ")),
        None => zero(&state.fields[0].1),
    };
    let nats = nats(state);
    let counts = if nats.is_empty() { "Nil".to_string() } else { format!("[{}]", nats.iter().map(|&i| state.count(i)).collect::<Vec<_>>().join(", ")) };
    let zero_counts = nats.iter().rev().fold("trivial".to_string(), |rest, _| format!("⟨Nat::le_refl(0), {rest}⟩"));
    let default = format!("[{}]", command.default.iter().map(|&on| if on { "True" } else { "False" }).collect::<Vec<_>>().join(", "));
    let (name, columns) = (&command.name, &command.columns);
    format!("\
import {root}; import command_program; import filter_program; import stream_filter; import filter_step_piece; import elf64_read_filter;
import function_ir_loop; import bitvec; import bool; import list; import logic; import nat; import option; import omega;
// `{name}` as the read profile builds it (docs/native-wc-command-design.md
// §8): its data, as the profile needs them, and its facts over them.
fn {prefix}_step() → {ty} → BitVec(8) → Filtered<{ty}> {{ {step} }}
fn {prefix}_init() → {ty} {{ {init} }}
fn {prefix}_counts() → List<{ty} → Nat> {{ {counts} }}
fn {prefix}_columns() → List<Column<{ty}>> {{ {columns}() }}
fn {prefix}_default_columns() → List<Bool> {{ {default} }}
// The command is one of these: its state starts at zeros and its counts are
// its Nat fields in order.
fn {prefix}_program() → Command<{ty}>({prefix}_step(), {prefix}_init(), {prefix}_counts(), {prefix}_columns(), {prefix}_default_columns()) {{
    {name}()
}}
theorem {prefix}_advances(): (state: {ty}) → (byte: BitVec(8)) → counts_advance({prefix}_counts(), {prefix}_step()(state, byte).next, state) {{
    λ state byte => {prefix}_program().advances(state, byte)
}}
theorem {prefix}_zero(): CountsAtMost({prefix}_counts(), {prefix}_init(), 0) {{ {zero_counts} }}
// What the process reads: each column's option letter, and the columns that
// print when no option selects one, as a selection word.
fn {prefix}_letters() → List<BitVec(8)> {{ {prefix}_columns().map(λ (c: Column<{ty}>) => c.letter) }}
fn {prefix}_default() → BitVec(64) {{ selection_of({prefix}_default_columns()) }}
")
}

/// A closed `List<Nat>`, the value of `value` in a module that imports
/// `imports` (`evaluate`): elaborated in a fork of the checked state, which
/// the caller's elaborator never sees.
fn evaluate(elab: &Elaborator, imports: &str, decls: &str, value: &str) -> Result<Vec<u64>, String> {
    let mut fork = elab.clone();
    let text = format!("{imports}\n{decls}\nfn command_probe() → List<Nat> {{ {value} }}\n");
    fork.elab_module_source("command_probe", &text).map_err(|e| format!("evaluating `{value}`: {}", e.render(&text)))?;
    last_nat_list(&fork).map_err(|e| format!("evaluating `{value}`: {e}"))
}

/// Per column: its option letter, and the state field its count reads.
pub(super) struct Columns { pub letters: Vec<u8>, pub fields: Vec<usize> }

/// The columns, read back from the checked context: each column's letter,
/// and which of the state's Nat fields its count is, by evaluating the count
/// at a state whose Nat field `k` holds `k + 1`. The column table the
/// certificate states over that mapping is checked against the columns
/// themselves (`{prefix}_column{j}_means`), so a count that only agrees with
/// a field at this one state is refused there.
pub(super) fn read_columns(elab: &Elaborator, prefix: &str, context: &str, command: &Command) -> Result<Columns, String> {
    let state = &command.state;
    let ty = &state.type_name;
    let imports = format!("import {}; import {context}; import filter_program; import command_program; import bitvec; import list; import nat;",
        command.root);
    let letters = evaluate(elab, &imports, "", &format!("{prefix}_letters().map(λ (b: BitVec(8)) => b.toNat())"))?;
    let probe = match &state.constructor {
        Some(ctor) => format!("{ctor}({})", state.fields.iter().enumerate().map(|(k, (_, kind))|
            if *kind == StructuredSourceType::NatWord { (k + 1).to_string() } else { zero(kind) }).collect::<Vec<_>>().join(", ")),
        None => "1".to_string(),
    };
    let counts = evaluate(elab, &imports, "", &format!("{prefix}_columns().map(λ (c: Column<{ty}>) => c.count({probe}))"))?;
    let symbol = &command.name;
    if letters.is_empty() { return Err(format!("`{symbol}` has no columns")); }
    if letters.len() > SLOTS { return Err(format!("`{symbol}` has {} columns; a command prints at most {SLOTS}", letters.len())); }
    if command.default.len() != letters.len() {
        return Err(format!("`{symbol}`'s default has {} flags for {} columns", command.default.len(), letters.len()));
    }
    if let Some(j) = letters.iter().position(|&l| l == 0 || l == u64::from(b'-') || l > 255) {
        return Err(format!("`{symbol}`'s column {j} is selected by `{}`, which no option letter can be", letters[j]));
    }
    let nats = nats(state);
    let fields = counts.iter().enumerate().map(|(j, &v)| {
        let k = (v as usize).wrapping_sub(1);
        if nats.contains(&k) { Ok(k) } else { Err(format!("`{symbol}`'s column {j} does not count one of its state's Nat fields")) }
    }).collect::<Result<Vec<_>, _>>()?;
    Ok(Columns { letters: letters.iter().map(|&l| l as u8).collect(), fields })
}

/// `match i { Zero => at(0), Succ(i1) => match i1 { … Succ(_) => fallback } }`
/// over the `n` columns: column `j` at slot `j`, and column 0's past them.
fn by_slot(n: usize, at: &dyn Fn(usize) -> String, motive: &dyn Fn(&str) -> Option<String>) -> String {
    fn go(j: usize, n: usize, at: &dyn Fn(usize) -> String, motive: &dyn Fn(&str) -> Option<String>) -> String {
        let var = if j == 0 { "i".to_string() } else { format!("i{j}") };
        // The scrutinee's slot, as the motive spells it: Succ applied j times.
        let slot = (0..j).fold(var.clone(), |inner, _| format!("Succ({inner})"));
        let header = match motive(&slot) { Some(m) => format!("match {var} as λ {var} => {m}"), None => format!("match {var}") };
        let rest = if j + 1 == n { at(0) } else { go(j + 1, n, at, motive) };
        format!("{header} {{ Zero => {}, Succ(i{}) => {rest} }}", at(j), j + 1)
    }
    go(0, n, at, motive)
}

/// Lay out the command and write its certificate after the step piece's
/// (whose modules the caller has checked). Returns the file to publish.
pub(super) fn certify(elab: &Elaborator, module: &mut Module, prefix: &str, context: &str, command: &Command, columns: &Columns,
    step: &FilterStepEmission) -> Result<Vec<u8>, String>
{
    let s = format!("{prefix}_piece");
    let state = &command.state;
    let ty = &state.type_name;
    let n = columns.letters.len();
    let k = state.fields.len();

    // The column table: slot `j` reads column `j`'s field from its register.
    let register = |j: usize| REGISTERS[columns.fields[j]];
    let spill = by_slot(n, &|j| register(j).0.to_string(), &|_| None);
    let column = by_slot(n, &|j| format!("λ (s: {ty}) => bitvec_nat::word_of_nat(64, {})", state.field("s", columns.fields[j])), &|_| None);
    let decls = format!("\
// Which state register holds each slot's count, and the count as the row
// prints it: slot `j` is column `j`, and a slot past the columns repeats
// column 0 (the selection never reaches it).
fn {prefix}_spill(i: Nat) → StateReg {{ {spill} }}
fn {prefix}_column(i: Nat) → {ty} → BitVec(64) {{ {column} }}
");

    // The library's code, read back, and where its items end: the read head
    // before the chunk loop is the last.
    let imports = format!("import {}; import {context}; import elf64_command; import x86_64_asm; import bitvec_nat; import x86_64; import x86_64_block; import x86_64_structured_block; import elf64_frame; import elf64_stat_width; import elf64_row_fields; import elf64_format_width; import elf64_arg_scan; import linux_x86_64_io; import elf64_read_pieces; import x86_64_layout; import filter_program; \
        import command_program; import bitvec; import list; import nat;", command.root);
    let (letters, default) = (format!("{prefix}_letters()"), format!("{prefix}_default()"));
    let fills = format!("cmd_fills({letters}, {default}, {prefix}_spill)");
    let lens = evaluate(elab, &imports, "", "asm_lens(cmd_prog())")?;
    let library = evaluate(elab, &imports, &decls, &format!("asm_code({fills}, cmd_labels(), cmd_prog()).map(λ (b: BitVec(8)) => b.toNat())"))?;
    if lens.iter().sum::<u64>() != library.len() as u64 || lens.is_empty() {
        return Err(format!("the command's library code is {} bytes, but its items measure {}", library.len(), lens.iter().sum::<u64>()));
    }
    let library: Vec<u8> = library.into_iter().map(|b| u8::try_from(b).map_err(|_| format!("the library's code holds {b}, not a byte")))
        .collect::<Result<_, _>>()?;
    let mut items: Vec<&[u8]> = Vec::new();
    let mut at = 0;
    for &len in &lens {
        items.push(&library[at..at + len as usize]);
        at += len as usize;
    }
    let head = *items.last().expect("the items are not empty");
    // The read head, then the chunk loop after it: its jumps back to the read
    // land on the head.
    let layout = Layout::default().label("read").fixed("head", head.to_vec()).then(core_layout(&s, &step.bytes));
    let code = [&library[..library.len() - head.len()], &layout.code()[..]].concat();
    let file = super::calls::io_image(&code)?;

    module.raw(decls.clone());
    layout.declare(module, prefix);
    print_jumps(module, prefix, &layout);
    let d = |jump| format!("@bitvec::BitVec::ofNat(32, {})", layout.displacement(jump));
    let none = "@bitvec::BitVec::ofNat(32, 0)";
    module.raw(format!("\
// The chunk loop's two jumps; the command's own read head and failure tail
// are the library's, so the filter's other three are not used.
fn {prefix}_jumps() → FilterJumps {{ FilterJumps({none}, {none}, {}, {}, {none}) }}
", d("jnz"), d("cjz")));

    let (jumps, pj) = (format!("{prefix}_jumps()"), format!("{prefix}_print_jumps()"));
    let code_term = format!("command_code({letters}, {default}, {prefix}_spill, {s}_code(), {jumps}, {pj})");
    // The code as written, an item at a time so that no one declaration
    // evaluates more than an item's bytes (a long one's, a chunk's): each
    // item's bytes at its label, found from the program's end, the chunk loop
    // with the step by its lemma, and the code from them by `asm_code_same`.
    let bytes_ty = "List<BitVec(8)>";
    let chain_of = |items: &[String]| items.iter().rev().fold("Nil".to_string(), |rest, item| format!("Cons({item}, {rest})"));
    let pairs = |proofs: &[String]| proofs.iter().rev().fold("trivial".to_string(), |rest, proof| format!("⟨{proof}, {rest}⟩"));
    let mut spelled_items = Vec::new();
    for (k, bytes) in items.iter().enumerate() {
        let item = format!("item_bytes({fills}, cmd_labels(), asm_back(cmd_prog(), {}))", items.len() - 1 - k);
        let name = format!("{prefix}_item{k}");
        if bytes.len() <= CHUNK {
            module.raw(format!("fn {name}_written() → {bytes_ty} {{ {} }}\ntheorem {name}(): {item} = {name}_written() {{ refl }}", literal(bytes)));
            spelled_items.push(format!("{name}_written()"));
            continue;
        }
        // Chunk `j` is what is left after `j` chunks, taken a chunk long.
        let after = |j: usize| format!("{item}{}", format!(".drop({CHUNK})").repeat(j));
        let mut lits = Vec::new();
        let mut proofs = Vec::new();
        for (j, chunk) in bytes.chunks(CHUNK).enumerate() {
            module.raw(format!("fn {name}_{j}_written() → {bytes_ty} {{ {} }}\ntheorem {name}_{j}(): {}.take({CHUNK}) = {name}_{j}_written() {{ refl }}",
                literal(chunk), after(j)));
            lits.push(format!("{name}_{j}_written()"));
            proofs.push(format!("{name}_{j}()"));
        }
        let ended = format!("{}.drop({CHUNK})", after(lits.len() - 1));
        let each = proofs.iter().rev().fold(format!("{name}_end()"), |rest, proof| format!("⟨{proof}, {rest}⟩"));
        module.raw(format!("\
theorem {name}_end(): {ended} = Nil {{ refl }}
theorem {name}(): {item} = layout_code({c}, Nil) {{ chunks_same({CHUNK}, {c}, {item}, {each}) }}", c = chain_of(&lits)));
        spelled_items.push(format!("layout_code({}, Nil)", chain_of(&lits)));
    }
    let core_term = format!("filter_core_code({s}_code(), {jumps}, {pj})");
    let core = |with: &str| nested(&layout.spelled_with(prefix, &[("step", with)])[1..]);
    module.raw(format!("theorem {prefix}_core_written(): {core_term} = {} {{ j({s}_bytes_are(), λ y _ => {core_term} = {}, refl) }}",
        core(&format!("{s}_lit()")), core("y")));
    // The items from the end, as `asm_code_same` takes them.
    let all = chain_of(&spelled_items.iter().rev().cloned().collect::<Vec<_>>());
    let same = pairs(&(0..items.len()).rev().map(|k| format!("{prefix}_item{k}()")).collect::<Vec<_>>());
    let chain = format!("trans(cong_fn<{bytes_ty}, {bytes_ty}>(λ c => c ++ {core_term}, asm_code_same({fills}, cmd_labels(), cmd_prog(), {all}, {same})),
        cong_fn<{bytes_ty}, {bytes_ty}>(λ c => back_code({all}) ++ c, {prefix}_core_written()))");
    let spelled = format!("back_code({all}) ++ ({})", core(&format!("{s}_lit()")));
    let p = step.bytes.len();
    let length = format!("asm_len_is({fills}, cmd_labels(), cmd_prog(), cmd_fits({letters}, {default}, {prefix}_spill), {core_term}, \
        filter_core_len({p}), filter_core_code_len({s}_code(), {jumps}, {pj}, {p}, {s}_byte_length()))");
    image_facts(module, prefix, &code_term, &spelled, &chain, &file, code.len(), &length);

    // Each column's register holds its count wherever the step piece holds
    // the state.
    let word = |j: usize| format!("sym(loop_nat_placed(read_gpr({r}, g), {v}, {c}))", r = register(j).1,
        v = state.field("s", columns.fields[j]), c = component("placed", columns.fields[j], k));
    let spilled = by_slot(n, &word, &|slot| Some(format!("read_gpr(state_gpr({prefix}_spill({slot})), g) = {prefix}_column({slot})(s)")));
    let shape = format!("{prefix}_shape()");
    module.raw(format!("\
// The program as the process takes it (elf64_read_filter's `FilterShape` and
// `FilterFacts`): the context's data, the generated piece and placement.
fn {shape} → FilterShape<{ty}> {{ FilterShape({prefix}_step(), {prefix}_init(), {prefix}_counts(), {s}_rep, {s}_code()) }}
fn {prefix}_facts() → FilterFacts<{ty}>({shape}) {{
    FilterFacts({s}_step_piece<IoMemory>(), {s}_framed(), {s}_initialised(), {prefix}_advances(), {prefix}_zero())
}}
// Where the chunk loop's jumps land, from the written displacements: closed
// facts once the step's length is its lemma's, proved by evaluation
// (`asm_lands_back`): the core's offset is the whole program's length.
fn {prefix}_targets() → CoreTargets(ca(l_core()), ca(l_head()), structured_bytes({s}_code()).len(), {jumps}, {pj}) {{
    j(sym({s}_byte_length()), λ n _ => CoreTargets(ca(l_core()), ca(l_head()), n, {jumps}, {pj}),
        CoreTargets(
            again := jumps_back(io_entry(), fc_at_jnz(ca(l_core()), {p}), 6, {jumps}.ld, fc_at_load(ca(l_core()), {p}),
                asm_lands_back(fc_at_jnz(ca(l_core()), {p}), 6, {jumps}.ld, fc_at_load(ca(l_core()), {p}), refl)),
            quiet := jumps_back(io_entry(), fc_at_cjz(ca(l_core()), {p}), 6, {jumps}.cd, ca(l_head()),
                asm_lands_back(fc_at_cjz(ca(l_core()), {p}), 6, {jumps}.cd, ca(l_head()), refl)),
            write := write_targets_to(fc_at_write(ca(l_core()), {p}), ca(l_head()), {pj}, WriteJumpFacts(refl, refl, refl),
                jumps_back(io_entry(), wl_at_wjz(fc_at_write(ca(l_core()), {p})), 6, {pj}.zd, ca(l_head()),
                    asm_lands_back(wl_at_wjz(fc_at_write(ca(l_core()), {p})), 6, {pj}.zd, ca(l_head()), refl)))))
}}
theorem {prefix}_spilled(i: Nat, below: i < 8, g: Gprs, s: {ty}, placed: {s}_rep(g, s)):
    read_gpr(state_gpr({prefix}_spill(i)), g) = {prefix}_column(i)(s) {{
    {spilled}
}}
"));
    // What each column prints of an input is what it means.
    for j in 0..n {
        let path = format!("{prefix}_program().computes(input){}.left", ".right".repeat(j));
        module.raw(format!("\
theorem {prefix}_column{j}_means(input: List<BitVec(8)>):
    input_counts({shape}, {prefix}_column, input)({j}) = bitvec_nat::word_of_nat(64, column_means({prefix}_columns(), {j})(input)) {{
    cong_fn<Nat, BitVec(64)>(λ v => bitvec_nat::word_of_nat(64, v), sym({path}))
}}
"));
    }

    let events = format!("command_events({shape}, {prefix}_column, {letters}, {default}, argv, history)");
    let history = format!("argv: List<List<BitVec(8)>>, pointers: List<BitVec(64)>, history: CommandHistory,
    ok: CommandHistoryOk({shape}, {prefix}_column, {letters}, {default}, argv, history)");
    let premises = format!("frame: Nat → BitVec(8), rest: BitVec(64) → Option<BitVec(8)>, {history}, page: Nat → BitVec(8), gprs: Gprs, flags: Flags,
    stays: ArgvStaysAt({prefix}_io_image(frame, rest), read_gpr(Rsp, gprs), argv, pointers), argc: argv.len() < Nat::pow(2, 31)");
    let proof = format!("command_runs({prefix}_io_image(frame, rest), {letters}, {default}, {prefix}_spill, {shape}, {prefix}_facts(), {jumps}, {pj},
        λ fr => {prefix}_resident()(fr, rest), {prefix}_targets(), {prefix}_column, {prefix}_spilled, argv, pointers, history, ok, page, gprs, flags,
        stays, argc)");
    claims(module, prefix, &format!("\
// The process claim for the written file: for every command line on the
// initial stack and every history of what Linux answered (each stat, open,
// read, write and close), a run that parses the command line, stats the
// operands, folds `{name}`'s step over each one's reads and prints its row,
// then the total, and exits with the status those answers give.",
        name = command.name), &premises, &events, &proof);
    let written = format!("{history}, written: CommandWritten({letters}, {default}, argv, history)");
    module.raw(format!("\
// What stdout receives and how the run ends, on a run whose writes finish.
theorem {prefix}_stdout({written}):
    sent_to(@bitvec::BitVec::ofNat(64, 1), {events}) = command_stdout({shape}, {prefix}_column, {letters}, {default}, argv, history) {{
    command_sends({shape}, {prefix}_column, {letters}, {default}, argv, history, ok, written)
}}
theorem {prefix}_status({written}):
    EndsIn({events}, ExitEvent(command_status({letters}, {default}, argv, history))) {{
    command_exits({shape}, {prefix}_column, {letters}, {default}, argv, history, ok, written)
}}
"));
    Ok(file)
}
