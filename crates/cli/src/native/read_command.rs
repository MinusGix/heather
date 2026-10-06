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
//! The library's own code, everything before the chunk loop, is a function
//! of the command's letters, default and spill table (`command_parts`). Its
//! bytes are read back from the kernel's evaluator (`evaluate`) rather than
//! re-encoded here, and the certificate states them as literals that the
//! kernel re-checks against `command_code`, so a misread byte is refused.
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
pub(super) const IMPORTS: &[&str] = &["elf64_command", "elf64_command_output", "elf64_command_events", "elf64_row_fields", "elf64_frame",
    "elf64_stat_width", "elf64_operand_cursor", "elf64_arg_scan", "elf64_format_width", "command_program", "elf64_read_filter", "filter_program",
    "filter_step_piece", "stream_filter", "decimal_line", "elf64_write_loop", "elf64_print_pieces", "elf64_read_pieces", "elf64_io", "elf64_calls",
    "elf64", "linux_x86_64_entry", "linux_x86_64_io", "linux_x86_64_determinism", "x86_64_structured_block", "x86_64_layout", "function_ir_loop",
    "function_ir_loop_trace", "x86_64_fetched_code", "x86_64_fetch", "bitvec_nat", "x86_64", "x86_64_block", "bitvec", "bool", "list", "logic",
    "nat", "option"];

/// The library's parts (elf64_command's `command_parts`), by which the long
/// ones are found: the letters, default and spill table at `{L}`, `{D}` and
/// `{S}`. A part named for the wrong place only fails to be split.
const PARTS: [&str; 18] = ["scan_code({L}, {D})", "keep_code()", "stat_code()", "init_code()", "start_code()", "begin_code()", "cursor_code()",
    "operand_code()", "spill_code({S})", "setup_code()", "row_code()", "tails_code()", "total_code()", "tsetup_code()", "row_code()",
    "tname_code()", "finish_code()", "read_head_code(FdIn(Rsp), cmd_ed(), cmd_sd())"];
/// A part longer than this is stated piece by piece of its own layout: one
/// declaration's fuel evaluates a few hundred bytes.
const SPLIT_ABOVE: usize = 400;
/// The long parts' layouts (`layout_code(pieces, last)`), by the part.
const SPLIT: [(&str, &str, &str); 4] = [
    ("scan_code({L}, {D})", "scan_parts({L})", "canonical_block_bytes(scan_default_block({D}))"),
    ("stat_code()", "stat_parts()", "canonical_block_bytes(stat_widen_block())"),
    ("row_code()", "row_parts()", "near_control_bytes(JumpIfNear(NE, rj_back()))"),
    ("tails_code()", "tails_parts()", "tails_last()"),
];
/// A piece of a long part still too long, as appends of what it is made of
/// (by the part and the piece): elf64_format_width's `format_code`, the setup,
/// the places' counting blocks, the padding loop, and the places' digits.
fn deep(part: &str, piece: usize) -> Option<Tree> {
    let places = |each: &str, all: &str, last: Tree| (1..=19).fold(last, |rest, i| Tree::App(format!("{all}({i})"),
        Box::new(Tree::Leaf(format!("{each}({i})"))), Box::new(rest)));
    (part == "row_code()" && piece == 10).then(|| Tree::App("format_code()".into(),
        Box::new(Tree::Leaf("canonical_block_bytes(fmt_setup_block())".into())),
        Box::new(Tree::App("count_blocks(19) ++ (pad_code() ++ emit_code(19))".into(),
            Box::new(places("count_block", "count_blocks", Tree::Leaf("count_blocks(0)".into()))),
            Box::new(Tree::App("pad_code() ++ emit_code(19)".into(), Box::new(Tree::Leaf("pad_code()".into())),
                Box::new(places("emit_block", "emit_code", Tree::Leaf("emit_code(0)".into())))))))))
}
/// A term as appends: `App(term, a, b)` is `term`, by unfolding `a ++ b`.
enum Tree { Leaf(String), App(String, Box<Tree>, Box<Tree>) }
impl Tree {
    fn leaves<'t>(&'t self, out: &mut Vec<&'t str>) {
        match self { Tree::Leaf(term) => out.push(term), Tree::App(_, a, b) => { a.leaves(out); b.leaves(out) } }
    }
    fn term(&self) -> &str { match self { Tree::Leaf(term) | Tree::App(term, _, _) => term } }
    // The tree spelled with the leaves' literals, and its proof from the
    // leaves' lemmas (taken in order).
    fn spell(&self, leaves: &mut std::slice::Iter<'_, (String, String)>) -> (String, String) {
        match self {
            Tree::Leaf(_) => leaves.next().expect("a lemma per leaf").clone(),
            Tree::App(_, a, b) => {
                let ((ra, pa), (rb, pb)) = (a.spell(leaves), b.spell(leaves));
                let ty = "List<BitVec(8)>";
                (format!("({ra}) ++ ({rb})"), format!("trans(cong_fn<{ty}, {ty}>(λ x => x ++ ({}), {pa}), cong_fn<{ty}, {ty}>(λ y => ({ra}) ++ y, {pb}))", b.term()))
            }
        }
    }
}
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

    // The library's code, read back, and where its parts end: each part is
    // stated as written, and the read head before the chunk loop is the last.
    let imports = format!("import {}; import {context}; import elf64_command; import bitvec_nat; import x86_64; import x86_64_block; import x86_64_structured_block; import elf64_frame; import elf64_stat_width; import elf64_row_fields; import elf64_format_width; import elf64_arg_scan; import linux_x86_64_io; import elf64_read_pieces; import x86_64_layout; import filter_program; \
        import command_program; import bitvec; import list; import nat;", command.root);
    let lens = evaluate(elab, &imports, "", "command_lens()")?;
    let library = evaluate(elab, &imports, &decls,
        &format!("layout_code(command_parts({prefix}_letters(), {prefix}_default(), {prefix}_spill), Nil).map(λ (b: BitVec(8)) => b.toNat())"))?;
    if lens.iter().sum::<u64>() != library.len() as u64 || lens.is_empty() {
        return Err(format!("the command's library code is {} bytes, but its parts measure {}", library.len(), lens.iter().sum::<u64>()));
    }
    let library: Vec<u8> = library.into_iter().map(|b| u8::try_from(b).map_err(|_| format!("the library's code holds {b}, not a byte")))
        .collect::<Result<_, _>>()?;
    let mut parts: Vec<&[u8]> = Vec::new();
    let mut at = 0;
    for &len in &lens {
        parts.push(&library[at..at + len as usize]);
        at += len as usize;
    }
    let head = parts.pop().expect("the parts are not empty");
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
    let (letters, default) = (format!("{prefix}_letters()"), format!("{prefix}_default()"));
    let code_term = format!("command_code({letters}, {default}, {prefix}_spill, {s}_code(), {jumps}, {pj})");
    // The code as written, a piece at a time so that no one declaration
    // evaluates more than a piece's bytes: each library part's bytes where
    // the library's list selects it (the largest, piece by piece of its own
    // layout), the chunk loop with the step by its lemma, and the code from
    // them by `layout_code_same`.
    let bytes_ty = "List<BitVec(8)>";
    let chain_of = |items: &[String]| items.iter().rev().fold("Nil".to_string(), |rest, item| format!("Cons({item}, {rest})"));
    let pairs = |proofs: &[String]| proofs.iter().rev().fold("trivial".to_string(), |rest, proof| format!("⟨{proof}, {rest}⟩"));
    let parts_term = format!("command_parts({letters}, {default}, {prefix}_spill)");
    let mut all_parts: Vec<&[u8]> = parts.clone();
    all_parts.push(head);
    let mut spelled_parts = Vec::new();
    for (k, bytes) in all_parts.iter().enumerate() {
        let piece = format!("layout_piece({parts_term}, Nil, {k})");
        let Some((_, pieces, last)) = (bytes.len() > SPLIT_ABOVE).then(|| SPLIT.iter().find(|(part, _, _)| *part == PARTS[k])).flatten() else {
            let lit = if k + 1 == all_parts.len() { format!("{prefix}_head_written()") } else {
                module.raw(format!("fn {prefix}_part{k}_written() → {bytes_ty} {{ {} }}", literal(bytes)));
                format!("{prefix}_part{k}_written()")
            };
            module.raw(format!("theorem {prefix}_part{k}(): {piece} = {lit} {{ refl }}"));
            spelled_parts.push(lit);
            continue;
        };
        let (pieces, last) = (pieces.replace("{L}", &letters).replace("{D}", &default), last.replace("{D}", &default));
        let lens = evaluate(elab, &imports, &decls, &format!("{pieces}.map(λ (p: {bytes_ty}) => p.len())"))?;
        let mut at = 0;
        let mut lits = Vec::new();
        let mut proofs = Vec::new();
        for (j, &len) in lens.iter().enumerate() {
            let sub = bytes.get(at..at + len as usize).ok_or("a part's pieces measure past it")?;
            at += len as usize;
            let name = format!("{prefix}_part{k}_{j}");
            let lit = match deep(PARTS[k], j).filter(|_| sub.len() > SPLIT_ABOVE) {
                None => {
                    module.raw(format!("fn {name}_written() → {bytes_ty} {{ {} }}", literal(sub)));
                    module.raw(format!("theorem {name}(): layout_piece({pieces}, {last}, {j}) = {name}_written() {{ refl }}"));
                    format!("{name}_written()")
                }
                Some(tree) => {
                    // Each leaf stated as written, then the piece from them.
                    let mut leaves = Vec::new();
                    tree.leaves(&mut leaves);
                    let lens = evaluate(elab, &imports, &decls, &format!("[{}]", leaves.iter().map(|l| format!("{l}.len()")).collect::<Vec<_>>().join(", ")))?;
                    let mut from = 0;
                    let mut lemmas = Vec::new();
                    for (i, (leaf, &len)) in leaves.iter().zip(&lens).enumerate() {
                        let bytes = sub.get(from..from + len as usize).ok_or("a piece's leaves measure past it")?;
                        from += len as usize;
                        module.raw(format!("fn {name}_{i}_written() → {bytes_ty} {{ {} }}", literal(bytes)));
                        module.raw(format!("theorem {name}_{i}(): {leaf} = {name}_{i}_written() {{ refl }}"));
                        lemmas.push((format!("{name}_{i}_written()"), format!("{name}_{i}()")));
                    }
                    if from != sub.len() { return Err(format!("{}'s piece {j} is {} bytes, but its leaves measure {from}", PARTS[k], sub.len())); }
                    let (spelled, proof) = tree.spell(&mut lemmas.iter());
                    module.raw(format!("theorem {name}(): layout_piece({pieces}, {last}, {j}) = {spelled} {{ {proof} }}"));
                    spelled
                }
            };
            lits.push(lit);
            proofs.push(format!("{name}()"));
        }
        module.raw(format!("\
fn {prefix}_part{k}_last_written() → {bytes_ty} {{ {} }}
theorem {prefix}_part{k}_last(): {last} = {prefix}_part{k}_last_written() {{ refl }}
theorem {prefix}_part{k}(): {piece} = layout_code({c}, {prefix}_part{k}_last_written()) {{
    trans(layout_code_same({last}, {pieces}, {c}, {same}),
        cong_fn<{bytes_ty}, {bytes_ty}>(λ l => layout_code({c}, l), {prefix}_part{k}_last()))
}}", literal(&bytes[at..]), c = chain_of(&lits), same = pairs(&proofs)));
        spelled_parts.push(format!("layout_code({}, {prefix}_part{k}_last_written())", chain_of(&lits)));
    }
    let core_term = format!("filter_core_code({s}_code(), {jumps}, {pj})");
    let core = |with: &str| nested(&layout.spelled_with(prefix, &[("step", with)])[1..]);
    module.raw(format!("theorem {prefix}_core_written(): {core_term} = {} {{ j({s}_bytes_are(), λ y _ => {core_term} = {}, refl) }}",
        core(&format!("{s}_lit()")), core("y")));
    let all = chain_of(&spelled_parts);
    let same = pairs(&(0..all_parts.len()).map(|k| format!("{prefix}_part{k}()")).collect::<Vec<_>>());
    let chain = format!("trans(layout_code_same({core_term}, {parts_term}, {all}, {same}),
        cong_fn<{bytes_ty}, {bytes_ty}>(λ c => layout_code({all}, c), {prefix}_core_written()))");
    let spelled = format!("layout_code({all}, {})", core(&format!("{s}_lit()")));
    let p = step.bytes.len();
    let length = format!("layout_len(command_parts({letters}, {default}, {prefix}_spill), filter_core_code({s}_code(), {jumps}, {pj}), command_lens(), \
        command_measured({letters}, {default}, {prefix}_spill), filter_core_len({p}), filter_core_code_len({s}_code(), {jumps}, {pj}, {p}, {s}_byte_length()))");
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
// facts once the step's length is its lemma's.
fn {prefix}_targets() → CoreTargets(ca_core(), ca_head(), structured_bytes({s}_code()).len(), {jumps}, {pj}) {{
    j(sym({s}_byte_length()), λ n _ => CoreTargets(ca_core(), ca_head(), n, {jumps}, {pj}),
        CoreTargets(
            again := jumps_back(io_entry(), fc_at_jnz(ca_core(), {p}), 6, {jumps}.ld, fc_at_load(ca_core(), {p}), refl),
            quiet := jumps_back(io_entry(), fc_at_cjz(ca_core(), {p}), 6, {jumps}.cd, ca_head(), refl),
            write := write_targets_to(fc_at_write(ca_core(), {p}), ca_head(), {pj}, WriteJumpFacts(refl, refl, refl),
                jumps_back(io_entry(), wl_at_wjz(fc_at_write(ca_core(), {p})), 6, {pj}.zd, ca_head(), refl))))
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
