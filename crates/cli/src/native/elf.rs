//! `write-elf`: an effectful source (a nullary `Source`, native_source)
//! compiled by `native_compile` with its region at the I/O profile's page,
//! assembled, and written in the profile's ELF (`io_elf_file`,
//! linux_x86_64_image), executable.
//!
//! The program and its bytes are read off elaborator forks, which are
//! untrusted, and then stated as literals the kernel checks: that the source
//! compiles to the literal program (`<source>_elf_compiles`), and that the
//! file of any program it compiles to is the bytes written
//! (`<source>_elf_written`). From those, its layout's fit to the page
//! (`<source>_elf_fits`, by evaluation) and the code's length, every
//! certificate states the once-proved compiler's theorem of the file
//! (`<source>_elf_simulates`, by `Source::elf_file_simulates`,
//! native_compile_elf): the process Linux makes of it simulates the source.
//! So a theorem about the source's tree (cat's `cat_implements`) is about
//! the file written. That Linux loads the file as the theorem's loader says
//! is outside the proof. Nothing is written unless the kernel accepts every
//! statement, and a source that does not fit the page, or that the compiler
//! refuses, is refused with its reason (`Source::refusal`, untrusted).
//!
//! A compile is most of what one declaration's fuel buys, so no statement
//! repeats it: the emission is checked against the literal a part of the
//! statement tree at a time; the layout check `Source::compile` makes, and
//! the bytes, by a table of the program's labels (crates/cli/src/native/labels.rs):
//! `Prog::laid_out` and `assemble` look each label up by walking the
//! program, so stating them over the program itself, even a stretch at a
//! time, was quadratic in it (issues/native-compile-linear-layout.md).
//!
//! The read-back evaluates the emission alone, not `Source::compile`: the
//! layout check is quadratic in the program, and a read keeps every value it
//! forces until it returns, so checking the layout there made the read's
//! peak memory grow as the square of the code
//! (issues/native-compile-capacity.md). The table's pass is that check, and
//! a program the compile would refuse for its layout is refused by the
//! kernel at the stretch that fails. The bytes are read on the same fork, a
//! read at a time over the parts' own programs and the table
//! (`emission::byte_reads`), so the program's literal, whose items are most
//! of what elaborating it costs, is elaborated once, in the certificate
//! (issues/write-elf-build-constants.md). The literal spells each address in the region as the compiler
//! does, `add_nat` from the page's start, so the emission's check compares
//! the two by their arguments instead of evaluating each one's bits.
use std::path::{Path, PathBuf};

use heather_elab::{function_ir_source, Elaborator};
use heather_cache::module_image::ImageFreshness;
use heather_cli::{loader, semantic::SemanticSession};

use super::{check_file, emission, labels, symbol_ok, verified, write_new};

/// The I/O profile's file is at most this long (`io_elf_file`'s sixteen-bit
/// size), its header included.
const MAX_FILE: usize = 65535;
const HEADER: usize = 232;
/// Bytes a piece of the code is cut at, at least. A piece's statement costs
/// about its bytes' assembly, linear in them (its addresses are `add_nat`
/// from the page, which compare by their arguments), so the pieces together
/// cost about the same at any size; this one is the cheapest of a sweep over
/// cat, and a piece a long last item stretches well past it still fits a
/// declaration's fuel, which eight times this size does not.
const PIECE: usize = 96;
/// Where the region is, and the window an address in it is spelled from.
const LOW: &str = "DataRegion::io_page().low";
const REGION: std::ops::Range<u64> = 0x410000..0x412000;

/// The modules the probes and the certificate import besides the source's
/// own; `write-elf` loads them itself, so a program file imports only what
/// it uses.
const IMPORTS: &[&str] = &["native_source", "native_compile", "native_compile_correct", "native_compile_elf",
    "linux_x86_64_byte_memory", "linux_x86_64_image", "linux_x86_64_sim", "x86_64", "x86_64_asm", "x86_64_asm_runs",
    "x86_64_asm_table",
    "x86_64_byte_memory", "x86_64_data_read", "x86_64_store", "bitvec", "bool", "list", "logic", "nat", "option"];

pub(super) fn write(args: &[String]) -> Result<(), String> {
    let mut positional = Vec::new();
    let mut output = None;
    let mut cache = None;
    let mut freshness = ImageFreshness::Exact;
    let mut timings = None;
    let mut kernel_workers = None;
    let mut search = vec![PathBuf::from("lib/std"), PathBuf::from("lib")];
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            // `check`'s flag: replay images an earlier build wrote, as the
            // suite's stale lanes do everywhere else.
            "--accept-stale-images" => freshness = ImageFreshness::AcceptStale,
            "-o" | "-L" | "--cache-dir" | "--timings" => {
                let value = PathBuf::from(args.next().ok_or_else(|| format!("{arg} needs a path"))?);
                match arg.as_str() {
                    "-o" => output = Some(value),
                    "-L" => { if !search.contains(&value) { search.push(value); } }
                    "--timings" => timings = Some(value),
                    _ => cache = Some(value),
                }
            }
            "--kernel-workers" => {
                let n = args.next().and_then(|value| value.parse::<usize>().ok()).filter(|&n| n > 0)
                    .ok_or("--kernel-workers needs a positive integer")?;
                kernel_workers = Some(n);
            }
            _ if arg.starts_with('-') => return Err(format!("unknown option `{arg}`")),
            _ => positional.push(arg.as_str()),
        }
    }
    if positional.len() != 2 || output.is_none() {
        return Err("usage: heather write-elf <file.hthr> <source> -o <output> [-L <dir>]... [--cache-dir <dir>] [--accept-stale-images] [--timings <file.tsv>] [--kernel-workers <n>]".into());
    }
    let (source, symbol, output) = (Path::new(positional[0]), positional[1], output.unwrap());
    if !symbol_ok(symbol) {
        return Err("the source must be a plain identifier".into());
    }
    let certificate = output.with_extension("certificate.hthr");
    for path in [&output, &certificate] {
        if path.symlink_metadata().is_ok() {
            return Err(format!("output already exists: {}", path.display()));
        }
    }
    let sources = loader::load_with(source, &search, IMPORTS).map_err(|e| e.msg)?;
    let canonical = source.canonicalize().map_err(|e| format!("{}: {e}", source.display()))?;
    let root = sources.iter().find(|m| m.path == canonical).ok_or("the source is not in its own closure")?.name.clone();
    let mut elab = Elaborator::with_prelude().map_err(|e| format!("prelude: {e}"))?;
    elab.set_kernel_workers(
        kernel_workers.or_else(heather_elab::kernel_workers_from_env).unwrap_or(heather_elab::DEFAULT_KERNEL_WORKERS),
    );
    // As `compile-x86`'s: the library's modules, each read-back and the
    // certificate's declarations each get a row, with what each raised the
    // process's peak memory by.
    if let Some(path) = &timings {
        elab.enable_item_timings();
        heather_elab::stats::live_table(path).map_err(|e| format!("{}: {e}", path.display()))?;
        if elab.kernel_workers() == 1 { elab.enable_value_metrics(); }
    }
    let run_scope = timings.as_ref().map(|_| heather_elab::stats::scope(heather_elab::stats::ScopeKind::Run, "", ""));
    let verdicts = cache.as_ref().map(|dir| {
        let (store, rejected) = heather_cache::Cache::open(dir.clone());
        if let Some(msg) = rejected.as_ref().and_then(|r| r.message()) {
            eprintln!("{msg}");
        }
        std::sync::Arc::new(store)
    });
    if let Some(store) = &verdicts {
        elab.set_gate(std::sync::Arc::clone(store) as std::sync::Arc<dyn heather_elab::gate::KernelGate>);
    }
    let mut session = SemanticSession::new(cache).with_freshness(freshness);
    for module in &sources {
        check_file(&mut elab, &mut session, module)?;
    }

    // The program and its bytes, read on forks: a misreading is not a
    // hazard, since the kernel checks every literal below; it is a refusal.
    let prefix = format!("{symbol}_elf");
    let p = &prefix;
    let imports = IMPORTS.iter().map(|module| format!("import {module};\n")).collect::<String>();
    let probe = format!("{p}_probe");
    let finish = "then(then(c.prog, Block([MovRI(Rdi, BitVec::ofNat(0)), MovRI(Rax, BitVec::ofNat(60))])), Syscall)";
    let layout = format!("{symbol}().layout({LOW})");
    let entry = format!("{symbol}().entry({LOW})");
    let probes = format!("import {root};\n{imports}
fn {p}_room() → List<Nat> {{ [Layout({LOW}, {symbol}().capacities()).size(), DataRegion::io_page().size] }}
fn {p}_refusal() → List<Nat> {{ {symbol}().refusal({LOW}) }}
fn {p}_shape() → List<Nat> {{ {symbol}().shape() }}
");
    let mut fork = elab.fork();
    fork.elab_module_source(&probe, &probes).map_err(|e| e.render(&probes))?;
    let numbers = |fork: &Elaborator, module: &str, name: &str| {
        let _row = heather_elab::stats::scope(heather_elab::stats::ScopeKind::Item, module, name);
        function_ir_source::evaluate_numbers(fork, &format!("{module}::{name}")).map_err(|e| format!("`{symbol}` ({name}): {e}"))
    };
    let address = |width: u32, n: u64| {
        if width == 64 && REGION.contains(&n) { format!("{LOW}.add_nat({})", n - REGION.start) }
        else { format!("@bitvec::BitVec::ofNat({width}, {n})") }
    };
    // The theorem takes the fit as a hypothesis, so a program past the page
    // would be written with nothing said of it.
    if let [size, page] = numbers(&fork, &probe, &format!("{p}_room"))?[..] && size > page {
        return Err(format!("`{symbol}` does not fit the I/O page: its words, buffers and scratch range take {size} bytes \
            and the page holds {page}, so `Source::elf_file_simulates` would not cover it"));
    }
    // The program a part at a time, each read on its own, so a read holds
    // one part's values and not the program's.
    let plan = emission::plan(p, &format!("{symbol}().main"), &entry, &layout, &numbers(&fork, &probe, &format!("{p}_shape"))?)?;
    let parts = format!("{p}_parts");
    // The refusal again here: once this module is elaborated, the fork reads
    // only its names.
    let text = format!("import {root};\n{imports}\n{}fn {p}_refusal() → List<Nat> {{ {symbol}().refusal({LOW}) }}\n", plan.text);
    fork.elab_module_source(&parts, &text).map_err(|e| e.render(&text))?;
    let mut readings = Vec::with_capacity(plan.reads.len());
    for (name, &whole) in plan.reads.iter().zip(&plan.whole) {
        match emission::Reading::of(&numbers(&fork, &parts, name)?, whole, &address)? {
            Some(reading) => readings.push(reading),
            None => return Err(refused(symbol, &numbers(&fork, &parts, &format!("{p}_refusal"))?)),
        }
    }
    // The literal in stretches, each its own definition on the one before,
    // cut too wherever a statement of the emission starts or ends.
    let emission::Stated { theorems: statements, items, lens, mut cuts, spans } = emission::state(p, &entry, &layout, plan, readings)?;
    let length = lens.iter().sum::<u64>() as usize;
    if HEADER + length > MAX_FILE {
        return Err(format!("`{symbol}` compiles to {length} bytes, past the profile's {MAX_FILE} with its header"));
    }
    if let Some(why) = layout_refusal(&items, &lens) {
        return Err(format!("`{symbol}` is refused: the program's labels did not lay out ({why})"));
    }
    let pieces = verified::cut_pieces(&lens, PIECE);
    // The literal cut where each piece's window ends too, so the window and
    // the pass up to it are definitions.
    cuts.extend(labels::piece_cuts(&pieces, items.len()));
    let code = emission::code(p, &items, &cuts);
    let offsets = labels::offsets(&lens);
    let table = labels::table(p, &items, &offsets);
    let header = format!("io_elf_header(BitVec::ofNat(232 + {length}), BitVec::ofNat((232 + {length}).shr(8)))");
    // The bytes on the same fork, a read at a time by the parts' programs
    // and the table, so only the certificate elaborates the literal.
    let (byte_text, byte_reads) = emission::byte_reads(p, &spans, &offsets);
    let reads = format!("import {root};\nimport {parts};\n{imports}\n{table}{byte_text}\
        fn {p}_header_numbers() → List<Nat> {{ {header}.map(λ (b: BitVec(8)) => b.toNat()) }}\n");
    let read = format!("{p}_read");
    fork.elab_module_source(&read, &reads).map_err(|e| e.render(&reads))?;
    let byte = |n: u64| u8::try_from(n).map_err(|_| "a byte above 255".to_string());
    let mut bytes = Vec::with_capacity(length);
    for (name, span) in &byte_reads {
        let read = numbers(&fork, &read, name)?;
        if read.len() as u64 != lens[span.start..span.start + span.count].iter().sum::<u64>() {
            return Err(format!("`{symbol}`'s bytes from item {} are not as long as its items", span.start));
        }
        for n in read { bytes.push(byte(n)?); }
    }
    if bytes.len() != length {
        return Err(format!("`{symbol}`'s bytes did not read back"));
    }
    let head = numbers(&fork, &read, &format!("{p}_header_numbers"))?.into_iter().map(byte).collect::<Result<Vec<u8>, String>>()?;
    drop(fork);
    if head.len() != HEADER {
        return Err("the header did not read back".into());
    }
    let header_literal: Vec<String> = head.iter().map(|b| format!("@bitvec::BitVec::ofNat(8, {b})")).collect();

    let mut text = format!("// `{symbol}` compiled into the I/O profile's ELF, as `heather write-elf` writes
// it: generated, and checked by the kernel.
import {root};
{imports}
// The program: what `{symbol}().compile` computes.
{code}
// Its emission, a part of the statement tree at a time.
{statements}
theorem {p}_emitted(): {symbol}().main.emit({entry}, {symbol}().layout({LOW}), 0).map(λ (c: Compiled) => {finish}) = Some({p}_code()) {{
    j(sym({p}_entry()), λ x _ => {symbol}().main.emit(x, {symbol}().layout({LOW}), 0).map(λ (c: Compiled) => {finish}) = Some({p}_code()),
        cong_fn<Option<Compiled>, Option<Prog>>(λ o => o.map(λ (c: Compiled) => {finish}), {p}_e_0()))
}}

// Its layout, by a table of its labels checked a stretch at a time.
{table}{layout}
theorem {p}_holes(): {p}_code().no_holes().IsTrue() {{ trivial }}

theorem {p}_laid(): {p}_code().laid_out().IsTrue() {{
    {p}_table().laid_out_of({p}_code(), {length}, {p}_checked_{count}(), {p}_holes())
}}

theorem {p}_compiles(): {symbol}().compile({LOW}) = Some({p}_code()) {{
    {symbol}().compile_of({LOW}, {p}_code(), {p}_emitted(), {p}_laid())
}}

// Its words, buffers and scratch range fit the page.
theorem {p}_fits(): Layout({LOW}, {symbol}().capacities()).size() <= DataRegion::io_page().size {{
    Nat::leb_sound(Layout({LOW}, {symbol}().capacities()).size(), DataRegion::io_page().size, trivial)
}}

// The bytes, a piece at a time from the last item.
", count = items.len(), layout = labels::layout(p, &offsets, &cuts));
    text.push_str(&labels::byte_pieces(p, &pieces, &bytes, items.len(), &offsets));
    text.push_str(&format!("
fn {p}_header() → List<BitVec(8)> {{ [{}] }}
theorem {p}_header_is(): {header} = {p}_header() {{ refl }}
{lengths}theorem {p}_length(): {p}_upto_0().len() = {length} {{ {p}_upto_0_len() }}

// The file written: its header, then the code.
fn {p}_file() → List<BitVec(8)> {{ {p}_header() ++ {p}_upto_0() }}

theorem {p}_file_is(): io_elf_file({p}_upto_0()) = {p}_file() {{
    trans(cong_fn<Nat, List<BitVec(8)>>(λ n => List::append(io_elf_header(BitVec::ofNat(232 + n), BitVec::ofNat((232 + n).shr(8))), {p}_upto_0()), {p}_length()),
        cong_fn<List<BitVec(8)>, List<BitVec(8)>>(λ h => List::append(h, {p}_upto_0()), {p}_header_is()))
}}

// Whatever names the compile's program, its file is the one written.
theorem {p}_written(program: Prog, compiled: {symbol}().compile({LOW}) = Some(program)):
    io_elf_file(assemble(no_fills(), program, [])) = {p}_file() {{
    let same: ({p}_code() = program) = Option::some_inj({p}_code(), program, trans(sym({p}_compiles()), compiled));
    j(same, λ q _ => io_elf_file(assemble(no_fills(), q, [])) = {p}_file(),
        trans(cong_fn<List<BitVec(8)>, List<BitVec(8)>>(λ x => io_elf_file(x), {p}_bytes()), {p}_file_is()))
}}

theorem {p}_short(): 232 + assemble(no_fills(), {p}_code(), []).len() <= 65536 {{
    j(sym({p}_bytes()), λ b _ => 232 + b.len() <= 65536,
        j(sym({p}_length()), λ n _ => 232 + n <= 65536, Nat::leb_sound(232 + {length}, 65536, trivial)))
}}

// The process Linux makes of the file written, at its entry, simulates
// `{symbol}`'s tree (`Source::elf_file_simulates`, from
// `native_compile_correct`).
theorem {p}_simulates(s: MachineState<X86Memory(X86Profile::io())>, entry: s.rip = io_entry(),
    loaded: s.memory = X86Memory::io_load({p}_file())): SimProgram(X86Profile::io().linux(), {symbol}().denote(), s) {{
    {symbol}().elf_file_simulates({p}_code(), {p}_compiles(), {p}_fits(), {p}_short(), s, entry,
        j(sym({p}_written({p}_code(), {p}_compiles())), λ f _ => s.memory = X86Memory::io_load(f), loaded))
}}
", header_literal.join(", "), lengths = upto_lengths(p, &pieces, length)));
    let mut file = head;
    file.extend_from_slice(&bytes);

    let unchecked = certificate.with_extension("unchecked.hthr");
    if unchecked.symlink_metadata().is_ok() {
        std::fs::remove_file(&unchecked).map_err(|e| format!("{}: {e}", unchecked.display()))?;
    }
    write_new(&unchecked, text.as_bytes())?;
    eprintln!("checking `{symbol}`'s compile and its {} bytes in {}", file.len(), unchecked.display());
    let checked = check_file(&mut elab, &mut session, &loader::Module {
        name: format!("{p}_certificate"),
        path: unchecked.clone(),
        src: text.clone(),
    });
    drop(run_scope);
    if let Some(store) = verdicts {
        if let Err(err) = store.save() {
            eprintln!("cache: could not write verdicts: {err}");
        }
    }
    // Before the refusal, which is the build worth attributing.
    if let Some(path) = &timings {
        heather_elab::stats::dump(&heather_elab::stats::Dest::File(path.clone()), &elab.take_item_timings())
            .map_err(|e| format!("{}: {e}", path.display()))?;
    }
    checked?;
    write_new(&certificate, text.as_bytes())?;
    std::fs::remove_file(&unchecked).map_err(|e| format!("{}: {e}", unchecked.display()))?;
    write_executable(&output, &file)?;
    println!("{}: {} bytes, `{symbol}` compiled into the I/O profile's ELF as the kernel checked it", output.display(), file.len());
    println!("certificate: {}", certificate.display());
    Ok(())
}

/// The message for a compile `Source::refusal` explains
/// (native_compile.hthr): the statement and the reason it was refused.
fn refused(symbol: &str, why: &[u64]) -> String {
    let [at, kind, reason, first, second] = *why else {
        return format!("`{symbol}` did not compile, and `Source::refusal` names no reason");
    };
    let kind = match kind { 0 => "a computation", 1 => "a call", 2 => "a branch", 3 => "a loop", 4 => "an exit", _ => "the program" };
    let reason = match reason {
        0 => format!("a {} region; only a dataflow leaf compiles (issues/native-compile-wider-leaves.md)",
            ["", "sequence", "compose", "conditional", "call", "loop"].get(first as usize).unwrap_or(&"structured")),
        1 => format!("the leaf needs {first} registers, one per input and per node, and the pool holds {second}"),
        2 => "the leaf's nodes are not in evaluation order".into(),
        3 => "the leaf writes one of its own inputs".into(),
        4 => format!("word {first} is past the {second} word slots"),
        5 => format!("an input of width {first}: only words (64) and bits (1) load"),
        6 => "S4's lowering refused the leaf".into(),
        7 => format!("`{}` is not compiled yet (issues/native-compile-other-calls.md)",
            ["", "", "open", "close", "stat", "fstat"].get(first as usize).unwrap_or(&"the call")),
        8 => format!("buffer {first} does not exist: the source has {second}"),
        9 => "the program's labels did not lay out".into(),
        10 => format!("a leaf with a byte node compiles only as that one node, its words in the slots and its buffer present ({first} nodes)"),
        _ => format!("reason {reason} ({first}, {second})"),
    };
    if kind == "the program" { format!("`{symbol}` is refused: {reason}") }
    else { format!("`{symbol}` is refused at statement {at}, {kind}: {reason}") }
}

/// `{p}_upto_c()`'s length for each piece `c`, from the program's start:
/// the code is the pieces appended one after another, so one `refl` over
/// its length walks every append for each of its bytes, quadratic in the
/// program; here each is its piece's length on the one before.
fn upto_lengths(p: &str, pieces: &[verified::Piece], length: usize) -> String {
    let m = pieces.len();
    let mut text = format!("theorem {p}_upto_{m}_len(): {p}_upto_{m}().len() = 0 {{ refl }}\n");
    let mut end = length;
    let mut upto = Vec::new();
    for piece in pieces { upto.push(end); end = piece.start; }
    for (c, n) in upto.iter().enumerate().rev() {
        let next = c + 1;
        text.push_str(&format!("theorem {p}_upto_{c}_len(): {p}_upto_{c}().len() = {n} {{
    trans(List::len_append({p}_upto_{next}(), {p}_piece_{c}()), cong_fn<Nat, Nat>(λ n => n + {p}_piece_{c}().len(), {p}_upto_{next}_len()))
}}
"));
    }
    text
}

/// What `Prog::laid_out` checks of the names, over the items read back: the
/// read evaluates the emission alone (see the module comment), so a program
/// the compile would refuse for its labels is refused here with a reason,
/// before the kernel refuses its layout's statements, which still decide.
fn layout_refusal(items: &[(u64, String)], lens: &[u64]) -> Option<String> {
    let mut named = std::collections::BTreeMap::new();
    let mut at = 0;
    for ((name, _), len) in items.iter().zip(lens) {
        if *name != 0 && named.insert(*name, at).is_some() { return Some(format!("label {name} is named twice")); }
        at += len;
    }
    let mut at = 0;
    for ((_, item), len) in items.iter().zip(lens) {
        let target = |prefix: &str| item.strip_prefix(prefix)
            .and_then(|rest| rest.trim_end_matches(')').rsplit(", ").next()?.parse::<u64>().ok());
        let (jump, forward) = match (target("Jcc("), target("Jmp(").or_else(|| target("CallTo("))) {
            (Some(t), _) => (t, true),
            (_, Some(t)) => (t, false),
            _ => { at += len; continue; }
        };
        match named.get(&jump) {
            None => return Some(format!("a jump to label {jump}, which no item names")),
            Some(&to) if forward && to < at + len => return Some(format!("a conditional jump back to label {jump}")),
            _ => {}
        }
        at += len;
    }
    None
}

fn write_executable(path: &Path, bytes: &[u8]) -> Result<(), String> {
    use std::io::Write;
    use std::os::unix::fs::OpenOptionsExt;
    let mut file = std::fs::OpenOptions::new().write(true).create_new(true).mode(0o755).open(path)
        .map_err(|e| format!("{}: {e}", path.display()))?;
    file.write_all(bytes).map_err(|e| format!("{}: {e}", path.display()))
}
