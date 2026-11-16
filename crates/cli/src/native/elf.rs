//! `write-elf`: an effectful source (a nullary `Source`, native_source)
//! compiled by `native_compile` with its region at the I/O profile's page,
//! assembled, and written in the profile's ELF (`io_elf_file`,
//! linux_x86_64_image), executable.
//!
//! The program and its bytes are read off elaborator forks, which are
//! untrusted, and then stated as literals the kernel checks: that the source
//! compiles to the literal program (`<source>_elf_compiles`), and that the
//! file of any program it compiles to is the bytes written
//! (`<source>_elf_written`). The program's data segment is its layout's
//! size rounded up to a page (`<source>_elf_size`), up to the profile's
//! limit (issues/native-data-capacity.md); it is zero-filled, so it takes
//! nothing in the file. From those, the layout's fit to the segment
//! (`<source>_elf_fits`, by evaluation) and the code's length, every
//! certificate states the once-proved compiler's theorem of the file
//! (`<source>_elf_simulates`, by `Source::elf_file_simulates`,
//! native_compile_elf): the process Linux makes of it simulates the source.
//! So a theorem about the source's tree (cat's `cat_implements`) is about
//! the file written. That Linux loads the file as the theorem's loader says
//! is outside the proof. Nothing is written unless the kernel accepts every
//! statement, and a source past the profile's data limit, or that the compiler
//! refuses, is refused with its reason (`Source::refusal`, untrusted).
//!
//! A compile is most of what one declaration's fuel buys, so no statement
//! repeats it, and nothing that grows with the program is one statement:
//! a builder's tool is lowered a part of its statement tree at a time
//! (`parts`); the emission, and the compile's check of the homes, are
//! checked against the literal a part of the statement tree at a time; the
//! entry's initial bytes a few dozen at a time (`emission::Inits`,
//! issues/native-tool-certificate-budget.md); the layout check `Source::compile` makes, and
//! the bytes, by a table of the program's labels (crates/cli/src/native/labels.rs):
//! `Prog::laid_out` and `assemble` look each label up by walking the
//! program, so stating them over the program itself, even a stretch at a
//! time, was quadratic in it (issues/native-compile-linear-layout.md).
//!
//! A source that calls functions (`Source.functions`, a builder's `program`)
//! has them compiled into the same file by the function compiler, after the
//! program's own code (`Prog::links`, native_compile,
//! docs/native/native-one-compiler-design.md §2.2): the literal spells each
//! function, the homes carry where their values go (`plan_program`'s
//! heuristic, run once here and checked by the lowering), and the functions'
//! lowering onto the program is one statement (`<source>_elf_deep`).
//!
//! The read-back evaluates the emission alone, not `Source::compile`: the
//! layout check is quadratic in the program, and a read keeps every value it
//! forces until it returns, so checking the layout there made the read's
//! peak memory grow as the square of the code
//! (issues/native-compile-capacity.md). The table's pass is that check, and
//! a program the compile would refuse for its layout is refused by the
//! kernel at the stretch that fails. The bytes are read on the same fork, a
//! read at a time over the parts' own programs (a long one in windows) and
//! the table (`emission::byte_reads`), so the program's literal, whose items are most
//! of what elaborating it costs, is elaborated once, in the certificate
//! (issues/write-elf-build-constants.md). The literal spells each address in the region as the compiler
//! does, `add_nat` from the segment's start, so the emission's check compares
//! the two by their arguments instead of evaluating each one's bits.
use std::path::{Path, PathBuf};

use heather_elab::{function_ir_source, Elaborator};
use heather_cache::module_image::ImageFreshness;
use heather_cli::{loader, semantic::SemanticSession};

use super::{allocator, check_file, emission, labels, lowered, parts, refuse_assumptions, symbol_ok, verified, write_new};

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
/// Where the data segment starts; an address in it is spelled from here.
pub(super) const LOW: &str = "io_data_low()";
const DATA: u64 = 0x410000;
/// The segment is a whole number of pages.
const PAGE: u64 = 4096;

/// The modules the probes and the certificate import besides the source's
/// own; `write-elf` loads them itself, so a program file imports only what
/// it uses. In the lib so the library gate can hold them to the world.
use heather_cli::world::WRITE_ELF_IMPORTS as IMPORTS;

pub(super) fn write(args: &[String]) -> Result<(), String> {
    let mut positional = Vec::new();
    let mut output = None;
    let mut cache = None;
    let mut freshness = ImageFreshness::Exact;
    let mut timings = None;
    let mut kernel_workers = None;
    let mut world = None;
    let mut search = vec![PathBuf::from("lib/std"), PathBuf::from("lib")];
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            // `check`'s flag: replay images an earlier build wrote, as the
            // suite's stale lanes do everywhere else.
            "--accept-stale-images" => freshness = ImageFreshness::AcceptStale,
            "-o" | "-L" | "--cache-dir" | "--timings" | "--world" => {
                let value = PathBuf::from(args.next().ok_or_else(|| format!("{arg} needs a path"))?);
                match arg.as_str() {
                    "-o" => output = Some(value),
                    "-L" => { if !search.contains(&value) { search.push(value); } }
                    "--timings" => timings = Some(value),
                    "--world" => world = Some(value),
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
    if !(1..=2).contains(&positional.len()) || output.is_none() {
        return Err("usage: heather write-elf <file.hthr> [<source>] -o <output> [-L <dir>]... [--cache-dir <dir>] [--accept-stale-images] [--world <dir>] [--timings <file.tsv>] [--kernel-workers <n>]".into());
    }
    // The source: a function of no arguments that builds a `Source` or a
    // `Tool` (`tr`), or the `Source` a `runtime fn` program publishes, by
    // its path (`tr_upper::source`); `main::source` when none is named
    // (docs/native/io-programs-design.md §5, D1).
    let (source, symbol, output) = (Path::new(positional[0]), positional.get(1).copied().unwrap_or("main::source"), output.unwrap());
    let path = symbol.contains("::");
    if !symbol.split("::").all(symbol_ok) {
        return Err("the source must be an identifier, or a path such as `main::source`".into());
    }
    let certificate = output.with_extension("certificate.hthr");
    for path in [&output, &certificate] {
        if path.symlink_metadata().is_ok() {
            return Err(format!("output already exists: {}", path.display()));
        }
    }
    // `--world` is accepted and ignored: every module is checked over its
    // own closure (`docs/infrastructure/module-dag-design.md`), so the closure is all this
    // loads and its images are the ones every other process wrote.
    let _ = &world;
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
    // Without a directory, the verdicts of this process alone
    // (`Cache::in_process`).
    let gate = verdicts.clone().unwrap_or_else(|| std::sync::Arc::new(heather_cache::Cache::in_process()));
    elab.set_gate(gate as std::sync::Arc<dyn heather_elab::gate::KernelGate>);
    let mut session = SemanticSession::new(cache).with_freshness(freshness);
    for module in &sources {
        check_file(&mut elab, &mut session, module)?;
    }

    // The program and its bytes, read on forks: a misreading is not a
    // hazard, since the kernel checks every literal below; it is a refusal.
    let prefix = format!("{}_elf", symbol.replace("::", "_"));
    let p = &prefix;
    let imports = IMPORTS.iter().map(|module| format!("import {module};\n")).collect::<String>();
    let probe = format!("{p}_probe");
    // A builder's tool (`Tool`, native_build) is lowered a part at a time
    // (`parts`); any other source is read as a literal whole.
    let tool_probe = format!("{p}_tool");
    let tool_text = format!("import {root};\n{imports}\nfn {p}_is_tool() → Tool {{ {symbol}() }}\n\
        fn {p}_whole() → Nat {{ {symbol}().opened(0).procedures.len() + {symbol}().opened(0).functions.len() }}\n");
    let mut tool_fork = elab.fork();
    let is_tool = !path && tool_fork.elab_module_source(&tool_probe, &tool_text).is_ok();
    // A tool with procedures, or one that calls functions of its program
    // (`call`, native_build), is lowered whole, as a literal like any
    // source: the part-at-a-time lowering (`parts`) walks `main` only.
    let in_parts = is_tool && function_ir_source::evaluate_number(&tool_fork, &format!("{tool_probe}::{p}_whole")).map_err(|e| format!("`{symbol}` (procedures): {e}"))? == 0;
    drop(tool_fork);
    let source = if is_tool { format!("{symbol}().source()") } else if path { symbol.to_string() } else { format!("{symbol}()") };
    let (src, lowered, lowered_is, shapes) = if in_parts {
        let stated = tool_parts(&elab, p, symbol, &root, &imports)?;
        (format!("{p}_lowered"), stated.defs, stated.theorems, Some(stated.shapes))
    } else {
        // The source as a literal, read on a fork, and compiled in its place:
        // every probe and statement below names the source, and a builder's
        // lowering would otherwise be evaluated again in each.
        let spelling = format!("{p}_spelling");
        let spelling_text = format!("import {root};\n{imports}\nfn {p}_spelled() → List<Nat> {{ {source}.spelled() }}\n");
        let mut fork = elab.fork();
        fork.elab_module_source(&spelling, &spelling_text).map_err(|e| e.render(&spelling_text))?;
        let spelled = {
            let _row = heather_elab::stats::scope(heather_elab::stats::ScopeKind::Item, &spelling, &format!("{p}_spelled"));
            function_ir_source::evaluate_numbers(&fork, &format!("{spelling}::{p}_spelled")).map_err(|e| format!("`{symbol}` (spelled): {e}"))?
        };
        drop(fork);
        match lowered::literal(p, &spelled).map_err(|e| format!("`{symbol}` did not read back: {e}"))? {
            Some((text, shapes)) => {
                let theorem = format!("theorem {p}_lowered_is(): {source} = {p}_lowered() {{ refl }}\n");
                (format!("{p}_lowered"), text, theorem, Some(shapes))
            }
            // A published `Source` is a value, not a function to call: it
            // is compiled through its literal.
            None if path => return Err(format!("`{symbol}` did not read back as a literal")),
            None => (symbol.to_string(), String::new(), String::new(), None),
        }
    };
    let finish = "then(then(c.prog, Block([MovRI(Rdi, BitVec::ofNat(0)), MovRI(Rax, BitVec::ofNat(60))])), Syscall)";
    let homes = format!("{p}_homes()");
    // The layout by name, a literal (`layout_literal`): every statement of
    // the emission names it, and `Source::layout` walks the program for its
    // word count and filters the register pools by the homes, which each
    // declaration of the certificate otherwise did again
    // (issues/native-certificate-layout-per-item.md).
    let layout = format!("{p}_layout()");
    let entry = format!("{src}().entry({LOW}, {homes})");
    let probes = format!("import {root};\n{imports}{lowered}
fn {p}_room() → List<Nat> {{ [Layout::of({LOW}, {src}().words, {src}().capacities(), Homes([], [])).size(), io_data_limit()] }}
fn {p}_sizes() → List<Nat> {{ Cons({src}().words, {src}().capacities()) }}
fn {p}_shape() → List<Nat> {{ {src}().shape() }}
fn {p}_homes_spelled() → List<Nat> {{ {src}().homes().spelled() }}
fn {p}_lowered_spelled() → List<Nat> {{ {src}().spelled() }}
fn {p}_first() → List<Nat> {{ [{src}().main_names(), {src}().procedures.len(), {src}().functions.len()] }}
fn {p}_bodies() → List<Nat> {{ {src}().procedures.procedures_shapes({src}().main_end_names()) }}
fn {p}_place_number(place: Place) → Nat {{ match place {{ Into(register) => register.index(), Folded => 16, Saving(count) => 17 + count, Spilling(mask) => 32 + mask }} }}
fn {p}_places() → List<Nat> {{ plan_program({src}().functions).map({p}_place_number) }}
");
    let mut fork = elab.fork();
    fork.elab_module_source(&probe, &probes).map_err(|e| e.render(&probes))?;
    let numbers = |fork: &Elaborator, module: &str, name: &str| {
        let _row = heather_elab::stats::scope(heather_elab::stats::ScopeKind::Item, module, name);
        function_ir_source::evaluate_numbers(fork, &format!("{module}::{name}")).map_err(|e| format!("`{symbol}` ({name}): {e}"))
    };
    // The segment: the layout's size in whole pages, which the theorem
    // takes only up to the profile's limit.
    let [needed, limit] = numbers(&fork, &probe, &format!("{p}_room"))?[..] else {
        return Err(format!("`{symbol}`'s layout did not read back"));
    };
    let size = needed.div_ceil(PAGE) * PAGE;
    if size > limit {
        return Err(format!("`{symbol}` needs a data segment of {size} bytes for its words, buffers, scratch range and saved RSP, \
            past the I/O profile's limit of {limit} (`io_data_limit`)"));
    }
    let sizes = numbers(&fork, &probe, &format!("{p}_sizes"))?;
    let region = DATA..DATA + size;
    let address = |width: u32, n: u64| {
        if width == 64 && region.contains(&n) { format!("{LOW}.add_nat({})", n - DATA) }
        else { format!("@bitvec::BitVec::ofNat({width}, {n})") }
    };
    // The words' homes, from the greedy allocator (`Source::homes`,
    // native_alloc), spelled: the compile checks them, so the allocator is
    // run once, here, and never by the kernel. Over a literal source it runs
    // in Rust (`allocator`), the same steps on the literal read back: on the
    // fork every value it forced was kept until the read returned, and its
    // memory grew with the tool past the rail. `HEATHER_ELF_ALLOCATOR=both`
    // runs the fork's too and refuses unless they agree.
    let on_fork = |fork: &Elaborator| numbers(fork, &probe, &format!("{p}_homes_spelled"));
    let in_rust = if lowered.is_empty() { None } else { allocator::homes_spelled(&numbers(&fork, &probe, &format!("{p}_lowered_spelled"))?) };
    if let Some(ours) = &in_rust && std::env::var("HEATHER_ELF_ALLOCATOR").as_deref() == Ok("both") && on_fork(&fork)? != *ours {
        return Err(format!("`{symbol}`'s homes from native_alloc and from write-elf's allocator differ"));
    }
    // The program a part at a time, each read on its own, so a read holds
    // one part's values and not the program's.
    let [first, procedures, functions] = numbers(&fork, &probe, &format!("{p}_first"))?[..] else {
        return Err(format!("`{symbol}`'s procedures did not read back"));
    };
    let bodies = if procedures > 0 { numbers(&fork, &probe, &format!("{p}_bodies"))? } else { Vec::new() };
    let plan = emission::plan(p, &format!("{src}().main"), &entry, &layout, &numbers(&fork, &probe, &format!("{p}_shape"))?,
        first, (procedures > 0 || functions > 0).then_some(emission::CallsOf { src: &src, homes: &homes, shapes: &bodies, functions: usize::try_from(functions).map_err(|_| format!("`{symbol}`'s functions did not read back"))? }))?;
    // Where the values of the functions the source calls go, from the
    // function compiler's heuristic (`plan_program`,
    // function_ir_lower_calls), spelled: a proposal the functions' lowering
    // checks (`Prog::links`), so the heuristic runs once, here.
    let places = if functions == 0 { None } else {
        let places = numbers(&fork, &probe, &format!("{p}_places"))?.into_iter().map(|n| match n {
            16 => Ok("Folded".to_string()),
            n if n >= 32 => Ok(format!("Spilling({})", n - 32)),
            n if n >= 17 => Ok(format!("Saving({})", n - 17)),
            n => verified::GPRS.get(n as usize).map(|gpr| format!("Into({gpr})")).ok_or_else(|| format!("`{symbol}`'s functions' placement did not read back")),
        }).collect::<Result<Vec<_>, String>>()?;
        Some(format!("[{}]", places.join(", ")))
    };
    // The parts over the homes, and the check's verdict on them. The refusal
    // here: once this module is elaborated, the fork reads only its names.
    let state = |fork: &mut Elaborator, parts: &str, spelled: &[u64]| -> Result<(String, Vec<u64>), String> {
        let homes_def = format!("fn {homes} → Homes {{ {} }}\nfn {layout} → Layout {{ {} }}\n",
            homes_literal(spelled, places.as_deref()).ok_or_else(|| format!("`{symbol}`'s homes did not read back"))?,
            layout_literal(&src, &homes, &sizes, spelled).ok_or_else(|| format!("`{symbol}`'s layout did not read back"))?);
        let text = format!("import {root};\n{imports}{lowered}\n{homes_def}{}fn {p}_refusal() → List<Nat> {{ {src}().refusal({LOW}, {homes}) }}\n\
            fn {p}_allocation() → List<Nat> {{ match {src}().allocation_ok({homes}) {{ True => [], False => [0, 5, 12, 0, 0] }} }}\n\
            fn {p}_live_sets() → List<Nat> {{ {src}().checked_spelled({homes}) }}\n", plan.text);
        fork.elab_module_source(parts, &text).map_err(|e| e.render(&text))?;
        Ok((homes_def, numbers(fork, parts, &format!("{p}_allocation"))?))
    };
    let mut parts = format!("{p}_parts");
    let first = match &in_rust { Some(ours) => ours.clone(), None => on_fork(&fork)? };
    let (mut homes_def, mut allocation) = state(&mut fork, &parts, &first)?;
    // `Greedy::assign`'s fallback: a colouring the check refuses gives way
    // to every word in its slot, which is the fork's answer then
    // (`Homes::or_else`).
    if !allocation.is_empty() && in_rust.is_some() {
        parts = format!("{p}_parts_slotted");
        let slotted = on_fork(&fork)?;
        (homes_def, allocation) = state(&mut fork, &parts, &slotted)?;
    }
    // Homes the check refuses are refused here, by reason, and not by the
    // kernel at the certificate: the parts emit whatever the homes say.
    if !allocation.is_empty() {
        return Err(refused(symbol, &allocation));
    }
    let live_sets = numbers(&fork, &parts, &format!("{p}_live_sets"))?;
    let plain = numbers(&fork, &parts, &format!("{p}_plain"))?;
    // The reads of the parts in sessions that share what they force
    // (`function_ir_source::read_sharing`): a part's statement, its
    // live-out set and what is known as it starts are each spelled from its
    // parent's, and a read on its own works every one of them out from the
    // root again, which was most of what the reads cost
    // (issues/native-tool-compile-attribution.md).
    let shared = |reads: &function_ir_source::Reads<'_, '_>, name: &str| {
        let _row = heather_elab::stats::scope(heather_elab::stats::ScopeKind::Item, &parts, name);
        reads.numbers(&format!("{parts}::{name}")).map_err(|e| format!("`{symbol}` ({name}): {e}"))
    };
    // With them each part's live-out set, to state as a literal: spelled
    // from its parent's, a part's set is otherwise worked out again from
    // the root in every declaration of the certificate that reads it, which
    // for a part deep in nested loops is past one declaration's fuel
    // (`native_heap_tools`' tac and sort,
    // docs/native/native-heap-arena-design.md §3). From a literal parent the
    // kernel checks a part's set in one step down the tree: the joins
    // (`Stmt::emits_then_of` and its siblings) compare it with its spelling
    // over the parent's literal.
    enum Got { Set(Vec<u64>), Items(emission::Reading) }
    let order = emission::reads(p, &plan);
    let got = function_ir_source::read_sharing(&fork, order.len(), |reads, i| match &order[i] {
        emission::Read::Live(name) => shared(reads, name).map(Got::Set),
        emission::Read::Items(r) => {
            let (name, whole) = plan.reads.get(*r).zip(plan.whole.get(*r)).ok_or_else(|| format!("`{symbol}`'s parts did not read back in order"))?;
            match emission::Reading::of(&shared(reads, name)?, *whole, &address)? {
                Some(reading) => Ok(Got::Items(reading)),
                None => Err(refused(symbol, &numbers(&fork, &parts, &format!("{p}_refusal"))?)),
            }
        }
    })?;
    let (mut sets, mut readings) = (Vec::new(), Vec::with_capacity(plan.reads.len()));
    for read in got {
        match read { Got::Set(set) => sets.push(set), Got::Items(reading) => readings.push(reading) }
    }
    let mut plan = plan;
    plan.text = emission::live_literals(p, &plan.text, &sets)?;
    // The literal in stretches, each its own definition on the one before,
    // cut too wherever a statement of the emission starts or ends.
    let emission::Stated { theorems: statements, items, lens, mut cuts, spans, calls } = emission::state(p, &entry, &layout, plan, &plain, readings, shapes.as_deref().map(|shapes| emission::Inits { src: &src, homes: &homes, shapes }),
        emission::Checks { src: &src, homes: &homes, sets: &live_sets })?;
    let length = lens.iter().sum::<u64>() as usize;
    if HEADER + length > MAX_FILE {
        return Err(format!("`{symbol}` compiles to {length} bytes, past the profile's {MAX_FILE} with its header"));
    }
    if let Some(why) = layout_refusal(&items, &lens) {
        // The compile's own reason first, where it has one: functions that
        // do not link (`Prog::links`) leave the calls of them with no label
        // to go to, and the reason is theirs, not the layout's.
        let reason = numbers(&fork, &parts, &format!("{p}_refusal"))?;
        if !reason.is_empty() { return Err(refused(symbol, &reason)); }
        return Err(format!("`{symbol}` is refused: the program's labels did not lay out ({why})"));
    }
    let pieces = verified::cut_pieces(&lens, PIECE);
    // The literal cut where each piece's window ends too, so the window and
    // the pass up to it are definitions.
    cuts.extend(labels::piece_cuts(&pieces, items.len()));
    let code = emission::code(p, &items, &cuts);
    let offsets = labels::offsets(&lens);
    let table = labels::table(p, &items, &offsets);
    let header = format!("io_elf_header(BitVec::ofNat(232 + {length}), BitVec::ofNat((232 + {length}).shr(8)), {size})");
    // The bytes: a part's as its read gave them, the items' around parts
    // read on the same fork, and every jump's displacement written here,
    // now that the labels are laid out (`labels::link`). So only the
    // certificate elaborates the literal, and its table.
    let (byte_text, byte_reads) = emission::byte_reads(p, &spans);
    let reads = format!("import {root};\nimport {parts};\n{imports}\n{byte_text}\
        fn {p}_header_numbers() → List<Nat> {{ {header}.map(λ (b: BitVec(8)) => b.toNat()) }}\n");
    let read = format!("{p}_read");
    fork.elab_module_source(&read, &reads).map_err(|e| e.render(&reads))?;
    let byte = |n: u64| u8::try_from(n).map_err(|_| "a byte above 255".to_string());
    let mut bytes = vec![0u8; length];
    let mut place = |items: std::ops::Range<usize>, read: &[u8]| {
        let at = offsets[items.start] as usize..offsets[items.end] as usize;
        if read.len() != at.len() {
            return Err(format!("`{symbol}`'s bytes from item {} are not as long as its items", items.start));
        }
        bytes[at].copy_from_slice(read);
        Ok(())
    };
    for span in &spans {
        if let Some(read) = &span.bytes { place(span.start..span.start + span.count, read)?; }
    }
    for (name, items) in &byte_reads {
        place(items.clone(), &numbers(&fork, &read, name)?.into_iter().map(byte).collect::<Result<Vec<u8>, String>>()?)?;
    }
    labels::link(&items, &offsets, &mut bytes).map_err(|why| format!("`{symbol}`'s bytes did not read back: {why}"))?;
    let head = numbers(&fork, &read, &format!("{p}_header_numbers"))?.into_iter().map(byte).collect::<Result<Vec<u8>, String>>()?;
    drop(fork);
    if head.len() != HEADER {
        return Err("the header did not read back".into());
    }
    let header_literal: Vec<String> = head.iter().map(|b| format!("@bitvec::BitVec::ofNat(8, {b})")).collect();

    // Of the literal, then of the source by its equation.
    let simulated = format!("{src}().elf_file_simulates({p}_size(), {p}_within(), {p}_code(), {homes}, {p}_compiles(), {p}_fits(), {p}_short(),
        top, depth, placed, s, entry, rsp,
        j(sym({p}_written({p}_code(), {p}_compiles())), λ f _ => s.memory.LoadedFrom({p}_size(), f), loaded), deep, args, argv)");
    let (lowered_is, simulates) = if lowered.is_empty() { (String::new(), simulated) } else {
        (format!("// `{symbol}` as `write-elf` read it, a literal; what follows compiles the literal.
{lowered}{lowered_is}"), format!("j(sym({p}_lowered_is()), λ src _ => SimProgram(X86Profile::process({p}_size(), top, depth).linux(), src.denote(args), s),\n        {simulated})"))
    };
    // How the program is the compile: `main` and exit 0 (`Source::compile_of`),
    // or with procedures `main` past their labels, then exit 0, the
    // procedures, the shared exit and the functions
    // (`Source::compile_calls_of`; with functions and no procedure,
    // `Source::compile_functions_of`).
    let (emitted, compiles) = match &calls {
        None => (format!("theorem {p}_emitted(): {src}().main.emit({entry}, {layout}, [], 0).map(λ (c: Compiled) => {finish}) = Some({p}_code()) {{
    j(sym({p}_entry()), λ x _ => {src}().main.emit(x, {layout}, [], 0).map(λ (c: Compiled) => {finish}) = Some({p}_code()),
        cong_fn<Option<Compiled>, Option<Prog>>(λ o => o.map(λ (c: Compiled) => {finish}), {p}_e_0()))
}}
"), format!("{src}().compile_of({LOW}, {homes}, {p}_code(), {p}_allocated(), refl, refl, {p}_emitted(), {p}_laid())")),
        Some(emission::CallsStated { main, names, procedures: procs, after }) => (format!("theorem {p}_emitted(): {src}().main.emit({entry}, {layout}, [], {layout}.deep_label()) = Some(Compiled({main}, {names})) {{
    j(sym({p}_entry()), λ x _ => {src}().main.emit(x, {layout}, [], {layout}.deep_label()) = Some(Compiled({main}, {names})), {p}_e_0())
}}
"), if procedures > 0 {
            format!("{src}().compile_calls_of({LOW}, {homes}, {src}().procedures.head_or(Procedure([], [], Exit(0))), {src}().procedures.tail(), {p}_code(), {main}, {procs}, {names}, {after},
        {p}_allocated(), refl, {p}_emitted(), {p}_procedures(), {p}_deep(), {p}_laid())")
        } else {
            format!("{src}().compile_functions_of({LOW}, {homes}, {src}().functions.head_or(Function([], Call(0, [], 0), 0)), {src}().functions.tail(), {p}_code(), {main}, {procs}, {names}, {after},
        {p}_allocated(), refl, refl, {p}_emitted(), {p}_procedures(), {p}_deep(), {p}_laid())")
        }),
    };
    let mut text = format!("// `{symbol}` compiled into the I/O profile's ELF, as `heather write-elf` writes
// it: generated, and checked by the kernel.
import {root};
{imports}
{lowered_is}
// The words' homes and the loops' sets, as the greedy allocator gave them
// (and, for a source that calls functions, where the function compiler's
// heuristic puts their values).
{homes_def}theorem {p}_layout_is(): {p}_layout() = {src}().layout({LOW}, {homes}) {{ refl }}
// The program: what `{src}().compile` computes.
{code}
// Its emission, and the compile's check of the homes (`{p}_ck_`), a part of
// the statement tree at a time.
{statements}
theorem {p}_allocated(): {src}().allocation_ok({homes}).IsTrue() {{ j(sym({p}_allocation_is()), λ b _ => b.IsTrue(), trivial) }}
{emitted}
// Its layout, by a table of its labels checked a stretch at a time.
{table}{layout}
theorem {p}_holes(): {p}_code().no_holes().IsTrue() {{ trivial }}

// Every block reads only flags it set itself (issues/x86-undefined-flags.md).
theorem {p}_reads(): {p}_code().blocks_read_own().IsTrue() {{ trivial }}

theorem {p}_laid(): {p}_code().laid_out().IsTrue() {{
    {p}_table().laid_out_of({p}_code(), {length}, {p}_checked_{count}(), {p}_holes(), {p}_reads())
}}

theorem {p}_compiles(): {src}().compile({LOW}, {homes}) = Some({p}_code()) {{
    {compiles}
}}

// Its data segment, in whole pages, within the profile's limit; its words,
// buffers and scratch range fit it.
fn {p}_size() → Nat {{ {size} }}
theorem {p}_within(): {p}_size() <= io_data_limit() {{ Nat::leb_sound({p}_size(), io_data_limit(), trivial) }}

theorem {p}_fits(): Layout::of({LOW}, {src}().words, {src}().capacities(), {homes}).size() <= {p}_size() {{
    Nat::leb_sound(Layout::of({LOW}, {src}().words, {src}().capacities(), {homes}).size(), {p}_size(), trivial)
}}

// The bytes, a piece at a time from the last item.
", count = items.len(), layout = labels::layout(p, &offsets, &cuts), emitted = emitted, compiles = compiles);
    text.push_str(&labels::byte_pieces(p, &pieces, &bytes, items.len(), &offsets));
    text.push_str(&format!("
fn {p}_header() → List<BitVec(8)> {{ [{}] }}
theorem {p}_header_is(): {header} = {p}_header() {{ refl }}
{lengths}theorem {p}_length(): {p}_upto_0().len() = {length} {{ {p}_upto_0_len() }}

// The file written: its header, then the code.
fn {p}_file() → List<BitVec(8)> {{ {p}_header() ++ {p}_upto_0() }}

theorem {p}_file_is(): io_elf_file({p}_upto_0(), {p}_size()) = {p}_file() {{
    trans(cong_fn<Nat, List<BitVec(8)>>(λ n => List::append(io_elf_header(BitVec::ofNat(232 + n), BitVec::ofNat((232 + n).shr(8)), {p}_size()), {p}_upto_0()), {p}_length()),
        cong_fn<List<BitVec(8)>, List<BitVec(8)>>(λ h => List::append(h, {p}_upto_0()), {p}_header_is()))
}}

// Whatever names the compile's program, its file is the one written.
theorem {p}_written(program: Prog, compiled: {src}().compile({LOW}, {homes}) = Some(program)):
    io_elf_file(assemble(no_fills(), program, []), {p}_size()) = {p}_file() {{
    let same: ({p}_code() = program) = Option::some_inj({p}_code(), program, trans(sym({p}_compiles()), compiled));
    j(same, λ q _ => io_elf_file(assemble(no_fills(), q, []), {p}_size()) = {p}_file(),
        trans(cong_fn<List<BitVec(8)>, List<BitVec(8)>>(λ x => io_elf_file(x, {p}_size()), {p}_bytes()), {p}_file_is()))
}}

theorem {p}_short(): 232 + assemble(no_fills(), {p}_code(), []).len() <= 65536 {{
    j(sym({p}_bytes()), λ b _ => 232 + b.len() <= 65536,
        j(sym({p}_length()), λ n _ => 232 + n <= 65536, Nat::leb_sound(232 + {length}, 65536, trivial)))
}}

// The process Linux makes of the file written, at its entry with `depth`
// bytes of stack below RSP, enough for the source's words (`main`'s
// frame) and its calls of procedures and of functions, and the command
// line `args` on the stack above,
// simulates `{symbol}`'s tree run with `args` (`Source::elf_file_simulates`,
// from `native_compile_correct`).
theorem {p}_simulates(top, depth: Nat, placed: StackPlaced({p}_size(), top, depth),
    s: MachineState<X86Memory(X86Profile::process({p}_size(), top, depth))>, entry: s.rip = io_entry(), rsp: read_gpr(Rsp, s.gprs).toNat() = top,
    loaded: s.memory.LoadedFrom({p}_size(), {p}_file()), deep: ({src}().depth * (8 * ({src}().words + 7)) + program_calls_room({src}().functions)) + 8 * ({src}().words + 1) <= depth, args: List<List<BitVec(8)>>,
    argv: ArgvAt(X86Profile::process({p}_size(), top, depth).data().above(top), s.memory, read_gpr(Rsp, s.gprs), args)):
    SimProgram(X86Profile::process({p}_size(), top, depth).linux(), {source}.denote(args), s) {{
    {simulates}
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
    refuse_assumptions(&elab, &format!("{p}_certificate"), &unchecked)?;
    write_new(&certificate, text.as_bytes())?;
    std::fs::remove_file(&unchecked).map_err(|e| format!("{}: {e}", unchecked.display()))?;
    write_executable(&output, &file)?;
    println!("{}: {} bytes and a {size}-byte data segment, `{symbol}` compiled into the I/O profile's ELF as the kernel checked it",
        output.display(), file.len());
    println!("certificate: {}", certificate.display());
    Ok(())
}

/// A tool's lowering, read and stated a part at a time (`parts`): the
/// definitions of `{p}_lowered()` and the theorems that the tool lowers to it.
fn tool_parts(elab: &Elaborator, p: &str, symbol: &str, root: &str, imports: &str) -> Result<parts::Stated, String> {
    let numbers = |fork: &Elaborator, module: &str, name: &str| {
        let _row = heather_elab::stats::scope(heather_elab::stats::ScopeKind::Item, module, name);
        function_ir_source::evaluate_numbers(fork, &format!("{module}::{name}")).map_err(|e| format!("`{symbol}` ({name}): {e}"))
    };
    let tool = format!("{symbol}()");
    let shape = format!("{p}_shape");
    let shape_text = format!("import {root};\n{imports}\n{}", parts::shape_text(p, &tool));
    let mut fork = elab.fork();
    fork.elab_module_source(&shape, &shape_text).map_err(|e| e.render(&shape_text))?;
    let plan = parts::plan(p, &numbers(&fork, &shape, &format!("{p}_shape"))?)?;
    let buffers = numbers(&fork, &shape, &format!("{p}_buffers_spelled"))?;
    let trace = format!("{p}_trace");
    let trace_text = format!("import {root};\nimport {shape};\n{imports}\n{}", plan.text);
    fork.elab_module_source(&trace, &trace_text).map_err(|e| e.render(&trace_text))?;
    let traced = numbers(&fork, &trace, &format!("{p}_trace"))?;
    parts::state(p, &tool, plan, &traced, &buffers).map_err(|e| format!("`{symbol}`'s lowering did not read back: {e}"))
}

/// Said of a leaf S4 does not take whole that cannot go a node at a time
/// either (`computes_refusal`, native_compile.hthr).
const NARROW: &str = "; it does not compile a node at a time because a node is not at width 64";

/// The message for a compile `Source::refusal` explains
/// (native_compile.hthr): the statement and the reason it was refused.
fn refused(symbol: &str, why: &[u64]) -> String {
    let [at, kind, reason, first, second] = *why else {
        return format!("`{symbol}` did not compile, and `Source::refusal` names no reason");
    };
    let kind = match kind { 0 => "a computation", 1 => "a call", 2 => "a branch", 3 => "a loop", 4 => "an exit", 6 => "an argument", 7 => "a procedure call", _ => "the program" };
    let reason = match reason {
        0 => format!("a {} region the compiler does not take: a node not at width 64 or reading a word not written before it, \
            a branch on a bit that may not be its word's low bit, a loop not in counted form, or a call over views, \
            which only a function makes (native_structured)",
            ["", "sequence", "compose", "conditional", "call", "loop", "call over views"].get(first as usize).unwrap_or(&"structured")),
        1 => format!("the leaf needs {first} registers, one per input and per node, and the pool holds {second}{NARROW}"),
        2 => format!("the leaf's nodes are not in evaluation order{NARROW}"),
        3 => format!("the leaf writes one of its own inputs{NARROW}"),
        4 => format!("word {first} is past the {second} word slots"),
        5 => format!("an input of width {first}: only words (64) and bits (1) load"),
        6 => format!("S4's lowering refused the leaf{NARROW}"),
        7 => format!("`{}` is not compiled yet (issues/native-compile-stat.md)",
            ["", "", "open", "close", "stat", "fstat"].get(first as usize).unwrap_or(&"the call")),
        8 => format!("buffer {first} does not exist: the source has {second}"),
        9 => "the program's labels did not lay out".into(),
        10 => format!("node {first} of the leaf is not at width 64, and a leaf S4 does not take whole compiles a node at a time only when every node is"),
        11 => format!("S4's lowering refused node {first} of the leaf alone"),
        12 => "the words' homes fail the allocation's check (`Source::allocation_ok`): the allocator's proposal is wrong, a bug in it".into(),
        13 => "a loop whose words live after it include one it moves or counts with, or whose leaves do not compile".into(),
        14 => format!("the call of procedure {first} does not fit: no such procedure, other counts of arguments or results than it takes, more than six, a word past the slots, more saved words than slots, or a result not apart from what is live after it"),
        15 => format!("procedure {first} does not compile (`Procedure::code`)"),
        16 => format!("the call of function {first} does not fit: no such function, another count of arguments than it takes after the homes of the buffers it is lent, more than six registers with them, a word past the slots, or more buffers lent than the source has"),
        17 => "the functions it calls do not link (`Prog::links`): they are not evaluable, they are not placeless (an answer could depend on where a lent buffer lies), no rows of marks hold of them (a function stores through a view it was lent to read, `program_rowed`), or the function compiler refused them with its own placement of their values".into(),
        _ => format!("reason {reason} ({first}, {second})"),
    };
    if kind == "the program" { format!("`{symbol}` is refused: {reason}") }
    else { format!("`{symbol}` is refused at statement {at}, {kind}: {reason}") }
}

/// The homes `Homes::spelled` (native_alloc) reads back as, spelled: how
/// many words have one, each (0 the slot, `k + 1` register `k`), then each
/// loop's set, its length first. With `places`, where the values of the
/// functions the source calls go.
fn homes_literal(numbers: &[u64], places: Option<&str>) -> Option<String> {
    let (&count, rest) = numbers.split_first()?;
    let count = usize::try_from(count).ok().filter(|&c| c <= rest.len())?;
    let of: Vec<String> = rest[..count].iter().map(|&h| if h == 0 { "InSlot".into() } else { format!("InReg({})", h - 1) }).collect();
    let mut sets = Vec::new();
    let mut at = &rest[count..];
    while let Some((&len, more)) = at.split_first() {
        let len = usize::try_from(len).ok().filter(|&l| l <= more.len())?;
        sets.push(format!("[{}]", more[..len].iter().map(u64::to_string).collect::<Vec<_>>().join(", ")));
        at = &more[len..];
    }
    let places = places.map(|places| format!(", {places}")).unwrap_or_default();
    Some(format!("Homes([{}], [{}]{places})", of.join(", "), sets.join(", ")))
}

/// The layout `Source::layout` computes over these homes, as a literal: the
/// word count and the capacities as read (`sizes`), the registers no word
/// lives in (`Homes::leaf_pool`) and those one does (`Homes::registers`),
/// each worked out here from the homes' spelling. The kernel checks it
/// against the computed one, once (`{p}_layout_is`).
fn layout_literal(src: &str, homes: &str, sizes: &[u64], spelled: &[u64]) -> Option<String> {
    const REGISTER_POOL: [&str; 14] = ["Rax", "Rcx", "Rdx", "Rsi", "Rdi", "R8", "R9", "R10", "R11", "R12", "R13", "R14", "R15", "Rbp"];
    const HOME_POOL: [&str; 6] = ["R12", "R13", "R14", "R15", "Rbp", "R10"];
    let (words, capacities) = sizes.split_first()?;
    let (&count, rest) = spelled.split_first()?;
    let of = rest.get(..usize::try_from(count).ok()?)?;
    // `home_register`: a home past the pool reads as the pool's first.
    let used: Vec<&str> = of.iter().filter(|&&h| h != 0).map(|&h| HOME_POOL.get((h - 1) as usize).copied().unwrap_or(HOME_POOL[0])).collect();
    let list = |pool: &[&str], keep: bool| pool.iter().filter(|r| used.contains(r) == keep).copied().collect::<Vec<_>>().join(", ");
    Some(format!("Layout({LOW}, {words}, [{}], {homes}, [{}], [{}], {src}().procedures, {src}().functions)",
        capacities.iter().map(u64::to_string).collect::<Vec<_>>().join(", "), list(&REGISTER_POOL, false), list(&HOME_POOL, true)))
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
        let Some((jump, forward)) = labels::jump(item) else { at += len; continue; };
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
