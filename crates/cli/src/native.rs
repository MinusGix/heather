//! `compile-x86`: a word function and the word functions it calls, compiled
//! by the verified lowering (`lower_program`) and certified by its theorem
//! (`compiled_returns`, issues/function-ir-verified-lowering.md round 4). The
//! certificate is checked before any output is published; the platform ABI
//! around the code is outside the proof.
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::sync::Arc;

use heather_elab::{Elaborator, LintProfile};
use heather_cli::{loader, semantic::SemanticSession};

mod allocator;
mod elf;
mod emission;
mod labels;
mod lowered;
mod parts;
mod support;
use support::SUPPORT;
mod verified;

pub fn run(args: &[String]) -> ExitCode {
    report(compile(args, false))
}

/// `reflect`: a word function's FunctionIR program and the theorem that it
/// evaluates to the function, as a module of their own, checked before it
/// is written; no code. A builder tool names the program to call the
/// function (`native_build`'s `call`, issues/native-build-reflected-helpers.md).
pub fn reflect(args: &[String]) -> ExitCode {
    report(compile(args, true))
}

/// `warm-native`: check the modules `compile-x86` would check for the given
/// sources, the sources themselves included, through the same bundled prefix
/// and into the same stores, and nothing else: no certificate. The order is
/// every source's imports first (each module after its own), then the
/// sources. `--through M` stops after module `M`, so a caller can build a
/// long closure one module per process, each replaying the ones before it
/// under its own CPU rail; `--list` prints that order and `--unbuilt` the
/// modules in it that have no image in the store yet (read from the image
/// headers, `BuildPlan`), one per line, checking nothing.
///
/// Why it exists: a test's first `compile-x86` child over a cold store builds
/// its source and the whole closure under it before its certificate, under
/// one rail. Since the `runtime fn` examples import the generator's closure
/// and run the generator for every function, that is past the rail
/// (issues/master-red-2026-11-06.md), so `scripts/test` warms the store with
/// this first.
pub fn warm(args: &[String]) -> ExitCode {
    report(warm_closure(args))
}

fn warm_closure(args: &[String]) -> Result<(), String> {
    let mut files = Vec::new();
    let mut cache = None;
    let mut through = None;
    let mut list = false;
    let mut unbuilt = false;
    let mut kernel_workers = None;
    let mut search = vec![PathBuf::from("lib/std"), PathBuf::from("lib")];
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "-L" => {
                let value = PathBuf::from(args.next().ok_or("-L needs a path")?);
                if !search.contains(&value) { search.push(value); }
            }
            "--cache-dir" => cache = Some(PathBuf::from(args.next().ok_or("--cache-dir needs a path")?)),
            "--through" => through = Some(args.next().ok_or("--through needs a module name")?.clone()),
            "--list" => list = true,
            "--unbuilt" => unbuilt = true,
            "--kernel-workers" => {
                let value = args.next().ok_or("--kernel-workers needs a count")?;
                kernel_workers = Some(value.parse::<usize>().ok().filter(|&n| n > 0)
                    .ok_or("--kernel-workers needs a positive integer")?);
            }
            _ if arg.starts_with('-') => return Err(format!("unknown option `{arg}`")),
            _ => files.push(PathBuf::from(arg)),
        }
    }
    if files.is_empty() || (!list && cache.is_none()) {
        return Err("usage: heather warm-native <file.hthr>... --cache-dir <dir> [--through <module> | --unbuilt] [-L <dir>]... [--kernel-workers <n>]\n\
                    \x20      heather warm-native <file.hthr>... --list [-L <dir>]...".into());
    }
    // Every file's imports in load order, each module at its first
    // appearance (which follows its own imports), the bundled modules left to
    // the prefix below; then the files themselves. Imports before every root,
    // so `--through` an import never checks a root.
    let bundled: Vec<&str> = SUPPORT.iter().map(|(name, _)| *name).collect();
    let mut closure: Vec<loader::Module> = Vec::new();
    let mut roots: Vec<loader::Module> = Vec::new();
    for file in &files {
        let mut sources = loader::load_providing(file, &search, &bundled).map_err(|e| e.msg)?;
        roots.extend(sources.pop());
        for module in sources {
            if bundled.contains(&module.name.as_str()) || closure.iter().any(|m| m.name == module.name) { continue; }
            closure.push(module);
        }
    }
    for root in roots {
        if !closure.iter().any(|m| m.name == root.name) { closure.push(root); }
    }
    if let Some(name) = &through {
        if !closure.iter().any(|m| &m.name == name) {
            return Err(format!("`{name}` is not in the closure of {}", files.iter().map(|f| f.display().to_string()).collect::<Vec<_>>().join(", ")));
        }
    }
    if list {
        for module in &closure { println!("{}", module.name); }
        return Ok(());
    }
    if unbuilt {
        // The bundled prefix as `compile-x86` checks it, then the rest: a
        // key chains through its imports' interface hashes.
        let mut modules: Vec<loader::Module> = SUPPORT.iter().map(|&(name, src)| loader::Module {
            name: name.into(), path: PathBuf::from(format!("{name}.hthr")), src: src.into(),
        }).collect();
        modules.extend(closure.iter().cloned());
        let plan = heather_cli::semantic::BuildPlan::new(cache.unwrap(), heather_cache::module_image::ImageFreshness::Exact, modules);
        for (i, m) in plan.modules().iter().enumerate() {
            if plan.state(i) != heather_cli::semantic::BuildState::Built && !bundled.contains(&m.name.as_str()) {
                println!("{}", m.name);
            }
        }
        return Ok(());
    }
    let mut elab = Elaborator::with_prelude().map_err(|e| format!("prelude: {e}"))?;
    elab.set_kernel_workers(
        kernel_workers.or_else(heather_elab::kernel_workers_from_env).unwrap_or(heather_elab::DEFAULT_KERNEL_WORKERS),
    );
    // Both halves of the cache, as `compile-x86` opens them, so what is
    // written here is what its replay finds and vouches for.
    let dir = cache.unwrap();
    let (store, rejected) = heather_cache::Cache::open(dir.clone());
    if let Some(msg) = rejected.as_ref().and_then(|r| r.message()) {
        eprintln!("{msg}");
    }
    let store = Arc::new(store);
    elab.set_gate(Arc::clone(&store) as Arc<dyn heather_elab::gate::KernelGate>);
    let mut session = SemanticSession::new(Some(dir));
    for &(name, src) in SUPPORT {
        check_module(&mut elab, &mut session, &loader::Module {
            name: name.into(), path: PathBuf::from(format!("{name}.hthr")), src: src.into(),
        })?;
    }
    for module in &closure {
        check_file(&mut elab, &mut session, module)?;
        if through.as_deref() == Some(module.name.as_str()) { break; }
    }
    // The verdicts too: without them the next replay re-checks every
    // declaration in the kernel, which is most of what warming saves.
    store.save().map_err(|err| format!("cache: could not write verdicts: {err}"))
}

/// `linked-exports <dir> [--check]`: write `<dir>/exports.rs`, the Rust
/// declarations of the exports `<dir>/EXPORTS.tsv` lists, from the table and
/// the signature each `<dir>/<function>.s` states
/// (`heather_cli::linked::exports_rs`), and `<dir>/constants.rs`, the
/// constants `<dir>/CONSTANTS.tsv` lists, from their `def`s
/// (`heather_cli::linked::constants_rs`). `--check` writes nothing and fails
/// where a file on disk is not that. `scripts/linked` runs it after the
/// assembly is rewritten.
pub fn linked_exports(args: &[String]) -> ExitCode {
    report((|| {
        let (dir, check) = match args {
            [dir] => (Path::new(dir), false),
            [dir, flag] if flag == "--check" => (Path::new(dir), true),
            _ => return Err("usage: heather linked-exports <generated dir> [--check]".to_string()),
        };
        let read = |name: &str| std::fs::read_to_string(dir.join(name)).map_err(|e| format!("{}: {e}", dir.join(name).display()));
        let exports = heather_cli::linked::exports_rs(&read("EXPORTS.tsv")?, &|function| read(&format!("{function}.s")))?;
        // A row's module is named from the repository's root, where
        // `scripts/linked` runs this.
        let module = |path: &str| std::fs::read_to_string(path).map_err(|e| format!("{path}: {e}"));
        let constants = heather_cli::linked::constants_rs(&read("CONSTANTS.tsv")?, &module)?;
        let mut stale = Vec::new();
        for (name, text) in [("exports.rs", exports), ("constants.rs", constants)] {
            let path = dir.join(name);
            if std::fs::read_to_string(&path).is_ok_and(|on_disk| on_disk == text) {
                println!("{name}: unchanged");
            } else if check {
                stale.push(format!("{} is stale: run scripts/linked", path.display()));
            } else {
                std::fs::write(&path, text).map_err(|e| format!("{}: {e}", path.display()))?;
                println!("{name}: rewritten");
            }
        }
        if stale.is_empty() { Ok(()) } else { Err(stale.join("\n")) }
    })())
}

/// `write-elf` (`native/elf.rs`).
pub fn write_elf(args: &[String]) -> ExitCode {
    report(elf::write(args))
}

fn report(result: Result<(), String>) -> ExitCode {
    match result {
        Ok(()) => ExitCode::SUCCESS,
        // A diagnostic with its file's snippet (`check_file`) is headed already.
        Err(error) if error.starts_with("error: ") => {
            eprintln!("{error}");
            ExitCode::from(1)
        }
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::from(1)
        }
    }
}

/// A closed bitvector in a generated certificate: its bits written out,
/// least significant first, which the elaborator packs into one kernel
/// vector literal (`Term::VecLit`, docs/bitvector-literal-entry-design.md
/// §3) — a word the kernel reads in one step, where `BitVec::ofNat(width, n)`
/// is a fold it runs a bit at a time.
fn word_literal(width: u32, n: u64) -> String {
    let bits: Vec<&str> = (0..width).map(|i| if i < 64 && n >> i & 1 == 1 { "True" } else { "False" }).collect();
    format!("@bitvec::BitVec::from_bits({width}, [{}])", bits.join(", "))
}

fn symbol_ok(name: &str) -> bool {
    let mut chars = name.chars();
    chars.next().is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

fn compile(args: &[String], program_only: bool) -> Result<(), String> {
    let mut positional = Vec::new();
    let mut output = None;
    let mut cache = None;
    let mut timings = None;
    let mut kernel_workers = None;
    // Other functions of the program to export beside the function: each a
    // module and a function in it.
    let mut entries: Vec<(String, String)> = Vec::new();
    let mut search = vec![PathBuf::from("lib/std"), PathBuf::from("lib")];
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--entry" => {
                let value = args.next().ok_or("--entry needs a function, as `<module>::<function>`")?;
                match value.split_once("::") {
                    Some((module, function)) if symbol_ok(module) && symbol_ok(function) => entries.push((module.to_string(), function.to_string())),
                    _ => return Err(format!("--entry `{value}` is not `<module>::<function>`, the function an ASCII C/assembly identifier")),
                }
            }
            "-o" | "-L" | "--cache-dir" | "--item-timings" | "--timings" => {
                let value = PathBuf::from(args.next().ok_or_else(|| format!("{arg} needs a path"))?);
                match arg.as_str() {
                    "-o" => output = Some(value),
                    "-L" => { if !search.contains(&value) { search.push(value); } }
                    "--item-timings" | "--timings" => timings = Some(value),
                    _ => cache = Some(value),
                }
            }
            "--kernel-workers" => {
                let value = args.next().ok_or("--kernel-workers needs a count")?;
                let n: usize = value
                    .parse()
                    .map_err(|_| "--kernel-workers needs a positive integer".to_string())?;
                if n == 0 {
                    return Err("--kernel-workers needs a positive integer".into());
                }
                kernel_workers = Some(n);
            }
            _ if arg.starts_with('-') => return Err(format!("unknown option `{arg}`")),
            _ => positional.push(arg.as_str()),
        }
    }
    if positional.len() != 2 || output.is_none() {
        return Err(if program_only {
            "usage: heather reflect <file.hthr> <function> -o <output.hthr> [-L <dir>]... [--cache-dir <dir>] [--kernel-workers <n>]"
        } else {
            "usage: heather compile-x86 <file.hthr> <function> -o <output.s> [--entry <module>::<function>]... [-L <dir>]... [--cache-dir <dir>] [--timings <file.tsv>] [--kernel-workers <n>]"
        }.into());
    }
    if program_only && !entries.is_empty() {
        return Err("--entry is compile-x86's: a reflected program is named whole".into());
    }
    let source = Path::new(positional[0]);
    let symbol = positional[1];
    if !symbol_ok(symbol) {
        return Err("function must be an ASCII C/assembly identifier".into());
    }
    let output = output.unwrap();
    if program_only {
        if output.extension().and_then(|s| s.to_str()) != Some("hthr") || output.file_stem().and_then(|s| s.to_str()).is_none_or(|stem| !symbol_ok(stem)) {
            return Err("the program's module must be a .hthr file named by an identifier".into());
        }
    } else if output.extension().and_then(|s| s.to_str()) != Some("s") {
        return Err("assembly output must have the .s extension".into());
    }
    let certificate = output.with_extension("certificate.hthr");
    // What is checked is written first, under a name that is not the
    // published one: a refusal or a build killed mid-check points into a file
    // that exists. Replaced on every build, and removed once the certificate
    // is published.
    let unchecked = certificate.with_extension("unchecked.hthr");
    // Refuse replacement, including symlinks: failed builds cannot leave a
    // previous body looking like the newly checked result.
    for path in [&output, &certificate] {
        if path.symlink_metadata().is_ok() {
            return Err(format!("output already exists: {}", path.display()));
        }
    }
    // A program may import the bundled proof library by its bundled names,
    // which need not be files on the search path.
    let bundled: Vec<&str> = SUPPORT.iter().map(|(name, _)| *name).collect();
    let sources = loader::load_providing(source, &search, &bundled).map_err(|e| e.msg)?;
    let root_name = sources.last().ok_or("empty source closure")?.name.clone();
    let mut elab = Elaborator::with_prelude().map_err(|e| format!("prelude: {e}"))?;
    // The deferred kernel gate (`docs/parallel-kernel-gate-design.md`). Set
    // after the prelude, which is milliseconds and is checked serially; every
    // module from here on joins before it is accepted, and the certificate —
    // thousands of independent generated theorems — is the point.
    elab.set_kernel_workers(
        kernel_workers.or_else(heather_elab::kernel_workers_from_env).unwrap_or(heather_elab::DEFAULT_KERNEL_WORKERS),
    );
    // Observation only: the collector changes no judgment, no fuel, and no
    // cache entry, and stays off unless `--item-timings` names a file. Turning
    // it on here rather than at the certificate separates a module actually
    // elaborated (a cache miss, or the root source) from the generated
    // certificate by the `module` column.
    if let Some(path) = &timings {
        elab.enable_item_timings();
        // Live from here: a build killed at the CPU rail leaves the rows of
        // every scope that closed and, beside them, the ones still open.
        heather_elab::stats::live_table(path).map_err(|e| format!("{}: {e}", path.display()))?;
        // The same opt-in also turns on the value-machine counters (the
        // TSV's last four columns) and, under the `value-metrics` feature,
        // the typing seam's conversion-miss sampler with its item column
        // (issues/conv-miss-sampler-item-attribution.md), written beside
        // the table. Without the feature the report is empty and no file
        // is written.
        //
        // Not with a worker pool, though: the collector is an `Rc` this
        // elaborator owns and the profiled checker entry points want, so
        // having one pins the kernel gate to this thread
        // (`docs/parallel-kernel-gate-design.md` §4). Asking for both used to
        // mean silently getting neither — the serial gate, wearing the
        // parallel flag — so the flag wins and the four value-machine columns
        // go empty, out loud.
        if elab.kernel_workers() == 1 {
            elab.enable_value_metrics();
        } else {
            eprintln!(
                "--kernel-workers {}: value-machine columns off (the collector is per-elaborator)",
                elab.kernel_workers(),
            );
        }
    }
    // The run row these commands never wrote: `heather check` has opened a
    // `Run` scope since the layer landed, so the two native commands reported
    // per-declaration and per-module rows with nothing to total them against
    // (`issues/perf-instrumentation-consolidation.md`, 2026-09-11).
    let run_scope = timings
        .as_ref()
        .map(|_| heather_elab::stats::scope(heather_elab::stats::ScopeKind::Run, "", ""));
    // `--cache-dir` names both halves of the cache `heather check --cache`
    // keeps under one directory: the semantic image store the session reads,
    // and the declaration-verdict store (docs/cache-v1-design.md §6) that
    // vouches for a replayed image's stored definitions. Until 2026-09-17
    // only the first half was wired here, so every build re-kernel-checked
    // all of the bundled proof library's bindings before it looked at the
    // user's function — ~25 s of a debug-profile build, and ~150 of the
    // suite's ~220 CPU-s across the four native integration binaries.
    //
    // Since 2026-09-23 the gate stays on for the user's sources and the
    // generated certificate too (it was sealed to `NoGate` before them). The
    // generator and the elaborator still run on every build — only the
    // kernel's re-check of a term it already accepted is skipped, and the
    // key is the elaborated term with its dependencies' interfaces
    // (docs/cache-v1-design.md §5), so any change to what the generator or
    // elaborator emits is a new key and a real check, and a changed kernel
    // discards the store.
    let verdicts = cache.as_ref().map(|dir| {
        let (store, rejected) = heather_cache::Cache::open(dir.clone());
        if let Some(msg) = rejected.as_ref().and_then(|r| r.message()) {
            eprintln!("{msg}");
        }
        Arc::new(store)
    });
    // Without a directory, the verdicts of this process alone
    // (`Cache::in_process`): a module loaded into a second world is not
    // checked a second time.
    let gate = verdicts.clone().unwrap_or_else(|| Arc::new(heather_cache::Cache::in_process()));
    elab.set_gate(gate as Arc<dyn heather_elab::gate::KernelGate>);
    let mut session = SemanticSession::new(cache);
    for &(name, src) in SUPPORT {
        check_module(&mut elab, &mut session, &loader::Module {
            name: name.into(), path: PathBuf::from(format!("{name}.hthr")), src: src.into(),
        })?;
    }
    for module in &sources {
        if let Some((_, bundled)) = SUPPORT.iter().find(|(name, _)| *name == module.name) {
            if module.src != *bundled {
                return Err(format!("source module `{}` differs from the compiler's bundled proof library", module.name));
            }
        } else {
            check_file(&mut elab, &mut session, module)?;
        }
    }
    let prefix = format!("{symbol}_native");
    let source_name = format!("{root_name}::{symbol}");
    if program_only {
        let program = verified::reflect(&elab, &source_name)?;
        // The program and its agreement, a module checked as any other
        // before it is written. Untrusted, as every generated text is: the
        // kernel checks that the program evaluates to the function.
        let module = output.file_stem().and_then(|s| s.to_str()).unwrap_or_default().to_string();
        let mut text = format!("// Generated by `heather reflect {} {symbol}`: `{root_name}::{symbol}` reflected into a\n\
            // FunctionIR program, `{prefix}_program()`, its function {} the source function\n\
            // (`{prefix}_agrees`). Regenerate rather than edit.\n", positional[0], program.root);
        for name in verified::PROGRAM_IMPORTS { text.push_str(&format!("import {name};\n")); }
        text.push_str(&verified::owner_imports(&program));
        text.push_str(&verified::program_text(&prefix, &program));
        text.push_str(&verified::agreement_text(&prefix, &program));
        // Laid out as `heather fmt` lays out the library it is checked into.
        let text = heather_syntax::fmt::format_source(&text);
        let unchecked = output.with_extension("unchecked.hthr");
        if unchecked.symlink_metadata().is_ok() {
            std::fs::remove_file(&unchecked).map_err(|e| format!("{}: {e}", unchecked.display()))?;
        }
        write_new(&unchecked, text.as_bytes())?;
        let checked = check_file(&mut elab, &mut session, &loader::Module { name: module, path: unchecked.clone(), src: text.clone() });
        drop(run_scope);
        if let Some(store) = verdicts && let Err(err) = store.save() {
            eprintln!("cache: could not write verdicts: {err}");
        }
        checked?;
        write_new(&output, text.as_bytes())?;
        std::fs::remove_file(&unchecked).map_err(|e| format!("{}: {e}", unchecked.display()))?;
        println!("{}: `{symbol}` as a FunctionIR program of {} functions, its agreement checked", output.display(), program.functions.len());
        return Ok(());
    }
    // A function runs only when it is marked: `runtime fn f` publishes its
    // program and the program's agreement (from its `Compile` instance and
    // its callees', docs/runtime-fn-setups-design.md §16.9), loops
    // included (§16.11). The Rust reflector stays only for what the default
    // setup does not compile yet, tests through `Bool` helpers; anything
    // else unmarked is refused, naming the marker.
    let published = |member: &str| elab.qualified_global(&format!("{source_name}::{member}")).is_some();
    let mut shape = if published("runs_over") {
        // A function that stores into its span publishes its run at every
        // file: the word it answers and the span as it leaves it
        // (docs/native-library-exports-design.md §7).
        verified::runtime_shape(&elab, &prefix, &root_name, &source_name, verified::Spans::Written)?
    } else if published("compile") {
        // One that reads spans publishes its agreement at every file.
        let spans = if published("agrees_over") { verified::Spans::Read } else { verified::Spans::None };
        verified::runtime_shape(&elab, &prefix, &root_name, &source_name, spans)?
    } else {
        let program = verified::reflect(&elab, &source_name)?;
        if !program.functions.iter().any(|function| function.helped) {
            return Err(format!("`{symbol}` is not a runtime fn: mark it `runtime fn {symbol}`, and the functions it calls, with `import runtime;` \
                (docs/runtime-fn-setups-design.md §16.9)"));
        }
        verified::Shape::reflected(&prefix, &program)
    };
    // The program's other functions to export: one program, emitted once,
    // with a label and a `_returns` for each
    // (docs/native-library-exports-design.md §6.3).
    if !entries.is_empty() {
        if shape.marks.is_none() && !published("names") {
            return Err(format!("`{symbol}` publishes no program of named functions: an entry is another function of a `runtime fn`'s program"));
        }
        for (module, function) in &entries {
            if function == symbol { return Err(format!("--entry `{module}::{function}` is the function compiled")); }
            // The file's own label for the start of the program.
            if *function == format!("{symbol}_program") { return Err(format!("--entry `{module}::{function}` has the name of the program's label")); }
            if elab.qualified_global(&format!("{module}::{function}")).is_none() {
                return Err(format!("--entry `{module}::{function}` is no function `{symbol}`'s module reaches"));
            }
        }
        verified::runtime_entries(&elab, &prefix, &root_name, &source_name, &mut shape, &entries)?;
    }
    // What the code takes, as the certificate's `_returns` states it: a span
    // is an address and a length, the spans first; and the stack its premise
    // asks for below the return address.
    // A span the program stores into is one its caller lends to write.
    let spans = shape.lent.as_ref().map_or(0, |counts| counts[shape.root] as usize);
    let written = |span: usize| shape.marks.as_ref().is_some_and(|marks| marks.get(span) == Some(&true));
    let mut kinds: Vec<_> = (0..spans).map(|span| if written(span) { heather_cli::linked::Kind::SpanMut } else { heather_cli::linked::Kind::Span }).collect();
    kinds.resize(shape.arity - spans, heather_cli::linked::Kind::Word);
    let signature = heather_cli::linked::Signature { kinds, stack: 120 * (shape.root as u64 + 1) };
    // A program in the fragment that the lowering then refuses is a defect
    // of the lowering or its planner, never a reason to certify it another
    // way.
    let compiled = verified::compile(&elab, &prefix, &format!("{prefix}_certificate"), &shape)
        .map_err(|why| format!("verified lowering: {why}"))?;
    let proof = compiled.text;
    eprintln!("checking the lowering, source agreement, bytes and return certificate in {}", unchecked.display());
    let certificate_module = format!("{prefix}_certificate");
    // The certificate is a module like any other, and goes through the
    // session like one: a repeated build at the same compiler and sources
    // replays its image instead of re-elaborating it, a build after an edit
    // replays the unchanged declarations from the previous image's slices,
    // and `check_module`
    // opens the module row that totals them. A miss elaborates on the
    // journalled delta path, which costs what `elab_module_source` does since
    // a clone stopped copying the journal
    // (issues/check-module-delta-certificate-cost.md).
    if unchecked.symlink_metadata().is_ok() {
        std::fs::remove_file(&unchecked).map_err(|e| format!("{}: {e}", unchecked.display()))?;
    }
    write_new(&unchecked, proof.as_bytes())?;
    let checked = check_file(&mut elab, &mut session, &loader::Module {
        name: certificate_module.clone(),
        path: unchecked.clone(),
        src: proof.clone(),
    });
    drop(run_scope);
    // Written whether or not the certificate was accepted: every entry is a
    // declaration the kernel did accept.
    if let Some(store) = verdicts {
        if let Err(err) = store.save() {
            eprintln!("cache: could not write verdicts: {err}");
        }
    }
    // A refused certificate is the case worth attributing, so the table is
    // written before the failure is reported.
    if let Some(path) = &timings {
        heather_elab::stats::dump(
            &heather_elab::stats::Dest::File(path.clone()),
            &elab.take_item_timings(),
        )
        .map_err(|e| format!("{}: {e}", path.display()))?;
        if let Some(report) = elab.value_conv_miss_report().filter(|r| !r.is_empty()) {
            let beside = path.with_extension("conv-miss.txt");
            std::fs::write(&beside, report).map_err(|e| format!("{}: {e}", beside.display()))?;
            eprintln!("conversion-miss report in {}", beside.display());
        }
    }
    checked?;
    write_new(&certificate, proof.as_bytes())?;
    std::fs::remove_file(&unchecked).map_err(|e| format!("{}: {e}", unchecked.display()))?;
    // The root, then the program's other entries: each a function of words.
    let mut exported = vec![(symbol.to_string(), signature, compiled.entry)];
    for (entry, at) in shape.entries.iter().zip(&compiled.entries) {
        let signature = heather_cli::linked::Signature { kinds: vec![heather_cli::linked::Kind::Word; entry.arity], stack: 120 * (entry.index as u64 + 1) };
        exported.push((entry.symbol.clone(), signature, *at));
    }
    write_new(&output, program_assembly(&exported, &compiled.bytes).as_bytes())?;
    println!("{}: {} certified program bytes, `{symbol}` at offset {}, its RET included", output.display(), compiled.bytes.len(), compiled.entry);
    for (entry, _, at) in &exported[1..] { println!("  `{entry}`, a function of the same program, at offset {at}"); }
    println!("certificate: {}", certificate.display());
    Ok(())
}

fn check_module(elab: &mut Elaborator, session: &mut SemanticSession, module: &loader::Module) -> Result<(), String> {
    let outcome = session.check(elab, module, LintProfile::Default);
    for notice in outcome.notices { eprintln!("{notice}"); }
    if outcome.errors.is_empty() { Ok(()) } else {
        Err(outcome.errors.iter().map(|e| e.render(&module.src)).collect::<Vec<_>>().join("\n"))
    }
}

/// [`check_module`] for a module that is a file on disk: its diagnostics
/// name the file, with the offending line quoted.
fn check_file(elab: &mut Elaborator, session: &mut SemanticSession, module: &loader::Module) -> Result<(), String> {
    let outcome = session.check(elab, module, module.lint_profile());
    for notice in outcome.notices { eprintln!("{notice}"); }
    if outcome.errors.is_empty() { Ok(()) } else {
        let file = module.path.display().to_string();
        Err(outcome.errors.iter().map(|e| e.render_snippet(&module.src, &file)).collect::<Vec<_>>().join("\n"))
    }
}

fn write_new(path: &Path, contents: &[u8]) -> Result<(), String> {
    use std::io::Write;
    let mut file = std::fs::OpenOptions::new().write(true).create_new(true).open(path)
        .map_err(|e| format!("{}: {e}", path.display()))?;
    file.write_all(contents).map_err(|e| format!("{}: {e}", path.display()))
}

// A whole program from the verified lowering: every function's code, its
// own frames and RETs included, each exported symbol at its function's
// label: the program's root first in `exported`, then any other of its
// functions exported beside it. What each takes is stated first, for
// whoever declares it (`heather_cli::linked`).
fn program_assembly(exported: &[(String, heather_cli::linked::Signature, usize)], bytes: &[u8]) -> String {
    let root = &exported[0].0;
    let mut out = String::from("# Heather certified program (function_ir_compile); the platform ABI around it is outside the proof.\n");
    for (symbol, signature, _) in exported { out.push_str(&heather_cli::linked::header(symbol, signature)); }
    out.push_str(".text\n");
    for (symbol, _, _) in exported { writeln!(out, ".globl {symbol}\n.type {symbol}, @function").unwrap(); }
    writeln!(out, "{root}_program:").unwrap();
    // The code up to the first label, then each label and the code from it
    // to the next. A program whose first function is exported has nothing
    // before that label, and each label is written once: an assembler
    // refuses a second definition.
    let mut labels: Vec<(usize, &str)> = exported.iter().map(|(symbol, _, entry)| (*entry, symbol.as_str())).collect();
    labels.sort();
    let mut from = 0;
    for (at, label) in labels.iter().map(|(at, label)| (*at, Some(*label))).chain([(bytes.len(), None)]) {
        for line in bytes[from..at].chunks(12) {
            writeln!(out, "    .byte {}", line.iter().map(|b| format!("0x{b:02x}")).collect::<Vec<_>>().join(", ")).unwrap();
        }
        if let Some(label) = label { writeln!(out, "{label}:").unwrap(); }
        from = at;
    }
    for (symbol, _, _) in exported { writeln!(out, ".size {symbol}, .-{symbol}").unwrap(); }
    out.push_str(".section .note.GNU-stack,\"\",@progbits\n");
    out
}

// The bundled proof library, checked through the cache directory the native
// tests share (`target/native-test-images`): `scripts/test`'s native warm-up
// runs this alone, so the `compile-x86` children replay the library instead
// of each elaborating it. Every replayed declaration is still kernel-checked.
//
// The gate is a verdict store with no file behind it: every declaration
// still faces the kernel once in this process, and a module's image moved
// into another module's world (where two import chains meet, such as grind's
// and the x86 model's) is vouched for by the verdicts this process recorded,
// as `warm-native` and `compile-x86` are by theirs. Without it each such
// world rechecked the whole of the moved chain in the kernel
// (`issues/grind-closure-cost.md`).
#[cfg(test)]
mod tests {
    use super::*;

    // The exported label is defined exactly once, wherever the entry
    // function falls: at the start (a function that calls nothing; the
    // label was written twice there until `crates/linked` assembled one)
    // and after its callees.
    #[test]
    fn the_exported_label_is_defined_once() {
        let bytes: Vec<u8> = (0..30).collect();
        for entry in [0, 13, 24] {
            let signature = heather_cli::linked::Signature { kinds: vec![heather_cli::linked::Kind::Word], stack: 72 };
            let text = program_assembly(&[("f".to_string(), signature.clone(), entry)], &bytes);
            assert_eq!(heather_cli::linked::Signature::read(&text, "f"), Ok(signature));
            let lines: Vec<&str> = text.lines().collect();
            assert_eq!(lines.iter().filter(|line| **line == "f:").count(), 1, "entry {entry}:\n{text}");
            let label = lines.iter().position(|line| *line == "f:").unwrap();
            let count = |lines: &[&str]| lines.iter().filter(|line| line.trim_start().starts_with(".byte"))
                .map(|line| line.split(',').count()).sum::<usize>();
            assert_eq!(count(&lines[..label]), entry, "bytes before the label, entry {entry}");
            assert_eq!(count(&lines[label..]), bytes.len() - entry, "bytes from the label, entry {entry}");
        }
    }

    // A program with several entries: each symbol is global, stated with
    // its own signature, and defined once at its own offset, whatever order
    // the entries are named in; the bytes are the program's, in order.
    #[test]
    fn every_entry_has_its_label() {
        use heather_cli::linked::{Kind, Signature};
        let bytes: Vec<u8> = (0..40).collect();
        let exported = [("root".to_string(), Signature { kinds: vec![Kind::Span, Kind::Word], stack: 216 }, 25),
            ("late".to_string(), Signature { kinds: vec![Kind::Word], stack: 144 }, 13),
            ("first".to_string(), Signature { kinds: vec![], stack: 72 }, 0)];
        let text = program_assembly(&exported, &bytes);
        let lines: Vec<&str> = text.lines().collect();
        let count = |lines: &[&str]| lines.iter().filter(|line| line.trim_start().starts_with(".byte"))
            .map(|line| line.split(',').count()).sum::<usize>();
        for (symbol, signature, entry) in &exported {
            assert_eq!(Signature::read(&text, symbol).as_ref(), Ok(signature), "{symbol}");
            assert_eq!(lines.iter().filter(|line| **line == format!(".globl {symbol}")).count(), 1, "{symbol}:\n{text}");
            let label = format!("{symbol}:");
            assert_eq!(lines.iter().filter(|line| **line == label).count(), 1, "{symbol}:\n{text}");
            let at = lines.iter().position(|line| *line == label).unwrap();
            assert_eq!(count(&lines[..at]), *entry, "bytes before `{symbol}`");
        }
        assert_eq!(lines.iter().filter(|line| **line == "root_program:").count(), 1, "{text}");
        let stated: Vec<u8> = lines.iter().filter_map(|line| line.trim_start().strip_prefix(".byte "))
            .flat_map(|line| line.split(", ").map(|byte| u8::from_str_radix(byte.trim_start_matches("0x"), 16).unwrap())).collect();
        assert_eq!(stated, bytes);
    }

    #[test]
    fn the_bundled_library_checks() {
        let mut elab = Elaborator::with_prelude().unwrap();
        let verdicts = heather_cache::Cache::in_process();
        elab.set_gate(Arc::new(verdicts) as Arc<dyn heather_elab::gate::KernelGate>);
        let mut session = SemanticSession::new(Some(heather_cli::showcase::native_test_images()));
        for &(name, src) in SUPPORT {
            check_module(&mut elab, &mut session, &loader::Module {
                name: name.into(), path: PathBuf::from(format!("{name}.hthr")), src: src.into(),
            }).unwrap_or_else(|error| panic!("{name}: {error}"));
        }
    }
}
