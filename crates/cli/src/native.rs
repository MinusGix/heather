//! `compile-x86`: a word function and the word functions it calls, compiled
//! by the verified lowering (`lower_program`) and certified by its theorem
//! (`compiled_returns`, issues/function-ir-verified-lowering.md round 4). The
//! certificate is checked before any output is published; the platform ABI
//! around the code is outside the proof.
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::sync::Arc as Rc;

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
    let store = Rc::new(store);
    elab.set_gate(Rc::clone(&store) as Rc<dyn heather_elab::gate::KernelGate>);
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
    let mut search = vec![PathBuf::from("lib/std"), PathBuf::from("lib")];
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
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
            "usage: heather compile-x86 <file.hthr> <function> -o <output.s> [-L <dir>]... [--cache-dir <dir>] [--timings <file.tsv>] [--kernel-workers <n>]"
        }.into());
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
        Rc::new(store)
    });
    if let Some(store) = &verdicts {
        elab.set_gate(Rc::clone(store) as Rc<dyn heather_elab::gate::KernelGate>);
    }
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
    // its callees', docs/runtime-fn-setups-design.md §16.9). The Rust
    // reflector stays only for what the default setup does not compile yet,
    // loops and tests through `Bool` helpers; anything else unmarked is
    // refused, naming the marker.
    let shape = if elab.qualified_global(&format!("{source_name}::compile")).is_some() {
        verified::runtime_shape(&elab, &prefix, &root_name, &source_name)?
    } else {
        let program = verified::reflect(&elab, &source_name)?;
        if !program.functions.iter().any(|function| function.looped.is_some() || function.helped) {
            return Err(format!("`{symbol}` is not a runtime fn: mark it `runtime fn {symbol}`, and the functions it calls, with `import runtime;` \
                (docs/runtime-fn-setups-design.md §16.9)"));
        }
        verified::Shape::reflected(&prefix, &program)
    };
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
    write_new(&output, program_assembly(symbol, &compiled.bytes, compiled.entry).as_bytes())?;
    println!("{}: {} certified program bytes, `{symbol}` at offset {}, its RET included", output.display(), compiled.bytes.len(), compiled.entry);
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
// own frames and RETs included, the exported symbol at its function's label.
fn program_assembly(symbol: &str, bytes: &[u8], entry: usize) -> String {
    let mut out = format!("# Heather certified program (function_ir_compile); the platform ABI around it is outside the proof.\n.text\n.globl {symbol}\n.type {symbol}, @function\n{symbol}_program:\n");
    for (start, chunk) in [(0, &bytes[..entry]), (entry, &bytes[entry..])] {
        if start == entry { writeln!(out, "{symbol}:").unwrap(); }
        for line in chunk.chunks(12) {
            writeln!(out, "    .byte {}", line.iter().map(|b| format!("0x{b:02x}")).collect::<Vec<_>>().join(", ")).unwrap();
        }
    }
    writeln!(out, ".size {symbol}, .-{symbol}\n.section .note.GNU-stack,\"\",@progbits").unwrap();
    out
}

// The bundled proof library, checked through the cache directory the native
// tests share (`target/native-test-images`): `scripts/test`'s native warm-up
// runs this alone, so the `compile-x86` children replay the library instead
// of each elaborating it. Every replayed declaration is still kernel-checked.
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_bundled_library_checks() {
        let mut elab = Elaborator::with_prelude().unwrap();
        let mut session = SemanticSession::new(Some(heather_cli::showcase::native_test_images()));
        for &(name, src) in SUPPORT {
            check_module(&mut elab, &mut session, &loader::Module {
                name: name.into(), path: PathBuf::from(format!("{name}.hthr")), src: src.into(),
            }).unwrap_or_else(|error| panic!("{name}: {error}"));
        }
    }
}
