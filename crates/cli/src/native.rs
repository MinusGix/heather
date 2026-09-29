//! First native export boundary: a checked straight-line body plus an explicit
//! unproved SysV return shim. The Rust encoder is checked by a literal-byte
//! equality in the generated certificate before any output is published.
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::sync::Arc as Rc;

use heather_elab::{Elaborator, LintProfile, function_ir_source};
use heather_elab::function_ir_x86_lower::{Gpr, encode_instructions as encode, encode_structured, register_code as reg};
#[cfg(test)]
use heather_elab::function_ir_x86_lower::{Instruction, LowByteGpr};
use heather_elab::heather_emit::{Block, Declaration, Expr, Module};
use heather_cli::{loader, semantic::SemanticSession};

mod elf;
mod calls;
mod order;
mod read_loop;
mod read_fields;

mod support;
use support::SUPPORT;

pub fn run(args: &[String]) -> ExitCode {
    report(on_deep_stack(args, false))
}

pub fn build(args: &[String]) -> ExitCode {
    report(on_deep_stack(args, true))
}

/// The main thread's stack is the platform's (8 MiB on Linux), and replaying a
/// certificate's image decodes each term recursively, to the image format's
/// depth budget. A program's published byte tree is a right spine hundreds of
/// appends deep, and in the test profile its decoding overflowed that stack
/// (issues/module-image-decode-depth-vs-stack.md). The whole build runs on a
/// thread whose stack is sized for the budget.
const COMPILE_STACK_BYTES: usize = 256 << 20;

fn on_deep_stack(args: &[String], executable: bool) -> Result<(), String> {
    let args = args.to_vec();
    std::thread::Builder::new().name("build-x86".into()).stack_size(COMPILE_STACK_BYTES)
        .spawn(move || compile(&args, executable)).map_err(|e| format!("cannot start the build thread: {e}"))?
        .join().unwrap_or_else(|panic| std::panic::resume_unwind(panic))
}

fn report(result: Result<(), String>) -> ExitCode {
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::from(1)
        }
    }
}

fn symbol_ok(name: &str) -> bool {
    let mut chars = name.chars();
    chars.next().is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

fn compile(args: &[String], executable: bool) -> Result<(), String> {
    let mut positional = Vec::new();
    let mut output = None;
    let mut inputs = Vec::new();
    let mut cache = None;
    let mut callee = None;
    let mut callable_caller = false;
    let mut read_loop = false;
    let mut print = false;
    let mut fields = false;
    let (mut needle, mut advance, mut computes, mut folds) = (None, None, None, None);
    let mut specs: Vec<String> = Vec::new();
    let mut timings = None;
    let mut kernel_workers = None;
    let mut search = vec![PathBuf::from("lib/std"), PathBuf::from("lib")];
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--callable-caller" if executable => { callable_caller = true; }
            "--read-loop" if executable => { read_loop = true; }
            "--print" if executable => { print = true; }
            "--fields" if executable => { fields = true; }
            "--needle" | "--advance" | "--spec" | "--computes" | "--folds" if executable => {
                let value = args.next().ok_or_else(|| format!("{arg} needs a value"))?.clone();
                match arg.as_str() {
                    "--needle" => needle = Some(u8::try_from(elf::parse_argument(&value)?).map_err(|_| "--needle must be a byte".to_string())?),
                    "--advance" => advance = Some(value),
                    "--spec" => specs.push(value),
                    "--folds" => folds = Some(value),
                    _ => computes = Some(value),
                }
            }
            "--callee" if executable => {
                callee = Some(args.next().ok_or("--callee needs a source function name")?.clone());
            }
            "--arg" if executable => {
                inputs.push(elf::parse_argument(args.next().ok_or("--arg needs an unsigned integer")?)?);
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
    if read_loop {
        if !inputs.is_empty() || callee.is_some() { return Err("--read-loop takes its input from stdin: no --arg or --callee".into()); }
        if needle.is_none() || advance.is_none() || specs.is_empty() || computes.is_none() || folds.is_none() {
            return Err("--read-loop needs --needle <byte>, --advance <theorem>, --spec <function>, --computes <theorem> and --folds <theorem>".into());
        }
        if print && fields { return Err("--print and --fields are two outputs: give one".into()); }
        if fields && specs.len() != 3 { return Err("--fields prints three counts: give --spec three times, in the order printed".into()); }
        if !fields && specs.len() != 1 { return Err("--read-loop takes one --spec (three with --fields)".into()); }
    } else if print || fields || needle.is_some() || advance.is_some() || !specs.is_empty() || computes.is_some() || folds.is_some() {
        return Err("--needle, --advance, --spec, --computes, --folds, --print and --fields belong to --read-loop".into());
    } else if executable && inputs.len() != 2 {
        return Err("build-x86 needs exactly two --arg values for the source function".into());
    }
    if positional.len() != 2 || output.is_none() {
        if executable {
            return Err("usage: heather build-x86 <file.hthr> <function> (--arg <u64> --arg <u64> [--callee <function> [--callable-caller]] | --read-loop --needle <byte> --advance <theorem> --spec <function> --computes <theorem> --folds <theorem> [--print | --fields]) -o <executable> [-L <dir>]... [--cache-dir <dir>] [--timings <file.tsv>] [--kernel-workers <n>]".into());
        }
        return Err("usage: heather compile-x86 <file.hthr> <function> -o <output.s> [-L <dir>]... [--cache-dir <dir>] [--timings <file.tsv>] [--kernel-workers <n>]".into());
    }
    let source = Path::new(positional[0]);
    let symbol = positional[1];
    if !symbol_ok(symbol) {
        return Err("function must be an ASCII C/assembly identifier".into());
    }
    let output = output.unwrap();
    if !executable && output.extension().and_then(|s| s.to_str()) != Some("s") {
        return Err("assembly output must have the .s extension".into());
    }
    if callable_caller && callee.is_none() { return Err("--callable-caller requires --callee".into()); }
    let certificate = if executable {
        let mut name = output.as_os_str().to_os_string();
        name.push(".certificate.hthr");
        PathBuf::from(name)
    } else { output.with_extension("certificate.hthr") };
    // Refuse replacement, including symlinks: failed builds cannot leave a
    // previous executable body looking like the newly checked result.
    for path in [&output, &certificate] {
        if path.symlink_metadata().is_ok() {
            return Err(format!("output already exists: {}", path.display()));
        }
    }
    let bundle: Vec<(&str, &str)> = SUPPORT.iter().chain(if read_loop { read_loop::SUPPORT } else { &[] })
        .chain(if print { read_loop::PRINT_SUPPORT } else { &[] })
        .chain(if fields { read_fields::SUPPORT } else { &[] }).copied().collect();
    // A program may import the bundled proof library by its bundled names,
    // which need not be files on the search path.
    let bundled: Vec<&str> = bundle.iter().map(|(name, _)| *name).collect();
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
    if timings.is_some() {
        elab.enable_item_timings();
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
    // discards the store. A second build of the same function with other
    // `--arg`s re-checks only the declarations the inputs reach.
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
    for &(name, src) in &bundle {
        check_module(&mut elab, &mut session, &loader::Module {
            name: name.into(), path: PathBuf::from(format!("{name}.hthr")), src: src.into(),
        })?;
    }
    // The formatter's three certificates, each a module of its own. They
    // depend on the profile, not the program, so their names do not name the
    // program, and they are checked before any of its modules: an image's
    // cache key covers every module checked before it, so a second program
    // replays them instead of re-proving them.
    let format = if read_loop && (print || fields) {
        let parts = if fields { read_fields::generate_format(&elab, read_fields::FORMAT_PREFIX)? }
            else { read_loop::generate_format(&elab, read_loop::FORMAT_PREFIX)? };
        for part in &parts {
            check_module(&mut elab, &mut session, &loader::Module {
                name: part.module.clone(), path: PathBuf::from(format!("{}.hthr", part.module)), src: part.text.clone(),
            })?;
        }
        Some(parts)
    } else { None };
    for module in &sources {
        if let Some((_, bundled)) = bundle.iter().find(|(name, _)| *name == module.name) {
            if module.src != *bundled {
                return Err(format!("source module `{}` differs from the compiler's bundled proof library", module.name));
            }
        } else {
            check_module(&mut elab, &mut session, module)?;
        }
    }
    let prefix = format!("{symbol}_native");
    let mut proof = Module::default();
    for name in ["function_ir_x86_support", "function_ir", "x86_64", "x86_64_block",
        "x86_64_control_block", "x86_64_control_flow", "x86_64_structured_block", "bitvec", "list", "logic", "elf64", "linux_x86_64_entry", "x86_64_fetch", "x86_64_fetch_block", "elf64_load", "linux_x86_64_fetch", "bool", "option", "nat"] {
        proof.raw(format!("import {name};"));
    }
    // The same certificate at other inputs, generated only to tell which
    // declarations depend on the inputs (`native/order.rs`); never checked.
    // A probe that fails to generate just leaves the order alone.
    let input = |i: usize| inputs.get(i).copied().unwrap_or(0);
    let probe_inputs = [[!input(0), !input(1)],
        [input(0).wrapping_add(0x9e37_79b9_7f4a_7c15), input(1).wrapping_add(0x6a09_e667_f3bc_c909)]];
    let mut probes = Some(Vec::new());
    let (image, body_bytes) = if read_loop && fields {
        let [s0, s1, s2] = [&specs[0], &specs[1], &specs[2]].map(|s| s.as_str());
        let program = read_fields::Program { root: &root_name, source: symbol, advance: advance.as_deref().unwrap(),
            needle: needle.unwrap(), specs: [s0, s1, s2], computes: computes.as_deref().unwrap(), folds: folds.as_deref().unwrap() };
        let context = format!("{prefix}_context");
        check_module(&mut elab, &mut session, &loader::Module {
            name: context.clone(), path: PathBuf::from(format!("{context}.hthr")), src: read_fields::context(&program),
        })?;
        let record = read_fields::record(&elab, &context, &program)?;
        let emission = read_fields::generate_loop(&elab, &context, &prefix, &program, &record)?;
        let pieces = format!("{prefix}_pieces");
        check_module(&mut elab, &mut session, &loader::Module {
            name: pieces.clone(), path: PathBuf::from(format!("{pieces}.hthr")), src: emission.pieces.clone(),
        })?;
        proof = Module::default();
        for name in read_loop::IMPORTS.iter().chain(read_fields::IMPORTS).filter(|name| !emission.text.contains(&format!("import {name};"))) {
            proof.raw(format!("import {name};"));
        }
        if !emission.text.contains(&format!("import {root_name};")) { proof.raw(format!("import {root_name};")); }
        for part in format.iter().flatten() { proof.raw(format!("import {};", part.module)); }
        proof.raw(emission.text.clone());
        probes = None;
        let parts = format.as_deref().expect("the fields profile generated its formatter");
        (Some(read_fields::certify(&mut proof, &prefix, &program, &record, &emission, parts)?), None)
    } else if read_loop {
        let spec = specs[0].as_str();
        let program = read_loop::Program { root: &root_name, source: symbol, advance: advance.as_deref().unwrap(),
            needle: needle.unwrap(), spec, computes: computes.as_deref().unwrap(), folds: folds.as_deref().unwrap() };
        let context = format!("{prefix}_context");
        check_module(&mut elab, &mut session, &loader::Module {
            name: context.clone(), path: PathBuf::from(format!("{context}.hthr")), src: read_loop::context(&program),
        })?;
        let emission = read_loop::generate_loop(&elab, &context, &prefix, &program)?;
        // The loop's pieces are a module of their own, which its composition imports.
        let pieces = format!("{prefix}_pieces");
        check_module(&mut elab, &mut session, &loader::Module {
            name: pieces.clone(), path: PathBuf::from(format!("{pieces}.hthr")), src: emission.pieces.clone(),
        })?;
        proof = Module::default();
        let imports = read_loop::IMPORTS.iter().chain(if print { read_loop::PRINT_IMPORTS } else { &[] });
        for name in imports.filter(|name| !emission.text.contains(&format!("import {name};"))) {
            proof.raw(format!("import {name};"));
        }
        for part in format.iter().flatten() { proof.raw(format!("import {};", part.module)); }
        proof.raw(emission.text.clone());
        probes = None;
        (Some(match &format {
            Some(parts) => read_loop::certify_print(&mut proof, &prefix, &program, &emission, parts)?,
            None => read_loop::certify(&mut proof, &prefix, &program, &emission)?,
        }), None)
    } else if let Some(callee) = callee {
        if !symbol_ok(&callee) { return Err("callee must be a source identifier".into()); }
        let generate = |module: &mut Module, inputs: [u64; 2]| calls::generate(&elab, module, &prefix,
            &format!("{root_name}::{symbol}"), &format!("{root_name}::{callee}"), inputs, callable_caller);
        for at in probe_inputs {
            let mut other = proof.clone();
            probes = probes.zip(generate(&mut other, at).ok()).map(|(mut all, _)| { all.push(other.render()); all });
        }
        (Some(generate(&mut proof, [inputs[0], inputs[1]])?), None)
    } else if !executable && function_ir_source::reflect_elaborated(&elab, &format!("{root_name}::{symbol}")).is_err() {
        let emission = function_ir_source::generate_elaborated_structured_x86(
            &elab, &prefix, &format!("{root_name}::{symbol}"),
            [Gpr::Rdi, Gpr::Rsi], &[Gpr::Rax, Gpr::Rcx, Gpr::Rdx, Gpr::R8, Gpr::R9, Gpr::R10, Gpr::R11], Gpr::Rax,
        ).map_err(|e| e.to_string())?;
        let bytes = encode_structured(&emission.lowered);
        proof.raw(emission.text);
        // Published as the certificate's own literal pieces, in the code's
        // shape (`_lit`): one comparison of the whole literal would evaluate
        // past the per-declaration fuel on a long body.
        proof.declaration(Declaration::function(format!("{prefix}_published"), Expr::raw("List<BitVec(8)>"),
            Block::expression(Expr::call(format!("{prefix}_lit"), []))));
        proof.declaration(Declaration::theorem(format!("{prefix}_exported_bytes"),
            Expr::equal(Expr::nullary(format!("{prefix}_bytes")), Expr::nullary(format!("{prefix}_published"))),
            Block::expression(Expr::call(format!("{prefix}_bytes_are"), []))));
        (None, Some(bytes))
    } else {
        let emission = function_ir_source::generate_elaborated_x86(
            &elab, &prefix, &format!("{root_name}::{symbol}"),
            [Gpr::Rdi, Gpr::Rsi], &[Gpr::Rax, Gpr::Rcx, Gpr::Rdx, Gpr::R8, Gpr::R9, Gpr::R10, Gpr::R11], Gpr::Rax,
        ).map_err(|e| e.to_string())?;
        let bytes = encode(&emission.instructions);
        proof.raw(emission.text.clone());
        proof.declaration(Declaration::theorem(
            format!("{prefix}_exported_bytes"),
            Expr::equal(Expr::nullary(format!("{prefix}_bytes")), Expr::list(bytes.iter().map(|b|
                Expr::explicit_call("bitvec::BitVec::ofNat", [Expr::nat(8), Expr::nat(u64::from(*b))])))),
            Block::expression(Expr::name("refl")),
        ));
        let image = if executable {
            for at in probe_inputs {
                let mut other = proof.clone();
                probes = probes.zip(elf::certify(&mut other, &prefix, &emission, at, &bytes).ok())
                    .map(|(mut all, _)| { all.push(other.render()); all });
            }
            Some(elf::certify(&mut proof, &prefix, &emission, [inputs[0], inputs[1]], &bytes)?)
        } else { None };
        (image, Some(bytes))
    };
    let proof = match probes.filter(|all| !all.is_empty()) {
        Some(probes) => order::inputs_last(&proof.render(), &probes),
        None => proof.render(),
    };
    eprintln!("checking source refinement, exported bytes, and execution certificate");
    let certificate_module = format!("{prefix}_certificate");
    // The certificate is a module like any other, and goes through the
    // session like one: a repeated build at the same compiler, sources and
    // inputs replays its image instead of re-elaborating thousands of
    // generated theorems, a build with other `--arg`s replays the unchanged
    // declarations from the previous image's slices, and `check_module`
    // opens the module row that totals them. A miss elaborates on the
    // journalled delta path, which costs what `elab_module_source` does since
    // a clone stopped copying the journal
    // (issues/check-module-delta-certificate-cost.md).
    let checked = check_module(&mut elab, &mut session, &loader::Module {
        name: certificate_module.clone(),
        path: certificate.clone(),
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
    if let Some(image) = image {
        write_new(&output, &image)?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            std::fs::set_permissions(&output, std::fs::Permissions::from_mode(0o755))
                .map_err(|e| format!("{}: {e}", output.display()))?;
        }
        if fields {
            println!("{}: {}-byte ELF64 executable; checked read-until-EOF process trace printing `{}` as a three-field line", output.display(), image.len(), specs.join("`, `"));
        } else if print {
            println!("{}: {}-byte ELF64 executable; checked read-until-EOF process trace printing `{}` as a decimal line", output.display(), image.len(), specs[0]);
        } else if read_loop {
            println!("{}: {}-byte ELF64 executable; checked read-until-EOF process trace against `{}`", output.display(), image.len(), specs[0]);
        } else {
            println!("{}: {}-byte ELF64 executable; checked loaded-memory trace and Linux exit request", output.display(), image.len());
        }
        println!("Linux loading and syscall delivery remain environment assumptions");
    } else {
        let bytes = body_bytes.expect("assembly path has a certified body");
        write_new(&output, assembly(symbol, &bytes).as_bytes())?;
        println!("{}: {} certified body bytes; SysV ret shim outside the proof", output.display(), bytes.len());
    }
    println!("certificate: {}", certificate.display());
    Ok(())
}

// A file-sized `[…]` literal is a dependent-vector fold, and every lookup
// inside it re-runs the fold from the front. The same bytes as a chain of
// one-cons definitions cost a δ-step per element, and the chain gives every
// suffix a name for the lookups below. (Building the literal itself was also
// quadratic in its length until the kernel's spelled-`Vec` congruence,
// 2026-09-11 — issues/elf-mutation-test-shape.md; the chain's reason now is
// the lookups.)
// `{name}()` is the whole list; `{name}_from_{k}()` is the k-th suffix.
pub(super) fn byte_chain(m: &mut Module, name: &str, list: &[u8]) {
    let list_fn = |m: &mut Module, name: &str, value: String| m.declaration(
        Declaration::function(name, Expr::raw("List<BitVec(8)>"), Block::expression(Expr::raw(value))));
    list_fn(m, &format!("{name}_from_{}", list.len()), "[]".into());
    for (k, byte) in list.iter().enumerate().rev() {
        list_fn(m, &format!("{name}_from_{k}"), format!("Cons(elf_byte({byte}), {name}_from_{}())", k+1));
    }
    list_fn(m, name, format!("{name}_from_0()"));
}
// Name the suffix each index reaches, once, in one forward pass: step `k+1`
// is `drop_succ` at step `k`, and `list::List::drop({name}_from_{k}(), 1)` is the
// next name by one unfolding. Without this every byte lookup re-traverses the
// whole file prefix (issues/native-summary-test-cpu-margin.md).
pub(super) fn drop_chain(m: &mut Module, name: &str, len: usize) {
    let thm = |m: &mut Module, name: &str, ty: String, value: String| m.declaration(
        Declaration::theorem(name, Expr::raw(ty), Block::expression(Expr::raw(value))));
    thm(m, &format!("{name}_drop_0"), format!("list::List::drop({name}(), 0) = {name}_from_0()"), "refl".into());
    for k in 1..=len {
        thm(m, &format!("{name}_drop_{k}"), format!("list::List::drop({name}(), {k}) = {name}_from_{k}()"),
            format!("trans(list::List::drop_succ({name}(), {}), cong_fn<List<BitVec(8)>, List<BitVec(8)>>(λ suffix => list::List::drop(suffix, 1), {name}_drop_{}()))", k-1, k-1));
    }
}
// The `found` premise of `static_elf64_read_split` at one code offset: the named
// suffix, plus one head read. Both steps are constant work.
pub(super) fn byte_at(name: &str, index: usize) -> String {
    format!("trans(list::List::nth_drop({name}(), {index}), cong_fn<List<BitVec(8)>, Option<BitVec(8)>>(λ suffix => suffix.nth(0), {name}_drop_{index}()))")
}

fn check_module(elab: &mut Elaborator, session: &mut SemanticSession, module: &loader::Module) -> Result<(), String> {
    let outcome = session.check(elab, module, LintProfile::Default);
    for notice in outcome.notices { eprintln!("{notice}"); }
    if outcome.errors.is_empty() { Ok(()) } else {
        Err(outcome.errors.iter().map(|e| e.render(&module.src)).collect::<Vec<_>>().join("\n"))
    }
}

fn write_new(path: &Path, contents: &[u8]) -> Result<(), String> {
    use std::io::Write;
    let mut file = std::fs::OpenOptions::new().write(true).create_new(true).open(path)
        .map_err(|e| format!("{}: {e}", path.display()))?;
    file.write_all(contents).map_err(|e| format!("{}: {e}", path.display()))
}

fn assembly(symbol: &str, bytes: &[u8]) -> String {
    let mut out = format!("# Heather certified body; ret and platform ABI are outside the proof.\n.text\n.globl {symbol}\n.type {symbol}, @function\n{symbol}:\n");
    for chunk in bytes.chunks(12) {
        writeln!(out, "    .byte {}", chunk.iter().map(|b| format!("0x{b:02x}")).collect::<Vec<_>>().join(", ")).unwrap();
    }
    writeln!(out, "    ret\n.size {symbol}, .-{symbol}\n.section .note.GNU-stack,\"\",@progbits").unwrap();
    out
}

// Each certificate test checks its probe modules on a fresh elaborator over
// the complete proof library (~1 GB resident), at the default worker width.
// libtest runs two of them at once under the suite's 6 GiB address-space
// rail; the lock that once serialized them dates from the 4 GiB rail and the
// serial gate.
//
// The library is replayed ONCE per process, and through the declaration-
// verdict store at `target/decl-cache` — the same trust argument as
// `crates/elab/tests/support`'s `semantic_test_base`: a replayed image's
// stored definitions ask the store the question the cold gate answered, and
// a changed kernel discards the store loudly on open. Without it every test
// re-kernel-checked all 28 modules' bindings in the debug profile: 25 s of
// replay per test against ~1 s of the test's own content, 100 of this
// binary's 105 CPU-s (2026-09-17, alone, width one). The gate is sealed to
// `NoGate` before the image is taken, so every certificate, mutation and
// refusal below faces the real kernel on every run.
#[cfg(test)]
pub(crate) fn native_test_base() -> Elaborator {
    use std::sync::OnceLock;
    static IMAGE: OnceLock<heather_elab::SemanticImage> = OnceLock::new();
    IMAGE.get_or_init(|| {
        let mut elab = Elaborator::with_prelude().unwrap();
        let mut session = SemanticSession::new(Some(PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/../../target/native-test-images"))));
        let decl_cache = PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/../../target/decl-cache"));
        let (cache, rejected) = heather_cache::Cache::open(decl_cache.clone());
        if let Some(msg) = rejected.as_ref().and_then(|r| r.message()) { eprintln!("decl-cache: {msg}"); }
        let cache = Rc::new(cache);
        elab.set_gate(Rc::clone(&cache) as Rc<dyn heather_elab::gate::KernelGate>);
        for &(name, src) in SUPPORT {
            check_module(&mut elab, &mut session, &loader::Module {
                name: name.into(), path: PathBuf::from(name), src: src.into(),
            }).unwrap();
        }
        elab.set_gate(Rc::new(heather_elab::gate::NoGate));
        if let Err(err) = cache.save() { eprintln!("decl-cache: could not write {}: {err}", decl_cache.display()); }
        elab.semantic_image()
    }).elaborator()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn native_encoder_is_checked_and_corruption_is_rejected() {
        let elab = native_test_base();
        let instructions = [
            Instruction::MovRR { destination: Gpr::R15, source: Gpr::R8 },
            Instruction::MovRI { destination: Gpr::R9, immediate: 257 },
            Instruction::AddRR { destination: Gpr::Rax, source: Gpr::Rsi },
            Instruction::SubRR { destination: Gpr::Rdx, source: Gpr::R10 },
            Instruction::AndRR { destination: Gpr::R12, source: Gpr::Rbx },
            Instruction::OrRR { destination: Gpr::Rbp, source: Gpr::R11 },
            Instruction::XorRR { destination: Gpr::Rdi, source: Gpr::R13 },
            Instruction::CmpRR { left: Gpr::R14, right: Gpr::Rcx },
            Instruction::SetBelow { destination: LowByteGpr::Dl },
            Instruction::SetLess { destination: LowByteGpr::Bl },
        ];
        for (index, instruction) in instructions.iter().enumerate() {
            let mut bytes = encode(&[*instruction]);
            for corrupted in [false, true] {
                if corrupted { bytes[0] ^= 1; }
                let mut module = Module::default();
                module.raw("import x86_64;\nimport bitvec;\nimport list;");
                module.declaration(Declaration::theorem("encoder_agrees", Expr::equal(
                    Expr::call("canonical_bytes", [instruction.heather_expr()]),
                    Expr::list(bytes.iter().map(|b| Expr::explicit_call("bitvec::BitVec::ofNat", [Expr::nat(8), Expr::nat(u64::from(*b))]))),
                ), Block::expression(Expr::name("refl"))));
                let text = module.render();
                let result = elab.fork().elab_module_source("native_encoder_check", &text);
                if corrupted {
                    let error = result.expect_err("wrong encoding must fail");
                    assert!(format!("{error:?}").contains("NotConvertible"), "case {index}: {}", error.render(&text));
                } else {
                    result.unwrap_or_else(|e| panic!("case {index}: {}", e.render(&text)));
                }
            }
        }
    }
}
