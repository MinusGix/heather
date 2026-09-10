//! First native export boundary: a checked straight-line body plus an explicit
//! unproved SysV return shim. The Rust encoder is checked by a literal-byte
//! equality in the generated certificate before any output is published.
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use heather_elab::{Elaborator, LintProfile, function_ir_source};
use heather_elab::function_ir_x86_lower::{Gpr, Instruction, LowByteGpr};
use heather_elab::heather_emit::{Block, Declaration, Expr, Module};
use heather_cli::{loader, semantic::SemanticSession};

mod elf;
mod calls;

const SUPPORT: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/logic.hthr")),
    ("bool", include_str!("../../../lib/std/bool.hthr")),
    ("nat", include_str!("../../../lib/std/nat.hthr")),
    ("option", include_str!("../../../lib/std/option.hthr")),
    ("pair", include_str!("../../../lib/std/pair.hthr")),
    ("list", include_str!("../../../lib/std/list.hthr")),
    ("algebra", include_str!("../../../lib/std/algebra.hthr")),
    ("int", include_str!("../../../lib/std/int.hthr")),
    ("bitvec", include_str!("../../../lib/std/bitvec.hthr")),
    ("relation", include_str!("../../../lib/std/relation.hthr")),
    ("location", include_str!("../../../lib/std/location.hthr")),
    ("certified_lookup", include_str!("../../../lib/std/certified_lookup.hthr")),
    ("x86_64", include_str!("../../../lib/std/arch/x86_64/model.hthr")),
    ("x86_64_block", include_str!("../../../lib/std/arch/x86_64/block.hthr")),
    ("x86_64_control_block", include_str!("../../../lib/std/arch/x86_64/control_block.hthr")),
    ("x86_64_control_flow", include_str!("../../../lib/std/arch/x86_64/control_flow.hthr")),
    ("function_ir", include_str!("../../../lib/function_ir.hthr")),
    ("function_ir_x86_support", include_str!("../../../lib/function_ir_x86_support.hthr")),
    ("elf64", include_str!("../../../lib/elf64.hthr")),
    ("linux_x86_64_entry", include_str!("../../../lib/linux_x86_64_entry.hthr")),
    ("x86_64_fetch", include_str!("../../../lib/std/arch/x86_64/fetch.hthr")),
    ("x86_64_fetch_block", include_str!("../../../lib/std/arch/x86_64/fetch_block.hthr")),
    ("elf64_load", include_str!("../../../lib/elf64_load.hthr")),
    ("x86_64_calls", include_str!("../../../lib/std/arch/x86_64/calls.hthr")),
    ("x86_64_call_frame", include_str!("../../../lib/std/arch/x86_64/call_frame.hthr")),
    ("x86_64_call_summary", include_str!("../../../lib/std/arch/x86_64/call_summary.hthr")),
    ("elf64_calls", include_str!("../../../lib/elf64_calls.hthr")),
    ("linux_x86_64_fetch", include_str!("../../../lib/linux_x86_64_fetch.hthr")),
];

pub fn run(args: &[String]) -> ExitCode {
    report(compile(args, false))
}

pub fn build(args: &[String]) -> ExitCode {
    report(compile(args, true))
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
    let mut timings = None;
    let mut search = vec![PathBuf::from("lib/std"), PathBuf::from("lib")];
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--callee" if executable => {
                callee = Some(args.next().ok_or("--callee needs a source function name")?.clone());
            }
            "--arg" if executable => {
                inputs.push(elf::parse_argument(args.next().ok_or("--arg needs an unsigned integer")?)?);
            }
            "-o" | "-L" | "--cache-dir" | "--item-timings" => {
                let value = PathBuf::from(args.next().ok_or_else(|| format!("{arg} needs a path"))?);
                match arg.as_str() {
                    "-o" => output = Some(value),
                    "-L" => { if !search.contains(&value) { search.push(value); } }
                    "--item-timings" => timings = Some(value),
                    _ => cache = Some(value),
                }
            }
            _ if arg.starts_with('-') => return Err(format!("unknown option `{arg}`")),
            _ => positional.push(arg.as_str()),
        }
    }
    if executable && inputs.len() != 2 {
        return Err("build-x86 needs exactly two --arg values for the source function".into());
    }
    if positional.len() != 2 || output.is_none() {
        if executable {
            return Err("usage: heather build-x86 <file.hthr> <function> --arg <u64> --arg <u64> -o <executable> [--callee <function>] [-L <dir>]... [--cache-dir <dir>] [--item-timings <file.tsv>]".into());
        }
        return Err("usage: heather compile-x86 <file.hthr> <function> -o <output.s> [-L <dir>]... [--cache-dir <dir>] [--item-timings <file.tsv>]".into());
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
    let sources = loader::load(source, &search).map_err(|e| e.msg)?;
    let root_name = sources.last().ok_or("empty source closure")?.name.clone();
    let mut elab = Elaborator::with_prelude().map_err(|e| format!("prelude: {e}"))?;
    // Observation only: the collector changes no judgment, no fuel, and no
    // cache entry, and stays off unless `--item-timings` names a file. Turning
    // it on here rather than at the certificate separates a module actually
    // elaborated (a cache miss, or the root source) from the generated
    // certificate by the `module` column.
    if timings.is_some() { elab.enable_item_timings(); }
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
            check_module(&mut elab, &mut session, module)?;
        }
    }
    let prefix = format!("{symbol}_native");
    let mut proof = Module::default();
    for name in ["function_ir_x86_support", "function_ir", "x86_64", "x86_64_block",
        "x86_64_control_block", "x86_64_control_flow", "bitvec", "list", "logic", "elf64", "linux_x86_64_entry", "x86_64_fetch", "x86_64_fetch_block", "elf64_load", "linux_x86_64_fetch", "bool", "option", "nat"] {
        proof.raw(format!("import {name};"));
    }
    let (image, body_bytes) = if let Some(callee) = callee {
        if !symbol_ok(&callee) { return Err("callee must be a source identifier".into()); }
        (Some(calls::generate(&elab, &mut proof, &prefix, &format!("{root_name}::{symbol}"),
            &format!("{root_name}::{callee}"), [inputs[0], inputs[1]])?), None)
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
                Expr::call("bitvec::ofNat", [Expr::nat(8), Expr::nat(u64::from(*b))])))),
            Block::expression(Expr::name("refl")),
        ));
        let image = if executable {
            Some(elf::certify(&mut proof, &prefix, &emission, [inputs[0], inputs[1]], &bytes)?)
        } else { None };
        (image, Some(bytes))
    };
    let proof = proof.render();
    eprintln!("checking source refinement, exported bytes, and execution certificate");
    let checked = elab.elab_module_source(&format!("{prefix}_certificate"), &proof);
    // A refused certificate is the case worth attributing, so the table is
    // written before the failure is reported.
    if let Some(path) = &timings { write_item_timings(path, &elab.take_item_timings())?; }
    checked.map_err(|e| e.render(&proof))?;
    write_new(&certificate, proof.as_bytes())?;
    if let Some(image) = image {
        write_new(&output, &image)?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            std::fs::set_permissions(&output, std::fs::Permissions::from_mode(0o755))
                .map_err(|e| format!("{}: {e}", output.display()))?;
        }
        println!("{}: {}-byte ELF64 executable; checked loaded-memory trace and Linux exit request", output.display(), image.len());
        println!("Linux loading and syscall delivery remain environment assumptions");
    } else {
        let bytes = body_bytes.expect("assembly path has a straight-line body");
        write_new(&output, assembly(symbol, &bytes).as_bytes())?;
        println!("{}: {} certified body bytes; SysV ret shim outside the proof", output.display(), bytes.len());
    }
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

/// One row per surface item the elaborator actually ran, in emission order.
/// The value-metric columns are empty unless the build carries the
/// `value-metrics` feature, which is what makes them collected at all.
fn write_item_timings(path: &Path, timings: &[heather_elab::ItemTiming]) -> Result<(), String> {
    let ms = |ns: u64| format!("{:.3}", ns as f64 / 1e6);
    let mut out = String::from("module\titem\ttotal_ms\tkernel_ms\tterm_cache_lookups\tterm_cache_hits\ttype_cache_lookups\ttype_cache_hits\n");
    for timing in timings {
        let cells = timing.value_metrics.map_or_else(|| "\t\t\t".to_string(), |m| {
            format!("{}\t{}\t{}\t{}", m.term_cache_lookups, m.term_cache_hits, m.type_cache_lookups, m.type_cache_hits)
        });
        writeln!(out, "{}\t{}\t{}\t{}\t{cells}", timing.module, timing.item, ms(timing.total_ns), ms(timing.kernel_ns))
            .expect("writing to a string");
    }
    std::fs::write(path, out).map_err(|e| format!("{}: {e}", path.display()))?;
    eprintln!("item timings: {} rows in {}", timings.len(), path.display());
    Ok(())
}

fn write_new(path: &Path, contents: &[u8]) -> Result<(), String> {
    use std::io::Write;
    let mut file = std::fs::OpenOptions::new().write(true).create_new(true).open(path)
        .map_err(|e| format!("{}: {e}", path.display()))?;
    file.write_all(contents).map_err(|e| format!("{}: {e}", path.display()))
}

fn reg(register: Gpr) -> u8 {
    match register {
        Gpr::Rax => 0, Gpr::Rcx => 1, Gpr::Rdx => 2, Gpr::Rbx => 3,
        Gpr::Rsp => 4, Gpr::Rbp => 5, Gpr::Rsi => 6, Gpr::Rdi => 7,
        Gpr::R8 => 8, Gpr::R9 => 9, Gpr::R10 => 10, Gpr::R11 => 11,
        Gpr::R12 => 12, Gpr::R13 => 13, Gpr::R14 => 14, Gpr::R15 => 15,
    }
}

fn encode(instructions: &[Instruction]) -> Vec<u8> {
    let mut bytes = Vec::new();
    for &instruction in instructions {
        let (opcode, destination, source) = match instruction {
            Instruction::MovRI { destination, immediate } => {
                let r = reg(destination);
                bytes.extend([0x48 | (r >> 3), 0xb8 | (r & 7)]);
                bytes.extend(immediate.to_le_bytes());
                continue;
            }
            Instruction::SetBelow { destination } | Instruction::SetLess { destination } => {
                let r = match destination { LowByteGpr::Al => 0, LowByteGpr::Cl => 1, LowByteGpr::Dl => 2, LowByteGpr::Bl => 3 };
                bytes.extend([0x0f, if matches!(instruction, Instruction::SetBelow { .. }) { 0x92 } else { 0x9c }, 0xc0 | r]);
                continue;
            }
            Instruction::MovRR { destination, source } => (0x89, destination, source),
            Instruction::AddRR { destination, source } => (0x01, destination, source),
            Instruction::SubRR { destination, source } => (0x29, destination, source),
            Instruction::AndRR { destination, source } => (0x21, destination, source),
            Instruction::OrRR { destination, source } => (0x09, destination, source),
            Instruction::XorRR { destination, source } => (0x31, destination, source),
            Instruction::CmpRR { left, right } => (0x39, left, right),
        };
        let (rm, r) = (reg(destination), reg(source));
        bytes.extend([0x48 | (rm >> 3) | ((r >> 3) << 2), opcode, 0xc0 | ((r & 7) << 3) | (rm & 7)]);
    }
    bytes
}

fn assembly(symbol: &str, bytes: &[u8]) -> String {
    let mut out = format!("# Heather certified body; ret and platform ABI are outside the proof.\n.text\n.globl {symbol}\n.type {symbol}, @function\n{symbol}:\n");
    for chunk in bytes.chunks(12) {
        writeln!(out, "    .byte {}", chunk.iter().map(|b| format!("0x{b:02x}")).collect::<Vec<_>>().join(", ")).unwrap();
    }
    writeln!(out, "    ret\n.size {symbol}, .-{symbol}\n.section .note.GNU-stack,\"\",@progbits").unwrap();
    out
}

// Each certificate test loads the complete proof library. Keep these loads
// serial so two elaborators do not exceed the test process's 4 GiB cap.
#[cfg(test)]
static CERTIFICATE_TEST_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn native_encoder_is_checked_and_corruption_is_rejected() {
        let _guard = CERTIFICATE_TEST_LOCK.lock().unwrap();
        let mut elab = Elaborator::with_prelude().unwrap();
        let mut session = SemanticSession::new(Some(PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/../../target/native-test-images"))));
        for &(name, src) in SUPPORT {
            check_module(&mut elab, &mut session, &loader::Module {
                name: name.into(), path: PathBuf::from(name), src: src.into(),
            }).unwrap();
        }
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
                    Expr::list(bytes.iter().map(|b| Expr::call("bitvec::ofNat", [Expr::nat(8), Expr::nat(u64::from(*b))]))),
                ), Block::expression(Expr::name("refl"))));
                let text = module.render();
                let result = elab.clone().elab_module_source("native_encoder_check", &text);
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
