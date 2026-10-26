//! `write-elf`: an effectful source (a nullary `Source`, native_source)
//! compiled by `native_compile` with its region at the I/O profile's page,
//! assembled, and written in the profile's ELF (`io_elf_file`,
//! linux_x86_64_image), executable.
//!
//! The program and its bytes are read off elaborator forks, which are
//! untrusted, and then stated as literals the kernel checks: that the source
//! compiles to the literal program (`<source>_elf_compiles`), and that the
//! file of any program it compiles to is the bytes written
//! (`<source>_elf_written`). So a theorem about that file
//! (`native_cat_executable`'s, for cat) is about the one written. That Linux
//! loads the file as the theorem's loader says is outside the proof.
//! Nothing is written unless the kernel accepts every statement.
//!
//! A compile is most of what one declaration's fuel buys, so no statement
//! repeats it: the emission is checked against the literal once, by
//! evaluation; the layout check `Source::compile` makes is proved a stretch
//! at a time over the literal (as `compile-x86` does); the bytes a piece at
//! a time. The literal spells each address in the region as the compiler
//! does, `add_nat` from the page's start, so the emission's check compares
//! the two by their arguments instead of evaluating each one's bits.
use std::path::{Path, PathBuf};

use heather_elab::{function_ir_source, Elaborator};
use heather_cache::module_image::ImageFreshness;
use heather_cli::{loader, semantic::SemanticSession};

use super::{check_file, symbol_ok, verified, write_new};

/// The I/O profile's file is at most this long (`io_elf_file`'s sixteen-bit
/// size), its header included.
const MAX_FILE: usize = 65535;
const HEADER: usize = 232;
/// Items in each definition of the program's literal.
const STRETCH: usize = 32;
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

const IMPORTS: &[&str] = &["native_source", "native_compile", "native_compile_correct", "linux_x86_64_image", "x86_64",
    "x86_64_asm", "x86_64_asm_runs", "x86_64_data_read", "x86_64_store", "bitvec", "bool", "list", "logic", "nat", "option"];

pub(super) fn write(args: &[String]) -> Result<(), String> {
    let mut positional = Vec::new();
    let mut output = None;
    let mut cache = None;
    let mut freshness = ImageFreshness::Exact;
    let mut search = vec![PathBuf::from("lib/std"), PathBuf::from("lib")];
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            // `check`'s flag: replay images an earlier build wrote, as the
            // suite's stale lanes do everywhere else.
            "--accept-stale-images" => freshness = ImageFreshness::AcceptStale,
            "-o" | "-L" | "--cache-dir" => {
                let value = PathBuf::from(args.next().ok_or_else(|| format!("{arg} needs a path"))?);
                match arg.as_str() {
                    "-o" => output = Some(value),
                    "-L" => { if !search.contains(&value) { search.push(value); } }
                    _ => cache = Some(value),
                }
            }
            _ if arg.starts_with('-') => return Err(format!("unknown option `{arg}`")),
            _ => positional.push(arg.as_str()),
        }
    }
    if positional.len() != 2 || output.is_none() {
        return Err("usage: heather write-elf <file.hthr> <source> -o <output> [-L <dir>]... [--cache-dir <dir>] [--accept-stale-images]".into());
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
    let sources = loader::load(source, &search).map_err(|e| e.msg)?;
    let root = sources.last().ok_or("empty source closure")?.name.clone();
    let mut elab = Elaborator::with_prelude().map_err(|e| format!("prelude: {e}"))?;
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
    let probes = format!("import {root};\n{imports}
fn {p}_program() → Prog {{ match {symbol}().compile({LOW}) {{ None => Start, Some(program) => program }} }}
fn {p}_numbers() → List<Nat> {{ {p}_program().numbers() }}
fn {p}_lens() → List<Nat> {{ asm_lens({p}_program()) }}
");
    let mut fork = elab.fork();
    fork.elab_module_source(&probe, &probes).map_err(|e| e.render(&probes))?;
    let numbers = |fork: &Elaborator, module: &str, item: &str| function_ir_source::evaluate_numbers(fork, &format!("{module}::{p}_{item}"))
        .map_err(|e| format!("`{symbol}` ({item}): {e}"));
    let address = |width: u32, n: u64| {
        if width == 64 && REGION.contains(&n) { format!("{LOW}.add_nat({})", n - REGION.start) }
        else { format!("@bitvec::BitVec::ofNat({width}, {n})") }
    };
    let items = verified::read_items_with(&numbers(&fork, &probe, "numbers")?, &address)?;
    let lens = numbers(&fork, &probe, "lens")?;
    drop(fork);
    if items.is_empty() || lens.len() != items.len() {
        return Err(format!("`{symbol}` did not compile, or its items' lengths did not read back"));
    }
    let length = lens.iter().sum::<u64>() as usize;
    if HEADER + length > MAX_FILE {
        return Err(format!("`{symbol}` compiles to {length} bytes, past the profile's {MAX_FILE} with its header"));
    }

    // The literal in stretches, each its own definition on the one before.
    let mut code = String::new();
    let mut earlier = "Start".to_string();
    for (k, stretch) in items.chunks(STRETCH).enumerate() {
        let mut at = earlier.clone();
        for (name, item) in stretch { at = format!("At({at},\n    {name}, {item})"); }
        code.push_str(&format!("fn {p}_code_{k}() → Prog {{\n    {at}\n}}\n"));
        earlier = format!("{p}_code_{k}()");
    }
    code.push_str(&format!("fn {p}_code() → Prog {{ {earlier} }}\n"));
    let pieces = verified::cut_pieces(&lens, PIECE);
    let header = format!("io_elf_header(BitVec::ofNat(232 + {length}), BitVec::ofNat((232 + {length}).shr(8)))");
    let mut reads = format!("import {root};\n{imports}\n{code}");
    for (c, verified::Piece { back, count, .. }) in pieces.iter().enumerate() {
        reads.push_str(&format!("fn {p}_piece_numbers_{c}() → List<Nat> {{ asm_code_after(no_fills(), asm_labels({p}_code()), asm_back({p}_code(), {back}), {count}).map(λ (b: BitVec(8)) => b.toNat()) }}\n"));
    }
    reads.push_str(&format!("fn {p}_header_numbers() → List<Nat> {{ {header}.map(λ (b: BitVec(8)) => b.toNat()) }}\n"));
    let read = format!("{p}_read");
    let mut fork = elab.fork();
    fork.elab_module_source(&read, &reads).map_err(|e| e.render(&reads))?;
    let byte = |n: u64| u8::try_from(n).map_err(|_| "a byte above 255".to_string());
    let mut bytes = vec![0u8; length];
    let mut end = length;
    for (c, piece) in pieces.iter().enumerate() {
        let read = numbers(&fork, &read, &format!("piece_numbers_{c}"))?;
        if read.len() != end - piece.start {
            return Err(format!("`{symbol}`'s piece {c} is not as long as its items"));
        }
        for (at, n) in (piece.start..end).zip(read) { bytes[at] = byte(n)?; }
        end = piece.start;
    }
    let head = numbers(&fork, &read, "header_numbers")?.into_iter().map(byte).collect::<Result<Vec<u8>, String>>()?;
    drop(fork);
    if head.len() != HEADER {
        return Err("the header did not read back".into());
    }
    let header_literal: Vec<String> = head.iter().map(|b| format!("@bitvec::BitVec::ofNat(8, {b})")).collect();
    let finish = "then(then(c.prog, Block([MovRI(Rdi, BitVec::ofNat(0)), MovRI(Rax, BitVec::ofNat(60))])), Syscall)";

    let mut text = format!("// `{symbol}` compiled into the I/O profile's ELF, as `heather write-elf` writes
// it: generated, and checked by the kernel.
import {root};
{imports}
// The program: what `{symbol}().compile` computes.
{code}
theorem {p}_emitted(): {symbol}().main.emit(Start, {symbol}().layout({LOW}), 0).map(λ (c: Compiled) => {finish}) = Some({p}_code()) {{ refl }}

{layout}
theorem {p}_holes(): {p}_code().no_holes().IsTrue() {{ trivial }}

theorem {p}_laid(): {p}_code().laid_out().IsTrue() {{
    {p}_code().laid_out_intro({p}_holes(), {p}_unique_0(), {p}_lands_0(), {p}_named_0())
}}

theorem {p}_compiles(): {symbol}().compile({LOW}) = Some({p}_code()) {{
    {symbol}().compile_of({LOW}, {p}_code(), {p}_emitted(), {p}_laid())
}}

// The bytes, a piece at a time from the last item.
", layout = verified::layout(p, items.len()));
    text.push_str(&verified::byte_pieces(p, &pieces, &bytes));
    text.push_str(&format!("
fn {p}_header() → List<BitVec(8)> {{ [{}] }}
theorem {p}_header_is(): {header} = {p}_header() {{ refl }}
theorem {p}_length(): {p}_upto_0().len() = {length} {{ refl }}

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
", header_literal.join(", ")));
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
    if let Some(store) = verdicts {
        if let Err(err) = store.save() {
            eprintln!("cache: could not write verdicts: {err}");
        }
    }
    checked?;
    write_new(&certificate, text.as_bytes())?;
    std::fs::remove_file(&unchecked).map_err(|e| format!("{}: {e}", unchecked.display()))?;
    write_executable(&output, &file)?;
    println!("{}: {} bytes, `{symbol}` compiled into the I/O profile's ELF as the kernel checked it", output.display(), file.len());
    println!("certificate: {}", certificate.display());
    Ok(())
}

fn write_executable(path: &Path, bytes: &[u8]) -> Result<(), String> {
    use std::io::Write;
    use std::os::unix::fs::OpenOptionsExt;
    let mut file = std::fs::OpenOptions::new().write(true).create_new(true).mode(0o755).open(path)
        .map_err(|e| format!("{}: {e}", path.display()))?;
    file.write_all(bytes).map_err(|e| format!("{}: {e}", path.display()))
}
