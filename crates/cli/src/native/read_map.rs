//! The map profile (docs/native-tr-design.md): read stdin a page at a time,
//! translate each chunk in place through a certified byte map, write it to
//! stdout and go back to the read; exit 0 at the empty read. The process
//! shape and its proof are the library's (`lib/elf64_read_map.hthr`); this
//! producer lowers the program's byte map through the typed generator, lays
//! out the code, and instantiates the library theorem at the written file.
//! Nothing in it is about any one program.
use heather_elab::function_ir_source::{generate_elaborated_typed_x86, reflect_elaborated_structured, StructuredSourceType};
use heather_elab::function_ir_x86_lower::{encode_structured, Gpr, Instruction, Placements};
use heather_elab::heather_emit::Module;
use heather_elab::Elaborator;

use super::read_loop::{backward, claims, copy, forward, image_facts, literal, mov, near, nested, syscall, SYSCALL, TEST};

// Bundled after the read profile's (less its state process) and the write
// loop: the map process.
pub(super) const SUPPORT: &[(&str, &str)] = &[
    ("elf64_read_map", include_str!("../../../../lib/elf64_read_map.hthr")),
];
pub(super) const IMPORTS: &[&str] = &["elf64_read_map", "elf64_write_loop", "elf64_print_pieces", "elf64_read_pieces", "elf64_io",
    "elf64_calls", "elf64", "linux_x86_64_entry", "linux_x86_64_io", "linux_x86_64_determinism", "x86_64_structured_block",
    "x86_64_fetched_code", "x86_64_fetch", "bitvec_nat", "x86_64", "x86_64_block", "bitvec", "list", "logic", "nat"];

/// The byte map's certificate: a module of its own, and its bytes.
pub(super) struct Piece { pub module: String, pub prefix: String, pub text: String, pub bytes: Vec<u8> }

// The byte map at the map loop's registers (elf64_read_map's `MapPiece`):
// the byte in RAX, its image to RDX, scratch that leaves RSI, RCX, R9, R10
// and R11 to the loop.
pub(super) fn generate_piece(elab: &Elaborator, root: &str, symbol: &str, prefix: &str) -> Result<Piece, String> {
    use Gpr::*;
    let source = format!("{root}::{symbol}");
    let part = format!("{prefix}_map");
    elab.with_module_scope(root, |elab| {
        let reflected = reflect_elaborated_structured(elab, &source).map_err(|e| format!("{symbol}: {e:?}"))?;
        if reflected.parameters != [StructuredSourceType::Word(8)] || reflected.result != StructuredSourceType::Word(8)
            || reflected.record.is_some() || reflected.choice.is_some() {
            return Err(format!("--map needs a byte map `{symbol}(b: BitVec(8)) → BitVec(8)`"));
        }
        let emission = generate_elaborated_typed_x86(elab, &part, &source, &Placements::from([(0, Rax)]), &[Rdx, Rbx, Rdi, R8],
            &Placements::from([(1, Rdx)])).map_err(|e| format!("{symbol}: {e:?}"))?;
        Ok(Piece { module: format!("{part}_piece"), prefix: part, bytes: encode_structured(&emission.lowered), text: emission.text })
    })?
}

/// Lay out the program and write its certificate. Returns the file to
/// publish.
pub(super) fn certify(module: &mut Module, prefix: &str, root: &str, symbol: &str, piece: &Piece) -> Result<Vec<u8>, String> {
    use Gpr::*;
    let encode = super::encode;
    let entry = encode(&[mov(Rax, 0), mov(Rdi, 0), mov(Rsi, 0x410000), mov(Rdx, 4096)]);
    let setup = encode(&[mov(Rsi, 0x410000), mov(R9, 0x410000), copy(Rcx, Rax), copy(R10, Rax), mov(R11, 1)]);
    // MOVZX RAX, byte [RSI] and MOV byte [RSI], DL: the library's ByteLoad
    // and ByteStore, checked against the model's encodings.
    let load = vec![0x48, 0x0f, 0xb6, 0x06];
    let store = vec![0x40, 0x88, 0x16];
    let step = encode(&[Instruction::AddRR { destination: Rsi, source: R11 }, Instruction::SubRR { destination: Rcx, source: R11 }]);
    let retry = encode(&[mov(Rbx, 4), Instruction::AddRR { destination: Rax, source: Rbx }]);
    let fail = encode(&[mov(Rdi, 1), mov(Rax, 60)]);
    let write = encode(&[copy(Rsi, R9), copy(Rdx, R10), mov(Rdi, 1), mov(Rax, 1)]);
    let advance = encode(&[Instruction::AddRR { destination: R9, source: Rax }, Instruction::SubRR { destination: R10, source: Rax }]);
    let exit = encode(&[mov(Rdi, 0), mov(Rax, 60)]);

    // Offsets from the entry, as elf64_read_map's `map_at_*`.
    let at_js = entry.len() + 2 + TEST.len() + 6;
    let at_load = at_js + 6 + setup.len();
    let at_jnz = at_load + load.len() + piece.bytes.len() + store.len() + step.len();
    let at_write = at_jnz + 6;
    let at_wjz = at_write + write.len() + 2 + TEST.len() + 6 + advance.len();
    let at_exit = at_wjz + 6 + 5 + retry.len() + 6 + fail.len() + 2;
    let at_failed = at_exit + exit.len() + 2;
    let at_rjz = at_failed + retry.len();
    // JZ at end of file to the write loop's exit(0); JS past the chunk and the
    // write loop to the failure path; JNZ back to the load; the retry's JZ back
    // to the read. The write loop's JS and JMP are elf64_write_loop's; its JZ
    // once all is sent goes back to the read.
    let ed = forward(at_exit - (at_js));
    let sd = forward(at_failed - (at_js + 6));
    let ld = backward(at_jnz + 6 - at_load);
    let rd = backward(at_rjz + 6);
    let psd = forward(advance.len() + 6 + 5);
    let pzd = backward(at_wjz + 6);
    let wspan = write.len() + 2 + TEST.len() + 6 + advance.len() + 6;
    let (pbd, prd) = (backward(wspan + 5), backward(wspan + 5 + retry.len() + 6));

    let pieces: Vec<(&str, Vec<u8>)> = vec![("entry", entry), ("test", TEST.to_vec()), ("jz", near(&[0x0f, 0x84], ed)),
        ("js", near(&[0x0f, 0x88], sd)), ("setup", setup), ("load", load), ("store", store), ("step", step),
        ("jnz", near(&[0x0f, 0x85], ld)), ("write", write), ("wjs", near(&[0x0f, 0x88], psd)), ("advance", advance),
        ("wjz", near(&[0x0f, 0x84], pzd)), ("wjmp", near(&[0xe9], pbd)), ("retry", retry), ("wrjz", near(&[0x0f, 0x84], prd)),
        ("fail", fail), ("exit", exit), ("rjz", near(&[0x0f, 0x84], rd))];
    let p = |name: &str| pieces.iter().find(|(n, _)| *n == name).expect("a map piece").1.clone();
    let write_loop = [p("write"), SYSCALL.to_vec(), TEST.to_vec(), p("wjs"), p("advance"), p("wjz"), p("wjmp"), p("retry"), p("wrjz"),
        p("fail"), SYSCALL.to_vec(), p("exit"), SYSCALL.to_vec()].concat();
    let code = [p("entry"), SYSCALL.to_vec(), TEST.to_vec(), p("jz"), p("js"), p("setup"), p("load"), piece.bytes.clone(), p("store"),
        p("step"), p("jnz"), write_loop, p("retry"), p("rjz"), p("fail"), SYSCALL.to_vec()].concat();
    debug_assert_eq!(code.len(), at_rjz + 6 + p("fail").len() + 2);
    let file = super::calls::io_image(&code)?;

    for (name, bytes) in &pieces {
        module.raw(format!("fn {prefix}_{name}_written() → List<BitVec(8)> {{ {} }}", literal(bytes)));
    }
    let n = |v: u32| format!("@bitvec::BitVec::ofNat(32, {v})");
    module.raw(format!("fn {prefix}_jumps() → MapJumps {{ MapJumps({}, {}, {}, {}) }}", n(ed), n(sd), n(ld), n(rd)));
    module.raw(format!("fn {prefix}_print_jumps() → PrintJumps {{ PrintJumps({}, {}, {}, {}) }}", n(psd), n(pzd), n(pbd), n(prd)));

    let m = &piece.prefix;
    let pj = format!("{prefix}_print_jumps()");
    let code_term = format!("map_code({m}_code(), {prefix}_jumps(), {pj})");
    let w = |name: &str| format!("{prefix}_{name}_written()");
    let writes = format!("({})", nested(&[w("write"), syscall(), w("test"), w("wjs"), w("advance"), w("wjz"), w("wjmp"), w("retry"),
        w("wrjz"), w("fail"), syscall(), w("exit"), format!("({})", syscall())]));
    let layout = |mapped: &str| nested(&[w("entry"), syscall(), w("test"), w("jz"), w("js"), w("setup"), w("load"), mapped.to_string(),
        w("store"), w("step"), w("jnz"), writes.clone(), w("retry"), w("rjz"), format!("({} ++ {})", w("fail"), syscall())]);
    // The code as written: fixed pieces by evaluation, the byte map's bytes
    // by its lemma. Its length the same way (map_code_len).
    let chain = format!("j({m}_bytes_are(), λ y _ => {code_term} = {}, refl)", layout("y"));
    let measure = format!("map_code_len({m}_code(), {prefix}_jumps(), {pj}, {}, {m}_byte_length())", piece.bytes.len());
    image_facts(module, prefix, &code_term, &layout(&format!("{m}_lit()")), &chain, &file, code.len(), &measure);
    // Where the jumps land, from the written displacements: closed facts,
    // the byte map's length by its lemma.
    let by_length = |name: &str, statement: &dyn Fn(&str) -> String| format!("\
theorem {prefix}_{name}(): {} {{ j(sym({m}_byte_length()), λ n _ => {}, refl) }}\n",
        statement(&format!("{m}_bytes().len()")), statement("n"));
    let jumps = format!("{prefix}_jumps()");
    module.raw(by_length("exit_reads", &|len| format!("{jumps}.ed.sign_extend(32).toNat() = map_exit_skip({len})")));
    module.raw(by_length("fail_reads", &|len| format!("{jumps}.sd.sign_extend(32).toNat() = map_fail_skip({len})")));
    module.raw(by_length("again_closes", &|len| format!("map_loop_span({len}) + 6 + {jumps}.ld.sign_extend(32).toNat() = Nat::pow(2, 64)")));
    module.raw(by_length("retry_closes", &|len| format!("map_at_retry({len}) + 6 + {jumps}.rd.sign_extend(32).toNat() = Nat::pow(2, 64)")));
    module.raw(by_length("write_read_closes",
        &|len| format!("wl_at_wjz(map_at_write({len})) + 6 + {pj}.zd.sign_extend(32).toNat() = Nat::pow(2, 64)")));
    module.raw(format!("\
theorem {prefix}_write_fail_reads(): {pj}.sd.sign_extend(32).toNat() = print_fail_skip() {{ refl }}
theorem {prefix}_write_back_closes(): print_loop_span() + 5 + {pj}.bd.sign_extend(32).toNat() = Nat::pow(2, 64) {{ refl }}
theorem {prefix}_write_retry_closes(): print_retry_span() + 6 + {pj}.rd.sign_extend(32).toNat() = Nat::pow(2, 64) {{ refl }}
"));
    let f = format!("{root}::{symbol}");
    let premises = format!("steps: List<EofStep<List<WriteStep>>>, ok: MapSteps({f}, steps), ending: EofEnd<WriteFailure>, ending_ok: MapEndingOk({f}, ending),
    page: Nat → BitVec(8), gprs: Gprs, flags: Flags");
    let events = format!("map_events({f}, steps, ending)");
    // The byte map's certificate and the jump facts (elf64_read_map's
    // `MapByte` and `MapJumpFacts`).
    module.raw(format!("\
fn {prefix}_map_byte() → MapByte({f}) {{
    MapByte({m}_code(), {m}_Protected, λ before b placed => {m}_typed_artifact(b, before, placed),
        MapKeeps(trivial, trivial, trivial, trivial, trivial))
}}
fn {prefix}_jump_facts() → MapJumpFacts(structured_bytes({m}_code()).len(), {jumps}, {pj}) {{
    MapJumpFacts({prefix}_exit_reads(), {prefix}_fail_reads(), {prefix}_again_closes(), {prefix}_retry_closes(),
        {prefix}_write_fail_reads(), {prefix}_write_read_closes(), {prefix}_write_back_closes(), {prefix}_write_retry_closes())
}}
"));
    let proof = format!("read_map_runs({prefix}_file(), {f}, {prefix}_map_byte(), {jumps}, {pj}, {prefix}_jump_facts(),
        {prefix}_resident(), steps, ok, ending, ending_ok, page, gprs, flags)");
    claims(module, prefix, &format!("\
// The process claim for the written file: for every way the reads may split
// stdin into non-empty chunks, with EINTRs between them, and every way each
// chunk's writes may return (short counts and EINTRs), ending at the empty
// read or at a failed read or write, a run that reads each chunk and writes
// its image under `{f}` to stdout, then exits 0, or exits 1 at the failure.
// There is no bound on the input."), &premises, &events, &proof);
    module.raw(format!("\
// What stdout receives on a run that ends at the empty read: the input,
// mapped byte by byte.
theorem {prefix}_sends(steps: List<EofStep<List<WriteStep>>>, ok: MapSteps({f}, steps)):
    sent_to(@bitvec::BitVec::ofNat(64, 1), map_events({f}, steps, AtEnd)) = map_input(steps).map({f}) {{
    map_sends({f}, steps, ok)
}}
"));
    Ok(file)
}
