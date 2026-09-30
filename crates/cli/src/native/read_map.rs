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

use super::layout::JNZ;
use super::read_loop::{claims, copy, fail_tail, image_facts, mov, nested, print_jumps, read_head, write_loop};

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
    let m = &piece.prefix;
    // The head's JZ at end of file goes to the write loop's exit(0), its JS to
    // the failure tail; the chunk is mapped in place (MOVZX RAX, byte [RSI]
    // and MOV byte [RSI], DL: the library's ByteLoad and ByteStore, checked
    // against the model's encodings), JNZ back to the load, then written, and
    // the write loop's all-sent JZ goes back to the read.
    let layout = read_head("wexit", "failed")
        .fixed("setup", encode(&[mov(Rsi, 0x410000), mov(R9, 0x410000), copy(Rcx, Rax), copy(R10, Rax), mov(R11, 1)]))
        .label("load").fixed("load", vec![0x48, 0x0f, 0xb6, 0x06])
        .generated("map", format!("{m}_lit()"), piece.bytes.clone())
        .fixed("store", vec![0x40, 0x88, 0x16])
        .fixed("step", encode(&[Instruction::AddRR { destination: Rsi, source: R11 }, Instruction::SubRR { destination: Rcx, source: R11 }]))
        .jump("jnz", JNZ, "load")
        .then(write_loop("read"))
        .then(fail_tail("failed", "rjz", "read"));
    let code = layout.code();
    let file = super::calls::io_image(&code)?;

    layout.declare(module, prefix);
    let d = |jump| format!("@bitvec::BitVec::ofNat(32, {})", layout.displacement(jump));
    module.raw(format!("fn {prefix}_jumps() → MapJumps {{ MapJumps({}, {}, {}, {}) }}", d("jz"), d("js"), d("jnz"), d("rjz")));
    print_jumps(module, prefix, &layout);

    let pj = format!("{prefix}_print_jumps()");
    let jumps = format!("{prefix}_jumps()");
    let code_term = format!("map_code({m}_code(), {jumps}, {pj})");
    let spelled = |mapped: &str| nested(&layout.spelled_with(prefix, &[("map", mapped)]));
    // The code as written: fixed pieces by evaluation, the byte map's bytes
    // by its lemma. Its length the same way (map_code_len).
    let chain = format!("j({m}_bytes_are(), λ y _ => {code_term} = {}, refl)", spelled("y"));
    let measure = format!("map_code_len({m}_code(), {jumps}, {pj}, {}, {m}_byte_length())", piece.bytes.len());
    image_facts(module, prefix, &code_term, &spelled(&format!("{m}_lit()")), &chain, &file, code.len(), &measure);
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
// Where the jumps land, from the written displacements: closed facts once
// the byte map's length is its lemma's.
fn {prefix}_jump_facts() → MapJumpFacts(structured_bytes({m}_code()).len(), {jumps}, {pj}) {{
    j(sym({m}_byte_length()), λ n _ => MapJumpFacts(n, {jumps}, {pj}), MapJumpFacts(refl, refl, refl, refl, WriteJumpFacts(refl, refl, refl), refl))
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
