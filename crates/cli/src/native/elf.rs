//! Restricted ELF layout producer. Header bytes and code spans are checked
//! against lib/elf64.hthr and the canonical x86 model before publication.
use heather_elab::function_ir_cert::{Node, Region};
use heather_elab::function_ir_source::SourceX86Emission;
use heather_elab::function_ir_x86_lower::{Gpr, Instruction};
use heather_elab::heather_emit::{Block, Declaration, Expr, Module, Parameter};

const HEADER_SIZE: usize = 64 + 2 * 56;
const LOAD_BASE: u64 = 0x400000;

pub(super) fn parse_argument(text: &str) -> Result<u64, String> {
    let (radix, digits) = if let Some(s) = text.strip_prefix("0x") { (16, s) }
        else if let Some(s) = text.strip_prefix("0b") { (2, s) }
        else { (10, text) };
    if digits.is_empty() || !digits.chars().all(|c| c.is_digit(radix)) {
        return Err(format!("invalid unsigned integer `{text}` (decimal, 0x hex, or 0b binary)"));
    }
    u64::from_str_radix(digits, radix).map_err(|_| format!("argument `{text}` exceeds u64"))
}

fn image(code: &[u8]) -> Result<Vec<u8>, String> {
    if code.is_empty() { return Err("ELF entry must point to code inside the load segment".into()); }
    let size = HEADER_SIZE.checked_add(code.len()).ok_or("ELF size overflow")?;
    if size > u16::MAX as usize {
        return Err("the initial ELF64 profile supports files up to 65535 bytes".into());
    }
    let mut bytes = Vec::with_capacity(size);
    bytes.extend(b"\x7fELF\x02\x01\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00");
    bytes.extend(2u16.to_le_bytes()); // ET_EXEC
    bytes.extend(62u16.to_le_bytes()); // EM_X86_64
    bytes.extend(1u32.to_le_bytes());
    bytes.extend((LOAD_BASE + HEADER_SIZE as u64).to_le_bytes());
    bytes.extend(64u64.to_le_bytes()); // program header offset
    bytes.extend(0u64.to_le_bytes()); // no section table
    bytes.extend(0u32.to_le_bytes());
    for field in [64u16, 56, 2, 0, 0, 0] { bytes.extend(field.to_le_bytes()); }
    // A single read/execute mapping, with file offset and address congruent
    // modulo 4096. Header and code share it; p_memsz equals p_filesz.
    bytes.extend(1u32.to_le_bytes());
    bytes.extend(5u32.to_le_bytes());
    for field in [0, LOAD_BASE, LOAD_BASE, size as u64, size as u64, 4096] {
        bytes.extend(field.to_le_bytes());
    }
    bytes.extend(0x6474e551u32.to_le_bytes()); // PT_GNU_STACK
    bytes.extend(6u32.to_le_bytes()); // RW, not executable
    for field in [0u64, 0, 0, 0, 0, 16] { bytes.extend(field.to_le_bytes()); }
    assert_eq!(bytes.len(), HEADER_SIZE);
    bytes.extend(code);
    Ok(bytes)
}

fn byte_list(bytes: &[u8]) -> Expr {
    Expr::list(bytes.iter().map(|b| Expr::call("bitvec::ofNat", [Expr::nat(8), Expr::nat(u64::from(*b))])))
}

fn function(module: &mut Module, name: &str, ty: &str, body: Expr) {
    module.declaration(Declaration::function(name, Expr::raw(ty), Block::expression(body)));
}

fn theorem(module: &mut Module, name: &str, ty: Expr, body: Expr) {
    module.declaration(Declaration::theorem(name, ty, Block::expression(body)));
}

fn machine_theorem(module: &mut Module, name: &str, ty: String, body: String) {
    module.declaration(Declaration::theorem(name, Expr::raw(ty), Block::expression(Expr::raw(body)))
        .generic("M").parameter(Parameter::explicit("before", Expr::name("MachineState<M>"))));
}

// A valuation built from the actual graph, at an arbitrary width. It gives
// each node a named expression, so the concrete graph witness is a chain of
// reflexivity proofs; no unproved RegionHolds assumption remains at entry.
fn valuation(module: &mut Module, prefix: &str, region: &Region, inputs: [u64; 2]) -> Result<(), String> {
    let value_name = |id| format!("{prefix}_value_{id}");
    let value = |id| Expr::call(value_name(id), [Expr::name("width")]);
    let mut declarations = vec![(0, Expr::call("bitvec::ofNat", [Expr::name("width"), Expr::nat(inputs[0])])),
        (1, Expr::call("bitvec::ofNat", [Expr::name("width"), Expr::nat(inputs[1])]))];
    for &node in &region.nodes {
        let expr = match node {
            Node::Const { value: constant, .. } => Expr::call("bitvec::ofNat", [Expr::name("width"), Expr::nat(constant)]),
            Node::Add { left, right, .. } => Expr::call("bitvec::add", [Expr::name("width"), value(left), value(right)]),
            Node::Sub { left, right, .. } => Expr::call("bitvec::sub", [Expr::name("width"), value(left), value(right)]),
            Node::BitAnd { left, right, .. } => Expr::call("bitvec::band", [Expr::name("width"), value(left), value(right)]),
            Node::BitOr { left, right, .. } => Expr::call("bitvec::bor", [Expr::name("width"), value(left), value(right)]),
            Node::BitXor { left, right, .. } => Expr::call("bitvec::bxor", [Expr::name("width"), value(left), value(right)]),
            _ => return Err("unsupported source node in ELF entry valuation".into()),
        };
        declarations.push((node.output().id, expr));
    }
    let ids: Vec<u64> = declarations.iter().map(|(id, _)| *id).collect();
    for (id, body) in declarations {
        module.declaration(Declaration::function(value_name(id), Expr::name("BitVec(width)"), Block::expression(body))
            .parameter(Parameter::explicit("width", Expr::name("Nat"))));

    }
    let mut cases = "bitvec::ofNat(width, 0)".to_string();
    let last = *ids.iter().max().unwrap();
    for id in (0..=last).rev() {
        let scrutinee = if id == 0 { "id".into() } else { format!("id_{id}") };
        let tail = if id == last { "_".into() } else { format!("id_{}", id + 1) };
        let here = if ids.contains(&id) { format!("{}(width)", value_name(id)) }
            else { "bitvec::ofNat(width, 0)".into() };
        cases = format!("match {scrutinee} {{ Zero => {here}, Succ({tail}) => {cases} }}");
    }
    function(module, &format!("{prefix}_values"), "Valuation()",
        Expr::raw(format!("λ width id => {cases}")));
    let mut graph = "trivial".to_string();
    for _ in &region.nodes { graph = format!("⟨refl, {graph}⟩"); }
    theorem(module, &format!("{prefix}_entry_graph"),
        Expr::raw(format!("RegionHolds({prefix}_raw(), {prefix}_values())")), Expr::raw(graph));
    Ok(())
}

pub(super) fn certify(module: &mut Module, prefix: &str, emission: &SourceX86Emission,
    inputs: [u64; 2], body: &[u8]) -> Result<Vec<u8>, String>
{

    let entry = super::encode(&[
        Instruction::MovRI { destination: Gpr::Rdi, immediate: inputs[0] },
        Instruction::MovRI { destination: Gpr::Rsi, immediate: inputs[1] },
    ]);
    let exit = super::encode(&[
        Instruction::MovRR { destination: Gpr::Rdi, source: Gpr::Rax },
        Instruction::MovRI { destination: Gpr::Rax, immediate: 60 },
    ]);
    let mut code = entry.clone();
    code.extend(body);
    code.extend(&exit);
    code.extend([0x0f, 0x05]);
    let bytes = image(&code)?;
    let left = format!("bitvec::ofNat(64, {})", inputs[0]);
    let right = format!("bitvec::ofNat(64, {})", inputs[1]);
    let begin = format!("linux_entry_state({left}, {right}, before)");
    let after = format!("{prefix}_after({begin})");
    let result = format!("{}({left}, {right})", emission.reflected.source_name);
    valuation(module, prefix, &emission.reflected.region, inputs)?;
    machine_theorem(module, &format!("{prefix}_exit_request"),
        format!("LinuxExitRequest<M>(linux_exit_state({after}), {result})"),
        format!("LinuxExitRequest(number := linux_exit_number({after}),\nstatus := trans(linux_exit_value({after}),\ntrans({prefix}_refines_function_ir({prefix}_values(), {begin}, refl, refl, {prefix}_entry_graph()),\n{prefix}_denotes_source({prefix}_values(), {prefix}_entry_graph()))))"));
    machine_theorem(module, &format!("{prefix}_inline_trace"),
        format!("LinuxInlineTrace<M>({prefix}_instructions(), {left}, {right}, before, {result})"),
        format!("LinuxInlineTrace(after_body := {after},\nentry_execution := linux_entry_executes({left}, {right}, before),\nbody_execution := {prefix}_block_is_allowed({begin}),\nexit_execution := linux_exit_executes({after}),\nrequest := {prefix}_exit_request(before))"));

    // Exact emitted spans. The body uses the already checked native byte
    // theorem; the other spans acquire independent canonical byte equalities.
    for (suffix, actual, expected) in [
        ("entry_bytes", entry.as_slice(), format!("canonical_block_bytes(linux_entry_instructions({left}, {right}))")),
        ("exit_bytes", exit.as_slice(), "canonical_block_bytes(linux_exit_instructions())".into()),
        ("syscall_bytes", &[0x0f, 0x05][..], "linux_syscall_bytes()".into()),
    ] {
        function(module, &format!("{prefix}_{suffix}"), "List<BitVec(8)>", byte_list(actual));
        theorem(module, &format!("{prefix}_{suffix}_correct"), Expr::equal(
            Expr::nullary(format!("{prefix}_{suffix}")), Expr::raw(expected)), Expr::name("refl"));
    }
    function(module, &format!("{prefix}_image_code"), "List<BitVec(8)>", byte_list(&bytes[HEADER_SIZE..]));
    theorem(module, &format!("{prefix}_image_code_layout"),
        Expr::raw(format!("{prefix}_image_code() = {prefix}_entry_bytes() ++ {prefix}_bytes() ++ {prefix}_exit_bytes() ++ {prefix}_syscall_bytes()")),
        Expr::name("refl"));
    function(module, &format!("{prefix}_elf_image"), &format!("StaticElf64Image({prefix}_image_code())"),
        Expr::named_call("StaticElf64Image", [
            ("code_nonempty", Expr::name("trivial")),
            ("size_low", Expr::call("elf_byte", [Expr::nat((bytes.len() & 255) as u64)])),
            ("size_high", Expr::call("elf_byte", [Expr::nat((bytes.len() >> 8) as u64)])),
            ("file_size_correct", Expr::name("refl")),
        ]));
    // Avoid duplicating the payload in the source while still taking every
    // header byte from the exact Vec that will be written to disk.
    function(module, &format!("{prefix}_elf_header"), "List<BitVec(8)>", byte_list(&bytes[..HEADER_SIZE]));
    function(module, &format!("{prefix}_elf_file"), "List<BitVec(8)>",
        Expr::raw(format!("{prefix}_elf_header() ++ {prefix}_image_code()")));
    theorem(module, &format!("{prefix}_elf_file_correct"), Expr::raw(format!(
        "{prefix}_elf_file() = static_elf64_bytes({prefix}_elf_image())")), Expr::name("refl"));
    theorem(module, &format!("{prefix}_elf_entry_code"), Expr::raw(format!(
        "list::drop({prefix}_elf_file(), 176) = {prefix}_image_code()")),
        Expr::call("static_elf64_entry_bytes", [Expr::nullary(format!("{prefix}_elf_image"))]));
    Ok(bytes)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn elf_header_mutations_are_rejected_by_heather() {
        use heather_elab::Elaborator;
        use heather_cli::{loader, semantic::SemanticSession};
        use std::path::PathBuf;
        let mut elab = Elaborator::with_prelude().unwrap();
        let mut session = SemanticSession::new(Some(PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/../../target/native-test-images"))));
        for &(name, src) in super::super::SUPPORT {
            super::super::check_module(&mut elab, &mut session, &loader::Module {
                name: name.into(), path: PathBuf::from(name), src: src.into(),
            }).unwrap();
        }
        let good = image(&[0x0f, 0x05]).unwrap();
        // Identity/class/endian/type/machine/entry/table offsets and sizes,
        // segment permissions/mapping/file bounds/alignment, and stack policy.
        let mutations = [0, 4, 5, 16, 18, 24, 32, 40, 48, 50, 52, 54, 56, 58,
            60, 62, 64, 68, 72, 80, 88, 96, 104, 112, 120, 124, 168];
        for changed in std::iter::once(None).chain(mutations.into_iter().map(Some)) {
            let mut bytes = good.clone();
            if let Some(offset) = changed { bytes[offset] ^= 1; }
            let mut proof = Module::default();
            proof.raw("import elf64;\nimport bitvec;\nimport list;");
            function(&mut proof, "actual_header", "List<BitVec(8)>", byte_list(&bytes[..HEADER_SIZE]));
            theorem(&mut proof, "header_agrees", Expr::equal(Expr::nullary("actual_header"),
                Expr::call("static_elf64_header", [Expr::call("elf_byte", [Expr::nat(good.len() as u64)]),
                    Expr::call("elf_byte", [Expr::nat(0)])])), Expr::name("refl"));
            let text = proof.render();
            let checked = elab.clone().elab_module_source("elf_header_test", &text);
            if changed.is_some() {
                let error = checked.expect_err("malformed header must be rejected");
                assert!(format!("{error:?}").contains("NotConvertible"), "{changed:?}: {}", error.render(&text));
            } else { checked.unwrap_or_else(|e| panic!("{}", e.render(&text))); }
        }
    }

    #[test]
    fn image_bounds_and_argument_errors() {
        assert!(image(&[]).is_err());
        assert!(image(&vec![0; 65535 - HEADER_SIZE]).is_ok());
        assert!(image(&vec![0; 65536 - HEADER_SIZE]).is_err());
        assert_eq!(parse_argument("0x2a"), Ok(42));
        assert_eq!(parse_argument("0b101010"), Ok(42));
        for bad in ["", "-1", "+1", "0x", "0b2", "18446744073709551616"] {
            assert!(parse_argument(bad).is_err(), "{bad}");
        }
    }
}
