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

pub(super) fn image(code: &[u8]) -> Result<Vec<u8>, String> {
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

fn loaded_address(offset: usize) -> String {
    let bits = (0..16).map(|bit| if offset & (1 << bit) == 0 { "False" } else { "True" })
        .collect::<Vec<_>>().join(", ");
    format!("static_elf64_address(bitvec::from_bits(16, [{bits}]))")
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
pub(super) fn valuation(module: &mut Module, prefix: &str, region: &Region, inputs: [u64; 2]) -> Result<(), String> {
    valuation_expressions(module, prefix, prefix, region, [
        Expr::call("bitvec::ofNat", [Expr::name("width"), Expr::nat(inputs[0])]),
        Expr::call("bitvec::ofNat", [Expr::name("width"), Expr::nat(inputs[1])]),
    ])
}

pub(super) fn valuation_expressions(module: &mut Module, prefix: &str, graph_prefix: &str,
    region: &Region, inputs: [Expr; 2]) -> Result<(), String> {
    let value_name = |id| format!("{prefix}_value_{id}");
    let value = |id| Expr::call(value_name(id), [Expr::name("width")]);
    let [left, right] = inputs;
    let mut declarations = vec![(0, left), (1, right)];
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
        Expr::raw(format!("RegionHolds({graph_prefix}_raw(), {prefix}_values())")), Expr::raw(graph));
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
    // Chains of named suffixes rather than `[…]` literals, and one forward
    // pass naming every `drop` of the code: a byte lookup below is then a
    // step, not a re-traversal of the file (see `super::byte_chain`).
    super::byte_chain(module, &format!("{prefix}_image_code"), &bytes[HEADER_SIZE..]);
    super::drop_chain(module, &format!("{prefix}_image_code"), bytes.len() - HEADER_SIZE);
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
    super::byte_chain(module, &format!("{prefix}_elf_header"), &bytes[..HEADER_SIZE]);
    theorem(module, &format!("{prefix}_elf_header_length"),
        Expr::raw(format!("{prefix}_elf_header().len() = {HEADER_SIZE}")), Expr::name("refl"));
    function(module, &format!("{prefix}_elf_file"), "List<BitVec(8)>",
        Expr::raw(format!("{prefix}_elf_header() ++ {prefix}_image_code()")));
    theorem(module, &format!("{prefix}_elf_file_correct"), Expr::raw(format!(
        "{prefix}_elf_file() = static_elf64_bytes({prefix}_elf_image())")), Expr::name("refl"));
    theorem(module, &format!("{prefix}_elf_entry_code"), Expr::raw(format!(
        "list::drop({prefix}_elf_file(), 176) = {prefix}_image_code()")),
        Expr::call("static_elf64_entry_bytes", [Expr::nullary(format!("{prefix}_elf_image"))]));
    certify_loaded_trace(module, prefix, &emission.instructions, inputs, &left, &right, &result);
    Ok(bytes)
}

fn certify_loaded_trace(module: &mut Module, prefix: &str, body: &[Instruction],
    inputs: [u64; 2], left: &str, right: &str, result: &str)
{
    function(module, &format!("{prefix}_loaded_image"),
        &format!("StaticElf64Loaded({prefix}_image_code(), {prefix}_elf_file())"),
        Expr::raw(format!("StaticElf64Loaded({prefix}_elf_image(), {prefix}_elf_file_correct())")));
    function(module, &format!("{prefix}_loaded_instructions"), "List<Instruction>",
        Expr::raw(format!("linux_inline_instructions({prefix}_instructions(), {left}, {right})")));
    let mut selected = vec![
        Instruction::MovRI { destination: Gpr::Rdi, immediate: inputs[0] },
        Instruction::MovRI { destination: Gpr::Rsi, immediate: inputs[1] },
    ];
    selected.extend_from_slice(body);
    selected.extend([
        Instruction::MovRR { destination: Gpr::Rdi, source: Gpr::Rax },
        Instruction::MovRI { destination: Gpr::Rax, immediate: 60 },
    ]);
    let parameters = |decl: Declaration| decl
        .parameter(Parameter::explicit("gprs", Expr::name("Gprs")))
        .parameter(Parameter::explicit("flags", Expr::name("Flags")));
    let state = |i| format!("{prefix}_loaded_state_{i}(gprs, flags)");
    let suffix = |i| format!("{prefix}_loaded_suffix_{i}");
    let fetches = |i| format!("{prefix}_loaded_fetches_{i}(gprs, flags)");
    module.declaration(parameters(Declaration::function(format!("{prefix}_loaded_state_0"),
        Expr::raw("MachineState<List<BitVec(8)>>"), Block::expression(Expr::raw(
            format!("static_elf64_initial({prefix}_elf_file(), gprs, flags)"))))));
    let mut offset = HEADER_SIZE;
    for (i, instruction) in selected.iter().enumerate() {
        offset += super::encode(&[*instruction]).len();
        let step = format!("execute_normal(decoded_canonical({}), {})", instruction.render(), state(i));
        // Expose memory and RIP directly so each byte lookup does not expand
        // the preceding register computations. Conversion still checks that
        // this state is the canonical successor when composing the trace.
        module.declaration(parameters(Declaration::function(format!("{prefix}_loaded_state_{}", i + 1),
            Expr::raw("MachineState<List<BitVec(8)>>"), Block::expression(Expr::raw(
                format!("MachineState(gprs := ({step}).gprs, flags := ({step}).flags, rip := {}, memory := {prefix}_elf_file())", loaded_address(offset)))))));
    }
    function(module, &suffix(selected.len()), "List<Instruction>", Expr::list([]));
    for (i, instruction) in selected.iter().enumerate().rev() {
        function(module, &suffix(i), "List<Instruction>", Expr::call("Cons", [
            instruction.heather_expr(), Expr::nullary(suffix(i + 1))]));
    }
    let mut instruction_offset = HEADER_SIZE;
    let spans = selected.iter().map(|instruction| super::encode(&[*instruction]))
        .chain(std::iter::once(vec![0x0f, 0x05]));
    let file = format!("{prefix}_elf_file()");
    for (i, bytes) in spans.enumerate() {
        // The span as a chain of named suffixes, the per-byte premises as
        // named theorems (attributable, and measurably cheaper than inlining
        // them), and the fetch chain nested in one declaration: stating a
        // `FetchedFrom` is work proportional to the span left.
        let span = format!("{prefix}_loaded_span_{i}");
        super::byte_chain(module, &span, &bytes);
        let mut proof = String::new();
        for j in (0..bytes.len()).rev() {
            let address = loaded_address(instruction_offset + j);
            let byte = format!("elf_byte({})", bytes[j]);
            let offset = instruction_offset + j - HEADER_SIZE;
            let fact = |kind| format!("{prefix}_loaded_{kind}_{i}_{j}");
            for (kind, claim, proof) in [
                ("page", format!("is_zero_bits(48, bitvec::bxor(48, bitvec::drop_low(16, 48, {address}), bitvec::ofNat(48, 64))) = True"), "refl".to_string()),
                ("offset", format!("bitvec::toNat(16, bitvec::take_low(16, 48, {address})) = {offset} + {HEADER_SIZE}"), "refl".to_string()),
                ("found", format!("{prefix}_image_code().nth({offset}) = Some({byte})"), super::byte_at(&format!("{prefix}_image_code"), offset)),
                ("read", format!("static_elf64_read({file}, {address}) = Some({byte})"),
                    format!("static_elf64_read_split({prefix}_elf_header(), {prefix}_image_code(), {HEADER_SIZE}, {offset}, {address}, {byte}, {prefix}_elf_header_length(), {}(), {}(), {}())", fact("page"), fact("offset"), fact("found"))),
            ] { theorem(module, &fact(kind), Expr::raw(claim), Expr::raw(proof)); }
            proof = if j + 1 == bytes.len() {
                format!("static_elf64_fetch_one({file}, {address}, {byte}, {}())", fact("read"))
            } else {
                let next = loaded_address(instruction_offset + j + 1);
                for (kind, claim) in [
                    ("no_wrap", format!("bitvec::carry_add_bit(64, {address}, bitvec::ofNat(64, 1)) = False")),
                    ("next", format!("next_rip({address}, 1) = {next}")),
                ] { theorem(module, &fact(kind), Expr::raw(claim), Expr::name("refl")); }
                format!("static_elf64_fetch_more({file}, {address}, {next}, {byte}, elf_byte({}), {span}_from_{}(), {}(), {}(), {}(), {proof})",
                    bytes[j + 1], j + 2, fact("read"), fact("no_wrap"), fact("next"))
            };
        }
        theorem(module, &format!("{prefix}_loaded_byte_{i}_0"),
            Expr::raw(format!("FetchedFrom(static_elf64_access(), {file}, InstructionBytes({}, {span}()))", loaded_address(instruction_offset))),
            Expr::raw(proof));
        instruction_offset += bytes.len();
    }
    let final_state = state(selected.len());
    module.declaration(parameters(Declaration::theorem(format!("{prefix}_loaded_execution_{}", selected.len()),
        Expr::raw(format!("ExecuteFetchedBlock(static_elf64_access(), {}(), {final_state}, {final_state})", suffix(selected.len()))),
        Block::expression(Expr::raw(format!("fetched_block_nil(static_elf64_access(), {final_state})"))))));
    let mut offsets = vec![HEADER_SIZE];
    for instruction in &selected { offsets.push(offsets.last().unwrap() + super::encode(&[*instruction]).len()); }
    for (i, instruction) in selected.iter().enumerate().rev() {
        let before = state(i);
        let middle = state(i + 1);
        let instruction = instruction.render();
        let bytes = format!("{prefix}_loaded_span_{i}()");
        let address = loaded_address(offsets[i]);
        for (name, ty, proof) in [
            (format!("{prefix}_loaded_fetches_{i}"),
                format!("FetchedFrom(static_elf64_access(), ({before}).memory, encoded_at(({before}).rip, {instruction}))"),
                format!("fetched_encoding_at_state(static_elf64_access(), {prefix}_elf_file(), {address}, {bytes}, {instruction}, {before}, refl, refl, refl, {prefix}_loaded_byte_{i}_0())")),
            (format!("{prefix}_loaded_successor_{i}"),
                format!("{middle} = execute_normal(decoded_canonical({instruction}), {before})"), "refl".to_string()),
            (format!("{prefix}_loaded_execution_{i}"),
                format!("ExecuteFetchedBlock(static_elf64_access(), {}(), {before}, {final_state})", suffix(i)),
                format!("fetched_block_cons(static_elf64_access(), {instruction}, {}(), {before}, {middle}, {final_state}, canonical_fetched_step(static_elf64_access(), {instruction}, {before}, {middle}, {}, {prefix}_loaded_successor_{i}(gprs, flags)), {prefix}_loaded_execution_{}(gprs, flags))", suffix(i + 1), fetches(i), i + 1)),
        ] {
            module.declaration(parameters(Declaration::theorem(name, Expr::raw(ty), Block::expression(Expr::raw(proof)))));
        }
    }
    let start = state(0);
    let instructions = format!("{prefix}_loaded_instructions()");
    theorem(module, &format!("{prefix}_loaded_instructions_agree"),
        Expr::raw(format!("{}() = {instructions}", suffix(0))), Expr::name("refl"));
    let original_final = format!("linux_exit_state({prefix}_after(linux_entry_state({left}, {right}, {start})))");
    let reference = |i| format!("{prefix}_loaded_reference_{i}(gprs, flags)");
    let begin = format!("linux_entry_state({left}, {right}, {start})");
    for i in 0..=selected.len() {
        let body = if i == 0 { start.clone() }
            else if i == 1 { format!("execute_normal(decoded_canonical({}), {start})", selected[0].render()) }
            else if i == 2 { begin.clone() }
            else if i <= selected.len() - 2 { format!("{prefix}_state_{}({begin})", i - 2) }
            else if i == selected.len() - 1 { format!("execute_normal(decoded_canonical({}), {prefix}_after({begin}))", selected[i - 1].render()) }
            else { original_final.clone() };
        module.declaration(parameters(Declaration::function(format!("{prefix}_loaded_reference_{i}"),
            Expr::raw("MachineState<List<BitVec(8)>>"), Block::expression(Expr::raw(body)))));
        let proof = if i == 0 { "refl".to_string() } else {
            module.declaration(parameters(Declaration::theorem(format!("{prefix}_loaded_reference_step_{i}"),
                Expr::raw(format!("{} = execute_normal(decoded_canonical({}), {})", reference(i), selected[i - 1].render(), reference(i - 1))),
                Block::expression(Expr::name("refl")))));
            format!("canonical_successor_cong({}, {}, {}, {}, {}, {prefix}_loaded_reference_agrees_{}(gprs, flags), {prefix}_loaded_successor_{}(gprs, flags), {prefix}_loaded_reference_step_{i}(gprs, flags))",
                selected[i - 1].render(), state(i - 1), reference(i - 1), state(i), reference(i), i - 1, i - 1)
        };
        module.declaration(parameters(Declaration::theorem(format!("{prefix}_loaded_reference_agrees_{i}"),
            Expr::raw(format!("{} = {}", state(i), reference(i))), Block::expression(Expr::raw(proof)))));
    }
    module.declaration(parameters(Declaration::theorem(format!("{prefix}_loaded_final_state_agrees"),
        Expr::raw(format!("{original_final} = {final_state}")),
        Block::expression(Expr::raw(format!("sym({prefix}_loaded_reference_agrees_{}(gprs, flags))", selected.len()))))));
    for (name, ty, proof) in [
        ("loaded_execution", format!("ExecuteFetchedBlock(static_elf64_access(), {instructions}, {start}, {final_state})"),
            format!("fetched_block_instructions_cong(static_elf64_access(), {}(), {instructions}, {start}, {final_state}, {prefix}_loaded_instructions_agree(), {prefix}_loaded_execution_0(gprs, flags))", suffix(0))),
        ("loaded_syscall", format!("FetchedFrom(static_elf64_access(), ({final_state}).memory, InstructionBytes(({final_state}).rip, linux_syscall_bytes()))"),
            format!("fetched_span_at_state(static_elf64_access(), {prefix}_elf_file(), {}, {prefix}_loaded_span_{}(), linux_syscall_bytes(), {final_state}, refl, refl, refl, {prefix}_loaded_byte_{}_0())", loaded_address(offsets[selected.len()]), selected.len(), selected.len())),
        ("loaded_request", format!("LinuxExitRequest<List<BitVec(8)>>({final_state}, {result})"),
            format!("linux_exit_request_at_equal_state({original_final}, {final_state}, {result}, {prefix}_loaded_final_state_agrees(gprs, flags), {prefix}_exit_request({start}))")),
    ] {
        module.declaration(parameters(Declaration::theorem(format!("{prefix}_{name}"), Expr::raw(ty), Block::expression(Expr::raw(proof)))));
    }
    module.declaration(parameters(Declaration::theorem(format!("{prefix}_loaded_trace"),
        Expr::raw(format!("LinuxFetchedTrace<List<BitVec(8)>>(static_elf64_access(), {instructions}, {start}, {result})")),
        Block::expression(Expr::raw(format!("LinuxFetchedTrace(after := {final_state},\nexecution := {prefix}_loaded_execution(gprs, flags),\nsyscall_fetched := {prefix}_loaded_syscall(gprs, flags),\nrequest := {prefix}_loaded_request(gprs, flags))"))))));

}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn elf_header_mutations_are_rejected_by_heather() {
        let _guard = super::super::CERTIFICATE_TEST_LOCK.lock().unwrap();
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
    fn loaded_mapping_and_fetch_refusals() {
        let _guard = super::super::CERTIFICATE_TEST_LOCK.lock().unwrap();
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
        let source = r#"
import elf64;
import elf64_load;
import linux_x86_64_entry;
import x86_64;
import x86_64_fetch;
import bitvec;
import bool;
import list;
import option;
import logic;
fn code() -> List<BitVec(8)> {
    canonical_bytes(MovRR(Rax, Rbx)) ++ linux_syscall_bytes()
}
fn image() -> StaticElf64Image(code()) {
    StaticElf64Image(trivial, elf_byte(181), elf_byte(0), refl)
}
fn file() -> List<BitVec(8)> { static_elf64_bytes(image()) }
fn address(n: Nat) -> BitVec(64) { static_elf64_address(bitvec::ofNat(16, n)) }
theorem header_read(): static_elf64_read(file(), address(0)) = Some(elf_byte(127)) { refl }
theorem code_read(): static_elf64_read(file(), static_elf64_entry()) = Some(elf_byte(72)) { refl }
theorem exact_code(): FetchedFrom(static_elf64_access(), file(),
    InstructionBytes(static_elf64_entry(), code())) { FetchedFrom(⟨refl, ⟨refl, ⟨refl, ⟨refl, ⟨refl, ⟨refl, ⟨refl, ⟨refl, ⟨refl, ⟨refl, ⟨refl, ⟨refl, ⟨refl, ⟨refl, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩) }
theorem file_end(): static_elf64_read(file(), address(181)) = None { refl }
theorem end_denied(): fetch_instruction_bytes(static_elf64_access(), file(), 1, address(181))
    = FetchDenied(address(181)) { refl }
theorem below_mapping(): static_elf64_read(file(),
    bitvec::concat(16, 48, bitvec::ofNat(16, 176), bitvec::ofNat(48, 63))) = None { refl }
theorem next_window(): static_elf64_read(file(),
    bitvec::concat(16, 48, bitvec::ofNat(16, 0), bitvec::ofNat(48, 65))) = None { refl }
theorem neutral_byte(byte: BitVec(8)):
    static_elf64_read([byte], address(0)) = Some(byte) { refl }
"#;
        elab.elab_module_source("loaded_checks", source)
            .unwrap_or_else(|e| panic!("{}", e.render(source)));
        for (name, memory, address, expected, access) in [
            ("changed_byte", "static_elf64_header(elf_byte(181), elf_byte(0)) ++ [elf_byte(0), elf_byte(137), elf_byte(216), elf_byte(15), elf_byte(5)]", "static_elf64_entry()", "code()", "static_elf64_access()"),
            ("entry_mismatch", "file()", "address(177)", "code()", "static_elf64_access()"),
            ("wrong_base", "file()", "bitvec::concat(16, 48, bitvec::ofNat(16, 176), bitvec::ofNat(48, 65))", "code()", "static_elf64_access()"),
            ("missing_tail", "static_elf64_header(elf_byte(180), elf_byte(0)) ++ canonical_bytes(MovRR(Rax, Rbx)) ++ [elf_byte(15)]", "static_elf64_entry()", "code()", "static_elf64_access()"),
            ("syscall_mismatch", "static_elf64_header(elf_byte(181), elf_byte(0)) ++ canonical_bytes(MovRR(Rax, Rbx)) ++ [elf_byte(15), elf_byte(4)]", "address(179)", "linux_syscall_bytes()", "static_elf64_access()"),
            ("non_executable", "file()", "static_elf64_entry()", "code()", "FetchAccess<List<BitVec(8)>>(static_elf64_read, λ file address => False)"),
        ] {
            let count = if expected == "linux_syscall_bytes()" { 2 } else { 5 };
            let mut witness = "⟨refl, ⟨refl, trivial⟩⟩".to_string();
            for _ in 1..count { witness = format!("⟨refl, ⟨refl, ⟨refl, {witness}⟩⟩⟩"); }
            let source = format!("import loaded_checks;\nimport elf64;\nimport elf64_load;\nimport linux_x86_64_entry;\nimport x86_64;\nimport x86_64_fetch;\nimport bitvec;\nimport list;\nimport bool;\ntheorem bad(): FetchedFrom({access}, {memory}, InstructionBytes({address}, {expected})) {{ FetchedFrom({witness}) }}");
            let error = elab.clone().elab_module_source(name, &source).expect_err("invalid loaded fetch accepted");
            assert!(format!("{error:?}").contains("NotConvertible"), "{name}: {}", error.render(&source));
        }
        // A valid fetch cannot authorize a successor that leaves RIP unchanged.
        for valid in [true, false] {
            let after = if valid { "execute_normal(decoded_canonical(MovRR(Rax, Rbx)), before())" }
                else { "before()" };
            let source = format!(r#"
import loaded_checks;
import elf64_load;
import x86_64;
import x86_64_fetch;
import x86_64_fetch_block;
import bitvec;
import list;
import logic;
import relation;
fn before() -> MachineState<List<BitVec(8)>> {{
    static_elf64_initial(file(), zero_gprs(), clear_flags())
}}
fn after() -> MachineState<List<BitVec(8)>> {{ {after} }}
theorem step(): ExecuteFetched(static_elf64_access(),
    encoded_at(before().rip, MovRR(Rax, Rbx)), decoded_canonical(MovRR(Rax, Rbx)),
    before(), Returned(after())) {{
    canonical_fetched_step(static_elf64_access(), MovRR(Rax, Rbx), before(), after(),
        FetchedFrom(⟨refl, ⟨refl, ⟨refl, ⟨refl, ⟨refl, ⟨refl, ⟨refl, ⟨refl, trivial⟩⟩⟩⟩⟩⟩⟩⟩), refl)
}}
"#);
            let checked = elab.clone().elab_module_source("loaded_step_check", &source);
            if valid { checked.unwrap_or_else(|e| panic!("{}", e.render(&source))); }
            else {
                let error = checked.expect_err("unadvanced successor accepted");
                assert!(format!("{error:?}").contains("NotConvertible"), "{}", error.render(&source));
            }
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
