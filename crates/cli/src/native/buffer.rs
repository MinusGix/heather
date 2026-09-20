//! Fixed-buffer cursor export. The host supplies storage; generated code owns
//! the bounds check, byte load, source classifier, and cursor update.
use super::*;
use heather_elab::heather_emit::Parameter;

fn declaration(module: &mut Module, name: &str, ty: &str, body: &str, theorem: bool) {
    let d = if theorem { Declaration::theorem(name, Expr::raw(ty), Block::expression(Expr::raw(body))) }
        else { Declaration::function(name, Expr::raw(ty), Block::expression(Expr::raw(body))) };
    module.declaration(d.generic("M")
        .parameter(Parameter::explicit("access", Expr::raw("BufferAccess<M>")))
        .parameter(Parameter::explicit("before", Expr::raw("MachineState<M>"))));
}

pub(super) fn generate(elab: &Elaborator, module: &mut Module, prefix: &str, source: &str) -> Result<Vec<u8>, String> {
    let body = format!("{prefix}_classifier");
    let emission = function_ir_source::generate_elaborated_x86(elab, &body, source,
        [Gpr::Rdi, Gpr::Rsi], &[Gpr::Rax, Gpr::Rcx, Gpr::R8, Gpr::R9, Gpr::R10, Gpr::R11], Gpr::Rax)
        .map_err(|e| e.to_string())?;
    let body_bytes = encode(&emission.instructions);
    let skip = 50 + body_bytes.len();
    if skip > 127 { return Err("buffer-cursor classifier exceeds the forward short-branch span".into()); }
    module.raw("import byte_cursor;\nimport x86_64_buffer_cursor;");
    module.raw(emission.text);
    let ordinary = |instructions: &[Instruction]| encode(instructions);
    let mut bytes = ordinary(&[Instruction::CmpRR { left: Gpr::Rdx, right: Gpr::Rsi }]);
    bytes.extend([0x73, skip as u8]);
    bytes.extend([0x48, 0x0f, 0xb6, 0x3c, 0x17]);
    bytes.extend(ordinary(&[Instruction::MovRR { destination: Gpr::Rsi, source: Gpr::Rdx }]));
    bytes.extend(&body_bytes);
    bytes.extend([0x48, 0x85, 0xc0]);
    bytes.extend([0x74, 12]);
    bytes.extend(ordinary(&[Instruction::MovRI { destination: Gpr::Rax, immediate: 1 }]));
    bytes.extend([0xeb, 35]);
    bytes.extend(ordinary(&[Instruction::MovRI { destination: Gpr::Rax, immediate: 0 },
        Instruction::MovRI { destination: Gpr::Rcx, immediate: 1 },
        Instruction::AddRR { destination: Gpr::Rdx, source: Gpr::Rcx }]));
    bytes.extend([0xeb, 10]);
    bytes.extend(ordinary(&[Instruction::MovRI { destination: Gpr::Rax, immediate: 2 }]));
    let expected = format!("canonical_block_bytes(cursor_guard()) ++ jump_not_below_bytes(bitvec::ofNat(8, {skip})) ++ load_cursor_byte_bytes() ++ canonical_block_bytes(cursor_prepare()) ++ {body}_bytes() ++ canonical_block_bytes(cursor_test()) ++ short_control_bytes(JumpZero(bitvec::ofNat(8, 12))) ++ canonical_block_bytes(cursor_miss()) ++ short_control_bytes(Jump(bitvec::ofNat(8, 35))) ++ canonical_block_bytes(cursor_hit()) ++ short_control_bytes(Jump(bitvec::ofNat(8, 10))) ++ canonical_block_bytes(cursor_empty())");
    let literal = format!("[{}]", bytes.iter().map(|b| format!("bitvec::ofNat(8, {b})")).collect::<Vec<_>>().join(", "));
    module.raw(format!("theorem {prefix}_exported_bytes(): {expected} = {literal} {{ refl }}"));
    let state = |name: &str| format!("{prefix}_{name}(access, before)");
    for (name, expr) in [
        ("guard", "execute_block_normal(cursor_guard(), before)".into()),
        ("branch", format!("jump_not_below(bitvec::ofNat(8, {skip}), {})", state("guard"))),
        ("loaded", format!("load_cursor_byte(access, {})", state("branch"))),
        ("ready", format!("execute_block_normal(cursor_prepare(), {})", state("loaded"))),
        ("body", format!("{body}_after({})", state("ready"))),
        ("present", format!("cursor_tail({})", state("body"))),
        ("empty", format!("execute_block_normal(cursor_empty(), {})", state("branch"))),
        ("after", format!("match {}.flags.cf {{ False => {}, True => {} }}", state("guard"), state("empty"), state("present"))),
    ] { declaration(module, &format!("{prefix}_{name}"), "MachineState<M>", &expr, false); }
    let cursor = "read_gpr(Rdx, before.gprs)";
    let length = "read_gpr(Rsi, before.gprs)";
    let byte = "access.read(before.memory, byte_address(before))";
    let result = format!("{source}(bitvec::zero_extend(8, 56, {byte}), {cursor})");
    // Reuse the source/FunctionIR theorem over arbitrary loaded bytes, rather
    // than reducing the source and selected register program together.
    elf::valuation_with_parameters(module, &format!("{prefix}_input"), &body,
        &emission.reflected.region, [
            Expr::raw("bitvec::ofNat(width, bitvec::toNat(64, left))"),
            Expr::raw("bitvec::ofNat(width, bitvec::toNat(64, right))"),
        ], &[("left", "BitVec(64)"), ("right", "BitVec(64)")])?;
    let left = format!("bitvec::zero_extend(8, 56, {byte})");
    let values = format!("{prefix}_input_values({left}, {cursor})");
    let source_result = format!("trans({body}_refines_function_ir({values}, {}, bitvec::ofNat_toNat(64, {left}), bitvec::ofNat_toNat(64, {cursor}), {prefix}_input_entry_graph({left}, {cursor})), {body}_denotes_source({values}, {prefix}_input_entry_graph({left}, {cursor})))", state("ready"));
    let normalized = format!("trans(cong_fn<BitVec(64), BitVec(64)>(λ left => {source}(left, {values}(64, 1)), bitvec::ofNat_toNat(64, {left})), cong_fn<BitVec(64), BitVec(64)>(λ right => {source}({left}, right), bitvec::ofNat_toNat(64, {cursor})))");
    declaration(module, &format!("{prefix}_body_result"),
        &format!("read_gpr(Rax, {}.gprs) = {result}", state("body")), &format!("trans({source_result}, {normalized})"), true);
    declaration(module, &format!("{prefix}_body_cursor"),
        &format!("read_gpr(Rdx, {}.gprs) = {cursor}", state("body")), "refl", true);
    declaration(module, &format!("{prefix}_present_result"),
        &format!("cursor_observe({}) = recognized(classifier_accepts({result}), {cursor})", state("present")),
        &format!("trans(cursor_tail_observation({}), trans(cong_fn<BitVec(64), CursorReply>(λ value => recognized(classifier_accepts(value), read_gpr(Rdx, {}.gprs)), {prefix}_body_result(access, before)), cong_fn<BitVec(64), CursorReply>(λ cursor => recognized(classifier_accepts({result}), cursor), {prefix}_body_cursor(access, before))))", state("body"), state("body")), true);
    let spec = format!("recognize({length}, λ cursor => access.read(before.memory, bitvec::add(64, read_gpr(Rdi, before.gprs), cursor)), {cursor}, λ byte => classifier_accepts({source}(bitvec::zero_extend(8, 56, byte), {cursor})))");
    declaration(module, &format!("{prefix}_recognizes"), &format!("cursor_observe({}) = {spec}", state("after")),
        &format!("cursor_selection_observation(bitvec::unsigned_lt_bit(64, {cursor}, {length}), {}, {}, recognized(classifier_accepts({result}), {cursor}), {cursor}, {prefix}_present_result(access, before), refl)", state("present"), state("empty")), true);
    declaration(module, &format!("{prefix}_present_memory"), &format!("{}.memory = before.memory", state("present")),
        &format!("trans(cursor_tail_memory({}), {body}_preserves_memory({}))", state("body"), state("ready")), true);
    declaration(module, &format!("{prefix}_memory_preserved"), &format!("{}.memory = before.memory", state("after")),
        &format!("cursor_selection_preserves(bitvec::unsigned_lt_bit(64, {cursor}, {length}), {}, {}, λ state => state.memory, before.memory, {prefix}_present_memory(access, before), refl)", state("present"), state("empty")), true);
    for r in [Gpr::Rbx, Gpr::Rbp, Gpr::Rsp, Gpr::R12, Gpr::R13, Gpr::R14, Gpr::R15] {
        let register = r.heather_name();
        declaration(module, &format!("{prefix}_present_{register}"),
            &format!("read_gpr({register}, {}.gprs) = read_gpr({register}, before.gprs)", state("present")),
            &format!("trans(cursor_tail_register({}, {register}, trivial), {body}_preserves_protected({register}, {}, trivial))", state("body"), state("ready")), true);
        declaration(module, &format!("{prefix}_preserves_{register}"),
            &format!("read_gpr({register}, {}.gprs) = read_gpr({register}, before.gprs)", state("after")),
            &format!("cursor_selection_preserves(bitvec::unsigned_lt_bit(64, {cursor}, {length}), {}, {}, λ state => read_gpr({register}, state.gprs), read_gpr({register}, before.gprs), {prefix}_present_{register}(access, before), refl)", state("present"), state("empty")), true);
    }
    // A load premise is conditional on the very flag that selects that path.
    module.raw(format!("theorem {prefix}_read_allowed<M>(access: BufferAccess<M>, before: MachineState<M>, readable: BufferReadable(access, before), selected: {}.flags.cf = True): ExecuteCursorLoad(access, {}, {}) {{ ⟨readable(selected), refl⟩ }}", state("guard"), state("branch"), state("loaded")));
    module.raw(format!("fn {prefix}_execution<M>(access: BufferAccess<M>, before: MachineState<M>, readable: BufferReadable(access, before)) -> CursorExecution<M>(access, {body}_instructions(), bitvec::ofNat(8, {skip}), before, {}) {{ CursorExecution(middle := {}, guard := canonical_block_executes_normal(cursor_guard(), before), load := λ selected => {prefix}_read_allowed(access, before, readable, selected), prepare := canonical_block_executes_normal(cursor_prepare(), {}), body := {body}_block_is_allowed({}), tail := cursor_tail_trace({}), empty := canonical_block_executes_normal(cursor_empty(), {}), selected := refl) }}", state("after"), state("body"), state("loaded"), state("ready"), state("body"), state("branch")));
    // The static branch targets are checked for an arbitrary code address.
    for (label, offset, delta, target) in [("empty_target", 3, skip, skip+5),
        ("hit_target", 16+body_bytes.len(), 12, 30+body_bytes.len()),
        ("miss_join", 28+body_bytes.len(), 35, bytes.len()),
        ("hit_join", 53+body_bytes.len(), 10, bytes.len())] {
        module.raw(format!("fn {prefix}_{label}_offset() -> Nat {{ {target} }}"));
        module.raw(format!("theorem {prefix}_{label}_span(): ({offset} + 2) + {delta} = {prefix}_{label}_offset() {{ refl }}"));
        module.raw(format!("theorem {prefix}_{label}(start: BitVec(64)): short_branch_target(next_rip(start, {offset}), bitvec::ofNat(8, {delta})) = next_rip(start, {prefix}_{label}_offset()) {{ trans(cursor_forward_target(start, {offset}, bitvec::ofNat(8, {delta}), {delta}, refl), cong_fn<Nat, BitVec(64)>(λ count => next_rip(start, count), {prefix}_{label}_span())) }}"));
    }
    let middle_end = 13 + body_bytes.len();
    let mut advance = "refl".to_string();
    let mut offset = 0;
    for instruction in &emission.instructions {
        let length = instruction.canonical_length();
        advance = if offset == 0 { format!("bitvec::iterate_increment_compose(64, start, 0, {length})") }
            else { format!("trans(bitvec::cong_iterate_increment(64, {length}, {advance}), bitvec::iterate_increment_compose(64, start, {offset}, {length}))") };
        offset += length;
    }
    module.raw(format!("theorem {prefix}_body_span(start: BitVec(64)): {body}_final_rip(start) = next_rip(start, {}) {{ {advance} }}", body_bytes.len()));
    module.raw(format!("theorem {prefix}_ready_rip<M>(access: BufferAccess<M>, before: MachineState<M>, selected: {}.flags.cf = True): {}.rip = next_rip(before.rip, 13) {{
        trans(cong_fn<Bool, BitVec(64)>(λ flag => (cursor_ready_selected(access, flag, bitvec::ofNat(8, {skip}), before)).rip, selected), cursor_ready_true_rip(access, bitvec::ofNat(8, {skip}), before))
    }}", state("guard"), state("ready")));
    module.raw(format!("theorem {prefix}_middle_rip<M>(access: BufferAccess<M>, before: MachineState<M>, selected: {}.flags.cf = True): {}.rip = next_rip(before.rip, {middle_end}) {{
        trans({body}_advances_rip({}), trans({prefix}_body_span({}.rip),
            trans(bitvec::cong_iterate_increment(64, {}, {prefix}_ready_rip(access, before, selected)), bitvec::iterate_increment_compose(64, before.rip, 13, {}))))
    }}", state("guard"), state("body"), state("ready"), state("ready"), body_bytes.len(), body_bytes.len()));
    module.raw(format!("theorem {prefix}_present_rip<M>(access: BufferAccess<M>, before: MachineState<M>, selected: {}.flags.cf = True): {}.rip = next_rip(before.rip, {}) {{
        trans(cursor_tail_rip({}), trans(bitvec::cong_iterate_increment(64, 52, {prefix}_middle_rip(access, before, selected)), bitvec::iterate_increment_compose(64, before.rip, {middle_end}, 52)))
    }}", state("guard"), state("present"), bytes.len(), state("body")));
    module.raw(format!("theorem {prefix}_empty_rip<M>(access: BufferAccess<M>, before: MachineState<M>, selected: {}.flags.cf = False): {}.rip = next_rip(before.rip, {}) {{
        trans(cong_fn<Bool, BitVec(64)>(λ flag => (execute_block_normal(cursor_empty(), cursor_guarded_selected(flag, bitvec::ofNat(8, {skip}), before))).rip, selected),
            trans(bitvec::cong_iterate_increment(64, 10, {prefix}_empty_target(before.rip)), bitvec::iterate_increment_compose(64, before.rip, {}, 10)))
    }}", state("guard"), state("empty"), bytes.len(), bytes.len()-10));
    declaration(module, &format!("{prefix}_ends_at_return"), &format!("{}.rip = next_rip(before.rip, {})", state("after"), bytes.len()),
        &format!("cursor_selection_guarded({}.flags.cf, {}, {}, λ state => state.rip, next_rip(before.rip, {}), λ selected => {prefix}_present_rip(access, before, selected), λ selected => {prefix}_empty_rip(access, before, selected))", state("guard"), state("present"), state("empty"), bytes.len()), true);
    Ok(bytes)
}
