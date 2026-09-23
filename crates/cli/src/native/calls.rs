//! Final-image layout and proof producer for bounded callers and reusable leaf summaries.
use std::collections::BTreeMap;
use heather_elab::function_ir_source::{self, SourceX86Emission};
use heather_elab::function_ir_x86_lower::{Gpr, Instruction};
use heather_elab::heather_emit::{Block, Declaration, Expr, Module, Parameter};
use heather_elab::Elaborator;

mod composition;
mod callable;

const ENTRY: u64 = 0x4000e8;
const HEADER: usize = 232;
const STACK_TOP: u64 = 0x402000;

#[derive(Clone, Debug)]
enum Op { Normal(Instruction), Call(String), Ret, Store, StoreArgument, Load, Save(Gpr), Restore(Gpr), Syscall }
impl Op {
    fn len(&self) -> usize { match self { Self::Normal(i) => super::encode(&[*i]).len(), Self::Call(_) => 5, Self::Ret => 1, Self::Store | Self::StoreArgument | Self::Load | Self::Save(_) | Self::Restore(_) => 4, Self::Syscall => 2 } }
}
#[derive(Clone)]
struct Fragment { name: String, ops: Vec<Op> }
struct Layout { bytes: Vec<u8>, symbols: BTreeMap<String, u64>, placed: BTreeMap<u64, (Op, Vec<u8>, String)> }
fn displacement(start: u64, target: u64) -> Result<i32, String> {
    let next = start.checked_add(5).ok_or("relative call address overflow")?;
    i32::try_from(i128::from(target) - i128::from(next)).map_err(|_| "relative call displacement exceeds signed 32 bits".into())
}
fn layout(fragments: &[Fragment]) -> Result<Layout, String> {
    if fragments.is_empty() { return Err("no code fragments".into()); }
    let mut symbols = BTreeMap::new();
    let mut address = ENTRY;
    for fragment in fragments {
        if symbols.insert(fragment.name.clone(), address).is_some() { return Err("duplicate fragment symbol".into()); }
        if fragment.ops.is_empty() { return Err("empty code fragment".into()); }
        for op in &fragment.ops { address = address.checked_add(op.len() as u64).ok_or("code layout overflow")?; }
    }
    if address > 0x401000 { return Err("code overlaps the owned stack page".into()); }
    let mut placed = BTreeMap::new();
    let mut bytes = Vec::new();
    address = ENTRY;
    for fragment in fragments {
        for op in &fragment.ops {
            let (encoded, instruction) = match op {
                Op::Normal(i) => (super::encode(&[*i]), format!("Ordinary({})", i.heather_expr().render())),
                Op::Call(target) => {
                    let target = *symbols.get(target).ok_or_else(|| format!("unresolved call symbol `{target}`"))?;
                    let delta = displacement(address, target)?;
                    let mut encoded = vec![0xe8]; encoded.extend(delta.to_le_bytes());
                    (encoded, format!("CallRelative(@bitvec::BitVec::ofNat(32, {}))", delta as u32))
                }
                Op::Ret => (vec![0xc3], "NearReturn".into()),
                Op::Syscall => (vec![0x0f, 0x05], String::new()),
                Op::Save(r) | Op::Restore(r) => {
                    let register = super::reg(*r);
                    let opcode = if matches!(op, Op::Save(_)) { 0x89 } else { 0x8b };
                    let constructor = if matches!(op, Op::Save(_)) { "StoreStack64" } else { "LoadStack64" };
                    (vec![0x48 | ((register >> 3) << 2), opcode, ((register & 7) << 3) | 4, 0x24], format!("{constructor}({})", r.heather_name()))
                }
                Op::StoreArgument => (vec![0x48, 0x89, 0x3c, 0x24], "StoreStack64(Rdi)".into()),
                Op::Store => (vec![0x4c, 0x89, 0x1c, 0x24], "StoreStack64(R11)".into()),
                Op::Load => (vec![0x4c, 0x8b, 0x1c, 0x24], "LoadStack64(R11)".into()),
            };
            placed.insert(address, (op.clone(), encoded.clone(), instruction));
            address += encoded.len() as u64;
            bytes.extend(encoded);
        }
    }
    Ok(Layout { bytes, symbols, placed })
}
fn selected_leaf_ops(leaf: &SourceX86Emission, clobber: bool, frame: bool) -> Vec<Op> {
    let mut ops = Vec::new();
    if frame {
        ops.extend([Op::Normal(Instruction::MovRR { destination: Gpr::R10, source: Gpr::Rsp }),
            Op::Normal(Instruction::MovRI { destination: Gpr::R11, immediate: 8 }),
            Op::Normal(Instruction::SubRR { destination: Gpr::Rsp, source: Gpr::R11 }), Op::StoreArgument]);
    }
    ops.extend(leaf.instructions.iter().copied().map(Op::Normal));
    if frame { ops.push(Op::Normal(Instruction::MovRR { destination: Gpr::Rsp, source: Gpr::R10 })); }
    if clobber { ops.push(Op::Normal(Instruction::XorRR { destination: Gpr::R11, source: Gpr::R11 })); }
    ops.push(Op::Ret);
    ops
}
fn summary_instructions(leaf: &SourceX86Emission, clobber: bool, frame: bool) -> Vec<String> {
    selected_leaf_ops(leaf, clobber, frame).iter().map(|op| match op {
        Op::Normal(i) => format!("Ordinary({})", i.heather_expr().render()),
        Op::StoreArgument => "StoreStack64(Rdi)".into(),
        Op::Ret => "NearReturn".into(),
        _ => unreachable!("selected leaf operation"),
    }).collect()
}
// Propose a literal for concrete byte stores; the emitted equality to the
// source result is kernel-checked before any artifact is published.
fn proposed_result(expr: &function_ir_source::SourceExpr, inputs: [u64; 2]) -> u64 {
    use function_ir_source::{SourceExpr as E, SourceBinaryOperation as B};
    match expr {
        E::Input(i) => inputs[*i as usize],
        E::Constant(n) => *n,
        E::Binary { operation, left, right } => {
            let a = proposed_result(left, inputs); let b = proposed_result(right, inputs);
            match operation { B::Add => a.wrapping_add(b), B::Sub => a.wrapping_sub(b), B::BitAnd => a & b, B::BitOr => a | b, B::BitXor => a ^ b }
        }
    }
}

// Keep register/flag projections out of the accumulated whole-machine spine.
// The successor equality still checks these proposed fields against the model.
fn normal_effect_fields(instruction: Instruction, before: &str) -> Option<(Gpr, String, String)> {
    let read = |r: Gpr| format!("read_gpr({}, {before}.gprs)", r.heather_name());
    let (destination, value, flags) = match instruction {
        Instruction::MovRR { destination, source } => (destination, read(source), format!("{before}.flags")),
        Instruction::MovRI { destination, immediate } => (destination, format!("@bitvec::BitVec::ofNat(64, {immediate})"), format!("{before}.flags")),
        Instruction::AddRR { destination, source } | Instruction::SubRR { destination, source }
        | Instruction::AndRR { destination, source } | Instruction::OrRR { destination, source }
        | Instruction::XorRR { destination, source } => {
            let operation = match instruction { Instruction::AddRR { .. } => "add", Instruction::SubRR { .. } => "sub",
                Instruction::AndRR { .. } => "band", Instruction::OrRR { .. } => "bor", _ => "bxor" };
            let value = format!("@bitvec::BitVec::{operation}(64, {}, {})", read(destination), read(source));
            let flags = match instruction {
                Instruction::AddRR { .. } => format!("add_flags({}, {})", read(destination), read(source)),
                Instruction::SubRR { .. } => format!("sub_flags({}, {})", read(destination), read(source)),
                _ => format!("logic_flags({value})"),
            };
            (destination, value, flags)
        },
        _ => return None,
    };
    Some((destination, value, flags))
}
fn normal_fields(instruction: Instruction, before: &str) -> Option<String> {
    let (destination, value, flags) = normal_effect_fields(instruction, before)?;
    Some(format!("write_gpr({}, {value}, {before}.gprs), {flags}", destination.heather_name()))
}

fn normal_flat_proof(instruction: Instruction, before: &str, address: &str, advanced: &str) -> Option<String> {
    let (name, destination, source) = match instruction {
        Instruction::MovRI { destination, immediate } => ("mov_ri", destination, format!("@bitvec::BitVec::ofNat(64, {immediate})")),
        Instruction::MovRR { destination, source } => ("mov_rr", destination, source.heather_name().into()),
        Instruction::AddRR { destination, source } => ("add_rr", destination, source.heather_name().into()),
        Instruction::SubRR { destination, source } => ("sub_rr", destination, source.heather_name().into()),
        Instruction::AndRR { destination, source } => ("and_rr", destination, source.heather_name().into()),
        Instruction::OrRR { destination, source } => ("or_rr", destination, source.heather_name().into()),
        Instruction::XorRR { destination, source } => ("xor_rr", destination, source.heather_name().into()),
        _ => return None,
    };
    Some(format!("call_{name}_flat({}, {source}, {before}, {address}, {advanced})", destination.heather_name()))
}

// Check width-bounded arithmetic, then transport to the canonical operations.
// Host arithmetic proposes the result; the ripple equality is kernel-checked.
fn certify_add(module: &mut Module, words: &Words, name: &str, start: u64, count: u64) {
    let (a, b, result) = (words.get(start), words.get(count), words.get(start.wrapping_add(count)));
    thm(module, name, format!("@bitvec::BitVec::add(64, {a}, {b}) = {result}"),
        format!("bitvec::BitVec::add_eq_of_ripple_add(64, {a}, {b}, {result}, refl)"));
}

fn certify_sub(module: &mut Module, words: &Words, name: &str, start: u64, count: u64) {
    let (a, b, result) = (words.get(start), words.get(count), words.get(start.wrapping_sub(count)));
    thm(module, name, format!("@bitvec::BitVec::sub(64, {a}, {b}) = {result}"),
        format!("bitvec::BitVec::sub_eq_of_ripple_sub(64, {a}, {b}, {result}, refl)"));
}

// Intern concrete words per certificate. Each dependent vector constructor is
// checked once; uses refer to the resulting transparent, kernel-checked value.
struct Words {
    prefix: String,
    values: std::cell::RefCell<std::collections::BTreeSet<u64>>,
}
impl Words {
    fn get(&self, value: u64) -> String {
        self.values.borrow_mut().insert(value);
        format!("{}_word_{value:x}()", self.prefix)
    }
}

fn word(n: u64) -> String {
    let bits = (0..64).map(|i| if n & (1 << i) == 0 { "False" } else { "True" }).collect::<Vec<_>>().join(", ");
    format!("@bitvec::BitVec::from_bits(64, [{bits}])")
}
use super::{byte_chain, drop_chain, byte_at};
fn fun(m: &mut Module, name: &str, ty: &str, value: String) {
    m.declaration(Declaration::function(name, Expr::raw(ty), Block::expression(Expr::raw(value))));
}
fn thm(m: &mut Module, name: &str, ty: String, value: String) {
    m.declaration(Declaration::theorem(name, Expr::raw(ty), Block::expression(Expr::raw(value))));
}
fn state_decl(m: &mut Module, name: &str, ty: String, value: String, theorem: bool) {
    let decl = if theorem { Declaration::theorem(name, Expr::raw(ty), Block::expression(Expr::raw(value))) }
        else { Declaration::function(name, Expr::raw(ty), Block::expression(Expr::raw(value))) };
    m.declaration(decl.parameter(Parameter::explicit("gprs", Expr::name("Gprs")))
        .parameter(Parameter::explicit("flags", Expr::name("Flags")))
        .parameter(Parameter::explicit("stack", Expr::raw("BitVec(64) → BitVec(8)"))));
}
/// Returns the fetch proof for the whole instruction and the name of its byte
/// span. The span is a chain of named suffixes rather than a `[…]` literal for
/// the same reason the file is (`byte_chain`): the fetch lemmas state their
/// spans in `Cons` form, and a literal has to be re-folded at every link.
fn certify_fetch(module: &mut Module, words: &Words, prefix: &str, index: usize, memory: &str, pc: u64, encoding: &[u8], header_size: usize) -> (String, String) {
    let actual_memory = memory;
    let memory = format!("CallMemory({prefix}_file(), stack)");
    let span = format!("{prefix}_span_{index}");
    byte_chain(module, &span, encoding);
    let suffix = |j: usize| format!("{span}_from_{j}()");
    let stack_decl = |module: &mut Module, name: &str, ty: String, body: String| {
        module.declaration(Declaration::theorem(name, Expr::raw(ty), Block::expression(Expr::raw(body)))
            .parameter(Parameter::explicit("stack", Expr::raw("BitVec(64) → BitVec(8)"))));
    };
    let word = |n| words.get(n);
    // The span's `FetchedFrom` type is `ReadableBytes` unfolded over the
    // remaining bytes, so *stating* one is work proportional to what is left
    // of the instruction. The chain is therefore nested in one declaration —
    // stated once, for the whole instruction — while the premises each byte
    // needs stay named: those statements are small, and naming them is what
    // lets `--item-timings` attribute the fetch cost.
    let mut proof = String::new();
    for j in (0..encoding.len()).rev() {
        let address = word(pc + j as u64);
        let byte = format!("elf_byte({})", encoding[j]);
        let offset = (pc + j as u64 - 0x400000) as usize - header_size;
        thm(module, &format!("{prefix}_byte_page_{index}_{j}"),
            format!("is_zero_bits(48, @bitvec::BitVec::bxor(48, bitvec::BitVec::drop_low(16, 48, {address}), @bitvec::BitVec::ofNat(48, 64))) = True"), "refl".into());
        thm(module, &format!("{prefix}_byte_offset_{index}_{j}"),
            format!("@bitvec::BitVec::toNat(16, bitvec::BitVec::take_low(16, 48, {address})) = {offset} + {header_size}"), "refl".into());
        thm(module, &format!("{prefix}_byte_found_{index}_{j}"),
            format!("{prefix}_code().nth({offset}) = Some({byte})"), byte_at(&format!("{prefix}_code"), offset));
        thm(module, &format!("{prefix}_byte_present_{index}_{j}"),
            format!("static_elf64_read({prefix}_header() ++ {prefix}_code(), {address}) = Some({byte})"),
            format!("static_elf64_read_split({prefix}_header(), {prefix}_code(), {header_size}, {offset}, {address}, {byte}, {prefix}_header_length(), {prefix}_byte_page_{index}_{j}(), {prefix}_byte_offset_{index}_{j}(), {prefix}_byte_found_{index}_{j}())"));
        let present = format!("{prefix}_byte_present_{index}_{j}()");
        proof = if j+1 == encoding.len() {
            format!("call_file_fetch_one({memory}, {address}, {byte}, {present})")
        } else {
            let next = word(pc + j as u64 + 1);
            thm(module, &format!("{prefix}_byte_wrap_{index}_{j}"),
                format!("@bitvec::BitVec::carry_add_bit(64, {address}, @bitvec::BitVec::ofNat(64, 1)) = False"), "refl".into());
            thm(module, &format!("{prefix}_byte_next_{index}_{j}"),
                format!("next_rip({address}, 1) = {next}"), "refl".into());
            format!("call_file_fetch_more({memory}, {address}, {next}, {byte}, elf_byte({}), {}, {present}, {prefix}_byte_wrap_{index}_{j}(), {prefix}_byte_next_{index}_{j}(), {proof})",
                encoding[j+1], suffix(j+2))
        };
    }
    stack_decl(module, &format!("{prefix}_byte_{index}_0"),
        format!("FetchedFrom(call_fetch_access(), {memory}, InstructionBytes({}, {}))", word(pc), suffix(0)), proof);
    (format!("{prefix}_byte_{index}_0({actual_memory}.stack)"), format!("{span}()"))
}

fn certify_stack_permissions(module: &mut Module, words: &Words, prefix: &str, index: usize, sp: u64) -> String {
    let word = |n| words.get(n);
    for j in (0..=8).rev() {
        let address = word(sp+j as u64);
        let ty = format!("StackReadsAllowed(call_stack_access(), {}, {address})", 8-j);
        let proof = if j == 8 { "trivial".into() } else {
            let next = word(sp+j as u64+1);
            format!("stack_reads_cons(call_stack_access(), {}, {address}, {next}, refl, refl, refl, refl, {prefix}_stack_allowed_{index}_{}())", 7-j, j+1)
        };
        thm(module, &format!("{prefix}_stack_allowed_{index}_{j}"), ty, proof);
    }
    format!("{prefix}_stack_allowed_{index}_0()")
}

fn certify_call_memory(module: &mut Module, words: &Words, prefix: &str, i: usize, before: &str, sp: u64, pc: u64, delta: u32, local: Option<(u64, &str)>, value_proof: Option<String>) -> (String, String) {
    let word = |n| words.get(n);
    let slot = sp - if local.is_some() { 0 } else { 8 };
    let stored = local.map_or(pc + 5, |(value, _)| value);
    let register = local.map_or("R11", |(_, register)| register);
    let base = if local.is_some() { format!("read_gpr(Rsp, {before}.gprs)") }
        else { format!("@bitvec::BitVec::sub(64, read_gpr(Rsp, {before}.gprs), @bitvec::BitVec::ofNat(64, 8))") };
    let value = if local.is_some() { format!("read_gpr({register}, {before}.gprs)") } else { format!("call_return_address({before})") };
    let literal_base = word(slot);
    let literal_value = word(stored);
    let fact = |kind: &str| format!("{prefix}_store_{kind}_{i}(gprs, flags, stack)");
    if local.is_some() {
        state_decl(module, &format!("{prefix}_store_base_{i}"), format!("{base} = {literal_base}"), format!("{prefix}_rsp_{i}(gprs, flags, stack)"), true);
    } else {
    thm(module, &format!("{prefix}_store_sub_{i}"), format!("@bitvec::BitVec::sub(64, {}, @bitvec::BitVec::ofNat(64, 8)) = {literal_base}", word(sp)), "refl".into());
    state_decl(module, &format!("{prefix}_store_base_{i}"), format!("{base} = {literal_base}"),
        format!("trans(cong_fn<BitVec(64), BitVec(64)>(λ pointer => @bitvec::BitVec::sub(64, pointer, @bitvec::BitVec::ofNat(64, 8)), {prefix}_rsp_{i}(gprs, flags, stack)), {prefix}_store_sub_{i}())"), true);
    }
    state_decl(module, &format!("{prefix}_store_value_{i}"), format!("{value} = {literal_value}"), value_proof.unwrap_or_else(|| "refl".into()), true);
    let memory = |j| format!("{prefix}_store_memory_{i}_{j}(gprs, flags, stack)");
    state_decl(module, &format!("{prefix}_store_memory_{i}_0"), "CallMemory".into(), format!("{before}.memory"), false);
    state_decl(module, &format!("{prefix}_store_equal_{i}_0"), format!("word_write_0(call_stack_access(), {value}, {before}.memory, {base}) = {}", memory(0)), "refl".into(), true);
    for j in 0..8 {
        let address = word(slot+j as u64); let byte = stored.to_le_bytes()[j];
        thm(module, &format!("{prefix}_store_offset_{i}_{j}"), format!("@bitvec::BitVec::add(64, {literal_base}, @bitvec::BitVec::ofNat(64, {j})) = {address}"), "refl".into());
        thm(module, &format!("{prefix}_store_byte_literal_{i}_{j}"), format!("imm_byte{j}({literal_value}) = elf_byte({byte})"), "refl".into());
        state_decl(module, &format!("{prefix}_store_address_{i}_{j}"), format!("@bitvec::BitVec::add(64, {base}, @bitvec::BitVec::ofNat(64, {j})) = {address}"),
            format!("trans(cong_fn<BitVec(64), BitVec(64)>(λ pointer => @bitvec::BitVec::add(64, pointer, @bitvec::BitVec::ofNat(64, {j})), {}), {prefix}_store_offset_{i}_{j}())", fact("base")), true);
        state_decl(module, &format!("{prefix}_store_byte_{i}_{j}"), format!("imm_byte{j}({value}) = elf_byte({byte})"),
            format!("trans(cong_fn<BitVec(64), BitVec(8)>(imm_byte{j}, {}), {prefix}_store_byte_literal_{i}_{j}())", fact("value")), true);
        state_decl(module, &format!("{prefix}_store_memory_{i}_{}", j+1), "CallMemory".into(),
            format!("CallMemory({prefix}_file(), call_memory_write({}, {address}, elf_byte({byte})).stack)", memory(j)), false);
        state_decl(module, &format!("{prefix}_store_equal_{i}_{}", j+1),
            format!("word_write_{}(call_stack_access(), {value}, {before}.memory, {base}) = {}", j+1, memory(j+1)),
            format!("call_memory_write_cong(word_write_{j}(call_stack_access(), {value}, {before}.memory, {base}), {}, @bitvec::BitVec::add(64, {base}, @bitvec::BitVec::ofNat(64, {j})), {address}, imm_byte{j}({value}), elf_byte({byte}), {prefix}_store_equal_{i}_{j}(gprs, flags, stack), {prefix}_store_address_{i}_{j}(gprs, flags, stack), {prefix}_store_byte_{i}_{j}(gprs, flags, stack))", memory(j)), true);
    }
    let model_memory = if local.is_some() { format!("stack_store_memory(call_stack_access(), {register}, {before})") }
        else { format!("call_after_memory(call_stack_access(), @bitvec::BitVec::ofNat(32, {delta}), {before})") };
    (memory(8), format!("sym(trans({model_memory}, {prefix}_store_equal_{i}_8(gprs, flags, stack)))"))
}

fn certify_word_outside(module: &mut Module, words: &Words, name: &str, slot: u64, protected: u64) {
    let word = |n| words.get(n);
    for j in 0..8 {
        for (kind, base) in [("written", slot), ("protected", protected)] {
            thm(module, &format!("{name}_{kind}_offset_{j}"),
                format!("@bitvec::BitVec::add(64, {}, @bitvec::BitVec::ofNat(64, {j})) = {}", word(base), word(base+j)), "refl".into());
        }
    }
    let mut fields = Vec::new();
    for k in 0..8 {
        let target = word(protected+k);
        thm(module, &format!("{name}_excluded_{k}_0"), format!("¬WordPrefixWrites(0, {}, {target})", word(slot)), "λ hit => hit".into());
        for j in 0..8 {
            let pointer = word(slot+j);
            thm(module, &format!("{name}_different_{k}_{j}"),
                format!("is_zero_bits(64, @bitvec::BitVec::bxor(64, {pointer}, {target})) = False"), "refl".into());
            thm(module, &format!("{name}_excluded_{k}_{}", j+1),
                format!("¬WordPrefixWrites({}, {}, {target})", j+1, word(slot)),
                format!("word_prefix_excluded({j}, {}, {target}, {name}_excluded_{k}_{j}(), j(sym({name}_written_offset_{j}()), λ pointer _ => ¬ByteWrite(pointer, {target}), byte_write_excluded({pointer}, {target}, {name}_different_{k}_{j}())))", word(slot)));
        }
        fields.push(format!("byte{k} := j(sym({name}_protected_offset_{k}()), λ target _ => ¬WordPrefixWrites(8, {}, target), {name}_excluded_{k}_8())", word(slot)));
    }
    fun(module, name, &format!("WordOutside({}, {})", word(slot), word(protected)), format!("WordOutside({})", fields.join(", ")));
}

fn certify_return_target(module: &mut Module, words: &Words, prefix: &str, i: usize, before: &str, sp: u64, target: u64, from_contract: Option<(&str, bool)>) -> String {
    let word = |n| words.get(n);
    let base = word(sp); let value = word(target);
    let mut fields = Vec::new();
    for j in 0..8 {
        let query = if j == 0 { base.clone() } else { format!("@bitvec::BitVec::add(64, {base}, @bitvec::BitVec::ofNat(64, {j}))") };
        let literal = word(sp+j as u64);
        thm(module, &format!("{prefix}_read_address_{i}_{j}"), format!("{query} = {literal}"), "refl".into());
        let read_proof = if let Some((contract, frame)) = from_contract {
            let outside = if frame { format!("{contract}_callee_local_outside_{j}(gprs, flags, stack)") } else { "λ impossible => impossible".into() };
            // The contract observes the stack directly, so this is the equation
            // the theorem states; reading it through `call_memory_read` would
            // walk the file list on both memories before reaching the stack.
            format!("trans({contract}_callee_memory_effects(gprs, flags, stack)({literal}, {outside}), refl)")
        } else { "refl".into() };
        state_decl(module, &format!("{prefix}_read_literal_{i}_{j}"),
            format!("call_stack_access().read({before}.memory, {literal}) = imm_byte{j}({value})"), read_proof, true);
        state_decl(module, &format!("{prefix}_return_read_{i}_{j}"),
            format!("call_stack_access().read({before}.memory, {query}) = imm_byte{j}({value})"),
            format!("trans(cong_fn<BitVec(64), BitVec(8)>(λ pointer => call_stack_access().read({before}.memory, pointer), {prefix}_read_address_{i}_{j}()), {prefix}_read_literal_{i}_{j}(gprs, flags, stack))"), true);
        fields.push(format!("byte{j} := {prefix}_return_read_{i}_{j}(gprs, flags, stack)"));
    }
    state_decl(module, &format!("{prefix}_return_reads_{i}"), format!("StackWordReads(call_stack_access(), {before}.memory, {base}, {value})"),
        format!("StackWordReads({})", fields.join(", ")), true);
    state_decl(module, &format!("{prefix}_return_value_{i}"),
        format!("stack_word(call_stack_access(), {before}.memory, read_gpr(Rsp, {before}.gprs)) = {value}"),
        format!("trans(cong_fn<BitVec(64), BitVec(64)>(λ pointer => stack_word(call_stack_access(), {before}.memory, pointer), {prefix}_rsp_{i}(gprs, flags, stack)), stack_word_matches(call_stack_access(), {before}.memory, {base}, {value}, {prefix}_return_reads_{i}(gprs, flags, stack)))"), true);
    format!("sym(trans(return_after_target(call_stack_access(), {before}), {prefix}_return_value_{i}(gprs, flags, stack)))")
}

pub(super) fn generate(elab: &Elaborator, module: &mut Module, prefix: &str, caller: &str,
    requested_callee: &str, inputs: [u64; 2], callable: bool) -> Result<Vec<u8>, String>
{
    let legacy = if callable { None } else { function_ir_source::reflect_call_plan(elab, caller).ok() };
    let composition = if legacy.is_none() { Some(function_ir_source::reflect_call_expression(elab, caller, requested_callee).map_err(|e| e.to_string())?) } else { None };
    let (callee, local, twice) = legacy.unwrap_or_else(|| (requested_callee.into(), false, false));
    if callee != requested_callee { return Err(format!("caller resolves to `{callee}`, not opted-in callee `{requested_callee}`")); }
    let leaf_prefix = format!("{prefix}_leaf");
    let mut registers = vec![Gpr::Rax, Gpr::Rcx, Gpr::Rdx, Gpr::R8, Gpr::R9, Gpr::R10, Gpr::R11];
    if callable { registers = vec![Gpr::Rax, Gpr::R11, Gpr::R10, Gpr::R9, Gpr::R8, Gpr::Rcx, Gpr::Rdx]; }
    if twice { registers.retain(|r| *r != Gpr::R10); }
    let leaf = function_ir_source::generate_elaborated_x86(elab, &leaf_prefix, &callee,
        [Gpr::Rdi, Gpr::Rsi], &registers, Gpr::Rax)
        .map_err(|e| if callable { format!("callable callee: {e}") } else { format!("callee: {e}") })?;
    let normal = |i| Op::Normal(i);
    let mov = |r, value| normal(Instruction::MovRI { destination: r, immediate: value });
    let leaf_ops = selected_leaf_ops(&leaf, local && !twice, twice);
    let mut caller_ops = vec![mov(Gpr::R11, 8), normal(Instruction::SubRR { destination: Gpr::Rsp, source: Gpr::R11 })];
    if local { caller_ops.extend([normal(Instruction::MovRR { destination: Gpr::R11, source: Gpr::Rdi }),
        normal(Instruction::XorRR { destination: Gpr::R11, source: Gpr::Rsi }), Op::Store]); }
    caller_ops.push(Op::Call("leaf".into()));
    if twice { caller_ops.extend([normal(Instruction::MovRR { destination: Gpr::Rdi, source: Gpr::Rax }), Op::Call("leaf_again".into())]); }
    if local { caller_ops.extend([Op::Load, normal(Instruction::XorRR { destination: Gpr::Rax, source: Gpr::R11 })]); }
    caller_ops.extend([mov(Gpr::R11, 8), normal(Instruction::AddRR { destination: Gpr::Rsp, source: Gpr::R11 }), Op::Ret]);
    if let Some(expr) = &composition { caller_ops = composition::lower(expr, callable, &composition::leaf_clobbers(&leaf))?; }
    // Place the leaf before the wrapper: its call deliberately exercises a negative rel32.
    let mut fragments = vec![
        Fragment { name: "entry".into(), ops: vec![mov(Gpr::Rsp, STACK_TOP), mov(Gpr::Rdi, inputs[0]), mov(Gpr::Rsi, inputs[1]),
            Op::Call("caller".into()), normal(Instruction::MovRR { destination: Gpr::Rdi, source: Gpr::Rax }), mov(Gpr::Rax, 60), Op::Syscall] },
        Fragment { name: "leaf".into(), ops: leaf_ops.clone() },
        Fragment { name: "caller".into(), ops: caller_ops },
    ];
    if twice { fragments.insert(2, Fragment { name: "leaf_again".into(), ops: leaf_ops }); }
    let layout = layout(&fragments)?;
    let mut file = super::elf::image(&layout.bytes)?;
    // Extend the existing fixed profile with a zero-filled RW PT_LOAD.
    let size = HEADER + layout.bytes.len();
    file.truncate(176);
    file[24..32].copy_from_slice(&ENTRY.to_le_bytes());
    file[56..58].copy_from_slice(&3u16.to_le_bytes());
    file[96..104].copy_from_slice(&(size as u64).to_le_bytes());
    file[104..112].copy_from_slice(&(size as u64).to_le_bytes());
    file.extend(1u32.to_le_bytes()); file.extend(6u32.to_le_bytes());
    for n in [0x1000u64, 0x401000, 0x401000, 0, 0x1000, 0x1000] { file.extend(n.to_le_bytes()); }
    file.extend(&layout.bytes);
    for name in ["x86_64_calls", "x86_64_call_frame", "x86_64_call_summary", "elf64_calls"] { module.raw(format!("import {name};")); }
    module.raw(leaf.text.clone());
    emit_leaf_summary(module, &leaf_prefix, &leaf, local && !twice, twice);
    super::elf::valuation(module, &leaf_prefix, &leaf.reflected.region, inputs)?;
    if twice {
        super::elf::valuation_expressions(module, &format!("{leaf_prefix}_second"), &leaf_prefix, &leaf.reflected.region,
            [Expr::call(format!("{leaf_prefix}_value_{}", leaf.reflected.region.outputs[0].id), [Expr::name("width")]),
             Expr::call(format!("{leaf_prefix}_value_1"), [Expr::name("width")])])?;
    }
    if let Some(expr) = &composition {
        module.declaration(Declaration::theorem(format!("{prefix}_source_call"),
            Expr::equal(Expr::call(caller, [Expr::name("left"), Expr::name("right")]),
                expr.expression(&callee, &[Expr::name("left"), Expr::name("right")])), Block::expression(Expr::name("refl")))
            .parameter(Parameter::explicit("left", Expr::raw("BitVec(64)")))
            .parameter(Parameter::explicit("right", Expr::raw("BitVec(64)"))));
    } else {
        let left = if twice { format!("{callee}(left, right)") } else { "left".into() };
        module.declaration(Declaration::theorem(format!("{prefix}_source_call"),
            Expr::raw(format!("{caller}(left, right) = {}", if local { format!("@bitvec::BitVec::bxor(64, {callee}({left}, right), @bitvec::BitVec::bxor(64, left, right))") } else { format!("{callee}(left, right)") })), Block::expression(Expr::name("refl")))
            .parameter(Parameter::explicit("left", Expr::raw("BitVec(64)")))
            .parameter(Parameter::explicit("right", Expr::raw("BitVec(64)"))));
    }
    byte_chain(module, &format!("{prefix}_code"), &layout.bytes);
    drop_chain(module, &format!("{prefix}_code"), layout.bytes.len());
    byte_chain(module, &format!("{prefix}_header"), &file[..HEADER]);
    thm(module, &format!("{prefix}_header_length"), format!("{prefix}_header().len() = {HEADER}"), "refl".into());
    fun(module, &format!("{prefix}_file"), "List<BitVec(8)>", format!("{prefix}_header() ++ {prefix}_code()"));
    fun(module, &format!("{prefix}_image"), &format!("CallElfImage({prefix}_code())"),
        format!("CallElfImage(trivial, elf_byte({}), elf_byte({}), refl, trivial)", size & 255, size >> 8));
    thm(module, &format!("{prefix}_file_correct"), format!("{prefix}_file() = call_elf_bytes({prefix}_code(), {prefix}_image())"), "refl".into());
    let words = Words { prefix: prefix.into(), values: Default::default() };
    let mut trace = Module::default();
    if callable { callable::emit(&mut trace, &words, prefix, caller, &leaf, &leaf_prefix, &layout)?; }
    certify_trace(&mut trace, &words, prefix, caller, inputs, &leaf, &leaf_prefix, &layout, local, twice, composition.is_some(), callable)?;
    for value in words.values.into_inner() {
        fun(module, &format!("{prefix}_word_{value:x}"), "BitVec(64)", word(value));
    }
    module.extend(trace);
    Ok(file)
}

// This theorem is checked once for arbitrary arguments, memory and placement.
// Call sites discharge graph/input, fetch and stack-access premises separately.
fn emit_leaf_summary(module: &mut Module, prefix: &str, leaf: &SourceX86Emission, clobber: bool, frame: bool) {
    let code = summary_instructions(leaf, clobber, frame);
    fun(module, &format!("{prefix}_summary_code"), "List<CallInstruction>", format!("[{}]", code.join(", ")));
    for i in 0..=code.len() {
        fun(module, &format!("{prefix}_summary_suffix_{i}"), "List<CallInstruction>", format!("[{}]", code[i..].join(", ")));
        let body = if i == 0 { "before".into() } else {
            format!("call_next(call_stack_access(), {}, {prefix}_summary_state_{}(before))", code[i-1], i-1)
        };
        module.declaration(Declaration::function(format!("{prefix}_summary_state_{i}"), Expr::raw("MachineState<CallMemory>"), Block::expression(Expr::raw(body)))
            .parameter(Parameter::explicit("before", Expr::raw("MachineState<CallMemory>"))));
    }
    let result = format!("{}(values(64, 0), values(64, 1))", leaf.reflected.source_name);
    let pointer = "@bitvec::BitVec::sub(64, read_gpr(Rsp, before.gprs), @bitvec::BitVec::ofNat(64, 8))";
    let footprint = if frame { format!("λ address => WordPrefixWrites(8, {pointer}, address)") } else { "NoWrites".into() };
    module.declaration(Declaration::function(format!("{prefix}_summary_post"), Expr::name("Type"),
        // The footprint is stated over the stack observation, not over
        // `call_memory_read`: a caller discharging it at a concrete address
        // would otherwise pay a file lookup per byte. Constancy of the file is
        // carried as its own conjunct, so `memory_writes_of_stack_writes`
        // recovers the full observation whenever a caller wants it.
        Block::expression(Expr::raw(format!("NativeIntegerCallContract<CallMemory, BitVec(8)>(stack_observation, {footprint}, before, after, {result}, stack_word(call_stack_access(), before.memory, read_gpr(Rsp, before.gprs))) ∧ read_gpr(Rsi, after.gprs) = read_gpr(Rsi, before.gprs) ∧ after.memory.file = before.memory.file"))))
        .parameter(Parameter::explicit("values", Expr::raw("Valuation()")))
        .parameter(Parameter::explicit("before", Expr::raw("MachineState<CallMemory>")))
        .parameter(Parameter::explicit("after", Expr::raw("MachineState<CallMemory>"))));
    let body_start = if frame { format!("{prefix}_summary_state_4(before)") } else { "before".into() };
    let graph = if frame { "entry.right.right.left" } else { "entry.right.right" };
    let core = format!("trans({prefix}_refines_function_ir(values, {body_start}, entry.left, entry.right.left, {graph}), {prefix}_denotes_source(values, {graph}))");
    let result_proof = if clobber { format!("trans(xor_r11_preserves_rax({prefix}_summary_state_{}(before)), {core})", code.len()-2) } else { core };
    let extra = if frame { format!(" ∧ @bitvec::BitVec::borrow_sub_bit(64, read_gpr(Rsp, before.gprs), @bitvec::BitVec::ofNat(64, 8)) = False ∧ WordOutside({pointer}, read_gpr(Rsp, before.gprs))") } else { String::new() };
    let returned = if frame { format!("stored_word_preserves_return(before.memory, {pointer}, read_gpr(Rdi, before.gprs), read_gpr(Rsp, before.gprs), entry.right.right.right.right)") } else { "refl".into() };
    let effects = if frame { format!("word_stack_effect_8(before.memory, {pointer}, read_gpr(Rdi, before.gprs))") }
        else { format!("writes_only_equal(stack_observation, NoWrites, before.memory, call_run(call_stack_access(), {prefix}_summary_code(), before).memory, refl)") };
    module.declaration(Declaration::function(format!("{prefix}_summary"),
        Expr::raw(format!("CallSummary<CallMemory>(call_stack_access(), {prefix}_summary_code(), λ before after => {prefix}_summary_post(values, before, after))")),
        Block::expression(Expr::raw(format!("CallSummary(requires := λ before => values(64, 0) = read_gpr(Rdi, before.gprs) ∧ values(64, 1) = read_gpr(Rsi, before.gprs) ∧ RegionHolds({prefix}_raw(), values){extra}, ensures := λ before entry => ⟨NativeIntegerCallContract(result_correct := {result_proof}, returned_to := {returned}, stack_restored := refl, memory_effects := {effects}, preserved_rbx := refl, preserved_rbp := refl, preserved_r12 := refl, preserved_r13 := refl, preserved_r14 := refl, preserved_r15 := refl), ⟨refl, refl⟩⟩)"))))
        .parameter(Parameter::explicit("values", Expr::raw("Valuation()"))));
}

fn certify_trace(module: &mut Module, words: &Words, prefix: &str, caller: &str, inputs: [u64;2], leaf: &SourceX86Emission,
    leaf_prefix: &str, layout: &Layout, local: bool, twice: bool, composed: bool, callable: bool) -> Result<(), String>
{
    let word = |n| words.get(n);
    let state = |i| format!("{prefix}_state_{i}(gprs, flags, stack)");
    state_decl(module, &format!("{prefix}_state_0"), "MachineState<CallMemory>".into(),
        format!("call_initial({prefix}_file(), gprs, flags, stack)"), false);
    if twice {
        for (name, protected) in [("return", STACK_TOP-24), ("local", STACK_TOP-16)] {
            certify_word_outside(module, words, &format!("{prefix}_{name}_outside"), STACK_TOP-32, protected);
        }
    }
    let mut pc = ENTRY;
    let mut returns = Vec::new();
    let mut rsp = STACK_TOP;
    let mut trace = Vec::new();
    let mut operations = Vec::new();
    let leaf_count = selected_leaf_ops(leaf, local && !twice, twice).len();
    let mut leaf_start = 0;
    let mut leaf_end = 0;
    let mut instances = Vec::new();
    let mut current_instance = prefix.to_string();
    let mut ledger = composition::Ledger::default();
    let mut call_inputs = [0; 2];
    let mut call_entry = None;
    let mut caller_start = 0;
    let mut caller_end = 0;
    loop {
        let (op, encoding, instruction) = layout.placed.get(&pc).ok_or("execution escaped laid-out fragments")?;
        let i = trace.len();
        if matches!(op, Op::Syscall) { break; }
        if pc == layout.symbols["caller"] { caller_start = i; }
        if pc == layout.symbols["leaf"] || layout.symbols.get("leaf_again") == Some(&pc) { leaf_start = i; }
        let in_leaf = leaf_start != 0 && i < leaf_start + leaf_count;
        if composed && in_leaf && i == leaf_start {
            call_inputs = [ledger.value(Gpr::Rdi)?, ledger.value(Gpr::Rsi)?];
            call_entry = Some([format!("sym({})", ledger.fact(Gpr::Rdi)?), format!("sym({})", ledger.fact(Gpr::Rsi)?)]);
        }
        let before = state(i);
        let (after_expr, next) = match op {
            Op::Normal(instruction) => (format!("execute_normal(decoded_canonical({}), {before})", instruction.heather_expr().render()), pc + encoding.len() as u64),
            Op::Call(symbol) => {
                let target = layout.symbols[symbol]; let delta = displacement(pc, target)? as u32;
                returns.push(pc + 5);
                (format!("call_after(call_stack_access(), @bitvec::BitVec::ofNat(32, {delta}), {before})"), target)
            }
            Op::Ret => {
                if i + 1 == leaf_start + leaf_count { leaf_end = i; }
                (format!("return_after(call_stack_access(), {before})"), returns.pop().ok_or("return with empty static frame chain")?)
            }
            Op::Save(r) => (format!("stack_store_after(call_stack_access(), {}, {before})", r.heather_name()), pc + 4),
            Op::Restore(r) => (format!("stack_load_after(call_stack_access(), {}, {before})", r.heather_name()), pc + 4),
            Op::StoreArgument => (format!("stack_store_after(call_stack_access(), Rdi, {before})"), pc + 4),
            Op::Store => (format!("stack_store_after(call_stack_access(), R11, {before})"), pc + 4),
            Op::Load => (format!("stack_load_after(call_stack_access(), R11, {before})"), pc + 4),
            Op::Syscall => unreachable!(),
        };
        let after = state(i+1);
        // Name each step, then flatten RIP to the independently laid-out address.
        state_decl(module, &format!("{prefix}_computed_{i}"), "MachineState<CallMemory>".into(), after_expr, false);
        let computed = format!("{prefix}_computed_{i}(gprs, flags, stack)");
        let (memory, memory_proof) = match op {
            Op::Call(symbol) => certify_call_memory(module, words, prefix, i, &before, rsp, pc, displacement(pc, layout.symbols[symbol])? as u32, None, None),
            Op::Normal(normal) => (format!("{before}.memory"), format!("sym(normal_memory({}, {before}))", normal.heather_expr().render())),
            Op::Ret => (format!("{before}.memory"), format!("sym(return_memory(call_stack_access(), {before}))")),
            Op::Save(r) => certify_call_memory(module, words, prefix, i, &before, rsp, pc, 0, Some((ledger.value(*r)?, r.heather_name())), Some(ledger.fact(*r)?)),
            Op::Store => certify_call_memory(module, words, prefix, i, &before, rsp, pc, 0, Some((inputs[0] ^ inputs[1], "R11")), None),
            Op::StoreArgument => {
                let (value, proof) = if instances.is_empty() { (inputs[0], None) } else {
                    let value = proposed_result(&leaf.reflected.result, inputs);
                    thm(module, &format!("{prefix}_stored_source_result"),
                        format!("{}({}, {}) = {}", leaf.reflected.source_name, word(inputs[0]), word(inputs[1]), word(value)), "refl".into());
                    (value, Some(format!("trans({current_instance}_callee_result(gprs, flags, stack), {prefix}_stored_source_result())")))
                };
                certify_call_memory(module, words, prefix, i, &before, rsp, pc, 0, Some((value, "Rdi")), proof)
            },
            Op::Load | Op::Restore(_) => (format!("{before}.memory"), "refl".into()),
            _ => unreachable!(),
        };
        let direct_normal = matches!(op, Op::Normal(normal) if normal_fields(*normal, &before).is_some());
        if !direct_normal {
            state_decl(module, &format!("{prefix}_memory_same_{i}"), format!("{memory} = {computed}.memory"), memory_proof, true);
        }
        let fields = match op {
            Op::Call(_) => format!("write_gpr(Rsp, {}, {before}.gprs), {before}.flags", word(rsp-8)),
            Op::Ret => format!("write_gpr(Rsp, {}, {before}.gprs), {before}.flags", word(rsp+8)),
            Op::Store | Op::StoreArgument | Op::Save(_) => format!("{before}.gprs, {before}.flags"),
            Op::Restore(r) => format!("write_gpr({}, {}, {before}.gprs), {before}.flags", r.heather_name(), word(ledger.saved(rsp)?)),
            Op::Load => format!("write_gpr(R11, {}, {before}.gprs), {before}.flags", word(inputs[0] ^ inputs[1])),
            Op::Normal(normal) => normal_fields(*normal, &before).unwrap_or_else(|| format!("{computed}.gprs, {computed}.flags")),
            _ => unreachable!(),
        };
        state_decl(module, &format!("{prefix}_state_{}", i+1), "MachineState<CallMemory>".into(),
            format!("MachineState({fields}, {}, {memory})", word(next)), false);
        // Track RSP one step at a time; consumers use this equality instead of
        // normalizing the preceding register updates inside every address check.
        let next_rsp = match op {
            Op::Call(_) | Op::Normal(Instruction::SubRR { destination: Gpr::Rsp, .. }) => rsp-8,
            Op::Ret | Op::Normal(Instruction::AddRR { destination: Gpr::Rsp, .. }) | Op::Normal(Instruction::MovRR { destination: Gpr::Rsp, source: Gpr::R10 }) => rsp+8,
            _ => rsp,
        };
        let read_before = format!("read_gpr(Rsp, {before}.gprs)");
        let mut rhs = read_before.clone();
        let step_proof = match op {
            Op::Call(_) | Op::Ret => {
                rhs = word(next_rsp);
                format!("read_gpr_after_write(Rsp, {}, {before}.gprs)", word(next_rsp))
            }
            Op::Normal(Instruction::MovRI { destination: Gpr::Rsp, immediate }) => { rhs = format!("@bitvec::BitVec::ofNat(64, {immediate})"); "refl".into() }
            Op::Normal(Instruction::SubRR { destination: Gpr::Rsp, .. }) => { rhs = format!("@bitvec::BitVec::sub(64, {read_before}, @bitvec::BitVec::ofNat(64, 8))"); "refl".into() }
            Op::Normal(Instruction::AddRR { destination: Gpr::Rsp, .. }) => { rhs = format!("@bitvec::BitVec::add(64, {read_before}, @bitvec::BitVec::ofNat(64, 8))"); "refl".into() }
            Op::Normal(Instruction::MovRR { destination: Gpr::Rsp, source: Gpr::R10 }) => { rhs = format!("read_gpr(R10, {before}.gprs)"); "refl".into() }
            _ => "refl".into(),
        };
        let write = match op {
            Op::Normal(instruction) => normal_effect_fields(*instruction, &before).map(|(register, value, _)| (register, value)),
            Op::Restore(r) => Some((*r, word(ledger.saved(rsp)?))),
            Op::Load => Some((Gpr::R11, word(inputs[0] ^ inputs[1]))),
            _ => None,
        };
        let step_proof = if let Some((register, value)) = write {
            if register == Gpr::Rsp { format!("read_gpr_after_write(Rsp, {value}, {before}.gprs)") }
            else { format!("read_gpr_after_other_write(Rsp, {}, {value}, {before}.gprs, refl)", register.heather_name()) }
        } else { step_proof };
        state_decl(module, &format!("{prefix}_rsp_step_{i}"), format!("read_gpr(Rsp, {after}.gprs) = {rhs}"), step_proof, true);
        let rhs_proof = if i == 0 || matches!(op, Op::Call(_) | Op::Ret | Op::Normal(Instruction::MovRR { destination: Gpr::Rsp, source: Gpr::R10 })) { "refl".into() } else if next_rsp == rsp {
            format!("{prefix}_rsp_{i}(gprs, flags, stack)")
        } else {
            let operation = if next_rsp < rsp { "sub" } else { "add" };
            thm(module, &format!("{prefix}_rsp_arithmetic_{i}"), format!("@bitvec::BitVec::{operation}(64, {}, @bitvec::BitVec::ofNat(64, 8)) = {}", word(rsp), word(next_rsp)), "refl".into());
            format!("trans(cong_fn<BitVec(64), BitVec(64)>(λ pointer => @bitvec::BitVec::{operation}(64, pointer, @bitvec::BitVec::ofNat(64, 8)), {prefix}_rsp_{i}(gprs, flags, stack)), {prefix}_rsp_arithmetic_{i}())")
        };
        state_decl(module, &format!("{prefix}_rsp_rhs_{i}"), format!("{rhs} = {}", word(next_rsp)), rhs_proof, true);
        state_decl(module, &format!("{prefix}_rsp_{}", i+1), format!("read_gpr(Rsp, {after}.gprs) = {}", word(next_rsp)),
            format!("trans({prefix}_rsp_step_{i}(gprs, flags, stack), {prefix}_rsp_rhs_{i}(gprs, flags, stack))"), true);
        if matches!(op, Op::Call(_) | Op::Ret | Op::Store | Op::StoreArgument | Op::Load | Op::Save(_) | Op::Restore(_)) {
            if matches!(op, Op::Call(_) | Op::Store | Op::StoreArgument | Op::Save(_)) {
                let slot = rsp - if matches!(op, Op::Store | Op::StoreArgument | Op::Save(_)) { 0 } else { 8 };
                let base = word(slot);
                let actual_base = if matches!(op, Op::Store | Op::StoreArgument | Op::Save(_)) { format!("read_gpr(Rsp, {before}.gprs)") }
                    else { format!("@bitvec::BitVec::sub(64, read_gpr(Rsp, {before}.gprs), @bitvec::BitVec::ofNat(64, 8))") };
                let mut fields = vec!["canonical := refl".to_string(), format!("end_canonical := j(sym({prefix}_store_offset_{i}_7()), λ address _ => LowCanonical(address), refl)"), "no_wrap := refl".into()];
                for j in 0..8 {
                    thm(module, &format!("{prefix}_write_literal_{i}_{j}"), format!("call_stack_access().writable({}) = True", word(slot+j as u64)), "refl".into());
                    state_decl(module, &format!("{prefix}_write_permission_{i}_{j}"),
                        format!("call_stack_access().writable(@bitvec::BitVec::add(64, {base}, @bitvec::BitVec::ofNat(64, {j}))) = True"),
                        format!("trans(cong_fn<BitVec(64), Bool>(call_stack_access().writable, {prefix}_store_offset_{i}_{j}()), {prefix}_write_literal_{i}_{j}())"), true);
                    fields.push(format!("byte{j} := {prefix}_write_permission_{i}_{j}(gprs, flags, stack)"));
                }
                state_decl(module, &format!("{prefix}_literal_permissions_{i}"),
                    format!("WordWritesAllowed<CallMemory>(call_stack_access(), {base})"), format!("WordWritesAllowed({})", fields.join(", ")), true);
                state_decl(module, &format!("{prefix}_slot_address_{i}"), format!("{base} = {actual_base}"),
                    format!("sym({prefix}_store_base_{i}(gprs, flags, stack))"), true);
                state_decl(module, &format!("{prefix}_stack_permissions_{i}"),
                    format!("WordWritesAllowed<CallMemory>(call_stack_access(), {actual_base})"),
                    format!("word_writes_at(call_stack_access(), {base}, {actual_base}, {prefix}_slot_address_{i}(gprs, flags, stack), {prefix}_literal_permissions_{i}(gprs, flags, stack))"), true);
            } else {
                let permissions = certify_stack_permissions(module, words, prefix, i, rsp);
                let expected_address = format!("read_gpr(Rsp, {before}.gprs)");
                state_decl(module, &format!("{prefix}_stack_address_{i}"), format!("{} = {expected_address}", word(rsp)), format!("sym({prefix}_rsp_{i}(gprs, flags, stack))"), true);
                state_decl(module, &format!("{prefix}_stack_permissions_{i}"),
                    format!("StackReadsAllowed(call_stack_access(), 8, {expected_address})"),
                    format!("stack_reads_at(call_stack_access(), 8, {}, {expected_address}, {prefix}_stack_address_{i}(gprs, flags, stack), {permissions})", word(rsp)), true);
            }
        }
        if matches!(op, Op::Call(_) | Op::Ret) {
            let target_proof = if let Op::Call(symbol) = op {
                let delta = displacement(pc, layout.symbols[symbol])? as u32;
                let extended = word((delta as i32 as i64) as u64);
                thm(module, &format!("{prefix}_displacement_{i}"), format!("@bitvec::BitVec::sign_extend(31, 32, @bitvec::BitVec::ofNat(32, {delta})) = {extended}"), "refl".into());
                let add_proof = if (delta as i32) < 0 {
                    let magnitude = word(-(delta as i32 as i64) as u64);
                    certify_sub(module, words, &format!("{prefix}_negative_offset_{i}"), 0, -(delta as i32 as i64) as u64);
                    certify_sub(module, words, &format!("{prefix}_target_sub_{i}"), pc + 5, -(delta as i32 as i64) as u64);
                    format!("trans(cong_fn<BitVec(64), BitVec(64)>(λ offset => @bitvec::BitVec::add(64, {}, offset), sym({prefix}_negative_offset_{i}())), trans(add_negative(64, {}, {magnitude}), {prefix}_target_sub_{i}()))", word(pc+5), word(pc+5))
                } else {
                    certify_add(module, words, &format!("{prefix}_positive_offset_{i}"), pc+5, delta as u64);
                    format!("{prefix}_positive_offset_{i}()")
                };
                thm(module, &format!("{prefix}_target_add_{i}"), format!("@bitvec::BitVec::add(64, {}, {extended}) = {}", word(pc+5), word(next)), add_proof);
                state_decl(module, &format!("{prefix}_target_arithmetic_{i}"),
                    format!("{} = call_target({before}.rip, @bitvec::BitVec::ofNat(32, {delta}))", word(next)),
                    format!("sym(trans(cong_fn<BitVec(64), BitVec(64)>(λ pointer => @bitvec::BitVec::add(64, pointer, @bitvec::BitVec::sign_extend(31, 32, @bitvec::BitVec::ofNat(32, {delta}))), {prefix}_store_value_{i}(gprs, flags, stack)), trans(cong_fn<BitVec(64), BitVec(64)>(λ offset => @bitvec::BitVec::add(64, {}, offset), {prefix}_displacement_{i}()), {prefix}_target_add_{i}())))", word(pc+5)), true);
                format!("trans({prefix}_target_arithmetic_{i}(gprs, flags, stack), sym(call_after_target(call_stack_access(), @bitvec::BitVec::ofNat(32, {delta}), {before})))")
            } else { certify_return_target(module, words, prefix, i, &before, rsp, next, None) };
            state_decl(module, &format!("{prefix}_target_{i}"), format!("{} = {computed}.rip", word(next)), target_proof, true);
            let successor_proof = if let Op::Call(symbol) = op {
                let delta = displacement(pc, layout.symbols[symbol])? as u32;
                format!("call_after_flat(call_stack_access(), @bitvec::BitVec::ofNat(32, {delta}), {before}, {}, {}, {memory}, sym({prefix}_store_base_{i}(gprs, flags, stack)), {prefix}_target_arithmetic_{i}(gprs, flags, stack), sym({prefix}_store_equal_{i}_8(gprs, flags, stack)))", word(next_rsp), word(next))
            } else {
                thm(module, &format!("{prefix}_ret_sp_add_{i}"), format!("@bitvec::BitVec::add(64, {}, @bitvec::BitVec::ofNat(64, 8)) = {}", word(rsp), word(next_rsp)), "refl".into());
                state_decl(module, &format!("{prefix}_ret_sp_same_{i}"), format!("{} = @bitvec::BitVec::add(64, read_gpr(Rsp, {before}.gprs), @bitvec::BitVec::ofNat(64, 8))", word(next_rsp)),
                    format!("sym(trans(cong_fn<BitVec(64), BitVec(64)>(λ pointer => @bitvec::BitVec::add(64, pointer, @bitvec::BitVec::ofNat(64, 8)), {prefix}_rsp_{i}(gprs, flags, stack)), {prefix}_ret_sp_add_{i}()))"), true);
                format!("return_after_flat(call_stack_access(), {before}, {}, {}, {prefix}_ret_sp_same_{i}(gprs, flags, stack), sym({prefix}_return_value_{i}(gprs, flags, stack)))", word(next_rsp), word(next))
            };
            state_decl(module, &format!("{prefix}_successor_{i}"), format!("{after} = {computed}"), successor_proof, true);
        }

        if let Op::Normal(normal) = op {
            let decoded = format!("decoded_canonical({})", normal.heather_expr().render());
            state_decl(module, &format!("{prefix}_target_arithmetic_{i}"),
                format!("{} = next_rip({before}.rip, {decoded}.length)", word(next)), "refl".into(), true);
            let proof = if let Some(proof) = normal_flat_proof(*normal, &before, &word(next), &format!("{prefix}_target_arithmetic_{i}(gprs, flags, stack)")) {
                proof
            } else {
                state_decl(module, &format!("{prefix}_target_{i}"), format!("{} = {computed}.rip", word(next)),
                    format!("trans({prefix}_target_arithmetic_{i}(gprs, flags, stack), sym(execute_normal_advances_rip({decoded}, {before})))"), true);
                format!("machine_rebuild({computed}, {}, {memory}, {prefix}_target_{i}(gprs, flags, stack), {prefix}_memory_same_{i}(gprs, flags, stack))", word(next))
            };
            state_decl(module, &format!("{prefix}_successor_{i}"), format!("{after} = {computed}"), proof, true);
        }
        if matches!(op, Op::Store | Op::StoreArgument | Op::Load | Op::Save(_) | Op::Restore(_)) {
            state_decl(module, &format!("{prefix}_target_{i}"), format!("{} = next_rip({before}.rip, 4)", word(next)), "refl".into(), true);
            let proof = if matches!(op, Op::Store | Op::StoreArgument | Op::Save(_)) {
                format!("machine_rebuild({computed}, {}, {memory}, {prefix}_target_{i}(gprs, flags, stack), {prefix}_memory_same_{i}(gprs, flags, stack))", word(next))
            } else if let Op::Restore(r) = op {
                let value = ledger.saved(rsp)?;
                certify_return_target(module, words, prefix, i, &before, rsp, value, Some((&current_instance, false)));
                format!("stack_load_flat(call_stack_access(), {}, {before}, {}, {}, sym({prefix}_return_value_{i}(gprs, flags, stack)), {prefix}_target_{i}(gprs, flags, stack))", r.heather_name(), word(value), word(next))
            } else {
                certify_return_target(module, words, prefix, i, &before, rsp, inputs[0] ^ inputs[1], Some((&current_instance, twice)));
                format!("stack_load_flat(call_stack_access(), R11, {before}, {}, {}, sym({prefix}_return_value_{i}(gprs, flags, stack)), {prefix}_target_{i}(gprs, flags, stack))", word(inputs[0] ^ inputs[1]), word(next))
            };
            state_decl(module, &format!("{prefix}_successor_{i}"), format!("{after} = {computed}"), proof, true);
        }
        match op {
            Op::Call(symbol) => {
                let delta = displacement(pc, layout.symbols[symbol])? as u32;
                state_decl(module, &format!("{prefix}_stack_bound_{i}"), format!("@bitvec::BitVec::borrow_sub_bit(64, read_gpr(Rsp, {before}.gprs), @bitvec::BitVec::ofNat(64, 8)) = False"),
                    format!("trans(cong_fn<BitVec(64), Bool>(λ pointer => @bitvec::BitVec::borrow_sub_bit(64, pointer, @bitvec::BitVec::ofNat(64, 8)), {prefix}_rsp_{i}(gprs, flags, stack)), refl)"), true);
                state_decl(module, &format!("{prefix}_return_canonical_{i}"), format!("LowCanonical(call_return_address({before}))"),
                    format!("j(sym({prefix}_store_value_{i}(gprs, flags, stack)), λ address _ => LowCanonical(address), refl)"), true);
                state_decl(module, &format!("{prefix}_target_canonical_{i}"), format!("LowCanonical(call_target({before}.rip, @bitvec::BitVec::ofNat(32, {delta})))"),
                    format!("j({prefix}_target_arithmetic_{i}(gprs, flags, stack), λ address _ => LowCanonical(address), refl)"), true);
            }
            Op::Ret => {
                state_decl(module, &format!("{prefix}_stack_bound_{i}"), format!("@bitvec::BitVec::carry_add_bit(64, read_gpr(Rsp, {before}.gprs), @bitvec::BitVec::ofNat(64, 8)) = False"),
                    format!("trans(cong_fn<BitVec(64), Bool>(λ pointer => @bitvec::BitVec::carry_add_bit(64, pointer, @bitvec::BitVec::ofNat(64, 8)), {prefix}_rsp_{i}(gprs, flags, stack)), refl)"), true);
                state_decl(module, &format!("{prefix}_target_canonical_{i}"), format!("LowCanonical(stack_word(call_stack_access(), {before}.memory, read_gpr(Rsp, {before}.gprs)))"),
                    format!("j(sym({prefix}_return_value_{i}(gprs, flags, stack)), λ address _ => LowCanonical(address), refl)"), true);
            }
            _ => {},
        }
        let step = match op {
            Op::Normal(normal) => format!("ordinary_call_step(call_stack_access(), {}, {before}, {after}, {prefix}_successor_{i}(gprs, flags, stack))", normal.heather_expr().render()),
            Op::Call(_) => format!("⟨{prefix}_stack_bound_{i}(gprs, flags, stack), ⟨{prefix}_return_canonical_{i}(gprs, flags, stack), ⟨{prefix}_target_canonical_{i}(gprs, flags, stack), ⟨{prefix}_stack_permissions_{i}(gprs, flags, stack), {prefix}_successor_{i}(gprs, flags, stack)⟩⟩⟩⟩"),
            Op::Store | Op::StoreArgument | Op::Load | Op::Save(_) | Op::Restore(_) => format!("⟨{prefix}_stack_permissions_{i}(gprs, flags, stack), {prefix}_successor_{i}(gprs, flags, stack)⟩"),
            Op::Ret => format!("⟨{prefix}_stack_bound_{i}(gprs, flags, stack), ⟨{prefix}_target_canonical_{i}(gprs, flags, stack), ⟨{prefix}_stack_permissions_{i}(gprs, flags, stack), {prefix}_successor_{i}(gprs, flags, stack)⟩⟩⟩"),
            _ => unreachable!(),
        };
        let (fetched, span) = certify_fetch(module, words, prefix, i, &format!("{before}.memory"), pc, encoding, HEADER);
        let fetched = format!("fetched_span_at_state(call_fetch_access(), {before}.memory, {}, {span}, call_instruction_bytes({instruction}), {before}, refl, refl, refl, {fetched})", word(pc));
        if in_leaf {
            let allowed = if matches!(op, Op::Ret) {
                format!("⟨{prefix}_stack_bound_{i}(gprs, flags, stack), ⟨{prefix}_target_canonical_{i}(gprs, flags, stack), {prefix}_stack_permissions_{i}(gprs, flags, stack)⟩⟩")
            } else if matches!(op, Op::StoreArgument) { format!("{prefix}_stack_permissions_{i}(gprs, flags, stack)") } else { "trivial".into() };
            state_decl(module, &format!("{prefix}_leaf_access_{i}"), format!("CallAccessAllowed(call_stack_access(), {instruction}, {before})"), allowed, true);
            state_decl(module, &format!("{prefix}_leaf_fetch_{i}"),
                format!("FetchedFrom(call_fetch_access(), {before}.memory, InstructionBytes({before}.rip, call_instruction_bytes({instruction})))"), fetched, true);
        } else {
            state_decl(module, &format!("{prefix}_step_{i}"),
                format!("FetchedCallStep(call_fetch_access(), call_stack_access(), {instruction}, {before}, {after})"),
                format!("⟨{fetched}, {step}⟩"), true);
        }
        if matches!(op, Op::Call(_)) {
            state_decl(module, &format!("{prefix}_aligned_call_{i}"),
                format!("bitvec::BitVec::take_low(4, 60, read_gpr(Rsp, {before}.gprs)) = @bitvec::BitVec::zero(4)"),
                format!("trans(cong_fn<BitVec(64), BitVec(4)>(λ pointer => bitvec::BitVec::take_low(4, 60, pointer), {prefix}_rsp_{i}(gprs, flags, stack)), refl)"), true);
        }
        match op {
            Op::Call(_) => rsp -= 8,
            Op::Ret => rsp += 8,
            Op::Normal(Instruction::SubRR { destination: Gpr::Rsp, .. }) => rsp -= 8,
            Op::Normal(Instruction::AddRR { destination: Gpr::Rsp, .. }) | Op::Normal(Instruction::MovRR { destination: Gpr::Rsp, source: Gpr::R10 }) => rsp += 8,
            _ => {},
        }
        if matches!(op, Op::Ret) && i == leaf_end {
            current_instance = if twice || composed { format!("{prefix}_call_{leaf_start}") } else { prefix.into() };
            let values = if composed {
                let values = format!("{current_instance}_arguments");
                super::elf::valuation_expressions(module, &values, leaf_prefix, &leaf.reflected.region,
                    call_inputs.map(|n| Expr::explicit_call("bitvec::BitVec::ofNat", [Expr::name("width"), Expr::nat(n)])))?;
                values
            } else if instances.is_empty() { leaf_prefix.to_string() } else { format!("{leaf_prefix}_second") };
            certify_callee_contract(module, words, prefix, &current_instance, &values, leaf, leaf_prefix, leaf_start, leaf_end, local, twice, instances.last().map(|(_, _, name): &(usize, usize, String)| name.as_str()), call_entry.clone());
            if composed { ledger.returned(module, words, prefix, i+1, &current_instance, &values, leaf, call_inputs, callable)?; }
            instances.push((leaf_start, leaf_end, current_instance.clone()));
        }
        if matches!(op, Op::Ret) && !in_leaf { caller_end = i; }
        if composed && !in_leaf { ledger.step(module, words, prefix, i, op, rsp)?; }
        trace.push(instruction.clone()); operations.push(op.clone()); pc = next;
        if trace.len() > 128 { return Err("call trace exceeds the initial bounded profile".into()); }
    }
    let n = trace.len(); let end = state(n);
    if callable { callable::apply(module, prefix, caller, caller_start, caller_end, &operations, &trace, &instances, words); }
    fun(module, &format!("{prefix}_trace_{n}"), "List<CallInstruction>", "[]".into());
    state_decl(module, &format!("{prefix}_execution_{n}"),
        format!("FetchedCallTrace(call_fetch_access(), call_stack_access(), {prefix}_trace_{n}(), {end}, {end})"), "refl".into(), true);
    for i in (0..n).rev() {
        fun(module, &format!("{prefix}_trace_{i}"), "List<CallInstruction>", format!("Cons({}, {prefix}_trace_{}())", trace[i], i+1));
    }
    for i in (0..n).rev() {
        if callable && i > caller_start && i <= caller_end { continue; }
        if instances.iter().any(|(start, end, _)| i > *start && i <= *end) { continue; }
        let proof = if callable && i == caller_start {
            format!("call_trace_append(call_fetch_access(), call_stack_access(), {prefix}_composed_code(), {prefix}_trace_{}(), {}, {}, {end}, {prefix}_caller_execution(gprs, flags, stack), {prefix}_execution_{}(gprs, flags, stack))", caller_end+1, state(i), state(caller_end+1), caller_end+1)
        } else if let Some((_, leaf_end, instance)) = instances.iter().find(|(start, _, _)| *start == i) {
            format!("call_trace_append(call_fetch_access(), call_stack_access(), {leaf_prefix}_summary_code(), {prefix}_trace_{}(), {}, {}, {end}, {instance}_callee_execution(gprs, flags, stack), {prefix}_execution_{}(gprs, flags, stack))", leaf_end+1, state(i), state(leaf_end+1), leaf_end+1)
        } else {
            format!("call_trace_cons(call_fetch_access(), call_stack_access(), {}, {prefix}_trace_{}(), {}, {}, {end}, {prefix}_step_{i}(gprs, flags, stack), {prefix}_execution_{}(gprs, flags, stack))", trace[i], i+1, state(i), state(i+1), i+1)
        };
        state_decl(module, &format!("{prefix}_execution_{i}"),
            format!("FetchedCallTrace(call_fetch_access(), call_stack_access(), {prefix}_trace_{i}(), {}, {end})", state(i)),
            proof, true);
    }
    state_decl(module, &format!("{prefix}_loaded_execution"),
        format!("CallImageExecution({prefix}_file(), {prefix}_code(), {prefix}_trace_0(), {}, {end})", state(0)),
        format!("CallImageExecution(image := {prefix}_image(), file_correct := {prefix}_file_correct(), initial_memory := refl, execution := {prefix}_execution_0(gprs, flags, stack))"), true);
    if composed {
        composition::finish(module, words, prefix, caller, inputs, n, pc, &ledger, callable)?;
        return Ok(());
    }
    let caller_result = format!("{caller}({}, {})", word(inputs[0]), word(inputs[1]));
    let source_left = if twice { format!("{}({}, {})", leaf.reflected.source_name, word(inputs[0]), word(inputs[1])) } else { word(inputs[0]) };
    let result_start = instances.last().expect("callee instance").1 + 1;
    let last_return = state(result_start);
    let returned_source = format!("{}({source_left}, {})", leaf.reflected.source_name, word(inputs[1]));
    let result_proof = if twice {
        thm(module, &format!("{prefix}_first_source_result"),
            format!("{leaf_prefix}_second_values()(64, 0) = {source_left}"),
            format!("{leaf_prefix}_denotes_source({leaf_prefix}_values(), {leaf_prefix}_entry_graph())"));
        thm(module, &format!("{prefix}_second_source_result"),
            format!("{}({leaf_prefix}_second_values()(64, 0), {leaf_prefix}_second_values()(64, 1)) = {returned_source}", leaf.reflected.source_name),
            format!("cong_fn<BitVec(64), BitVec(64)>(λ left => {}(left, {}), {prefix}_first_source_result())", leaf.reflected.source_name, word(inputs[1])));
        format!("trans({current_instance}_callee_result(gprs, flags, stack), {prefix}_second_source_result())")
    } else { format!("{current_instance}_callee_result(gprs, flags, stack)") };
    state_decl(module, &format!("{prefix}_returned_source"),
        format!("read_gpr(Rax, {last_return}.gprs) = {returned_source}"), result_proof, true);
    let mut register = "Rax";
    let mut expression = returned_source.clone();
    let mut result_fact = format!("{prefix}_returned_source(gprs, flags, stack)");
    for (i, op) in operations.iter().enumerate().skip(result_start) {
        let before_read = format!("read_gpr({register}, {}.gprs)", state(i));
        let xor = matches!(op, Op::Normal(Instruction::XorRR { destination: Gpr::Rax, source: Gpr::R11 }));
        if matches!(op, Op::Normal(Instruction::MovRR { destination: Gpr::Rdi, source: Gpr::Rax })) { register = "Rdi"; }
        let rhs = if xor { format!("@bitvec::BitVec::bxor(64, {before_read}, {})", word(inputs[0] ^ inputs[1])) } else { before_read };
        let rhs_proof = if xor {
            expression = format!("@bitvec::BitVec::bxor(64, {expression}, {})", word(inputs[0] ^ inputs[1]));
            format!("cong_fn<BitVec(64), BitVec(64)>(λ value => @bitvec::BitVec::bxor(64, value, {}), {result_fact})", word(inputs[0] ^ inputs[1]))
        } else { result_fact };
        let after_read = format!("read_gpr({register}, {}.gprs)", state(i+1));
        let (written, value) = match op {
            Op::Load => (Gpr::R11, word(inputs[0] ^ inputs[1])),
            Op::Ret => (Gpr::Rsp, word(STACK_TOP)),
            Op::Normal(instruction) => normal_effect_fields(*instruction, &state(i))
                .map(|(register, value, _)| (register, value)).ok_or("unsupported result-register epilogue")?,
            _ => return Err("unsupported result-register epilogue".into()),
        };
        let step_proof = if written.heather_name() == register {
            format!("read_gpr_after_write({register}, {value}, {}.gprs)", state(i))
        } else {
            format!("read_gpr_after_other_write({register}, {}, {value}, {}.gprs, refl)", written.heather_name(), state(i))
        };
        state_decl(module, &format!("{prefix}_result_step_{i}"), format!("{after_read} = {rhs}"), step_proof, true);
        state_decl(module, &format!("{prefix}_result_rhs_{i}"), format!("{rhs} = {expression}"), rhs_proof, true);
        state_decl(module, &format!("{prefix}_result_at_{}", i+1), format!("{after_read} = {expression}"),
            format!("trans({prefix}_result_step_{i}(gprs, flags, stack), {prefix}_result_rhs_{i}(gprs, flags, stack))"), true);
        result_fact = format!("{prefix}_result_at_{}(gprs, flags, stack)", i+1);
    }
    let source_proof = if local {
        thm(module, &format!("{prefix}_saved_value"), format!("@bitvec::BitVec::bxor(64, {}, {}) = {}", word(inputs[0]), word(inputs[1]), word(inputs[0] ^ inputs[1])), "refl".into());
        format!("trans(cong_fn<BitVec(64), BitVec(64)>(λ saved => @bitvec::BitVec::bxor(64, {returned_source}, saved), sym({prefix}_saved_value())), sym({prefix}_source_call({}, {})))", word(inputs[0]), word(inputs[1]))
    } else { format!("sym({prefix}_source_call({}, {}))", word(inputs[0]), word(inputs[1])) };
    thm(module, &format!("{prefix}_combined_source"), format!("{expression} = {caller_result}"), source_proof);
    state_decl(module, &format!("{prefix}_exit_status"), format!("read_gpr(Rdi, {end}.gprs) = {caller_result}"),
        format!("trans({result_fact}, {prefix}_combined_source())"), true);
    state_decl(module, &format!("{prefix}_exit_request"), format!("LinuxExitRequest<CallMemory>({end}, {caller_result})"),
        format!("LinuxExitRequest(number := refl, status := {prefix}_exit_status(gprs, flags, stack))"), true);
    if twice {
        let dead = word(STACK_TOP - 32);
        let byte = proposed_result(&leaf.reflected.result, inputs) as u8;
        state_decl(module, &format!("{prefix}_dead_frame_byte"),
            format!("call_memory_read({end}.memory, {dead}) = Some(elf_byte({byte}))"), "refl".into(), true);
    }
    let (syscall_fetch, _) = certify_fetch(module, words, prefix, n, &format!("{end}.memory"), pc, &[0x0f, 0x05], HEADER);
    state_decl(module, &format!("{prefix}_syscall_fetched"),
        format!("FetchedFrom(call_fetch_access(), {end}.memory, InstructionBytes({end}.rip, linux_syscall_bytes()))"), syscall_fetch, true);
    state_decl(module, &format!("{prefix}_stack_restored"), format!("read_gpr(Rsp, {end}.gprs) = {}", word(STACK_TOP)), format!("{prefix}_rsp_{n}(gprs, flags, stack)"), true);
    Ok(())
}

fn certify_callee_contract(module: &mut Module, words: &Words, prefix: &str, instance: &str, values: &str, leaf: &SourceX86Emission,
    leaf_prefix: &str, leaf_start: usize, leaf_end: usize, local: bool, frame: bool, previous: Option<&str>, arguments: Option<[String; 2]>) {
    let state = |i| format!("{prefix}_state_{i}(gprs, flags, stack)");
    let begin = state(leaf_start); let returned = state(leaf_end+1);
    let count = leaf_end + 1 - leaf_start;
    let code = summary_instructions(leaf, local && !frame, frame);
    for j in (0..=count).rev() {
        let i = leaf_start+j;
        let before = state(i);
        let proof = if j == count { "refl".into() } else {
            format!("call_premises_cons(call_fetch_access(), call_stack_access(), {}, {leaf_prefix}_summary_suffix_{}(), {before}, {}, {returned}, {prefix}_leaf_fetch_{i}(gprs, flags, stack), {prefix}_leaf_access_{i}(gprs, flags, stack), {prefix}_successor_{i}(gprs, flags, stack), {instance}_callee_ready_{}(gprs, flags, stack))", code[j], j+1, state(i+1), j+1)
        };
        state_decl(module, &format!("{instance}_callee_ready_{j}"),
            format!("CallPremises(call_fetch_access(), call_stack_access(), {leaf_prefix}_summary_suffix_{j}(), {before}, {returned})"), proof, true);
    }
    let post = format!("λ before after => {leaf_prefix}_summary_post({values}_values(), before, after)");
    let left = previous.map_or_else(|| "refl".into(), |name|
        format!("trans({leaf_prefix}_denotes_source({leaf_prefix}_values(), {leaf_prefix}_entry_graph()), sym({name}_callee_result(gprs, flags, stack)))"));
    let right = previous.map_or_else(|| "refl".into(), |name| format!("sym({name}_callee_preserved_rsi(gprs, flags, stack))"));
    let [left, right] = arguments.unwrap_or([left, right]);
    let entry = if frame {
        state_decl(module, &format!("{instance}_callee_return_outside"),
            format!("WordOutside(@bitvec::BitVec::sub(64, read_gpr(Rsp, {begin}.gprs), @bitvec::BitVec::ofNat(64, 8)), read_gpr(Rsp, {begin}.gprs))"),
            format!("j(sym({prefix}_rsp_{leaf_start}(gprs, flags, stack)), λ rsp _ => WordOutside(@bitvec::BitVec::sub(64, rsp, @bitvec::BitVec::ofNat(64, 8)), rsp), {prefix}_return_outside())"), true);
        for j in 0..8 {
            let address = words.get(STACK_TOP-16+j);
            state_decl(module, &format!("{instance}_callee_local_outside_{j}"),
                format!("¬WordPrefixWrites(8, @bitvec::BitVec::sub(64, read_gpr(Rsp, {begin}.gprs), @bitvec::BitVec::ofNat(64, 8)), {address})"),
                format!("j(sym({prefix}_rsp_{leaf_start}(gprs, flags, stack)), λ rsp _ => ¬WordPrefixWrites(8, @bitvec::BitVec::sub(64, rsp, @bitvec::BitVec::ofNat(64, 8)), {address}), {prefix}_local_outside().byte{j})"), true);
        }
        format!("⟨{left}, ⟨{right}, ⟨{values}_entry_graph(), ⟨refl, {instance}_callee_return_outside(gprs, flags, stack)⟩⟩⟩⟩")
    } else { format!("⟨{left}, ⟨{right}, {values}_entry_graph()⟩⟩") };
    let footprint = if frame { format!("λ address => WordPrefixWrites(8, @bitvec::BitVec::sub(64, read_gpr(Rsp, {begin}.gprs), @bitvec::BitVec::ofNat(64, 8)), address)") } else { "NoWrites".into() };
    state_decl(module, &format!("{instance}_callee_applied"),
        format!("FetchedCallTrace(call_fetch_access(), call_stack_access(), {leaf_prefix}_summary_code(), {begin}, {returned}) ∧ {leaf_prefix}_summary_post({values}_values(), {begin}, {returned})"),
        format!("use_call_summary(call_fetch_access(), call_stack_access(), {leaf_prefix}_summary_code(), {post}, {leaf_prefix}_summary({values}_values()), {begin}, {returned}, {entry}, {instance}_callee_ready_0(gprs, flags, stack))"), true);
    state_decl(module, &format!("{instance}_callee_execution"),
        format!("FetchedCallTrace(call_fetch_access(), call_stack_access(), {leaf_prefix}_summary_code(), {begin}, {returned})"),
        format!("{instance}_callee_applied(gprs, flags, stack).left"), true);
    state_decl(module, &format!("{instance}_callee_post"),
        format!("{leaf_prefix}_summary_post({values}_values(), {begin}, {returned})"),
        format!("{instance}_callee_applied(gprs, flags, stack).right"), true);
    state_decl(module, &format!("{instance}_callee_contract"),
        format!("NativeIntegerCallContract<CallMemory, BitVec(8)>(stack_observation, {footprint}, {begin}, {returned}, {}({values}_values()(64, 0), {values}_values()(64, 1)), stack_word(call_stack_access(), {begin}.memory, read_gpr(Rsp, {begin}.gprs)))", leaf.reflected.source_name),
        format!("{instance}_callee_post(gprs, flags, stack).left"), true);
    state_decl(module, &format!("{instance}_callee_preserved_rsi"),
        format!("read_gpr(Rsi, {returned}.gprs) = read_gpr(Rsi, {begin}.gprs)"),
        format!("{instance}_callee_post(gprs, flags, stack).right.left"), true);
    // The callee leaves the loaded file alone. Together with the stack-level
    // footprint this is what `memory_writes_of_stack_writes` needs to restate
    // the footprint over the full memory observation.
    state_decl(module, &format!("{instance}_callee_preserved_file"),
        format!("{returned}.memory.file = {begin}.memory.file"),
        format!("{instance}_callee_post(gprs, flags, stack).right.right"), true);
    state_decl(module, &format!("{instance}_callee_result"),
        format!("read_gpr(Rax, {returned}.gprs) = {}({values}_values()(64, 0), {values}_values()(64, 1))", leaf.reflected.source_name),
        format!("{instance}_callee_contract(gprs, flags, stack).result_correct"), true);
    state_decl(module, &format!("{instance}_callee_memory_effects"),
        format!("WritesOnly(stack_observation, {footprint}, {begin}.memory, {returned}.memory)"),
        format!("{instance}_callee_contract(gprs, flags, stack).memory_effects"), true);
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn symbolic_layout_rejects_bad_references_and_ranges() {
        assert!(layout(&[]).is_err());
        assert_eq!(displacement(10, 0).unwrap(), -15);
        assert_eq!(displacement(i32::MAX as u64 - 4, 0).unwrap(), i32::MIN);
        assert!(displacement(i32::MAX as u64 - 3, 0).is_err());
        assert_eq!(displacement(0, i32::MAX as u64 + 5).unwrap(), i32::MAX);
        assert!(displacement(0, i32::MAX as u64 + 6).is_err());
        assert!(displacement(u64::MAX, 0).is_err());
        let fragment = Fragment { name: "entry".into(), ops: vec![Op::Call("missing".into())] };
        assert!(layout(&[fragment.clone()]).is_err());
        assert!(layout(&[fragment.clone(), fragment]).is_err());
        assert!(layout(&[Fragment { name: "large".into(), ops: vec![Op::Ret; 4096] }]).is_err());
    }
    #[test]
    fn call_stack_semantics_and_refusals() {
        let mut elab = super::super::native_test_base();
        let normal_forms = [
            Instruction::MovRR { destination: Gpr::Rax, source: Gpr::Rdi },
            Instruction::MovRI { destination: Gpr::Rax, immediate: 17 },
            Instruction::AddRR { destination: Gpr::Rax, source: Gpr::Rsi },
            Instruction::SubRR { destination: Gpr::Rax, source: Gpr::Rsi },
            Instruction::AndRR { destination: Gpr::Rax, source: Gpr::Rsi },
            Instruction::OrRR { destination: Gpr::Rax, source: Gpr::Rsi },
            Instruction::XorRR { destination: Gpr::Rax, source: Gpr::Rsi },
        ];
        for (i, instruction) in normal_forms.into_iter().enumerate() {
            let decoded = format!("decoded_canonical({})", instruction.heather_expr().render());
            let fields = normal_fields(instruction, "before").unwrap();
            let source = format!("import x86_64; import bitvec; theorem fields<M>(before: MachineState<M>): MachineState({fields}, next_rip(before.rip, {decoded}.length), before.memory) = execute_normal({decoded}, before) {{ refl }}");
            elab.fork().elab_module_source(&format!("normal_fields_{i}"), &source).unwrap_or_else(|e| panic!("{}", e.render(&source)));
        }
        let forwarding = "import bitvec; fn leaf(left: BitVec(64), right: BitVec(64)) -> BitVec(64) { @bitvec::BitVec::add(64, left, right) } fn forward(left: BitVec(64), right: BitVec(64)) -> BitVec(64) { leaf(left, right) } fn swapped(left: BitVec(64), right: BitVec(64)) -> BitVec(64) { leaf(right, left) } fn expression(left: BitVec(64), right: BitVec(64)) -> BitVec(64) { @bitvec::BitVec::add(64, leaf(left, right), right) }";
        elab.elab_module_source("forwarding", forwarding).unwrap_or_else(|e| panic!("{}", e.render(forwarding)));
        assert_eq!(function_ir_source::reflect_forwarded_call(&elab, "forwarding::forward").unwrap(), "forwarding::leaf");
        for name in ["forwarding::swapped", "forwarding::expression", "forwarding::missing"] {
            assert!(function_ir_source::reflect_forwarded_call(&elab, name).is_err(), "accepted unsupported wrapper {name}");
        }
        let local_source = "import bitvec; import forwarding; fn local(left: BitVec(64), right: BitVec(64)) -> BitVec(64) { @bitvec::BitVec::bxor(64, forwarding::leaf(left, right), @bitvec::BitVec::bxor(64, left, right)) }";
        elab.elab_module_source("local_wrapper", local_source).unwrap_or_else(|e| panic!("{}", e.render(local_source)));
        assert_eq!(function_ir_source::reflect_call_wrapper(&elab, "local_wrapper::local").unwrap(), ("forwarding::leaf".into(), true));
        let nested = "import bitvec; import forwarding; fn twice(left: BitVec(64), right: BitVec(64)) -> BitVec(64) { @bitvec::BitVec::bxor(64, forwarding::leaf(forwarding::leaf(left, right), right), @bitvec::BitVec::bxor(64, left, right)) } fn wrong(left: BitVec(64), right: BitVec(64)) -> BitVec(64) { @bitvec::BitVec::bxor(64, forwarding::leaf(forwarding::leaf(right, left), right), @bitvec::BitVec::bxor(64, left, right)) }";
        elab.elab_module_source("nested_wrapper", nested).unwrap_or_else(|e| panic!("{}", e.render(nested)));
        assert_eq!(function_ir_source::reflect_call_plan(&elab, "nested_wrapper::twice").unwrap(), ("forwarding::leaf".into(), true, true));
        assert!(function_ir_source::reflect_call_plan(&elab, "nested_wrapper::wrong").is_err());
        let leaf = function_ir_source::generate_elaborated_x86(&elab, "summary_leaf", "forwarding::leaf",
            [Gpr::Rdi, Gpr::Rsi], &[Gpr::Rax, Gpr::Rcx, Gpr::Rdx, Gpr::R8, Gpr::R9, Gpr::R10, Gpr::R11], Gpr::Rax).unwrap();
        let mut summary = Module::default();
        for name in ["function_ir_x86_support", "function_ir", "x86_64", "x86_64_block", "x86_64_calls", "x86_64_call_frame", "x86_64_call_summary", "elf64_calls", "bitvec", "list", "logic", "bool", "option"] {
            summary.raw(format!("import {name};"));
        }
        summary.raw(leaf.text.clone());
        emit_leaf_summary(&mut summary, "summary_leaf", &leaf, false, true);
        let source = summary.render();
        elab.elab_module_source("summary_check", &source).unwrap_or_else(|e| panic!("{}", e.render(&source)));
        let stale = "import list; import summary_check; import function_ir; import x86_64; import x86_64_calls; import x86_64_call_summary; import elf64_calls; fn stale(values: Valuation()) -> CallSummary<CallMemory>(call_stack_access(), [Ordinary(MovRR(Rax, Rsi)), NearReturn], λ before after => summary_leaf_summary_post(values, before, after)) { summary_leaf_summary(values) }";
        let error = elab.fork().elab_module_source("stale_summary", stale).expect_err("summary accepted for different code");
        assert!(format!("{error:?}").contains("NotConvertible"), "{}", error.render(stale));
        for (name, declaration) in [
            ("wrong_summary_interface", "fn bad(values: Valuation()) -> CallSummary<CallMemory>(call_stack_access(), summary_leaf_summary_code(), λ before after => read_gpr(Rax, after.gprs) = @bitvec::BitVec::zero(64)) { summary_leaf_summary(values) }"),
            ("missing_summary_fetch", "theorem bad(before: MachineState<CallMemory>): CallPremises(call_fetch_access(), call_stack_access(), [NearReturn], before, before) { trivial }"),
        ] {
            let source = format!("import list; import bitvec; import logic; import summary_check; import function_ir; import x86_64; import x86_64_calls; import x86_64_call_summary; import elf64_calls; {declaration}");
            let error = elab.fork().elab_module_source(name, &source).expect_err("accepted an incompatible summary premise");
            let expected = if name == "missing_summary_fetch" { error.render(&source).contains("`trivial` proves `True`") }
                else { format!("{error:?}").contains("NotConvertible") };
            assert!(expected, "{}", error.render(&source));
        }
        for (name, final_state, valid) in [("placed_successor", "call_next(call_stack_access(), Ordinary(MovRR(Rax, Rsi)), before)", true), ("invented_successor", "before", false)] {
            let source = format!("import list; import logic; import x86_64; import x86_64_calls; import x86_64_fetch; import x86_64_call_summary; import elf64_calls; theorem check(before: MachineState<CallMemory>, fetched: FetchedFrom(call_fetch_access(), before.memory, InstructionBytes(before.rip, call_instruction_bytes(Ordinary(MovRR(Rax, Rsi)))))): CallPremises(call_fetch_access(), call_stack_access(), [Ordinary(MovRR(Rax, Rsi))], before, {final_state}) {{ ⟨{final_state}, ⟨fetched, ⟨trivial, ⟨refl, refl⟩⟩⟩⟩ }}");
            let checked = elab.fork().elab_module_source(name, &source);
            if valid { checked.unwrap_or_else(|e| panic!("{}", e.render(&source))); }
            else { let error = checked.expect_err("accepted an invented callee state"); assert!(format!("{error:?}").contains("NotConvertible"), "{}", error.render(&source)); }
        }
        let imports = "import x86_64; import x86_64_call_frame; import x86_64_calls; import elf64_calls; import bitvec; import bool; import list; import logic; import option; import nat; import elf64_load;";
        // Long instruction near the end of a file, with arbitrary stack bytes.
        // Corrupting the requested byte must fail the file-observation proof.
        let actual = super::super::encode(&[Instruction::MovRI { destination: Gpr::Rax, immediate: 0x0123456789abcdef }]);
        let mut file = vec![0; 512]; file[496..496+actual.len()].copy_from_slice(&actual);
        let words = Words { prefix: "fetch_fixture".into(), values: Default::default() };
        let mut fetch_cases = Vec::new();
        for valid in [true, false] {
            let requested = if valid { actual.clone() } else { vec![actual[0] ^ 1] };
            let mut proofs = Module::default();
            certify_fetch(&mut proofs, &words, "fetch_fixture", 0, "memory", 0x4001f0, &requested, 256);
            fetch_cases.push((valid, proofs));
        }
        let mut fixture = Module::default(); fixture.raw(format!("{imports} import elf64;"));
        byte_chain(&mut fixture, "fetch_fixture_header", &file[..256]);
        byte_chain(&mut fixture, "fetch_fixture_code", &file[256..]);
        drop_chain(&mut fixture, "fetch_fixture_code", file.len()-256);
        fun(&mut fixture, "fetch_fixture_file", "List<BitVec(8)>", "fetch_fixture_header() ++ fetch_fixture_code()".into());
        thm(&mut fixture, "fetch_fixture_header_length", "fetch_fixture_header().len() = 256".into(), "refl".into());
        for value in words.values.into_inner() {
            fun(&mut fixture, &format!("fetch_fixture_word_{value:x}"), "BitVec(64)", word(value));
        }
        let source = fixture.render();
        elab.elab_module_source("file_fixture", &source).unwrap_or_else(|e| panic!("{}", e.render(&source)));
        for (valid, proofs) in fetch_cases {
            let mut module = Module::default();
            module.raw(format!("{imports} import x86_64_fetch; import elf64; import file_fixture;"));
            module.extend(proofs);
            let source = module.render();
            let checked = elab.fork().elab_module_source(if valid { "file_fetch" } else { "wrong_file_fetch" }, &source);
            if valid { checked.unwrap_or_else(|e| panic!("{}", e.render(&source))); }
            else { let error = checked.expect_err("accepted a corrupted file fetch"); assert!(format!("{error:?}").contains("NotConvertible"), "{}", error.render(&source)); }
        }
        let offsets = Words { prefix: "offset_literal".into(), values: Default::default() };
        let mut offset_proofs = Module::default();
        certify_add(&mut offset_proofs, &offsets, "forward_offset", 0x4000fd, 112);
        certify_add(&mut offset_proofs, &offsets, "wrapped_word_add", u64::MAX-2, 4);
        certify_add(&mut offset_proofs, &offsets, "large_word_add", 1 << 63, 1 << 63);
        certify_sub(&mut offset_proofs, &offsets, "wrapped_word_sub", 0, 1 << 63);
        let mut offset_module = Module::default();
        offset_module.raw(imports);
        for value in offsets.values.into_inner() {
            fun(&mut offset_module, &format!("offset_literal_word_{value:x}"), "BitVec(64)", word(value));
        }
        offset_module.extend(offset_proofs);
        let source = offset_module.render();
        elab.elab_module_source("offset_checks", &source).unwrap_or_else(|e| panic!("{}", e.render(&source)));
        let source = format!("{imports} import offset_checks; theorem wrong_target(): @bitvec::BitVec::add(64, {}, {}) = {} {{ forward_offset() }}", word(0x4000fd), word(112), word(0x40016e));
        let error = elab.fork().elab_module_source("wrong_forward_target", &source).expect_err("accepted the wrong positive displacement result");
        assert!(format!("{error:?}").contains("NotConvertible"), "{}", error.render(&source));
        let source = format!("{imports}\nfn start(rsp: BitVec(64)) -> MachineState<CallMemory> {{ MachineState(write_gpr(Rsp, rsp, zero_gprs()), clear_flags(), {}, CallMemory([], λ address => @bitvec::BitVec::ofNat(8, 0))) }}", word(0x400100));
        elab.elab_module_source("call_test", &source).unwrap_or_else(|e| panic!("{}", e.render(&source)));
        for (name, protected, valid) in [("private_word", 0x401fe8, true), ("overlapping_word", 0x401fe0, false)] {
            let mut proofs = Module::default();
            let words = Words { prefix: name.into(), values: Default::default() };
            certify_word_outside(&mut proofs, &words, "outside", 0x401fe0, protected);
            let mut declarations = Module::default();
            declarations.raw(imports);
            for value in words.values.into_inner() {
                fun(&mut declarations, &format!("{name}_word_{value:x}"), "BitVec(64)", word(value));
            }
            declarations.extend(proofs);
            let slot = word(0x401fe0); let protected = word(protected);
            let changed_value = word(0x0700000000000000);
            let last = format!("@bitvec::BitVec::add(64, {slot}, @bitvec::BitVec::ofNat(64, 7))");
            thm(&mut declarations, "changed",
                format!("word_write_8(call_stack_access(), {changed_value}, CallMemory([], λ address => @bitvec::BitVec::zero(8)), {slot}).stack({last}) = @bitvec::BitVec::ofNat(8, 7)"),
                format!("stack_write_same(word_write_7(call_stack_access(), {changed_value}, CallMemory([], λ address => @bitvec::BitVec::zero(8)), {slot}), {last}, imm_byte7({changed_value}))"));
            declarations.declaration(Declaration::theorem("preserved",
                Expr::raw(format!("stack_word(call_stack_access(), word_write_8(call_stack_access(), @bitvec::BitVec::ofNat(64, 7), CallMemory([], stack), {slot}), {protected}) = stack_word(call_stack_access(), CallMemory([], stack), {protected})")),
                Block::expression(Expr::raw(format!("stored_word_preserves_return(CallMemory([], stack), {slot}, @bitvec::BitVec::ofNat(64, 7), {protected}, outside())"))))
                .parameter(Parameter::explicit("stack", Expr::raw("BitVec(64) → BitVec(8)"))));
            let source = declarations.render();
            let checked = elab.fork().elab_module_source(name, &source);
            if valid { checked.unwrap_or_else(|e| panic!("{}", e.render(&source))); }
            else { let error = checked.expect_err("accepted a write over the protected return word"); assert!(format!("{error:?}").contains("NotConvertible"), "{}", error.render(&source)); }
        }
        // Test the exact access/underflow premises required by CallStep independently.
        for (name, claim, valid) in [
            ("writable_return_slot", format!("call_stack_access().writable({}) = True", word(0x401ff8)), true),
            ("exhausted_stack", format!("call_stack_access().writable({}) = True", word(0x400ff8)), false),
            ("stack_underflow", format!("@bitvec::BitVec::borrow_sub_bit(64, {}, @bitvec::BitVec::ofNat(64, 8)) = False", word(0)), false),
            ("empty_return", format!("call_stack_access().readable({}) = True", word(0x402000)), false),
            ("noncanonical_stack", format!("LowCanonical({})", word(1u64 << 47)), false),
        ] {
            let source = format!("{imports} import call_test; theorem check(): {claim} {{ refl }}");
            let checked = elab.fork().elab_module_source(name, &source);
            if valid { checked.unwrap_or_else(|e| panic!("{}", e.render(&source))); }
            else { let error = checked.expect_err("invalid stack premise accepted"); assert!(format!("{error:?}").contains("NotConvertible"), "{}", error.render(&source)); }
        }
        for (name, opcode, delta, valid) in [("call_encoding", 0xe8, 0x20, true), ("wrong_call_opcode", 0xe9, 0x20, false), ("wrong_call_displacement", 0xe8, 0x21, false)] {
            let source = format!("{imports} fn actual() -> List<BitVec(8)> {{ [@bitvec::BitVec::ofNat(8, {opcode}), @bitvec::BitVec::ofNat(8, {delta}), @bitvec::BitVec::ofNat(8, 0), @bitvec::BitVec::ofNat(8, 0), @bitvec::BitVec::ofNat(8, 0)] }} theorem encoding(): actual() = call_instruction_bytes(CallRelative(@bitvec::BitVec::ofNat(32, 0x20))) {{ refl }}");
            let checked = elab.fork().elab_module_source(name, &source);
            if valid { checked.unwrap_or_else(|e| panic!("{}", e.render(&source))); }
            else { let error = checked.expect_err("corrupted CALL encoding accepted"); assert!(format!("{error:?}").contains("NotConvertible"), "{}", error.render(&source)); }
        }
        for (name, opcode, sib, valid) in [("stack_store_encoding", 0x89, 0x24, true), ("wrong_stack_opcode", 0x8b, 0x24, false), ("wrong_stack_address", 0x89, 0x25, false)] {
            let source = format!("{imports} fn actual() -> List<BitVec(8)> {{ [@bitvec::BitVec::ofNat(8, 0x4c), @bitvec::BitVec::ofNat(8, {opcode}), @bitvec::BitVec::ofNat(8, 0x1c), @bitvec::BitVec::ofNat(8, {sib})] }} theorem encoding(): actual() = call_instruction_bytes(StoreStack64(R11)) {{ refl }}");
            let checked = elab.fork().elab_module_source(name, &source);
            if valid { checked.unwrap_or_else(|e| panic!("{}", e.render(&source))); }
            else { let error = checked.expect_err("invalid stack encoding accepted"); assert!(format!("{error:?}").contains("NotConvertible"), "{}", error.render(&source)); }
        }
        let local = word(0x401fe0); let shared = word(0x401fd0); let live = word(0x401ff0);
        let source = format!("{imports} fn base(stack: BitVec(64) -> BitVec(8)) -> CallMemory {{ CallMemory([], stack) }} fn changed(stack: BitVec(64) -> BitVec(8), byte: BitVec(8)) -> CallMemory {{ call_memory_write(base(stack), {local}, byte) }} theorem effects(stack: BitVec(64) -> BitVec(8), byte: BitVec(8)): WritesOnly(call_memory_read, ByteWrite({local}), base(stack), changed(stack, byte)) {{ memory_write_effect(base(stack), {local}, byte) }} theorem outside(): DisjointWrites(ByteWrite({local}), λ address => address = {live}) {{ point_disjoint(ByteWrite({local}), {live}, λ bad => absurd(bad)) }} theorem live_byte(stack: BitVec(64) -> BitVec(8), byte: BitVec(8)): call_memory_read(changed(stack, byte), {live}) = call_memory_read(base(stack), {live}) {{ protected_read(call_memory_read, ByteWrite({local}), λ address => address = {live}, base(stack), changed(stack, byte), outside(), effects(stack, byte), {live}, refl) }} theorem shared_effect(stack: BitVec(64) -> BitVec(8), first, second: BitVec(8)): WritesOnly(call_memory_read, UnionWrites(ByteWrite({local}), ByteWrite({shared})), base(stack), call_memory_write(changed(stack, first), {shared}, second)) {{ writes_only_compose(call_memory_read, ByteWrite({local}), ByteWrite({shared}), base(stack), changed(stack, first), call_memory_write(changed(stack, first), {shared}, second), effects(stack, first), memory_write_effect(changed(stack, first), {shared}, second)) }}");
        let source = format!("{source} fn policy() -> CallMemoryPolicy {{ CallMemoryPolicy(ByteWrite({local}), ByteWrite({shared}), λ address => address = {live}, point_disjoint(ByteWrite({local}), {live}, λ bad => absurd(bad)), point_disjoint(ByteWrite({shared}), {live}, λ bad => absurd(bad))) }} theorem child_in_parent(stack: BitVec(64) -> BitVec(8), byte: BitVec(8)): WritesOnly(call_memory_read, permitted_writes(policy()), base(stack), changed(stack, byte)) {{ writes_only_weaken(call_memory_read, ByteWrite({local}), permitted_writes(policy()), base(stack), changed(stack, byte), λ address witness => Inl(witness), effects(stack, byte)) }} theorem policy_live(stack: BitVec(64) -> BitVec(8), byte: BitVec(8)): call_memory_read(changed(stack, byte), {live}) = call_memory_read(base(stack), {live}) {{ protected_read(call_memory_read, permitted_writes(policy()), policy().protected, base(stack), changed(stack, byte), policy_disjoint(policy()), child_in_parent(stack, byte), {live}, refl) }}");
        elab.elab_module_source("frame_checks", &source).unwrap_or_else(|e| panic!("{}", e.render(&source)));
        for (name, address, valid) in [("dead_local_may_change", local.clone(), true), ("live_slot_cannot_change", live.clone(), false), ("return_slot_cannot_change", word(0x401ff8), false)] {
            let source = format!("{imports} import frame_checks; theorem check(): call_memory_read(changed(λ address => @bitvec::BitVec::ofNat(8, 0), @bitvec::BitVec::ofNat(8, 7)), {address}) = Some(@bitvec::BitVec::ofNat(8, 7)) {{ refl }}");
            let checked = elab.fork().elab_module_source(name, &source);
            if valid { checked.unwrap_or_else(|e| panic!("{}", e.render(&source))); }
            else { let error = checked.expect_err("protected byte changed"); assert!(format!("{error:?}").contains("NotConvertible"), "{}", error.render(&source)); }
        }
        let source = format!("{imports} import frame_checks; fn overlapping() -> CallMemoryPolicy {{ CallMemoryPolicy(ByteWrite({local}), NoWrites, λ address => address = {local}, outside(), λ address impossible live => impossible) }}");
        let error = elab.fork().elab_module_source("overlapping_policy", &source).expect_err("overlapping frame accepted");
        assert!(format!("{error:?}").contains("NotConvertible"), "{}", error.render(&source));
        for (name, restored, valid) in [("contract_restores_rsp", 0x401ff8, true), ("missing_frame_release", 0x401ff0, false)] {
            let before = format!("start({})", word(0x401ff0)); let after = format!("start({})", word(restored));
            let source = format!("{imports} import call_test; theorem contract(): NativeIntegerCallContract<CallMemory, BitVec(8)>(stack_observation, NoWrites, {before}, {after}, @bitvec::BitVec::zero(64), {before}.rip) {{ NativeIntegerCallContract(result_correct := refl, returned_to := refl, stack_restored := refl, memory_effects := writes_only_equal(stack_observation, NoWrites, {before}.memory, {after}.memory, refl), preserved_rbx := refl, preserved_rbp := refl, preserved_r12 := refl, preserved_r13 := refl, preserved_r14 := refl, preserved_r15 := refl) }}");
            let checked = elab.fork().elab_module_source(name, &source);
            if valid { checked.unwrap_or_else(|e| panic!("{}", e.render(&source))); }
            else { let error = checked.expect_err("unrestored frame accepted"); assert!(format!("{error:?}").contains("NotConvertible"), "{}", error.render(&source)); }
        }
        // The extra ELF segment must remain RW, never executable.
        for (name, flags, valid) in [("stack_segment_flags", 6, true), ("executable_stack_segment", 7, false)] {
            let source = format!("{imports} fn expected() -> List<BitVec(8)> {{ [@bitvec::BitVec::ofNat(8, {flags}), @bitvec::BitVec::ofNat(8, 0), @bitvec::BitVec::ofNat(8, 0), @bitvec::BitVec::ofNat(8, 0)] }} theorem flags(): list::List::take(list::List::drop(call_elf_header(@bitvec::BitVec::ofNat(8, 233), @bitvec::BitVec::ofNat(8, 0)), 180), 4) = expected() {{ refl }}");
            let checked = elab.fork().elab_module_source(name, &source);
            if valid { checked.unwrap_or_else(|e| panic!("{}", e.render(&source))); }
            else { let error = checked.expect_err("executable stack header accepted"); assert!(format!("{error:?}").contains("NotConvertible"), "{}", error.render(&source)); }
        }
        let source = format!("{imports} import call_test; theorem stored(byte: BitVec(8)): call_memory_write(start({}).memory, {}, byte).stack({}) = byte {{ refl }} theorem disjoint(byte: BitVec(8)): call_memory_write(start({}).memory, {}, byte).stack({}) = @bitvec::BitVec::ofNat(8, 0) {{ refl }}", word(0x402000), word(0x401ff8), word(0x401ff8), word(0x402000), word(0x401ff8), word(0x401ff9));
        elab.elab_module_source("stack_store", &source).unwrap_or_else(|e| panic!("{}", e.render(&source)));
        let source = format!("{imports} import call_test; fn actual() -> CallMemory {{ word_write_1(call_stack_access(), {}, start({}).memory, {}) }} fn proposed() -> CallMemory {{ call_memory_write(start({}).memory, {}, @bitvec::BitVec::ofNat(8, 5)) }} theorem pointer(): @bitvec::BitVec::add(64, {}, @bitvec::BitVec::ofNat(64, 0)) = {} {{ refl }} theorem first_write(): actual() = proposed() {{ call_memory_write_cong(start({}).memory, start({}).memory, @bitvec::BitVec::add(64, {}, @bitvec::BitVec::ofNat(64, 0)), {}, imm_byte0({}), @bitvec::BitVec::ofNat(8, 5), refl, pointer(), refl) }}", word(0x400105), word(0x402000), word(0x401ff8), word(0x402000), word(0x401ff8), word(0x401ff8), word(0x401ff8), word(0x402000), word(0x402000), word(0x401ff8), word(0x401ff8), word(0x400105));
        elab.elab_module_source("first_write", &source).unwrap_or_else(|e| panic!("{}", e.render(&source)));
        for (name, expected, valid) in [("return_byte", 5, true), ("corrupted_return_byte", 6, false)] {
            let source = format!("{imports} import first_write; theorem check(): actual().stack({}) = @bitvec::BitVec::ofNat(8, {expected}) {{ trans(cong_fn<CallMemory, BitVec(8)>(λ memory => memory.stack({}), first_write()), refl) }}", word(0x401ff8), word(0x401ff8));
            let checked = elab.fork().elab_module_source(name, &source);
            if valid { checked.unwrap_or_else(|e| panic!("{}", e.render(&source))); }
            else { let error = checked.expect_err("corrupted return byte accepted"); assert!(format!("{error:?}").contains("NotConvertible"), "{}", error.render(&source)); }
        }
    }
}
