//! Small final-image layout and proof producer for a forwarding caller and leaf.
use std::collections::BTreeMap;
use heather_elab::function_ir_source::{self, SourceX86Emission};
use heather_elab::function_ir_x86_lower::{Gpr, Instruction};
use heather_elab::heather_emit::{Block, Declaration, Expr, Module, Parameter};
use heather_elab::Elaborator;

const ENTRY: u64 = 0x4000e8;
const HEADER: usize = 232;
const STACK_TOP: u64 = 0x402000;

#[derive(Clone, Debug)]
enum Op { Normal(Instruction), Call(String), Ret, Store, Load, Syscall }
impl Op {
    fn len(&self) -> usize { match self { Self::Normal(i) => super::encode(&[*i]).len(), Self::Call(_) => 5, Self::Ret => 1, Self::Store | Self::Load => 4, Self::Syscall => 2 } }
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
                    (encoded, format!("CallRelative(bitvec::ofNat(32, {}))", delta as u32))
                }
                Op::Ret => (vec![0xc3], "NearReturn".into()),
                Op::Syscall => (vec![0x0f, 0x05], String::new()),
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
// Certify subtraction through literal intermediate values, keeping each reduction small.
fn certify_sub(module: &mut Module, words: &Words, name: &str, start: u64, count: u64) {
    let word = |n| words.get(n);
    let mut previous = 0;
    for remaining in 0..=count {
        if remaining != 0 && remaining % 4 != 0 && remaining != count { continue; }
        let value = start.wrapping_sub(count - remaining);
        let body = if remaining == 0 { "refl".into() } else {
            let chunk = remaining - previous;
            thm(module, &format!("{name}_decrement_{remaining}"),
                format!("bitvec::iterate_decrement(64, {chunk}, {}) = {}", word(value), word(value.wrapping_sub(chunk))), "refl".into());
            format!("trans(cong_fn<BitVec(64), BitVec(64)>(λ value => bitvec::iterate_decrement(64, {previous}, value), {name}_decrement_{remaining}()), {name}_steps_{previous}())")
        };
        thm(module, &format!("{name}_steps_{remaining}"),
            format!("bitvec::iterate_decrement(64, {remaining}, {}) = {}", word(value), word(start.wrapping_sub(count))), body);
        previous = remaining;
    }
    thm(module, name, format!("bitvec::sub(64, {}, {}) = {}", word(start), word(count), word(start.wrapping_sub(count))), format!("{name}_steps_{count}()"));
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
    format!("bitvec::from_bits(64, [{bits}])")
}
fn bytes(bytes: &[u8]) -> Expr { Expr::list(bytes.iter().map(|b| Expr::call("elf_byte", [Expr::nat(u64::from(*b))]))) }
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
fn certify_fetch(module: &mut Module, words: &Words, prefix: &str, index: usize, memory: &str, pc: u64, encoding: &[u8]) -> String {
    let word = |n| words.get(n);
    for j in (0..encoding.len()).rev() {
        let address = word(pc + j as u64);
        let byte = format!("elf_byte({})", encoding[j]);
        let fact = |kind| format!("{prefix}_{kind}_{index}_{j}");
        for (kind, ty) in [
            ("permission", format!("call_fetch_access().executable({memory}, {address}) = True")),
            ("read", format!("call_fetch_access().read_byte({memory}, {address}) = Some({byte})")),
        ] { state_decl(module, &fact(kind), ty, "refl".into(), true); }
        let proof = if j+1 == encoding.len() {
            format!("fetch_span_one(call_fetch_access(), {memory}, {address}, {byte}, {}(gprs, flags, stack), {}(gprs, flags, stack))", fact("permission"), fact("read"))
        } else {
            let next = word(pc + j as u64 + 1);
            for (kind, ty) in [("nowrap", format!("bitvec::carry_add_bit(64, {address}, bitvec::ofNat(64, 1)) = False")),
                ("next", format!("next_rip({address}, 1) = {next}"))] {
                thm(module, &fact(kind), ty, "refl".into());
            }
            format!("fetch_span_more(call_fetch_access(), {memory}, {address}, {next}, {byte}, elf_byte({}), {}, {}(gprs, flags, stack), {}(gprs, flags, stack), {}(), {}(), {prefix}_byte_{index}_{}(gprs, flags, stack))",
                encoding[j+1], bytes(&encoding[j+2..]).render(), fact("permission"), fact("read"), fact("nowrap"), fact("next"), j+1)
        };
        state_decl(module, &format!("{prefix}_byte_{index}_{j}"),
            format!("FetchedFrom(call_fetch_access(), {memory}, InstructionBytes({address}, {}))", bytes(&encoding[j..]).render()), proof, true);
    }
    format!("{prefix}_byte_{index}_0(gprs, flags, stack)")
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

fn certify_call_memory(module: &mut Module, words: &Words, prefix: &str, i: usize, before: &str, sp: u64, pc: u64, delta: u32, local: Option<u64>) -> (String, String) {
    let word = |n| words.get(n);
    let slot = sp - if local.is_some() { 0 } else { 8 };
    let stored = local.unwrap_or(pc + 5);
    let base = if local.is_some() { format!("read_gpr(Rsp, {before}.gprs)") }
        else { format!("bitvec::sub(64, read_gpr(Rsp, {before}.gprs), bitvec::ofNat(64, 8))") };
    let value = if local.is_some() { format!("read_gpr(R11, {before}.gprs)") } else { format!("call_return_address({before})") };
    let literal_base = word(slot);
    let literal_value = word(stored);
    let fact = |kind: &str| format!("{prefix}_store_{kind}_{i}(gprs, flags, stack)");
    if local.is_some() {
        state_decl(module, &format!("{prefix}_store_base_{i}"), format!("{base} = {literal_base}"), format!("{prefix}_rsp_{i}(gprs, flags, stack)"), true);
    } else {
    thm(module, &format!("{prefix}_store_sub_{i}"), format!("bitvec::sub(64, {}, bitvec::ofNat(64, 8)) = {literal_base}", word(sp)), "refl".into());
    state_decl(module, &format!("{prefix}_store_base_{i}"), format!("{base} = {literal_base}"),
        format!("trans(cong_fn<BitVec(64), BitVec(64)>(λ pointer => bitvec::sub(64, pointer, bitvec::ofNat(64, 8)), {prefix}_rsp_{i}(gprs, flags, stack)), {prefix}_store_sub_{i}())"), true);
    }
    state_decl(module, &format!("{prefix}_store_value_{i}"), format!("{value} = {literal_value}"), "refl".into(), true);
    let memory = |j| format!("{prefix}_store_memory_{i}_{j}(gprs, flags, stack)");
    state_decl(module, &format!("{prefix}_store_memory_{i}_0"), "CallMemory".into(), format!("{before}.memory"), false);
    state_decl(module, &format!("{prefix}_store_equal_{i}_0"), format!("word_write_0(call_stack_access(), {value}, {before}.memory, {base}) = {}", memory(0)), "refl".into(), true);
    for j in 0..8 {
        let address = word(slot+j as u64); let byte = stored.to_le_bytes()[j];
        thm(module, &format!("{prefix}_store_offset_{i}_{j}"), format!("bitvec::add(64, {literal_base}, bitvec::ofNat(64, {j})) = {address}"), "refl".into());
        thm(module, &format!("{prefix}_store_byte_literal_{i}_{j}"), format!("imm_byte{j}({literal_value}) = elf_byte({byte})"), "refl".into());
        state_decl(module, &format!("{prefix}_store_address_{i}_{j}"), format!("bitvec::add(64, {base}, bitvec::ofNat(64, {j})) = {address}"),
            format!("trans(cong_fn<BitVec(64), BitVec(64)>(λ pointer => bitvec::add(64, pointer, bitvec::ofNat(64, {j})), {}), {prefix}_store_offset_{i}_{j}())", fact("base")), true);
        state_decl(module, &format!("{prefix}_store_byte_{i}_{j}"), format!("imm_byte{j}({value}) = elf_byte({byte})"),
            format!("trans(cong_fn<BitVec(64), BitVec(8)>(imm_byte{j}, {}), {prefix}_store_byte_literal_{i}_{j}())", fact("value")), true);
        state_decl(module, &format!("{prefix}_store_memory_{i}_{}", j+1), "CallMemory".into(),
            format!("CallMemory({prefix}_file(), call_memory_write({}, {address}, elf_byte({byte})).stack)", memory(j)), false);
        state_decl(module, &format!("{prefix}_store_equal_{i}_{}", j+1),
            format!("word_write_{}(call_stack_access(), {value}, {before}.memory, {base}) = {}", j+1, memory(j+1)),
            format!("call_memory_write_cong(word_write_{j}(call_stack_access(), {value}, {before}.memory, {base}), {}, bitvec::add(64, {base}, bitvec::ofNat(64, {j})), {address}, imm_byte{j}({value}), elf_byte({byte}), {prefix}_store_equal_{i}_{j}(gprs, flags, stack), {prefix}_store_address_{i}_{j}(gprs, flags, stack), {prefix}_store_byte_{i}_{j}(gprs, flags, stack))", memory(j)), true);
    }
    let model_memory = if local.is_some() { format!("stack_store_memory(call_stack_access(), R11, {before})") }
        else { format!("call_after_memory(call_stack_access(), bitvec::ofNat(32, {delta}), {before})") };
    (memory(8), format!("sym(trans({model_memory}, {prefix}_store_equal_{i}_8(gprs, flags, stack)))"))
}

fn certify_return_target(module: &mut Module, words: &Words, prefix: &str, i: usize, before: &str, sp: u64, target: u64, from_contract: bool) -> String {
    let word = |n| words.get(n);
    let base = word(sp); let value = word(target);
    let mut fields = Vec::new();
    for j in 0..8 {
        let query = if j == 0 { base.clone() } else { format!("bitvec::add(64, {base}, bitvec::ofNat(64, {j}))") };
        let literal = word(sp+j as u64);
        thm(module, &format!("{prefix}_read_address_{i}_{j}"), format!("{query} = {literal}"), "refl".into());
        let read_proof = if from_contract {
            format!("trans(cong_fn<Option<BitVec(8)>, BitVec(8)>(call_read_value, {prefix}_callee_memory_effects(gprs, flags, stack)({literal}, λ impossible => impossible)), refl)")
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
    requested_callee: &str, inputs: [u64; 2]) -> Result<Vec<u8>, String>
{
    let (callee, local) = function_ir_source::reflect_call_wrapper(elab, caller).map_err(|e| e.to_string())?;
    if callee != requested_callee { return Err(format!("caller resolves to `{callee}`, not opted-in callee `{requested_callee}`")); }
    let leaf_prefix = format!("{prefix}_leaf");
    let leaf = function_ir_source::generate_elaborated_x86(elab, &leaf_prefix, &callee,
        [Gpr::Rdi, Gpr::Rsi], &[Gpr::Rax, Gpr::Rcx, Gpr::Rdx, Gpr::R8, Gpr::R9, Gpr::R10, Gpr::R11], Gpr::Rax)
        .map_err(|e| format!("callee: {e}"))?;
    let normal = |i| Op::Normal(i);
    let mov = |r, value| normal(Instruction::MovRI { destination: r, immediate: value });
    let mut leaf_ops = leaf.instructions.iter().copied().map(normal).collect::<Vec<_>>();
    if local { leaf_ops.push(normal(Instruction::XorRR { destination: Gpr::R11, source: Gpr::R11 })); }
    leaf_ops.push(Op::Ret);
    let mut caller_ops = vec![mov(Gpr::R11, 8), normal(Instruction::SubRR { destination: Gpr::Rsp, source: Gpr::R11 })];
    if local { caller_ops.extend([normal(Instruction::MovRR { destination: Gpr::R11, source: Gpr::Rdi }),
        normal(Instruction::XorRR { destination: Gpr::R11, source: Gpr::Rsi }), Op::Store]); }
    caller_ops.push(Op::Call("leaf".into()));
    if local { caller_ops.extend([Op::Load, normal(Instruction::XorRR { destination: Gpr::Rax, source: Gpr::R11 })]); }
    caller_ops.extend([mov(Gpr::R11, 8), normal(Instruction::AddRR { destination: Gpr::Rsp, source: Gpr::R11 }), Op::Ret]);
    // Place the leaf before the wrapper: its call deliberately exercises a negative rel32.
    let fragments = vec![
        Fragment { name: "entry".into(), ops: vec![mov(Gpr::Rsp, STACK_TOP), mov(Gpr::Rdi, inputs[0]), mov(Gpr::Rsi, inputs[1]),
            Op::Call("caller".into()), normal(Instruction::MovRR { destination: Gpr::Rdi, source: Gpr::Rax }), mov(Gpr::Rax, 60), Op::Syscall] },
        Fragment { name: "leaf".into(), ops: leaf_ops },
        Fragment { name: "caller".into(), ops: caller_ops },
    ];
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
    for name in ["x86_64_calls", "x86_64_call_frame", "elf64_calls"] { module.raw(format!("import {name};")); }
    module.raw(leaf.text.clone());
    super::elf::valuation(module, &leaf_prefix, &leaf.reflected.region, inputs)?;
    module.declaration(Declaration::theorem(format!("{prefix}_source_call"),
        Expr::raw(format!("{caller}(left, right) = {}", if local { format!("bitvec::bxor(64, {callee}(left, right), bitvec::bxor(64, left, right))") } else { format!("{callee}(left, right)") })), Block::expression(Expr::name("refl")))
        .parameter(Parameter::explicit("left", Expr::raw("BitVec(64)")))
        .parameter(Parameter::explicit("right", Expr::raw("BitVec(64)"))));
    module.declaration(Declaration::function(format!("{prefix}_code"), Expr::raw("List<BitVec(8)>"), Block::expression(bytes(&layout.bytes))));
    module.declaration(Declaration::function(format!("{prefix}_header"), Expr::raw("List<BitVec(8)>"), Block::expression(bytes(&file[..HEADER]))));
    fun(module, &format!("{prefix}_file"), "List<BitVec(8)>", format!("{prefix}_header() ++ {prefix}_code()"));
    fun(module, &format!("{prefix}_image"), &format!("CallElfImage({prefix}_code())"),
        format!("CallElfImage(trivial, elf_byte({}), elf_byte({}), refl, trivial)", size & 255, size >> 8));
    thm(module, &format!("{prefix}_file_correct"), format!("{prefix}_file() = call_elf_bytes({prefix}_code(), {prefix}_image())"), "refl".into());
    let words = Words { prefix: prefix.into(), values: Default::default() };
    let mut trace = Module::default();
    certify_trace(&mut trace, &words, prefix, caller, inputs, &leaf, &leaf_prefix, &layout, local)?;
    for value in words.values.into_inner() {
        fun(module, &format!("{prefix}_word_{value:x}"), "BitVec(64)", word(value));
    }
    module.extend(trace);
    Ok(file)
}

fn certify_trace(module: &mut Module, words: &Words, prefix: &str, caller: &str, inputs: [u64;2], leaf: &SourceX86Emission,
    leaf_prefix: &str, layout: &Layout, local: bool) -> Result<(), String>
{
    let word = |n| words.get(n);
    let state = |i| format!("{prefix}_state_{i}(gprs, flags, stack)");
    state_decl(module, &format!("{prefix}_state_0"), "MachineState<CallMemory>".into(),
        format!("call_initial({prefix}_file(), gprs, flags, stack)"), false);
    let mut pc = ENTRY;
    let mut returns = Vec::new();
    let mut rsp = STACK_TOP;
    let mut trace = Vec::new();
    let mut leaf_start = 0;
    let mut leaf_end = 0;
    loop {
        let (op, encoding, instruction) = layout.placed.get(&pc).ok_or("execution escaped laid-out fragments")?;
        let i = trace.len();
        if matches!(op, Op::Syscall) { break; }
        if pc == layout.symbols["leaf"] { leaf_start = i; }
        let before = state(i);
        let (after_expr, next) = match op {
            Op::Normal(instruction) => (format!("execute_normal(decoded_canonical({}), {before})", instruction.heather_expr().render()), pc + encoding.len() as u64),
            Op::Call(symbol) => {
                let target = layout.symbols[symbol]; let delta = displacement(pc, target)? as u32;
                returns.push(pc + 5);
                (format!("call_after(call_stack_access(), bitvec::ofNat(32, {delta}), {before})"), target)
            }
            Op::Ret => {
                if i == leaf_start + leaf.instructions.len() + usize::from(local) { leaf_end = i; }
                (format!("return_after(call_stack_access(), {before})"), returns.pop().ok_or("return with empty static frame chain")?)
            }
            Op::Store => (format!("stack_store_after(call_stack_access(), R11, {before})"), pc + 4),
            Op::Load => (format!("stack_load_after(call_stack_access(), R11, {before})"), pc + 4),
            Op::Syscall => unreachable!(),
        };
        let after = state(i+1);
        // Name each step, then flatten RIP to the independently laid-out address.
        state_decl(module, &format!("{prefix}_computed_{i}"), "MachineState<CallMemory>".into(), after_expr, false);
        let computed = format!("{prefix}_computed_{i}(gprs, flags, stack)");
        let (memory, memory_proof) = match op {
            Op::Call(symbol) => certify_call_memory(module, words, prefix, i, &before, rsp, pc, displacement(pc, layout.symbols[symbol])? as u32, None),
            Op::Normal(normal) => (format!("{before}.memory"), format!("sym(normal_memory({}, {before}))", normal.heather_expr().render())),
            Op::Ret => (format!("{before}.memory"), format!("sym(return_memory(call_stack_access(), {before}))")),
            Op::Store => certify_call_memory(module, words, prefix, i, &before, rsp, pc, 0, Some(inputs[0] ^ inputs[1])),
            Op::Load => (format!("{before}.memory"), "refl".into()),
            _ => unreachable!(),
        };
        state_decl(module, &format!("{prefix}_memory_same_{i}"), format!("{memory} = {computed}.memory"), memory_proof, true);
        let fields = match op {
            Op::Call(_) => format!("write_gpr(Rsp, {}, {before}.gprs), {before}.flags", word(rsp-8)),
            Op::Ret => format!("write_gpr(Rsp, {}, {before}.gprs), {before}.flags", word(rsp+8)),
            Op::Store => format!("{before}.gprs, {before}.flags"),
            Op::Load => format!("write_gpr(R11, {}, {before}.gprs), {before}.flags", word(inputs[0] ^ inputs[1])),
            _ => format!("{computed}.gprs, {computed}.flags"),
        };
        state_decl(module, &format!("{prefix}_state_{}", i+1), "MachineState<CallMemory>".into(),
            format!("MachineState({fields}, {}, {memory})", word(next)), false);
        // Track RSP one step at a time; consumers use this equality instead of
        // normalizing the preceding register updates inside every address check.
        let next_rsp = match op {
            Op::Call(_) | Op::Normal(Instruction::SubRR { destination: Gpr::Rsp, .. }) => rsp-8,
            Op::Ret | Op::Normal(Instruction::AddRR { destination: Gpr::Rsp, .. }) => rsp+8,
            _ => rsp,
        };
        let read_before = format!("read_gpr(Rsp, {before}.gprs)");
        let mut rhs = read_before.clone();
        let step_proof = match op {
            Op::Call(_) | Op::Ret => {
                rhs = word(next_rsp);
                format!("read_gpr_after_write(Rsp, {}, {before}.gprs)", word(next_rsp))
            }
            Op::Normal(Instruction::MovRI { destination: Gpr::Rsp, immediate }) => { rhs = format!("bitvec::ofNat(64, {immediate})"); "refl".into() }
            Op::Normal(Instruction::SubRR { destination: Gpr::Rsp, .. }) => { rhs = format!("bitvec::sub(64, {read_before}, bitvec::ofNat(64, 8))"); "refl".into() }
            Op::Normal(Instruction::AddRR { destination: Gpr::Rsp, .. }) => { rhs = format!("bitvec::add(64, {read_before}, bitvec::ofNat(64, 8))"); "refl".into() }
            _ => "refl".into(),
        };
        state_decl(module, &format!("{prefix}_rsp_step_{i}"), format!("read_gpr(Rsp, {after}.gprs) = {rhs}"), step_proof, true);
        let rhs_proof = if i == 0 || matches!(op, Op::Call(_) | Op::Ret) { "refl".into() } else if next_rsp == rsp {
            format!("{prefix}_rsp_{i}(gprs, flags, stack)")
        } else {
            let operation = if next_rsp < rsp { "sub" } else { "add" };
            thm(module, &format!("{prefix}_rsp_arithmetic_{i}"), format!("bitvec::{operation}(64, {}, bitvec::ofNat(64, 8)) = {}", word(rsp), word(next_rsp)), "refl".into());
            format!("trans(cong_fn<BitVec(64), BitVec(64)>(λ pointer => bitvec::{operation}(64, pointer, bitvec::ofNat(64, 8)), {prefix}_rsp_{i}(gprs, flags, stack)), {prefix}_rsp_arithmetic_{i}())")
        };
        state_decl(module, &format!("{prefix}_rsp_rhs_{i}"), format!("{rhs} = {}", word(next_rsp)), rhs_proof, true);
        state_decl(module, &format!("{prefix}_rsp_{}", i+1), format!("read_gpr(Rsp, {after}.gprs) = {}", word(next_rsp)),
            format!("trans({prefix}_rsp_step_{i}(gprs, flags, stack), {prefix}_rsp_rhs_{i}(gprs, flags, stack))"), true);
        if matches!(op, Op::Call(_) | Op::Ret | Op::Store | Op::Load) {
            if matches!(op, Op::Call(_) | Op::Store) {
                let slot = rsp - if matches!(op, Op::Store) { 0 } else { 8 };
                let base = word(slot);
                let actual_base = if matches!(op, Op::Store) { format!("read_gpr(Rsp, {before}.gprs)") }
                    else { format!("bitvec::sub(64, read_gpr(Rsp, {before}.gprs), bitvec::ofNat(64, 8))") };
                let mut fields = vec!["canonical := refl".to_string(), format!("end_canonical := j(sym({prefix}_store_offset_{i}_7()), λ address _ => LowCanonical(address), refl)"), "no_wrap := refl".into()];
                for j in 0..8 {
                    thm(module, &format!("{prefix}_write_literal_{i}_{j}"), format!("call_stack_access().writable({}) = True", word(slot+j as u64)), "refl".into());
                    state_decl(module, &format!("{prefix}_write_permission_{i}_{j}"),
                        format!("call_stack_access().writable(bitvec::add(64, {base}, bitvec::ofNat(64, {j}))) = True"),
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
                thm(module, &format!("{prefix}_displacement_{i}"), format!("bitvec::sign_extend(31, 32, bitvec::ofNat(32, {delta})) = {extended}"), "refl".into());
                let add_proof = if (delta as i32) < 0 {
                    let magnitude = word(-(delta as i32 as i64) as u64);
                    certify_sub(module, words, &format!("{prefix}_negative_offset_{i}"), 0, -(delta as i32 as i64) as u64);
                    certify_sub(module, words, &format!("{prefix}_target_sub_{i}"), pc + 5, -(delta as i32 as i64) as u64);
                    format!("trans(cong_fn<BitVec(64), BitVec(64)>(λ offset => bitvec::add(64, {}, offset), sym({prefix}_negative_offset_{i}())), trans(add_negative(64, {}, {magnitude}), {prefix}_target_sub_{i}()))", word(pc+5), word(pc+5))
                } else { "refl".into() };
                thm(module, &format!("{prefix}_target_add_{i}"), format!("bitvec::add(64, {}, {extended}) = {}", word(pc+5), word(next)), add_proof);
                state_decl(module, &format!("{prefix}_target_arithmetic_{i}"),
                    format!("{} = call_target({before}.rip, bitvec::ofNat(32, {delta}))", word(next)),
                    format!("sym(trans(cong_fn<BitVec(64), BitVec(64)>(λ pointer => bitvec::add(64, pointer, bitvec::sign_extend(31, 32, bitvec::ofNat(32, {delta}))), {prefix}_store_value_{i}(gprs, flags, stack)), trans(cong_fn<BitVec(64), BitVec(64)>(λ offset => bitvec::add(64, {}, offset), {prefix}_displacement_{i}()), {prefix}_target_add_{i}())))", word(pc+5)), true);
                format!("trans({prefix}_target_arithmetic_{i}(gprs, flags, stack), sym(call_after_target(call_stack_access(), bitvec::ofNat(32, {delta}), {before})))")
            } else { certify_return_target(module, words, prefix, i, &before, rsp, next, false) };
            state_decl(module, &format!("{prefix}_target_{i}"), format!("{} = {computed}.rip", word(next)), target_proof, true);
            let successor_proof = if let Op::Call(symbol) = op {
                let delta = displacement(pc, layout.symbols[symbol])? as u32;
                format!("call_after_flat(call_stack_access(), bitvec::ofNat(32, {delta}), {before}, {}, {}, {memory}, sym({prefix}_store_base_{i}(gprs, flags, stack)), {prefix}_target_arithmetic_{i}(gprs, flags, stack), sym({prefix}_store_equal_{i}_8(gprs, flags, stack)))", word(next_rsp), word(next))
            } else {
                thm(module, &format!("{prefix}_ret_sp_add_{i}"), format!("bitvec::add(64, {}, bitvec::ofNat(64, 8)) = {}", word(rsp), word(next_rsp)), "refl".into());
                state_decl(module, &format!("{prefix}_ret_sp_same_{i}"), format!("{} = bitvec::add(64, read_gpr(Rsp, {before}.gprs), bitvec::ofNat(64, 8))", word(next_rsp)),
                    format!("sym(trans(cong_fn<BitVec(64), BitVec(64)>(λ pointer => bitvec::add(64, pointer, bitvec::ofNat(64, 8)), {prefix}_rsp_{i}(gprs, flags, stack)), {prefix}_ret_sp_add_{i}()))"), true);
                format!("return_after_flat(call_stack_access(), {before}, {}, {}, {prefix}_ret_sp_same_{i}(gprs, flags, stack), sym({prefix}_return_value_{i}(gprs, flags, stack)))", word(next_rsp), word(next))
            };
            state_decl(module, &format!("{prefix}_successor_{i}"), format!("{after} = {computed}"), successor_proof, true);
        }

        if let Op::Normal(normal) = op {
            let decoded = format!("decoded_canonical({})", normal.heather_expr().render());
            state_decl(module, &format!("{prefix}_target_arithmetic_{i}"),
                format!("{} = next_rip({before}.rip, {decoded}.length)", word(next)), "refl".into(), true);
            state_decl(module, &format!("{prefix}_target_{i}"), format!("{} = {computed}.rip", word(next)),
                format!("trans({prefix}_target_arithmetic_{i}(gprs, flags, stack), sym(execute_normal_advances_rip({decoded}, {before})))"), true);
            state_decl(module, &format!("{prefix}_successor_{i}"), format!("{after} = {computed}"),
                format!("machine_rebuild({computed}, {}, {memory}, {prefix}_target_{i}(gprs, flags, stack), {prefix}_memory_same_{i}(gprs, flags, stack))", word(next)), true);
        }
        if matches!(op, Op::Store | Op::Load) {
            state_decl(module, &format!("{prefix}_target_{i}"), format!("{} = next_rip({before}.rip, 4)", word(next)), "refl".into(), true);
            let proof = if matches!(op, Op::Store) {
                format!("machine_rebuild({computed}, {}, {memory}, {prefix}_target_{i}(gprs, flags, stack), {prefix}_memory_same_{i}(gprs, flags, stack))", word(next))
            } else {
                certify_return_target(module, words, prefix, i, &before, rsp, inputs[0] ^ inputs[1], true);
                format!("stack_load_flat(call_stack_access(), R11, {before}, {}, {}, sym({prefix}_return_value_{i}(gprs, flags, stack)), {prefix}_target_{i}(gprs, flags, stack))", word(inputs[0] ^ inputs[1]), word(next))
            };
            state_decl(module, &format!("{prefix}_successor_{i}"), format!("{after} = {computed}"), proof, true);
        }
        match op {
            Op::Call(symbol) => {
                let delta = displacement(pc, layout.symbols[symbol])? as u32;
                state_decl(module, &format!("{prefix}_stack_bound_{i}"), format!("bitvec::borrow_sub_bit(64, read_gpr(Rsp, {before}.gprs), bitvec::ofNat(64, 8)) = False"),
                    format!("trans(cong_fn<BitVec(64), Bool>(λ pointer => bitvec::borrow_sub_bit(64, pointer, bitvec::ofNat(64, 8)), {prefix}_rsp_{i}(gprs, flags, stack)), refl)"), true);
                state_decl(module, &format!("{prefix}_return_canonical_{i}"), format!("LowCanonical(call_return_address({before}))"),
                    format!("j(sym({prefix}_store_value_{i}(gprs, flags, stack)), λ address _ => LowCanonical(address), refl)"), true);
                state_decl(module, &format!("{prefix}_target_canonical_{i}"), format!("LowCanonical(call_target({before}.rip, bitvec::ofNat(32, {delta})))"),
                    format!("j({prefix}_target_arithmetic_{i}(gprs, flags, stack), λ address _ => LowCanonical(address), refl)"), true);
            }
            Op::Ret => {
                state_decl(module, &format!("{prefix}_stack_bound_{i}"), format!("bitvec::carry_add_bit(64, read_gpr(Rsp, {before}.gprs), bitvec::ofNat(64, 8)) = False"),
                    format!("trans(cong_fn<BitVec(64), Bool>(λ pointer => bitvec::carry_add_bit(64, pointer, bitvec::ofNat(64, 8)), {prefix}_rsp_{i}(gprs, flags, stack)), refl)"), true);
                state_decl(module, &format!("{prefix}_target_canonical_{i}"), format!("LowCanonical(stack_word(call_stack_access(), {before}.memory, read_gpr(Rsp, {before}.gprs)))"),
                    format!("j(sym({prefix}_return_value_{i}(gprs, flags, stack)), λ address _ => LowCanonical(address), refl)"), true);
            }
            _ => {},
        }
        let step = match op {
            Op::Normal(normal) => format!("ordinary_call_step(call_stack_access(), {}, {before}, {after}, {prefix}_successor_{i}(gprs, flags, stack))", normal.heather_expr().render()),
            Op::Call(_) => format!("⟨{prefix}_stack_bound_{i}(gprs, flags, stack), ⟨{prefix}_return_canonical_{i}(gprs, flags, stack), ⟨{prefix}_target_canonical_{i}(gprs, flags, stack), ⟨{prefix}_stack_permissions_{i}(gprs, flags, stack), {prefix}_successor_{i}(gprs, flags, stack)⟩⟩⟩⟩"),
            Op::Store | Op::Load => format!("⟨{prefix}_stack_permissions_{i}(gprs, flags, stack), {prefix}_successor_{i}(gprs, flags, stack)⟩"),
            Op::Ret => format!("⟨{prefix}_stack_bound_{i}(gprs, flags, stack), ⟨{prefix}_target_canonical_{i}(gprs, flags, stack), ⟨{prefix}_stack_permissions_{i}(gprs, flags, stack), {prefix}_successor_{i}(gprs, flags, stack)⟩⟩⟩"),
            _ => unreachable!(),
        };
        let fetched = certify_fetch(module, words, prefix, i, &format!("{before}.memory"), pc, encoding);
        let fetched = format!("fetched_span_at_state(call_fetch_access(), {before}.memory, {}, {}, call_instruction_bytes({instruction}), {before}, refl, refl, refl, {fetched})", word(pc), bytes(encoding).render());
        state_decl(module, &format!("{prefix}_step_{i}"),
            format!("FetchedCallStep(call_fetch_access(), call_stack_access(), {instruction}, {before}, {after})"),
            format!("⟨{fetched}, {step}⟩"), true);
        if matches!(op, Op::Call(_)) {
            state_decl(module, &format!("{prefix}_aligned_call_{i}"),
                format!("bitvec::take_low(4, 60, read_gpr(Rsp, {before}.gprs)) = bitvec::zero(4)"),
                format!("trans(cong_fn<BitVec(64), BitVec(4)>(λ pointer => bitvec::take_low(4, 60, pointer), {prefix}_rsp_{i}(gprs, flags, stack)), refl)"), true);
        }
        match op {
            Op::Call(_) => rsp -= 8,
            Op::Ret => rsp += 8,
            Op::Normal(Instruction::SubRR { destination: Gpr::Rsp, .. }) => rsp -= 8,
            Op::Normal(Instruction::AddRR { destination: Gpr::Rsp, .. }) => rsp += 8,
            _ => {},
        }
        if matches!(op, Op::Ret) && i == leaf_end {
            certify_callee_contract(module, words, prefix, inputs, leaf, leaf_prefix, leaf_start, leaf_end, local);
        }
        trace.push(instruction.clone()); pc = next;
        if trace.len() > 128 { return Err("call trace exceeds the initial bounded profile".into()); }
    }
    let n = trace.len(); let end = state(n);
    fun(module, &format!("{prefix}_trace_{n}"), "List<CallInstruction>", "[]".into());
    state_decl(module, &format!("{prefix}_execution_{n}"),
        format!("FetchedCallTrace(call_fetch_access(), call_stack_access(), {prefix}_trace_{n}(), {end}, {end})"), "refl".into(), true);
    for i in (0..n).rev() {
        fun(module, &format!("{prefix}_trace_{i}"), "List<CallInstruction>", format!("Cons({}, {prefix}_trace_{}())", trace[i], i+1));
        state_decl(module, &format!("{prefix}_execution_{i}"),
            format!("FetchedCallTrace(call_fetch_access(), call_stack_access(), {prefix}_trace_{i}(), {}, {end})", state(i)),
            format!("call_trace_cons(call_fetch_access(), call_stack_access(), {}, {prefix}_trace_{}(), {}, {}, {end}, {prefix}_step_{i}(gprs, flags, stack), {prefix}_execution_{}(gprs, flags, stack))", trace[i], i+1, state(i), state(i+1), i+1), true);
    }
    state_decl(module, &format!("{prefix}_loaded_execution"),
        format!("CallImageExecution({prefix}_file(), {prefix}_code(), {prefix}_trace_0(), {}, {end})", state(0)),
        format!("CallImageExecution(image := {prefix}_image(), file_correct := {prefix}_file_correct(), initial_memory := refl, execution := {prefix}_execution_0(gprs, flags, stack))"), true);
    let caller_result = format!("{caller}({}, {})", word(inputs[0]), word(inputs[1]));
    let status = if local {
        thm(module, &format!("{prefix}_saved_value"), format!("bitvec::bxor(64, {}, {}) = {}", word(inputs[0]), word(inputs[1]), word(inputs[0] ^ inputs[1])), "refl".into());
        format!("trans(cong_fn<BitVec(64), BitVec(64)>(λ value => bitvec::bxor(64, value, {}), {prefix}_callee_contract(gprs, flags, stack).result_correct), trans(cong_fn<BitVec(64), BitVec(64)>(λ saved => bitvec::bxor(64, {}({}, {}), saved), sym({prefix}_saved_value())), sym({prefix}_source_call({}, {}))))", word(inputs[0] ^ inputs[1]), leaf.reflected.source_name, word(inputs[0]), word(inputs[1]), word(inputs[0]), word(inputs[1]))
    } else { format!("trans({prefix}_callee_contract(gprs, flags, stack).result_correct, sym({prefix}_source_call({}, {})))", word(inputs[0]), word(inputs[1])) };
    state_decl(module, &format!("{prefix}_exit_request"), format!("LinuxExitRequest<CallMemory>({end}, {caller_result})"),
        format!("LinuxExitRequest(number := refl, status := {status})"), true);
    let syscall_fetch = certify_fetch(module, words, prefix, n, &format!("{end}.memory"), pc, &[0x0f, 0x05]);
    state_decl(module, &format!("{prefix}_syscall_fetched"),
        format!("FetchedFrom(call_fetch_access(), {end}.memory, InstructionBytes({end}.rip, linux_syscall_bytes()))"), syscall_fetch, true);
    state_decl(module, &format!("{prefix}_stack_restored"), format!("read_gpr(Rsp, {end}.gprs) = {}", word(STACK_TOP)), format!("{prefix}_rsp_{n}(gprs, flags, stack)"), true);
    Ok(())
}

fn certify_callee_contract(module: &mut Module, words: &Words, prefix: &str, inputs: [u64; 2], leaf: &SourceX86Emission,
    leaf_prefix: &str, leaf_start: usize, leaf_end: usize, local: bool) {
    let word = |n| words.get(n);
    let state = |i| format!("{prefix}_state_{i}(gprs, flags, stack)");
    let begin = state(leaf_start); let after_leaf = state(leaf_end);
    // Export the leaf's result through a contract. The caller's result proof
    // below consumes this field rather than reducing the leaf's source body.
    let result_agrees = if local {
        let core = state(leaf_end - 1);
        state_decl(module, &format!("{prefix}_leaf_core_result_agrees"),
            format!("read_gpr(Rax, {core}.gprs) = read_gpr(Rax, {leaf_prefix}_after({begin}).gprs)"), "refl".into(), true);
        format!("trans(xor_r11_preserves_rax({core}), {prefix}_leaf_core_result_agrees(gprs, flags, stack))")
    } else { "refl".into() };
    state_decl(module, &format!("{prefix}_leaf_result_agrees"),
        format!("read_gpr(Rax, {after_leaf}.gprs) = read_gpr(Rax, {leaf_prefix}_after({begin}).gprs)"), result_agrees, true);
    let result = format!("{}({}, {})", leaf.reflected.source_name, word(inputs[0]), word(inputs[1]));
    state_decl(module, &format!("{prefix}_callee_result"), format!("read_gpr(Rax, {after_leaf}.gprs) = {result}"),
        format!("trans({prefix}_leaf_result_agrees(gprs, flags, stack), trans({leaf_prefix}_refines_function_ir({leaf_prefix}_values(), {begin}, refl, refl, {leaf_prefix}_entry_graph()), {leaf_prefix}_denotes_source({leaf_prefix}_values(), {leaf_prefix}_entry_graph())))"), true);
    let returned = state(leaf_end+1);
    state_decl(module, &format!("{prefix}_callee_contract"),
        format!("NativeIntegerCallContract<CallMemory, Option<BitVec(8)>>(call_memory_read, NoWrites, {begin}, {returned}, {result}, stack_word(call_stack_access(), {begin}.memory, read_gpr(Rsp, {begin}.gprs)))"),
        format!("NativeIntegerCallContract(result_correct := {prefix}_callee_result(gprs, flags, stack), returned_to := {prefix}_target_{leaf_end}(gprs, flags, stack), stack_restored := refl, memory_effects := writes_only_equal(call_memory_read, NoWrites, {begin}.memory, {returned}.memory, refl), preserved_rbx := refl, preserved_rbp := refl, preserved_r12 := refl, preserved_r13 := refl, preserved_r14 := refl, preserved_r15 := refl)"), true);
    state_decl(module, &format!("{prefix}_callee_memory_effects"),
        format!("WritesOnly(call_memory_read, NoWrites, {begin}.memory, {returned}.memory)"),
        format!("{prefix}_callee_contract(gprs, flags, stack).memory_effects"), true);
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
        let _guard = super::super::CERTIFICATE_TEST_LOCK.lock().unwrap();
        use heather_cli::{loader, semantic::SemanticSession};
        use std::path::PathBuf;
        let mut elab = Elaborator::with_prelude().unwrap();
        let mut session = SemanticSession::new(Some(PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/../../target/native-test-images"))));
        for &(name, src) in super::super::SUPPORT {
            super::super::check_module(&mut elab, &mut session, &loader::Module {
                name: name.into(), path: PathBuf::from(name), src: src.into(),
            }).unwrap();
        }
        let forwarding = "import bitvec; fn leaf(left: BitVec(64), right: BitVec(64)) -> BitVec(64) { bitvec::add(64, left, right) } fn forward(left: BitVec(64), right: BitVec(64)) -> BitVec(64) { leaf(left, right) } fn swapped(left: BitVec(64), right: BitVec(64)) -> BitVec(64) { leaf(right, left) } fn expression(left: BitVec(64), right: BitVec(64)) -> BitVec(64) { bitvec::add(64, leaf(left, right), right) }";
        elab.elab_module_source("forwarding", forwarding).unwrap_or_else(|e| panic!("{}", e.render(forwarding)));
        assert_eq!(function_ir_source::reflect_forwarded_call(&elab, "forwarding::forward").unwrap(), "forwarding::leaf");
        for name in ["forwarding::swapped", "forwarding::expression", "forwarding::missing"] {
            assert!(function_ir_source::reflect_forwarded_call(&elab, name).is_err(), "accepted unsupported wrapper {name}");
        }
        let local_source = "import bitvec; import forwarding; fn local(left: BitVec(64), right: BitVec(64)) -> BitVec(64) { bitvec::bxor(64, forwarding::leaf(left, right), bitvec::bxor(64, left, right)) }";
        elab.elab_module_source("local_wrapper", local_source).unwrap_or_else(|e| panic!("{}", e.render(local_source)));
        assert_eq!(function_ir_source::reflect_call_wrapper(&elab, "local_wrapper::local").unwrap(), ("forwarding::leaf".into(), true));
        let imports = "import x86_64; import x86_64_call_frame; import x86_64_calls; import elf64_calls; import bitvec; import bool; import list; import logic; import option;";
        let source = format!("{imports}\nfn start(rsp: BitVec(64)) -> MachineState<CallMemory> {{ MachineState(write_gpr(Rsp, rsp, zero_gprs()), clear_flags(), {}, CallMemory([], λ address => bitvec::ofNat(8, 0))) }}", word(0x400100));
        elab.elab_module_source("call_test", &source).unwrap_or_else(|e| panic!("{}", e.render(&source)));
        // Test the exact access/underflow premises required by CallStep independently.
        for (name, claim, valid) in [
            ("writable_return_slot", format!("call_stack_access().writable({}) = True", word(0x401ff8)), true),
            ("exhausted_stack", format!("call_stack_access().writable({}) = True", word(0x400ff8)), false),
            ("stack_underflow", format!("bitvec::borrow_sub_bit(64, {}, bitvec::ofNat(64, 8)) = False", word(0)), false),
            ("empty_return", format!("call_stack_access().readable({}) = True", word(0x402000)), false),
            ("noncanonical_stack", format!("LowCanonical({})", word(1u64 << 47)), false),
        ] {
            let source = format!("{imports} import call_test; theorem check(): {claim} {{ refl }}");
            let checked = elab.clone().elab_module_source(name, &source);
            if valid { checked.unwrap_or_else(|e| panic!("{}", e.render(&source))); }
            else { let error = checked.expect_err("invalid stack premise accepted"); assert!(format!("{error:?}").contains("NotConvertible"), "{}", error.render(&source)); }
        }
        for (name, opcode, delta, valid) in [("call_encoding", 0xe8, 0x20, true), ("wrong_call_opcode", 0xe9, 0x20, false), ("wrong_call_displacement", 0xe8, 0x21, false)] {
            let source = format!("{imports} fn actual() -> List<BitVec(8)> {{ [bitvec::ofNat(8, {opcode}), bitvec::ofNat(8, {delta}), bitvec::ofNat(8, 0), bitvec::ofNat(8, 0), bitvec::ofNat(8, 0)] }} theorem encoding(): actual() = call_instruction_bytes(CallRelative(bitvec::ofNat(32, 0x20))) {{ refl }}");
            let checked = elab.clone().elab_module_source(name, &source);
            if valid { checked.unwrap_or_else(|e| panic!("{}", e.render(&source))); }
            else { let error = checked.expect_err("corrupted CALL encoding accepted"); assert!(format!("{error:?}").contains("NotConvertible"), "{}", error.render(&source)); }
        }
        for (name, opcode, sib, valid) in [("stack_store_encoding", 0x89, 0x24, true), ("wrong_stack_opcode", 0x8b, 0x24, false), ("wrong_stack_address", 0x89, 0x25, false)] {
            let source = format!("{imports} fn actual() -> List<BitVec(8)> {{ [bitvec::ofNat(8, 0x4c), bitvec::ofNat(8, {opcode}), bitvec::ofNat(8, 0x1c), bitvec::ofNat(8, {sib})] }} theorem encoding(): actual() = call_instruction_bytes(StoreStack64(R11)) {{ refl }}");
            let checked = elab.clone().elab_module_source(name, &source);
            if valid { checked.unwrap_or_else(|e| panic!("{}", e.render(&source))); }
            else { let error = checked.expect_err("invalid stack encoding accepted"); assert!(format!("{error:?}").contains("NotConvertible"), "{}", error.render(&source)); }
        }
        let local = word(0x401fe0); let shared = word(0x401fd0); let live = word(0x401ff0);
        let source = format!("{imports} fn base(stack: BitVec(64) -> BitVec(8)) -> CallMemory {{ CallMemory([], stack) }} fn changed(stack: BitVec(64) -> BitVec(8), byte: BitVec(8)) -> CallMemory {{ call_memory_write(base(stack), {local}, byte) }} theorem effects(stack: BitVec(64) -> BitVec(8), byte: BitVec(8)): WritesOnly(call_memory_read, ByteWrite({local}), base(stack), changed(stack, byte)) {{ memory_write_effect(base(stack), {local}, byte) }} theorem outside(): DisjointWrites(ByteWrite({local}), λ address => address = {live}) {{ point_disjoint(ByteWrite({local}), {live}, λ bad => absurd(bad)) }} theorem live_byte(stack: BitVec(64) -> BitVec(8), byte: BitVec(8)): call_memory_read(changed(stack, byte), {live}) = call_memory_read(base(stack), {live}) {{ protected_read(call_memory_read, ByteWrite({local}), λ address => address = {live}, base(stack), changed(stack, byte), outside(), effects(stack, byte), {live}, refl) }} theorem shared_effect(stack: BitVec(64) -> BitVec(8), first, second: BitVec(8)): WritesOnly(call_memory_read, UnionWrites(ByteWrite({local}), ByteWrite({shared})), base(stack), call_memory_write(changed(stack, first), {shared}, second)) {{ writes_only_compose(call_memory_read, ByteWrite({local}), ByteWrite({shared}), base(stack), changed(stack, first), call_memory_write(changed(stack, first), {shared}, second), effects(stack, first), memory_write_effect(changed(stack, first), {shared}, second)) }}");
        let source = format!("{source} fn policy() -> CallMemoryPolicy {{ CallMemoryPolicy(ByteWrite({local}), ByteWrite({shared}), λ address => address = {live}, point_disjoint(ByteWrite({local}), {live}, λ bad => absurd(bad)), point_disjoint(ByteWrite({shared}), {live}, λ bad => absurd(bad))) }} theorem child_in_parent(stack: BitVec(64) -> BitVec(8), byte: BitVec(8)): WritesOnly(call_memory_read, permitted_writes(policy()), base(stack), changed(stack, byte)) {{ writes_only_weaken(call_memory_read, ByteWrite({local}), permitted_writes(policy()), base(stack), changed(stack, byte), λ address witness => Inl(witness), effects(stack, byte)) }} theorem policy_live(stack: BitVec(64) -> BitVec(8), byte: BitVec(8)): call_memory_read(changed(stack, byte), {live}) = call_memory_read(base(stack), {live}) {{ protected_read(call_memory_read, permitted_writes(policy()), policy().protected, base(stack), changed(stack, byte), policy_disjoint(policy()), child_in_parent(stack, byte), {live}, refl) }}");
        elab.elab_module_source("frame_checks", &source).unwrap_or_else(|e| panic!("{}", e.render(&source)));
        for (name, address, valid) in [("dead_local_may_change", local.clone(), true), ("live_slot_cannot_change", live.clone(), false), ("return_slot_cannot_change", word(0x401ff8), false)] {
            let source = format!("{imports} import frame_checks; theorem check(): call_memory_read(changed(λ address => bitvec::ofNat(8, 0), bitvec::ofNat(8, 7)), {address}) = Some(bitvec::ofNat(8, 7)) {{ refl }}");
            let checked = elab.clone().elab_module_source(name, &source);
            if valid { checked.unwrap_or_else(|e| panic!("{}", e.render(&source))); }
            else { let error = checked.expect_err("protected byte changed"); assert!(format!("{error:?}").contains("NotConvertible"), "{}", error.render(&source)); }
        }
        let source = format!("{imports} import frame_checks; fn overlapping() -> CallMemoryPolicy {{ CallMemoryPolicy(ByteWrite({local}), NoWrites, λ address => address = {local}, outside(), λ address impossible live => impossible) }}");
        let error = elab.clone().elab_module_source("overlapping_policy", &source).expect_err("overlapping frame accepted");
        assert!(format!("{error:?}").contains("NotConvertible"), "{}", error.render(&source));
        for (name, restored, valid) in [("contract_restores_rsp", 0x401ff8, true), ("missing_frame_release", 0x401ff0, false)] {
            let before = format!("start({})", word(0x401ff0)); let after = format!("start({})", word(restored));
            let source = format!("{imports} import call_test; theorem contract(): NativeIntegerCallContract<CallMemory, Option<BitVec(8)>>(call_memory_read, NoWrites, {before}, {after}, bitvec::zero(64), {before}.rip) {{ NativeIntegerCallContract(result_correct := refl, returned_to := refl, stack_restored := refl, memory_effects := writes_only_equal(call_memory_read, NoWrites, {before}.memory, {after}.memory, refl), preserved_rbx := refl, preserved_rbp := refl, preserved_r12 := refl, preserved_r13 := refl, preserved_r14 := refl, preserved_r15 := refl) }}");
            let checked = elab.clone().elab_module_source(name, &source);
            if valid { checked.unwrap_or_else(|e| panic!("{}", e.render(&source))); }
            else { let error = checked.expect_err("unrestored frame accepted"); assert!(format!("{error:?}").contains("NotConvertible"), "{}", error.render(&source)); }
        }
        // The extra ELF segment must remain RW, never executable.
        for (name, flags, valid) in [("stack_segment_flags", 6, true), ("executable_stack_segment", 7, false)] {
            let source = format!("{imports} fn expected() -> List<BitVec(8)> {{ [bitvec::ofNat(8, {flags}), bitvec::ofNat(8, 0), bitvec::ofNat(8, 0), bitvec::ofNat(8, 0)] }} theorem flags(): list::take(list::drop(call_elf_header(bitvec::ofNat(8, 233), bitvec::ofNat(8, 0)), 180), 4) = expected() {{ refl }}");
            let checked = elab.clone().elab_module_source(name, &source);
            if valid { checked.unwrap_or_else(|e| panic!("{}", e.render(&source))); }
            else { let error = checked.expect_err("executable stack header accepted"); assert!(format!("{error:?}").contains("NotConvertible"), "{}", error.render(&source)); }
        }
        let source = format!("{imports} import call_test; theorem stored(byte: BitVec(8)): call_memory_write(start({}).memory, {}, byte).stack({}) = byte {{ refl }} theorem disjoint(byte: BitVec(8)): call_memory_write(start({}).memory, {}, byte).stack({}) = bitvec::ofNat(8, 0) {{ refl }}", word(0x402000), word(0x401ff8), word(0x401ff8), word(0x402000), word(0x401ff8), word(0x401ff9));
        elab.elab_module_source("stack_store", &source).unwrap_or_else(|e| panic!("{}", e.render(&source)));
        let source = format!("{imports} import call_test; fn actual() -> CallMemory {{ word_write_1(call_stack_access(), {}, start({}).memory, {}) }} fn proposed() -> CallMemory {{ call_memory_write(start({}).memory, {}, bitvec::ofNat(8, 5)) }} theorem pointer(): bitvec::add(64, {}, bitvec::ofNat(64, 0)) = {} {{ refl }} theorem first_write(): actual() = proposed() {{ call_memory_write_cong(start({}).memory, start({}).memory, bitvec::add(64, {}, bitvec::ofNat(64, 0)), {}, imm_byte0({}), bitvec::ofNat(8, 5), refl, pointer(), refl) }}", word(0x400105), word(0x402000), word(0x401ff8), word(0x402000), word(0x401ff8), word(0x401ff8), word(0x401ff8), word(0x402000), word(0x402000), word(0x401ff8), word(0x401ff8), word(0x400105));
        elab.elab_module_source("first_write", &source).unwrap_or_else(|e| panic!("{}", e.render(&source)));
        for (name, expected, valid) in [("return_byte", 5, true), ("corrupted_return_byte", 6, false)] {
            let source = format!("{imports} import first_write; theorem check(): actual().stack({}) = bitvec::ofNat(8, {expected}) {{ trans(cong_fn<CallMemory, BitVec(8)>(λ memory => memory.stack({}), first_write()), refl) }}", word(0x401ff8), word(0x401ff8));
            let checked = elab.clone().elab_module_source(name, &source);
            if valid { checked.unwrap_or_else(|e| panic!("{}", e.render(&source))); }
            else { let error = checked.expect_err("corrupted return byte accepted"); assert!(format!("{error:?}").contains("NotConvertible"), "{}", error.render(&source)); }
        }
    }
}
