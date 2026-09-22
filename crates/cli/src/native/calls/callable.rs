//! A reusable composed-function contract over neutral registers and memory.
use super::*;
use heather_elab::function_ir_cert::Node;

const ABI: [Gpr; 6] = [Gpr::Rbx, Gpr::Rbp, Gpr::R12, Gpr::R13, Gpr::R14, Gpr::R15];
const PARAMS: &str = "gprs, flags, memory, rip";
fn decl(module: &mut Module, name: &str, ty: String, body: String, theorem: bool) {
    let d = if theorem { Declaration::theorem(name, Expr::raw(ty), Block::expression(Expr::raw(body))) }
        else { Declaration::function(name, Expr::raw(ty), Block::expression(Expr::raw(body))) };
    module.declaration(d.parameter(Parameter::explicit("gprs", Expr::name("Gprs")))
        .parameter(Parameter::explicit("flags", Expr::name("Flags")))
        .parameter(Parameter::explicit("memory", Expr::name("CallMemory")))
        .parameter(Parameter::explicit("rip", Expr::raw("BitVec(64)"))));
}
fn binary_name(i: Instruction) -> Option<&'static str> {
    match i { Instruction::AddRR { .. } => Some("add"), Instruction::SubRR { .. } => Some("sub"),
        Instruction::AndRR { .. } => Some("band"), Instruction::OrRR { .. } => Some("bor"),
        Instruction::XorRR { .. } => Some("bxor"), _ => None }
}
fn binary_source(i: Instruction) -> Option<Gpr> {
    match i { Instruction::AddRR { source, .. } | Instruction::SubRR { source, .. }
        | Instruction::AndRR { source, .. } | Instruction::OrRR { source, .. }
        | Instruction::XorRR { source, .. } => Some(source), _ => None }
}

// The valuation is polymorphic in width; the roundtrip lemmas supply the
// width-64 input equalities without assuming arbitrary words are literals.
fn leaf_contract(module: &mut Module, name: &str, leaf_prefix: &str, leaf: &SourceX86Emission) -> Result<(), String> {
    let value = |id| format!("{name}_value_{id}(left, right, width)");
    let mut definitions = vec![(0, "@bitvec::BitVec::ofNat(width, @bitvec::BitVec::toNat(64, left))".into()), (1, "@bitvec::BitVec::ofNat(width, @bitvec::BitVec::toNat(64, right))".into())];
    for node in &leaf.reflected.region.nodes {
        let body = match *node {
            Node::Const { value: n, .. } => format!("@bitvec::BitVec::ofNat(width, {n})"),
            Node::Add { left, right, .. } | Node::Sub { left, right, .. }
            | Node::BitAnd { left, right, .. } | Node::BitOr { left, right, .. } | Node::BitXor { left, right, .. } => {
                let op = match node { Node::Add { .. } => "add", Node::Sub { .. } => "sub", Node::BitAnd { .. } => "band", Node::BitOr { .. } => "bor", _ => "bxor" };
                format!("@bitvec::BitVec::{op}(width, {}, {})", value(left), value(right))
            }
            _ => return Err("callable leaf contains unsupported node".into()),
        };
        definitions.push((node.output().id, body));
    }
    let pair_decl = |module: &mut Module, name: &str, ty: String, body: String, width: bool, theorem: bool| {
        let d = if theorem { Declaration::theorem(name, Expr::raw(ty), Block::expression(Expr::raw(body))) }
            else { Declaration::function(name, Expr::raw(ty), Block::expression(Expr::raw(body))) };
        let d = d.parameter(Parameter::explicit("left", Expr::raw("BitVec(64)"))).parameter(Parameter::explicit("right", Expr::raw("BitVec(64)")));
        module.declaration(if width { d.parameter(Parameter::explicit("width", Expr::name("Nat"))) } else { d });
    };
    let mut cases = "@bitvec::BitVec::zero(width)".to_string();
    for (id, _) in definitions.iter().rev() {
        let scrutinee = if *id == 0 { "id".into() } else { format!("id_{id}") };
        cases = format!("match {scrutinee} {{ Zero => {}, Succ(id_{}) => {cases} }}", value(*id), id+1);
    }
    for (id, body) in &definitions { pair_decl(module, &format!("{name}_value_{id}"), "BitVec(width)".into(), body.clone(), true, false); }
    pair_decl(module, &format!("{name}_values"), "Valuation()".into(), format!("λ width id => {cases}"), false, false);
    let mut graph = "trivial".to_string();
    for _ in &leaf.reflected.region.nodes { graph = format!("⟨refl, {graph}⟩"); }
    pair_decl(module, &format!("{name}_graph"), format!("RegionHolds({leaf_prefix}_raw(), {name}_values(left, right))"), graph, false, true);
    let a = "read_gpr(Rdi, before.gprs)"; let b = "read_gpr(Rsi, before.gprs)";
    let values = format!("{name}_values({a}, {b})");
    let after = format!("call_run(call_stack_access(), {leaf_prefix}_summary_code(), before)");
    let result = format!("{}({a}, {b})", leaf.reflected.source_name);
    let contract_type = |r: &str| format!("NativeIntegerCallContract<CallMemory, BitVec(8)>(stack_observation, NoWrites, before, {after}, {r}, stack_word(call_stack_access(), before.memory, read_gpr(Rsp, before.gprs)))");
    let leaf_source = &leaf.reflected.source_name;
    let same = format!("trans<BitVec(64)>(cong_fn<BitVec(64), BitVec(64)>(λ left => {leaf_source}(left, {values}(64, 1)), bitvec::BitVec::ofNat_toNat(64, {a})), cong_fn<BitVec(64), BitVec(64)>(λ right => {leaf_source}({a}, right), bitvec::BitVec::ofNat_toNat(64, {b})))");
    let post = format!("{leaf_prefix}_summary({values}).ensures(before, ⟨bitvec::BitVec::ofNat_toNat(64, {a}), ⟨bitvec::BitVec::ofNat_toNat(64, {b}), {name}_graph({a}, {b})⟩⟩).left");
    module.declaration(Declaration::function(format!("{name}_contract"), Expr::raw(contract_type(&result)),
        Block::expression(Expr::raw(format!("j({same}, λ result _ => {}, {post})", contract_type("result")))))
        .parameter(Parameter::explicit("before", Expr::raw("MachineState<CallMemory>"))));
    for r in composition::SCRATCH {
        if composition::leaf_clobbers(leaf).contains(&r) { continue; }
        let register = r.heather_name();
        module.declaration(Declaration::theorem(format!("{name}_preserves_{register}"),
            Expr::raw(format!("read_gpr({register}, {after}.gprs) = read_gpr({register}, before.gprs)")), Block::expression(Expr::raw("refl")))
            .parameter(Parameter::explicit("before", Expr::raw("MachineState<CallMemory>"))));
    }
    Ok(())
}

pub(super) fn instructions(layout: &Layout) -> Result<(Vec<Op>, Vec<String>, Vec<(usize, usize)>), String> {
    let mut pc = layout.symbols["caller"]; let mut returns = Vec::new();
    let mut ops = Vec::new(); let mut code = Vec::new(); let mut leaves = Vec::new(); let mut start = 0;
    loop {
        let (op, bytes, instruction) = layout.placed.get(&pc).ok_or("callable trace escaped code")?;
        if pc == layout.symbols["leaf"] { start = ops.len(); }
        ops.push(op.clone()); code.push(instruction.clone());
        match op {
            Op::Call(symbol) => { returns.push(pc+5); pc = layout.symbols[symbol]; }
            Op::Ret => if let Some(next) = returns.pop() { leaves.push((start, ops.len()-1)); pc = next; } else { break; },
            Op::Normal(_) | Op::Save(_) | Op::Restore(_) => pc += bytes.len() as u64,
            _ => return Err("unsupported callable instruction".into()),
        }
        if ops.len() > 128 { return Err("callable trace exceeds 128 instructions".into()); }
    }
    Ok((ops, code, leaves))
}

struct Frame { slots: Vec<u64>, children: Vec<u64>, writes: Vec<u64> }
impl Frame {
    fn collect(ops: &[Op]) -> Self {
        let mut rsp = STACK_TOP-8;
        let mut slots = std::collections::BTreeSet::new();
        let mut children = std::collections::BTreeSet::new();
        for op in ops {
            match op {
                Op::Save(_) => { slots.insert(rsp); }
                Op::Call(_) => { rsp -= 8; children.insert(rsp); }
                Op::Ret => rsp += 8,
                Op::Normal(Instruction::SubRR { destination: Gpr::Rsp, .. }) => rsp -= 8,
                Op::Normal(Instruction::AddRR { destination: Gpr::Rsp, .. }) => rsp += 8,
                _ => {}
            }
        }
        let slots: Vec<_> = slots.into_iter().collect();
        let children: Vec<_> = children.into_iter().collect();
        let writes = children.iter().chain(&slots).copied().collect();
        Self { slots, children, writes }
    }
    fn footprint(&self, words: &Words) -> String {
        format!("λ address => {}", self.writes.iter().map(|slot|
            format!("WordPrefixWrites(8, {}, address)", words.get(*slot))).collect::<Vec<_>>().join(" ∨ "))
    }
    fn inject(&self, slot: u64) -> String {
        let index = self.writes.iter().position(|s| *s == slot).unwrap();
        let mut hit = if index+1 == self.writes.len() { "hit".into() } else { "Inl(hit)".into() };
        for _ in 0..index { hit = format!("Inr({hit})"); }
        hit
    }
}
fn outside_name(name: &str, written: u64, protected: u64) -> String {
    format!("{name}_outside_{written:x}_{protected:x}")
}

// Fixed addresses, arbitrary incoming memory and saved word. Each read checks
// the canonical byte-store model; reconstruction uses the word roundtrip lemma.
fn save_support(module: &mut Module, words: &Words, name: &str, address: u64) {
    let slot = words.get(address);
    let written = format!("word_write_8(call_stack_access(), value, memory, {slot})");
    let pair = |module: &mut Module, name: String, ty: String, body: String| {
        module.declaration(Declaration::theorem(name, Expr::raw(ty), Block::expression(Expr::raw(body)))
            .parameter(Parameter::explicit("memory", Expr::name("CallMemory")))
            .parameter(Parameter::explicit("value", Expr::raw("BitVec(64)"))));
    };
    let mut fields = Vec::new();
    for j in 0..8 {
        let pointer = if j == 0 { slot.clone() } else { format!("@bitvec::BitVec::add(64, {slot}, @bitvec::BitVec::ofNat(64, {j}))") };
        pair(module, format!("{name}_saved_byte_{address:x}_{j}"), format!("call_stack_access().read({written}, {pointer}) = imm_byte{j}(value)"), "refl".into());
        fields.push(format!("byte{j} := {name}_saved_byte_{address:x}_{j}(memory, value)"));
    }
    pair(module, format!("{name}_saved_roundtrip_{address:x}"), format!("stack_word(call_stack_access(), {written}, {slot}) = value"),
        format!("stack_word_matches(call_stack_access(), {written}, {slot}, value, StackWordReads({}))", fields.join(", ")));
}

fn carry_saved(module: &mut Module, words: &Words, name: &str, index: usize, before: &str, after: &str,
    saved: &mut BTreeMap<u64, (String, String)>, effect: &str, written: Option<u64>)
{
    for (address, (value, fact)) in saved {
        let slot = words.get(*address);
        let reads: Vec<_> = (0..8).map(|j| {
            let pointer = if j == 0 { slot.to_string() } else { format!("@bitvec::BitVec::add(64, {slot}, @bitvec::BitVec::ofNat(64, {j}))") };
            let excluded = written.map_or_else(|| "λ impossible => impossible".into(), |w| format!("{}().byte{j}", outside_name(name, w, *address)));
            format!("{effect}({pointer}, {excluded})")
        }).collect();
        let proof = format!("trans(stack_word_agrees(call_stack_access(), {before}.memory, {after}.memory, {slot}, {}), {fact})", reads.join(", "));
        let theorem = format!("{name}_saved_{index}_{address:x}");
        decl(module, &theorem, format!("stack_word(call_stack_access(), {after}.memory, {slot}) = {value}"), proof, true);
        *fact = format!("{theorem}({PARAMS})");
    }
}

pub(super) fn emit(module: &mut Module, words: &Words, prefix: &str, caller: &str, leaf: &SourceX86Emission, leaf_prefix: &str, layout: &Layout) -> Result<(), String> {
    let name = format!("{prefix}_composed");
    leaf_contract(module, &format!("{name}_leaf"), leaf_prefix, leaf)?;
    let (ops, code, leaves) = instructions(layout)?;
    let n = ops.len();
    let state = |i| format!("{name}_state_{i}({PARAMS})");
    let word = |v| words.get(v);
    let entry_rsp = word(STACK_TOP-8);
    let frame = Frame::collect(&ops);
    let writes = frame.footprint(words);
    for slot in &frame.slots {
        save_support(module, words, &name, *slot);
        for written in &frame.writes {
            if written != slot || frame.children.contains(written) {
                certify_word_outside(module, words, &outside_name(&name, *written, *slot), *written, *slot);
            }
        }
    }
    let mut saved = BTreeMap::new();
    fun(module, &format!("{name}_code"), "List<CallInstruction>", format!("[{}]", code.join(", ")));
    // Compare each declared instruction with its independent state step before
    // checking any accumulated execution. A stale stream fails at its first
    // divergent index, including extra or missing instructions.
    for i in 0..=n {
        let suffix = format!("{name}_code_at_{i}");
        let body = if i == 0 { format!("{name}_code()") }
            else { format!("list::List::drop({name}_code_at_{}(), 1)", i-1) };
        fun(module, &suffix, "List<CallInstruction>", body);
        if i > 0 {
            thm(module, &format!("{name}_instruction_{}", i-1),
                format!("{name}_code_at_{}() = Cons({}, {suffix}())", i-1, code[i-1]), "refl".into());
        }
    }
    thm(module, &format!("{name}_instruction_end"), format!("{name}_code_at_{n}() = []"), "refl".into());
    // A child span must be exactly the stream indexed by its reusable summary.
    // Catch an extra or changed clobber before converting any state projections.
    for (first, last) in &leaves {
        thm(module, &format!("{name}_leaf_code_{first}"),
            format!("list::List::take({name}_code_at_{first}(), {}) = {leaf_prefix}_summary_code()", last-first+1), "refl".into());
    }
    decl(module, &format!("{name}_state_0"), "MachineState<CallMemory>".into(),
        format!("MachineState(write_gpr(Rsp, {entry_rsp}, gprs), flags, rip, memory)"), false);
    for i in 0..n {
        fun(module, &format!("{name}_step_instruction_{i}"), "CallInstruction", code[i].clone());
        thm(module, &format!("{name}_step_selected_{i}"), format!("{name}_step_instruction_{i}() = {}", code[i]), "refl".into());
        decl(module, &format!("{name}_state_{}", i+1), "MachineState<CallMemory>".into(),
            format!("call_next(call_stack_access(), {name}_step_instruction_{i}(), {})", state(i)), false);
    }
    let mut known: BTreeMap<Gpr, (String, String)> = BTreeMap::new();
    for r in ABI.into_iter().chain(composition::SCRATCH).chain([Gpr::Rdi, Gpr::Rsi, Gpr::Rax]) {
        known.insert(r, (format!("read_gpr({}, gprs)", r.heather_name()), "refl".into()));
    }
    let mut rsp = STACK_TOP-8; let mut rsp_fact = "refl".to_string();
    let mut effects = format!("writes_only_equal(stack_observation, {writes}, memory, memory, refl)");
    let mut i = 0;
    while i < n {
        let before = state(i);
        if let Some((_, last)) = leaves.iter().find(|(first, _)| *first == i) {
            let end = *last+1; let after = state(end);
            let contract = format!("{name}_leaf_contract({before})");
            let left = known[&Gpr::Rdi].clone(); let right = known[&Gpr::Rsi].clone();
            let result = format!("{}({}, {})", leaf.reflected.source_name, left.0, right.0);
            let relation = format!("trans<BitVec(64)>(cong_fn<BitVec(64), BitVec(64)>(λ value => {}(value, read_gpr(Rsi, {before}.gprs)), {}), cong_fn<BitVec(64), BitVec(64)>(λ value => {}({}, value), {}))", leaf.reflected.source_name, left.1, leaf.reflected.source_name, left.0, right.1);
            let old = std::mem::take(&mut known);
            let clobbers = composition::leaf_clobbers(leaf);
            for r in ABI.into_iter().chain(composition::SCRATCH) {
                if clobbers.contains(&r) { continue; }
                let Some((value, fact)) = old.get(&r).cloned() else { continue; };
                let preserved = if ABI.contains(&r) { format!("{contract}.preserved_{}", r.heather_name().to_ascii_lowercase()) } else { format!("{name}_leaf_preserves_{}({before})", r.heather_name()) };
                record(module, &name, end, r, &value, format!("trans({preserved}, {fact})"), &mut known);
            }
            record(module, &name, end, Gpr::Rax, &result, format!("trans({contract}.result_correct, {relation})"), &mut known);
            let next_rsp = rsp+8;
            thm(module, &format!("{name}_rsp_arithmetic_{i}"), format!("@bitvec::BitVec::add(64, {}, @bitvec::BitVec::ofNat(64, 8)) = {}", word(rsp), word(next_rsp)), "refl".into());
            decl(module, &format!("{name}_rsp_{end}"), format!("read_gpr(Rsp, {after}.gprs) = {}", word(next_rsp)),
                format!("trans({contract}.stack_restored, trans<BitVec(64)>(cong_fn<BitVec(64), BitVec(64)>(λ pointer => @bitvec::BitVec::add(64, pointer, @bitvec::BitVec::ofNat(64, 8)), {rsp_fact}), {name}_rsp_arithmetic_{i}()))"), true);
            rsp_fact = format!("{name}_rsp_{end}({PARAMS})"); rsp = next_rsp;
            decl(module, &format!("{name}_effects_{end}"), format!("WritesOnly(stack_observation, {writes}, memory, {after}.memory)"),
                format!("λ address outside => trans({contract}.memory_effects(address, λ impossible => impossible), {effects}(address, outside))"), true);
            carry_saved(module, words, &name, end, &before, &after, &mut saved, &format!("{contract}.memory_effects"), None);
            effects = format!("{name}_effects_{end}({PARAMS})"); i = end; continue;
        }
        let after = state(i+1);
        if let Op::Save(r) = ops[i] {
            if saved.contains_key(&rsp) { return Err("save overlaps a live slot".into()); }
            let save_slot = word(rsp);
            let (value, fact) = known.get(&r).ok_or("saving an unknown register")?.clone();
            let register = r.heather_name();
            let raw = format!("read_gpr({register}, {before}.gprs)");
            let normalized = format!("word_write_8(call_stack_access(), {value}, {before}.memory, {save_slot})");
            decl(module, &format!("{name}_save_memory_{i}"), format!("{after}.memory = {normalized}"),
                format!("trans(cong_fn<BitVec(64), CallMemory>(λ pointer => word_write_8(call_stack_access(), {raw}, {before}.memory, pointer), {rsp_fact}), cong_fn<BitVec(64), CallMemory>(λ value => word_write_8(call_stack_access(), value, {before}.memory, {save_slot}), {fact}))"), true);
            decl(module, &format!("{name}_saved_{}", i+1), format!("stack_word(call_stack_access(), {after}.memory, {save_slot}) = {value}"),
                format!("trans(cong_fn<CallMemory, BitVec(64)>(λ memory => stack_word(call_stack_access(), memory, {save_slot}), {name}_save_memory_{i}({PARAMS})), {name}_saved_roundtrip_{rsp:x}({before}.memory, {value}))"), true);
            let local_writes = format!("λ address => WordPrefixWrites(8, {save_slot}, address)");
            decl(module, &format!("{name}_save_effect_{i}"), format!("WritesOnly(stack_observation, {local_writes}, {before}.memory, {after}.memory)"),
                format!("j(sym({name}_save_memory_{i}({PARAMS})), λ result_memory _ => WritesOnly(stack_observation, {local_writes}, {before}.memory, result_memory), word_stack_effect_8({before}.memory, {save_slot}, {value}))"), true);
            carry_saved(module, words, &name, i+1, &before, &after, &mut saved, &format!("{name}_save_effect_{i}({PARAMS})"), Some(rsp));
            saved.insert(rsp, (value.clone(), format!("{name}_saved_{}({PARAMS})", i+1)));
            let hit = frame.inject(rsp);
            decl(module, &format!("{name}_effects_{}", i+1), format!("WritesOnly(stack_observation, {writes}, memory, {after}.memory)"),
                format!("λ address outside => trans({name}_save_effect_{i}({PARAMS})(address, λ hit => outside({hit})), {effects}(address, outside))"), true);
            effects = format!("{name}_effects_{}({PARAMS})", i+1);
            decl(module, &format!("{name}_rsp_{}", i+1), format!("read_gpr(Rsp, {after}.gprs) = {}", word(rsp)), rsp_fact, true);
            rsp_fact = format!("{name}_rsp_{}({PARAMS})", i+1);
            i += 1; continue;
        }
        let (changed, expression, new_value, value_proof) = match ops[i] {
            Op::Normal(inst) => {
                let (r, expression, _) = normal_effect_fields(inst, &before).ok_or("unsupported symbolic instruction")?;
                if r == Gpr::Rsp {
                    let op = binary_name(inst).ok_or("unsupported stack adjustment")?;
                    let source = binary_source(inst).unwrap();
                    let next = if op == "sub" { rsp-8 } else { rsp+8 };
                    thm(module, &format!("{name}_rsp_arithmetic_{i}"), format!("@bitvec::BitVec::{op}(64, {}, {}) = {}", word(rsp), word(8), word(next)), "refl".into());
                    let proof = format!("trans<BitVec(64)>(bitvec64_{op}_congruent({rsp_fact}, {}), {name}_rsp_arithmetic_{i}())", known[&source].1);
                    (r, expression, word(next), proof)
                } else {
                    let (value, proof) = match inst {
                        Instruction::MovRI { immediate, .. } => (word(immediate), "refl".into()),
                        Instruction::MovRR { source, .. } => known[&source].clone(),
                        _ => { let op = binary_name(inst).unwrap(); let source = binary_source(inst).unwrap();
                            (format!("@bitvec::BitVec::{op}(64, {}, {})", known[&r].0, known[&source].0), format!("bitvec64_{op}_congruent({}, {})", known[&r].1, known[&source].1)) }
                    };
                    (r, expression, value, proof)
                }
            }
            Op::Restore(r) => {
                let (value, fact) = saved.remove(&rsp).ok_or("restore without a live saved word at RSP")?;
                (r, format!("stack_word(call_stack_access(), {before}.memory, read_gpr(Rsp, {before}.gprs))"), value,
                    format!("trans(cong_fn<BitVec(64), BitVec(64)>(λ pointer => stack_word(call_stack_access(), {before}.memory, pointer), {rsp_fact}), {fact})"))
            }
            Op::Call(_) | Op::Ret => {
                let op = if matches!(ops[i], Op::Call(_)) { "sub" } else { "add" };
                let next = if op == "sub" { rsp-8 } else { rsp+8 };
                thm(module, &format!("{name}_rsp_arithmetic_{i}"), format!("@bitvec::BitVec::{op}(64, {}, @bitvec::BitVec::ofNat(64, 8)) = {}", word(rsp), word(next)), "refl".into());
                (Gpr::Rsp, format!("@bitvec::BitVec::{op}(64, read_gpr(Rsp, {before}.gprs), @bitvec::BitVec::ofNat(64, 8))"), word(next),
                    format!("trans<BitVec(64)>(cong_fn<BitVec(64), BitVec(64)>(λ pointer => @bitvec::BitVec::{op}(64, pointer, @bitvec::BitVec::ofNat(64, 8)), {rsp_fact}), {name}_rsp_arithmetic_{i}())"))
            }
            _ => return Err("unsupported symbolic step".into()),
        };
        let old = known.clone();
        for (r, (value, fact)) in old {
            if r == changed { continue; }
            record(module, &name, i+1, r, &value,
                format!("trans(read_gpr_after_other_write({}, {}, {expression}, {before}.gprs, refl), {fact})", r.heather_name(), changed.heather_name()), &mut known);
        }
        let proof = format!("trans(read_gpr_after_write({}, {expression}, {before}.gprs), {value_proof})", changed.heather_name());
        if changed == Gpr::Rsp {
            decl(module, &format!("{name}_rsp_{}", i+1), format!("read_gpr(Rsp, {after}.gprs) = {new_value}"), proof, true);
            rsp_fact = format!("{name}_rsp_{}({PARAMS})", i+1);
        } else {
            record(module, &name, i+1, changed, &new_value, proof, &mut known);
            let carried = format!("trans(read_gpr_after_other_write(Rsp, {}, {expression}, {before}.gprs, refl), {rsp_fact})", changed.heather_name());
            decl(module, &format!("{name}_rsp_{}", i+1), format!("read_gpr(Rsp, {after}.gprs) = {}", word(rsp)), carried, true);
            rsp_fact = format!("{name}_rsp_{}({PARAMS})", i+1);
        }
        if matches!(ops[i], Op::Call(_)) {
            let child_slot = rsp-8;
            let child_writes = format!("λ address => WordPrefixWrites(8, {}, address)", word(child_slot));
            let actual = format!("@bitvec::BitVec::sub(64, read_gpr(Rsp, {before}.gprs), @bitvec::BitVec::ofNat(64, 8))");
            let pointer = format!("trans<BitVec(64)>(cong_fn<BitVec(64), BitVec(64)>(λ pointer => @bitvec::BitVec::sub(64, pointer, @bitvec::BitVec::ofNat(64, 8)), {}), {name}_rsp_arithmetic_{i}())", if i == 0 { "refl".into() } else { format!("{name}_rsp_{i}({PARAMS})") });
            let effect = format!("j({pointer}, λ pointer _ => WritesOnly(stack_observation, λ address => WordPrefixWrites(8, pointer, address), {before}.memory, {after}.memory), word_stack_effect_8({before}.memory, {actual}, call_return_address({before})))");
            decl(module, &format!("{name}_write_{}", i+1), format!("WritesOnly(stack_observation, {child_writes}, {before}.memory, {after}.memory)"), effect, true);
            carry_saved(module, words, &name, i+1, &before, &after, &mut saved, &format!("{name}_write_{}({PARAMS})", i+1), Some(child_slot));
            let exclude = format!("λ hit => outside({})", frame.inject(child_slot));
            effects = format!("λ address outside => trans({name}_write_{}({PARAMS})(address, {exclude}), ({effects})(address, outside))", i+1);
        }
        if !matches!(ops[i], Op::Call(_)) {
            let same = match ops[i] {
                Op::Normal(inst) => format!("normal_memory({}, {before})", inst.heather_expr().render()),
                Op::Ret => format!("return_memory(call_stack_access(), {before})"),
                _ => "refl".into(),
            };
            decl(module, &format!("{name}_memory_same_{i}"), format!("{after}.memory = {before}.memory"), same, true);
            effects = format!("j(sym({name}_memory_same_{i}({PARAMS})), λ final_memory _ => WritesOnly(stack_observation, {writes}, memory, final_memory), {effects})");
        }
        decl(module, &format!("{name}_effects_{}", i+1), format!("WritesOnly(stack_observation, {writes}, memory, {after}.memory)"), effects, true);
        effects = format!("{name}_effects_{}({PARAMS})", i+1);
        match ops[i] { Op::Call(_) | Op::Normal(Instruction::SubRR { destination: Gpr::Rsp, .. }) => rsp -= 8,
            Op::Ret | Op::Normal(Instruction::AddRR { destination: Gpr::Rsp, .. }) => rsp += 8, _ => {} }
        i += 1;
    }
    finish(module, words, prefix, caller, &name, n, &known, &effects, &rsp_fact, &frame)?;
    Ok(())
}

fn record(module: &mut Module, name: &str, i: usize, r: Gpr, value: &str, proof: String, known: &mut BTreeMap<Gpr, (String, String)>) {
    let fact = format!("{name}_known_{i}_{}", r.heather_name());
    decl(module, &fact, format!("read_gpr({}, {name}_state_{i}({PARAMS}).gprs) = {value}", r.heather_name()), proof, true);
    known.insert(r, (value.into(), format!("{fact}({PARAMS})")));
}

fn finish(module: &mut Module, words: &Words, prefix: &str, caller: &str, name: &str, n: usize,
    known: &BTreeMap<Gpr, (String, String)>, effects: &str, rsp_fact: &str, frame: &Frame) -> Result<(), String>
{
    let initial = format!("{name}_state_0({PARAMS})"); let after = format!("{name}_state_{n}({PARAMS})");
    let before_return = format!("{name}_state_{}({PARAMS})", n-1);
    let ret = words.get(STACK_TOP-8);
    let writes = frame.footprint(words);
    for slot in &frame.writes {
        certify_word_outside(module, words, &outside_name(name, *slot, STACK_TOP-8), *slot, STACK_TOP-8);
    }
    let mut reads = Vec::new();
    for j in 0..8 {
        let pointer = if j == 0 { ret.clone() } else { format!("@bitvec::BitVec::add(64, {ret}, @bitvec::BitVec::ofNat(64, {j}))") };
        let mut body = format!("{}().byte{j}(hit)", outside_name(name, *frame.writes.last().unwrap(), STACK_TOP-8));
        for slot in frame.writes[..frame.writes.len()-1].iter().rev() {
            body = format!("match hit {{ Inl(written) => {}().byte{j}(written), Inr(hit) => {body} }}", outside_name(name, *slot, STACK_TOP-8));
        }
        let outside = format!("λ hit => {body}");
        decl(module, &format!("{name}_return_read_{j}"), format!("call_stack_access().read({after}.memory, {pointer}) = call_stack_access().read(memory, {pointer})"),
            format!("{effects}({pointer}, {outside})"), true);
        reads.push(format!("{name}_return_read_{j}({PARAMS})"));
    }
    decl(module, &format!("{name}_return_word"), format!("stack_word(call_stack_access(), {after}.memory, {ret}) = stack_word(call_stack_access(), memory, {ret})"),
        format!("stack_word_agrees(call_stack_access(), memory, {after}.memory, {ret}, {})", reads.join(", ")), true);
    let returned = format!("trans<BitVec(64)>(cong_fn<BitVec(64), BitVec(64)>(λ pointer => stack_word(call_stack_access(), {before_return}.memory, pointer), {name}_rsp_{}({PARAMS})), {name}_return_word({PARAMS}))", n-1);
    let result = format!("{caller}(read_gpr(Rdi, gprs), read_gpr(Rsi, gprs))");
    decl(module, &format!("{name}_result_source"), format!("{} = {result}", known[&Gpr::Rax].0), format!("sym({prefix}_source_call(read_gpr(Rdi, gprs), read_gpr(Rsi, gprs)))"), true);
    let mut fields = vec![format!("result_correct := trans({}, {name}_result_source({PARAMS}))", known[&Gpr::Rax].1), format!("returned_to := {returned}"),
        format!("stack_restored := {rsp_fact}"), format!("memory_effects := {effects}")];
    for r in ABI { fields.push(format!("preserved_{} := {}", r.heather_name().to_ascii_lowercase(), known[&r].1)); }
    let post = format!("NativeIntegerCallContract<CallMemory, BitVec(8)>(stack_observation, {writes}, before, after, {caller}(read_gpr(Rdi, before.gprs), read_gpr(Rsi, before.gprs)), stack_word(call_stack_access(), before.memory, read_gpr(Rsp, before.gprs))) ∧ after.memory.file = before.memory.file");
    module.declaration(Declaration::function(format!("{name}_post"), Expr::name("Type"), Block::expression(Expr::raw(post)))
        .parameter(Parameter::explicit("before", Expr::raw("MachineState<CallMemory>"))).parameter(Parameter::explicit("after", Expr::raw("MachineState<CallMemory>"))));
    decl(module, &format!("{name}_post_proof"), format!("{name}_post({initial}, {after})"), format!("⟨NativeIntegerCallContract({}), refl⟩", fields.join(", ")), true);
    decl(module, &format!("{name}_summary"), format!("CallSummary<CallMemory>(call_stack_access(), {name}_code(), {name}_post)"),
        format!("CallSummary(requires := λ before => before = {initial}, ensures := λ before entry => j(sym(entry), λ start _ => {name}_post(start, call_run(call_stack_access(), {name}_code(), start)), {name}_post_proof({PARAMS})))"), false);
    Ok(())
}

pub(super) fn apply(module: &mut Module, prefix: &str, caller: &str, first: usize, last: usize,
    ops: &[Op], code: &[String], leaves: &[(usize, usize, String)], words: &Words)
{
    let name = format!("{prefix}_composed");
    let state = |i| format!("{prefix}_state_{i}(gprs, flags, stack)");
    let before = state(first); let after = state(last+1);
    for i in (first..=last+1).rev() {
        let suffix = format!("{prefix}_caller_suffix_{i}");
        let (body, proof) = if i == last+1 { ("[]".into(), "refl".into()) } else {
            let body = format!("Cons({}, {prefix}_caller_suffix_{}())", code[i], i+1);
            let in_leaf = leaves.iter().any(|(start, end, _)| i >= *start && i <= *end);
            let fetched = if in_leaf { format!("{prefix}_leaf_fetch_{i}(gprs, flags, stack)") } else { format!("{prefix}_step_{i}(gprs, flags, stack).left") };
            let allowed = match ops[i] {
                Op::Normal(_) => "trivial".into(),
                Op::Call(_) => format!("⟨{prefix}_stack_bound_{i}(gprs, flags, stack), ⟨{prefix}_return_canonical_{i}(gprs, flags, stack), ⟨{prefix}_target_canonical_{i}(gprs, flags, stack), {prefix}_stack_permissions_{i}(gprs, flags, stack)⟩⟩⟩"),
                Op::Save(_) | Op::Restore(_) => format!("{prefix}_stack_permissions_{i}(gprs, flags, stack)"),
                Op::Ret => format!("⟨{prefix}_stack_bound_{i}(gprs, flags, stack), ⟨{prefix}_target_canonical_{i}(gprs, flags, stack), {prefix}_stack_permissions_{i}(gprs, flags, stack)⟩⟩"),
                _ => unreachable!("callable instruction selection"),
            };
            let proof = format!("call_premises_cons(call_fetch_access(), call_stack_access(), {}, {prefix}_caller_suffix_{}(), {}, {}, {after}, {fetched}, {allowed}, {prefix}_successor_{i}(gprs, flags, stack), {prefix}_caller_ready_{}(gprs, flags, stack))", code[i], i+1, state(i), state(i+1), i+1);
            (body, proof)
        };
        fun(module, &suffix, "List<CallInstruction>", body);
        state_decl(module, &format!("{prefix}_caller_ready_{i}"), format!("CallPremises(call_fetch_access(), call_stack_access(), {suffix}(), {}, {after})", state(i)), proof, true);
    }
    let args = format!("{}.gprs, {before}.flags, {before}.memory, {before}.rip", state(first-1));
    state_decl(module, &format!("{prefix}_caller_applied"),
        format!("FetchedCallTrace(call_fetch_access(), call_stack_access(), {name}_code(), {before}, {after}) ∧ {name}_post({before}, {after})"),
        format!("use_call_summary(call_fetch_access(), call_stack_access(), {name}_code(), {name}_post, {name}_summary({args}), {before}, {after}, refl, {prefix}_caller_ready_{first}(gprs, flags, stack))"), true);
    state_decl(module, &format!("{prefix}_caller_execution"), format!("FetchedCallTrace(call_fetch_access(), call_stack_access(), {name}_code(), {before}, {after})"),
        format!("{prefix}_caller_applied(gprs, flags, stack).left"), true);
    let writes = Frame::collect(&ops[first..=last]).footprint(words);
    state_decl(module, &format!("{prefix}_caller_contract"),
        format!("NativeIntegerCallContract<CallMemory, BitVec(8)>(stack_observation, {writes}, {before}, {after}, {caller}(read_gpr(Rdi, {before}.gprs), read_gpr(Rsi, {before}.gprs)), stack_word(call_stack_access(), {before}.memory, read_gpr(Rsp, {before}.gprs)))"),
        format!("{prefix}_caller_applied(gprs, flags, stack).right.left"), true);
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn callable_requires_an_opted_in_leaf() {
        let args = ["composition.hthr", "caller", "--callable-caller", "--arg", "1", "--arg", "2", "-o", "target/unused-callable-output"]
            .map(str::to_string);
        let error = super::super::super::compile(&args, true).unwrap_err();
        assert_eq!(error, "--callable-caller requires --callee");
    }

    fn certificate(elab: &Elaborator, fixture: &str, omitted_clobber: bool) -> String {
        let prefix = "probe"; let leaf_prefix = "probe_leaf";
        let leaf = function_ir_source::generate_elaborated_x86(elab, leaf_prefix, &format!("{fixture}::leaf"), [Gpr::Rdi, Gpr::Rsi], &[Gpr::Rax, Gpr::R11, Gpr::R10, Gpr::R9, Gpr::R8, Gpr::Rcx, Gpr::Rdx], Gpr::Rax).unwrap();
        let expr = function_ir_source::reflect_call_expression(elab, &format!("{fixture}::caller"), &format!("{fixture}::leaf")).unwrap();
        if fixture == "multi_register" {
            let clobbers = composition::leaf_clobbers(&leaf);
            assert!(clobbers.contains(&Gpr::Rax) && clobbers.contains(&Gpr::R11));
        }
        let mut leaf_ops = selected_leaf_ops(&leaf, false, false);
        if omitted_clobber { leaf_ops.insert(0, Op::Normal(Instruction::MovRI { destination: Gpr::R8, immediate: 0 })); }
        let layout = layout(&[Fragment { name: "leaf".into(), ops: leaf_ops },
            Fragment { name: "caller".into(), ops: composition::lower(&expr, true, &composition::leaf_clobbers(&leaf)).unwrap() }]).unwrap();
        if fixture == "multi_stack_save" {
            let (ops, _, _) = instructions(&layout).unwrap();
            let frame = Frame::collect(&ops);
            assert_eq!(frame.slots, vec![STACK_TOP-32, STACK_TOP-24]);
            assert_eq!(frame.children, vec![STACK_TOP-40]);
            assert_eq!(ops.iter().filter(|op| matches!(op, Op::Save(_))).count(), 2);
            assert_eq!(ops.iter().filter(|op| matches!(op, Op::Restore(_))).count(), 2);
        }
        if fixture == "stack_save" {
            let (ops, _, _) = instructions(&layout).unwrap();
            assert_eq!(ops.iter().filter(|op| matches!(op, Op::Save(_))).count(), 2);
            assert_eq!(ops.iter().filter(|op| matches!(op, Op::Restore(_))).count(), 2);
        }
        let mut module = Module::default();
        for name in ["function_ir", "function_ir_x86_support", "x86_64", "x86_64_block", "x86_64_calls", "x86_64_call_frame", "x86_64_call_summary", "elf64_calls", "bitvec", "list", "logic", "bool", "option"] { module.raw(format!("import {name};")); }
        module.raw(leaf.text.clone()); emit_leaf_summary(&mut module, leaf_prefix, &leaf, false, false);
        let result = expr.expression(&format!("{fixture}::leaf"), &[Expr::name("left"), Expr::name("right")]).render();
        module.raw(format!("theorem probe_source_call(left: BitVec(64), right: BitVec(64)): {fixture}::caller(left, right) = {result} {{ refl }}"));
        let words = Words { prefix: prefix.into(), values: Default::default() };
        let mut generated = Module::default();
        emit(&mut generated, &words, prefix, &format!("{fixture}::caller"), &leaf, leaf_prefix, &layout).unwrap();
        for n in words.values.into_inner() { fun(&mut module, &format!("probe_word_{n:x}"), "BitVec(64)", word(n)); }
        module.extend(generated);
        module.render()
    }

    #[test]
    fn slow_acceptance_callable_summary_and_refusals() {
        let mut elab = super::super::super::native_test_base();
        let source = include_str!("../../../../../examples/x86-native/composition.hthr");
        elab.elab_module_source("composition", source).unwrap();
        let text = certificate(&elab, "composition", false);
        let mut checked = elab.fork();
        if let Err(error) = checked.elab_module_source("callable", &text) {
            let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/callable-refusal.hthr");
            std::fs::write(&path, &text).unwrap();
            panic!("{}; generated certificate: {}", error.render(&text), path.display());
        }
        for (name, declaration) in [
            ("stale_composed_code", "fn bad(gprs: Gprs, flags: Flags, memory: CallMemory, rip: BitVec(64)) -> CallSummary<CallMemory>(call_stack_access(), [NearReturn], probe_composed_post) { probe_composed_summary(gprs, flags, memory, rip) }"),
            ("wrong_composed_post", "fn bad(gprs: Gprs, flags: Flags, memory: CallMemory, rip: BitVec(64)) -> CallSummary<CallMemory>(call_stack_access(), probe_composed_code(), λ before after => read_gpr(Rax, after.gprs) = @bitvec::BitVec::zero(64)) { probe_composed_summary(gprs, flags, memory, rip) }"),
            ("missing_composed_entry", "theorem bad(gprs: Gprs, flags: Flags, memory: CallMemory, rip: BitVec(64), before: MachineState<CallMemory>): probe_composed_summary(gprs, flags, memory, rip).requires(before) { refl }"),
        ] {
            let source = format!("import callable; import x86_64; import x86_64_calls; import x86_64_call_summary; import elf64_calls; import bitvec; import list; {declaration}");
            let error = checked.fork().elab_module_source(name, &source).expect_err("accepted an invalid composed-function interface");
            assert!(format!("{error:?}").contains("NotConvertible"), "{}", error.render(&source));
        }
        // Corrupt a canonical step while retaining its generated register
        // facts: the ABI clobber must fail at that local proof boundary.
        let code_start = text.find("fn probe_composed_step_instruction_2(").unwrap();
        let original = "Ordinary(MovRR(Rcx, Rdi))";
        let offset = code_start + text[code_start..].find(original).unwrap();
        let mut corrupt = text.clone();
        corrupt.replace_range(offset..offset+original.len(), "Ordinary(MovRR(Rbx, Rdi))");
        let error = elab.fork().elab_module_source("clobbered_abi", &corrupt).expect_err("accepted code clobbering RBX under the old summary");
        assert!(format!("{error:?}").contains("NotConvertible"), "{}", error.render(&corrupt));
        let code_start = text.find("fn probe_composed_code(").unwrap();
        let offset = code_start + text[code_start..].find(original).unwrap();
        let mut corrupt = text.clone();
        corrupt.replace_range(offset..offset+original.len(), "Ordinary(MovRR(Rbx, Rdi))");
        let error = elab.fork().elab_module_source("stale_declared_code", &corrupt).expect_err("accepted a stale declared instruction");
        assert!(format!("{error:?}").contains("NotConvertible"), "{}", error.render(&corrupt));
        assert!(error.render(&corrupt).contains("probe_composed_instruction_2"), "{}", error.render(&corrupt));
    }

    #[test]
    fn slow_acceptance_shared_and_multi_register_summaries() {
        // Each independent fixture keeps the runner's inherited memory/CPU
        // rails. The parent does no proof work, so adding another fixture does
        // not consume the CLI unit binary's cumulative CPU allowance.
        const FIXTURE_ENV: &str = "HEATHER_COMPOSED_PROOF_FIXTURE";
        let selected = match std::env::var(FIXTURE_ENV) {
            Ok(fixture) => fixture,
            Err(_) => {
                // Cargo may replace this binary during an independent build.
                // Re-exec the running image on Linux, including an unlinked
                // inode, instead of a current_exe path ending in "(deleted)".
                let executable = if cfg!(target_os = "linux") {
                    std::path::PathBuf::from("/proc/self/exe")
                } else { std::env::current_exe().unwrap() };
                for fixture in ["multi_stack_save", "stack_save", "sharing", "multi_register"] {
                    let output = std::process::Command::new(&executable)
                        .args(["--exact", "native::calls::callable::tests::slow_acceptance_shared_and_multi_register_summaries", "--nocapture", "--test-threads=1"])
                        .env(FIXTURE_ENV, fixture).output().unwrap();
                    let stdout = String::from_utf8_lossy(&output.stdout);
                    assert!(output.status.success() && stdout.contains("1 passed; 0 failed"), "{fixture}: {stdout}\n{}",
                        String::from_utf8_lossy(&output.stderr));
                }
                return;
            }
        };
        assert!(["multi_stack_save", "stack_save", "sharing", "multi_register"].contains(&selected.as_str()));
        let mut elab = super::super::super::native_test_base();
        for (fixture, source) in [
            ("multi_stack_save", include_str!("../../../../../examples/x86-native/multi_stack_save.hthr")),
            ("stack_save", include_str!("../../../../../examples/x86-native/stack_save.hthr")),
            ("sharing", include_str!("../../../../../examples/x86-native/sharing.hthr")),
            ("multi_register", include_str!("../../../../../examples/x86-native/multi_register.hthr")),
        ] {
            if fixture != selected { continue; }
            elab.elab_module_source(fixture, source).unwrap();
            let complete = certificate(&elab, fixture, false);
            // Every control changes the caller, not its leaf theorem. Check that
            // common prefix once, then fork its checked environment for each
            // independently elaborated caller and mutation.
            let split = complete.find("fn probe_word_").unwrap();
            let imports = complete.lines().filter(|line| line.starts_with("import ")).collect::<Vec<_>>().join("\n");
            let mut proof_base = elab.fork();
            proof_base.elab_module_source("checked_leaf", &complete[..split]).unwrap();
            let caller_only = |source: &str| format!("{imports}\nimport checked_leaf;\n{}", &source[source.find("fn probe_word_").unwrap()..]);
            let text = caller_only(&complete);
            let mut checked = proof_base.fork();
            checked.elab_module_source("valid", &text).unwrap_or_else(|e| {
                std::fs::write(std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/stack-save-refusal.hthr"), &text).unwrap();
                panic!("{}", e.render(&text))
            });
            if fixture == "multi_stack_save" {
                for (label, original, replacement) in [
                    ("wrong_multi_save", "StoreStack64(R10)", "StoreStack64(R11)"),
                    ("wrong_multi_restore", "LoadStack64(R10)", "LoadStack64(R11)"),
                    ("missing_multi_restore", "LoadStack64(R10)", "Ordinary(MovRR(R10, R10))"),
                ] {
                    let start = text.find("fn probe_composed_state_0(").unwrap();
                    let offset = start + text[start..].find(original).unwrap();
                    let mut corrupt = text.clone();
                    corrupt.replace_range(offset..offset+original.len(), replacement);
                    let error = proof_base.fork().elab_module_source(label, &corrupt).expect_err("accepted stale multi-slot restoration");
                    assert!(format!("{error:?}").contains("NotConvertible"), "{}", error.render(&corrupt));
                }
                let original = "@bitvec::BitVec::bxor(64, probe_word_401fe8(), probe_word_401fe0())";
                assert!(text.contains(original));
                let corrupt = text.replacen(original, "@bitvec::BitVec::bxor(64, probe_word_401fe8(), probe_word_401fe8())", 1);
                let error = proof_base.fork().elab_module_source("aliased_live_slots", &corrupt).expect_err("accepted overlapping live save words");
                assert!(format!("{error:?}").contains("NotConvertible"), "{}", error.render(&corrupt));
                let start = text.find("fn probe_composed_post(").unwrap();
                let original = " ∨ WordPrefixWrites(8, probe_word_401fe8(), address)";
                let offset = start + text[start..].find(original).unwrap();
                let mut corrupt = text.clone();
                corrupt.replace_range(offset..offset+original.len(), "");
                // This mutation starts at the postcondition. Its earlier state
                // and memory facts are exactly those already kernel-checked.
                let corrupt = format!("{imports}\nimport checked_leaf;\nimport valid;\n{}", &corrupt[start..]);
                let error = checked.fork().elab_module_source("missing_save_footprint", &corrupt).expect_err("accepted an omitted save footprint");
                assert!(format!("{error:?}").contains("NotConvertible"), "{}", error.render(&corrupt));
            }
            if fixture == "stack_save" {
                for (label, original, replacement) in [
                    ("wrong_save", "StoreStack64(R11)", "StoreStack64(R10)"),
                    ("wrong_restore", "LoadStack64(R11)", "LoadStack64(R10)"),
                ] {
                    let start = text.find("fn probe_composed_state_0(").unwrap();
                    let offset = start + text[start..].find(original).unwrap();
                    let mut corrupt = text.clone();
                    corrupt.replace_range(offset..offset+original.len(), replacement);
                    let error = proof_base.fork().elab_module_source(label, &corrupt).expect_err("accepted a stale save/restore proof");
                    assert!(format!("{error:?}").contains("NotConvertible"), "{}", error.render(&corrupt));
                }
                let original = "@bitvec::BitVec::bxor(64, probe_word_401fe8(), probe_word_401ff0())";
                assert!(text.contains(original));
                let corrupt = text.replacen(original, "@bitvec::BitVec::bxor(64, probe_word_401fe8(), probe_word_401fe8())", 1);
                let error = proof_base.fork().elab_module_source("overlapping_save", &corrupt).expect_err("accepted overlap with the child's return word");
                assert!(format!("{error:?}").contains("NotConvertible"), "{}", error.render(&corrupt));
            }
            let corrupt = caller_only(&certificate(&elab, fixture, true));
            let error = proof_base.fork().elab_module_source("omitted_clobber", &corrupt).expect_err("accepted a clobbered live caller value");
            assert!(format!("{error:?}").contains("NotConvertible"), "{}", error.render(&corrupt));
        }
    }
}
