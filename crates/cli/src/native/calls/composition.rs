//! Bounded caller selection and checked register facts across summary applications.
use super::*;
use function_ir_source::{CallExpr, SourceBinaryOperation as B};

pub(super) const SCRATCH: [Gpr; 6] = [Gpr::R8, Gpr::R9, Gpr::R10, Gpr::R11, Gpr::Rcx, Gpr::Rdx];
const SAVED: [Gpr; 6] = [Gpr::Rbx, Gpr::Rbp, Gpr::R12, Gpr::R13, Gpr::R14, Gpr::R15];
fn binary(op: B, destination: Gpr, source: Gpr) -> Instruction {
    match op {
        B::Add => Instruction::AddRR { destination, source },
        B::Sub => Instruction::SubRR { destination, source },
        B::BitAnd => Instruction::AndRR { destination, source },
        B::BitOr => Instruction::OrRR { destination, source },
        B::BitXor => Instruction::XorRR { destination, source },
    }
}

pub(super) fn leaf_clobbers(leaf: &SourceX86Emission) -> Vec<Gpr> {
    leaf.instructions.iter().filter_map(|i| i.destination()).collect()
}

pub(super) fn lower(expr: &CallExpr, callable: bool, clobbers: &[Gpr]) -> Result<Vec<Op>, String> {
    if !callable { return lower_with_registers(expr, &SAVED, &[]); }
    let preserved: Vec<_> = SCRATCH.iter().copied().filter(|r| !clobbers.contains(r)).collect();
    if let Ok(ops) = lower_with_registers(expr, &preserved, clobbers) { return Ok(ops); }
    let borrowable: Vec<_> = SCRATCH.iter().copied().filter(|r| clobbers.contains(r)).collect();
    // Try smaller borrowed sets first. The register bound is six, so exhaustive
    // subsets are small and avoid depending on one arbitrary register order.
    for count in 1..=borrowable.len() {
        for mask in 1usize..(1 << borrowable.len()) {
            if mask.count_ones() as usize != count { continue; }
            let registers: Vec<_> = borrowable.iter().enumerate().filter_map(|(i, r)|
                ((mask >> i) & 1 == 1).then_some(*r)).chain(preserved.iter().copied()).collect();
            if let Ok(ops) = lower_with_registers(expr, &registers, clobbers) { return Ok(ops); }
        }
    }
    Err("caller register pressure exceeds six scratch registers; general expression spilling is not supported".into())
}

fn lower_with_registers(expr: &CallExpr, registers: &[Gpr], clobbers: &[Gpr]) -> Result<Vec<Op>, String> {
    // Intern the pure source tree before selection. Each node has one definition;
    // use counts retain its register until every distinct consumer has used it.
    fn intern<'a>(expr: &'a CallExpr, ids: &mut BTreeMap<&'a CallExpr, usize>, nodes: &mut Vec<&'a CallExpr>) -> usize {
        if let Some(id) = ids.get(expr) { return *id; }
        match expr {
            CallExpr::Binary(_, left, right) | CallExpr::Call(left, right) => {
                intern(left, ids, nodes); intern(right, ids, nodes);
            }
            _ => {}
        }
        let id = nodes.len(); nodes.push(expr); ids.insert(expr, id); id
    }
    let mut ids = BTreeMap::new(); let mut nodes = Vec::new();
    let root = intern(expr, &mut ids, &mut nodes);
    let mut uses = vec![0; nodes.len()]; uses[root] = 1;
    for node in &nodes {
        if let CallExpr::Binary(_, left, right) | CallExpr::Call(left, right) = node {
            uses[ids[left.as_ref()]] += 1; uses[ids[right.as_ref()]] += 1;
        }
    }
    if registers.len() < 3 { return Err("caller register pressure: leaf leaves fewer than two input registers and one temporary; spilling is not supported".into()); }
    let count = registers.len()-2;
    let inputs = [registers[count], registers[count+1]];
    let mut ops = vec![
        Op::Normal(Instruction::MovRI { destination: Gpr::R11, immediate: 8 }),
        Op::Normal(Instruction::SubRR { destination: Gpr::Rsp, source: Gpr::R11 }),
        Op::Normal(Instruction::MovRR { destination: inputs[0], source: Gpr::Rdi }),
        Op::Normal(Instruction::MovRR { destination: inputs[1], source: Gpr::Rsi }),
    ];
    let mut max_saves = 0;
    let mut locations = vec![None; nodes.len()];
    for (id, node) in nodes.iter().enumerate() {
        let allocate = |locations: &[Option<Gpr>]| registers[..count].iter().copied()
            .find(|r| !locations.contains(&Some(*r)))
            .ok_or_else(|| format!("caller register pressure exceeds {count} temporaries after leaf clobbers; spilling is not supported"));
        let dst = match node {
            CallExpr::Input(i) => inputs[*i],
            CallExpr::Constant(n) => {
                let dst = allocate(&locations)?;
                ops.push(Op::Normal(Instruction::MovRI { destination: dst, immediate: *n })); dst
            }
            CallExpr::Binary(_, left, right) | CallExpr::Call(left, right) => {
                let l = ids[left.as_ref()]; let r = ids[right.as_ref()];
                let lhs = locations[l].unwrap(); let rhs = locations[r].unwrap();
                uses[l] -= 1; uses[r] -= 1;
                let dst = if let CallExpr::Binary(op, _, _) = node {
                    let dst = if uses[l] == 0 && !inputs.contains(&lhs) { lhs } else { allocate(&locations)? };
                    if dst != lhs { ops.push(Op::Normal(Instruction::MovRR { destination: dst, source: lhs })); }
                    ops.push(Op::Normal(binary(*op, dst, rhs))); dst
                } else {
                    ops.extend([
                        Op::Normal(Instruction::MovRR { destination: Gpr::Rdi, source: lhs }),
                        Op::Normal(Instruction::MovRR { destination: Gpr::Rsi, source: rhs }),
                    ]);
                    let live: Vec<_> = locations.iter().enumerate().filter_map(|(id, r)|
                        r.filter(|r| uses[id] > 0 && clobbers.contains(r))).collect();
                    max_saves = max_saves.max(live.len());
                    slot_walk(&mut ops, &live, false);
                    ops.push(Op::Call("leaf".into()));
                    if uses[l] == 0 { locations[l] = None; }
                    if uses[r] == 0 { locations[r] = None; }
                    let dst = allocate(&locations)?;
                    ops.push(Op::Normal(Instruction::MovRR { destination: dst, source: Gpr::Rax }));
                    slot_walk(&mut ops, &live, true);
                    dst
                };
                if uses[l] == 0 { locations[l] = None; }
                if uses[r] == 0 { locations[r] = None; }
                dst
            }
        };
        locations[id] = Some(dst);
    }
    let result = locations[root].unwrap();
    ops.extend([
        Op::Normal(Instruction::MovRR { destination: Gpr::Rax, source: result }),
        Op::Normal(Instruction::MovRI { destination: Gpr::R11, immediate: 8 }),
        Op::Normal(Instruction::AddRR { destination: Gpr::Rsp, source: Gpr::R11 }),
        Op::Ret,
    ]);
    // An odd number of words changes the incoming 8-mod-16 RSP to a
    // 16-byte-aligned call base. Unused padding is outside the write footprint.
    let frame_words = max_saves.max(1) | 1;
    let sub = Op::Normal(Instruction::SubRR { destination: Gpr::Rsp, source: Gpr::R11 });
    let add = Op::Normal(Instruction::AddRR { destination: Gpr::Rsp, source: Gpr::R11 });
    for _ in 1..frame_words { ops.insert(2, sub.clone()); ops.insert(ops.len()-1, add.clone()); }
    Ok(ops)
}

fn slot_walk(ops: &mut Vec<Op>, registers: &[Gpr], restore: bool) {
    if registers.len() > 1 { ops.push(Op::Normal(Instruction::MovRI { destination: Gpr::Rax, immediate: 8 })); }
    for (i, r) in registers.iter().enumerate() {
        if i > 0 { ops.push(Op::Normal(Instruction::AddRR { destination: Gpr::Rsp, source: Gpr::Rax })); }
        ops.push(if restore { Op::Restore(*r) } else { Op::Save(*r) });
    }
    for _ in 1..registers.len() { ops.push(Op::Normal(Instruction::SubRR { destination: Gpr::Rsp, source: Gpr::Rax })); }
}

#[derive(Default)]
pub(super) struct Ledger { registers: BTreeMap<Gpr, (u64, String)>, saved: BTreeMap<u64, u64> }
impl Ledger {
    pub(super) fn value(&self, r: Gpr) -> Result<u64, String> {
        self.registers.get(&r).map(|v| v.0).ok_or_else(|| format!("uninitialized caller register {r:?}"))
    }
    pub(super) fn saved(&self, slot: u64) -> Result<u64, String> { self.saved.get(&slot).copied().ok_or_else(|| "restore without a checked save".into()) }
    pub(super) fn fact(&self, r: Gpr) -> Result<String, String> {
        self.registers.get(&r).map(|v| v.1.clone()).ok_or_else(|| format!("missing caller register evidence {r:?}"))
    }
    fn insert(&mut self, module: &mut Module, words: &Words, prefix: &str, i: usize, r: Gpr, value: u64, proof: String) {
        let name = format!("{prefix}_known_{i}_{}", r.heather_name());
        state_decl(module, &name, format!("read_gpr({}, {prefix}_state_{i}(gprs, flags, stack).gprs) = {}", r.heather_name(), words.get(value)), proof, true);
        self.registers.insert(r, (value, format!("{name}(gprs, flags, stack)")));
    }
    pub(super) fn step(&mut self, module: &mut Module, words: &Words, prefix: &str, i: usize, op: &Op, rsp: u64) -> Result<(), String> {
        let before = format!("{prefix}_state_{i}(gprs, flags, stack)");
        let mut written = None;
        if let Op::Save(r) = op { self.saved.insert(rsp, self.value(*r)?); }
        if let Op::Restore(r) = op {
            let value = self.saved(rsp)?;
            written = Some((*r, value, format!("read_gpr_after_write({}, {}, {before}.gprs)", r.heather_name(), words.get(value))));
        }
        if let Op::Normal(inst) = op {
            let (r, expr, _) = normal_effect_fields(*inst, &before).ok_or("unsupported caller instruction")?;
            if r != Gpr::Rsp {
                let (value, equality) = match *inst {
                    Instruction::MovRI { immediate, .. } => (immediate, "refl".into()),
                    Instruction::MovRR { source, .. } => (self.value(source)?, self.fact(source)?),
                    Instruction::AddRR { destination, source } | Instruction::SubRR { destination, source }
                    | Instruction::AndRR { destination, source } | Instruction::OrRR { destination, source }
                    | Instruction::XorRR { destination, source } => {
                        let a = self.value(destination)?; let b = self.value(source)?;
                        let (name, result) = match inst {
                            Instruction::AddRR { .. } => ("add", a.wrapping_add(b)),
                            Instruction::SubRR { .. } => ("sub", a.wrapping_sub(b)),
                            Instruction::AndRR { .. } => ("band", a & b),
                            Instruction::OrRR { .. } => ("bor", a | b),
                            _ => ("bxor", a ^ b),
                        };
                        let arithmetic = format!("{prefix}_arithmetic_{i}");
                        let proof = match name {
                            "add" => format!("bitvec::BitVec::add_eq_of_ripple_add(64, {}, {}, {}, refl)", words.get(a), words.get(b), words.get(result)),
                            "sub" => format!("bitvec::BitVec::sub_eq_of_ripple_sub(64, {}, {}, {}, refl)", words.get(a), words.get(b), words.get(result)),
                            _ => "refl".into(),
                        };
                        thm(module, &arithmetic, format!("@bitvec::BitVec::{name}(64, {}, {}) = {}", words.get(a), words.get(b), words.get(result)), proof);
                        (result, format!("trans(bitvec64_{name}_congruent({}, {}), {arithmetic}())", self.fact(destination)?, self.fact(source)?))
                    }
                    _ => return Err("unsupported caller arithmetic".into()),
                };
                written = Some((r, value, format!("trans(read_gpr_after_write({}, {expr}, {before}.gprs), {equality})", r.heather_name())));
            }
        }
        // Each non-leaf instruction changes at most one GPR. Transport the
        // remaining facts locally; never normalize the accumulated execution.
        let changed = match op {
            Op::Normal(inst) => normal_effect_fields(*inst, &before).map(|(r, v, _)| (r, v)),
            Op::Restore(r) => Some((*r, words.get(self.saved(rsp)?))),
            Op::Call(_) | Op::Ret => Some((Gpr::Rsp, format!("read_gpr(Rsp, {prefix}_state_{}(gprs, flags, stack).gprs)", i+1))),
            _ => None,
        };
        let old = self.registers.clone();
        for (r, (value, fact)) in old {
            if changed.as_ref().is_some_and(|(dst, _)| *dst == r) { continue; }
            let step = match &changed {
                Some((dst, value)) => format!("read_gpr_after_other_write({}, {}, {value}, {before}.gprs, refl)", r.heather_name(), dst.heather_name()),
                None => "refl".into(),
            };
            self.insert(module, words, prefix, i+1, r, value, format!("trans({step}, {fact})"));
        }
        if let Some((r, value, proof)) = written { self.insert(module, words, prefix, i+1, r, value, proof); }
        Ok(())
    }
    pub(super) fn returned(&mut self, module: &mut Module, words: &Words, prefix: &str, i: usize,
        instance: &str, values: &str, leaf: &SourceX86Emission, inputs: [u64; 2], callable: bool) -> Result<(), String>
    {
        let old = std::mem::take(&mut self.registers);
        // Retain only scratch registers untouched by the selected leaf. Their
        // preservation is checked against its actual states, not trusted here.
        let clobbers = leaf_clobbers(leaf);
        for r in if callable { SCRATCH } else { SAVED } {
            if callable && clobbers.contains(&r) { continue; }
            if let Some((value, fact)) = old.get(&r) {
                let field = r.heather_name().to_ascii_lowercase();
                self.insert(module, words, prefix, i, r, *value,
                    if callable { format!("trans(refl, {fact})") } else { format!("trans({instance}_callee_contract(gprs, flags, stack).preserved_{field}, {fact})") });
            }
        }
        let result = proposed_result(&leaf.reflected.result, inputs);
        let name = format!("{instance}_source_literal");
        thm(module, &name, format!("{}({values}_values()(64, 0), {values}_values()(64, 1)) = {}", leaf.reflected.source_name, words.get(result)), "refl".into());
        self.insert(module, words, prefix, i, Gpr::Rax, result, format!("trans({instance}_callee_result(gprs, flags, stack), {name}())"));
        Ok(())
    }
}

pub(super) fn finish(module: &mut Module, words: &Words, prefix: &str, caller: &str, inputs: [u64;2], n: usize, pc: u64, ledger: &Ledger, callable: bool) -> Result<(), String> {
    let end = format!("{prefix}_state_{n}(gprs, flags, stack)");
    let result = format!("{caller}({}, {})", words.get(inputs[0]), words.get(inputs[1]));
    if !callable { thm(module, &format!("{prefix}_source_result"), format!("{result} = {}", words.get(ledger.value(Gpr::Rdi)?)), "refl".into()); }
    state_decl(module, &format!("{prefix}_exit_status"), format!("read_gpr(Rdi, {end}.gprs) = {result}"),
        if callable { format!("trans(refl, {prefix}_caller_contract(gprs, flags, stack).result_correct)") }
        else { format!("trans({}, sym({prefix}_source_result()))", ledger.fact(Gpr::Rdi)?) }, true);
    state_decl(module, &format!("{prefix}_exit_request"), format!("LinuxExitRequest<CallMemory>({end}, {result})"),
        format!("LinuxExitRequest(number := refl, status := {prefix}_exit_status(gprs, flags, stack))"), true);
    let (fetch, _) = certify_fetch(module, words, prefix, n, &format!("{end}.memory"), pc, &[0x0f, 0x05], HEADER);
    state_decl(module, &format!("{prefix}_syscall_fetched"),
        format!("FetchedFrom(call_fetch_access(), {end}.memory, InstructionBytes({end}.rip, syscall_bytes()))"), fetch, true);
    state_decl(module, &format!("{prefix}_stack_restored"), format!("read_gpr(Rsp, {end}.gprs) = {}", words.get(STACK_TOP)), format!("{prefix}_rsp_{n}(gprs, flags, stack)"), true);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn caller_reflection_and_pressure_refusals() {
        let mut elab = super::super::super::native_test_base();
        let source = include_str!("../../../../../examples/x86-native/composition.hthr");
        elab.elab_module_source("composition", source).unwrap_or_else(|e| panic!("{}", e.render(source)));
        let expr = function_ir_source::reflect_call_expression(&elab, "composition::caller", "composition::leaf").unwrap();
        assert_eq!(lower(&expr, false, &[]).unwrap().iter().filter(|op| matches!(op, Op::Call(_))).count(), 2);
        for (name, expression, accepted) in [("source_plan", expr.clone(), true),
            ("stale_plan", CallExpr::Binary(B::Add, Box::new(expr.clone()), Box::new(CallExpr::Constant(1))), false)] {
            let result = expression.expression("composition::leaf", &[Expr::name("left"), Expr::name("right")]).render();
            let proof = format!("import composition; import bitvec; theorem agrees(left: BitVec(64), right: BitVec(64)): composition::caller(left, right) = {result} {{ refl }}");
            let checked = elab.fork().elab_module_source(name, &proof);
            if accepted { checked.unwrap_or_else(|e| panic!("{}", e.render(&proof))); }
            else { assert!(format!("{:?}", checked.expect_err("accepted a stale caller plan")).contains("NotConvertible")); }
        }
        assert!(function_ir_source::reflect_call_expression(&elab, "composition::caller", "composition::caller").unwrap_err().to_string().contains("not selected"));
        assert!(function_ir_source::reflect_call_expression(&elab, "composition::leaf", "composition::leaf").unwrap_err().to_string().contains("must call"));
        fn tree(depth: usize, seed: u64) -> CallExpr {
            if depth == 0 { return CallExpr::Constant(seed); }
            CallExpr::Binary(B::Sub, Box::new(tree(depth-1, seed*2)), Box::new(tree(depth-1, seed*2+1)))
        }
        let pressure = tree(4, 1);
        assert!(lower(&pressure, false, &[]).unwrap_err().contains("register pressure"));
        assert!(lower(&expr, true, &SCRATCH).unwrap().iter().filter(|op| matches!(op, Op::Save(_))).count() > 1);
        let many = "import bitvec; fn leaf(a: BitVec(64), b: BitVec(64)) -> BitVec(64) { @bitvec::BitVec::add(64, a, b) } fn caller(a: BitVec(64), b: BitVec(64)) -> BitVec(64) { leaf(leaf(leaf(leaf(leaf(a, b), b), b), b), b) }";
        elab.elab_module_source("many", many).unwrap();
        assert!(function_ir_source::reflect_call_expression(&elab, "many::caller", "many::leaf").unwrap_err().to_string().contains("four-call"));
    }

    #[test]
    fn shared_calls_have_one_definition_and_distinct_arguments_stay_distinct() {
        let mut elab = super::super::super::native_test_base();
        let source = include_str!("../../../../../examples/x86-native/sharing.hthr");
        elab.elab_module_source("sharing", source).unwrap();
        let expr = function_ir_source::reflect_call_expression(&elab, "sharing::caller", "sharing::leaf").unwrap();
        for callable in [false, true] {
            let ops = lower(&expr, callable, &[]).unwrap();
            assert_eq!(ops.iter().filter(|op| matches!(op, Op::Call(_))).count(), 2);
            // The shared `first + saved` is selected just once.
            assert_eq!(ops.iter().filter(|op| matches!(op, Op::Normal(Instruction::AddRR { destination, .. }) if *destination != Gpr::Rsp)).count(), 5);
            let placed = layout(&[Fragment { name: "caller".into(), ops }, Fragment { name: "leaf".into(), ops: vec![Op::Ret] }]).unwrap();
            let calls: Vec<_> = placed.placed.values().filter(|(op, _, _)| matches!(op, Op::Call(_))).collect();
            assert_eq!(calls.len(), 2);
            assert!(calls.iter().all(|(_, bytes, _)| bytes.len() == 5 && bytes[0] == 0xe8));
        }
    }

    #[test]
    fn register_evidence_rejects_a_wrong_value() {
        let base = super::super::super::native_test_base();
        let words = Words { prefix: "probe".into(), values: Default::default() };
        let mut module = Module::default();
        for name in ["x86_64", "x86_64_call_summary", "elf64_calls", "bitvec", "list", "logic", "option"] { module.raw(format!("import {name};")); }
        fun(&mut module, "probe_word_b", "BitVec(64)", word(11));
        fun(&mut module, "probe_word_c", "BitVec(64)", word(12));
        state_decl(&mut module, "probe_state_0", "MachineState<CallMemory>".into(), "call_initial([], gprs, flags, stack)".into(), false);
        let mut ledger = Ledger::default();
        for (i, inst) in [Instruction::MovRI { destination: Gpr::Rdi, immediate: 11 }, Instruction::MovRR { destination: Gpr::Rbx, source: Gpr::Rdi }].into_iter().enumerate() {
            let before = format!("probe_state_{i}(gprs, flags, stack)");
            state_decl(&mut module, &format!("probe_state_{}", i+1), "MachineState<CallMemory>".into(),
                format!("MachineState({}, {before}.rip, {before}.memory)", normal_fields(inst, &before).unwrap()), false);
            ledger.step(&mut module, &words, "probe", i, &Op::Normal(inst), STACK_TOP).unwrap();
        }
        let source = module.render();
        base.fork().elab_module_source("ledger", &source).unwrap_or_else(|e| panic!("{}", e.render(&source)));
        let original = "read_gpr(Rbx, probe_state_2(gprs, flags, stack).gprs) = probe_word_b()";
        assert!(source.contains(original));
        let wrong = source.replace(original, "read_gpr(Rbx, probe_state_2(gprs, flags, stack).gprs) = probe_word_c()");
        let error = base.fork().elab_module_source("wrong_ledger", &wrong).expect_err("accepted a stale register value");
        // Refused at the register fact, naming the value the ledger carries
        // and the stale one (the state's `.gprs` field reads spell since
        // issues/omega-record-projection-atoms.md; before, the note had no
        // spelling and the kernel's bare `NotConvertible` stood).
        let rendered = error.render(&wrong);
        assert!(rendered.contains("= probe_word_b`, but `") && rendered.contains("= probe_word_c` is expected"), "{rendered}");
    }
}
