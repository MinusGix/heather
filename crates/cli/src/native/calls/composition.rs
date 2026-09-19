//! Bounded caller selection and checked register facts across summary applications.
use super::*;
use function_ir_source::{CallExpr, SourceBinaryOperation as B};

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

pub(super) fn lower(expr: &CallExpr) -> Result<Vec<Op>, String> {
    fn emit(expr: &CallExpr, free: &[Gpr], ops: &mut Vec<Op>) -> Result<Gpr, String> {
        let (&dst, rest) = free.split_first().ok_or("caller register pressure exceeds four temporaries; spilling is not supported")?;
        match expr {
            CallExpr::Input(i) => ops.push(Op::Normal(Instruction::MovRR { destination: dst, source: [Gpr::R14, Gpr::R15][*i] })),
            CallExpr::Constant(n) => ops.push(Op::Normal(Instruction::MovRI { destination: dst, immediate: *n })),
            CallExpr::Binary(op, left, right) => {
                emit(left, free, ops)?;
                let rhs = emit(right, rest, ops)?;
                ops.push(Op::Normal(binary(*op, dst, rhs)));
            }
            CallExpr::Call(left, right) => {
                emit(left, free, ops)?;
                let rhs = emit(right, rest, ops)?;
                ops.extend([
                    Op::Normal(Instruction::MovRR { destination: Gpr::Rdi, source: dst }),
                    Op::Normal(Instruction::MovRR { destination: Gpr::Rsi, source: rhs }),
                    Op::Call("leaf".into()),
                    Op::Normal(Instruction::MovRR { destination: dst, source: Gpr::Rax }),
                ]);
            }
        }
        Ok(dst)
    }
    let mut ops = vec![
        Op::Normal(Instruction::MovRI { destination: Gpr::R11, immediate: 8 }),
        Op::Normal(Instruction::SubRR { destination: Gpr::Rsp, source: Gpr::R11 }),
        Op::Normal(Instruction::MovRR { destination: Gpr::R14, source: Gpr::Rdi }),
        Op::Normal(Instruction::MovRR { destination: Gpr::R15, source: Gpr::Rsi }),
    ];
    let result = emit(expr, &SAVED[..4], &mut ops)?;
    ops.extend([
        Op::Normal(Instruction::MovRR { destination: Gpr::Rax, source: result }),
        Op::Normal(Instruction::MovRI { destination: Gpr::R11, immediate: 8 }),
        Op::Normal(Instruction::AddRR { destination: Gpr::Rsp, source: Gpr::R11 }),
        Op::Ret,
    ]);
    Ok(ops)
}

#[derive(Default)]
pub(super) struct Ledger { registers: BTreeMap<Gpr, (u64, String)> }
impl Ledger {
    pub(super) fn value(&self, r: Gpr) -> Result<u64, String> {
        self.registers.get(&r).map(|v| v.0).ok_or_else(|| format!("uninitialized caller register {r:?}"))
    }
    pub(super) fn fact(&self, r: Gpr) -> Result<String, String> {
        self.registers.get(&r).map(|v| v.1.clone()).ok_or_else(|| format!("missing caller register evidence {r:?}"))
    }
    fn insert(&mut self, module: &mut Module, words: &Words, prefix: &str, i: usize, r: Gpr, value: u64, proof: String) {
        let name = format!("{prefix}_known_{i}_{}", r.heather_name());
        state_decl(module, &name, format!("read_gpr({}, {prefix}_state_{i}(gprs, flags, stack).gprs) = {}", r.heather_name(), words.get(value)), proof, true);
        self.registers.insert(r, (value, format!("{name}(gprs, flags, stack)")));
    }
    pub(super) fn step(&mut self, module: &mut Module, words: &Words, prefix: &str, i: usize, op: &Op) -> Result<(), String> {
        let before = format!("{prefix}_state_{i}(gprs, flags, stack)");
        let mut written = None;
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
                            "add" => format!("bitvec::add_eq_of_ripple_add(64, {}, {}, {}, refl)", words.get(a), words.get(b), words.get(result)),
                            "sub" => format!("bitvec::sub_eq_of_ripple_sub(64, {}, {}, {}, refl)", words.get(a), words.get(b), words.get(result)),
                            _ => "refl".into(),
                        };
                        thm(module, &arithmetic, format!("bitvec::{name}(64, {}, {}) = {}", words.get(a), words.get(b), words.get(result)), proof);
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
        instance: &str, values: &str, leaf: &SourceX86Emission, inputs: [u64; 2]) -> Result<(), String>
    {
        let old = std::mem::take(&mut self.registers);
        for r in SAVED {
            if let Some((value, fact)) = old.get(&r) {
                let field = r.heather_name().to_ascii_lowercase();
                self.insert(module, words, prefix, i, r, *value,
                    format!("trans({instance}_callee_contract(gprs, flags, stack).preserved_{field}, {fact})"));
            }
        }
        let result = proposed_result(&leaf.reflected.result, inputs);
        let name = format!("{instance}_source_literal");
        thm(module, &name, format!("{}({values}_values()(64, 0), {values}_values()(64, 1)) = {}", leaf.reflected.source_name, words.get(result)), "refl".into());
        self.insert(module, words, prefix, i, Gpr::Rax, result, format!("trans({instance}_callee_result(gprs, flags, stack), {name}())"));
        Ok(())
    }
}

pub(super) fn finish(module: &mut Module, words: &Words, prefix: &str, caller: &str, inputs: [u64;2], n: usize, pc: u64, ledger: &Ledger) -> Result<(), String> {
    let end = format!("{prefix}_state_{n}(gprs, flags, stack)");
    let result = format!("{caller}({}, {})", words.get(inputs[0]), words.get(inputs[1]));
    thm(module, &format!("{prefix}_source_result"), format!("{result} = {}", words.get(ledger.value(Gpr::Rdi)?)), "refl".into());
    state_decl(module, &format!("{prefix}_exit_status"), format!("read_gpr(Rdi, {end}.gprs) = {result}"),
        format!("trans({}, sym({prefix}_source_result()))", ledger.fact(Gpr::Rdi)?), true);
    state_decl(module, &format!("{prefix}_exit_request"), format!("LinuxExitRequest<CallMemory>({end}, {result})"),
        format!("LinuxExitRequest(number := refl, status := {prefix}_exit_status(gprs, flags, stack))"), true);
    let (fetch, _) = certify_fetch(module, words, prefix, n, &format!("{end}.memory"), pc, &[0x0f, 0x05], HEADER);
    state_decl(module, &format!("{prefix}_syscall_fetched"),
        format!("FetchedFrom(call_fetch_access(), {end}.memory, InstructionBytes({end}.rip, linux_syscall_bytes()))"), fetch, true);
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
        assert_eq!(lower(&expr).unwrap().iter().filter(|op| matches!(op, Op::Call(_))).count(), 2);
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
        let mut pressure = CallExpr::Call(Box::new(CallExpr::Input(1)), Box::new(CallExpr::Input(0)));
        for _ in 0..4 { pressure = CallExpr::Binary(B::Sub, Box::new(CallExpr::Input(0)), Box::new(pressure)); }
        assert!(lower(&pressure).unwrap_err().contains("register pressure"));
        let many = "import bitvec; fn leaf(a: BitVec(64), b: BitVec(64)) -> BitVec(64) { bitvec::add(64, a, b) } fn caller(a: BitVec(64), b: BitVec(64)) -> BitVec(64) { leaf(leaf(leaf(leaf(leaf(a, b), b), b), b), b) }";
        elab.elab_module_source("many", many).unwrap();
        assert!(function_ir_source::reflect_call_expression(&elab, "many::caller", "many::leaf").unwrap_err().to_string().contains("four-call"));
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
            ledger.step(&mut module, &words, "probe", i, &Op::Normal(inst)).unwrap();
        }
        let source = module.render();
        base.fork().elab_module_source("ledger", &source).unwrap_or_else(|e| panic!("{}", e.render(&source)));
        let original = "read_gpr(Rbx, probe_state_2(gprs, flags, stack).gprs) = probe_word_b()";
        assert!(source.contains(original));
        let wrong = source.replace(original, "read_gpr(Rbx, probe_state_2(gprs, flags, stack).gprs) = probe_word_c()");
        let error = base.fork().elab_module_source("wrong_ledger", &wrong).expect_err("accepted a stale register value");
        assert!(format!("{error:?}").contains("NotConvertible"), "{}", error.render(&wrong));
    }
}
