//! Native certificates for a bounded read-only loop
//! (docs/native-bounded-loops-design.md). Every piece is an ordinary typed
//! certificate from the shared generators. This module chooses their
//! placements, composes the loop's code, and emits the two per-iteration
//! proofs the library induction (`function_ir_loop_trace::loop_trace`)
//! consumes, plus the final theorem stated against the source loop itself.
use super::*;
use crate::function_ir_x86_lower::{near_loop_edges, AccessFragment};

/// Registers for one loop. The eight head registers carry its state from one
/// iteration to the next; the rest are scratch within an iteration. `extra`
/// widens the guard's and body's temporaries (their selection may need a
/// byte-addressable register beyond these).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeLoopPlacement {
    pub base: Gpr, pub length: Gpr, pub needle: Gpr, pub cursor: Gpr, pub budget: Gpr,
    pub carry: Gpr, pub flag: Gpr, pub step: Gpr,
    pub address: Gpr, pub byte: Gpr, pub payload: Gpr, pub next_cursor: Gpr, pub next_budget: Gpr,
    pub extra: Vec<Gpr>,
}

/// `pieces` is the per-step typed certificates, to be elaborated as module
/// `{prefix}_pieces`; `text` is the loop proper (code, bytes, layout, the two
/// iteration proofs and the final theorem), which imports it. Kept apart so a
/// change to the composition rechecks only the part that composes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoopX86Emission {
    pub bytes: Vec<u8>,
    pub pieces: String,
    pub text: String,
}

/// One loop, generated and composed. A Nat carry is counted: its certificate
/// keeps `loop_fits` (carry + budget < 2^64), and `advance` names the client's
/// `LoopAdvancesByAtMostOne` theorem about the step (design §9a). A Bool
/// carry needs neither.
pub fn generate_elaborated_loop_x86(elaborator: &Elaborator, prefix: &str, source: &str, p: &NativeLoopPlacement,
    advance: Option<&str>) -> Result<LoopX86Emission, SourceError>
{
    let mut registers = vec![p.base, p.length, p.needle, p.cursor, p.budget, p.carry, p.flag, p.step,
        p.address, p.byte, p.payload, p.next_cursor, p.next_budget];
    registers.extend(&p.extra);
    if registers.iter().collect::<std::collections::BTreeSet<_>>().len() != registers.len() {
        return unsupported("loop registers must be distinct");
    }
    let reflected = reflect_elaborated_readonly_loop(elaborator, source)?;
    if matches!(reflected.carry, LoopCarry::Record(_)) { return unsupported("a record carry uses generate_elaborated_record_loop_x86"); }
    let counted = reflected.carry == LoopCarry::Natural;
    let advance = match (counted, advance) {
        (true, Some(name)) => name,
        (true, None) => return unsupported("a Nat carry needs its step's LoopAdvancesByAtMostOne theorem"),
        (false, _) => "",
    };
    let (carry_type, word_rep, invariant) = if counted { ("Nat", "loop_nat_rep", "loop_fits") }
        else { ("Bool", "loop_bool_rep", "loop_no_invariant<Bool>") };
    // The carry's placement over the register file (function_ir_loop_trace).
    let rep_name = format!("loop_in({}, {word_rep})", p.carry.heather_name());
    let step_body = reflect_elaborated_structured(elaborator, &reflected.body_name)?;
    let [payload_port, step_port] = step_body.region.outputs() else {
        return unsupported("a loop step observes exactly a payload and a discriminator");
    };
    let (payload_port, step_port) = (payload_port.id, step_port.id);
    let name = |part: &str| format!("{prefix}_{part}");
    let mut scratch = vec![p.payload, p.step, p.address, p.next_cursor, p.next_budget];
    scratch.extend(&p.extra);
    let mut guard_temps = vec![p.flag];
    guard_temps.extend(&scratch);
    let typed = |part: &str, function: &str, inputs: &[(u64, Gpr)], temps: &[Gpr], output: (u64, Gpr)| {
        generate_elaborated_typed_x86(elaborator, &name(part), &format!("function_ir_loop_x86::{function}"),
            &inputs.iter().copied().collect(), temps, &[output].into_iter().collect())
    };
    let guard = typed("guard", "loop_guard", &[(0, p.cursor), (1, p.length), (2, p.budget)], &guard_temps, (3, p.flag))?;
    let address = typed("address", "loop_address", &[(0, p.base), (1, p.cursor)], &[p.address], (2, p.address))?;
    let step = generate_elaborated_read_x86(elaborator, &name("step"), &reflected.body_name, 2, p.address,
        &[(0, p.needle), (2, p.byte), (3, p.carry)].into_iter().collect(), &scratch,
        &[(payload_port, p.payload), (step_port, p.step)].into_iter().collect())?;
    let next_cursor = typed("next_cursor", "loop_next_cursor", &[(0, p.cursor)], &[p.next_cursor, p.address], (1, p.next_cursor))?;
    let next_budget = typed("next_budget", "loop_next_budget", &[(0, p.budget)], &[p.next_budget, p.address], (1, p.next_budget))?;
    let keep_carry = typed("keep_carry", "loop_copy", &[(0, p.payload)], &[p.carry], (1, p.carry))?;
    let keep_cursor = typed("keep_cursor", "loop_copy", &[(0, p.next_cursor)], &[p.cursor], (1, p.cursor))?;
    let keep_budget = typed("keep_budget", "loop_copy", &[(0, p.next_budget)], &[p.budget], (1, p.budget))?;

    let pure = |part: &str, emission: &x86::StructuredX86Emission| AccessFragment::structured(&name(part), &emission.lowered);
    let read = AccessFragment::read(step.load).sequence(AccessFragment::structured(&name("step_body"), &step.body));
    let tail5 = pure("keep_cursor", &keep_cursor).sequence(pure("keep_budget", &keep_budget));
    let tail4 = pure("keep_carry", &keep_carry).sequence(tail5.clone());
    let tail3 = pure("next_budget", &next_budget).sequence(tail4.clone());
    let tail2 = pure("next_cursor", &next_cursor).sequence(tail3.clone());
    let tail1 = read.clone().sequence(tail2.clone());
    let body = pure("address", &address).sequence(tail1.clone());
    let guard_fragment = pure("guard", &guard);
    let (exit, _, back) = near_loop_edges(guard_fragment.bytes.len(), body.bytes.len()).map_err(SourceError::Unsupported)?;
    let looped = AccessFragment::looped(guard_fragment.clone(), p.flag, body.clone(), p.step).map_err(SourceError::Unsupported)?;

    let mut pieces = Module::default();
    for text in [&guard.text, &address.text, &step.text, &next_cursor.text, &next_budget.text,
        &keep_carry.text, &keep_cursor.text, &keep_budget.text] { pieces.raw(text.clone()); }
    pieces.raw(generate_readonly_loop_certificate(&name("loop"), &reflected));
    let pieces = stitch_imports(&pieces.render());
    let mut module = Module::default();
    module.raw(pieces.lines().take_while(|line| line.starts_with("import ")).collect::<Vec<_>>().join("\n"));
    module.raw(format!("import {prefix}_pieces; import function_ir_loop_trace; import x86_64_access_code; import x86_64_data_read; import x86_64_block; import list; import logic; import option;"));
    module.raw(looped.publish(prefix));
    let reg = |g: Gpr| g.heather_name();
    let placement = name("placement");
    module.declaration(Declaration::function(&placement, HeatherExpr::name("LoopPlacement"), Block::expression(HeatherExpr::raw(format!(
        "LoopPlacement(base := {}, length := {}, needle := {}, cursor := {}, budget := {}, carry := {}, flag := {}, step := {})",
        reg(p.base), reg(p.length), reg(p.needle), reg(p.cursor), reg(p.budget), reg(p.carry), reg(p.flag), reg(p.step))))));
    let body_code = name("body_code");
    module.declaration(Declaration::function(&body_code, HeatherExpr::name("AccessCode"), Block::expression(HeatherExpr::raw(body.code()))));
    let region = format!("{}_region()", name("loop"));
    let guard_code = guard_fragment.code();

    // The guard: its typed result is loop_run's decision; nothing else moves.
    let (g, cw, lw, bw) = (name("guard"), format!("read_gpr({}, before.gprs)", reg(p.cursor)),
        format!("read_gpr({}, before.gprs)", reg(p.length)), format!("read_gpr({}, before.gprs)", reg(p.budget)));
    let kept = [p.base, p.length, p.needle, p.cursor, p.budget].map(|r| format!("{g}_preserves({}, before, trivial)", reg(r))).join(", ");
    let kept = format!("{kept}, j(sym({g}_preserves({c}, before, trivial)), λ word _ => {word_rep}(word, carry), head.carry_placed)", c = reg(p.carry));
    module.declaration(Declaration::theorem(name("guard_step"),
        HeatherExpr::raw(format!("LoopGuardStep<M, {carry_type}>({placement}(), {rep_name}, access, buffer, needle, {guard_code})")),
        Block::expression(HeatherExpr::raw(format!("λ before cursor budget carry head => Exists({g}_after(before), ⟨refl, ⟨\
            trans({g}_typed_correct({cw}, {lw}, {bw}, before, refl, refl, refl), cong_fn<Bool, BitVec(64)>(loop_bit, \
            loop_guard_word({cw}, {lw}, {bw}, cursor, buffer.length, budget, head.cursor_placed, head.length_placed, head.budget_placed))), \
            loop_head_transport({placement}(), {rep_name}, access, buffer, needle, before, {g}_after(before), cursor, budget, carry, head, \
            {kept}, {g}_memory(before))⟩⟩)")))).generic("M").parameters(vec![
        Parameter::explicit("access", HeatherExpr::raw("ByteReadAccess<M>")),
        Parameter::explicit("buffer", HeatherExpr::name("ReadonlyBytes")),
        Parameter::explicit("needle", HeatherExpr::raw("BitVec(8)"))]));

    // One iteration: s0 -address-> s1 -load, step-> s2 -next cursor-> s3
    // -next budget-> s4 -keep carry-> s5 -keep cursor-> s6 -keep budget-> s7.
    let (a, st, nc, nb, kc, kcur, kb) = (name("address"), name("step"), name("next_cursor"), name("next_budget"),
        name("keep_carry"), name("keep_cursor"), name("keep_budget"));
    let kept_by = |r: Gpr, index: usize| -> String {
        let r = reg(r);
        match index {
            0 => format!("{a}_preserves({r}, s0, trivial)"),
            1 => format!("trans({st}_body_preserves({r}, loaded, trivial), byte_load_preserves({st}_load(), byte, s1, {r}, refl))"),
            i => format!("{}_preserves({r}, s{i}, trivial)", [&nc, &nb, &kc, &kcur, &kb][i - 2]),
        }
    };
    // read_gpr(r, s_to) = read_gpr(r, s_from), one step at a time.
    let chain = |r: Gpr, from: usize, to: usize| -> String {
        (from + 1..to).fold(kept_by(r, from), |inner, i| format!("trans({}, {inner})", kept_by(r, i)))
    };
    let chain7 = |r: Gpr| chain(r, 0, 7);
    let observed = format!("needle, cursor, byte, carry, access, s1, placed_needle, placed_carry, canonical, present1");
    let execution = format!("access_sequence(access, AccessPure({a}_code()), {t1}, s0, s1, s7, refl, \
        access_sequence(access, {r}, {t2}, s1, s2, s7, \
            access_sequence(access, AccessRead({st}_load()), AccessPure({st}_body_code()), s1, loaded, s2, \
                Exists(byte, ByteLoadStep(canonical := canonical, present := present1, execution := refl)), refl), \
        access_sequence(access, AccessPure({nc}_code()), {t3}, s2, s3, s7, refl, \
        access_sequence(access, AccessPure({nb}_code()), {t4}, s3, s4, s7, refl, \
        access_sequence(access, AccessPure({kc}_code()), {t5}, s4, s5, s7, refl, \
        access_sequence(access, AccessPure({kcur}_code()), AccessPure({kb}_code()), s5, s6, s7, refl, refl))))))",
        t1 = tail1.code(), r = read.code(), t2 = tail2.code(), t3 = tail3.code(), t4 = tail4.code(), t5 = tail5.code());
    let lets = [
        ("s1", format!("{a}_after(s0)")),
        ("address_word", format!("loop_placed_address({addr}, s1, buffer, cursor, read_gpr({base}, s0.gprs), read_gpr({cur}, s0.gprs), \
            head.base_placed, head.cursor_placed, head.inside, bounded, {a}_typed_correct(read_gpr({base}, s0.gprs), read_gpr({cur}, s0.gprs), s0, refl, refl))",
            addr = reg(p.address), base = reg(p.base), cur = reg(p.cursor))),
        ("present1", format!("j(sym({a}_memory(s0)), λ m _ => access.read(m, read_gpr({addr}, s1.gprs)) = Some(byte), \
            loop_read_address(access, s0.memory, buffer, cursor, read_gpr({addr}, s1.gprs), byte, head.memory_agrees, address_word, present))", addr = reg(p.address))),
        ("canonical", format!("loop_address_canonical(buffer, cursor, read_gpr({}, s1.gprs), address_word, open, low)", reg(p.address))),
        ("placed_needle", format!("sym(trans({}, head.needle_placed))", kept_by(p.needle, 0))),
        ("placed_carry", if counted {
            format!("trans(loop_nat_placed(read_gpr({c}, s0.gprs), carry, head.carry_placed), sym({}))", kept_by(p.carry, 0), c = reg(p.carry))
        } else { format!("sym(trans({}, head.carry_placed))", kept_by(p.carry, 0)) }),
        ("payload", format!("{st}_read_correct({observed})")),
        ("stepped", format!("{st}_output_{step_port}_read_correct({observed})")),
        ("loaded", format!("byte_load_after({st}_load(), byte, s1)")),
        ("s2", format!("{st}_body_after(loaded)")),
        ("s3", format!("{nc}_after(s2)")),
        ("s4", format!("{nb}_after(s3)")),
        ("s5", format!("{kc}_after(s4)")),
        ("s6", format!("{kcur}_after(s5)")),
        ("s7", format!("{kb}_after(s6)")),
        ("value", "λ (word: BitVec(64)) => word.toNat()".to_string()),
        ("cursor_word", format!("trans(cong_fn(value, {}), head.cursor_placed)", chain(p.cursor, 0, 2))),
        ("length_word", format!("trans(cong_fn(value, {}), head.length_placed)", chain(p.length, 0, 2))),
        ("cursor_next", format!("trans(cong_fn(value, trans({}, trans({kcur}_typed_correct(read_gpr({ncr}, s5.gprs), s5, refl), \
            trans({}, {nc}_typed_correct(read_gpr({cur}, s2.gprs), s2, refl))))), \
            loop_cursor_increment(read_gpr({cur}, s2.gprs), read_gpr({len}, s2.gprs), cursor, buffer.length, cursor_word, length_word, open))",
            chain(p.cursor, 6, 7), chain(p.next_cursor, 3, 5), ncr = reg(p.next_cursor), cur = reg(p.cursor), len = reg(p.length))),
        ("budget_word", format!("trans(cong_fn(value, {}), head.budget_placed)", chain(p.budget, 0, 3))),
        ("budget_next", format!("trans(cong_fn(value, trans({kb}_typed_correct(read_gpr({nbr}, s6.gprs), s6, refl), \
            trans({}, {nb}_typed_correct(read_gpr({bud}, s3.gprs), s3, refl)))), loop_budget_decrement(read_gpr({bud}, s3.gprs), rest, budget_word))",
            chain(p.next_budget, 4, 6), nbr = reg(p.next_budget), bud = reg(p.budget))),
        ("carry_word", format!("trans({}, trans({kc}_typed_correct(read_gpr({pay}, s4.gprs), s4, refl), trans({}, payload)))",
            chain(p.carry, 5, 7), chain(p.payload, 2, 4), pay = reg(p.payload))),
        ("step_reg", format!("trans({}, stepped)", chain(p.step, 2, 7))),
        ("memory", format!("trans({kb}_memory(s6), trans({kcur}_memory(s5), trans({kc}_memory(s4), trans({nb}_memory(s3), \
            trans({nc}_memory(s2), trans({st}_body_memory(loaded), {a}_memory(s0)))))))")),
        ("step", format!("{region}.body(needle, cursor, byte, carry)")),
        // A counted carry is read back as its Nat under the invariant the
        // step keeps; a Bool carry is its placed bit already.
        ("next_invariant", if counted {
            format!("loop_fits_step(cursor, rest, carry, loop_step_payload(step), inv, {advance}()(needle, cursor, byte, carry))")
        } else { "trivial".to_string() }),
        ("carry_next", if counted {
            format!("loop_nat_word(read_gpr({}, s7.gprs), loop_step_payload(step), carry_word, loop_fits_bound(Succ(cursor), rest, loop_step_payload(step), next_invariant))", reg(p.carry))
        } else { "carry_word".to_string() }),
        ("next_head", format!("loop_head_advance({placement}(), {rep_name}, access, buffer, needle, s0, s7, cursor, Succ(rest), rest, carry, \
            loop_step_payload(step), head, {}, {}, {}, cursor_next, budget_next, carry_next, open, memory)",
            chain7(p.base), chain7(p.length), chain7(p.needle))),
        ("execution", execution),
    ];
    let lets = lets.iter().map(|(name, value)| format!("let {name} = {value};")).collect::<Vec<_>>().join("\n        ");
    module.declaration(Declaration::theorem(name("body_step"),
        HeatherExpr::raw(format!("LoopBodyStep<M, {carry_type}>({placement}(), {rep_name}, {invariant}, access, buffer, needle, {region}, {body_code}())")),
        Block::expression(HeatherExpr::raw(format!("λ s0 cursor rest carry byte head inv open present => {{\n        {lets}\n        \
            Exists(s7, ⟨execution, loop_stepped({placement}(), {rep_name}, {invariant}, access, buffer, needle, s0, s7, cursor, rest, \
            {}, step, step_reg, next_head, next_invariant)⟩)\n    }}", chain7(p.flag))))).generic("M").parameters(vec![
        Parameter::explicit("access", HeatherExpr::raw("ByteReadAccess<M>")),
        Parameter::explicit("buffer", HeatherExpr::name("ReadonlyBytes")),
        Parameter::explicit("needle", HeatherExpr::raw("BitVec(8)")),
        Parameter::explicit("bounded", HeatherExpr::raw("LoopAddressBound(64, buffer)")),
        Parameter::explicit("low", HeatherExpr::raw("buffer.base + buffer.length <= nat::Nat::pow(2, 47)"))]));

    // The whole loop, stated against the named source function. Premises are
    // the explicit export boundary: placement (LoopHead), the address bounds,
    // and the reads the chosen path makes. ABI entry, RET and fetch are outside.
    let exit = format!("@bitvec::BitVec::ofNat(32, {exit})");
    let back = format!("@bitvec::BitVec::ofNat(32, {back})");
    let observed = |outcome: &str| format!("LoopObserved<M, {carry_type}>({placement}(), {rep_name}, {outcome})");
    let invariant_proof = if counted { "fits" } else { "trivial" };
    module.declaration(Declaration::theorem(name("native"),
        HeatherExpr::raw(format!("Exists<MachineState<M>>(λ after => AccessArtifact<M>(access, {prefix}_code(), {prefix}_bytes(), before, after) ∧ \
            {})", observed(&format!("after, {}(buffer, needle, budget, cursor, carry)", reflected.source_name)))),
        Block::expression(HeatherExpr::raw(format!("{{
        let traced = loop_trace({placement}(), {rep_name}, {invariant}, access, buffer, needle, {region}, \
            {guard_code}, {body_code}(), {exit}, {back}, {prefix}_guard_step(access, buffer, needle), \
            {prefix}_body_step(access, buffer, needle, bounded, low), budget, before, cursor, carry, head, {invariant_proof}, readable);
        Exists(traced.witness, ⟨AccessArtifact(encoding := {prefix}_encoding(), layout := {prefix}_layout(), execution := traced.proof.left), \
            j({}_source_agreement(buffer, needle, budget, cursor, carry), λ outcome _ => {}, traced.proof.right)⟩)
    }}", name("loop"), observed("traced.witness, outcome"))))).generic("M").parameters(vec![
        Parameter::explicit("access", HeatherExpr::raw("ByteReadAccess<M>")),
        Parameter::explicit("before", HeatherExpr::raw("MachineState<M>")),
        Parameter::explicit("buffer", HeatherExpr::name("ReadonlyBytes")),
        Parameter::explicit("needle", HeatherExpr::raw("BitVec(8)")),
        Parameter::explicit("budget", HeatherExpr::name("Nat")),
        Parameter::explicit("cursor", HeatherExpr::name("Nat")),
        Parameter::explicit("carry", HeatherExpr::name(carry_type)),
        Parameter::explicit("bounded", HeatherExpr::raw("LoopAddressBound(64, buffer)")),
        Parameter::explicit("low", HeatherExpr::raw("buffer.base + buffer.length <= nat::Nat::pow(2, 47)")),
        Parameter::explicit("head", HeatherExpr::raw(format!("LoopHead<M, {carry_type}>({placement}(), {rep_name}, access, buffer, needle, before, cursor, budget, carry)"))),
        Parameter::explicit("readable", HeatherExpr::raw(format!("LoopReadable(budget, {region}, buffer, needle, cursor, carry)")))]
        .into_iter().chain(counted.then(|| Parameter::explicit("fits", HeatherExpr::raw("loop_fits(cursor, budget, carry)")))).collect::<Vec<_>>()));
    Ok(LoopX86Emission { bytes: looped.bytes, pieces, text: stitch_imports(&module.render()) })
}

/// One `import m;` per module, first, whatever line the pieces wrote them on.
fn stitch_imports(text: &str) -> String {
    let mut imports: Vec<String> = Vec::new();
    let mut body = String::new();
    for line in text.lines() {
        let trimmed = line.trim_start();
        if trimmed.starts_with("import ") {
            for item in trimmed.split(';').map(str::trim).filter(|item| !item.is_empty()) {
                let item = format!("{item};");
                if !imports.contains(&item) { imports.push(item); }
            }
        } else {
            body.push_str(line);
            body.push('\n');
        }
    }
    format!("{}\n{body}", imports.join("\n"))
}
