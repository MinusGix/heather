//! Native certificates for a bounded read-only loop
//! (docs/native-bounded-loops-design.md, docs/native-wc-design.md §4). Every
//! piece is an ordinary typed certificate from the shared generators; this
//! module chooses their placements, composes the loop's code, and emits the
//! two per-iteration proofs the library induction
//! (`function_ir_loop_trace::loop_trace`) consumes, plus the final theorem
//! stated against the source loop itself.
//!
//! The state's fields sit in registers of their own, and one iteration
//! updates them in place, one at a time: each field is computed alone
//! (`generate_elaborated_typed_fields_x86`) straight into its own register,
//! whose old value is dead once the field's piece has read it
//! (structured-lowering-in-place-results), in an order where no field reads a
//! register an earlier field was written to. The discriminator comes last when it reads no field (so the field
//! pieces may borrow its register), first otherwise. A Nat or Bool state is
//! a record of one field, which is the state itself
//! (docs/native-loop-generator-fold-design.md §3.1).
use super::*;
use super::structured::{FieldPiece, StructuredSourceRecord};
use crate::function_ir_x86_lower::{near_loop_edges, AccessFragment, ByteLoad};

/// Registers for a loop. The head registers carry its position from one
/// iteration to the next and `fields` its state; `byte` holds the load's
/// address, then the byte. `scratch` needs three registers, the pieces'
/// temporaries: comparisons need byte-addressable ones among them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeLoopPlacement {
    pub base: Gpr, pub length: Gpr, pub needle: Gpr, pub cursor: Gpr, pub budget: Gpr,
    pub flag: Gpr, pub step: Gpr, pub byte: Gpr,
    /// One register per field, in declaration order; one for a Nat or Bool.
    pub fields: Vec<Gpr>,
    pub scratch: Vec<Gpr>,
}

/// Fields in an order that writes none back before every other field that
/// reads it is done. A field reading itself is fine: it is computed before
/// its own register is written.
fn write_order(reads: &[Vec<usize>]) -> Result<Vec<usize>, SourceError> {
    let count = reads.len();
    let mut order = Vec::new();
    let mut done = vec![false; count];
    while order.len() < count {
        let next = (0..count).find(|&i| !done[i] && (0..count).all(|j| j == i || done[j] || !reads[j].contains(&i)))
            .ok_or_else(|| SourceError::Unsupported("the step's fields read each other in a cycle; in-place update needs a spare register".into()))?;
        done[next] = true;
        order.push(next);
    }
    Ok(order)
}

/// A right-nested conjunction's component `i` of `count`.
fn component(value: &str, i: usize, count: usize) -> String {
    let mut path = value.to_string();
    for _ in 0..i { path.push_str(".right"); }
    if i + 1 < count { path.push_str(".left"); }
    path
}
fn conjunction(parts: &[String]) -> String {
    match parts.split_last() {
        None => "True".into(),
        Some((last, rest)) => rest.iter().rev().fold(last.clone(), |acc, part| format!("({part}) ∧ ({acc})")),
    }
}
fn tuple(parts: &[String]) -> String {
    match parts.split_last() {
        None => "trivial".into(),
        Some((last, rest)) => rest.iter().rev().fold(last.clone(), |acc, part| format!("⟨{part}, {acc}⟩")),
    }
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

/// One loop, generated and composed. Every Nat field is counted: the
/// certificate keeps it below 2^64 with the budget still to run (`_fits`),
/// and `advance` names the client's theorem that the step grows each by at
/// most one (docs/native-bounded-loops-design.md §9a).
pub fn generate_elaborated_loop_x86(elaborator: &Elaborator, prefix: &str, source: &str, p: &NativeLoopPlacement, advance: Option<&str>)
    -> Result<LoopX86Emission, SourceError>
{
    let reflected = reflect_elaborated_readonly_loop(elaborator, source)?;
    // A Nat or Bool is a state of one field, which is the state itself.
    let (carry_type, fields, scalar) = match reflected.carry.clone() {
        LoopCarry::Record(StructuredSourceRecord { type_name, fields, .. }) => (type_name, fields, false),
        LoopCarry::Natural => ("Nat".to_string(), vec![("count".to_string(), StructuredSourceType::NatWord)], true),
        LoopCarry::Boolean => ("Bool".to_string(), vec![("flag".to_string(), StructuredSourceType::Boolean)], true),
    };
    // Field `i` of a state spelled `value`.
    let field_of = |value: &str, i: usize| if scalar { value.to_string() } else { format!("{value}.{}", fields[i].0) };
    let k = fields.len();
    if p.fields.len() != k { return unsupported("one register per record field"); }
    if p.scratch.len() < 3 { return unsupported("the record loop needs three scratch registers"); }
    let mut registers = vec![p.base, p.length, p.needle, p.cursor, p.budget, p.flag, p.step, p.byte];
    registers.extend(&p.fields);
    registers.extend(&p.scratch);
    if registers.iter().collect::<std::collections::BTreeSet<_>>().len() != registers.len() {
        return unsupported("loop registers must be distinct");
    }
    let body = reflect_elaborated_structured(elaborator, &reflected.body_name)?;
    // The body's ports: needle 0, the unused cursor, byte 2, then the fields.
    let field_leaf = |f: &str| body.leaves.iter().position(|(parameter, field)| *parameter == 3 && if scalar { field.is_none() } else { field.as_deref() == Some(f) });
    let leaves: Vec<u64> = fields.iter().map(|(f, _)| field_leaf(f).map(|l| l as u64)
        .ok_or_else(|| SourceError::Unsupported(format!("the step's carry has no field `{f}`")))).collect::<Result<_, _>>()?;
    let outputs = body.region.outputs().to_vec();
    if outputs.len() != k + 1 { return unsupported("a record step observes each field and a discriminator"); }
    let reads: Vec<Vec<usize>> = (0..k).map(|i| {
        let narrowed = cert::narrow_structured_region(&body.region, &[outputs[i]]);
        narrowed.inputs().iter().filter_map(|port| leaves.iter().position(|leaf| *leaf == port.id)).collect()
    }).collect();
    let order = write_order(&reads)?;
    let nat_fields: Vec<usize> = (0..k).filter(|&i| fields[i].1 == StructuredSourceType::NatWord).collect();
    let advance = match advance {
        Some(advance) => advance,
        None if nat_fields.is_empty() => "",
        None => return unsupported("a Nat field needs the step's advance theorem"),
    };

    let name = |part: &str| format!("{prefix}_{part}");
    let reg = |g: Gpr| g.heather_name();
    let (t, s1r, s2r) = (p.scratch[0], p.scratch[1], p.scratch[2]);
    let typed = |part: &str, function: &str, inputs: &[(u64, Gpr)], temps: &[Gpr], output: (u64, Gpr)| {
        generate_elaborated_typed_x86(elaborator, &name(part), &format!("function_ir_loop_x86::{function}"),
            &inputs.iter().copied().collect(), temps, &[output].into_iter().collect())
    };
    let mut guard_temps = vec![p.flag, p.step, p.byte];
    guard_temps.extend(&p.scratch);
    let guard = typed("guard", "loop_guard", &[(0, p.cursor), (1, p.length), (2, p.budget)], &guard_temps, (3, p.flag))?;
    let address = typed("address", "loop_address", &[(0, p.base), (1, p.cursor)], &[p.byte], (2, p.byte))?;
    let load = ByteLoad { destination: p.byte, base: p.byte };
    let mut placements: x86::Placements = [(0, p.needle), (2, p.byte)].into_iter().collect();
    for (i, leaf) in leaves.iter().enumerate() { placements.insert(*leaf, p.fields[i]); }
    // The discriminator goes last when it reads no field (a folding step's
    // collapses to a constant), so the field pieces may borrow its register;
    // otherwise first, before any field is written back.
    let discriminator_reads_fields = cert::narrow_structured_region(&body.region, &[outputs[k]]).inputs().iter().any(|port| leaves.contains(&port.id));
    let mut field_temps = p.scratch.clone();
    if !discriminator_reads_fields { field_temps.push(p.step); }
    let step_temps: Vec<Gpr> = std::iter::once(p.step).chain(p.scratch.iter().copied()).collect();
    let discriminator_piece = FieldPiece { prefix: name("discriminator"), port: outputs[k].id, inputs: &placements, temporaries: &step_temps, consumable: &[], output: p.step };
    // Each field into its own register: an input it reads last, or else one
    // more register it may write.
    let homes: Vec<[Gpr; 1]> = p.fields.iter().map(|&home| [home]).collect();
    let temps_writing: Vec<Vec<Gpr>> = (0..k).map(|i| field_temps.iter().copied().chain(if reads[i].contains(&i) { None } else { Some(p.fields[i]) }).collect()).collect();
    let field_pieces = order.iter().map(|&i| FieldPiece { prefix: name(&format!("field_{}", fields[i].0)), port: outputs[i].id,
        inputs: &placements, temporaries: &temps_writing[i], consumable: if reads[i].contains(&i) { &homes[i] } else { &[] }, output: p.fields[i] });
    let pieces: Vec<FieldPiece> = if discriminator_reads_fields { std::iter::once(discriminator_piece).chain(field_pieces).collect() }
        else { field_pieces.chain(std::iter::once(discriminator_piece)).collect() };
    let (fields_text, emissions) = generate_elaborated_typed_fields_x86(elaborator, &name("fields"), &reflected.body_name, &pieces)?;
    // The cursor and the budget, in place.
    let in_place = |part: &str, function: &str, register: Gpr, temps: &[Gpr]| {
        generate_elaborated_typed_consuming_x86(elaborator, &name(part), &format!("function_ir_loop_x86::{function}"),
            &[(0, register)].into_iter().collect(), temps, &[register], &[(1, register)].into_iter().collect())
    };
    let next_cursor = in_place("next_cursor", "loop_next_cursor", p.cursor, &[t, s2r])?;
    let next_budget = in_place("next_budget", "loop_next_budget", p.budget, &[s1r, s2r])?;

    // The iteration's pure steps after the load, in order, by name; each is
    // one state further along.
    let (discriminator, field_emissions) = if discriminator_reads_fields { (&emissions[0], &emissions[1..]) } else { (&emissions[k], &emissions[..k]) };
    let mut steps: Vec<(String, AccessFragment)> = Vec::new();
    let discriminator_step = (discriminator.prefix.clone(), AccessFragment::structured(&discriminator.prefix, &discriminator.lowered));
    if discriminator_reads_fields { steps.push(discriminator_step.clone()); }
    for piece in field_emissions {
        steps.push((piece.prefix.clone(), AccessFragment::structured(&piece.prefix, &piece.lowered)));
    }
    if !discriminator_reads_fields { steps.push(discriminator_step); }
    for (part, emission) in [("next_cursor", &next_cursor), ("next_budget", &next_budget)] {
        steps.push((name(part), AccessFragment::structured(&name(part), &emission.lowered)));
    }
    // States: s0 at the head, s1 after the address, s2 after the load, then
    // s{3 + n} after pure step n.
    let fragments: Vec<AccessFragment> = [AccessFragment::structured(&name("address"), &address.lowered), AccessFragment::read(load)]
        .into_iter().chain(steps.iter().map(|(_, fragment)| fragment.clone())).collect();
    let last = fragments.len();
    let body_fragment = fragments.iter().rev().cloned().reduce(|tail, fragment| fragment.sequence(tail)).expect("fragments");
    let guard_fragment = AccessFragment::structured(&name("guard"), &guard.lowered);
    let (exit, _, back) = near_loop_edges(guard_fragment.bytes.len(), body_fragment.bytes.len()).map_err(SourceError::Unsupported)?;
    let looped = AccessFragment::looped(guard_fragment.clone(), p.flag, body_fragment.clone(), p.step).map_err(SourceError::Unsupported)?;

    let mut pieces_module = Module::default();
    pieces_module.raw("import x86_64_data_read; import x86_64;");
    pieces_module.raw(format!("fn {}() → ByteLoad {{ {} }}", name("load"), load.render()));
    for text in [&guard.text, &address.text, &fields_text] { pieces_module.raw(text.clone()); }
    for emission in [&next_cursor, &next_budget] { pieces_module.raw(emission.text.clone()); }
    pieces_module.raw(generate_readonly_loop_certificate(&name("loop"), &reflected));
    let pieces_text = stitch_imports(&pieces_module.render());
    let mut module = Module::default();
    module.raw(pieces_text.lines().take_while(|line| line.starts_with("import ")).collect::<Vec<_>>().join("\n"));
    module.raw(format!("import {prefix}_pieces; import function_ir_loop_trace; import x86_64_access_code; import x86_64_data_read; import x86_64_block; import list; import logic; import option;"));
    module.raw(looped.publish(prefix));
    let placement = name("placement");
    module.declaration(Declaration::function(&placement, HeatherExpr::name("LoopPlacement"), Block::expression(HeatherExpr::raw(format!(
        "LoopPlacement(base := {}, length := {}, needle := {}, cursor := {}, budget := {}, carry := {}, flag := {}, step := {})",
        reg(p.base), reg(p.length), reg(p.needle), reg(p.cursor), reg(p.budget), reg(p.fields[0]), reg(p.flag), reg(p.step))))));
    let body_code = name("body_code");
    module.declaration(Declaration::function(&body_code, HeatherExpr::name("AccessCode"), Block::expression(HeatherExpr::raw(body_fragment.code()))));
    // Where the state sits: each field in its register, a Nat as its word
    // and a Bool as its placed bit.
    let rep_name = name("rep");
    let field_rep = |i: usize, gprs: &str, state: &str| match fields[i].1 {
        StructuredSourceType::Boolean => format!("read_gpr({}, {gprs}) = loop_bit({})", reg(p.fields[i]), field_of(state, i)),
        _ => format!("LoopWord(64, read_gpr({}, {gprs}), {})", reg(p.fields[i]), field_of(state, i)),
    };
    let rep_body = conjunction(&(0..k).map(|i| field_rep(i, "gprs", "carry")).collect::<Vec<_>>());
    module.declaration(Declaration::function(&rep_name, HeatherExpr::raw("Type"), Block::expression(HeatherExpr::raw(rep_body)))
        .parameters(vec![Parameter::explicit("gprs", HeatherExpr::name("Gprs")), Parameter::explicit("carry", HeatherExpr::raw(&carry_type))]));
    // The invariant: every Nat field fits a word with the budget still to run.
    let invariant = name("fits");
    let fits_body = conjunction(&nat_fields.iter().map(|&i| format!("loop_fits(cursor, budget, {})", field_of("carry", i))).collect::<Vec<_>>());
    module.declaration(Declaration::function(&invariant, HeatherExpr::raw("Type"), Block::expression(HeatherExpr::raw(fits_body)))
        .parameters(vec![Parameter::explicit("cursor", HeatherExpr::name("Nat")), Parameter::explicit("budget", HeatherExpr::name("Nat")),
            Parameter::explicit("carry", HeatherExpr::raw(&carry_type))]));
    let region = format!("{}_region()", name("loop"));
    // The placement reads only the fields' registers: it moves to any
    // register file that agrees on them (docs/native-wc-design.md §4.8).
    let moves_kept: Vec<Parameter> = (0..k).map(|i| Parameter::explicit(&format!("kept_{}", fields[i].0),
        HeatherExpr::raw(format!("read_gpr({r}, after) = read_gpr({r}, before)", r = reg(p.fields[i]))))).collect();
    let moved = tuple(&(0..k).map(|i| {
        let motive = match fields[i].1 {
            StructuredSourceType::Boolean => format!("word = loop_bit({})", field_of("carry", i)),
            _ => format!("LoopWord(64, word, {})", field_of("carry", i)),
        };
        format!("j(sym(kept_{}), λ word _ => {motive}, {})", fields[i].0, component("placed", i, k))
    }).collect::<Vec<_>>());
    module.declaration(Declaration::theorem(name("rep_moves"), HeatherExpr::raw(format!("{rep_name}(after, carry)")),
        Block::expression(HeatherExpr::raw(moved))).parameters(
        [Parameter::explicit("before", HeatherExpr::name("Gprs")), Parameter::explicit("after", HeatherExpr::name("Gprs")),
            Parameter::explicit("carry", HeatherExpr::raw(&carry_type))].into_iter().chain(moves_kept)
            .chain(std::iter::once(Parameter::explicit("placed", HeatherExpr::raw(format!("{rep_name}(before, carry)"))))).collect::<Vec<_>>()));
    // The state folded over any input from one whose Nat fields are zero fits
    // a loop over the next `budget` bytes, each field having grown by at most
    // one per byte read.
    let room_fields: Vec<String> = nat_fields.iter().enumerate().map(|(j, &i)| {
        let (folded, initial, state) = (field_of(&format!("step_fold({region}, needle, seen, init)"), i), field_of("init", i), field_of("state", i));
        format!("loop_fits_from({folded}, {initial}, seen.len(), budget, \
            step_fold_measure({region}, λ (state: {carry_type}) => {state}, \
                λ needle cursor byte carry => {}, needle, seen)(init), {}, room)",
            component(&format!("{advance}()(needle, cursor, byte, carry)"), j, nat_fields.len()), component("zero", j, nat_fields.len()))
    }).collect();
    module.declaration(Declaration::theorem(name("room"), HeatherExpr::raw(format!("{invariant}(0, budget, step_fold({region}, needle, seen, init))")),
        Block::expression(HeatherExpr::raw(tuple(&room_fields)))).parameters(vec![
        Parameter::explicit("needle", HeatherExpr::raw("BitVec(8)")),
        Parameter::explicit("init", HeatherExpr::raw(&carry_type)),
        Parameter::explicit("zero", HeatherExpr::raw(conjunction(&nat_fields.iter().map(|&i| format!("{} = 0", field_of("init", i))).collect::<Vec<_>>()))),
        Parameter::explicit("seen", HeatherExpr::raw("List<BitVec(8)>")),
        Parameter::explicit("budget", HeatherExpr::name("Nat")),
        Parameter::explicit("room", HeatherExpr::raw("seen.len() + budget < nat::Nat::pow(2, 64)"))]));
    let guard_code = guard_fragment.code();

    // The guard: its typed result is loop_run's decision; nothing else moves.
    let (g, cw, lw, bw) = (name("guard"), format!("read_gpr({}, before.gprs)", reg(p.cursor)),
        format!("read_gpr({}, before.gprs)", reg(p.length)), format!("read_gpr({}, before.gprs)", reg(p.budget)));
    let kept = [p.base, p.length, p.needle, p.cursor, p.budget].map(|r| format!("{g}_preserves({}, before, trivial)", reg(r))).join(", ");
    let carry_kept = tuple(&(0..k).map(|i| {
        let motive = match fields[i].1 {
            StructuredSourceType::Boolean => format!("word = loop_bit({})", field_of("carry", i)),
            _ => format!("LoopWord(64, word, {})", field_of("carry", i)),
        };
        format!("j(sym({g}_preserves({}, before, trivial)), λ word _ => {motive}, {})", reg(p.fields[i]), component("head.carry_placed", i, k))
    }).collect::<Vec<_>>());
    module.declaration(Declaration::theorem(name("guard_step"),
        HeatherExpr::raw(format!("LoopGuardStep<M, {carry_type}>({placement}(), {rep_name}, access, buffer, needle, {guard_code})")),
        Block::expression(HeatherExpr::raw(format!("λ before cursor budget carry head => Exists({g}_after(before), ⟨refl, ⟨\
            trans({g}_typed_correct({cw}, {lw}, {bw}, before, refl, refl, refl), cong_fn<Bool, BitVec(64)>(loop_bit, \
            loop_guard_word({cw}, {lw}, {bw}, cursor, buffer.length, budget, head.cursor_placed, head.length_placed, head.budget_placed))), \
            loop_head_transport({placement}(), {rep_name}, access, buffer, needle, before, {g}_after(before), cursor, budget, carry, head, \
            {kept}, {carry_kept}, {g}_memory(before))⟩⟩)")))).generic("M").parameters(vec![
        Parameter::explicit("access", HeatherExpr::raw("ByteReadAccess<M>")),
        Parameter::explicit("buffer", HeatherExpr::name("ReadonlyBytes")),
        Parameter::explicit("needle", HeatherExpr::raw("BitVec(8)"))]));

    // One iteration.
    let a = name("address");
    let state = |i: usize| format!("s{i}");
    let kept_by = |r: Gpr, index: usize| -> String {
        let r = reg(r);
        match index {
            0 => format!("{a}_preserves({r}, s0, trivial)"),
            1 => format!("byte_load_preserves({}(), byte, s1, {r}, refl)", name("load")),
            i => format!("{}_preserves({r}, s{i}, trivial)", steps[i - 2].0),
        }
    };
    // read_gpr(r, s_to) = read_gpr(r, s_from).
    let chain = |r: Gpr, from: usize, to: usize| -> String {
        if from == to { return "refl".into(); }
        (from + 1..to).fold(kept_by(r, from), |inner, i| format!("trans({}, {inner})", kept_by(r, i)))
    };
    // `trans(first, second)`, leaving out an empty chain.
    let seq = |first: String, second: String| if first == "refl" { second } else { format!("trans({first}, {second})") };
    // The state before pure step n is s{2 + n}, after it s{3 + n}.
    let before_step = |n: usize| 2 + n;
    let step_index = |part: &str| steps.iter().position(|(prefix, _)| prefix == part).expect("step");
    let head_field = |i: usize| component("head.carry_placed", i, k);
    let premise = |port: u64, entry: usize| -> String {
        if port == 0 { return format!("sym(trans({}, head.needle_placed))", chain(p.needle, 0, entry)); }
        if port == 2 { return format!("sym(trans({}, byte_load_result({}(), byte, s1)))", chain(p.byte, 2, entry), name("load")); }
        let i = leaves.iter().position(|leaf| *leaf == port).expect("a field port");
        match fields[i].1 {
            StructuredSourceType::Boolean => format!("sym(trans({}, {}))", chain(p.fields[i], 0, entry), head_field(i)),
            _ => format!("trans(loop_nat_placed(read_gpr({r}, s0.gprs), {f}, {h}), sym({c}))", r = reg(p.fields[i]), f = field_of("carry", i), h = head_field(i), c = chain(p.fields[i], 0, entry)),
        }
    };
    let mut lets: Vec<(String, String)> = vec![
        ("s1".into(), format!("{a}_after(s0)")),
        ("address_word".into(), format!("loop_placed_address({b}, s1, buffer, cursor, read_gpr({base}, s0.gprs), read_gpr({cur}, s0.gprs), \
            head.base_placed, head.cursor_placed, head.inside, bounded, {a}_typed_correct(read_gpr({base}, s0.gprs), read_gpr({cur}, s0.gprs), s0, refl, refl))",
            b = reg(p.byte), base = reg(p.base), cur = reg(p.cursor))),
        ("present1".into(), format!("j(sym({a}_memory(s0)), λ m _ => access.read(m, read_gpr({b}, s1.gprs)) = Some(byte), \
            loop_read_address(access, s0.memory, buffer, cursor, read_gpr({b}, s1.gprs), byte, head.memory_agrees, address_word, present))", b = reg(p.byte))),
        ("canonical".into(), format!("loop_address_canonical(buffer, cursor, read_gpr({}, s1.gprs), address_word, open, low)", reg(p.byte))),
        ("s2".into(), format!("byte_load_after({}(), byte, s1)", name("load"))),
    ];
    for (n, (part, _)) in steps.iter().enumerate() { lets.push((state(3 + n), format!("{part}_after({})", state(before_step(n))))); }
    let end = 2 + steps.len();
    let s_end = state(end);
    lets.push(("step".into(), format!("{region}.body(needle, cursor, byte, carry)")));
    lets.push(("next".into(), "loop_step_payload(step)".into()));
    // Each field's new word: its piece's result, kept since.
    let mut field_words = vec![String::new(); k];
    for (n, &i) in order.iter().enumerate() {
        let piece = &field_emissions[n];
        let at = step_index(&piece.prefix);
        let entry = before_step(at);
        let placed = piece.inputs.iter().map(|port| premise(port.id, entry)).collect::<Vec<_>>().join(", ");
        let result = format!("{}_typed_correct(needle, cursor, byte, carry, {}{}{placed})", piece.prefix, state(entry), if placed.is_empty() { "" } else { ", " });
        field_words[i] = seq(chain(p.fields[i], before_step(at) + 1, end), result);
        lets.push((format!("word_{}", fields[i].0), field_words[i].clone()));
    }
    let d_at = step_index(&discriminator.prefix);
    let d_placed = discriminator.inputs.iter().map(|port| premise(port.id, before_step(d_at))).collect::<Vec<_>>().join(", ");
    lets.push(("step_reg".into(), seq(chain(p.step, before_step(d_at) + 1, end), format!("{}_typed_correct(needle, cursor, byte, carry, {}{}{d_placed})",
        discriminator.prefix, state(before_step(d_at)), if d_placed.is_empty() { "" } else { ", " }))));
    let (nc, nb) = (step_index(&name("next_cursor")), step_index(&name("next_budget")));
    lets.push(("value".into(), "λ (word: BitVec(64)) => word.toNat()".into()));
    lets.push(("cursor_word".into(), format!("trans(cong_fn(value, {}), head.cursor_placed)", chain(p.cursor, 0, before_step(nc)))));
    lets.push(("length_word".into(), format!("trans(cong_fn(value, {}), head.length_placed)", chain(p.length, 0, before_step(nc)))));
    let kept_cursor = seq(chain(p.cursor, before_step(nc) + 1, end), format!("{}_typed_correct(read_gpr({cur}, {n}.gprs), {n}, refl)", steps[nc].0,
        cur = reg(p.cursor), n = state(before_step(nc))));
    lets.push(("cursor_next".into(), format!("trans(cong_fn(value, {kept_cursor}), \
        loop_cursor_increment(read_gpr({cur}, {n}.gprs), read_gpr({len}, {n}.gprs), cursor, buffer.length, cursor_word, length_word, open))",
        n = state(before_step(nc)), cur = reg(p.cursor), len = reg(p.length))));
    lets.push(("budget_word".into(), format!("trans(cong_fn(value, {}), head.budget_placed)", chain(p.budget, 0, before_step(nb)))));
    let kept_budget = seq(chain(p.budget, before_step(nb) + 1, end), format!("{}_typed_correct(read_gpr({bud}, {n}.gprs), {n}, refl)", steps[nb].0,
        bud = reg(p.budget), n = state(before_step(nb))));
    lets.push(("budget_next".into(), format!("trans(cong_fn(value, {kept_budget}), loop_budget_decrement(read_gpr({bud}, {n}.gprs), rest, budget_word))",
        n = state(before_step(nb)), bud = reg(p.budget))));
    // after.memory = before.memory, the last step outermost; the load keeps
    // memory by definition.
    let memory = (0..steps.len()).fold(format!("{a}_memory(s0)"), |inner, n| format!("trans({}_memory({}), {inner})", steps[n].0, state(before_step(n))));
    lets.push(("memory".into(), memory));
    // Every Nat field fits after the step: the client's advance, field by field.
    let adv = format!("{advance}()(needle, cursor, byte, carry)");
    let invs: Vec<String> = nat_fields.iter().enumerate().map(|(j, &i)| format!("loop_fits_step(cursor, rest, {}, {}, {}, {})",
        field_of("carry", i), field_of("next", i), component("inv", j, nat_fields.len()), component(&adv, j, nat_fields.len()))).collect();
    lets.push((format!("next_invariant: {invariant}(Succ(cursor), rest, next)"), tuple(&invs)));
    let carry_next = tuple(&(0..k).map(|i| match fields[i].1 {
        StructuredSourceType::Boolean => format!("word_{}", fields[i].0),
        _ => {
            let j = nat_fields.iter().position(|&n| n == i).expect("a Nat field");
            format!("loop_nat_word(read_gpr({}, {s_end}.gprs), {n}, word_{f}, loop_fits_bound(Succ(cursor), rest, {n}, {}))",
                reg(p.fields[i]), component("next_invariant", j, nat_fields.len()), f = fields[i].0, n = field_of("next", i))
        }
    }).collect::<Vec<_>>());
    lets.push((format!("carry_next: {rep_name}({s_end}.gprs, next)"), carry_next));
    lets.push(("next_head".into(), format!("loop_head_advance({placement}(), {rep_name}, access, buffer, needle, s0, {s_end}, cursor, Succ(rest), rest, carry, \
        next, head, {}, {}, {}, cursor_next, budget_next, carry_next, open, memory)", chain(p.base, 0, end), chain(p.length, 0, end), chain(p.needle, 0, end))));
    // The execution follows the fragments' right-nested sequence.
    let codes: Vec<String> = fragments.iter().map(|f| f.code().to_string()).collect();
    let rest_code = |from: usize| -> String {
        (from..last).rev().map(|i| codes[i].clone()).reduce(|tail, code| format!("AccessSequence({code}, {tail})")).expect("code")
    };
    let exec = |i: usize| if i == 1 { "Exists(byte, ByteLoadStep(canonical := canonical, present := present1, execution := refl))".to_string() } else { "refl".into() };
    let execution = (0..last - 1).rev().fold(exec(last - 1), |inner, i| format!("access_sequence(access, {}, {}, {}, {}, {s_end}, {}, {inner})",
        codes[i], rest_code(i + 1), state(i), state(i + 1), exec(i)));
    lets.push(("execution".into(), execution));
    let lets = lets.iter().map(|(name, value)| format!("let {name} = {value};")).collect::<Vec<_>>().join("\n        ");
    module.declaration(Declaration::theorem(name("body_step"),
        HeatherExpr::raw(format!("LoopBodyStep<M, {carry_type}>({placement}(), {rep_name}, {invariant}, access, buffer, needle, {region}, {body_code}())")),
        Block::expression(HeatherExpr::raw(format!("λ s0 cursor rest carry byte head inv open present => {{\n        {lets}\n        \
            Exists({s_end}, ⟨execution, loop_stepped({placement}(), {rep_name}, {invariant}, access, buffer, needle, s0, {s_end}, cursor, rest, \
            {}, step, step_reg, next_head, next_invariant)⟩)\n    }}", chain(p.flag, 0, end))))).generic("M").parameters(vec![
        Parameter::explicit("access", HeatherExpr::raw("ByteReadAccess<M>")),
        Parameter::explicit("buffer", HeatherExpr::name("ReadonlyBytes")),
        Parameter::explicit("needle", HeatherExpr::raw("BitVec(8)")),
        Parameter::explicit("bounded", HeatherExpr::raw("LoopAddressBound(64, buffer)")),
        Parameter::explicit("low", HeatherExpr::raw("buffer.base + buffer.length <= nat::Nat::pow(2, 47)"))]));

    // The whole loop, stated against the named source function.
    let exit = format!("@bitvec::BitVec::ofNat(32, {exit})");
    let back = format!("@bitvec::BitVec::ofNat(32, {back})");
    let observed = |outcome: &str| format!("LoopObserved<M, {carry_type}>({placement}(), {rep_name}, {outcome})");
    module.declaration(Declaration::theorem(name("native"),
        HeatherExpr::raw(format!("Exists<MachineState<M>>(λ after => AccessArtifact<M>(access, {prefix}_code(), {prefix}_bytes(), before, after) ∧ \
            {})", observed(&format!("after, {}(buffer, needle, budget, cursor, carry)", reflected.source_name)))),
        Block::expression(HeatherExpr::raw(format!("{{
        let traced = loop_trace({placement}(), {rep_name}, {invariant}, access, buffer, needle, {region}, \
            {guard_code}, {body_code}(), {exit}, {back}, {prefix}_guard_step(access, buffer, needle), \
            {prefix}_body_step(access, buffer, needle, bounded, low), budget, before, cursor, carry, head, fits, readable);
        Exists(traced.witness, ⟨AccessArtifact(encoding := {prefix}_encoding(), layout := {prefix}_layout(), execution := traced.proof.left), \
            j({}_source_agreement(buffer, needle, budget, cursor, carry), λ outcome _ => {}, traced.proof.right)⟩)
    }}", name("loop"), observed("traced.witness, outcome"))))).generic("M").parameters(vec![
        Parameter::explicit("access", HeatherExpr::raw("ByteReadAccess<M>")),
        Parameter::explicit("before", HeatherExpr::raw("MachineState<M>")),
        Parameter::explicit("buffer", HeatherExpr::name("ReadonlyBytes")),
        Parameter::explicit("needle", HeatherExpr::raw("BitVec(8)")),
        Parameter::explicit("budget", HeatherExpr::name("Nat")),
        Parameter::explicit("cursor", HeatherExpr::name("Nat")),
        Parameter::explicit("carry", HeatherExpr::raw(&carry_type)),
        Parameter::explicit("bounded", HeatherExpr::raw("LoopAddressBound(64, buffer)")),
        Parameter::explicit("low", HeatherExpr::raw("buffer.base + buffer.length <= nat::Nat::pow(2, 47)")),
        Parameter::explicit("head", HeatherExpr::raw(format!("LoopHead<M, {carry_type}>({placement}(), {rep_name}, access, buffer, needle, before, cursor, budget, carry)"))),
        Parameter::explicit("readable", HeatherExpr::raw(format!("LoopReadable(budget, {region}, buffer, needle, cursor, carry)"))),
        Parameter::explicit("fits", HeatherExpr::raw(format!("{invariant}(cursor, budget, carry)")))]));
    Ok(LoopX86Emission { bytes: looped.bytes, pieces: pieces_text, text: stitch_imports(&module.render()) })
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
