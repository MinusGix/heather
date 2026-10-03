//! A stream filter's step as one certified straight-line piece
//! (docs/native-stream-filter-design.md §5): the generator side of
//! `filter_step_piece::StepPiece`. From the state's registers and the byte in
//! RAX, the piece leaves the emit's flag in RBX and its byte in RDX, then the
//! next state in the same registers.
//!
//! Every output is an ordinary typed certificate from the shared generators,
//! computed alone into its own register. The two emit outputs go first, while
//! the state is intact; the state's fields follow in place, each straight
//! into its home register, in an order where no field overwrites a register
//! a later one reads (as the loop generator updates a record state). This
//! module composes the pieces' code as one `StructuredCode` and proves the
//! contract from their typed results.
//!
//! A step is a global whose result is `Filtered<C>` (reflected as one source
//! with the emit's two ports after the state's), `counting(g)` (the fields
//! are `g`'s, the emit the library's constant nothing) or `mapping(f)` (no
//! fields; the flag the library's constant, the byte `f`'s).
use super::*;
use super::loop_native::stitch_imports;
use super::structured::{FieldPiece, StructuredSourceRecord};

/// What a step is, by the resolved names of its parts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FilterStep {
    /// `step: C → BitVec(8) → Filtered<C>`, a global of its own.
    Step(String),
    /// `stream_filter::counting<C>(g)`, `g: C → BitVec(8) → C`.
    Counting(String),
    /// `stream_filter::mapping(f)`, `f: BitVec(8) → BitVec(8)`, over `Stateless`.
    Mapping(String),
}

/// Read a step off a global: the step function itself, or a definition whose
/// body is one (by its resolved name), `counting<C>(g)` or `mapping(f)` with
/// `g` and `f` resolved globals.
pub fn reflect_filter_step(elaborator: &Elaborator, name: &str) -> Result<FilterStep, SourceError> {
    let caller = elaborator.global_abs(name).ok_or_else(|| SourceError::Unsupported(format!("unknown filter step `{name}`")))?;
    let qualified = elaborator.global_qualified_name_at(caller).ok_or_else(|| SourceError::Unsupported("the filter step has no qualified identity".into()))?;
    let (_, body) = elaborator.global_body(&qualified).ok_or_else(|| SourceError::Unsupported("the filter step must be transparent".into()))?;
    let resolved = |term: &Term| match term { Term::GlobalTm { var, .. } => caller.checked_sub(1 + var.0 as usize), _ => None };
    let named = |abs: usize| elaborator.global_qualified_name_at(abs).ok_or_else(|| SourceError::Unsupported("a filter step's part has no qualified identity".into()));
    let mut term = &*body;
    while let Term::Lam { body, .. } = term { term = body; }
    if let Some(alias) = resolved(term) { return reflect_filter_step(elaborator, &named(alias)?); }
    let (head, args) = application_spine(term);
    let counting = elaborator.global_abs("stream_filter::counting");
    let mapping = elaborator.global_abs("stream_filter::mapping");
    match resolved(head) {
        Some(head) if Some(head) == counting && args.len() == 2 => {
            let g = resolved(args[1]).ok_or_else(|| SourceError::Unsupported("counting's step must be a resolved global function".into()))?;
            Ok(FilterStep::Counting(named(g)?))
        }
        Some(head) if Some(head) == mapping && args.len() == 1 => {
            let f = resolved(args[0]).ok_or_else(|| SourceError::Unsupported("mapping's byte map must be a resolved global function".into()))?;
            Ok(FilterStep::Mapping(named(f)?))
        }
        _ => Ok(FilterStep::Step(qualified)),
    }
}

/// `pieces` is the per-output typed certificates, to be elaborated as module
/// `{prefix}_pieces`; `text` is the step piece (its code, the state's
/// placement, the contract), which imports it and `elf64_read_pieces`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FilterStepEmission {
    pub bytes: Vec<u8>,
    pub pieces: String,
    pub text: String,
}

/// The read profile's state registers, in field order (elf64_read_pieces'
/// `state_init_block` zeroes them).
const STATE: [Gpr; 4] = [Gpr::R13, Gpr::R14, Gpr::R15, Gpr::R8];
/// filter_step_piece's `filter_step_scratch()`.
const SCRATCH: [Gpr; 11] = [Gpr::Rax, Gpr::Rdx, Gpr::Rbx, Gpr::R9, Gpr::R10, Gpr::R11, Gpr::Rbp, Gpr::R13, Gpr::R14, Gpr::R15, Gpr::R8];
const ALL: [Gpr; 16] = [Gpr::Rax, Gpr::Rcx, Gpr::Rdx, Gpr::Rbx, Gpr::Rsp, Gpr::Rbp, Gpr::Rsi, Gpr::Rdi, Gpr::R8, Gpr::R9, Gpr::R10, Gpr::R11, Gpr::R12, Gpr::R13, Gpr::R14, Gpr::R15];

/// What a piece's source parameter is at the step: the state (one field of
/// it, or all of a scalar state), or the byte.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Meaning { Field(usize), Byte }

/// One output's certificate: its prefix, its source's arguments as the
/// contract spells them, the source ports it reads and what each is.
struct Piece {
    prefix: String,
    arguments: String,
    inputs: Vec<(Port, Meaning)>,
    lowered: x86::LoweredStructured,
    output: Gpr,
    /// A copy into place (`emit_copy`): the holding register it reads.
    copies: Option<Gpr>,
}

/// The step's state: a record's fields, or a scalar as one field that is the
/// state itself.
struct State {
    type_name: String,
    constructor: Option<String>,
    fields: Vec<(String, StructuredSourceType)>,
}
impl State {
    fn of(record: Option<&StructuredSourceRecord>, scalar: StructuredSourceType) -> Self {
        match record {
            Some(record) => State { type_name: record.type_name.clone(), constructor: Some(record.constructor.clone()), fields: record.fields.clone() },
            None => State { type_name: scalar.name(), constructor: None, fields: vec![("value".into(), scalar)] },
        }
    }
    fn field(&self, value: &str, i: usize) -> String {
        if self.constructor.is_some() { format!("{value}.{}", self.fields[i].0) } else { value.to_string() }
    }
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

/// The step piece, generated and composed. `init` is the state the process
/// starts from, whose fields must be zeros (`StateInitialised`); without
/// one, `{prefix}_init()` is the zero state.
pub fn generate_elaborated_filter_step_x86(elaborator: &Elaborator, prefix: &str, step: &FilterStep, init: Option<&str>)
    -> Result<FilterStepEmission, SourceError>
{
    let name = |part: &str| format!("{prefix}_{part}");
    let reg = |g: Gpr| g.heather_name();
    // The state, and the source whose ports compute its fields.
    let (state, fields_source) = match step {
        FilterStep::Step(source) => {
            let reflected = reflect_elaborated_structured(elaborator, source)?;
            if !reflected.filtered { return unsupported(&format!("`{source}` is not a filter step: its result is not stream_filter::Filtered")); }
            (State::of(reflected.record.as_ref(), reflected.result), Some(reflected))
        }
        FilterStep::Counting(g) => {
            let reflected = reflect_elaborated_structured(elaborator, g)?;
            if reflected.filtered || reflected.choice.is_some() { return unsupported("counting's step returns the next state"); }
            (State::of(reflected.record.as_ref(), reflected.result), Some(reflected))
        }
        FilterStep::Mapping(_) => (State { type_name: "stream_filter::Stateless".into(), constructor: Some("stream_filter::Stateless".into()), fields: Vec::new() }, None),
    };
    let k = state.fields.len();
    if k > STATE.len() { return unsupported("a filter's state has at most four fields, one per state register"); }
    if let Some(reflected) = &fields_source {
        // The step is over (state, byte).
        let byte = reflected.leaves.iter().zip(&reflected.parameters).all(|((parameter, _), ty)| *parameter != 1 || *ty == StructuredSourceType::Word(8));
        if reflected.signature.len() != 2 || !byte { return unsupported("a filter's step takes its state, then a BitVec(8)"); }
    }
    let ty = state.type_name.clone();
    let step_term = match step {
        FilterStep::Step(source) => fields_source.as_ref().map(|r| r.source_name.clone()).unwrap_or_else(|| source.clone()),
        FilterStep::Counting(_) => format!("stream_filter::counting<{ty}>({})", fields_source.as_ref().expect("counting reflects its step").source_name),
        FilterStep::Mapping(f) => format!("stream_filter::mapping({f})"),
    };

    // Each port of the fields' source: what it is, and where it sits.
    let meaning_of = |reflected: &ReflectedStructuredFunction, port: u64| -> Option<Meaning> {
        let (parameter, field) = reflected.leaves.get(port as usize)?;
        match (*parameter, field) {
            (1, _) => Some(Meaning::Byte),
            (0, Some(field)) => state.fields.iter().position(|(f, _)| f == field).map(Meaning::Field),
            (0, None) if state.constructor.is_none() => Some(Meaning::Field(0)),
            _ => None,
        }
    };
    let home = |meaning: Meaning| match meaning { Meaning::Byte => Gpr::Rax, Meaning::Field(i) => STATE[i] };
    let placements = |reflected: &ReflectedStructuredFunction| -> x86::Placements {
        reflected.region.inputs().iter().filter_map(|port| meaning_of(reflected, port.id).map(|meaning| (port.id, home(meaning)))).collect()
    };

    // An emit computed from the state goes first, while the state is
    // intact, straight into place (the flag in RBX, the byte in RDX); the
    // fields after it compare in the pool's byte registers (R9B–R11B, BPL).
    // An emit that reads no state (counting's constant nothing, mapping's
    // flag and byte map) goes after the fields, also straight into place.
    let (field_ports, flag_port, byte_port): (Vec<Port>, Option<Port>, Option<Port>) = match &fields_source {
        Some(reflected) => {
            let outputs = reflected.region.outputs().to_vec();
            let filtered = reflected.filtered;
            (outputs[..k].to_vec(), filtered.then(|| outputs[k]), filtered.then(|| outputs[k + 1]))
        }
        None => (Vec::new(), None, None),
    };
    // Which state fields each field output reads.
    let reads: Vec<Vec<usize>> = field_ports.iter().map(|port| {
        let reflected = fields_source.as_ref().expect("fields have a source");
        cert::narrow_structured_region(&reflected.region, &[*port]).inputs().iter()
            .filter_map(|input| match meaning_of(reflected, input.id) { Some(Meaning::Field(i)) => Some(i), _ => None }).collect()
    }).collect();
    // Fields that read each other in a cycle can't all be written in place:
    // one of them is computed first into a holding register too, while every
    // field is intact, and copied home with the emit. The rest are written in
    // place, in an order where none overwrites what a later one reads.
    let mut held: Vec<usize> = Vec::new();
    let order = loop {
        let rest: Vec<usize> = (0..k).filter(|i| !held.contains(i)).collect();
        let among: Vec<Vec<usize>> = rest.iter().map(|&i| reads[i].iter().filter_map(|f| rest.iter().position(|r| r == f)).collect()).collect();
        match super::loop_native::write_order(&among) {
            Ok(order) => break order.into_iter().map(|j| rest[j]).collect::<Vec<_>>(),
            Err(error) => {
                // The field the most others read.
                let Some(&most) = rest.iter().max_by_key(|&&i| (rest.iter().filter(|&&j| j != i && reads[j].contains(&i)).count(), std::cmp::Reverse(i))) else { return Err(error) };
                held.push(most);
            }
        }
    };
    let pool = [Gpr::R9, Gpr::R10, Gpr::R11, Gpr::Rbp];
    if held.len() > pool.len() { return unsupported("the step's outputs need more holding registers than the piece has"); }
    let field_holder = |i: usize| held.iter().position(|&h| h == i).map(|n| pool[n]);
    // What a field's piece may use: the pool less what is held past it, and
    // RBX and RDX unless an emit computed first already sits there.
    let emits_first = flag_port.is_some();
    let free = pool[held.len()..].iter().copied().chain((!emits_first).then_some([Gpr::Rbx, Gpr::Rdx]).into_iter().flatten()).collect::<Vec<_>>();
    let all_temps: Vec<Gpr> = pool.iter().copied().chain([Gpr::Rbx, Gpr::Rdx]).collect();

    let mut texts: Vec<String> = Vec::new();
    let mut pieces: Vec<Piece> = Vec::new();
    if let Some(reflected) = &fields_source {
        let inputs = placements(reflected);
        // A held field into its holding register; any other into its own
        // register, an input it reads last, or else one more register it may
        // write.
        let homes: Vec<[Gpr; 1]> = (0..k).map(|i| [STATE[i]]).collect();
        let temps_writing: Vec<Vec<Gpr>> = (0..k).map(|i| free.iter().copied().chain(match field_holder(i) {
            Some(holding) => Some(holding),
            None => (!reads[i].contains(&i)).then_some(STATE[i]),
        }).collect()).collect();
        let flag_temps = all_temps.clone();
        let byte_temps: Vec<Gpr> = all_temps.iter().copied().filter(|r| *r != Gpr::Rbx).collect();
        let mut requested: Vec<FieldPiece> = Vec::new();
        if let (Some(flag), Some(byte)) = (flag_port, byte_port) {
            requested.push(FieldPiece { prefix: name("flag"), port: flag.id, inputs: &inputs, temporaries: &flag_temps, consumable: &[], output: Gpr::Rbx });
            requested.push(FieldPiece { prefix: name("byte"), port: byte.id, inputs: &inputs, temporaries: &byte_temps, consumable: &[], output: Gpr::Rdx });
        }
        for &i in held.iter().chain(&order) {
            let in_place = field_holder(i).is_none() && reads[i].contains(&i);
            requested.push(FieldPiece { prefix: name(&format!("field_{}", state.fields[i].0)), port: field_ports[i].id, inputs: &inputs,
                temporaries: &temps_writing[i], consumable: if in_place { &homes[i] } else { &[] }, output: field_holder(i).unwrap_or(STATE[i]) });
        }
        let (text, emissions) = generate_elaborated_typed_fields_x86(elaborator, &name("outputs"), &reflected.source_name, &requested)?;
        texts.push(text);
        for (emission, request) in emissions.into_iter().zip(&requested) {
            let inputs = emission.inputs.iter().map(|port| (*port, meaning_of(reflected, port.id).expect("a placed input"))).collect();
            pieces.push(Piece { prefix: emission.prefix, arguments: "s, b".into(), inputs, lowered: emission.lowered, output: request.output, copies: None });
        }
    }
    // A piece of one result from a source of its own, of at most one
    // parameter: a constant, the byte map over the byte in RAX, or a copy of
    // a held field home.
    let mut whole = |part: &str, source: &str, input: Option<Gpr>, temps: &[Gpr], output: Gpr, copies: bool| -> Result<(), SourceError> {
        let reflected = reflect_elaborated_structured(elaborator, source)?;
        let [port] = reflected.region.outputs() else { return unsupported("an emit piece has one result") };
        let placed: x86::Placements = reflected.region.inputs().iter().filter_map(|port| input.map(|register| (port.id, register))).collect();
        let emission = generate_elaborated_typed_x86(elaborator, &name(part), source, &placed, temps, &x86::Placements::from([(port.id, output)]))?;
        let (arguments, inputs, copies) = match (input, copies) {
            (Some(from), true) => (String::new(), Vec::new(), Some(from)),
            (Some(_), false) => ("b".to_string(), reflected.region.inputs().iter().map(|port| (*port, Meaning::Byte)).collect(), None),
            (None, _) => (String::new(), Vec::new(), None),
        };
        pieces.push(Piece { prefix: name(part), arguments, inputs, lowered: emission.lowered.clone(), output, copies });
        texts.push(emission.text);
        Ok(())
    };
    for &i in &held {
        whole(&format!("field_{}_copy", state.fields[i].0), "filter_step_piece::emit_copy", field_holder(i), &[STATE[i]], STATE[i], true)?;
    }
    match step {
        FilterStep::Step(_) => {}
        FilterStep::Counting(_) => {
            whole("flag", "filter_step_piece::emits_never", None, &[Gpr::Rbx], Gpr::Rbx, false)?;
            whole("byte", "filter_step_piece::emitted_nothing", None, &[Gpr::Rdx], Gpr::Rdx, false)?;
        }
        FilterStep::Mapping(f) => {
            let reflected = reflect_elaborated_structured(elaborator, f)?;
            if reflected.parameters != [StructuredSourceType::Word(8)] || reflected.result != StructuredSourceType::Word(8) || reflected.choice.is_some() || reflected.record.is_some() {
                return unsupported("mapping's byte map is BitVec(8) → BitVec(8)");
            }
            whole("byte", f, Some(Gpr::Rax), &all_temps, Gpr::Rdx, false)?;
            whole("flag", "filter_step_piece::emits_always", None, &[Gpr::Rbx], Gpr::Rbx, false)?;
        }
    }
    // Everything a piece writes is the contract's scratch, so every other
    // register follows by the pieces' frames.
    for piece in &pieces {
        if let Some(register) = piece.lowered.clobbered.iter().find(|register| !SCRATCH.contains(register)) {
            return unsupported(&format!("piece {} writes {}, outside the filter step's scratch", piece.prefix, register.heather_name()));
        }
    }
    let n = pieces.len();
    let bytes: Vec<u8> = pieces.iter().flat_map(|piece| x86::encode_structured(&piece.lowered)).collect();

    let mut pieces_module = Module::default();
    for text in &texts { pieces_module.raw(text.clone()); }
    let pieces_text = stitch_imports(&pieces_module.render());

    let mut module = Module::default();
    // The modules of the state's type and of the step's parts.
    let parts = match step { FilterStep::Mapping(f) => f.clone(), _ => fields_source.as_ref().expect("a step's fields are reflected").source_name.clone() };
    let mut owners: Vec<String> = Vec::new();
    for name in [&state.type_name, &parts] {
        if let Some((owner, _)) = name.rsplit_once("::") { if !owners.iter().any(|o| o == owner) { owners.push(owner.to_string()); } }
    }
    let owner_imports: String = owners.iter().map(|owner| format!(" import {owner};")).collect();
    module.raw(format!("import {prefix}_pieces; import filter_step_piece; import stream_filter; import elf64_read_pieces; import function_ir_loop; \
        import function_ir_loop_trace; import x86_64_structured_block; import x86_64; import x86_64_block; import bitvec; import bitvec_nat; \
        import bool; import list; import logic; import nat; import option;{owner_imports}"));

    // The code: the pieces in order, right-nested, and each suffix's code.
    let code = |j: usize| format!("{}_code()", pieces[j].prefix);
    let suffix = |from: usize| -> String {
        (from..n).rev().map(code).reduce(|tail, code| format!("CodeSequence({code}, {tail})")).expect("an emit has its pieces")
    };
    let states: Vec<String> = (0..=n).map(|j| (0..j).fold("before".to_string(), |state, i| format!("{}_after({state})", pieces[i].prefix))).collect();
    module.raw(format!("fn {}() → StructuredCode {{ {} }}", name("code"), suffix(0)));
    module.raw(format!("fn {}() → List<BitVec(8)> {{ structured_bytes({}()) }}", name("bytes"), name("code")));
    // The state the pieces reach, one after another: the code's own run.
    module.raw(format!("fn {}<M>(before: MachineState<M>) → MachineState<M> {{ {} }}", name("after"), states[n]));
    module.raw(format!("theorem {}(): StructuredLayout({}()) {{ {} }}", name("layout"), name("code"),
        tuple(&pieces.iter().map(|piece| format!("{}_layout()", piece.prefix)).collect::<Vec<_>>())));
    // Each piece decodes where the ones before it end, spelled as the
    // sequence's own `StructuredDecodes` spells it.
    let starts: Vec<String> = (0..n).map(|j| (0..j).fold("start".to_string(), |start, i| format!("next_rip({start}, structured_bytes({}).len())", code(i)))).collect();
    module.raw(format!("theorem {}(start: BitVec(64)): StructuredDecodes({}(), start) {{ {} }}", name("decodes"), name("code"),
        tuple(&(0..n).map(|j| format!("{}_decodes({})", pieces[j].prefix, starts[j])).collect::<Vec<_>>())));
    let mut rip = format!("{}_rip({})", pieces[n - 1].prefix, states[n - 1]);
    for j in (0..n - 1).rev() {
        rip = format!("structured_sequence_rip<M>({}, {}, {}, {}_rip({}), {rip})", code(j), suffix(j + 1), states[j], pieces[j].prefix, states[j]);
    }
    module.raw(format!("theorem {}<M>(before: MachineState<M>): {}(before).rip = next_rip(before.rip, structured_bytes({}()).len()) {{ {rip} }}",
        name("rip"), name("after"), name("code")));
    let memory = (1..n).fold(format!("{}_memory(before)", pieces[0].prefix), |inner, j| format!("trans({}_memory({}), {inner})", pieces[j].prefix, states[j]));
    module.raw(format!("theorem {}<M>(before: MachineState<M>): {}(before).memory = before.memory {{ {memory} }}", name("memory"), name("after")));
    let length: usize = pieces.iter().map(|piece| piece.lowered.byte_length).sum();
    let mut lengths = format!("{}_byte_length()", pieces[n - 1].prefix);
    let mut lit = format!("{}_lit()", pieces[n - 1].prefix);
    let mut bytes_are = format!("{}_bytes_are()", pieces[n - 1].prefix);
    let mut tail_length = pieces[n - 1].lowered.byte_length.to_string();
    for j in (0..n - 1).rev() {
        let piece = &pieces[j];
        lengths = format!("structured_sequence_length({}, {}, {}, {tail_length}, {}_byte_length(), {lengths})", code(j), suffix(j + 1), piece.lowered.byte_length, piece.prefix);
        tail_length = format!("{} + ({tail_length})", piece.lowered.byte_length);
        bytes_are = format!("structured_sequence_bytes({}, {}, {}_lit(), {lit}, {}_bytes_are(), {bytes_are})", code(j), suffix(j + 1), piece.prefix, piece.prefix);
        lit = format!("{}_lit() ++ ({lit})", piece.prefix);
    }
    // The length is stated at a literal from the pieces' own lemmas, never by
    // evaluating the encoding.
    module.raw(format!("theorem {}(): {}().len() = {length} {{ {lengths} }}", name("byte_length"), name("bytes")));
    module.raw(format!("fn {}() → List<BitVec(8)> {{ {lit} }}", name("lit")));
    module.raw(format!("theorem {}(): {}() = {}() {{ {bytes_are} }}", name("bytes_are"), name("bytes"), name("lit")));
    // read_gpr(r, s_to) = read_gpr(r, s_from), through the pieces between.
    let chain = |r: Gpr, from: usize, to: usize| -> String {
        if from >= to { return "refl".into(); }
        (from + 1..to).fold(format!("{}_preserves({}, {}, trivial)", pieces[from].prefix, reg(r), states[from]),
            |inner, j| format!("trans({}_preserves({}, {}, trivial), {inner})", pieces[j].prefix, reg(r), states[j]))
    };
    let arms: Vec<String> = ALL.iter().map(|&r| if SCRATCH.contains(&r) { format!("{} => kept ⊢ false_elim(kept)", reg(r)) }
        else { format!("{} => _ ⊢ {}", reg(r), chain(r, 0, n)) }).collect();
    module.raw(format!("theorem {}<M>(register: Gpr, before: MachineState<M>): Kept(filter_step_scratch(), register) → \
        read_gpr(register, {}(before).gprs) = read_gpr(register, before.gprs) {{ match register {{ {} }} }}", name("preserves"), name("after"), arms.join(", ")));

    // Where the state sits: each field in its register, a Nat as its word, a
    // Bool as its placed bit and a bitvector zero-extended.
    let placed = |i: usize, word: &str, value: &str| match state.fields[i].1 {
        StructuredSourceType::NatWord => format!("LoopWord(64, {word}, {value})"),
        StructuredSourceType::Boolean => format!("{word} = loop_bit({value})"),
        StructuredSourceType::Word(64) => format!("{word} = {value}"),
        StructuredSourceType::Word(w) => format!("{word} = @bitvec::BitVec::zero_extend({w}, {}, {value})", 64 - w),
        _ => unreachable!("record fields are scalars"),
    };
    let rep = name("rep");
    module.raw(format!("fn {rep}(gprs: Gprs, s: {ty}) → Type {{ {} }}", conjunction(&(0..k).map(|i|
        placed(i, &format!("read_gpr({}, gprs)", reg(STATE[i])), &state.field("s", i))).collect::<Vec<_>>())));
    // It reads only its registers, and init's zeros place the zero state.
    let moved = tuple(&(0..k).map(|i| format!("j(sym({}), λ word _ => {}, {})", component("kept", i, STATE.len()),
        placed(i, "word", &state.field("carry", i)), component("placed", i, k))).collect::<Vec<_>>());
    module.raw(format!("theorem {}(): StateFramed({rep}) {{ λ before after carry kept placed => {moved} }}", name("framed")));
    let init = match init {
        Some(init) => init.to_string(),
        None => {
            let zeros = state.fields.iter().map(|(_, kind)| match kind {
                StructuredSourceType::Boolean => "False".to_string(),
                StructuredSourceType::Word(w) => format!("@bitvec::BitVec::ofNat({w}, 0)"),
                _ => "0".to_string(),
            }).collect::<Vec<_>>().join(", ");
            let value = match &state.constructor { Some(ctor) => format!("{ctor}({zeros})"), None => zeros };
            module.raw(format!("fn {}() → {ty} {{ {value} }}", name("init")));
            format!("{}()", name("init"))
        }
    };
    module.raw(format!("theorem {}(): StateInitialised({rep}, {init}) {{ λ state => {} }}", name("initialised"), tuple(&vec!["refl".to_string(); k])));
    // The state's Nat fields, in order: what must fit a word.
    let nat_fields: Vec<usize> = (0..k).filter(|&i| state.fields[i].1 == StructuredSourceType::NatWord).collect();
    let counts = if nat_fields.is_empty() { "Nil".to_string() } else {
        format!("[{}]", nat_fields.iter().map(|&i| format!("λ (s: {ty}) => {}", state.field("s", i))).collect::<Vec<_>>().join(", "))
    };
    module.raw(format!("fn {}() → List<{ty} → Nat> {{ {counts} }}", name("counts")));

    // The contract. Piece `j` runs from state `j`; each reads its inputs
    // where the step's state and byte were placed, kept since.
    let premise = |meaning: Meaning, entry: usize| -> String {
        match meaning {
            Meaning::Byte => format!("sym(trans({}, rax))", chain(Gpr::Rax, 0, entry)),
            Meaning::Field(i) => {
                let held = component("held", i, k);
                let r = STATE[i];
                match state.fields[i].1 {
                    StructuredSourceType::NatWord => format!("trans(loop_nat_placed(read_gpr({}, before.gprs), {}, {held}), sym({}))", reg(r), state.field("s", i), chain(r, 0, entry)),
                    _ => format!("sym(trans({}, {held}))", chain(r, 0, entry)),
                }
            }
        }
    };
    let typed = |j: usize| -> String {
        let piece = &pieces[j];
        if let Some(from) = piece.copies { return format!("{}_typed_correct(read_gpr({}, {}.gprs), {}, refl)", piece.prefix, reg(from), states[j], states[j]); }
        let placed = piece.inputs.iter().map(|(_, meaning)| premise(*meaning, j)).collect::<Vec<_>>();
        let arguments = [piece.arguments.clone(), states[j].clone()].into_iter().filter(|a| !a.is_empty()).chain(placed).collect::<Vec<_>>().join(", ");
        format!("{}_typed_correct({arguments})", piece.prefix)
    };
    // What piece `j` wrote, in its register as state `to` has it.
    let kept = |j: usize, to: usize, fact: String| -> String {
        let chain = chain(pieces[j].output, j + 1, to);
        if chain == "refl" { fact } else { format!("trans({chain}, {fact})") }
    };
    // An output in its register at the end: through its copy when it was
    // held.
    let result = |part: &str| -> String {
        let j = pieces.iter().position(|piece| piece.prefix == name(part)).expect("a piece");
        match pieces.iter().position(|piece| piece.copies == Some(pieces[j].output)) {
            Some(c) => kept(c, n, format!("trans({}, {})", typed(c), kept(j, c, typed(j)))),
            None => kept(j, n, typed(j)),
        }
    };
    let next = format!("{step_term}(s, b).next");
    let fits_count = nat_fields.len() + 1;
    let next_held: Vec<String> = (0..k).map(|i| {
        let word = result(&format!("field_{}", state.fields[i].0));
        match state.fields[i].1 {
            StructuredSourceType::NatWord => {
                let j = nat_fields.iter().position(|&f| f == i).expect("a Nat field");
                format!("loop_nat_word(read_gpr({}, {}.gprs), {}, {word}, {})", reg(STATE[i]), states[n], state.field(&next, i), component("fit", j, fits_count))
            }
            _ => word,
        }
    }).collect();
    let fit = if nat_fields.is_empty() { String::new() } else {
        let bounds: Vec<String> = nat_fields.iter().map(|&i| format!("{} < Nat::pow(2, 64)", state.field(&next, i))).chain(["True".to_string()]).collect();
        format!("let fit: {} = fits;\n        ", conjunction(&bounds))
    };
    module.raw(format!("\
theorem {p}_step_piece<M>(): StepPiece<M, {ty}>({p}_code(), {rep}, {p}_counts(), {step_term}) {{
    λ before s b held rax fits => {{
        {fit}StepRan(after := {p}_after(before), execution := refl, layout := {p}_layout(), decoding := {p}_decodes(before.rip),
            next_held := {next_held},
            flag_is := {flag},
            byte_is := trans({byte}, emit_byte_word({step_term}(s, b).emit)),
            memory_preserved := {p}_memory(before), rip_correct := {p}_rip(before),
            registers_preserved := λ register kept => {p}_preserves(register, before, kept))
    }}
}}", p = prefix, next_held = tuple(&next_held), flag = result("flag"), byte = result("byte")));
    Ok(FilterStepEmission { bytes, pieces: pieces_text, text: stitch_imports(&module.render()) })
}
