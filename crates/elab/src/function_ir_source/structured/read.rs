//! Successful byte-read prefix feeding an ordinary typed source certificate.
use super::*;
use super::publication::{encode, vector};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReadX86Emission {
    pub load: x86::ByteLoad,
    pub body: x86::LoweredStructured,
    pub bytes: Vec<u8>,
    pub text: String,
}

/// Load one BitVec(8) source argument from a supplied address register, then
/// execute the shared typed body. Access is required at this selected read
/// boundary; selecting bounds branches and complete loops is a separate layer.
pub fn generate_elaborated_read_x86(
    elaborator: &Elaborator, prefix: &str, source_name: &str,
    byte_parameter: u64, address: Gpr, inputs: &x86::Placements,
    temporaries: &[Gpr], outputs: &x86::Placements,
) -> Result<ReadX86Emission, SourceError> {
    let reflected = reflect_elaborated_structured(elaborator, source_name)?;
    let byte_type = usize::try_from(byte_parameter).ok().and_then(|id| reflected.parameters.get(id));
    if byte_type != Some(&StructuredSourceType::Word(8)) {
        return unsupported("byte read requires a BitVec(8) source parameter");
    }
    let body_prefix = format!("{prefix}_body");
    let body = generate_elaborated_typed_x86(elaborator, &body_prefix, source_name, inputs, temporaries, outputs)?;
    let load = x86::ByteLoad { destination: inputs[&byte_parameter], base: address };
    let mut published = load.bytes();
    published.extend(x86::encode_structured(&body.lowered));
    let mut module = Module::default();
    module.raw("import x86_64_data_read; import option;");
    module.raw(body.text);
    let declaration = |m: &mut Module, name: String, machine: bool, ps: Vec<Parameter>, ty: String, value: String, theorem: bool| {
        let value = Block::expression(HeatherExpr::raw(value));
        let d = if theorem { Declaration::theorem(name, HeatherExpr::raw(ty), value) }
            else { Declaration::function(name, HeatherExpr::raw(ty), value) };
        let d = d.parameters(ps);
        m.declaration(if machine { d.generic("M") } else { d });
    };
    declaration(&mut module, format!("{prefix}_load"), false, vec![], "ByteLoad".into(), load.render(), false);
    let bytes = load.bytes().iter().map(|b| format!("@bitvec::BitVec::ofNat(8, {b})")).collect::<Vec<_>>().join(", ");
    declaration(&mut module, format!("{prefix}_load_bytes"), false, vec![], "List<BitVec(8)>".into(), format!("[{bytes}]"), false);
    declaration(&mut module, format!("{prefix}_load_decodes"), false, vec![], format!("ByteLoadDecodes({prefix}_load_bytes(), {prefix}_load())"), "refl".into(), true);
    declaration(&mut module, format!("{prefix}_bytes"), false, vec![], "List<BitVec(8)>".into(), format!("{prefix}_load_bytes() ++ {body_prefix}_bytes()"), false);
    let literal = published.iter().map(|b| format!("@bitvec::BitVec::ofNat(8, {b})")).collect::<Vec<_>>().join(", ");
    declaration(&mut module, format!("{prefix}_published_bytes"), false, vec![], "List<BitVec(8)>".into(), format!("[{literal}]"), false);
    declaration(&mut module, format!("{prefix}_published_agrees"), false, vec![], format!("{prefix}_published_bytes() = {prefix}_bytes()"), "refl".into(), true);
    let mut public: Vec<_> = reflected.parameters.iter().enumerate().map(|(id, ty)| Parameter::explicit(format!("arg{id}"), HeatherExpr::raw(ty.name()))).collect();
    public.push(Parameter::explicit("access", HeatherExpr::raw("ByteReadAccess<M>")));
    public.push(Parameter::explicit("before", HeatherExpr::raw("MachineState<M>")));
    let byte = format!("arg{byte_parameter}");
    let entry = format!("byte_load_after({prefix}_load(), {byte}, before)");
    let arguments = (0..reflected.parameters.len()).map(|id| format!("arg{id}")).collect::<Vec<_>>().join(", ");
    let mut placements = Vec::new();
    for port in reflected.region.inputs() {
        let id = port.id;
        let register = inputs[&id].heather_name();
        if id == byte_parameter {
            placements.push(format!("sym(byte_load_result({prefix}_load(), {byte}, before))"));
        } else {
            let name = format!("placed_{id}");
            public.push(Parameter::explicit(&name, HeatherExpr::raw(format!("{} = read_gpr({register}, before.gprs)", encode(port.width, &vector(reflected.parameters[id as usize], &format!("arg{id}")))))));
            placements.push(format!("trans({name}, sym(byte_load_preserves({prefix}_load(), {byte}, before, {register}, refl)))"));
        }
    }
    public.push(Parameter::explicit("canonical", HeatherExpr::raw(format!("bitvec::BitVec::drop_low(47, 17, read_gpr({}, before.gprs)) = @bitvec::BitVec::zero(17)", address.heather_name()))));
    public.push(Parameter::explicit("present", HeatherExpr::raw(format!("access.read(before.memory, read_gpr({}, before.gprs)) = Some({byte})", address.heather_name()))));
    let body_args = format!("{arguments}, {entry}, {}", placements.join(", "));
    for (i, port) in reflected.region.outputs().iter().enumerate() {
        let name = if i == 0 { prefix.to_string() } else { format!("{prefix}_output_{}", port.id) };
        let body_name = if i == 0 { body_prefix.clone() } else { format!("{body_prefix}_output_{}", port.id) };
        let observed = format!("{body_prefix}_observe_{}({}({arguments}))", port.id, reflected.source_name);
        let result = encode(port.width, &if port.width == 1 { format!("bitvec::BitVec::ofBool({observed})") } else { observed });
        let output = outputs[&port.id].heather_name();
        declaration(&mut module, format!("{name}_read_correct"), true, public.clone(),
            format!("read_gpr({output}, {body_prefix}_after({entry}).gprs) = {result}"),
            format!("{body_name}_typed_correct({body_args})"), true);
        declaration(&mut module, format!("{name}_read_artifact"), true, public.clone(),
            format!("ReadThenArtifact<M>(access, {prefix}_load(), {byte}, {body_prefix}_code(), {prefix}_published_bytes(), before, {output}, {result}, {body_prefix}_Protected)"),
            format!("read_then_artifact(access, {prefix}_load(), {byte}, {body_prefix}_code(), before, {output}, {result}, {body_prefix}_Protected, ByteLoadStep(canonical := canonical, present := present, execution := refl), {body_name}_typed_artifact({body_args}))"), true);
    }
    Ok(ReadX86Emission { load, body: body.lowered, bytes: published, text: module.render() })
}
