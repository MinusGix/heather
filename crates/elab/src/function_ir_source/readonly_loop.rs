//! Recognition of the bounded source combinator. This is a semantic interface,
//! not native body selection: the body retains its resolved checked identity.
use super::*;

/// A carry: one Nat or Bool, or a record of scalar fields, each in a register
/// of its own (docs/native-wc-design.md §4).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LoopCarry { Natural, Boolean, Record(super::structured::StructuredSourceRecord) }
impl LoopCarry {
    pub fn name(&self) -> String {
        match self { Self::Natural => "Nat".into(), Self::Boolean => "Bool".into(), Self::Record(record) => record.type_name.clone() }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReflectedReadonlyLoop {
    pub source_name: String,
    pub body_name: String,
    pub carry: LoopCarry,
}

/// Five explicit source parameters, in order: buffer, needle, budget, cursor,
/// carry. The sixth combinator argument must be a resolved global definition.
/// Neither positional rebinding nor source spelling can choose another op.
pub fn reflect_elaborated_readonly_loop(elaborator: &Elaborator, source: &str)
    -> Result<ReflectedReadonlyLoop, SourceError>
{
    let caller = elaborator.global_abs(source).ok_or_else(|| SourceError::Unsupported("unknown loop source".into()))?;
    let source_name = elaborator.global_qualified_name_at(caller).ok_or_else(|| SourceError::Unsupported("loop source has no qualified identity".into()))?;
    let (ty, term) = elaborator.global_body(&source_name).ok_or_else(|| SourceError::Unsupported("loop source must be transparent".into()))?;
    if pi_arity(&ty) != 5 { return unsupported("bounded loop source requires buffer, needle, budget, cursor, carry"); }
    let mut term = &*term;
    for _ in 0..5 {
        let Term::Lam { body, .. } = term else { return unsupported("missing loop source parameter"); };
        term = body;
    }
    let (head, args) = application_spine(term);
    let resolved = |term: &Term| match term {
        Term::GlobalTm { var, .. } => caller.checked_sub(1 + var.0 as usize),
        _ => None,
    };
    let operation = elaborator.global_abs("function_ir_loop::bounded_readonly")
        .ok_or_else(|| SourceError::Unsupported("bounded loop semantics are not loaded".into()))?;
    if resolved(head) != Some(operation) || args.len() != 7 {
        return unsupported("source must directly call the resolved bounded_readonly combinator");
    }
    for (position, argument) in args[1..6].iter().enumerate() {
        if !matches!(argument, Term::Var(LocalVar(index)) if *index as usize == 4 - position) {
            return unsupported("bounded loop source arguments must preserve the declared bindings");
        }
    }
    let boolean_code = elaborator.lookup_inductive("bool::Bool")
        .and_then(|ind| elaborator.types.gdefs().abs_for(&crate::gendefs::GenDef::TyCode(ind.tag)))
        .map(|abs| *abs as usize);
    let carry = match args[0] {
        Term::TmNat => LoopCarry::Natural,
        term if boolean_code.is_some() && resolved(term) == boolean_code => LoopCarry::Boolean,
        term => match super::structured::record_code_at(elaborator, caller, term)? {
            Some(record) => LoopCarry::Record(record),
            None => return unsupported("bounded loop reflection supports Nat, Bool, or record carries"),
        },
    };
    let body = resolved(args[6]).ok_or_else(|| SourceError::Unsupported("loop body must be a resolved global function".into()))?;
    let body_name = elaborator.global_qualified_name_at(body).ok_or_else(|| SourceError::Unsupported("loop body has no qualified identity".into()))?;
    if elaborator.global_body(&body_name).is_none() { return unsupported("loop body must be a transparent definition"); }
    Ok(ReflectedReadonlyLoop { source_name, body_name, carry })
}

/// What a program for the read profile says about itself
/// (`function_ir_loop`'s `CountProgram` and `FieldsProgram`,
/// docs/native-architecture-review.md R6).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReadProgramKind {
    /// One count: the process exits with it or prints it.
    Count,
    /// A record state whose first three fields are printed.
    Fields,
}

/// A program read off its bundle's type: the step, the byte it is given, and
/// what its printed counts mean, each by its resolved name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReflectedReadProgram {
    pub name: String,
    pub kind: ReadProgramKind,
    pub step: String,
    pub needle: u8,
    pub specs: Vec<String>,
    /// The state: a count, or the `FieldsProgram`'s record.
    pub carry: LoopCarry,
}

/// The record a `FieldsProgram`'s step folds: its fourth parameter's type.
pub fn reflect_step_record(elaborator: &Elaborator, step: &str) -> Result<super::structured::StructuredSourceRecord, SourceError> {
    let reflected = super::structured::reflect_elaborated_structured(elaborator, step)?;
    reflected.signature.get(3).cloned().flatten()
        .ok_or_else(|| SourceError::Unsupported("a FieldsProgram's state must be a record of scalar fields".into()))
}

/// A global byte constant, `BitVec::ofNat(n)` through functions of no
/// arguments, by name.
pub fn byte_constant(elaborator: &Elaborator, name: &str) -> Option<u8> {
    let at = elaborator.global_abs(name)?;
    let (_, body) = elaborator.global_body_at(at)?;
    byte_value(elaborator, &body, at)
}

// A closed byte: `BitVec::ofNat(n)`, through functions of no arguments.
fn byte_value(elaborator: &Elaborator, term: &Term, at: usize) -> Option<u8> {
    let (head, args) = application_spine(term);
    let abs = absolute(head, at)?;
    if Some(abs) == elaborator.global_abs("bitvec::BitVec::ofNat") {
        return match args.last() { Some(Term::NatLit(value)) => value.as_u64().and_then(|n| u8::try_from(n).ok()), _ => None };
    }
    if !args.is_empty() { return None; }
    let (_, body) = elaborator.global_body_at(abs)?;
    byte_value(elaborator, &body, abs)
}

fn absolute(term: &Term, caller: usize) -> Option<usize> {
    match term { Term::GlobalTm { var, .. } => caller.checked_sub(1 + var.0 as usize), _ => None }
}

/// The kernel checks both the typed body interface and equality with the actual
/// source over open buffer, byte, counters, and carry. Rebinding either source
/// or body in a stale descriptor cannot turn into an accepted certificate.
pub fn generate_readonly_loop_certificate(prefix: &str, reflected: &ReflectedReadonlyLoop) -> String {
    let mut module = Module::default();
    module.raw("import function_ir_loop;\nimport bitvec;\nimport bool;\nimport nat;");
    let mut imports = std::collections::BTreeSet::new();
    for name in [&reflected.source_name, &reflected.body_name] {
        if let Some((owner, _)) = name.rsplit_once("::") { imports.insert(owner); }
    }
    for owner in imports { module.raw(format!("import {owner};")); }
    let carry = reflected.carry.name();
    let region = format!("{prefix}_region");
    module.declaration(Declaration::function(&region, HeatherExpr::raw(format!("ReadonlyLoop<{carry}>")),
        Block::expression(HeatherExpr::raw(format!("ReadonlyLoop<{carry}>({})", reflected.body_name)))));
    let parameters = || [
        ("buffer", "ReadonlyBytes"), ("needle", "BitVec(8)"), ("budget", "Nat"),
        ("cursor", "Nat"), ("carry", carry.as_str()),
    ].into_iter().map(|(name, ty)| Parameter::explicit(name, HeatherExpr::name(ty))).collect::<Vec<_>>();
    module.declaration(Declaration::theorem(format!("{prefix}_source_agreement"),
        HeatherExpr::raw(format!("loop_run(budget, {region}(), buffer, needle, cursor, carry) = {}(buffer, needle, budget, cursor, carry)", reflected.source_name)),
        Block::expression(HeatherExpr::name("refl"))).parameters(parameters()));
    let mut artifact_parameters = parameters();
    artifact_parameters.push(Parameter::explicit("bounds", HeatherExpr::raw("LoopBounds(buffer, cursor)")));
    artifact_parameters.push(Parameter::explicit("access", HeatherExpr::raw(format!("LoopReadable(budget, {region}(), buffer, needle, cursor, carry)"))));
    module.declaration(Declaration::function(format!("{prefix}_artifact"),
        HeatherExpr::raw(format!("ReadonlyLoopArtifact<{carry}>({region}(), buffer, needle, budget, cursor, carry, {}(buffer, needle, budget, cursor, carry))", reflected.source_name)),
        Block::expression(HeatherExpr::raw(format!("ReadonlyLoopArtifact(source_agreement := {prefix}_source_agreement(buffer, needle, budget, cursor, carry), cursor_bound := bounds, selected_reads := access)"))))
        .parameters(artifact_parameters));
    module.render()
}
