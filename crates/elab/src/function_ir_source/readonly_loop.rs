//! Recognition of the bounded source combinator. This is a semantic interface,
//! not native body selection: the body retains its resolved checked identity.
use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LoopCarry { Natural, Boolean }
impl LoopCarry {
    fn name(self) -> &'static str { match self { Self::Natural => "Nat", Self::Boolean => "Bool" } }
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
        _ => return unsupported("bounded loop reflection currently supports Nat or Bool carries"),
    };
    let body = resolved(args[6]).ok_or_else(|| SourceError::Unsupported("loop body must be a resolved global function".into()))?;
    let body_name = elaborator.global_qualified_name_at(body).ok_or_else(|| SourceError::Unsupported("loop body has no qualified identity".into()))?;
    if elaborator.global_body(&body_name).is_none() { return unsupported("loop body must be a transparent definition"); }
    Ok(ReflectedReadonlyLoop { source_name, body_name, carry })
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
        ("cursor", "Nat"), ("carry", carry),
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
