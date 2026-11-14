//! Type recovery for the surface well-founded lowering. Queries run in a
//! disposable elaborator; neither provisional signatures nor goals commit.
use crate::*;
use heather_syntax::{Block, Stmt};
use crate::declarations::Declarations;
use crate::module_pass::ModulePassMut;

/// Measure contexts' part of the elaborator.
pub(crate) struct MeasureContext<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for MeasureContext<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl MeasureContext<'_> {
    pub(crate) fn measure_local_evidence(
        &self, decl: &Decl, scope: &[measure::Binder], goal: &Ty, arithmetic: bool,
    ) -> Option<Expr> {
        let span = goal.span;
        let mut facts = Vec::new();
        // Nearest binding first. A candidate gets only its own dependencies
        // and the goal's, so an unrelated unspellable local cannot poison it.
        for (i, binder) in scope.iter().enumerate().rev() {
            if binder.ty.is_none() || scope[i + 1..].iter().any(|b| b.name == binder.name) { continue; }
            let proof = Expr { kind: ExprKind::Var(binder.name.clone()), span };
            let Some(selected) = measure::select_scope(scope, goal, Some(&proof)) else { continue; };
            let mut head = decl.clone();
            head.params = selected.iter().map(|b| measure_param(&b.name, b.ty.as_ref().unwrap(), span)).collect();
            let mut query = self.0.clone();
            query.attempt.prepare();
            query.attempt.goal_arena.configure(0, 0);
            query.refresh_delta_psi();
            let Ok(cx) = Declarations(&query).decl_head_cx(&head) else { continue; };
            let Ok((expected, level)) = query.elab_ty(&cx, goal) else { continue; };
            let Ok((_, actual, _)) = query.elab_infer(&cx, &proof) else { continue; };
            if query.conv_types(&cx, &actual, &expected, &level) { return Some(proof); }
            // A refinement's own `__dec_eq` is the rewrite's: obligations
            // are stated at the refined measure already, and the companions
            // bind those equations to `refl` at the leaf.
            if arithmetic && facts.len() < 16 && !binder.name.starts_with("__dec_eq")
                && measure::arithmetic_fact(binder.ty.as_ref().unwrap(), goal, scope)
            { facts.push(proof); }
        }
        if facts.is_empty() { return None; }
        // Mention each selected fact in the proof expression so the ordinary
        // lifter captures it. The existing Omega closer combines the facts.
        let stmts = facts.into_iter().enumerate().map(|(i, expr)| {
            let mut name = format!("__dec_fact_{i}");
            while scope.iter().any(|b| b.name == name) { name.push('_'); }
            Stmt::Let { name, ty: None, expr, span, opaque: false }
        }).collect();
        let body = Block { stmts, result: Box::new(Expr { kind: ExprKind::Var(measure::CLOSER.into()), span }),
            ons: Vec::new(), span };
        let proof = Expr { kind: ExprKind::Block(Box::new(body.clone())), span };
        let selected = measure::select_scope(scope, goal, Some(&proof))?;
        let mut trial = decl.clone();
        trial.name = format!("{}#local_evidence", decl.name);
        trial.kind = DeclKind::Theorem;
        trial.decreases = None;
        trial.params = selected.iter().map(|b| measure_param(&b.name, b.ty.as_ref().unwrap(), span)).collect();
        trial.result = goal.clone();
        trial.body = body;
        let mut query = self.0.clone();
        ModulePassMut(&mut query).serially(|q| q.elab_decl_one(&trial, None)).ok()?;
        Some(proof)
    }

    /// A disposable elaborator and the walk's local telescope in it: the type
    /// parameters, the members' neutral signatures, then every binder in
    /// scope. `None` where a binder has no type (it cannot be left out: its
    /// name could then resolve to an unrelated global).
    fn measure_query(&self, decl: &Decl, signatures: &[(String, Ty)], scope: &[measure::Binder]) -> Option<(Elaborator, Cx)> {
        let mut query = self.0.clone();
        query.attempt.prepare();
        query.attempt.goal_arena.configure(0, 0);
        query.refresh_delta_psi();
        // Start with type parameters only, then neutral local signatures.
        // They supply result types, never proofs or global definitions.
        let mut head = decl.clone();
        head.params.clear();
        let mut cx = Declarations(&query).decl_head_cx(&head).ok()?;
        for (name, surface) in signatures {
            let (ty, level) = query.elab_ty(&cx, surface).ok()?;
            cx.push_skel(name.clone(), ty, level, skel_of_ty(surface));
        }
        for binder in scope {
            // Unknown locals cannot be omitted: that could resolve their
            // names to unrelated globals. Decline the query conservatively.
            let surface = binder.ty.as_ref()?;
            let (ty, level) = query.elab_ty(&cx, surface).ok()?;
            cx.push_skel(binder.name.clone(), ty.clone(), level, skel_of_ty(surface));
            if let Type::Ty(level) = ty {
                cx.tyvars.push(TyVar { name: binder.name.clone(),
                    ty: Type::El { level: level.clone(), tm: Rc::new(Term::Var(LocalVar(0))) },
                    level, depth: cx.names.len() });
            }
        }
        Some((query, cx))
    }

    /// The proofs `call` leaves to a default that searches its context, each
    /// with the goal it is found at, as a surface type over the walk's
    /// telescope. Read off an elaboration of the call that records its
    /// defaults, then checked: the call elaborates again with a local of
    /// each goal's type given by name.
    pub(crate) fn measure_default_goals(
        &self, decl: &Decl, signatures: &[(String, Ty)],
        scope: &[measure::Binder], call: &Expr,
    ) -> Option<Vec<measure::FoundGoal>> {
        let stripped = heather_syntax::without_decrease_labels(call);
        let (query, cx) = self.measure_query(decl, signatures, scope)?;
        *query.pass.default_goals.borrow_mut() = Some(Vec::new());
        query.elab_infer(&cx, &stripped).ok()?;
        let recorded = query.pass.default_goals.borrow_mut().take()?;
        // An argument's own defaults are elaborated before the call's, so
        // the call's are the last run of distinct parameters of one owner.
        let owner = recorded.last()?.owner.clone();
        let mut own: Vec<&crate::defaults::DefaultGoal> = Vec::new();
        for goal in recorded.iter().rev() {
            if goal.owner != owner || own.iter().any(|g| g.index == goal.index) { break; }
            own.push(goal);
        }
        own.reverse();
        let mut found = Vec::new();
        for goal in own {
            if !crate::defaults::is_context_search(&goal.default) { continue; }
            let wrapper = format!("fn __measure_type() -> {} {{ 0 }}", goal.goal.as_ref()?);
            let mut file = heather_syntax::parse_file(&wrapper).ok()?;
            let Item::Decl(parsed) = file.items.pop()? else { return None; };
            let mut ty = parsed.result;
            ty.span = call.span;
            found.push(measure::FoundGoal { name: goal.name.clone(), goal: ty, default: goal.default.clone() });
        }
        if found.is_empty() { return None; }
        // The check: with each goal assumed, the call takes the assumptions.
        let (check, mut cx) = self.measure_query(decl, signatures, scope)?;
        let mut given = stripped.clone();
        for (i, f) in found.iter().enumerate() {
            let local = format!("__found_given_{i}");
            let (ty, level) = check.elab_ty(&cx, &f.goal).ok()?;
            cx.push_skel(local.clone(), ty, level, skel_of_ty(&f.goal));
            let arg = heather_syntax::NamedArg { name: f.name.clone(), name_span: call.span,
                expr: Expr { kind: ExprKind::Var(local), span: call.span }, span: call.span };
            match &mut given.kind {
                ExprKind::App { named, .. } | ExprKind::Dot { named, .. } => named.push(arg),
                _ => return None,
            }
        }
        check.elab_infer(&cx, &given).ok()?;
        Some(found)
    }

    pub(crate) fn infer_measure_local(
        &self, decl: &Decl, signatures: &[(String, Ty)],
        scope: &[measure::Binder], expr: &Expr,
    ) -> Option<Ty> {
        let stripped = heather_syntax::without_decrease_labels(expr);
        let expr = &stripped;
        let (query, cx) = self.measure_query(decl, signatures, scope)?;
        let (term, ty, level) = query.elab_infer(&cx, expr).ok()?;
        let mut surface = if let Some(source) = query.spell_type_source(&cx, &ty) {
            let wrapper = format!("fn __measure_type() -> {source} {{ 0 }}");
            let mut file = heather_syntax::parse_file(&wrapper).ok()?;
            let Item::Decl(parsed) = file.items.pop()? else { return None; };
            parsed.result
        } else {
            // A provisional signature already has an exact surface result
            // telescope. Instantiate it before attempting structural inversion
            // of a dependent record whose generated code may be unavailable.
            measure::signature_result(signatures, expr)
                .or_else(|| MeasureContext(&query).measure_decl_result(&cx, &term))
                .or_else(|| MeasureContext(&query).measure_field_result(&cx, scope, expr))?
        };
        surface.span = expr.span;
        let (roundtrip, _) = query.elab_ty(&cx, &surface).ok()?;
        if !query.conv_types(&cx, &ty, &roundtrip, &level) { return None; }
        Some(surface)
    }
    // A projection may have no printable kernel spelling (for example an
    // inline dependent record). Its stored field signature is another checked
    // candidate, instantiated from the receiver's known surface annotation.
    fn measure_field_result(&self, cx: &Cx, scope: &[measure::Binder], expr: &Expr) -> Option<Ty> {
        let ExprKind::Dot { recv, name, args: None, .. } = &expr.kind else { return None; };
        let ExprKind::Var(local) = &recv.kind else { return None; };
        let surface = scope.iter().rev().find(|b| &b.name == local)?.ty.as_ref()?;
        let (_, ty, _) = self.elab_infer(cx, recv).ok()?;
        let ind = self.record_of_at(cx, &ty, expr.span)?;
        let (type_args, values) = match &surface.kind {
            TyKind::Named { args, .. } => (args.as_slice(), &[][..]),
            TyKind::OfExpr(e) => {
                let ExprKind::App { head, args, .. } = &e.kind else { return None; };
                let types = match &head.kind { ExprKind::TyApp { args, .. } => args.as_slice(),
                    ExprKind::Var(_) => &[][..], _ => return None };
                (types, args.as_slice())
            }
            _ => return None,
        };
        if type_args.len() != ind.params.len() || values.len() != ind.valparams.len() { return None; }
        let fields = &ind.ctors.first()?.fields;
        let index = fields.iter().position(|(field, _)| field.as_ref() == Some(name))?;
        let mut result = fields[index].1.clone();
        for (parameter, arg) in ind.params.iter().zip(type_args) {
            let code = Expr { kind: ExprKind::TyLit(Box::new(arg.clone())), span: expr.span };
            result = measure::subst_surface_ty(&result, parameter, &code);
        }
        for ((parameter, _), arg) in ind.valparams.iter().zip(values) {
            result = measure::subst_surface_ty(&result, parameter, arg);
        }
        for (field, _) in &fields[..index] {
            if let Some(field) = field {
                let projection = Expr { kind: ExprKind::Dot { recv: recv.clone(), name: field.clone(),
                    tyargs: Vec::new(), args: None, named: Vec::new() }, span: expr.span };
                result = measure::subst_surface_ty(&result, field, &projection);
            }
        }
        Some(result)
    }

    fn measure_decl_result(&self, cx: &Cx, term: &Term) -> Option<Ty> {
        let mut args = Vec::new();
        let mut head = term;
        while let Some((fun, arg)) = crate::spelling::app_of(head) {
            args.push(arg);
            head = fun;
        }
        args.reverse();
        let Term::GlobalTm { var, .. } = head else { return None; };
        let abs = self.global_abs_of(*var)?;
        // Surface reflection is indexed by written name. This remains only
        // a candidate: the inferred type comparison above is authoritative.
        let name = self.global_name_at(abs)?;
        let decl = self.names.surface_decl(&name)?;
        let names: Vec<_> = decl.tyvars.iter().map(|v| &v.name)
            .chain(decl.params.iter().map(|p| &p.name)).collect();
        if names.len() != args.len() { return None; }
        let mut result = decl.result.clone();
        for (name, arg) in names.into_iter().zip(args) {
            let source = self.spell_term_source(cx, arg)?;
            let mut file = heather_syntax::parse_file(&format!("fn __arg() -> Nat {{ {source} }}")).ok()?;
            let Item::Decl(parsed) = file.items.pop()? else { return None; };
            result = measure::subst_surface_ty(&result, name, &parsed.body.result);
        }
        Some(result)
    }
}

fn measure_param(name: &str, ty: &Ty, span: Span) -> heather_syntax::Param {
    heather_syntax::Param { name: name.into(), ty: ty.clone(), implicit: false,
        is_self: false, solver: None, default: None, origin: heather_syntax::ParamOrigin::Written,
        symbol: None, span }
}
