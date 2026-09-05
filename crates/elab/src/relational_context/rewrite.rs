//! One structural contextual rewrite, consuming a named local relation proof.
//! Uses the same certificate planner as declaration-level generation. No new
//! elaborator syntax: the source driver replaces a selected theorem's hole.
use super::{
    Elaborator, Fixed, Operation, Outcome, Request, Walker, atom, bound, call, required_imports,
    slice, term, validate_request,
};
use heather_syntax::{DeclKind, Expr, ExprKind, Item, Ty, TyKind, parse_file};

#[derive(Clone, Debug)]
pub struct RewriteRequest {
    pub theorem: String,
    /// A parameter of the selected theorem, typed as R(x, y).
    pub proof: String,
    pub operations: Vec<Operation>,
    pub fixed: Vec<Fixed>,
}

#[derive(Clone, Debug)]
pub struct RewriteResult {
    /// Typed lambda recovered from the pair of goal endpoints.
    pub context: String,
    /// Differing positions replaced by the supplied proof's endpoint pair.
    pub occurrences: usize,
    pub outcome: Outcome,
}

fn relation(source: &str, ty: &Ty) -> Result<(String, Expr, Expr), String> {
    if let TyKind::OfExpr(e) = &ty.kind {
        if let ExprKind::App {
            head,
            args,
            named,
            explicit: false,
            goal_oriented: false,
        } = &e.kind
        {
            if args.len() == 2
                && named.is_empty()
                && matches!(head.kind, ExprKind::Var(_) | ExprKind::TyApp { .. })
            {
                return Ok((
                    term(source, head).render(),
                    args[0].clone(),
                    args[1].clone(),
                ));
            }
        }
    }
    Err("rewrite requires a written binary relation R(left, right); use RelId<T>(left, right) for identity in this prototype".into())
}

// Never compare binder-bearing or otherwise unsupported forms by their printed
// spelling. This first fragment needs no alpha-renaming or capture heuristics.
fn supported(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Var(_) | ExprKind::Num(_) => true,
        ExprKind::App {
            head,
            args,
            named,
            explicit: false,
            goal_oriented: false,
        } => {
            let named_head = match &head.kind {
                ExprKind::Var(_) | ExprKind::OpSymbol { .. } => true,
                ExprKind::TyApp { head, .. } => matches!(head.kind, ExprKind::Var(_)),
                _ => false,
            };
            named_head
                && named.is_empty()
                && (1..=2).contains(&args.len())
                && args.iter().all(supported)
        }
        _ => false,
    }
}

fn recover(
    source: &str,
    left: &Expr,
    right: &Expr,
    from: &str,
    to: &str,
    variable: &str,
    path: &str,
    occurrences: &mut usize,
) -> Result<Expr, String> {
    let l = term(source, left).render();
    let r = term(source, right).render();
    // Unchanged occurrences stay fixed, even when they contain a witness
    // endpoint. Equal witnesses therefore select a constant context.
    if l == r {
        return Ok(left.clone());
    }
    if l == from && r == to {
        *occurrences += 1;
        return Ok(Expr {
            kind: ExprKind::Var(variable.into()),
            span: left.span,
        });
    }
    if let (
        ExprKind::App {
            head: lh, args: la, ..
        },
        ExprKind::App {
            head: rh, args: ra, ..
        },
    ) = (&left.kind, &right.kind)
    {
        if term(source, lh).render() == term(source, rh).render() && la.len() == ra.len() {
            let mut result = left.clone();
            let mut args = Vec::new();
            for (i, (l, r)) in la.iter().zip(ra).enumerate() {
                args.push(recover(
                    source,
                    l,
                    r,
                    from,
                    to,
                    variable,
                    &format!("{path}, argument {}", i + 1),
                    occurrences,
                )?);
            }
            if let ExprKind::App {
                args: result_args, ..
            } = &mut result.kind
            {
                *result_args = args;
            }
            return Ok(result);
        }
    }
    Err(format!(
        "context mismatch at {path}: `{l}` versus `{r}`; supplied proof rewrites `{from}` to `{to}`"
    ))
}

fn fresh(source: &str, rules: &str, stem: &str) -> String {
    for n in 0.. {
        let name = format!("__context_{stem}_{n}");
        if !source.contains(&name) && !rules.contains(&name) {
            return name;
        }
    }
    unreachable!()
}

/// Replace one theorem's hole using its named relation-proof parameter. The
/// dependency environment must not already contain this source module. No
/// definitions are installed in it, including on a blocked or rejected rewrite.
/// Relations/rules match textually; witness endpoints must be value parameters
/// with the same written type. Contexts are binder-free unary/binary call trees.
pub fn rewrite(
    environment: &Elaborator,
    module: &str,
    source: &str,
    request: &RewriteRequest,
) -> Result<RewriteResult, String> {
    let file = parse_file(source).map_err(|e| format!("input parse error: {e:?}"))?;
    let decl = file
        .items
        .iter()
        .find_map(|item| match item {
            Item::Decl(d) if d.name == request.theorem => Some(d),
            _ => None,
        })
        .ok_or("requested theorem was not found")?;
    if !matches!(decl.kind, DeclKind::Theorem)
        || decl.is_meta
        || !decl.body.stmts.is_empty()
        || !decl.body.ons.is_empty()
        || !matches!(decl.body.result.kind, ExprKind::Hole(_))
        || decl
            .params
            .iter()
            .any(|p| p.implicit || p.solver.is_some() || p.symbol.is_some() || p.is_self)
        || decl.tyvars.iter().any(|p| p.level != 0)
    {
        return Err("rewrite requires a theorem with explicit parameters, Type<0> type parameters, and a single hole body".into());
    }
    let proof = decl
        .params
        .iter()
        .find(|p| p.name == request.proof)
        .ok_or("rewrite proof must name a theorem parameter")?;
    let (input, from, to) = relation(source, &proof.ty)?;
    let (output, left, right) = relation(source, &decl.result)?;
    let carrier = |e: &Expr| {
        if let ExprKind::Var(name) = &e.kind {
            decl.params
                .iter()
                .find(|p| &p.name == name)
                .map(|p| slice(source, p.ty.span))
        } else {
            None
        }
    };
    let input_type =
        carrier(&from).ok_or("proof endpoints must be named value parameters in this prototype")?;
    if carrier(&to) != Some(input_type) {
        return Err("proof endpoints must be parameters with the same written carrier type".into());
    }
    bound(&left, 0, &mut 256)?;
    bound(&right, 0, &mut 256)?;
    if !supported(&left) || !supported(&right) {
        return Err("rewrite contexts support only variables, numerals and binder-free unary/binary positional calls".into());
    }
    let rules = format!("{:?}{:?}", request.operations, request.fixed);
    let variable = fresh(source, &rules, "input");
    let certificate = fresh(source, &rules, "certificate");
    let goal_name = fresh(source, &rules, "goal");
    let mut occurrences = 0;
    let context = recover(
        source,
        &left,
        &right,
        &term(source, &from).render(),
        &term(source, &to).render(),
        &variable,
        "goal",
        &mut occurrences,
    )?;
    let context_text = format!(
        "λ ({variable}: {input_type}) => {}",
        term(source, &context).render()
    );
    let plan = Request {
        function: request.theorem.clone(),
        variable,
        input,
        output,
        generated_name: certificate.clone(),
        operations: request.operations.clone(),
        fixed: request.fixed.clone(),
    };
    validate_request(&plan)?;
    let generics = if decl.tyvars.is_empty() {
        String::new()
    } else {
        format!(
            "<{}>",
            decl.tyvars
                .iter()
                .map(|p| p.name.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        )
    };
    let parameters = decl
        .params
        .iter()
        .map(|p| format!("{}: {}", p.name, slice(source, p.ty.span)))
        .collect::<Vec<_>>()
        .join(", ");
    let imports = required_imports(&file);
    let prefix = format!("{imports}{}", &source[..decl.span.start]);
    let check = |candidate: &str| {
        environment
            .clone()
            .elab_module_source(module, candidate)
            .map_err(|e| e.render(candidate))
    };
    // Check the original assumptions and target's well-formedness without an
    // axiom or a placeholder proof. Later declarations wait for the final check.
    let goal = call(
        &plan.output,
        vec![term(source, &left), term(source, &right)],
    )
    .render();
    let probe = format!("fn {goal_name}{generics}({parameters}) -> Type {{ {goal} }}\n");
    check(&format!("{prefix}{probe}"))
        .map_err(|e| format!("rewrite signature did not check: {e}"))?;
    let mut walker = Walker {
        source,
        request: &plan,
        remaining: 256,
        obligations: Vec::new(),
    };
    let generated = walker.walk(&context, &plan.output, 0)?;
    if !walker.obligations.is_empty() {
        for (i, obligation) in walker.obligations.iter_mut().enumerate() {
            // Avoid helper collisions as well as collisions with the context binder.
            let name = fresh(source, &rules, &format!("obligation_{i}"));
            obligation.declaration = format!(
                "fn {name}{generics}({parameters}) -> Type {{\n    {}\n}}\n",
                obligation.goal
            );
            check(&format!("{prefix}{}", obligation.declaration))
                .map_err(|e| format!("rewrite obligation did not check: {e}"))?;
        }
        return Ok(RewriteResult {
            context: context_text,
            occurrences,
            outcome: Outcome::Blocked {
                obligations: walker.obligations,
            },
        });
    }
    let compatibility = call(
        "PreservesRelation",
        vec![atom(&plan.input), atom(&plan.output), atom(&context_text)],
    )
    .render();
    let generated = generated
        .ok_or("no context certificate was generated")?
        .render();
    let body = format!(
        "{{\n    let {certificate}: {compatibility} =\n{};\n    {certificate}({}, {}, {})\n}}",
        generated
            .lines()
            .map(|line| format!("        {line}"))
            .collect::<Vec<_>>()
            .join("\n"),
        term(source, &from).render(),
        term(source, &to).render(),
        request.proof
    );
    let result = format!(
        "{imports}{}{}{}",
        &source[..decl.body.span.start],
        body,
        &source[decl.body.span.end..]
    );
    check(&result).map_err(|e| format!("generated rewrite did not check: {e}"))?;
    Ok(RewriteResult {
        context: context_text,
        occurrences,
        outcome: Outcome::Checked { source: result },
    })
}
