//! Bounded source-level prototype for relational context proof generation.
//!
//! No inference of a carrier's preferred relation, global registration, or
//! mutation of the caller's session. Certificates are explicit inputs. A
//! successful result is ordinary source checked in an isolated elaborator.
//! This prototype is not the eventual boxed-code/meta-layer generator.

use heather_syntax::{DeclKind, Expr, ExprKind, Item, Span, parse_file};

use crate::{Elaborator, heather_emit::Expr as Out};

pub(crate) mod proof;
mod rewrite;
pub use rewrite::{RewriteRequest, RewriteResult, rewrite};

#[derive(Clone, Debug)]
pub struct Operation {
    /// Written call head, e.g. `append<A>` or `++`. Matched exactly.
    pub head: String,
    /// Named function used in the certificate, e.g. `append<A>`.
    pub function: String,
    /// One or two argument relations. Output and intermediate carriers may differ.
    pub inputs: Vec<String>,
    pub output: String,
    /// Evidence of PreservesRelation (unary) or nested Respectful (binary).
    pub certificate: Option<String>,
}

#[derive(Clone, Debug)]
pub struct Fixed {
    /// A fixed parameter name or numeral in this first fragment.
    pub term: String,
    pub relation: String,
    /// Evidence of relation(term, term); never invented from syntactic sameness.
    pub evidence: String,
}

#[derive(Clone, Debug)]
pub struct Request {
    pub function: String,
    pub variable: String,
    pub input: String,
    pub output: String,
    pub generated_name: String,
    pub operations: Vec<Operation>,
    pub fixed: Vec<Fixed>,
}

#[derive(Clone, Debug)]
pub struct Obligation {
    pub at: Span,
    pub reason: String,
    pub goal: String,
    /// A checked Type-valued definition displaying the goal's binder context.
    pub declaration: String,
}

#[derive(Clone, Debug)]
pub enum Outcome {
    /// Complete augmented module source, including the requested definition.
    Checked { source: String },
    /// No candidate definition is emitted or registered. Supply evidence and rerun.
    Blocked { obligations: Vec<Obligation> },
}

fn atom(s: &str) -> Out {
    Out::raw(s)
}
fn call(name: &str, args: Vec<Out>) -> Out {
    Out::call(Out::name(name), args)
}
fn lambda(variable: &str, body: Out) -> Out {
    Out::lambda([variable], body)
}
fn slice(source: &str, span: Span) -> &str {
    &source[span.start..span.end]
}

// Infix spans need not retain both grouping parentheses. Rebuild supported
// expression forms structurally rather than treating a span as source code.
fn term(source: &str, e: &Expr) -> Out {
    match &e.kind {
        ExprKind::Var(name) => atom(name),
        ExprKind::OpSymbol { symbol, .. } => atom(symbol),
        ExprKind::Num(n) => Out::nat(*n),
        ExprKind::TyApp { head, args } => atom(&format!(
            "{}<{}>",
            term(source, head).render(),
            args.iter()
                .map(|a| slice(source, a.span))
                .collect::<Vec<_>>()
                .join(", ")
        )),
        ExprKind::App {
            head,
            args,
            named,
            explicit: false,
            goal_oriented: false,
        } if named.is_empty() => {
            let args: Vec<_> = args.iter().map(|a| term(source, a)).collect();
            if let ExprKind::OpSymbol { symbol, .. } = &head.kind {
                if args.len() == 2 {
                    return atom(&format!(
                        "({} {symbol} {})",
                        args[0].render(),
                        args[1].render()
                    ));
                }
            }
            Out::call(term(source, head), args)
        }
        _ => atom(slice(source, e.span)),
    }
}

fn expression(s: &str) -> Result<(), String> {
    let parsed = parse_file(&format!("fn expression_probe() -> Type {{ {s} }}"))
        .map_err(|e| format!("invalid request expression: {e:?}"))?;
    match parsed.items.as_slice() {
        [Item::Decl(d)] if d.body.stmts.is_empty() && d.body.ons.is_empty() => Ok(()),
        _ => Err("request values must be single expressions".into()),
    }
}

fn bound(e: &Expr, depth: usize, remaining: &mut usize) -> Result<(), String> {
    if depth > 32 || *remaining == 0 {
        return Err("context generation exceeded its 256-node / 32-depth bound".into());
    }
    *remaining -= 1;
    match &e.kind {
        ExprKind::App { head, args, .. } => {
            bound(head, depth + 1, remaining)?;
            for arg in args {
                bound(arg, depth + 1, remaining)?;
            }
        }
        ExprKind::TyApp { head, .. } => bound(head, depth + 1, remaining)?,
        _ => {}
    }
    Ok(())
}

struct Walker<'a> {
    source: &'a str,
    request: &'a Request,
    remaining: usize,
    obligations: Vec<Obligation>,
}

impl Walker<'_> {
    fn missing(&mut self, at: Span, reason: &str, goal: Out) -> Option<Out> {
        self.obligations.push(Obligation {
            at,
            reason: reason.into(),
            goal: goal.render(),
            declaration: String::new(),
        });
        None
    }

    fn context_goal(&mut self, e: &Expr, output: &str, reason: &str) -> Option<Out> {
        self.missing(
            e.span,
            reason,
            call(
                "PreservesRelation",
                vec![
                    atom(&self.request.input),
                    atom(output),
                    lambda(&self.request.variable, term(self.source, e)),
                ],
            ),
        )
    }

    fn walk(&mut self, e: &Expr, output: &str, depth: usize) -> Result<Option<Out>, String> {
        if self.remaining == 0 || depth > 32 {
            return Err("context generation exceeded its 256-node / 32-depth bound".into());
        }
        self.remaining -= 1;
        let written = slice(self.source, e.span);
        if let ExprKind::Var(name) = &e.kind {
            if name == &self.request.variable {
                return Ok(if output == self.request.input {
                    Some(call("respectful_id", vec![atom(output)]))
                } else {
                    self.context_goal(
                        e,
                        output,
                        "the variable needs a certificate at this different relation",
                    )
                });
            }
        }
        if matches!(e.kind, ExprKind::Var(_) | ExprKind::Num(_)) {
            let fixed = self
                .request
                .fixed
                .iter()
                .find(|f| f.term == written && f.relation == output);
            return Ok(match fixed {
                Some(f) => Some(call(
                    "respectful_const",
                    vec![
                        atom(&self.request.input),
                        atom(output),
                        atom(written),
                        atom(written),
                        atom(&f.evidence),
                    ],
                )),
                None => {
                    // A missing sufficient premise, not a refutation of preservation.
                    self.missing(
                        e.span,
                        "fixed value has no supplied self-relation evidence",
                        call(output, vec![atom(written), atom(written)]),
                    )
                }
            });
        }
        if let ExprKind::App {
            head,
            args,
            named,
            explicit: false,
            goal_oriented: false,
        } = &e.kind
        {
            if named.is_empty() {
                let head_name = match &head.kind {
                    ExprKind::OpSymbol { symbol, .. } => symbol.as_str(),
                    ExprKind::Var(_) | ExprKind::TyApp { .. } => slice(self.source, head.span),
                    _ => return Ok(self.context_goal(e, output, "unsupported application head")),
                };
                let rules: Vec<_> = self
                    .request
                    .operations
                    .iter()
                    .filter(|op| {
                        op.head == head_name && op.inputs.len() == args.len() && op.output == output
                    })
                    .collect();
                if rules.len() > 1 {
                    return Err(format!(
                        "ambiguous certificates for {head_name} at {output}"
                    ));
                }
                if let Some(op) = rules.first().copied().cloned() {
                    let mut proofs = Vec::new();
                    for (arg, relation) in args.iter().zip(&op.inputs) {
                        proofs.push(self.walk(arg, relation, depth + 1)?);
                    }
                    let certificate = match &op.certificate {
                        Some(proof) => Some(atom(proof)),
                        None => {
                            let goal = if args.len() == 1 {
                                call(
                                    "PreservesRelation",
                                    vec![atom(&op.inputs[0]), atom(output), atom(&op.function)],
                                )
                            } else {
                                call(
                                    "Respectful",
                                    vec![
                                        atom(&op.inputs[0]),
                                        call("Respectful", vec![atom(&op.inputs[1]), atom(output)]),
                                        atom(&op.function),
                                        atom(&op.function),
                                    ],
                                )
                            };
                            self.missing(
                                head.span,
                                "operation preservation has not been supplied",
                                goal,
                            )
                        }
                    };
                    if let (Some(cert), Some(proofs)) =
                        (certificate, proofs.into_iter().collect::<Option<Vec<_>>>())
                    {
                        let contexts: Vec<_> = args
                            .iter()
                            .map(|arg| lambda(&self.request.variable, term(self.source, arg)))
                            .collect();
                        return Ok(Some(if args.len() == 1 {
                            call(
                                "preserves_relation_compose",
                                vec![
                                    atom(&self.request.input),
                                    atom(&op.inputs[0]),
                                    atom(output),
                                    contexts[0].clone(),
                                    atom(&op.function),
                                    proofs[0].clone(),
                                    cert,
                                ],
                            )
                        } else {
                            call(
                                "preserves_relation_binary",
                                vec![
                                    atom(&self.request.input),
                                    atom(&op.inputs[0]),
                                    atom(&op.inputs[1]),
                                    atom(output),
                                    contexts[0].clone(),
                                    contexts[1].clone(),
                                    atom(&op.function),
                                    proofs[0].clone(),
                                    proofs[1].clone(),
                                    cert,
                                ],
                            )
                        }));
                    }
                    return Ok(None);
                }
            }
        }
        Ok(self.context_goal(
            e,
            output,
            "no rule for this expression at the requested relation",
        ))
    }
}

// Import each module at most once. Existing selective imports stay selective;
// the ordinary checker reports any helpers they omit.
fn required_imports(file: &heather_syntax::File) -> String {
    ["relation_props", "relation_context"]
        .into_iter()
        .filter(|module| {
            !file
                .items
                .iter()
                .any(|item| matches!(item, Item::Import(import) if import.module == *module))
        })
        .map(|module| format!("import {module};\n"))
        .collect()
}

fn validate_request(request: &Request) -> Result<(), String> {
    if request.generated_name.is_empty()
        || !request
            .generated_name
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '_')
    {
        return Err("generated name must be an ordinary identifier".into());
    }
    for value in [&request.input, &request.output] {
        expression(value)?;
    }
    for op in &request.operations {
        if !(1..=2).contains(&op.inputs.len()) {
            return Err("only unary and binary operation rules are supported".into());
        }
        for value in op
            .inputs
            .iter()
            .chain([&op.output, &op.function])
            .chain(op.certificate.iter())
        {
            expression(value)?;
        }
    }
    for (i, f) in request.fixed.iter().enumerate() {
        if request.fixed[..i]
            .iter()
            .any(|other| other.term == f.term && other.relation == f.relation)
        {
            return Err(format!(
                "ambiguous fixed evidence for {} at {}",
                f.term, f.relation
            ));
        }
        for value in [&f.term, &f.relation, &f.evidence] {
            expression(value)?;
        }
    }
    Ok(())
}

/// Derive a certificate from a source declaration. `environment` contains its
/// imports (including relation_context), but not `module` itself. Both input
/// and output are checked in private clones; even a failure leaves it unchanged.
pub fn derive(
    environment: &Elaborator,
    module: &str,
    source: &str,
    request: &Request,
) -> Result<Outcome, String> {
    validate_request(request)?;
    let file = parse_file(source).map_err(|e| format!("input parse error: {e:?}"))?;
    let decl = file
        .items
        .iter()
        .find_map(|item| match item {
            Item::Decl(d) if d.name == request.function => Some(d),
            _ => None,
        })
        .ok_or("requested function was not found")?;
    if !matches!(decl.kind, DeclKind::Fn)
        || decl.is_meta
        || !decl.body.stmts.is_empty()
        || !decl.body.ons.is_empty()
        || decl
            .params
            .iter()
            .any(|p| p.implicit || p.solver.is_some() || p.symbol.is_some() || p.is_self)
        || decl.tyvars.iter().any(|p| p.level != 0)
    {
        return Err("fragment requires a plain fn with explicit parameters, Type<0> type parameters, and an expression body".into());
    }
    if !decl.params.iter().any(|p| p.name == request.variable) {
        return Err("the varying input must name a function parameter".into());
    }
    bound(&decl.body.result, 0, &mut 256)?;
    let base = format!("{}{source}\n", required_imports(&file));
    let check = |candidate: &str| {
        environment
            .clone()
            .elab_module_source(module, candidate)
            .map_err(|e| e.render(candidate))
    };
    check(&base).map_err(|e| format!("input did not check: {e}"))?;
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
        .filter(|p| p.name != request.variable)
        .map(|p| format!("{}: {}", p.name, slice(source, p.ty.span)))
        .collect::<Vec<_>>()
        .join(", ");
    let mut walker = Walker {
        source,
        request,
        remaining: 256,
        obligations: Vec::new(),
    };
    let proof = walker.walk(&decl.body.result, &request.output, 0)?;
    if !walker.obligations.is_empty() {
        for (i, obligation) in walker.obligations.iter_mut().enumerate() {
            obligation.declaration = format!(
                "fn {}_obligation_{i}{generics}({parameters}) -> Type {{\n    {}\n}}\n",
                request.generated_name, obligation.goal
            );
            check(&format!("{base}{}", obligation.declaration)).map_err(|e| {
                format!("obligation is not well-formed in this binder context: {e}")
            })?;
        }
        return Ok(Outcome::Blocked {
            obligations: walker.obligations,
        });
    }
    let function = format!("{}{generics}", decl.name);
    let applied = Out::call(atom(&function), decl.params.iter().map(|p| atom(&p.name)));
    let goal = call(
        "PreservesRelation",
        vec![
            atom(&request.input),
            atom(&request.output),
            lambda(&request.variable, applied),
        ],
    );
    let output = format!(
        "{base}\nfn {}{generics}({parameters}) -> {} {{\n    {}\n}}\n",
        request.generated_name,
        goal.render(),
        proof.ok_or("no complete context proof")?.render()
    );
    check(&output).map_err(|e| format!("generated certificate did not check: {e}"))?;
    Ok(Outcome::Checked { source: output })
}
