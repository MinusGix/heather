//! Interface definitions (`docs/interface-definitions-design.md`).
//!
//! An `interface fn` is an ordinary definition inside its own module. Outside
//! it, the elaborator's semantic worlds withhold its body
//! ([`heather_kernel::term::GlobalCtx::withheld`]): a call at open arguments
//! is an atom, and a call saturated at closed arguments still computes. The
//! trusted check never withholds, so this decides what the elaborator
//! accepts and never what the kernel accepts.
//!
//! The registry is keyed by the global's qualified name, like the evidence
//! rules, so a module image carries it as an event and a relocated image
//! needs no rewriting.

use std::collections::BTreeMap;
use heather_kernel::rc::Rc;

use heather_kernel::term::{GlobalCtx, GlobalRef, GlobalVar, Term, Type, Withheld};
use heather_syntax::{Block, Decl, DeclKind, Expr, ExprKind, Span, Ty, TyKind};

use crate::{ElabError, Elaborator, R};

/// One registered interface definition.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct InterfaceInfo {
    /// The module that declared it: the one module where it is transparent.
    pub(crate) module: String,
    /// How many arguments a call needs before its body may unfold: the
    /// declaration's parameters, type parameters included.
    pub(crate) arity: u32,
    /// The declaration's name as written, and its generated equations' names
    /// (§5): what a refusal at the boundary tells a client to cite.
    pub(crate) name: String,
    pub(crate) equations: Vec<String>,
}

/// Every interface definition the session has seen, by global key.
#[derive(Clone, Default)]
pub(crate) struct Interfaces {
    by_key: BTreeMap<String, InterfaceInfo>,
}

impl Interfaces {
    pub(crate) fn get(&self, key: &str) -> Option<&InterfaceInfo> {
        self.by_key.get(key)
    }

    pub(crate) fn commit(&mut self, key: String, info: InterfaceInfo) {
        self.by_key.insert(key, info);
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.by_key.is_empty()
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = (&String, &InterfaceInfo)> {
        self.by_key.iter()
    }
}

impl Elaborator {
    /// The interface boundary of the module being elaborated: every
    /// registered interface definition of another module, at its arity.
    /// `None` when there is none, which leaves every world as it was.
    pub(crate) fn withheld_policy(&self) -> Option<Rc<Withheld>> {
        if self.interfaces.is_empty() {
            return None;
        }
        let current = &self.names.scope().module;
        let mut withheld = Withheld::new();
        for (key, info) in self.interfaces.iter() {
            if &info.module == current || self.scope.unfolded.contains(key) {
                continue;
            }
            if let Some(global) = self.names.global(key) {
                withheld.insert(global.abs as usize, info.arity);
            }
        }
        (!withheld.is_empty()).then(|| Rc::new(withheld))
    }

    /// Whether `key` names an interface definition this module may not see
    /// into: what the withheld-mismatch note asks.
    pub(crate) fn withheld_here(&self, key: &str) -> bool {
        self.interfaces.get(key).is_some_and(|info| info.module != self.names.scope().module)
    }

    /// `error`, a refusal of a check made with interface bodies withheld
    /// (`psi`), with a note naming the withheld definitions the refused
    /// statement or proof mentions and what to cite instead (§4). Without
    /// it a client sees a plain mismatch where the body used to convert.
    pub(crate) fn withheld_note(&self, error: ElabError, psi: &GlobalCtx, ty: &Type, body: Option<&Term>) -> ElabError {
        let Some(withheld) = psi.withheld.as_deref() else { return error };
        let len = psi.bindings.len();
        // Absolute indices of the globals the statement and proof mention,
        // and of those their statements mention in turn: a lemma cited at
        // an open call carries the call in its type, not in the proof's
        // syntax.
        let mut seen = std::collections::BTreeSet::new();
        let mut direct = Vec::new();
        let mut record = |r: GlobalRef| {
            if let Some(at) = GlobalVar::from(r).position(len) {
                direct.push(at);
            }
            Some(r)
        };
        ty.reindex_global(&mut record);
        if let Some(body) = body {
            body.reindex_global(&mut record);
        }
        for at in direct {
            if !seen.insert(at) {
                continue;
            }
            if let Some(heather_kernel::term::GlobalBinding::Tm { ty, .. }) = psi.bindings.get(at) {
                ty.reindex_global(&mut |r: GlobalRef| {
                    if let Some(named) = GlobalVar::from(r).position(at) {
                        seen.insert(named);
                    }
                    Some(r)
                });
            }
        }
        let mut lines = Vec::new();
        for (key, info) in self.interfaces.iter() {
            let Some(global) = self.names.global(key) else { continue };
            let abs = global.abs as usize;
            if withheld.arity(abs).is_none() || abs >= len || !seen.contains(&abs) {
                continue;
            }
            let cite = if info.equations.is_empty() {
                "a lemma about it".to_string()
            } else {
                let eqs: Vec<String> = info.equations.iter().map(|e| format!("`{e}`")).collect();
                format!("{} or a lemma about it", eqs.join(", "))
            };
            lines.push(format!(
                "`{}` is an interface definition of `{}`, so its body is withheld here at open \
                 arguments: cite {cite}, or declare the proof `unfolding {}` \
                 (docs/interface-definitions-design.md §4)",
                info.name, info.module, info.name
            ));
        }
        if lines.is_empty() {
            return error;
        }
        let extra = lines.join("; ");
        match error {
            ElabError::Kernel { decl, span, err, note, site } => ElabError::Kernel {
                decl,
                span,
                err,
                note: Some(match note {
                    Some(n) => format!("{n}\nnote: {extra}"),
                    None => extra,
                }),
                site,
            },
            ElabError::Elab { msg, span } => ElabError::Elab { msg: format!("{msg}\nnote: {extra}"), span },
            other => other,
        }
    }

    /// The global keys an `unfolding` clause names, each an interface
    /// definition (§4). Naming anything else is refused: the clause would
    /// do nothing, and a reader would believe it did.
    pub(crate) fn unfolding_keys(&self, decl: &Decl) -> R<Vec<String>> {
        decl.unfolding
            .iter()
            .map(|name| {
                let key = self.key_of(name).filter(|k| self.interfaces.get(k).is_some());
                key.ok_or_else(|| ElabError::Elab {
                    msg: format!(
                        "`unfolding {name}`: `{name}` is not an interface definition, so its \
                         body is never withheld (docs/interface-definitions-design.md §4)"
                    ),
                    span: decl.span,
                })
            })
            .collect()
    }

    /// The refusals of `docs/interface-definitions-design.md` §1 that need
    /// the elaborator: a `def` (the parser lets `interface def` through as
    /// no syntax of its own, so the flag on a value is refused here) and a
    /// function into a universe.
    pub(crate) fn interface_shape(&self, decl: &Decl) -> R<()> {
        let refuse = |msg: String, span: Span| Err(ElabError::Elab { msg, span });
        if decl.kind != DeclKind::Fn || decl.value || decl.is_meta {
            return refuse(
                "`interface` marks a `fn` with parameters (docs/interface-definitions-design.md §1)".into(),
                decl.span,
            );
        }
        if decl.tyvars.is_empty() && decl.params.is_empty() {
            return refuse(
                format!(
                    "`{}` has no parameters, so every call of it is closed and computes: \
                     `interface` would withhold nothing (docs/interface-definitions-design.md §1)",
                    decl.name
                ),
                decl.span,
            );
        }
        if matches!(decl.result.kind, TyKind::Univ { .. }) {
            return refuse(
                format!(
                    "`{}` returns a type: a client reads a defined proposition's shape (a \
                     projection, a `match`), so withholding its body is a design of its own, \
                     not this round's (docs/interface-definitions-design.md §1)",
                    decl.name
                ),
                decl.result.span,
            );
        }
        Ok(())
    }

    /// Register the elaborated interface definition `decl`.
    pub(crate) fn register_interface(&mut self, decl: &Decl, equations: Vec<String>) -> R<()> {
        let refuse = |msg: String| Err(ElabError::Elab { msg, span: decl.span });
        let Some(key) = self.key_of(&decl.name) else {
            return refuse(format!("`{}` is not a declared global", decl.name));
        };
        let Some(global) = self.names.global(&key) else {
            return refuse(format!("`{}` is not a declared global", decl.name));
        };
        let arity = global.params.len() as u32;
        let module = self.names.scope().module.clone();
        self.semantic_commit_interface(key, InterfaceInfo { module, arity, name: decl.name.clone(), equations });
        Ok(())
    }
}

fn var(name: &str, span: Span) -> Expr {
    Expr { kind: ExprKind::Var(name.to_string()), span }
}

/// `@f(x̄)`: every parameter passed, implicit ones included, so the
/// equation's left side is the call and nothing is left to inference.
fn call(decl: &Decl, span: Span) -> Expr {
    let head = if decl.tyvars.is_empty() {
        var(&decl.name, span)
    } else {
        Expr {
            kind: ExprKind::TyApp {
                head: Box::new(var(&decl.name, span)),
                args: decl
                    .tyvars
                    .iter()
                    .map(|t| Ty { kind: TyKind::Named { name: t.name.clone(), args: Vec::new() }, span })
                    .collect(),
            },
            span,
        }
    };
    let args: Vec<Expr> = decl.params.iter().map(|p| var(&p.name, span)).collect();
    if args.is_empty() {
        return head;
    }
    Expr {
        kind: ExprKind::App { head: Box::new(head), args, named: Vec::new(), explicit: true, goal_oriented: false },
        span,
    }
}

/// The body as one expression, self-calls spelled by the qualified name
/// (`decreases`'s `f_unfold` reads it the same way).
fn body_expr(decl: &Decl) -> Expr {
    let source = if decl.body.stmts.is_empty() {
        (*decl.body.result).clone()
    } else {
        Expr {
            kind: ExprKind::Block(Box::new(Block {
                stmts: decl.body.stmts.clone(),
                result: decl.body.result.clone(),
                ons: Vec::new(),
                span: decl.body.span,
            })),
            span: decl.body.span,
        }
    };
    let base = decl.name.rsplit("::").next().unwrap_or(&decl.name);
    if base == decl.name {
        return source;
    }
    let qualified = var(&decl.name, decl.span);
    crate::measure::subst(&source, &[(base, &qualified)], &mut Vec::new())
}

/// Whether `block` names the declaration at all: a call, a method call
/// (`t.len()`), or the bare name. Over-approximate on purpose: a shadowing
/// local only costs the whole-body equation, which the arm equations cover.
fn mentions(block: &Block, base: &str, full: &str) -> bool {
    let mut found = false;
    let mut scan = |e: &Expr| {
        crate::surface::walk_expr(e, &mut |x| match &x.kind {
            ExprKind::Var(n) if n == base || n == full => found = true,
            ExprKind::Dot { name, .. } if name == base => found = true,
            _ => {}
        });
    };
    for s in &block.stmts {
        match s {
            heather_syntax::Stmt::Let { expr, .. }
            | heather_syntax::Stmt::LetRecord { expr, .. }
            | heather_syntax::Stmt::LetCode { expr, .. } => scan(expr),
        }
    }
    scan(&block.result);
    found
}

fn theorem(decl: &Decl, name: String, lhs: Expr, rhs: Expr, span: Span) -> Decl {
    Decl {
        kind: DeclKind::Theorem,
        is_meta: false,
        is_evidence: false,
        is_interface: false, partial: None,
        value: false,
        elaborates: None,
        name,
        tyvars: decl.tyvars.clone(),
        params: decl.params.clone(),
        result: Ty { kind: TyKind::Eq(Box::new(lhs), Box::new(rhs)), span },
        decreases: None,
        unfolding: Vec::new(),
        body: Block { stmts: Vec::new(), result: Box::new(Expr { kind: ExprKind::Refl, span }), ons: Vec::new(), span },
        span,
    }
}

impl Elaborator {
    /// The unfolding equations of the interface definition `decl`, elaborated
    /// in its module right after it (docs/interface-definitions-design.md §5):
    ///
    /// - `f_unfold(x̄): f(x̄) = body`, by `refl`, for a function that does not
    ///   call itself (a `decreases` function already has its companion);
    /// - for a body that is a `match` on a parameter, one
    ///   `f_unfold_<Ctor>` per constructor arm, the parameter replaced by the
    ///   constructor at the arm's binders, by `refl`: a structural recursion
    ///   reduces on a constructor, and its recursor reduct of a self-call is
    ///   `f` at the child by δ.
    ///
    /// A recursive body of another shape gets none: `f(x̄) = body` at an open
    /// argument is not definitional for a structural recursion (the arm reads
    /// the recursor's hypothesis where the body says `f`).
    pub(crate) fn interface_equations(&mut self, decl: &Decl) -> R<Vec<String>> {
        let mut made = Vec::new();
        let span = decl.span;
        let base = decl.name.rsplit("::").next().unwrap_or(&decl.name).to_string();
        let recursive = mentions(&decl.body, &base, &decl.name);
        let unfold = crate::measure::unfold_name(&decl.name);
        if !recursive && self.key_of(&unfold).is_none() {
            let eq = theorem(decl, unfold.clone(), call(decl, span), body_expr(decl), span);
            self.elab_decl_one(&eq, None)?;
            made.push(unfold.clone());
        } else if self.key_of(&unfold).is_some() {
            made.push(unfold.clone());
        }
        if !decl.body.stmts.is_empty() {
            return Ok(made);
        }
        let ExprKind::Match { scrut, arms, .. } = &decl.body.result.kind else { return Ok(made) };
        let ExprKind::Var(scrut_name) = &scrut.kind else { return Ok(made) };
        let Some(at) = decl.params.iter().position(|p| &p.name == scrut_name) else { return Ok(made) };
        // The constructors with their field types, at the parameter's type
        // arguments. `Nat` is the kernel's, not a declared inductive.
        let ctors: Vec<(String, Vec<Ty>)> = if matches!(decl.params[at].ty.kind, TyKind::Nat) {
            vec![("Zero".into(), Vec::new()), ("Succ".into(), vec![decl.params[at].ty.clone()])]
        } else {
            let TyKind::Named { name: ind_name, args: ind_args } = &decl.params[at].ty.kind else { return Ok(made) };
            let Some(ind) = self.lookup_inductive(ind_name).cloned() else { return Ok(made) };
            if ind.params.len() != ind_args.len() {
                return Ok(made);
            }
            let ty_args: std::collections::HashMap<String, Ty> =
                ind.params.iter().cloned().zip(ind_args.iter().cloned()).collect();
            ind.ctors
                .iter()
                .map(|c| (c.name.clone(), c.fields.iter().map(|(_, ty)| crate::traits::subst_ty(&ty_args, ty)).collect()))
                .collect()
        };
        let qualified = var(&decl.name, span);
        for arm in arms.iter().filter(|a| !a.default) {
            let Some((ctor_name, field_tys)) = ctors.iter().find(|(name, _)| *name == arm.ctor) else { continue };
            if arm.binders.len() != field_tys.len() {
                continue;
            }
            let mut binders = Vec::new();
            for (i, pat) in arm.binders.iter().enumerate() {
                let heather_syntax::Pat::Var { name, .. } = pat else { binders.clear(); break };
                let name = if name == "_" { format!("__{ctor_name}_{i}") } else { name.clone() };
                binders.push(name);
            }
            if binders.len() != field_tys.len() {
                continue;
            }
            let mut params = decl.params.clone();
            let fields: Vec<heather_syntax::Param> = binders
                .iter()
                .zip(field_tys)
                .map(|(name, ty)| heather_syntax::Param {
                    name: name.clone(),
                    ty: ty.clone(),
                    implicit: false,
                    is_self: false,
                    ..decl.params[at].clone()
                })
                .collect();
            params.splice(at..=at, fields);
            let ctor_expr = if binders.is_empty() {
                var(ctor_name, span)
            } else {
                Expr {
                    kind: ExprKind::App {
                        head: Box::new(var(ctor_name, span)),
                        args: binders.iter().map(|b| var(b, span)).collect(),
                        named: Vec::new(),
                        explicit: false,
                        goal_oriented: false,
                    },
                    span,
                }
            };
            let lhs = crate::measure::subst(&call(decl, span), &[(scrut_name.as_str(), &ctor_expr)], &mut Vec::new());
            // The arm may still name the scrutinee, which is now the
            // constructor application.
            let rhs = crate::measure::subst(&arm.body, &[(scrut_name.as_str(), &ctor_expr)], &mut Vec::new());
            let rhs = if base == decl.name { rhs } else { crate::measure::subst(&rhs, &[(base.as_str(), &qualified)], &mut Vec::new()) };
            let mut eq = theorem(decl, format!("{unfold}_{ctor_name}"), lhs, rhs, span);
            eq.params = params;
            self.elab_decl_one(&eq, None)?;
            made.push(eq.name);
        }
        Ok(made)
    }
}
