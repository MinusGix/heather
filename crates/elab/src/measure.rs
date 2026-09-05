//! `decreases e` — termination by a `Nat` measure
//! (issues/termination-measures.md, docs/termination-measures-design.md).
//!
//! A declaration `fn f(x̄) -> T decreases e { body }` is elaborated as strong
//! induction on a bound for the measure, spelled entirely at the **surface**
//! and handed to the ordinary checker:
//!
//! ```text
//! match Succ(e) as λ z => (x̄) -> nat::Lt(e, z) -> T {
//!     Zero        => λ x̄ h => match h {},
//!     Succ(k, ih) => λ x̄ h => body[ f(ȳ) ↦ ih(ȳ, nat::le_trans(Succ(e[ȳ]), e, k, ?decN, h)) ],
//! }(x̄, nat::lt_succ_self(e))
//! ```
//!
//! The wrapper is a written-motive `match` with the explicit-ih arm — two
//! features older than this one — and the parameters are re-bound under
//! their own names, so the body reads exactly as written. Each recursive
//! call owes one obligation, `e[ȳ] < e`, a goal hole named `decN` in source
//! order; it is discharged by `on ?decN := …`, and defaults to `omega` where
//! no `on` names it.
//!
//! Nothing here is trusted. The rewrite reads names — the declaration's own
//! name for a self-call, the parameters' names for the measure's arguments
//! — and where a name misleads it the emitted term fails to check: the ih's
//! hypothesis binder is at the *elaborated* measure, so a wrong obligation
//! type is refused where the call is written, never accepted.

use heather_syntax::{
    Arm, Block, Decl, Expr, ExprKind, LamBinder, MatchForm, OnTarget, Pat, Span, Stmt, Ty, TyKind,
};

use crate::{Cx, Elaborator, R, err};

/// The obligations a wrapped body owes, one per recursive call in source
/// order: the call's span, the hole's name, and the obligation rendered for
/// a diagnostic.
pub(crate) struct Obligations {
    pub(crate) sites: Vec<(Span, String, String)>,
}

impl Obligations {
    /// Reword an `omega` failure at one of this declaration's obligations
    /// into a message that names the obligation and the way to discharge it
    /// by hand. Every other error passes through.
    pub(crate) fn explain(&self, error: crate::ElabError) -> crate::ElabError {
        let crate::ElabError::Elab { msg, span } = &error else {
            return error;
        };
        if !msg.starts_with("`omega` got stuck") {
            return error;
        }
        let Some((_, hole, text)) = self.sites.iter().find(|(s, ..)| s == span) else {
            return error;
        };
        crate::ElabError::Elab {
            msg: format!(
                "this recursive call must decrease the measure, and `{text}` was not \
                 proved automatically ({msg}). Discharge it by hand: \
                 `on ?{hole} := …;` at the end of the body"
            ),
            span: *span,
        }
    }
}

const K: &str = "__dec_k";
const IH: &str = "__dec_ih";
const H: &str = "__dec_h";
const Z: &str = "__dec_z";

impl Elaborator {
    /// Build the wrapper (module docs) for `decl`, whose body recurses under
    /// `decreases measure`. `cx` is the declaration's parameter context and
    /// `name` its self-name (the base name, for a member).
    pub(crate) fn wrap_measure(
        &self,
        cx: &Cx,
        decl: &Decl,
        name: &str,
        measure: &Expr,
    ) -> R<(Expr, Obligations)> {
        if decl.is_meta {
            return err("`decreases` is for ordinary declarations, not `meta fn`", measure.span);
        }
        if let Some(p) = decl.params.iter().find(|p| p.is_self || p.solver.is_some()) {
            return err(
                format!(
                    "`decreases` does not yet cover a declaration with a `self` or \
                     solver parameter (`{}`): the recursion re-binds every parameter \
                     explicitly, and those two are filled another way",
                    p.name
                ),
                p.span,
            );
        }
        // The measure is a `Nat`, checked here so the message says so rather
        // than surfacing as a mismatch inside `nat::Lt`.
        self.elab_check(
            cx,
            measure,
            &heather_kernel::term::Type::Nat,
            &heather_kernel::level::Level::Zero,
        )
        .map_err(|error| match error {
            crate::ElabError::Elab { msg, span } => crate::ElabError::Elab {
                msg: format!("a `decreases` measure is a `Nat`: {msg}"),
                span,
            },
            other => other,
        })?;
        let span = measure.span;
        // The wrapper spells `nat::Lt`, `nat::le_trans` and `nat::lt_succ_self`;
        // the default closer spells `omega`'s certificates, which name the
        // `omega` module. Neither is the prelude's, so the module has to
        // import them — checked here so the message says so.
        if !matches!(self.resolve_declared("nat::le_trans"), crate::NameRes::Found(_)) {
            return err(
                "`decreases` states its obligations with `nat::Lt` and discharges them \
                 through `nat::le_trans`: `import nat;` first",
                span,
            );
        }
        // `omega`'s certificates name `omega::` and `int::` lemmas, so the
        // default closer is available only where both modules are imported;
        // otherwise every obligation is an ordinary unsolved goal, reported
        // with its statement.
        let omega_available = ["omega::nat_le_of_not_not_le", "int::negsucc_lt_ofnat"]
            .iter()
            .all(|n| matches!(self.resolve_declared(n), crate::NameRes::Found(_)));
        let params: Vec<&heather_syntax::Param> = decl.params.iter().collect();
        let on_named: Vec<&str> = decl
            .body
            .ons
            .iter()
            .filter_map(|o| match &o.target {
                OnTarget::Name(n) => Some(n.as_str()),
                _ => None,
            })
            .collect();
        let mut state = Rewrite {
            name,
            params: &params,
            measure,
            on_named: &on_named,
            omega_available,
            next: 1,
            eqs: 0,
            refinements: Vec::new(),
            sites: Vec::new(),
            error: None,
        };
        let stmts: Vec<Stmt> = decl
            .body
            .stmts
            .iter()
            .map(|s| state.stmt(s, &mut Vec::new()))
            .collect();
        let result = state.expr(&decl.body.result, &mut Vec::new());
        if let Some(error) = state.error.take() {
            return Err(error);
        }
        let body = Expr {
            kind: ExprKind::Block(Box::new(Block {
                stmts,
                result: Box::new(result),
                ons: Vec::new(),
                span: decl.body.span,
            })),
            span: decl.body.span,
        };
        let var = |n: &str| Expr {
            kind: ExprKind::Var(n.to_string()),
            span,
        };
        let app = |head: Expr, args: Vec<Expr>| Expr {
            kind: ExprKind::App {
                head: Box::new(head),
                args,
                named: Vec::new(),
                explicit: false,
                goal_oriented: false,
            },
            span,
        };
        // λ x̄ h => e, the parameters under their own names.
        let lam = |body: Expr| {
            let binders = params
                .iter()
                .map(|p| p.name.as_str())
                .chain([H])
                .map(|n| LamBinder {
                    name: n.to_string(),
                    ty: None,
                    implicit: false,
                    span,
                })
                .collect();
            Expr {
                kind: ExprKind::Lam {
                    binders,
                    body: Box::new(body),
                },
                span,
            }
        };
        // (x̄) -> nat::Lt(e, z) -> T
        let bound = Ty {
            kind: TyKind::OfExpr(Box::new(app(var("nat::Lt"), vec![measure.clone(), var(Z)]))),
            span,
        };
        let mut motive_ty = Ty {
            kind: TyKind::Fn {
                binder: None,
                implicit: false,
                dom: Box::new(bound),
                cod: Box::new(decl.result.clone()),
            },
            span,
        };
        for p in params.iter().rev() {
            motive_ty = Ty {
                kind: TyKind::Fn {
                    binder: Some(p.name.clone()),
                    implicit: false,
                    dom: Box::new(p.ty.clone()),
                    cod: Box::new(motive_ty),
                },
                span,
            };
        }
        let motive = Expr {
            kind: ExprKind::Lam {
                binders: vec![LamBinder {
                    name: Z.to_string(),
                    ty: None,
                    implicit: false,
                    span,
                }],
                body: Box::new(Expr {
                    kind: ExprKind::TyLit(Box::new(motive_ty)),
                    span,
                }),
            },
            span,
        };
        let absurd = Expr {
            kind: ExprKind::Match {
                form: MatchForm::Match,
                generated: false,
                scrut: Box::new(var(H)),
                eqbind: None,
                motive: None,
                arms: Vec::new(),
            },
            span,
        };
        let pat = |n: &str| Pat::Var {
            name: n.to_string(),
            span,
        };
        let elim = Expr {
            kind: ExprKind::Match {
                form: MatchForm::Match,
                generated: false,
                scrut: Box::new(app(var("Succ"), vec![measure.clone()])),
                eqbind: None,
                motive: Some(Box::new(motive)),
                arms: vec![
                    Arm {
                        ctor: "Zero".into(),
                        default: false,
                        binders: Vec::new(),
                        body: lam(absurd),
                        span,
                    },
                    Arm {
                        ctor: "Succ".into(),
                        default: false,
                        binders: vec![pat(K), pat(IH)],
                        body: lam(body),
                        span: decl.body.span,
                    },
                ],
            },
            span,
        };
        let mut args: Vec<Expr> = params.iter().map(|p| var(&p.name)).collect();
        args.push(app(var("nat::lt_succ_self"), vec![measure.clone()]));
        let sites = state.sites;
        Ok((app(elim, args), Obligations { sites }))
    }
}

/// The self-call rewrite (module docs), threaded through a surface walk that
/// tracks the names bound around each node so a shadowed parameter or
/// declaration name is left alone.
struct Rewrite<'a> {
    name: &'a str,
    params: &'a [&'a heather_syntax::Param],
    measure: &'a Expr,
    on_named: &'a [&'a str],
    /// Whether an obligation nobody discharges by hand may default to `omega`.
    omega_available: bool,
    next: usize,
    eqs: usize,
    /// What the enclosing `match`es have established about the measure's
    /// variables, outermost first: `(variable, the arm's pattern as an
    /// expression, the equation binder that says so)`. An obligation is
    /// stated at the measure with all of these applied — the statement a
    /// reader expects inside the arm — and transported back through the
    /// equations to the ih's own hypothesis (§3 of the design).
    refinements: Vec<(String, Expr, String)>,
    sites: Vec<(Span, String, String)>,
    error: Option<crate::ElabError>,
}

impl Rewrite<'_> {
    fn fail(&mut self, msg: String, span: Span) {
        if self.error.is_none() {
            self.error = Some(crate::ElabError::Elab { msg, span });
        }
    }

    /// `f(ȳ, spill…)` ↦ `ih(ȳ, proof, spill…)`. Arguments were rewritten by
    /// the caller already, so a nested self-call is handled inside out.
    fn self_call(&mut self, call: &Expr, args: Vec<Expr>, explicit: bool) -> Expr {
        let span = call.span;
        let positions: Vec<usize> = (0..self.params.len())
            .filter(|&j| explicit || !self.params[j].implicit)
            .collect();
        if positions.len() < self.params.len() {
            self.fail(
                format!(
                    "a recursive call to `{}` under `decreases` passes every parameter, \
                     implicit ones included: write `@{}(…)`",
                    self.name, self.name
                ),
                span,
            );
        }
        if args.len() < positions.len() {
            self.fail(
                format!(
                    "a recursive call to `{}` under `decreases` is saturated: it takes \
                     {} argument(s), found {}",
                    self.name,
                    positions.len(),
                    args.len()
                ),
                span,
            );
            return call.clone();
        }
        let (passed, spill) = args.split_at(positions.len());
        // e[ȳ]: the measure with each parameter replaced by the argument
        // written at its position.
        let map: Vec<(&str, &Expr)> = positions
            .iter()
            .zip(passed)
            .map(|(&j, a)| (self.params[j].name.as_str(), a))
            .collect();
        let at_args = subst(self.measure, &map, &mut Vec::new());
        // The measure as the enclosing arms know it: `e[Succ(k)/n]` inside
        // `match n { Succ(k) => … }`, and so on down.
        let stages = self.stages();
        let refined = stages.last().expect("stage 0 is the measure itself");
        let hole = format!("dec{}", self.next);
        self.next += 1;
        let text = format!(
            "{} < {}",
            crate::traits::render_expr(&at_args),
            crate::traits::render_expr(refined)
        );
        let obligation = if self.on_named.contains(&hole.as_str()) || !self.omega_available {
            Expr {
                kind: ExprKind::Hole(Some(hole.clone())),
                span,
            }
        } else {
            Expr {
                kind: ExprKind::Var("omega".into()),
                span,
            }
        };
        self.sites.push((span, hole, text));
        let var = |n: &str| Expr {
            kind: ExprKind::Var(n.to_string()),
            span,
        };
        let app = |head: Expr, args: Vec<Expr>| Expr {
            kind: ExprKind::App {
                head: Box::new(head),
                args,
                named: Vec::new(),
                explicit: false,
                goal_oriented: false,
            },
            span,
        };
        // Transport the obligation back from the refined measure to the
        // measure the ih's hypothesis is stated at, one equation at a time:
        // `j(sym(eq_i), λ y _ => e[ȳ] < e_{i-1}[y/v_i], acc)` turns a proof at
        // `e_i = e_{i-1}[pat_i/v_i]` into one at `e_{i-1}`.
        let lt = |a: Expr, b: Expr| app(var("nat::Lt"), vec![a, b]);
        let mut acc = obligation;
        for (i, (v, _, eq)) in self.refinements.iter().enumerate().rev() {
            let below = &stages[i];
            let y = format!("__dec_y{i}");
            let at_y = subst(
                below,
                &[(v.as_str(), &var(&y))],
                &mut Vec::new(),
            );
            let motive = Expr {
                kind: ExprKind::Lam {
                    binders: [y.as_str(), "__dec_q"]
                        .into_iter()
                        .map(|n| LamBinder {
                            name: n.to_string(),
                            ty: None,
                            implicit: false,
                            span,
                        })
                        .collect(),
                    body: Box::new(lt(at_args.clone(), at_y)),
                },
                span,
            };
            acc = Expr {
                kind: ExprKind::J {
                    proof: Box::new(app(var("sym"), vec![var(eq)])),
                    motive: Box::new(motive),
                    case: Box::new(acc),
                },
                span,
            };
        }
        // Succ(e[ȳ]) <= e, e <= k  ⊢  Succ(e[ȳ]) <= k, which is `e[ȳ] < k`;
        // `h : e < Succ k` *is* `e <= k` by reduction.
        let proof = app(
            var("nat::le_trans"),
            vec![
                app(var("Succ"), vec![at_args]),
                self.measure.clone(),
                var(K),
                acc,
                var(H),
            ],
        );
        let mut all: Vec<Expr> = passed.to_vec();
        all.push(proof);
        all.extend(spill.iter().cloned());
        app(var(IH), all)
    }

    /// `e_0 = e`, `e_i = e_{i-1}[pat_i/v_i]` for each refinement in force.
    fn stages(&self) -> Vec<Expr> {
        let mut stages = vec![self.measure.clone()];
        for (v, pat, _) in &self.refinements {
            let last = stages.last().expect("seeded");
            stages.push(subst(last, &[(v.as_str(), pat)], &mut Vec::new()));
        }
        stages
    }

    /// A `match` on a variable the (refined) measure mentions is given an
    /// equation binding, so that each arm can state the obligation at the
    /// pattern and transport it back (module docs). Arms whose patterns are
    /// not expressions (`_`, a named field) get no refinement and see the
    /// measure as the enclosing arm did.
    fn refining_match(&self, scrut: &Expr, eqbind: &Option<String>) -> Option<String> {
        let ExprKind::Var(v) = &scrut.kind else {
            return None;
        };
        if eqbind.is_some() {
            return None;
        }
        let refined = self.stages().pop().expect("seeded");
        mentions(&refined, v).then(|| format!("__dec_eq{}", self.eqs))
    }

    fn expr(&mut self, e: &Expr, bound: &mut Vec<String>) -> Expr {
        let span = e.span;
        let kind = match &e.kind {
            ExprKind::App {
                head,
                args,
                named,
                explicit,
                goal_oriented,
            } => {
                let args: Vec<Expr> = args.iter().map(|a| self.expr(a, bound)).collect();
                let named: Vec<heather_syntax::NamedArg> = named
                    .iter()
                    .map(|n| heather_syntax::NamedArg {
                        name: n.name.clone(),
                        name_span: n.name_span,
                        expr: self.expr(&n.expr, bound),
                        span: n.span,
                    })
                    .collect();
                let callee = match &head.kind {
                    ExprKind::TyApp { head, .. } => &head.kind,
                    other => other,
                };
                if matches!(callee, ExprKind::Var(n) if n == self.name)
                    && !bound.iter().any(|b| b == self.name)
                {
                    if !named.is_empty() {
                        self.fail(
                            format!(
                                "a recursive call to `{}` under `decreases` takes positional \
                                 arguments only",
                                self.name
                            ),
                            span,
                        );
                    }
                    return self.self_call(e, args, *explicit);
                }
                ExprKind::App {
                    head: Box::new(self.expr(head, bound)),
                    args,
                    named,
                    explicit: *explicit,
                    goal_oriented: *goal_oriented,
                }
            }
            ExprKind::TyApp { head, args } => ExprKind::TyApp {
                head: Box::new(self.expr(head, bound)),
                args: args.clone(),
            },
            ExprKind::Lam { binders, body } => {
                let n = bound.len();
                bound.extend(binders.iter().map(|b| b.name.clone()));
                let body = self.expr(body, bound);
                bound.truncate(n);
                ExprKind::Lam {
                    binders: binders.clone(),
                    body: Box::new(body),
                }
            }
            ExprKind::CollectionLit(xs) => {
                ExprKind::CollectionLit(xs.iter().map(|x| self.expr(x, bound)).collect())
            }
            ExprKind::Eq(a, b) => {
                ExprKind::Eq(Box::new(self.expr(a, bound)), Box::new(self.expr(b, bound)))
            }
            ExprKind::Match {
                form,
                generated,
                scrut,
                eqbind,
                motive,
                arms,
            } => {
                let refine = if *form == MatchForm::Match {
                    self.refining_match(scrut, eqbind)
                } else {
                    None
                };
                if refine.is_some() {
                    self.eqs += 1;
                }
                let eqbind = eqbind.clone().or(refine.clone());
                let arms = arms
                    .iter()
                    .map(|a| {
                        let pattern = refine
                            .as_ref()
                            .filter(|_| !a.default)
                            .and_then(|eq| pattern_expr(a, span).map(|p| (eq.clone(), p)));
                        if let (Some((eq, p)), ExprKind::Var(v)) = (&pattern, &scrut.kind) {
                            self.refinements.push((v.clone(), p.clone(), eq.clone()));
                        }
                        let arm = self.arm(a, eqbind.as_deref(), bound);
                        if pattern.is_some() {
                            self.refinements.pop();
                        }
                        arm
                    })
                    .collect();
                ExprKind::Match {
                    form: *form,
                    generated: *generated,
                    scrut: Box::new(self.expr(scrut, bound)),
                    eqbind,
                    motive: motive.as_ref().map(|m| Box::new(self.expr(m, bound))),
                    arms,
                }
            }
            ExprKind::MatchCode {
                scrut,
                motive,
                arms,
            } => ExprKind::MatchCode {
                scrut: Box::new(self.expr(scrut, bound)),
                motive: motive.clone(),
                arms: arms.iter().map(|a| self.arm(a, None, bound)).collect(),
            },
            ExprKind::Dot {
                recv,
                name,
                args,
                named,
            } => ExprKind::Dot {
                recv: Box::new(self.expr(recv, bound)),
                name: name.clone(),
                args: args
                    .as_ref()
                    .map(|xs| xs.iter().map(|x| self.expr(x, bound)).collect()),
                named: named
                    .iter()
                    .map(|n| heather_syntax::NamedArg {
                        name: n.name.clone(),
                        name_span: n.name_span,
                        expr: self.expr(&n.expr, bound),
                        span: n.span,
                    })
                    .collect(),
            },
            ExprKind::Index { recv, idx } => ExprKind::Index {
                recv: Box::new(self.expr(recv, bound)),
                idx: Box::new(self.expr(idx, bound)),
            },
            ExprKind::RecordLit {
                name,
                tyargs,
                fields,
            } => ExprKind::RecordLit {
                name: name.clone(),
                tyargs: tyargs.clone(),
                fields: fields
                    .iter()
                    .map(|f| heather_syntax::RecordLitField {
                        name: f.name.clone(),
                        expr: self.expr(&f.expr, bound),
                        span: f.span,
                    })
                    .collect(),
            },
            ExprKind::Block(block) => {
                let n = bound.len();
                let stmts: Vec<Stmt> = block.stmts.iter().map(|s| self.stmt(s, bound)).collect();
                let result = self.expr(&block.result, bound);
                let ons = block
                    .ons
                    .iter()
                    .map(|o| heather_syntax::OnStmt {
                        target: o.target.clone(),
                        expr: self.expr(&o.expr, bound),
                        span: o.span,
                    })
                    .collect();
                bound.truncate(n);
                ExprKind::Block(Box::new(Block {
                    stmts,
                    result: Box::new(result),
                    ons,
                    span: block.span,
                }))
            }
            ExprKind::Quote(x) => ExprKind::Quote(Box::new(self.expr(x, bound))),
            ExprKind::Splice(x) => ExprKind::Splice(Box::new(self.expr(x, bound))),
            ExprKind::J {
                proof,
                motive,
                case,
            } => ExprKind::J {
                proof: Box::new(self.expr(proof, bound)),
                motive: Box::new(self.expr(motive, bound)),
                case: Box::new(self.expr(case, bound)),
            },
            leaf @ (ExprKind::Var(_)
            | ExprKind::OpSymbol { .. }
            | ExprKind::Univ { .. }
            | ExprKind::Num(_)
            | ExprKind::ArgSlot(_)
            | ExprKind::TyLit(_)
            | ExprKind::Refl
            | ExprKind::AutoRefl
            | ExprKind::Hole(_)) => leaf.clone(),
        };
        Expr { kind, span }
    }

    fn arm(&mut self, a: &Arm, eqbind: Option<&str>, bound: &mut Vec<String>) -> Arm {
        let n = bound.len();
        for p in &a.binders {
            pat_names(p, bound);
        }
        bound.extend(eqbind.map(str::to_string));
        let body = self.expr(&a.body, bound);
        bound.truncate(n);
        Arm {
            ctor: a.ctor.clone(),
            default: a.default,
            binders: a.binders.clone(),
            body,
            span: a.span,
        }
    }

    /// A statement, **extending** `bound` with what it binds (the caller
    /// truncates at the block's end).
    fn stmt(&mut self, s: &Stmt, bound: &mut Vec<String>) -> Stmt {
        match s {
            Stmt::Let {
                name,
                ty,
                expr,
                span,
            } => {
                let expr = self.expr(expr, bound);
                bound.push(name.clone());
                Stmt::Let {
                    name: name.clone(),
                    ty: ty.clone(),
                    expr,
                    span: *span,
                }
            }
            Stmt::LetRecord { fields, expr, span } => {
                let expr = self.expr(expr, bound);
                for f in fields {
                    pat_names(&f.pat, bound);
                }
                Stmt::LetRecord {
                    fields: fields.clone(),
                    expr,
                    span: *span,
                }
            }
            Stmt::LetCode { name, expr, span } => {
                let expr = self.expr(expr, bound);
                bound.push(name.clone());
                Stmt::LetCode {
                    name: name.clone(),
                    expr,
                    span: *span,
                }
            }
        }
    }
}

/// An arm's pattern as the expression it matches: `Succ(k)`, `Cons(h, t)`.
/// `None` for a pattern with no expression form (a named field).
fn pattern_expr(a: &Arm, span: Span) -> Option<Expr> {
    fn go(p: &Pat, span: Span) -> Option<Expr> {
        Some(match p {
            Pat::Var { name, .. } => Expr {
                kind: ExprKind::Var(name.clone()),
                span,
            },
            Pat::Ctor { name, args, .. } => Expr {
                kind: ExprKind::App {
                    head: Box::new(Expr {
                        kind: ExprKind::Var(name.clone()),
                        span,
                    }),
                    args: args.iter().map(|q| go(q, span)).collect::<Option<Vec<_>>>()?,
                    named: Vec::new(),
                    explicit: false,
                    goal_oriented: false,
                },
                span,
            },
            Pat::Named { .. } => return None,
        })
    }
    let args = a
        .binders
        .iter()
        .map(|p| go(p, span))
        .collect::<Option<Vec<_>>>()?;
    let head = Expr {
        kind: ExprKind::Var(a.ctor.clone()),
        span,
    };
    Some(if args.is_empty() {
        head
    } else {
        Expr {
            kind: ExprKind::App {
                head: Box::new(head),
                args,
                named: Vec::new(),
                explicit: false,
                goal_oriented: false,
            },
            span,
        }
    })
}

/// Does `e` mention the free variable `v`? Over the forms `subst` walks.
fn mentions(e: &Expr, v: &str) -> bool {
    let mut found = false;
    crate::surface::walk_expr(e, &mut |x| {
        if matches!(&x.kind, ExprKind::Var(n) if n == v) {
            found = true;
        }
    });
    found
}

fn pat_names(p: &Pat, out: &mut Vec<String>) {
    match p {
        Pat::Var { name, .. } => out.push(name.clone()),
        Pat::Ctor { args, .. } => args.iter().for_each(|a| pat_names(a, out)),
        Pat::Named { pat, .. } => pat_names(pat, out),
    }
}

/// `e[ȳ/x̄]`: the measure with each parameter name replaced by an argument
/// expression, stopping under a binder that shadows the name. Capture the
/// other way — an argument mentioning a name the measure binds — is not
/// avoided; a measure is a small expression over the parameters, and a
/// wrong substitution here yields an obligation the ih's domain refuses.
fn subst(e: &Expr, map: &[(&str, &Expr)], bound: &mut Vec<String>) -> Expr {
    let span = e.span;
    let go = |x: &Expr, bound: &mut Vec<String>| subst(x, map, bound);
    let kind = match &e.kind {
        ExprKind::Var(n) => {
            if !bound.iter().any(|b| b == n)
                && let Some((_, a)) = map.iter().find(|(p, _)| p == n)
            {
                return (*a).clone();
            }
            ExprKind::Var(n.clone())
        }
        ExprKind::App {
            head,
            args,
            named,
            explicit,
            goal_oriented,
        } => ExprKind::App {
            head: Box::new(go(head, bound)),
            args: args.iter().map(|a| go(a, bound)).collect(),
            named: named
                .iter()
                .map(|n| heather_syntax::NamedArg {
                    name: n.name.clone(),
                    name_span: n.name_span,
                    expr: go(&n.expr, bound),
                    span: n.span,
                })
                .collect(),
            explicit: *explicit,
            goal_oriented: *goal_oriented,
        },
        ExprKind::TyApp { head, args } => ExprKind::TyApp {
            head: Box::new(go(head, bound)),
            args: args.clone(),
        },
        ExprKind::Lam { binders, body } => {
            let n = bound.len();
            bound.extend(binders.iter().map(|b| b.name.clone()));
            let body = go(body, bound);
            bound.truncate(n);
            ExprKind::Lam {
                binders: binders.clone(),
                body: Box::new(body),
            }
        }
        ExprKind::Dot {
            recv,
            name,
            args,
            named,
        } => ExprKind::Dot {
            recv: Box::new(go(recv, bound)),
            name: name.clone(),
            args: args
                .as_ref()
                .map(|xs| xs.iter().map(|x| go(x, bound)).collect()),
            named: named
                .iter()
                .map(|n| heather_syntax::NamedArg {
                    name: n.name.clone(),
                    name_span: n.name_span,
                    expr: go(&n.expr, bound),
                    span: n.span,
                })
                .collect(),
        },
        ExprKind::Index { recv, idx } => ExprKind::Index {
            recv: Box::new(go(recv, bound)),
            idx: Box::new(go(idx, bound)),
        },
        ExprKind::Eq(a, b) => ExprKind::Eq(Box::new(go(a, bound)), Box::new(go(b, bound))),
        ExprKind::CollectionLit(xs) => {
            ExprKind::CollectionLit(xs.iter().map(|x| go(x, bound)).collect())
        }
        ExprKind::Match {
            form,
            generated,
            scrut,
            eqbind,
            motive,
            arms,
        } => ExprKind::Match {
            form: *form,
            generated: *generated,
            scrut: Box::new(go(scrut, bound)),
            eqbind: eqbind.clone(),
            motive: motive.as_ref().map(|m| Box::new(go(m, bound))),
            arms: arms
                .iter()
                .map(|a| {
                    let n = bound.len();
                    for p in &a.binders {
                        pat_names(p, bound);
                    }
                    bound.extend(eqbind.clone());
                    let body = go(&a.body, bound);
                    bound.truncate(n);
                    Arm {
                        ctor: a.ctor.clone(),
                        default: a.default,
                        binders: a.binders.clone(),
                        body,
                        span: a.span,
                    }
                })
                .collect(),
        },
        // A measure is an expression over the parameters; the remaining forms
        // either bind nothing to substitute under or are not measures anyone
        // writes. Left as they are.
        other => other.clone(),
    };
    Expr { kind, span }
}
