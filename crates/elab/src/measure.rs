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
//! …except that the three layers are **named**, not nested inline:
//! `f#body` is the `Succ` arm, `f#rec` is the eliminator, and `f` applies it
//! (`docs/decreases-unfolding-design.md` §2, which amends
//! `docs/termination-measures-design.md` §1/§5). The lifting is what makes the
//! unfolding companions of that document statable; nothing else changes, since
//! a `fn` is transparent and `f#rec(Succ k, …) ≡ f#body(k, f#rec(k), …)` is
//! `refl`.
//!
//! The wrapper is a written-motive `match` with the explicit-ih arm — two
//! features older than this one — and the parameters are re-bound under
//! their own names, so the body reads exactly as written. Each recursive
//! call owes one obligation, `e[ȳ] < e`, a goal hole named `decN` in source
//! order; it is discharged by `on ?decN := …`, and defaults to `omega` where
//! no `on` names it.
//!
//! The obligation is not spelled at the call: it is **lifted** into a
//! declaration of its own, `f#obl_N`, over the binders its statement names
//! (`docs/decreases-unfolding-design.md` §4). `f#body` and both unfolding
//! companions then reference the same opaque `f#obl_N(…)`, so the three
//! spellings of a self-call are identical by construction — which is what an
//! `omega`-defaulted obligation needs, since `omega` reconstructs its
//! certificate against the local context and the three contexts differ.
//!
//! Nothing here is trusted. The rewrite reads names — the declaration's own
//! name for a self-call, the parameters' names for the measure's arguments
//! — and where a name misleads it the emitted term fails to check: the ih's
//! hypothesis binder is at the *elaborated* measure, so a wrong obligation
//! type is refused where the call is written, never accepted.

use heather_syntax::{
    Arm, Block, Decl, DeclKind, Expr, ExprKind, LamBinder, MatchForm, OnStmt, OnTarget, Param,
    ParamOrigin, Pat, Span, Stmt, Ty, TyKind,
};

use crate::{R, err};

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

/// One generated declaration and the obligations its own body owes.
pub(crate) struct Lowered {
    pub(crate) decl: Decl,
    pub(crate) obligations: Obligations,
}

/// What a `decreases` declaration lowers to: the lifted obligations of §4
/// first — they are what the rest references — then the family of §2.
pub(crate) struct Family {
    pub(crate) obligations: Vec<Lowered>,
    pub(crate) decls: Vec<Lowered>,
}

/// The one thing the generator cannot read off the surface: what a
/// constructor pattern's binders are typed at. A lifted obligation quantifies
/// the arm binders its statement names, and a declaration parameter needs a
/// written type; the elaborator has the constructor's stored field types and
/// answers here (`docs/decreases-unfolding-design.md` §4).
///
/// `None` is an honest decline — the site is then not lifted, and `f` falls
/// back to the obligation spelled at the call as it was before.
pub(crate) trait BinderTys {
    fn ctor_fields(&self, scrut: &Ty, ctor: &str) -> Option<Vec<Ty>>;
}

/// A binder in scope during the walk, with the surface type a lifted
/// obligation may quantify it at — `None` where the walk cannot name it (an
/// unannotated `let`, a pattern [`BinderTys`] declines).
#[derive(Clone)]
struct Binder {
    name: String,
    ty: Option<Ty>,
}

/// A stored field type at the scrutinee's type arguments: type parameters are
/// monomorphized, so instantiation is a substitution on the surface type. A
/// shape this does not walk is left alone; a wrong instantiation costs a
/// refused `f#obl_N` and the un-lifted fallback, never a wrong proof.
pub(crate) fn instantiate_ty(t: &Ty, m: &[(String, Ty)]) -> Ty {
    let span = t.span;
    let go = |x: &Ty| instantiate_ty(x, m);
    let kind = match &t.kind {
        TyKind::Named { name, args } if args.is_empty() => {
            if let Some((_, ty)) = m.iter().find(|(p, _)| p == name) {
                return ty.clone();
            }
            TyKind::Named {
                name: name.clone(),
                args: Vec::new(),
            }
        }
        TyKind::Named { name, args } => TyKind::Named {
            name: name.clone(),
            args: args.iter().map(go).collect(),
        },
        TyKind::Fn {
            binder,
            implicit,
            dom,
            cod,
        } => TyKind::Fn {
            binder: binder.clone(),
            implicit: *implicit,
            dom: Box::new(go(dom)),
            cod: Box::new(go(cod)),
        },
        TyKind::Vec { elem, len } => TyKind::Vec {
            elem: Box::new(go(elem)),
            len: len.clone(),
        },
        TyKind::Squash(x) => TyKind::Squash(Box::new(go(x))),
        other => other.clone(),
    };
    Ty { kind, span }
}

/// `f#body` — the rewritten `Succ` arm, lifted out of the eliminator.
pub(crate) fn body_name(name: &str) -> String {
    format!("{name}#body")
}

/// `f#obl_N` — one self-call site's obligation, lifted out of the body (§4).
pub(crate) fn obl_name(name: &str, site: usize) -> String {
    format!("{name}#obl_{site}")
}

/// `f#rec` — the eliminator on the bound, lifted out of `f`.
pub(crate) fn rec_name(name: &str) -> String {
    format!("{name}#rec")
}

fn var(name: &str, span: Span) -> Expr {
    Expr {
        kind: ExprKind::Var(name.to_string()),
        span,
    }
}

fn app(head: Expr, args: Vec<Expr>, span: Span) -> Expr {
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
}

fn of_expr(e: Expr) -> Ty {
    let span = e.span;
    Ty {
        kind: TyKind::OfExpr(Box::new(e)),
        span,
    }
}

/// `nat::Lt(a, b)` as a type.
fn lt_ty(a: Expr, b: Expr, span: Span) -> Ty {
    of_expr(app(var("nat::Lt", span), vec![a, b], span))
}

fn arrow(binder: Option<String>, dom: Ty, cod: Ty, span: Span) -> Ty {
    Ty {
        kind: TyKind::Fn {
            binder,
            implicit: false,
            dom: Box::new(dom),
            cod: Box::new(cod),
        },
        span,
    }
}

/// `(x̄) -> cod`, the declaration's value parameters quantified explicitly —
/// the shape the motive already had before the lifting.
fn pi_over(params: &[Param], cod: Ty, span: Span) -> Ty {
    let mut ty = cod;
    for p in params.iter().rev() {
        ty = arrow(Some(p.name.clone()), p.ty.clone(), ty, span);
    }
    ty
}

fn param(name: &str, ty: Ty, span: Span) -> Param {
    Param {
        name: name.to_string(),
        ty,
        implicit: false,
        is_self: false,
        solver: None,
        origin: ParamOrigin::Written,
        symbol: None,
        span,
    }
}

/// The declaration's value parameters as **explicit** binders: a companion
/// quantifies an implicit parameter the way the motive always has, and its
/// call sites pass every argument positionally.
fn value_params(decl: &Decl) -> Vec<Param> {
    decl.params
        .iter()
        .map(|p| Param {
            implicit: false,
            is_self: false,
            solver: None,
            symbol: None,
            ..p.clone()
        })
        .collect()
}

/// A reference to a companion with the declaration's type parameters pinned
/// (`g<A, B>`) rather than left to unification, since a companion's leading
/// arguments are `Nat`s that mention none of them.
fn companion_ref(decl: &Decl, name: &str, span: Span) -> Expr {
    let head = var(name, span);
    if decl.tyvars.is_empty() {
        return head;
    }
    Expr {
        kind: ExprKind::TyApp {
            head: Box::new(head),
            args: decl
                .tyvars
                .iter()
                .map(|t| Ty {
                    kind: TyKind::Named {
                        name: t.name.clone(),
                        args: Vec::new(),
                    },
                    span,
                })
                .collect(),
        },
        span,
    }
}

/// A companion declaration: the writer's type parameters, `params`, and a
/// body with no `on`s unless `ons` says otherwise.
fn companion(decl: &Decl, name: String, params: Vec<Param>, result: Ty, body: Block) -> Decl {
    Decl {
        kind: decl.kind,
        is_meta: false,
        elaborates: None,
        name,
        tyvars: decl.tyvars.clone(),
        params,
        result,
        decreases: None,
        body,
        span: decl.span,
    }
}

fn block(result: Expr, span: Span) -> Block {
    Block {
        stmts: Vec::new(),
        result: Box::new(result),
        ons: Vec::new(),
        span,
    }
}

/// Whether the obligations of a body may be lifted at all (§4): the plan
/// rests on each obligation being a *named* goal that one generated
/// declaration discharges, so a body that discharges goals by statement
/// (`on _: P := …`) keeps the obligations where they were.
fn liftable(decl: &Decl) -> bool {
    decl.body
        .ons
        .iter()
        .all(|o| matches!(o.target, OnTarget::Name(_)))
}

/// Lower `decl`, whose body recurses under `decreases measure`, into the
/// lifted obligations of §4 and the `f#body` / `f#rec` / `f` family (module
/// docs, and `docs/decreases-unfolding-design.md` §2). `name` is the
/// declaration's self-name (the base name, for a member); `omega_available`
/// says whether an obligation nobody discharges by hand may default to
/// `omega`; `lift` is cleared to re-lower a declaration whose lifted
/// obligations the checker refused, which is the un-lifted spelling this
/// round replaced.
///
/// Purely syntactic: everything it builds is surface the writer could have
/// written, and a mis-generated program is refused by the ordinary checker.
pub(crate) fn lower(
    decl: &Decl,
    name: &str,
    measure: &Expr,
    omega_available: bool,
    tys: &dyn BinderTys,
    lift: bool,
) -> R<Family> {
    let span = measure.span;
    let params = value_params(decl);
    let refs: Vec<&Param> = decl.params.iter().collect();
    let mut state = Rewrite {
        decl,
        name,
        params: &refs,
        measure,
        ons: &decl.body.ons,
        omega_available,
        tys,
        lift: lift && liftable(decl),
        next: 1,
        eqs: 0,
        refinements: Vec::new(),
        scope: scope_of(decl),
        sites: Vec::new(),
        obls: Vec::new(),
        error: None,
    };
    let stmts: Vec<Stmt> = decl.body.stmts.iter().map(|s| state.stmt(s)).collect();
    let result = state.expr(&decl.body.result);
    if let Some(error) = state.error.take() {
        return Err(error);
    }
    let sites = state.sites;
    let obligations: Vec<Lowered> = state.obls.into_iter().flatten().collect();
    // A lifted obligation takes its `on` with it; every other discharge —
    // including one whose site could not be lifted — stays on the body.
    let moved: Vec<&str> = obligations
        .iter()
        .flat_map(|o| o.obligations.sites.iter().map(|(_, h, _)| h.as_str()))
        .collect();
    let body_ons = remaining_ons(&decl.body.ons, &moved);

    // `f#body(__dec_k, __dec_ih, x̄, __dec_h) -> T`, the `Succ` arm.
    let ih_ty = pi_over(
        &params,
        arrow(
            None,
            lt_ty(measure.clone(), var(K, span), span),
            decl.result.clone(),
            span,
        ),
        span,
    );
    let h_ty = lt_ty(
        measure.clone(),
        app(var("Succ", span), vec![var(K, span)], span),
        span,
    );
    let mut body_params = vec![
        param(
            K,
            Ty {
                kind: TyKind::Nat,
                span,
            },
            span,
        ),
        param(IH, ih_ty, span),
    ];
    body_params.extend(params.iter().cloned());
    body_params.push(param(H, h_ty, span));
    let body_decl = companion(
        decl,
        body_name(&decl.name),
        body_params,
        decl.result.clone(),
        Block {
            stmts,
            result: Box::new(result),
            // The writer's discharges follow their obligations into the
            // declaration that now raises them.
            ons: body_ons,
            span: decl.body.span,
        },
    );

    // `f#rec(__dec_z) -> (x̄) -> nat::Lt(e, __dec_z) -> T`, the eliminator.
    let motive_ty = pi_over(
        &params,
        arrow(
            None,
            lt_ty(measure.clone(), var(Z, span), span),
            decl.result.clone(),
            span,
        ),
        span,
    );
    let binder = |n: &str| LamBinder {
        name: n.to_string(),
        ty: None,
        implicit: false,
        span,
    };
    // λ x̄ __dec_h => e
    let lam = |body: Expr| Expr {
        kind: ExprKind::Lam {
            binders: params
                .iter()
                .map(|p| p.name.as_str())
                .chain([H])
                .map(binder)
                .collect(),
            body: Box::new(body),
        },
        span,
    };
    let motive = Expr {
        kind: ExprKind::Lam {
            binders: vec![binder(Z)],
            body: Box::new(Expr {
                kind: ExprKind::TyLit(Box::new(motive_ty.clone())),
                span,
            }),
        },
        span,
    };
    let absurd = Expr {
        kind: ExprKind::Match {
            form: MatchForm::Match,
            generated: false,
            scrut: Box::new(var(H, span)),
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
    let mut arm_args = vec![var(K, span), var(IH, span)];
    arm_args.extend(params.iter().map(|p| var(&p.name, span)));
    arm_args.push(var(H, span));
    let elim = Expr {
        kind: ExprKind::Match {
            form: MatchForm::Match,
            generated: false,
            scrut: Box::new(var(Z, span)),
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
                    body: lam(app(
                        companion_ref(decl, &body_name(&decl.name), span),
                        arm_args,
                        span,
                    )),
                    span: decl.body.span,
                },
            ],
        },
        span,
    };
    let rec_decl = companion(
        decl,
        rec_name(&decl.name),
        vec![param(
            Z,
            Ty {
                kind: TyKind::Nat,
                span,
            },
            span,
        )],
        motive_ty,
        block(elim, decl.body.span),
    );

    // `f(x̄) = f#rec(Succ(e), x̄, nat::lt_succ_self(e))`.
    let mut call_args = vec![app(var("Succ", span), vec![measure.clone()], span)];
    call_args.extend(decl.params.iter().map(|p| var(&p.name, span)));
    call_args.push(app(
        var("nat::lt_succ_self", span),
        vec![measure.clone()],
        span,
    ));
    let f_decl = Decl {
        decreases: None,
        body: block(
            app(
                companion_ref(decl, &rec_name(&decl.name), span),
                call_args,
                span,
            ),
            decl.body.span,
        ),
        ..decl.clone()
    };

    Ok(Family {
        obligations,
        decls: vec![
            Lowered {
                decl: body_decl,
                obligations: Obligations { sites },
            },
            Lowered {
                decl: rec_decl,
                obligations: Obligations { sites: Vec::new() },
            },
            Lowered {
                decl: f_decl,
                obligations: Obligations { sites: Vec::new() },
            },
        ],
    })
}

/// The discharges that stay where they were written: everything but the
/// `on ?decN` of a site whose obligation moved into `f#obl_N` (§4).
fn remaining_ons(ons: &[OnStmt], moved: &[&str]) -> Vec<OnStmt> {
    ons.iter()
        .filter(|o| !matches!(&o.target, OnTarget::Name(n) if moved.contains(&n.as_str())))
        .cloned()
        .collect()
}

/// The declaration's own binders, the seed of the walk's scope: a lifted
/// obligation quantifies these under their own names.
fn scope_of(decl: &Decl) -> Vec<Binder> {
    decl.params
        .iter()
        .map(|p| Binder {
            name: p.name.clone(),
            ty: Some(p.ty.clone()),
        })
        .collect()
}

/// The declaration-shape guards `decreases` owes before anything is built:
/// the forms whose lowering has no meaning rather than a wrong one.
pub(crate) fn check_shape(decl: &Decl, measure: &Expr) -> R<()> {
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
    Ok(())
}

/// The self-call rewrite (module docs), threaded through a surface walk that
/// tracks the names bound around each node so a shadowed parameter or
/// declaration name is left alone.
struct Rewrite<'a> {
    decl: &'a Decl,
    name: &'a str,
    params: &'a [&'a heather_syntax::Param],
    measure: &'a Expr,
    ons: &'a [OnStmt],
    /// Whether an obligation nobody discharges by hand may default to `omega`.
    omega_available: bool,
    tys: &'a dyn BinderTys,
    /// Whether an obligation is lifted into `f#obl_N` (§4).
    lift: bool,
    next: usize,
    eqs: usize,
    /// What the enclosing `match`es have established about the measure's
    /// variables, outermost first: `(variable, the arm's pattern as an
    /// expression, the equation binder that says so)`. An obligation is
    /// stated at the measure with all of these applied — the statement a
    /// reader expects inside the arm — and transported back through the
    /// equations to the ih's own hypothesis (§3 of the design).
    refinements: Vec<(String, Expr, String)>,
    /// The binders in scope at the node being walked, outermost first.
    scope: Vec<Binder>,
    sites: Vec<(Span, String, String)>,
    /// One entry per site in source order: the lifted `f#obl_N`, or `None`
    /// where the site's obligation stayed at the call (§4).
    obls: Vec<Option<Lowered>>,
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
        let acc = self.obligation(&at_args, span);
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

    /// The obligation this self-call site owes, as the body will spell it: a
    /// reference to the site's lifted `f#obl_N` (§4), stated at the
    /// **refined** measure and transported back to the ih's own statement
    /// through the enclosing arms' equations.
    ///
    /// Separate from [`Self::self_call`] because the companions re-emit
    /// exactly this term — same numbering, same reference — under their own
    /// bound and hypothesis, which is what makes the three spellings of a
    /// self-call identical.
    fn obligation(&mut self, at_args: &Expr, span: Span) -> Expr {
        // The measure as the enclosing arms know it: `e[Succ(k)/n]` inside
        // `match n { Succ(k) => … }`, and so on down.
        let stages = self.stages();
        let refined = stages.last().expect("stage 0 is the measure itself").clone();
        let site = self.next;
        let hole = format!("dec{site}");
        self.next += 1;
        let text = format!(
            "{} < {}",
            crate::traits::render_expr(at_args),
            crate::traits::render_expr(&refined)
        );
        let on = self
            .ons
            .iter()
            .find(|o| matches!(&o.target, OnTarget::Name(n) if *n == hole))
            .cloned();
        // What the obligation is proved by, wherever it is raised: the
        // writer's hole where an `on` names it, `omega` where the closer is
        // available, and the bare hole otherwise (reported with its
        // statement, `docs/termination-measures-design.md` §2).
        let closer = if on.is_some() || !self.omega_available {
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
        let lifted = self
            .lift
            .then(|| self.lift_obligation(site, &hole, &text, at_args, &refined, on, &closer, span))
            .flatten();
        let obligation = match lifted {
            Some(reference) => reference,
            None => {
                self.obls.push(None);
                closer
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
        let lt = |a: Expr, b: Expr| app(var("nat::Lt"), vec![a, b]);
        // Transport the obligation back from the refined measure to the
        // measure the ih's hypothesis is stated at, one equation at a time:
        // `j(sym(eq_i), λ y _ => e[ȳ] < e_{i-1}[y/v_i], acc)` turns a proof at
        // `e_i = e_{i-1}[pat_i/v_i]` into one at `e_{i-1}`.
        let mut acc = obligation;
        for (i, (v, _, eq)) in self.refinements.iter().enumerate().rev() {
            let below = &stages[i];
            let y = format!("__dec_y{i}");
            let at_y = subst(below, &[(v.as_str(), &var(&y))], &mut Vec::new());
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
        acc
    }

    /// Lift one site's obligation into `f#obl_N` and return the reference that
    /// replaces it (§4). The declaration quantifies exactly the binders in
    /// scope its statement — or the writer's `on` — names, under their own
    /// names and in binding order, so that both the body and the companions
    /// spell the call `f#obl_N(ȳ)` with the same arguments.
    ///
    /// `None` where a binder the statement names has no type this walk can
    /// write: the obligation then stays at the call, and the companions
    /// decline the body.
    #[allow(clippy::too_many_arguments)]
    fn lift_obligation(
        &mut self,
        site: usize,
        hole: &str,
        text: &str,
        at_args: &Expr,
        refined: &Expr,
        on: Option<OnStmt>,
        closer: &Expr,
        span: Span,
    ) -> Option<Expr> {
        let mut params = Vec::new();
        let mut args = Vec::new();
        for (i, b) in self.scope.iter().enumerate() {
            // A name re-bound further in is that name's meaning here.
            if self.scope[i + 1..].iter().any(|c| c.name == b.name) {
                continue;
            }
            let named = mentions(at_args, &b.name)
                || mentions(refined, &b.name)
                || on.as_ref().is_some_and(|o| mentions(&o.expr, &b.name));
            if !named {
                continue;
            }
            params.push(param(&b.name, b.ty.clone()?, span));
            args.push(var(&b.name, span));
        }
        let name = obl_name(&self.decl.name, site);
        let decl = Decl {
            kind: DeclKind::Theorem,
            is_meta: false,
            elaborates: None,
            name: name.clone(),
            tyvars: self.decl.tyvars.clone(),
            params,
            result: lt_ty(at_args.clone(), refined.clone(), span),
            decreases: None,
            body: Block {
                stmts: Vec::new(),
                result: Box::new(closer.clone()),
                ons: on.into_iter().collect(),
                span,
            },
            span: self.decl.span,
        };
        self.obls.push(Some(Lowered {
            decl,
            // The site travels with the declaration, so an `omega` failure is
            // still reworded at the call it belongs to.
            obligations: Obligations {
                sites: vec![(span, hole.to_string(), text.to_string())],
            },
        }));
        let head = companion_ref(self.decl, &name, span);
        Some(if args.is_empty() {
            head
        } else {
            app(head, args, span)
        })
    }

    /// The surface type of a scrutinee, where it is a binder the walk knows.
    fn scrut_ty(&self, e: &Expr) -> Option<Ty> {
        let ExprKind::Var(v) = &e.kind else {
            return None;
        };
        self.scope.iter().rev().find(|b| &b.name == v)?.ty.clone()
    }

    /// Bind one arm pattern, typing its binders from the scrutinee's type
    /// through [`BinderTys`]; a position the oracle declines binds untyped,
    /// which only costs the sites whose statements name it their lifting.
    fn bind_pat(&mut self, p: &Pat, ty: Option<&Ty>) {
        match p {
            Pat::Var { name, .. } => self.scope.push(Binder {
                name: name.clone(),
                ty: ty.cloned(),
            }),
            Pat::Ctor { name, args, .. } => {
                let fields = ty
                    .and_then(|t| self.tys.ctor_fields(t, name))
                    .filter(|f| f.len() == args.len());
                for (i, q) in args.iter().enumerate() {
                    self.bind_pat(q, fields.as_ref().map(|f| &f[i]));
                }
            }
            Pat::Named { pat, .. } => self.bind_pat(pat, None),
        }
    }

    /// The binders an arm introduces, typed at the scrutinee's type.
    fn bind_arm(&mut self, a: &Arm, scrut: Option<&Ty>) {
        let fields = scrut
            .and_then(|t| self.tys.ctor_fields(t, &a.ctor))
            .filter(|f| f.len() == a.binders.len());
        for (i, p) in a.binders.iter().enumerate() {
            self.bind_pat(p, fields.as_ref().map(|f| &f[i]));
        }
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

    fn expr(&mut self, e: &Expr) -> Expr {
        let span = e.span;
        let kind = match &e.kind {
            ExprKind::App {
                head,
                args,
                named,
                explicit,
                goal_oriented,
            } => {
                let args: Vec<Expr> = args.iter().map(|a| self.expr(a)).collect();
                let named: Vec<heather_syntax::NamedArg> = named
                    .iter()
                    .map(|n| heather_syntax::NamedArg {
                        name: n.name.clone(),
                        name_span: n.name_span,
                        expr: self.expr(&n.expr),
                        span: n.span,
                    })
                    .collect();
                let callee = match &head.kind {
                    ExprKind::TyApp { head, .. } => &head.kind,
                    other => other,
                };
                if matches!(callee, ExprKind::Var(n) if n == self.name)
                    && !self.scope.iter().any(|b| b.name == self.name)
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
                    head: Box::new(self.expr(head)),
                    args,
                    named,
                    explicit: *explicit,
                    goal_oriented: *goal_oriented,
                }
            }
            ExprKind::TyApp { head, args } => ExprKind::TyApp {
                head: Box::new(self.expr(head)),
                args: args.clone(),
            },
            ExprKind::Lam { binders, body } => {
                let n = self.scope.len();
                self.scope.extend(binders.iter().map(|b| Binder { name: b.name.clone(), ty: b.ty.clone() }));
                let body = self.expr(body);
                self.scope.truncate(n);
                ExprKind::Lam {
                    binders: binders.clone(),
                    body: Box::new(body),
                }
            }
            ExprKind::CollectionLit(xs) => {
                ExprKind::CollectionLit(xs.iter().map(|x| self.expr(x)).collect())
            }
            ExprKind::Eq(a, b) => {
                ExprKind::Eq(Box::new(self.expr(a)), Box::new(self.expr(b)))
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
                let scrut_ty = self.scrut_ty(scrut);
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
                        let arm = self.arm(a, eqbind.as_deref(), scrut_ty.as_ref());
                        if pattern.is_some() {
                            self.refinements.pop();
                        }
                        arm
                    })
                    .collect();
                ExprKind::Match {
                    form: *form,
                    generated: *generated,
                    scrut: Box::new(self.expr(scrut)),
                    eqbind,
                    motive: motive.as_ref().map(|m| Box::new(self.expr(m))),
                    arms,
                }
            }
            ExprKind::MatchCode {
                scrut,
                motive,
                arms,
            } => ExprKind::MatchCode {
                scrut: Box::new(self.expr(scrut)),
                motive: motive.clone(),
                arms: arms.iter().map(|a| self.arm(a, None, None)).collect(),
            },
            ExprKind::Dot {
                recv,
                name,
                args,
                named,
            } => ExprKind::Dot {
                recv: Box::new(self.expr(recv)),
                name: name.clone(),
                args: args
                    .as_ref()
                    .map(|xs| xs.iter().map(|x| self.expr(x)).collect()),
                named: named
                    .iter()
                    .map(|n| heather_syntax::NamedArg {
                        name: n.name.clone(),
                        name_span: n.name_span,
                        expr: self.expr(&n.expr),
                        span: n.span,
                    })
                    .collect(),
            },
            ExprKind::Index { recv, idx } => ExprKind::Index {
                recv: Box::new(self.expr(recv)),
                idx: Box::new(self.expr(idx)),
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
                        expr: self.expr(&f.expr),
                        span: f.span,
                    })
                    .collect(),
            },
            ExprKind::Block(block) => {
                let n = self.scope.len();
                let stmts: Vec<Stmt> = block.stmts.iter().map(|s| self.stmt(s)).collect();
                let result = self.expr(&block.result);
                let ons = block
                    .ons
                    .iter()
                    .map(|o| heather_syntax::OnStmt {
                        target: o.target.clone(),
                        expr: self.expr(&o.expr),
                        span: o.span,
                    })
                    .collect();
                self.scope.truncate(n);
                ExprKind::Block(Box::new(Block {
                    stmts,
                    result: Box::new(result),
                    ons,
                    span: block.span,
                }))
            }
            ExprKind::Quote(x) => ExprKind::Quote(Box::new(self.expr(x))),
            ExprKind::Splice(x) => ExprKind::Splice(Box::new(self.expr(x))),
            ExprKind::J {
                proof,
                motive,
                case,
            } => ExprKind::J {
                proof: Box::new(self.expr(proof)),
                motive: Box::new(self.expr(motive)),
                case: Box::new(self.expr(case)),
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

    fn arm(&mut self, a: &Arm, eqbind: Option<&str>, scrut: Option<&Ty>) -> Arm {
        let n = self.scope.len();
        self.bind_arm(a, scrut);
        self.scope.extend(eqbind.map(|e| Binder {
            name: e.to_string(),
            ty: None,
        }));
        let body = self.expr(&a.body);
        self.scope.truncate(n);
        Arm {
            ctor: a.ctor.clone(),
            default: a.default,
            binders: a.binders.clone(),
            body,
            span: a.span,
        }
    }

    /// A statement, **extending** the scope with what it binds (the caller
    /// truncates at the block's end).
    fn stmt(&mut self, s: &Stmt) -> Stmt {
        match s {
            Stmt::Let {
                name,
                ty,
                expr,
                span,
            } => {
                let expr = self.expr(expr);
                // An annotated `let` types its binder; an inferred one does
                // not, and a site whose statement names it is not lifted.
                self.scope.push(Binder {
                    name: name.clone(),
                    ty: ty.clone(),
                });
                Stmt::Let {
                    name: name.clone(),
                    ty: ty.clone(),
                    expr,
                    span: *span,
                }
            }
            Stmt::LetRecord { fields, expr, span } => {
                let expr = self.expr(expr);
                for f in fields {
                    self.bind_pat(&f.pat, None);
                }
                Stmt::LetRecord {
                    fields: fields.clone(),
                    expr,
                    span: *span,
                }
            }
            Stmt::LetCode { name, expr, span } => {
                let expr = self.expr(expr);
                self.scope.push(Binder {
                    name: name.clone(),
                    ty: None,
                });
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
        // `j` and blocks are not measure shapes, but the companions of
        // `docs/decreases-unfolding-design.md` §4 push substitutions through
        // obligation *proofs*, which are exactly these two.
        ExprKind::J {
            proof,
            motive,
            case,
        } => ExprKind::J {
            proof: Box::new(go(proof, bound)),
            motive: Box::new(go(motive, bound)),
            case: Box::new(go(case, bound)),
        },
        ExprKind::Block(block) => {
            let n = bound.len();
            let mut stmts = Vec::new();
            for st in &block.stmts {
                match st {
                    Stmt::Let {
                        name,
                        ty,
                        expr,
                        span,
                    } => {
                        let expr = go(expr, bound);
                        bound.push(name.clone());
                        stmts.push(Stmt::Let {
                            name: name.clone(),
                            ty: ty.clone(),
                            expr,
                            span: *span,
                        });
                    }
                    // Not substituted into, but what they bind still shadows.
                    Stmt::LetRecord { fields, .. } => {
                        for f in fields {
                            pat_names(&f.pat, bound);
                        }
                        stmts.push(st.clone());
                    }
                    Stmt::LetCode { name, .. } => {
                        bound.push(name.clone());
                        stmts.push(st.clone());
                    }
                }
            }
            let result = go(&block.result, bound);
            bound.truncate(n);
            ExprKind::Block(Box::new(Block {
                stmts,
                result: Box::new(result),
                ons: block.ons.clone(),
                span: block.span,
            }))
        }
        // A measure is an expression over the parameters; the remaining forms
        // either bind nothing to substitute under or are not measures anyone
        // writes. Left as they are.
        other => other.clone(),
    };
    Expr { kind, span }
}

// -- the unfolding companions -------------------------------------------------
//
// `docs/decreases-unfolding-design.md` §3–§6: a congruence proof over the
// body's own structure, with the self-call sites as its leaves, generated
// twice — once relating the arm to itself under two induction hypotheses
// (`f#ext`), once relating `f` to its body as written (`f_unfold`).

const A: &str = "__dec_a";
const B: &str = "__dec_b";
const G1: &str = "__dec_g1";
const G2: &str = "__dec_g2";
const HG: &str = "__dec_hg";
const H1: &str = "__dec_h1";
const H2: &str = "__dec_h2";
const P: &str = "__dec_p";
const W: &str = "__dec_w";

/// `f#ext` — the arm is extensional in its induction hypothesis.
pub(crate) fn ext_name(name: &str) -> String {
    format!("{name}#ext")
}

/// `f#irrel` — the recursor does not depend on which bound it was given.
pub(crate) fn irrel_name(name: &str) -> String {
    format!("{name}#irrel")
}

/// `f_unfold` — the artifact users cite, and so an ordinary name (§2).
pub(crate) fn unfold_name(name: &str) -> String {
    format!("{name}_unfold")
}

fn eq_ty(a: Expr, b: Expr, span: Span) -> Ty {
    Ty {
        kind: TyKind::Eq(Box::new(a), Box::new(b)),
        span,
    }
}

fn eq_expr(a: Expr, b: Expr, span: Span) -> Expr {
    Expr {
        kind: ExprKind::Eq(Box::new(a), Box::new(b)),
        span,
    }
}

fn lam(binders: &[&str], body: Expr, span: Span) -> Expr {
    Expr {
        kind: ExprKind::Lam {
            binders: binders
                .iter()
                .map(|n| LamBinder {
                    name: (*n).to_string(),
                    ty: None,
                    implicit: false,
                    span,
                })
                .collect(),
            body: Box::new(body),
        },
        span,
    }
}

fn ty_lit(ty: Ty, span: Span) -> Expr {
    Expr {
        kind: ExprKind::TyLit(Box::new(ty)),
        span,
    }
}

/// `(n₁: T₁) -> … -> cod`.
fn pi(binders: Vec<(&str, Ty)>, cod: Ty, span: Span) -> Ty {
    let mut ty = cod;
    for (n, dom) in binders.into_iter().rev() {
        ty = arrow(Some(n.to_string()), dom, ty, span);
    }
    ty
}

fn succ(e: Expr, span: Span) -> Expr {
    app(var("Succ", span), vec![e], span)
}

/// Which of the two companions a walk is generating: they differ only in how
/// the right-hand side is rendered and in what closes a self-call leaf
/// (§3's table).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Ext,
    Unfold,
}

/// The re-spelling walk (§3): a proof of `lhs = rhs` over the body's own
/// structure. `lhs`/`rhs` come back with the proof because a congruence step
/// one level up has to spell both sides of the argument it transports.
struct Triple {
    lhs: Expr,
    rhs: Expr,
    proof: Expr,
}

struct Respell<'a> {
    /// The body rewrite, driven in lockstep so that each self-call's
    /// obligation is *re-emitted* exactly as `f#body` spells it (§4) — same
    /// numbering, same hole name, same transport chain.
    rw: Rewrite<'a>,
    mode: Mode,
    decl: &'a Decl,
    /// The body as written, for `f_unfold`'s right-hand side.
    source: &'a Expr,
    /// What the enclosing arms substituted, outermost first, applied in order.
    sigma: Vec<(String, Expr)>,
    /// The bound hypotheses the anchors are currently at: `[h1, h2]` for
    /// `f#ext`, `[lt_succ_self(e)]` — then the generalized binder — for
    /// `f_unfold`.
    hyps: Vec<Expr>,
    /// `let`s owed by the arm being walked: the convoy equations at `refl`
    /// and the obligations, bound once and used on both sides (§4).
    lets: Vec<Stmt>,
    fresh: usize,
    span: Span,
}

impl Respell<'_> {
    fn sigma_apply(&self, e: &Expr) -> Expr {
        self.sigma_apply_ext(e, None)
    }

    /// `σ(e)`, optionally with one more substitution appended — the motive's
    /// abstraction of the scrutinee.
    fn sigma_apply_ext(&self, e: &Expr, ext: Option<(&str, &Expr)>) -> Expr {
        let mut out = e.clone();
        for (v, pat) in &self.sigma {
            out = subst(&out, &[(v.as_str(), pat)], &mut Vec::new());
        }
        if let Some((v, pat)) = ext {
            out = subst(&out, &[(v, pat)], &mut Vec::new());
        }
        out
    }

    fn args(&self, ext: Option<(&str, &Expr)>) -> Vec<Expr> {
        self.rw
            .params
            .iter()
            .map(|p| self.sigma_apply_ext(&var(&p.name, self.span), ext))
            .collect()
    }

    fn measure_at(&self, ext: Option<(&str, &Expr)>) -> Expr {
        self.sigma_apply_ext(self.rw.measure, ext)
    }

    fn cref(&self, name: &str) -> Expr {
        companion_ref(self.decl, name, self.span)
    }

    /// The left anchor: `f#body(a, g1, x̄, h1)`, or `f#rec(Succ(e), x̄, p)`.
    fn anchor_l(&self, ext: Option<(&str, &Expr)>, hyp: &Expr) -> Expr {
        let span = self.span;
        let mut args = match self.mode {
            Mode::Ext => vec![var(A, span), var(G1, span)],
            Mode::Unfold => vec![succ(self.measure_at(ext), span)],
        };
        args.extend(self.args(ext));
        args.push(hyp.clone());
        let head = match self.mode {
            Mode::Ext => body_name(&self.decl.name),
            Mode::Unfold => rec_name(&self.decl.name),
        };
        app(self.cref(&head), args, span)
    }

    /// The right anchor: `f#body(b, g2, x̄, h2)`, or the body **as written**
    /// with the enclosing arms' patterns substituted (§5 — no `__dec_…`
    /// binder reaches it).
    fn anchor_r(&self, ext: Option<(&str, &Expr)>, hyp: &Expr) -> Expr {
        let span = self.span;
        match self.mode {
            Mode::Ext => {
                let mut args = vec![var(B, span), var(G2, span)];
                args.extend(self.args(ext));
                args.push(hyp.clone());
                app(self.cref(&body_name(&self.decl.name)), args, span)
            }
            Mode::Unfold => self.sigma_apply_ext(self.source, ext),
        }
    }

    /// The generalized bound hypotheses at measure `m`, in `hyps` order.
    fn hyp_binders(&self, m: &Expr) -> Vec<(&'static str, Ty)> {
        let span = self.span;
        match self.mode {
            Mode::Ext => vec![
                (H1, lt_ty(m.clone(), succ(var(A, span), span), span)),
                (H2, lt_ty(m.clone(), succ(var(B, span), span), span)),
            ],
            Mode::Unfold => vec![(P, lt_ty(m.clone(), succ(m.clone(), span), span))],
        }
    }

    fn goal(&self, ext: Option<(&str, &Expr)>, hyps: &[Expr]) -> Ty {
        eq_ty(
            self.anchor_l(ext, &hyps[0]),
            self.anchor_r(ext, hyps.last().expect("a hypothesis per side")),
            self.span,
        )
    }

    fn fresh(&mut self, stem: &str) -> String {
        self.fresh += 1;
        format!("__dec_{stem}{}", self.fresh)
    }

    fn has_self_call(&self, e: &Expr) -> bool {
        let mut found = false;
        crate::surface::walk_expr(e, &mut |x| {
            if let ExprKind::App { head, .. } = &x.kind {
                let callee = match &head.kind {
                    ExprKind::TyApp { head, .. } => &head.kind,
                    other => other,
                };
                if matches!(callee, ExprKind::Var(n) if n == self.rw.name) {
                    found = true;
                }
            }
        });
        found
    }

    /// The walk proper. `at_anchor` says whether the current position is the
    /// whole of what the two anchors denote — only there can a `match` be
    /// re-matched under a motive that mentions them.
    fn walk(&mut self, e: &Expr, at_anchor: bool) -> Result<Triple, String> {
        let span = self.span;
        if !self.has_self_call(e) {
            let x = self.sigma_apply(e);
            return Ok(Triple {
                lhs: x.clone(),
                rhs: x,
                proof: Expr {
                    kind: ExprKind::Refl,
                    span,
                },
            });
        }
        match &e.kind {
            // §3: a `let` whose right-hand side holds no self-call is
            // substituted — `let` is zeta-transparent, so the two sides still
            // reduce alike.
            ExprKind::Block(b) => {
                if !b.ons.is_empty() {
                    return Err("a nested `on` block".into());
                }
                let mut result = (*b.result).clone();
                for s in b.stmts.iter().rev() {
                    let Stmt::Let { name, expr, .. } = s else {
                        return Err("a destructuring or `code` binding in the body".into());
                    };
                    if self.has_self_call(expr) {
                        return Err("a recursive call in a `let` right-hand side".into());
                    }
                    result = subst(&result, &[(name.as_str(), expr)], &mut Vec::new());
                }
                self.walk(&result, at_anchor)
            }
            ExprKind::App {
                head,
                args,
                named,
                explicit,
                ..
            } => {
                if !named.is_empty() {
                    return Err("named arguments around a recursive call".into());
                }
                let callee = match &head.kind {
                    ExprKind::TyApp { head, .. } => &head.kind,
                    other => other,
                };
                if matches!(callee, ExprKind::Var(n) if n == self.rw.name) {
                    return self.leaf(args, *explicit);
                }
                if self.has_self_call(head) {
                    return Err("a recursive call in a callee position".into());
                }
                let head_s = self.sigma_apply(head);
                let mut parts = Vec::new();
                for a in args {
                    parts.push((self.has_self_call(a), self.walk(a, false)?));
                }
                let lhs = app(
                    head_s.clone(),
                    parts.iter().map(|(_, t)| t.lhs.clone()).collect(),
                    span,
                );
                let rhs = app(
                    head_s.clone(),
                    parts.iter().map(|(_, t)| t.rhs.clone()).collect(),
                    span,
                );
                // One `j` per changed argument (§3), rewriting the argument
                // list left to right from the left rendering to the right.
                let mut cur: Vec<Expr> = parts.iter().map(|(_, t)| t.lhs.clone()).collect();
                let mut proof = Expr {
                    kind: ExprKind::Refl,
                    span,
                };
                for (i, (changed, t)) in parts.iter().enumerate() {
                    if !changed {
                        continue;
                    }
                    let y = self.fresh("y");
                    let mut at_y = cur.clone();
                    at_y[i] = var(&y, span);
                    let motive = lam(
                        &[&y, "__dec_q"],
                        eq_expr(lhs.clone(), app(head_s.clone(), at_y, span), span),
                        span,
                    );
                    proof = Expr {
                        kind: ExprKind::J {
                            proof: Box::new(t.proof.clone()),
                            motive: Box::new(motive),
                            case: Box::new(proof),
                        },
                        span,
                    };
                    cur[i] = t.rhs.clone();
                }
                Ok(Triple { lhs, rhs, proof })
            }
            ExprKind::Match {
                form,
                scrut,
                eqbind,
                motive,
                arms,
                ..
            } => {
                if !at_anchor {
                    return Err("a `match` holding a recursive call inside an argument".into());
                }
                if *form != MatchForm::Match {
                    return Err("a `split` or `if` around a recursive call".into());
                }
                if eqbind.is_some() || motive.is_some() {
                    return Err("a `match` with a written motive or equation binding".into());
                }
                let ExprKind::Var(v) = &scrut.kind else {
                    return Err("a `match` whose scrutinee is not a variable".into());
                };
                if self.sigma.iter().any(|(n, _)| n == v) {
                    return Err("a second `match` on an already-refined variable".into());
                }
                self.match_at_anchor(v, arms)
            }
            // §3: a self-call under a `λ` is funext again, and refused.
            ExprKind::Lam { .. } => {
                Err("a recursive call under a `λ`, which is functional extensionality".into())
            }
            _ => Err("a body shape the walk does not cover".into()),
        }
    }

    /// A `match` at the anchor: re-matched under the motive
    /// `λ s => lhs(s) = rhs(s)`, with the bound hypotheses generalized into it
    /// wherever the measure mentions the scrutinee (§3, probed).
    fn match_at_anchor(&mut self, v: &str, arms: &[Arm]) -> Result<Triple, String> {
        let span = self.span;
        let s = self.fresh("s");
        let sv = var(&s, span);
        let ext = Some((v, &sv));
        let m_at_s = self.measure_at(ext);
        let generalize = mentions(&m_at_s, &s);
        if !generalize && !self.args(ext).iter().any(|a| mentions(a, &s)) {
            return Err(
                "a `match` on a variable neither the measure nor an argument mentions".into(),
            );
        }
        let hyp_names: Vec<&str> = self.hyp_binders(&m_at_s).iter().map(|(n, _)| *n).collect();
        let goal = if generalize {
            let hyps: Vec<Expr> = hyp_names.iter().map(|n| var(n, span)).collect();
            pi(self.hyp_binders(&m_at_s), self.goal(ext, &hyps), span)
        } else {
            self.goal(ext, &self.hyps.clone())
        };
        let motive = lam(&[&s], ty_lit(goal, span), span);
        // The rewrite's own bookkeeping, so that the obligations below are
        // numbered and transported exactly as `f#body` numbered and
        // transported them.
        let eq = self.rw.refining_match(&var(v, span), &None);
        if eq.is_some() {
            self.rw.eqs += 1;
        }
        let outer_hyps = self.hyps.clone();
        let mut out = Vec::new();
        for a in arms {
            if a.default {
                return Err("a `_` arm around a recursive call".into());
            }
            let Some(pat) = pattern_expr(a, span) else {
                return Err("an arm whose pattern has no expression form".into());
            };
            if let Some(eq) = &eq {
                self.rw
                    .refinements
                    .push((v.to_string(), pat.clone(), eq.clone()));
            }
            self.sigma.push((v.to_string(), pat));
            if generalize {
                self.hyps = hyp_names.iter().map(|n| var(n, span)).collect();
            }
            let saved = std::mem::take(&mut self.lets);
            // The arm's binders, typed as the body's own walk types them, so
            // that a leaf below lifts its obligation over the same binders.
            let depth = self.rw.scope.len();
            let scrut_ty = self.rw.scrut_ty(&var(v, span));
            self.rw.bind_arm(a, scrut_ty.as_ref());
            let inner = self.walk(&a.body, true);
            self.rw.scope.truncate(depth);
            let stmts = std::mem::replace(&mut self.lets, saved);
            self.sigma.pop();
            if eq.is_some() {
                self.rw.refinements.pop();
            }
            self.hyps = outer_hyps.clone();
            let inner = inner?;
            // The convoy equation at this arm's pattern, bound to `refl` (§5).
            // Spelled as a `let` so the obligations below reach it by the same
            // name `f#body`'s body uses, and reduce to the same term.
            let proof = Expr {
                kind: ExprKind::Block(Box::new(Block {
                    stmts,
                    result: Box::new(inner.proof),
                    ons: Vec::new(),
                    span,
                })),
                span,
            };
            out.push(Arm {
                ctor: a.ctor.clone(),
                default: false,
                binders: a.binders.clone(),
                body: if generalize {
                    lam(&hyp_names, proof, span)
                } else {
                    proof
                },
                span: a.span,
            });
        }
        let matched = Expr {
            kind: ExprKind::Match {
                form: MatchForm::Match,
                generated: false,
                scrut: Box::new(var(v, span)),
                eqbind: None,
                motive: Some(Box::new(motive)),
                arms: out,
            },
            span,
        };
        let proof = if generalize {
            app(matched, outer_hyps.clone(), span)
        } else {
            matched
        };
        Ok(Triple {
            lhs: self.anchor_l(None, &outer_hyps[0]),
            rhs: self.anchor_r(None, outer_hyps.last().expect("a hypothesis")),
            proof,
        })
    }

    /// A self-call site: the leaf of the congruence (§3's table). Both sides
    /// need the *same* obligation proof, so it is bound once (§4).
    fn leaf(&mut self, args: &[Expr], explicit: bool) -> Result<Triple, String> {
        let span = self.span;
        if args.len() != self.rw.params.len() {
            return Err("an unsaturated recursive call".into());
        }
        if !explicit && self.rw.params.iter().any(|p| p.implicit) {
            return Err("a recursive call that does not pass its implicit parameters".into());
        }
        for a in args {
            if self.has_self_call(a) {
                return Err("a recursive call inside another recursive call's arguments".into());
            }
        }
        let map: Vec<(&str, &Expr)> = self
            .rw
            .params
            .iter()
            .map(|p| p.name.as_str())
            .zip(args)
            .collect();
        // `e[ȳ]` — built from the *unsubstituted* measure, then pushed through
        // the enclosing arms' patterns, so it reads as the rewritten body's
        // own copy does.
        let at_args = self.sigma_apply(&subst(self.rw.measure, &map, &mut Vec::new()));
        // The obligation is the site's lifted `f#obl_N` (§4), so the term
        // below and the body's are the same one — which is what an
        // `omega`-defaulted obligation needs, `omega` being a function of its
        // context and not of the goal alone.
        let mut acc = self.rw.obligation(&subst(self.rw.measure, &map, &mut Vec::new()), span);
        if !self.rw.obls.last().is_some_and(Option::is_some) {
            return Err(
                "a recursive call whose obligation cannot be lifted into a declaration \
                 of its own: its statement names a binder this generator cannot type"
                    .into(),
            );
        }
        // The convoy equations at their arms' patterns, bound to `refl` (§5)
        // **here** and not at the arm: only at the leaf is every enclosing
        // pattern substituted, and `Succ(k)` two arms up is `Succ(Succ(l))`
        // by the time the innermost arm binds `l`.
        for (_, pat, eq) in self.rw.refinements.clone() {
            let at = self.sigma_apply(&pat);
            let name = self.fresh("eq");
            self.lets.push(Stmt::Let {
                name: name.clone(),
                ty: Some(eq_ty(at.clone(), at, span)),
                expr: Expr {
                    kind: ExprKind::Refl,
                    span,
                },
                span,
            });
            acc = subst(&acc, &[(eq.as_str(), &var(&name, span))], &mut Vec::new());
        }
        let acc = self.sigma_apply(&acc);
        let m = self.measure_at(None);
        let name = self.fresh("o");
        self.lets.push(Stmt::Let {
            name: name.clone(),
            ty: Some(lt_ty(at_args.clone(), m.clone(), span)),
            expr: acc,
            span,
        });
        let ys: Vec<Expr> = args.iter().map(|a| self.sigma_apply(a)).collect();
        let trans = |bound: Expr, hyp: Expr| {
            app(
                var("nat::le_trans", span),
                vec![
                    succ(at_args.clone(), span),
                    m.clone(),
                    bound,
                    var(&name, span),
                    hyp,
                ],
                span,
            )
        };
        match self.mode {
            Mode::Ext => {
                let q1 = trans(var(A, span), self.hyps[0].clone());
                let q2 = trans(var(B, span), self.hyps[1].clone());
                let mut l = ys.clone();
                l.push(q1.clone());
                let mut r = ys.clone();
                r.push(q2.clone());
                let mut p = ys.clone();
                p.push(q1);
                p.push(q2);
                Ok(Triple {
                    lhs: app(var(G1, span), l, span),
                    rhs: app(var(G2, span), r, span),
                    proof: app(var(HG, span), p, span),
                })
            }
            Mode::Unfold => {
                let q = trans(m.clone(), self.hyps[0].clone());
                let mut l = vec![m.clone()];
                l.extend(ys.iter().cloned());
                l.push(q.clone());
                let mut irrel = vec![m.clone(), succ(at_args.clone(), span)];
                irrel.extend(ys.iter().cloned());
                irrel.push(q);
                irrel.push(app(
                    var("nat::lt_succ_self", span),
                    vec![at_args.clone()],
                    span,
                ));
                // The right-hand side is the call **as written** (§5).
                let mut rhs_args = ys;
                let head = self.cref(&self.decl.name);
                Ok(Triple {
                    lhs: app(self.cref(&rec_name(&self.decl.name)), l, span),
                    rhs: Expr {
                        kind: ExprKind::App {
                            head: Box::new(head),
                            args: std::mem::take(&mut rhs_args),
                            named: Vec::new(),
                            explicit,
                            goal_oriented: false,
                        },
                        span,
                    },
                    proof: app(self.cref(&irrel_name(&self.decl.name)), irrel, span),
                })
            }
        }
    }
}

/// The unfolding companions for `decl` (§2's last three rows): `f#ext`,
/// `f#irrel`, `f_unfold`.
///
/// `Err(reason)` is §3's refusal, not an error on `f`: the companions are
/// simply not emitted, `f` checks exactly as it does today, and the reason is
/// what a later reference to `f_unfold` reports.
pub(crate) fn companions(
    decl: &Decl,
    name: &str,
    measure: &Expr,
    omega_available: bool,
    tys: &dyn BinderTys,
) -> Result<Vec<Lowered>, String> {
    let span = measure.span;
    // §7: `fn` only. A `theorem` is opaque, so `f(ȳ)` in the equation's
    // right-hand side would never unfold — and nothing rewrites with a
    // proof's value anyway.
    if decl.kind != DeclKind::Fn {
        return Err("a `theorem`, whose value nothing rewrites with".into());
    }
    // §4: every obligation is lifted, and a body that discharges its goals by
    // statement rather than by name keeps them where they were written.
    if !liftable(decl) {
        return Err("an `on` clause naming a statement rather than an obligation".into());
    }
    let params = value_params(decl);
    let refs: Vec<&Param> = decl.params.iter().collect();
    // The body **as written** — the `on`s dropped, since they discharge the
    // measure's obligations and are no part of the equation (§5).
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
    // A member recurses under its base name (`nth(t)` inside `fn List::nth`),
    // and that name is in scope only for its own body. The equation's
    // right-hand side is read outside it, so the self-calls there are
    // qualified — the same declaration, spelled the way a reader must spell it.
    let qualified = var(&decl.name, span);
    let rhs_source = if decl.name == name {
        source.clone()
    } else {
        subst(&source, &[(name, &qualified)], &mut Vec::new())
    };
    let fresh = || Rewrite {
        decl,
        name,
        params: &refs,
        measure,
        ons: &decl.body.ons,
        omega_available,
        tys,
        lift: true,
        next: 1,
        eqs: 0,
        refinements: Vec::new(),
        scope: scope_of(decl),
        sites: Vec::new(),
        obls: Vec::new(),
        error: None,
    };
    let arg_vars: Vec<Expr> = params.iter().map(|p| var(&p.name, span)).collect();
    let explicit = decl.params.iter().any(|p| p.implicit);
    let apply = |head: Expr, args: Vec<Expr>| Expr {
        kind: ExprKind::App {
            head: Box::new(head),
            args,
            named: Vec::new(),
            explicit,
            goal_oriented: false,
        },
        span,
    };

    // -- `f#ext` --------------------------------------------------------------
    let mut ext = Respell {
        rw: fresh(),
        mode: Mode::Ext,
        decl,
        source: &source,
        sigma: Vec::new(),
        hyps: vec![var(H1, span), var(H2, span)],
        lets: Vec::new(),
        fresh: 0,
        span,
    };
    let ext_proof = ext.walk(&source, true)?;
    let ext_sites = std::mem::take(&mut ext.rw.sites);
    // Every obligation moved into its own declaration (§4), so the discharges
    // that raised them are no part of a companion; anything else the writer
    // wrote about a goal in the body still is.
    let moved: Vec<&str> = ext_sites.iter().map(|(_, h, _)| h.as_str()).collect();
    let companion_ons = remaining_ons(&decl.body.ons, &moved);
    let ext_body = Block {
        stmts: std::mem::take(&mut ext.lets),
        result: Box::new(ext_proof.proof),
        ons: companion_ons.clone(),
        span: decl.body.span,
    };
    let ih_ty = |k: &str| {
        pi_over(
            &params,
            arrow(
                None,
                lt_ty(measure.clone(), var(k, span), span),
                decl.result.clone(),
                span,
            ),
            span,
        )
    };
    let hg_ty = pi_over(
        &params,
        pi(
            vec![
                ("__dec_p1", lt_ty(measure.clone(), var(A, span), span)),
                ("__dec_q1", lt_ty(measure.clone(), var(B, span), span)),
            ],
            {
                let mut l = arg_vars.clone();
                l.push(var("__dec_p1", span));
                let mut r = arg_vars.clone();
                r.push(var("__dec_q1", span));
                eq_ty(
                    app(var(G1, span), l, span),
                    app(var(G2, span), r, span),
                    span,
                )
            },
            span,
        ),
        span,
    );
    let body_at = |k: &str, g: &str, h: &str| {
        let mut args = vec![var(k, span), var(g, span)];
        args.extend(arg_vars.iter().cloned());
        args.push(var(h, span));
        app(
            companion_ref(decl, &body_name(&decl.name), span),
            args,
            span,
        )
    };
    let nat = Ty {
        kind: TyKind::Nat,
        span,
    };
    let mut ext_params = vec![
        param(A, nat.clone(), span),
        param(B, nat.clone(), span),
        param(G1, ih_ty(A), span),
        param(G2, ih_ty(B), span),
        param(HG, hg_ty, span),
    ];
    ext_params.extend(params.iter().cloned());
    ext_params.push(param(
        H1,
        lt_ty(measure.clone(), succ(var(A, span), span), span),
        span,
    ));
    ext_params.push(param(
        H2,
        lt_ty(measure.clone(), succ(var(B, span), span), span),
        span,
    ));
    let ext_decl = Decl {
        kind: DeclKind::Theorem,
        is_meta: false,
        elaborates: None,
        name: ext_name(&decl.name),
        tyvars: decl.tyvars.clone(),
        params: ext_params,
        result: eq_ty(body_at(A, G1, H1), body_at(B, G2, H2), span),
        decreases: None,
        body: ext_body,
        span: decl.span,
    };

    // -- `f#irrel` ------------------------------------------------------------
    let rec_at = |z: Expr, h: Expr| {
        let mut args = vec![z];
        args.extend(arg_vars.iter().cloned());
        args.push(h);
        app(companion_ref(decl, &rec_name(&decl.name), span), args, span)
    };
    // The motive of the induction on the bound: everything but the bound
    // generalized, as bound irrelevance needs (§1).
    let outer_motive = |z: Expr| {
        let mut binders: Vec<(&str, Ty)> = vec![(W, nat.clone())];
        binders.extend(params.iter().map(|p| (p.name.as_str(), p.ty.clone())));
        binders.push((H1, lt_ty(measure.clone(), z.clone(), span)));
        binders.push((H2, lt_ty(measure.clone(), var(W, span), span)));
        pi(
            binders,
            eq_ty(
                rec_at(z, var(H1, span)),
                rec_at(var(W, span), var(H2, span)),
                span,
            ),
            span,
        )
    };
    let inner_motive = |w: Expr| {
        pi(
            vec![(H2, lt_ty(measure.clone(), w.clone(), span))],
            eq_ty(
                rec_at(succ(var(K, span), span), var(H1, span)),
                rec_at(w, var(H2, span)),
                span,
            ),
            span,
        )
    };
    let absurd = |h: &str| Expr {
        kind: ExprKind::Match {
            form: MatchForm::Match,
            generated: false,
            scrut: Box::new(var(h, span)),
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
    let ihz = "__dec_ihz";
    let l = "__dec_l";
    // `f#ext(k, l, f#rec(k), f#rec(l), λ ȳ p q => ih(l, ȳ, p, q), x̄, h1, h2)`
    let ext_call = {
        let side = |bound: &str, p: &str| {
            let mut binders: Vec<&str> = params.iter().map(|q| q.name.as_str()).collect();
            binders.push(p);
            lam(
                &binders,
                rec_at(var(bound, span), var(p, span)),
                span,
            )
        };
        let hg = {
            let mut binders: Vec<&str> = params.iter().map(|q| q.name.as_str()).collect();
            binders.push("__dec_p1");
            binders.push("__dec_q1");
            let mut args = vec![var(l, span)];
            args.extend(arg_vars.iter().cloned());
            args.push(var("__dec_p1", span));
            args.push(var("__dec_q1", span));
            lam(&binders, app(var(ihz, span), args, span), span)
        };
        let mut args = vec![
            var(K, span),
            var(l, span),
            side(K, "__dec_p1"),
            side(l, "__dec_q1"),
            hg,
        ];
        args.extend(arg_vars.iter().cloned());
        args.push(var(H1, span));
        args.push(var(H2, span));
        app(companion_ref(decl, &ext_name(&decl.name), span), args, span)
    };
    let inner = Expr {
        kind: ExprKind::Match {
            form: MatchForm::Match,
            generated: false,
            scrut: Box::new(var(W, span)),
            eqbind: None,
            motive: Some(Box::new(lam(
                &["__dec_ww"],
                ty_lit(inner_motive(var("__dec_ww", span)), span),
                span,
            ))),
            arms: vec![
                Arm {
                    ctor: "Zero".into(),
                    default: false,
                    binders: Vec::new(),
                    body: lam(&[H2], absurd(H2), span),
                    span,
                },
                Arm {
                    ctor: "Succ".into(),
                    default: false,
                    binders: vec![pat(l)],
                    body: lam(&[H2], ext_call, span),
                    span,
                },
            ],
        },
        span,
    };
    let mut zero_binders: Vec<&str> = vec![W];
    zero_binders.extend(params.iter().map(|p| p.name.as_str()));
    zero_binders.push(H1);
    zero_binders.push(H2);
    let mut succ_binders: Vec<&str> = vec![W];
    succ_binders.extend(params.iter().map(|p| p.name.as_str()));
    succ_binders.push(H1);
    let irrel_elim = Expr {
        kind: ExprKind::Match {
            form: MatchForm::Match,
            generated: false,
            scrut: Box::new(var(Z, span)),
            eqbind: None,
            motive: Some(Box::new(lam(
                &["__dec_zz"],
                ty_lit(outer_motive(var("__dec_zz", span)), span),
                span,
            ))),
            arms: vec![
                Arm {
                    ctor: "Zero".into(),
                    default: false,
                    binders: Vec::new(),
                    body: lam(&zero_binders, absurd(H1), span),
                    span,
                },
                Arm {
                    ctor: "Succ".into(),
                    default: false,
                    binders: vec![pat(K), pat(ihz)],
                    body: lam(&succ_binders, inner, span),
                    span,
                },
            ],
        },
        span,
    };
    let mut irrel_args = vec![var(W, span)];
    irrel_args.extend(arg_vars.iter().cloned());
    irrel_args.push(var(H1, span));
    irrel_args.push(var(H2, span));
    let mut irrel_params = vec![param(Z, nat.clone(), span), param(W, nat.clone(), span)];
    irrel_params.extend(params.iter().cloned());
    irrel_params.push(param(H1, lt_ty(measure.clone(), var(Z, span), span), span));
    irrel_params.push(param(H2, lt_ty(measure.clone(), var(W, span), span), span));
    let irrel_decl = Decl {
        kind: DeclKind::Theorem,
        is_meta: false,
        elaborates: None,
        name: irrel_name(&decl.name),
        tyvars: decl.tyvars.clone(),
        params: irrel_params,
        result: eq_ty(
            rec_at(var(Z, span), var(H1, span)),
            rec_at(var(W, span), var(H2, span)),
            span,
        ),
        decreases: None,
        body: block(app(irrel_elim, irrel_args, span), decl.body.span),
        span: decl.span,
    };

    // -- `f_unfold` -----------------------------------------------------------
    let mut unfold = Respell {
        rw: fresh(),
        mode: Mode::Unfold,
        decl,
        source: &rhs_source,
        sigma: Vec::new(),
        hyps: vec![app(
            var("nat::lt_succ_self", span),
            vec![measure.clone()],
            span,
        )],
        lets: Vec::new(),
        fresh: 0,
        span,
    };
    let unfold_proof = unfold.walk(&source, true)?;
    let unfold_sites = std::mem::take(&mut unfold.rw.sites);
    let unfold_decl = Decl {
        kind: DeclKind::Theorem,
        is_meta: false,
        elaborates: None,
        name: unfold_name(&decl.name),
        tyvars: decl.tyvars.clone(),
        params: decl.params.clone(),
        result: eq_ty(
            apply(
                companion_ref(decl, &decl.name, span),
                decl.params.iter().map(|p| var(&p.name, span)).collect(),
            ),
            rhs_source.clone(),
            span,
        ),
        decreases: None,
        body: Block {
            stmts: std::mem::take(&mut unfold.lets),
            result: Box::new(unfold_proof.proof),
            ons: companion_ons,
            span: decl.body.span,
        },
        span: decl.span,
    };

    Ok(vec![
        Lowered {
            decl: ext_decl,
            obligations: Obligations { sites: ext_sites },
        },
        Lowered {
            decl: irrel_decl,
            obligations: Obligations { sites: Vec::new() },
        },
        Lowered {
            decl: unfold_decl,
            obligations: Obligations {
                sites: unfold_sites,
            },
        },
    ])
}
