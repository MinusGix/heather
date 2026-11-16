//! Parameter defaults at a call (docs/language/named-arguments-design.md §9).
//!
//! A call that leaves a defaulted parameter out reaches the spine walkers
//! with [`application::PARAM_DEFAULT`]'s marker in that slot
//! (`application::resolve_named`), so the default is checked where a named
//! argument would be: at the parameter's domain as this call instantiates it,
//! once that domain is known. This module is what checking the marker does.
//!
//! A default may mention an earlier parameter (`k: Nat := n`). At the call
//! that name is bound to the call's argument for it, as a `let` binds an
//! alias, so the default reads the argument rather than any name the caller
//! can spell (§9.6).
//!
//! A default is also checked once where it is written, as far as the
//! declaration decides it (§9.7): [`Defaults::check_default_at_declaration`].

use heather_kernel::rc::Rc;

use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{LocalCtx, Term, Type};
use heather_syntax::{Expr, ExprKind, Span};

use crate::application::ParamMeta;
use crate::context::Alias;
use crate::resolve::SearchMark;
use crate::unification::{EarlierArg, strengthen_ty};
use crate::{Cx, ElabError, Elaborator, R, ResolutionScope, application, datarepr, err, stats, surface};
use crate::refusals::Refusals;

/// Defaults' part of the elaborator.
pub(crate) struct Defaults<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for Defaults<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl Defaults<'_> {
    /// A defaulted parameter, filled: its default checked at `expected`, the
    /// parameter's domain with this call's earlier arguments substituted.
    ///
    /// The goal is open in the caller's locals, so the default is checked in
    /// the caller's context — made [`Cx::hygienic`], so that a tactic sees
    /// every hypothesis while no caller's name can capture one of the
    /// default's — and with names resolving in the declaration's own scope.
    /// A caller's local named `trivial` therefore cannot change what
    /// `h: True := trivial` means (§9.4).
    ///
    /// Each earlier parameter the default mentions is bound, under its own
    /// name, to this call's argument for it, out of `earlier`: the call's
    /// arguments before this parameter, committed world, with their
    /// instantiated domains. The bindings are aliases, like a `let`'s, so the
    /// default's term is the one it would be with the arguments written in.
    pub(crate) fn elab_param_default(
        &self,
        cx: &Cx,
        args: &[Expr],
        expected: &Type,
        lvl: &Level,
        span: Span,
        earlier: &[EarlierArg],
    ) -> R<Term> {
        let (Some(ExprKind::Str(owner)), Some(ExprKind::Num(index))) =
            (args.first().map(|a| &a.kind), args.get(1).map(|a| &a.kind))
        else {
            return err("internal parameter default has the wrong form", span);
        };
        let params = self.names.global(owner).map(|g| Rc::clone(&g.params));
        let index = index.as_u64().and_then(|i| usize::try_from(i).ok());
        let param = index.and_then(|i| params.as_ref()?.get(i));
        let (Some(params), Some(index), Some((name, default))) =
            (&params, index, param.and_then(|p| Some((p.name.clone(), Rc::clone(p.default.as_ref()?)))))
        else {
            return err("internal parameter default names no defaulted parameter", span);
        };
        // A tested call's probe stops here (docs/language/when-design.md §4).
        if let Some(stop) = crate::tested::Tested(self).capture(cx, owner, &name, &default.expr, expected, lvl, span) {
            return stop;
        }
        let callee = owner.rsplit("::").next().unwrap_or(owner);
        let goal = self.spell_type_source(cx, expected).or_else(|| self.spell_type(cx, expected)).unwrap_or_else(|| "its type".into());
        let mut hidden = cx.hygienic();
        for j in mentioned_parameters(params, index) {
            let Some(arg) = earlier.iter().find(|e| e.param == j) else {
                return err(
                    format!("internal: `{callee}`'s `{name}` defaults to an expression mentioning `{}`, \
                        and this call did not hand its argument to the default", params[j].name),
                    span,
                );
            };
            hidden.aliases.push(Rc::new(Alias {
                name: params[j].name.clone(),
                depth: hidden.names.len(),
                term: Rc::clone(&arg.term),
                ty: arg.ty.clone(),
                level: arg.level.clone(),
                skel: params[j].skel.clone(),
                spliced: None,
                shifted: Default::default(),
            }));
        }
        if let Some(goals) = self.pass.default_goals.borrow_mut().as_mut() {
            goals.push(DefaultGoal {
                owner: owner.clone(),
                index,
                name: name.clone(),
                goal: self.spell_type_source(cx, expected),
                default: default.expr.clone(),
            });
        }
        // A condition a search was left with can also be tested, where the
        // caller can name `When` (docs/language/when-design.md §4).
        let or_test = if is_context_search(&default.expr)
            && !matches!(&default.expr.kind, ExprKind::Var(v) if v == crate::tested::KNOWN)
            && crate::tested::Tested(self).when_visible()
        {
            " or use the call where a `When` is wanted (a `match` on `Present`/`Absent`), which tests it"
        } else {
            ""
        };
        let _scope = self.use_scope(&default.scope);
        self.elab_check(&hidden, &default.expr, expected, lvl).map_err(|error| ElabError::Elab {
            msg: format!("`{callee}`'s `{name}` was left to its default, which did not give `{goal}` here: {}; \
                give it by name (`{name} := …`){or_test}", match error {
                    ElabError::Elab { msg, .. } => msg,
                    other => other.to_string(),
                }),
            span,
        })
    }

    /// A parameter's default, checked where it is written (§9.7): in the
    /// declaration's telescope `cx`, which binds exactly the parameters
    /// before it, at `ty`, the parameter's type there. A call that leaves the
    /// default out still elaborates it at the call (`elab_param_default`);
    /// this is the check that does not wait for one.
    ///
    /// What the declaration decides is checked here, and what a call decides
    /// is left to the call:
    ///
    /// - A **discharge** ([`is_discharge`]: a tactic, `refl`, `decide`, a
    ///   goal) has no meaning apart from the goal a call poses and the
    ///   hypotheses it has, as `:= infer` has none, so nothing is checked.
    /// - A **value** is checked as a term, by the kernel. It is first read at
    ///   the parameter's type. Where that reading fails, it is read at a type
    ///   of its own instead, and accepted when it checks there and the call
    ///   can still change whether that type is the parameter's: when either
    ///   type mentions an earlier parameter. `zero: IsZero(n) := Holds` is a
    ///   `Yes` that fits exactly the calls with `n` zero, and stays legal;
    ///   `b: Bool := 5` fits none, and is refused here.
    ///
    /// So a default's own subterms (`P(2, refl).a`'s `refl`) and its names
    /// are always checked at the declaration, used or not
    /// (issues/parameter-default-unchecked-at-declaration.md). The attempt
    /// leaves nothing behind: its goals, notes, warnings and dependency
    /// edges are rolled back, since a default belongs to each call's term
    /// and not to the declaration's.
    pub(crate) fn check_default_at_declaration(
        &self,
        cx: &Cx,
        decl: &str,
        param: &str,
        default: &Expr,
        ty: &Type,
        lvl: &Level,
    ) -> R<()> {
        if is_discharge(default) {
            return Ok(());
        }
        let depth = cx.names.len() as u32;
        let fixed = |t: &Type| strengthen_ty(&LocalCtx::nil(), t, depth).is_some();
        let attempt = |read: &dyn Fn() -> R<()>| {
            let mark = SearchMark::of(self);
            let verdict = read();
            mark.rollback(self);
            verdict
        };
        // The second reading's own failure is the one reported once the
        // default has a type the call could still fit: it is about the
        // default itself (`Holds(refl)`'s `refl`), not about its fit.
        let verdict = attempt(&|| self.default_reading(cx, decl, default, ty, lvl, None)).or_else(|at_param| {
            attempt(&|| match self.elab_infer(cx, default) {
                Ok((term, own, own_lvl)) if !(fixed(ty) && fixed(&own)) => {
                    self.default_reading(cx, decl, default, &own, &own_lvl, Some(term))
                }
                _ => Err(at_param.clone()),
            })
        });
        verdict.map_err(|error| match error {
            ElabError::Elab { msg, span } => ElabError::Elab {
                msg: format!("`{param}`'s default does not check where it is written: {msg}"),
                span,
            },
            other => other,
        })
    }

    /// One reading of a value default: `term` if it was already elaborated
    /// at `ty` (its own type), else the default checked at `ty`; then the
    /// kernel's verdict on it in the telescope. A default that would leave
    /// a goal open is not a value, and is refused.
    fn default_reading(&self, cx: &Cx, decl: &str, default: &Expr, ty: &Type, lvl: &Level, term: Option<Term>) -> R<()> {
        let goals = self.attempt.goal_arena.outstanding().len();
        let term = match term {
            Some(term) => term,
            None => self.elab_check(cx, default, ty, lvl)?,
        };
        if self.attempt.goal_arena.outstanding().len() != goals {
            return err("a default cannot leave a goal for its declaration to discharge", default.span);
        }
        // The term may name the declaration's goal slots (a lifted proof, a
        // transparent name), so it is judged in the padded world the
        // elaborator works in, before the attempt's slots are rolled back.
        let world = self.goal_psi();
        stats::time_kernel(|| self.kernel_check_type(&world, Layer::Prog, &cx.gamma, ty, lvl))
            .map_err(|e| Refusals(self).kernel_refusal(decl, default.span, e, &world, Layer::Prog, &cx.gamma, None, ty, lvl))?;
        stats::time_kernel(|| self.kernel_check_term(&world, Layer::Code, &cx.gamma, &term, ty, lvl))
            .map_err(|e| Refusals(self).kernel_refusal(decl, default.span, e, &world, Layer::Code, &cx.gamma, Some(&term), ty, lvl))
    }
}

impl Elaborator {
    /// Install a stored declaration scope for one read of stored syntax. The
    /// guard restores the caller's scope on every return path.
    pub(crate) fn use_scope<'a>(&'a self, scope: &Rc<crate::names::Scope>) -> ResolutionScope<'a> {
        self.scope.resolution_scopes.borrow_mut().push(Rc::clone(scope));
        ResolutionScope { stack: &self.scope.resolution_scopes }
    }
}

/// The earlier parameters `params[index]`'s default mentions, by index: the
/// value parameters before it whose names occur free in it. A type parameter
/// is never one, since the declaration refuses a default that mentions one.
/// Empty for a parameter with no default.
pub(crate) fn mentioned_parameters(params: &[ParamMeta], index: usize) -> Vec<usize> {
    let Some(default) = params.get(index).and_then(|p| p.default.as_ref()) else {
        return Vec::new();
    };
    (0..index)
        .filter(|&j| {
            !params[j].is_type
                && datarepr::mentions_free(&default.expr, std::slice::from_ref(&params[j].name), &mut Vec::new())
        })
        .collect()
}

/// Is `e` an omitted default's marker? Such an argument is checking-only:
/// it has no type of its own until the parameter's domain gives it one.
pub(crate) fn is_param_default(e: &Expr) -> bool {
    matches!(&e.kind, ExprKind::App { head, named, .. }
        if named.is_empty() && matches!(&head.kind, ExprKind::Var(v) if v == application::PARAM_DEFAULT))
}

/// Is this default a **discharge**: a form whose meaning is the goal it is
/// checked at, run at each call like `:= infer` (§9.7)? The tactics and the
/// proof searches (`omega`, `positivity`, `ring`, `linarith`, `nlinarith`, `bv_omega`, `decide`,
/// `rel_cong`/`rel_derive`, `rewrite`, `subst`, `by t`), `refl`, whose
/// endpoints the kernel compares at the goal, and any default that contains
/// a goal `?`, which it poses to the caller. Read off the head, so
/// `mk(omega)` is a value whose `omega` runs in the telescope.
///
/// A user declaration that shadows one of these names makes a default that
/// names it a value no check here reaches; the call still checks it.
/// One omitted default as a call elaborated it: whose parameter, the goal it
/// was checked at (as source in the call's context, where it has one) and the
/// default's expression.
#[derive(Clone)]
pub(crate) struct DefaultGoal {
    pub(crate) owner: String,
    pub(crate) index: usize,
    pub(crate) name: String,
    pub(crate) goal: Option<String>,
    pub(crate) default: Expr,
}

/// Whether a default is a proof search that reads its context: the same call
/// elaborated twice may then give two proof terms, which is why a `decreases`
/// body's are lifted into declarations of their own
/// (issues/found-proof-differs-across-recursion-companions.md).
pub(crate) fn is_context_search(e: &Expr) -> bool {
    matches!(&e.kind, ExprKind::Var(v) if matches!(v.as_str(), "omega" | "bv_omega" | "linarith" | "nlinarith" | "positivity" | crate::tested::KNOWN))
}

pub(crate) fn is_discharge(e: &Expr) -> bool {
    const SEARCHES: [&str; 10] = ["omega", "positivity", "ring", "linarith", "nlinarith", "bv_omega", "decide", "rel_derive", heather_syntax::POS_SEARCH, crate::tested::KNOWN];
    const TACTICS: [&str; 11] = ["omega", "ring", "linarith", "nlinarith", "rewrite", "subst", "simp_only", "simp_show", "rel_cong", "rel_derive", heather_syntax::BY_TACTIC];
    surface::count_holes_expr(e) > 0
        || match &e.kind {
            ExprKind::Refl | ExprKind::AutoRefl | ExprKind::Hole(_) => true,
            ExprKind::Var(v) => SEARCHES.contains(&v.as_str()),
            ExprKind::App { head, .. } => matches!(&head.kind, ExprKind::Var(v) if TACTICS.contains(&v.as_str())),
            ExprKind::Block(block) => is_discharge(&block.result),
            _ => false,
        }
}
