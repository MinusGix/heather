//! The tested call (docs/when-design.md §4): a call of a proof-taking
//! function where a `When<T, P>` is wanted leaves its condition out and
//! tests it.
//!
//! A proof-taking function takes its condition as a parameter whose default
//! is a context search (`Vec::at(v, i, inside: … := bv_omega)`). Where a `T`
//! is wanted the search finds the proof, as for any call. Where a `When` is
//! wanted (the expected type's head is `when::When`, or the call is the
//! scrutinee of a `match` or `if let` on `Present`/`Absent`) the call is
//! elaborated as
//!
//! ```text
//! When::of(λ (h: P) => f(args, name := h))
//! ```
//!
//! which is `if h: P { Present(f(args, h), h) } else { Absent(h) }`: the
//! branch is on the decision's bit, and `When::of_cases`/`When::of_val` are
//! the laws about it, proved once in `lib/std/core/when.hthr`.
//!
//! `P` is the parameter's domain as this call instantiates it, which only
//! the call's own elaboration knows (an implicit length, a method's
//! receiver). So the call is first elaborated in a probe that stops at the
//! condition's default ([`Tested::capture`]), and `P` is then bound to a name
//! the source cannot spell, as a `let` would bind it, for the rewritten call
//! to annotate its binder with.
//!
//! A condition the call writes (`inside := h`) is never tested: the call then
//! leaves no default, the probe captures nothing, and the call keeps its one
//! reading. Only the first condition the call leaves to a search is tested;
//! a later one is searched as usual, with the tested proof in scope.

use std::cell::RefCell;

use heather_kernel::level::Level;
use heather_kernel::rc::Rc;
use heather_kernel::term::Type;
use heather_syntax::{Expr, ExprKind, LamBinder, NamedArg, Span, Ty, TyKind};

use crate::context::Alias;
use crate::{Cx, Elaborator, R, code, defaults, err, goal_combinators};

/// The type a tested call gives, by its qualified name.
pub(crate) const WHEN: &str = "when::When";
/// The tested condition's name in the rewritten call. A lexable name, as
/// `__if_bitN` is: a tactic in a later default spells the proof back as
/// source (`omega`'s certificate), so it must parse.
const CONDITION: &str = "__when_condition";
/// The proof the rewritten call passes for it.
const PROOF: &str = "__when_proof";
/// `\0when-tested(call)`: the call read where a `When` is wanted, for a
/// caller that infers a `match` scrutinee's type alone (the `decreases`
/// walk, [`tested_marker`]).
const TESTED_MARK: &str = "\0when-tested";
/// The error the probe stops with once it has what it came for.
const STOP: &str = "internal: the tested call's probe stops at its condition";

/// The condition a call left to a search: the parameter's name and its
/// domain as the call instantiates it, in the call's context.
#[derive(Clone)]
pub(crate) struct Captured {
    callee: String,
    name: String,
    condition: Type,
    level: Level,
    depth: usize,
}

/// The call a probe is capturing for, by span, and where the capture goes.
/// Kept apart from the probe's restored cells: the capture is the probe's
/// answer, and must survive its rollback.
pub(crate) type Site = (Span, Rc<RefCell<Option<Captured>>>);

/// The tested call's part of the elaborator.
pub(crate) struct Tested<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for Tested<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

/// A call: a name applied to arguments, or a method call `recv.f(args)`.
fn is_call(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::App { head, explicit: false, goal_oriented: false, .. } => {
            matches!(&head.kind, ExprKind::Var(_)) && !is_of_call(head)
        }
        ExprKind::Dot { args: Some(_), .. } => true,
        _ => false,
    }
}

/// `call` with `name := value` added to its named arguments.
fn with_named(call: &Expr, name: &str, value: Expr) -> Option<Expr> {
    let span = call.span;
    let arg = NamedArg { name: name.to_string(), name_span: span, expr: value, span };
    let kind = match &call.kind {
        ExprKind::App { head, args, named, explicit, goal_oriented } => {
            let mut named = named.clone();
            named.push(arg);
            ExprKind::App { head: head.clone(), args: args.clone(), named, explicit: *explicit, goal_oriented: *goal_oriented }
        }
        ExprKind::Dot { recv, name: method, tyargs, args, named } => {
            let mut named = named.clone();
            named.push(arg);
            ExprKind::Dot { recv: recv.clone(), name: method.clone(), tyargs: tyargs.clone(), args: args.clone(), named }
        }
        _ => return None,
    };
    Some(Expr { kind, span })
}

/// The rewritten call's own head: never tested again.
fn is_of_call(head: &Expr) -> bool {
    matches!(&head.kind, ExprKind::Var(v) if v == "When::of" || v == "when::When::of")
}

/// Do these arms name `When`'s constructors?
pub(crate) fn when_arms(arms: &[heather_syntax::Arm]) -> bool {
    arms.iter().any(|a| {
        let ctor = a.ctor.rsplit("::").next().unwrap_or(&a.ctor);
        ctor == "Present" || ctor == "Absent"
    })
}

/// The scrutinee of a `match` with `arms`, as the walk that infers its type
/// alone must read it: a call under `When`'s constructors is marked to be
/// read as its test, which is what the `match` elaborates.
pub(crate) fn tested_marker(scrut: &Expr, arms: &[heather_syntax::Arm]) -> Option<Expr> {
    (when_arms(arms) && is_call(scrut)).then(|| Expr {
        kind: ExprKind::App {
            head: Box::new(Expr { kind: ExprKind::Var(TESTED_MARK.to_string()), span: scrut.span }),
            args: vec![scrut.clone()],
            named: vec![],
            explicit: false,
            goal_oriented: false,
        },
        span: scrut.span,
    })
}

impl Tested<'_> {
    /// A [`tested_marker`]: the call it holds, tested.
    pub(crate) fn tested_mark(&self, cx: &Cx, e: &Expr) -> R<Option<(Cx, Expr)>> {
        let ExprKind::App { head, args, .. } = &e.kind else { return Ok(None) };
        let (ExprKind::Var(v), [call]) = (&head.kind, args.as_slice()) else { return Ok(None) };
        if v != TESTED_MARK {
            return Ok(None);
        }
        match self.tested(cx, call)? {
            Some(found) => Ok(Some(found)),
            None => Ok(Some((cx.clone(), call.clone()))),
        }
    }

    /// Can the module being elaborated name `when::When`?
    pub(crate) fn when_visible(&self) -> bool {
        crate::name_lookup::NameLookup(self).key_of_kinds("When", &[crate::names::NameKind::Inductive]).as_deref() == Some(WHEN)
    }

    /// Is `ty` a `When<_, _>`?
    pub(crate) fn is_when(&self, cx: &Cx, ty: &Type) -> bool {
        // A name lookup first: a module that cannot name `When` pays only it.
        if !self.when_visible() {
            return false;
        }
        goal_combinators::type_inductive(self, cx, ty).is_some_and(|ind| ind.name == "When")
    }

    /// Is `e` a `match` whose arms name `When`'s constructors, with a call as
    /// its scrutinee?
    fn when_match(e: &Expr) -> Option<&Expr> {
        let ExprKind::Match { scrut, arms, .. } = &e.kind else { return None };
        (when_arms(arms) && is_call(scrut)).then_some(&**scrut)
    }

    /// Called by every omitted default before it runs: when a probe is
    /// capturing for the call this default belongs to and the default is a
    /// context search, record its parameter and goal and stop the probe.
    pub(crate) fn capture(&self, cx: &Cx, owner: &str, name: &str, default: &Expr, expected: &Type, lvl: &Level, span: Span) -> Option<R<heather_kernel::term::Term>> {
        let site = self.scope.tested_site.borrow();
        let (at, slot) = site.as_ref()?;
        if *at != span || !defaults::is_context_search(default) || slot.borrow().is_some() {
            return None;
        }
        *slot.borrow_mut() = Some(Captured {
            callee: owner.rsplit("::").next().unwrap_or(owner).to_string(),
            name: name.to_string(),
            condition: expected.clone(),
            level: lvl.clone(),
            depth: cx.names.len(),
        });
        Some(err(STOP, span))
    }

    /// The condition `call` leaves to a search, if it leaves one: the call
    /// elaborated in a probe that stops there.
    fn condition_of(&self, cx: &Cx, call: &Expr) -> Option<Captured> {
        let slot = Rc::new(RefCell::new(None));
        let outer = self.scope.tested_site.replace(Some((call.span, Rc::clone(&slot))));
        let _ = self.probe(|| self.elab_infer(cx, call));
        *self.scope.tested_site.borrow_mut() = outer;
        let found = slot.borrow_mut().take();
        found.filter(|c| c.depth == cx.names.len())
    }

    /// `call` as its tested form, with the context that binds its condition:
    /// `None` when the call leaves no condition to a search.
    pub(crate) fn tested(&self, cx: &Cx, call: &Expr) -> R<Option<(Cx, Expr)>> {
        if !is_call(call) {
            return Ok(None);
        }
        let Some(found) = self.condition_of(cx, call) else { return Ok(None) };
        let Some(code) = code::code_of(&found.condition) else { return Ok(None) };
        let mut bound = cx.clone();
        bound.aliases.push(Rc::new(Alias {
            name: CONDITION.to_string(),
            depth: cx.names.len(),
            term: Rc::new(code),
            ty: Type::Ty(found.level.clone()),
            level: Level::succ(found.level.clone()),
            skel: None,
            spliced: None,
            shifted: Default::default(),
        }));
        let span = call.span;
        let var = |name: &str| Expr { kind: ExprKind::Var(name.to_string()), span };
        // A decision of the condition is what the test needs: say so here,
        // rather than through `When::of`'s instance argument.
        let decision = Expr {
            kind: ExprKind::TyApp {
                head: Box::new(var("decide_bit")),
                args: vec![Ty { kind: TyKind::OfExpr(Box::new(var(CONDITION))), span }],
            },
            span,
        };
        let decision = Expr {
            kind: ExprKind::App { head: Box::new(decision), args: vec![], named: vec![], explicit: false, goal_oriented: false },
            span,
        };
        if self.probe(|| self.elab_infer(&bound, &decision)).is_err() {
            let shown = self.spell_type_source(cx, &found.condition).or_else(|| self.spell_type(cx, &found.condition)).unwrap_or_else(|| "it".into());
            return err(
                format!(
                    "a `When` is wanted here, so this call of `{}` tests its condition `{}`, which has no decision \
                     (`Decide<{shown}>`) here: give `{} := …` and take the value, or call a function whose own work \
                     decides it and returns a `When` (docs/when-design.md §3)",
                    found.callee, shown, found.name
                ),
                span,
            );
        }
        let Some(with_proof) = with_named(call, &found.name, var(PROOF)) else { return Ok(None) };
        let lambda = Expr {
            kind: ExprKind::Lam {
                binders: vec![LamBinder {
                    name: PROOF.to_string(),
                    ty: Some(Ty { kind: TyKind::OfExpr(Box::new(var(CONDITION))), span }),
                    implicit: false,
                    span,
                }],
                body: Box::new(with_proof),
            },
            span,
        };
        let tested = Expr {
            kind: ExprKind::App { head: Box::new(var("When::of")), args: vec![lambda], named: vec![], explicit: false, goal_oriented: false },
            span,
        };
        Ok(Some((bound, tested)))
    }

    /// A `match` on `When`'s constructors whose scrutinee is a call: the
    /// `match` with the call tested, and the context binding its condition.
    pub(crate) fn tested_match(&self, cx: &Cx, e: &Expr) -> R<Option<(Cx, Expr)>> {
        let Some(scrut) = Self::when_match(e) else { return Ok(None) };
        let Some((bound, tested)) = self.tested(cx, scrut)? else { return Ok(None) };
        let ExprKind::Match { form, motive, arms, eqbind, generated, .. } = &e.kind else { return Ok(None) };
        let rewritten = Expr {
            kind: ExprKind::Match {
                form: *form,
                motive: motive.clone(),
                scrut: Box::new(tested),
                arms: arms.clone(),
                eqbind: eqbind.clone(),
                generated: *generated,
            },
            span: e.span,
        };
        Ok(Some((bound, rewritten)))
    }
}

impl Tested<'_> {
    /// Checking `e` at `expected`: the tested form when `e` is a call and a
    /// `When` is expected, or a `match` on `When`'s constructors whose
    /// scrutinee is a call.
    pub(crate) fn tested_check(&self, cx: &Cx, e: &Expr, expected: &Type) -> R<Option<(Cx, Expr)>> {
        if Self::when_match(e).is_some() {
            return self.tested_match(cx, e);
        }
        if !is_call(e) || !self.is_when(cx, expected) {
            return Ok(None);
        }
        self.tested(cx, e)
    }
}
