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

/// The constructor the first arm naming `Present` or `Absent` writes, if one
/// does: a cheap syntactic filter, which [`Tested::names_when`] then resolves,
/// since another type may name its constructors so too.
fn when_arm(arms: &[heather_syntax::Arm]) -> Option<&str> {
    arms.iter().map(|a| a.ctor.as_str()).find(|ctor| {
        let last = ctor.rsplit("::").next().unwrap_or(ctor);
        last == "Present" || last == "Absent"
    })
}

/// Is `ind` `logic::And`?
fn is_and_ind(ind: &crate::inductive::Inductive) -> bool {
    ind.name == "And" && ind.scope.module == "logic"
}

/// Is `ind` `when::When`?
fn is_when_ind(ind: &crate::inductive::Inductive) -> bool {
    ind.name == "When" && ind.scope.module == "when"
}

/// The scrutinee of a `match` with `arms`, as the walk that infers its type
/// alone must read it: a call under an arm naming `Present`/`Absent` is
/// marked, with that constructor, to be read as its test when the
/// constructor is `When`'s, which is what the `match` elaborates.
pub(crate) fn tested_marker(scrut: &Expr, arms: &[heather_syntax::Arm]) -> Option<Expr> {
    let ctor = when_arm(arms).filter(|_| is_call(scrut))?;
    let var = |name: &str| Expr { kind: ExprKind::Var(name.to_string()), span: scrut.span };
    Some(Expr {
        kind: ExprKind::App {
            head: Box::new(var(TESTED_MARK)),
            args: vec![scrut.clone(), var(ctor)],
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
        let (ExprKind::Var(v), [call, ctor]) = (&head.kind, args.as_slice()) else { return Ok(None) };
        if v != TESTED_MARK {
            return Ok(None);
        }
        let ExprKind::Var(ctor) = &ctor.kind else { return Ok(None) };
        if !self.names_when(ctor) {
            return Ok(Some((cx.clone(), call.clone())));
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

    /// Does the module names resolve in (a default's owner, while its default
    /// elaborates; else the module being elaborated) import `when`, or is it
    /// `when`? The gate before a name lookup on a path every call takes: a
    /// scan of the module's written imports, no table probe.
    fn when_imported(&self) -> bool {
        let scopes = self.scope.resolution_scopes.borrow();
        let scope = scopes.last().map_or(self.names.scope(), |s| &**s);
        scope.module == "when" || scope.imports_module("when")
    }

    /// Is `ty` a `When<_, _>`? Run on every call checked at a type, so the
    /// structural read comes first: an inductive's tag names its declaration
    /// and module, and only a type with no tag in its shape (one a definition
    /// spells) is decoded, in a module that imports `when`.
    pub(crate) fn is_when(&self, cx: &Cx, ty: &Type) -> bool {
        self.when_of(cx, ty).is_some()
    }

    /// [`Self::is_when`], with the declaration.
    fn when_of(&self, cx: &Cx, ty: &Type) -> Option<Rc<crate::inductive::Inductive>> {
        match self.tag_of(ty) {
            Some(ind) => is_when_ind(&ind).then_some(ind),
            None if self.when_imported() => goal_combinators::type_inductive(self, cx, ty).filter(|ind| is_when_ind(ind)),
            None => None,
        }
    }

    /// Does `ctor`, as an arm writes it, resolve to `When`'s constructor? A
    /// type of the module's own, or another import's, may name one
    /// `Present` too; an ambiguous name is not taken for `When`'s.
    pub(crate) fn names_when(&self, ctor: &str) -> bool {
        if !self.when_imported() {
            return false;
        }
        let lookup = crate::name_lookup::NameLookup(self);
        // `When::Present`: the type it is qualified by.
        if let Some((ty, _)) = ctor.rsplit_once("::") {
            return lookup.key_of_kinds(ty, &[crate::names::NameKind::Inductive]).as_deref() == Some(WHEN);
        }
        lookup
            .key_of_kinds(ctor, &[crate::names::NameKind::Ctor])
            .and_then(|key| self.types.constructor(&key).map(|(ind, _)| is_when_ind(ind)))
            .unwrap_or(false)
    }

    /// Is `e` a `match` whose arms name `When`'s constructors, with a call as
    /// its scrutinee?
    fn when_match<'x>(&self, e: &'x Expr) -> Option<&'x Expr> {
        let ExprKind::Match { scrut, arms, .. } = &e.kind else { return None };
        let ctor = when_arm(arms).filter(|_| is_call(scrut))?;
        self.names_when(ctor).then_some(&**scrut)
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
        let Some(mut found) = self.condition_of(cx, call) else { return Ok(None) };
        // A condition whose proofs are interchangeable is `∥P∥`
        // (docs/strict-conditions-design.md §3): `P` is what is decided, and
        // its proof is accepted at the squash, wrapped.
        if let Type::Squash { level, ty } = &found.condition {
            let (level, ty) = (level.clone(), (**ty).clone());
            found.condition = ty;
            found.level = level;
        }
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

    /// A `match` on `When`'s constructors whose arms leave the proofs out
    /// (docs/when-design.md §5): `Present(x)` binds its proof as
    /// `__when_holds_N`, and the `_` arm beside it (an `if let`'s `else`) is
    /// `Absent`, binding the refutation as `__when_fails_N`, with `N` the
    /// scrutinee's place. The names are
    /// private, like `__if_bitN`, and visible to a tactic and to `known`.
    fn complete_arms(&self, e: &Expr) -> Option<Expr> {
        let ExprKind::Match { form, motive, scrut, arms, eqbind, generated } = &e.kind else { return None };
        if !when_arm(arms).is_some_and(|c| self.names_when(c)) {
            return None;
        }
        let ctor = |a: &heather_syntax::Arm| a.ctor.rsplit("::").next().unwrap_or(&a.ctor).to_string();
        let short = |a: &heather_syntax::Arm| ctor(a) == "Present" && !a.default && a.binders.len() == 1;
        let named_present = arms.iter().any(|a| ctor(a) == "Present" && !a.default);
        let named_absent = arms.iter().any(|a| ctor(a) == "Absent" && !a.default);
        let wild = arms.iter().any(|a| a.default) && named_present && !named_absent;
        if !arms.iter().any(short) && !wild {
            return None;
        }
        let bind = |name: &str, span: Span| heather_syntax::Pat::Var { name: name.to_string(), span };
        // Suffixed by the scrutinee's place, as `?`'s are: a nested test's
        // proof must not shadow an outer one, which `known` finds by name.
        let (holds, fails) = (format!("__when_holds_{}", scrut.span.start), format!("__when_fails_{}", scrut.span.start));
        let arms = arms
            .iter()
            .map(|a| {
                let mut a = a.clone();
                if short(&a) {
                    a.binders.push(bind(&holds, a.span));
                } else if a.default && wild {
                    a.default = false;
                    a.ctor = "Absent".to_string();
                    a.binders = vec![bind(&fails, a.span)];
                }
                a
            })
            .collect();
        Some(Expr {
            kind: ExprKind::Match {
                form: *form,
                motive: motive.clone(),
                scrut: scrut.clone(),
                arms,
                eqbind: eqbind.clone(),
                generated: *generated,
            },
            span: e.span,
        })
    }

    /// A `match` on `When`'s constructors, made ready: its arms completed
    /// ([`Self::complete_arms`]) and a call scrutinee tested.
    pub(crate) fn tested_match(&self, cx: &Cx, e: &Expr) -> R<Option<(Cx, Expr)>> {
        let completed = self.complete_arms(e);
        let e = completed.as_ref().unwrap_or(e);
        let Some(scrut) = self.when_match(e) else {
            return Ok(completed.map(|c| (cx.clone(), c)));
        };
        let Some((bound, tested)) = self.tested(cx, scrut)? else {
            return Ok(completed.map(|c| (cx.clone(), c)));
        };
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
        if let Some(value) = self.when_tail(cx, e) {
            return Ok(Some((cx.clone(), value)));
        }
        if matches!(&e.kind, ExprKind::Match { arms, .. } if when_arm(arms).is_some_and(|c| self.names_when(c))) {
            return self.tested_match(cx, e);
        }
        if let Some(found) = self.tested_propagation(cx, e, expected)? {
            return Ok(Some(found));
        }
        if !is_call(e) || !self.is_when(cx, expected) {
            return Ok(None);
        }
        self.tested(cx, e)
    }
}

impl Tested<'_> {
    /// A [`TAIL`] marker checked at the continuation's `When<U, Q>`: the
    /// value as written when it is a `When` by its type, or when it does not
    /// infer alone (a written `Present(x, known)` needs its expected type);
    /// else `When::Present(value, known)`. The value is inferred once in a
    /// probe and then checked, so only a `?`'s tail pays a second
    /// elaboration.
    fn when_tail(&self, cx: &Cx, e: &Expr) -> Option<Expr> {
        let ExprKind::App { head, args, .. } = &e.kind else { return None };
        let (ExprKind::Var(v), [value]) = (&head.kind, args.as_slice()) else { return None };
        if v != TAIL {
            return None;
        }
        let is_when = self.probe(|| self.elab_infer(cx, value).ok().map(|(_, ty, _)| self.is_when(cx, &ty)));
        if is_when != Some(false) {
            return Some(value.clone());
        }
        let span = value.span;
        let var = |name: &str| Expr { kind: ExprKind::Var(name.to_string()), span };
        Some(Expr {
            kind: ExprKind::App { head: Box::new(var("When::Present")), args: vec![value.clone(), var(KNOWN)], named: vec![], explicit: false, goal_oriented: false },
            span,
        })
    }
}

/// The `known` search's name: a hypothesis in scope, or a side of one that
/// is a conjunction, then `omega`, then `bv_omega` (docs/when-design.md §5).
/// The default of `When::val`'s condition.
pub(crate) const KNOWN: &str = "known";

impl Tested<'_> {
    /// `known` at `expected`: the innermost hypothesis of that type, or a
    /// side of a conjunction in scope, else the arithmetic searches a
    /// `decreases` obligation runs.
    pub(crate) fn known(&self, cx: &Cx, expected: &Type, lvl: &Level, span: Span) -> R<heather_kernel::term::Term> {
        // Binders and `let`/pattern aliases, innermost first within each.
        let names: Vec<String> = cx.aliases.iter_inner().map(|a| a.name.clone())
            .chain(cx.names.iter_inner().map(str::to_string))
            .collect();
        for name in &names {
            let var = Expr { kind: ExprKind::Var(name.clone()), span };
            let side = |field: &str| Expr {
                kind: ExprKind::Dot { recv: Box::new(var.clone()), name: field.to_string(), tyargs: vec![], args: None, named: vec![] },
                span,
            };
            let Ok((_, ty, _)) = self.resolve_reading(cx, name, span) else { continue };
            let mut candidates = vec![var.clone()];
            if goal_combinators::type_inductive(self, cx, &ty).is_some_and(|ind| is_and_ind(&ind)) {
                candidates.push(side("left"));
                candidates.push(side("right"));
            }
            for candidate in candidates {
                let fits = self.probe(|| {
                    self.elab_infer(cx, &candidate).is_ok_and(|(_, ty, _)| self.conv_types(cx, &ty, expected, lvl))
                });
                if fits {
                    return self.elab_check(cx, &candidate, expected, lvl);
                }
            }
        }
        // A conjunction is found side by side: `?`'s stated condition is the
        // conjunction of what its tests proved.
        if goal_combinators::type_inductive(self, cx, expected).is_some_and(|ind| is_and_ind(&ind)) {
            let pair = Expr {
                kind: ExprKind::App {
                    head: Box::new(Expr { kind: ExprKind::Var("And".to_string()), span }),
                    args: vec![Expr { kind: ExprKind::Var(KNOWN.to_string()), span }, Expr { kind: ExprKind::Var(KNOWN.to_string()), span }],
                    named: vec![],
                    explicit: false,
                    goal_oriented: false,
                },
                span,
            };
            if let Ok(term) = self.probe(|| self.elab_check(cx, &pair, expected, lvl)) {
                let _ = term;
                return self.elab_check(cx, &pair, expected, lvl);
            }
        }
        let closer = Expr { kind: ExprKind::Var(crate::measure::CLOSER.to_string()), span };
        self.elab_check(cx, &closer, expected, lvl).map_err(|error| {
            let goal = self.spell_type_source(cx, expected).or_else(|| self.spell_type(cx, expected)).unwrap_or_else(|| "it".into());
            let detail = match error {
                crate::ElabError::Elab { msg, .. } => msg,
                other => other.to_string(),
            };
            crate::ElabError::Elab {
                msg: format!(
                    "`known` found no hypothesis `{goal}` in scope, nor a side of a conjunction, and {detail}; \
                     test it (a `match` or `if let` on `Present`/`Absent`) or prove it"
                ),
                span,
            }
        })
    }
}

/// The call a `?` lowers to (`heather_syntax::try_lower`): `K[e?]` is this
/// applied to `e` and `λ v => K[v]`.
const PROPAGATE: &str = "result::Result::and_then";

/// `e` peeled of its blocks: the expression that gives its value.
fn tail(e: &Expr) -> &Expr {
    match &e.kind {
        ExprKind::Block(b) => tail(&b.result),
        _ => e,
    }
}

/// Is `e`'s value a further `?`, which the walk itself makes a `When`?
fn propagates(e: &Expr) -> bool {
    let ExprKind::App { head, .. } = &tail(e).kind else { return false };
    matches!(&head.kind, ExprKind::Var(name) if name == PROPAGATE)
}

/// `\0when-tail(e)`: a `?` continuation's value, made a `When` by its type
/// when it is checked ([`Tested::when_tail`]).
const TAIL: &str = "\0when-tail";

impl Tested<'_> {
    /// `K[w?]` where a `When<U, Q>` is wanted (docs/when-design.md §6):
    ///
    /// ```text
    /// When::and_then(w, λ v __when_holds_N => K[v], λ q => known)
    /// ```
    ///
    /// `w` is tested when it is a proof-taking call (§4). The continuation's
    /// value is wrapped as `Present(value, known)` unless it is a `When`
    /// already, by its type (a further `?`, a written `Present`/`Absent`, a
    /// call returning one: [`Self::when_tail`]); `known`
    /// finds `Q` from the proofs the `?`s bound, building a conjunction side
    /// by side, and `back: Q → P` from `q`.
    pub(crate) fn tested_propagation(&self, cx: &Cx, e: &Expr, expected: &Type) -> R<Option<(Cx, Expr)>> {
        let ExprKind::App { head, args, named, explicit: false, goal_oriented: false } = &e.kind else { return Ok(None) };
        let (ExprKind::Var(name), [input, continuation], true) = (&head.kind, args.as_slice(), named.is_empty()) else {
            return Ok(None);
        };
        let ExprKind::Lam { binders, body } = &continuation.kind else { return Ok(None) };
        if name != PROPAGATE || binders.len() != 1 || !self.is_when(cx, expected) {
            return Ok(None);
        }
        let span = e.span;
        let var = |name: &str| Expr { kind: ExprKind::Var(name.to_string()), span };
        let (bound, input) = match self.tested(cx, input)? {
            Some(found) => found,
            None => (cx.clone(), input.clone()),
        };
        let holds = format!("__when_holds_{}", input.span.start);
        let call = |name: &str, args: Vec<Expr>| Expr {
            kind: ExprKind::App { head: Box::new(var(name)), args, named: vec![], explicit: false, goal_oriented: false },
            span,
        };
        let build = |wrap: bool| {
            let body = if wrap { call(TAIL, vec![(**body).clone()]) } else { (**body).clone() };
            let mut binders = binders.clone();
            binders.push(LamBinder { name: holds.clone(), ty: None, implicit: false, span });
            let continuation = Expr { kind: ExprKind::Lam { binders, body: Box::new(body) }, span };
            let back = Expr {
                kind: ExprKind::Lam {
                    binders: vec![LamBinder { name: "__when_q".to_string(), ty: None, implicit: false, span }],
                    body: Box::new(var(KNOWN)),
                },
                span,
            };
            call("When::and_then", vec![input.clone(), continuation, back])
        };
        Ok(Some((bound, build(!propagates(body)))))
    }
}

/// The value a coercion takes the `.val()` of, in the rewritten call.
const COERCED: &str = "__when_coerced";

impl Tested<'_> {
    /// A `When<T, P>` where a `T` is wanted (docs/when-design.md §5, stage
    /// 5): the value, with `P` found by `known`. Reached only from the
    /// checking fallback after inference, and only when the inferred type is
    /// `When`, the expected one is not, and its `T` is the expected type;
    /// everything else keeps the ordinary verdict.
    pub(crate) fn coerce(&self, cx: &Cx, e: &Expr, term: &heather_kernel::term::Term, got: &Type, expected: &Type, lvl: &Level) -> R<Option<heather_kernel::term::Term>> {
        // On every checking path that infers: the structural read first, as
        // for the tested call, and no name lookup.
        let Some(ind) = self.when_of(cx, got) else { return Ok(None) };
        if self.is_when(cx, expected) {
            return Ok(None);
        }
        let Some(args) = crate::gendefs::GeneratedDefs(self).instance_args(cx, &ind, got) else { return Ok(None) };
        let Some(value) = args.first() else { return Ok(None) };
        let value_ty = Type::El { level: lvl.clone(), tm: Rc::clone(value) };
        if !self.conv_types(cx, &value_ty, expected, lvl) {
            return Ok(None);
        }
        let span = e.span;
        let mut bound = cx.clone();
        bound.aliases.push(Rc::new(Alias {
            name: COERCED.to_string(),
            depth: cx.names.len(),
            term: Rc::new(term.clone()),
            ty: got.clone(),
            level: lvl.clone(),
            skel: None,
            spliced: None,
            shifted: Default::default(),
        }));
        let call = Expr {
            kind: ExprKind::Dot {
                recv: Box::new(Expr { kind: ExprKind::Var(COERCED.to_string()), span }),
                name: "val".to_string(),
                tyargs: vec![],
                args: Some(vec![]),
                named: vec![],
            },
            span,
        };
        self.elab_check(&bound, &call, expected, lvl).map(Some).map_err(|error| {
            let detail = match error {
                crate::ElabError::Elab { msg, .. } => msg,
                other => other.to_string(),
            };
            crate::ElabError::Elab {
                msg: format!("this is a `When`, used where its value is wanted, so its condition must be known here: {detail}"),
                span,
            }
        })
    }
}
