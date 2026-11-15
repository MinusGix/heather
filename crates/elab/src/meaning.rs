//! The meaning check for structural recursion
//! (issues/recursion-meaning-check.md, docs/elaborator/elaborator-principles-survey.md §6).
//!
//! Structural recursion is compiled at a surface `match` (`recursion.rs`):
//! the recursor sits at the `match` the planner chose, and everything outside
//! it is evaluated once, by the top call. When the planner misses a form, the
//! result is a well-typed term that means a different function, and the
//! kernel cannot tell: the compiled term *is* the definition
//! (issues/recursion-let-reads-changing-parameter.md, the varied branch of
//! #389). What the kernel can tell is whether the compiled definition
//! unfolds to its source. So, once `f` is checked, this states
//!
//! ```text
//! theorem f#meaning(x̄): f(x̄) = { body } { match x_dec { C(ȳ) => refl, … } }
//! ```
//!
//! with the body as written (its self-calls now ordinary references to the
//! committed `f`) and the split on the parameter the recursion descended on.
//! In each constructor's arm both sides take the same step: the compiled
//! `f(C(ȳ), …)` runs its recursor once, the source body takes the recursive
//! `match`'s `C` arm, and every self-call on either side is `f` at the
//! smaller value. A lowering that kept a stale value, or skipped a branch at
//! the inner levels, differs at an open argument, and conversion refuses.
//!
//! The statement is elaborated and gated like any declaration, inside a
//! session transaction that is always rolled back, so nothing is registered
//! and the module image does not change. With the check on (`heather check
//! --meaning-check`; off by default until its cost comes down), a statement
//! the kernel refuses is the declaration's refusal (the issue's step 2);
//! with it off, review mode reports it as a lint. One it cannot settle (out
//! of fuel, or a body form the restatement does not reproduce) refuses
//! nothing, and review mode (`heather check --review`) reports it through the
//! `recursion-meaning` lint. Cost: one gated equation per structurally
//! recursive `fn`, one conversion per constructor of the split; deeper plans
//! are tried only after a refusal.

use heather_syntax::ast::{Arm, Block, Decl, DeclKind, Expr, ExprKind, MatchForm, Pat, Ty, TyKind};
use heather_syntax::Span;

use crate::lint::Lint;
use heather_kernel::typing::TypeError;

use crate::{ElabError, Elaborator};

/// Why the check did not confirm the definition.
pub(crate) enum Verdict {
    /// The equation holds at every constructor.
    Holds,
    /// The equation was stated and the kernel (or `refl`) refused it: the
    /// compiled definition does not unfold to its source.
    Differs(String),
    /// The equation could not be stated (a body form this check does not
    /// reproduce, an implicit it cannot infer), or the kernel ran out of fuel
    /// or refused its statement rather than its proof: not evidence either
    /// way.
    Undecided(String),
}

fn var(name: &str, span: Span) -> Expr {
    Expr { kind: ExprKind::Var(name.to_string()), span }
}

/// `f` applied to its parameters, type parameters pinned (`f<A>`).
fn call(decl: &Decl, span: Span) -> Expr {
    let mut head = var(&decl.name, span);
    if !decl.tyvars.is_empty() {
        head = Expr {
            kind: ExprKind::TyApp {
                head: Box::new(head),
                args: decl
                    .tyvars
                    .iter()
                    .map(|t| Ty { kind: TyKind::Named { name: t.name.clone(), args: Vec::new() }, span })
                    .collect(),
            },
            span,
        };
    }
    Expr {
        kind: ExprKind::App {
            head: Box::new(head),
            // The positional arguments only, as a caller writes the call:
            // implicits are inferred from them, and a solver parameter (a
            // constraint's dictionary, `requires`) or a default is resolved in
            // the statement's own telescope, where the same binder is in
            // scope. Passing every parameter under `@` instead put a
            // dictionary in a value slot (`mconcat`).
            args: decl
                .params
                .iter()
                .filter(|p| !p.implicit && p.solver.is_none() && p.default.is_none())
                .map(|p| var(&p.name, span))
                .collect(),
            named: Vec::new(),
            explicit: false,
            goal_oriented: false,
        },
        span,
    }
}

/// The body as written, `on`s dropped (they discharge goals, and are no part
/// of the value), as one expression.
fn source(decl: &Decl) -> Expr {
    if decl.body.stmts.is_empty() {
        return (*decl.body.result).clone();
    }
    Expr {
        kind: ExprKind::Block(Box::new(Block {
            stmts: decl.body.stmts.clone(),
            result: decl.body.result.clone(),
            ons: Vec::new(),
            span: decl.body.span,
        })),
        span: decl.body.span,
    }
}

/// A member recurses under its base name (`nth(t)` inside `fn List::nth`),
/// which is in scope only for its own body; outside it the self-calls are
/// spelled qualified, as `f_unfold`'s right-hand side spells them. A
/// parameter of the base name shadows it (`fn Stmt::weights(self s, …,
/// weights: List<Nat>)`, whose self-calls are all `rest.weights(…)`), so the
/// body's bare `weights` is the parameter and stays as written.
fn qualified_source(decl: &Decl) -> Expr {
    let body = source(decl);
    let base = decl.name.rsplit("::").next().unwrap_or(&decl.name);
    if base == decl.name {
        return body;
    }
    let qualified = var(&decl.name, decl.span);
    let mut bound: Vec<String> = decl.params.iter().map(|p| p.name.clone()).collect();
    crate::measure::subst(&body, &[(base, &qualified)], &mut bound)
}

/// The name of the statement. `#` keeps it out of the surface namespace,
/// and the owner's `::` is spelled out of it: a statement named into a
/// class's namespace (`MonoidRel::fold#meaning`) would be elaborated as that
/// class's member, whose constraint handling differs from the free theorem
/// the check means.
pub(crate) fn meaning_name(name: &str) -> String {
    format!("{}#meaning", name.replace("::", "__"))
}

/// A pattern binder.
fn pat(name: &str, span: Span) -> Pat {
    Pat::Var { name: name.to_string(), span }
}

fn split_on(scrut: &str, arms: Vec<Arm>, span: Span) -> Expr {
    Expr {
        kind: ExprKind::Match {
            form: MatchForm::Match,
            generated: true,
            scrut: Box::new(var(scrut, span)),
            eqbind: None,
            motive: None,
            arms,
        },
        span,
    }
}

fn arm(ctor: &str, binders: Vec<Pat>, body: Expr, span: Span) -> Arm {
    Arm { ctor: ctor.to_string(), default: false, binders, body, span }
}

/// Meaning's part of the elaborator.
pub(crate) struct Meaning<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for Meaning<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl Meaning<'_> {
    /// The proof of the equation: `scrut` split `depth` levels deep along its
    /// recursive fields, `refl` at every leaf. One level is the ordinary
    /// structural recursion; a course-of-values recursion that reads the
    /// predecessor's predecessor (`half`,
    /// docs/language/recursion/course-of-values-recursion-design.md) needs its source's nested
    /// `match` to reduce too, so the caller deepens on a refusal. A type this
    /// does not know the constructors of is split once, by a default arm.
    pub(crate) fn meaning_split(&self, scrut: &str, ty: &Ty, depth: usize, fresh: &mut usize, span: Span) -> Expr {
        let refl = Expr { kind: ExprKind::Refl, span };
        if depth == 0 {
            return refl;
        }
        let next = |fresh: &mut usize| {
            *fresh += 1;
            format!("{scrut}__m{fresh}")
        };
        let name = match &ty.kind {
            TyKind::Nat => "Nat",
            TyKind::Named { name, .. } => name.as_str(),
            _ => {
                return split_on(scrut, vec![Arm { ctor: "_".into(), default: true, binders: Vec::new(), body: refl, span }], span);
            }
        };
        if name == "Nat" {
            let k = next(fresh);
            let inner = self.meaning_split(&k, ty, depth - 1, fresh, span);
            return split_on(scrut, vec![arm("Zero", Vec::new(), refl, span), arm("Succ", vec![pat(&k, span)], inner, span)], span);
        }
        // Deeper than one level only along a single recursive field per
        // constructor (`Nat`, `List`): that is every course-of-values window
        // there is, and a branching type split d levels deep has a number of
        // leaves exponential in d.
        let linear = |ind: &crate::inductive::Inductive| {
            ind.ctors.iter().all(|c| c.kind.iter().filter(|k| !matches!(k, crate::inductive::FieldKind::Payload)).count() <= 1)
        };
        let ind = match self.lookup_inductive(name) {
            Some(ind) if ind.ctors.iter().all(|c| c.res.is_none()) && !ind.codata && (depth == 1 || linear(ind)) => {
                heather_kernel::rc::Rc::clone(ind)
            }
            _ if depth == 1 => {
                return split_on(scrut, vec![Arm { ctor: "_".into(), default: true, binders: Vec::new(), body: refl, span }], span);
            }
            _ => return self.meaning_split(scrut, ty, 1, fresh, span),
        };
        let arms = ind
            .ctors
            .iter()
            .map(|c| {
                let mut binders = Vec::new();
                let mut children = Vec::new();
                for kind in &c.kind {
                    if matches!(kind, crate::inductive::FieldKind::Plain) {
                        let b = next(fresh);
                        binders.push(pat(&b, span));
                        children.push(b);
                    } else {
                        binders.push(pat("_", span));
                    }
                }
                // Each recursive field split in turn, the next one at every
                // leaf of the one before.
                let mut body = Expr { kind: ExprKind::Refl, span };
                for child in children.iter().rev() {
                    body = self.meaning_split_then(child, ty, depth - 1, fresh, body, span);
                }
                arm(&c.name, binders, body, span)
            })
            .collect();
        split_on(scrut, arms, span)
    }

    /// [`Self::meaning_split`] of `scrut`, with `leaf` in place of each
    /// `refl` (so that a second recursive field is split under the first).
    fn meaning_split_then(&self, scrut: &str, ty: &Ty, depth: usize, fresh: &mut usize, leaf: Expr, span: Span) -> Expr {
        let split = self.meaning_split(scrut, ty, depth, fresh, span);
        replace_refl(split, &leaf)
    }
}

fn replace_refl(e: Expr, leaf: &Expr) -> Expr {
    match e.kind {
        ExprKind::Refl => leaf.clone(),
        ExprKind::Match { form, generated, scrut, eqbind, motive, arms } => Expr {
            kind: ExprKind::Match {
                form,
                generated,
                scrut,
                eqbind,
                motive,
                arms: arms.into_iter().map(|a| Arm { body: replace_refl(a.body, leaf), ..a }).collect(),
            },
            span: e.span,
        },
        kind => Expr { kind, span: e.span },
    }
}

/// `theorem f#meaning(x̄): f(x̄) = { body } { proof }`.
pub(crate) fn meaning_decl(decl: &Decl, proof: Expr) -> Decl {
    let span = decl.span;
    Decl {
        kind: DeclKind::Theorem,
        is_meta: false,
        is_evidence: false,
        value: false,
        is_interface: false, partial: None,
        elaborates: None,
        name: meaning_name(&decl.name),
        tyvars: decl.tyvars.clone(),
        params: decl.params.clone(),
        result: Ty {
            kind: TyKind::Eq(Box::new(call(decl, span)), Box::new(qualified_source(decl))),
            span,
        },
        decreases: None,
        unfolding: Vec::new(),
        body: Block { stmts: Vec::new(), result: Box::new(proof), ons: Vec::new(), span: decl.body.span },
        span,
    }
}

/// How deep [`MeaningMut::recursion_meaning`] splits before it believes a
/// refusal: depth one is plain structural recursion, and each further level
/// is one more predecessor a course-of-values window reads.
const MAX_SPLIT_DEPTH: usize = 5;

/// Meaning checks' part of the elaborator that writes.
pub(crate) struct MeaningMut<'e>(pub(crate) &'e mut Elaborator);

impl std::ops::Deref for MeaningMut<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl std::ops::DerefMut for MeaningMut<'_> {
    fn deref_mut(&mut self) -> &mut Elaborator {
        self.0
    }
}

impl MeaningMut<'_> {
    /// Check that the just-committed structural `fn` `decl`, whose recursion
    /// descended on the parameters `decs` (type parameters counted first),
    /// unfolds to its source, without registering anything.
    pub(crate) fn recursion_meaning(&mut self, decl: &Decl, decs: &[String]) -> Verdict {
        let Some(dec) = decs.iter().find_map(|d| decl.params.iter().position(|p| &p.name == d)) else {
            return Verdict::Undecided("the recursion descends on a parameter the declaration does not write".into());
        };
        if !decl.body.ons.is_empty() {
            return Verdict::Undecided("the body discharges goals with `on`".into());
        }
        let span = decl.span;
        let dec_name = decl.params[dec].name.clone();
        let dec_ty = decl.params[dec].ty.clone();
        // The plans, cheapest first: the recursed parameter alone, deeper
        // for each predecessor a course-of-values window reads; then each
        // parameter the body case-splits on, once, around it. A split that
        // the recursion does not descend through is evaluated outside the
        // recursor, so its other arms only meet the source's after the
        // split's own parameter is a constructor (`inner`, #389's outer case
        // split).
        let mut plans: Vec<Expr> = (1..=MAX_SPLIT_DEPTH)
            .map(|depth| Meaning(self).meaning_split(&dec_name, &dec_ty, depth, &mut 0, span))
            .collect();
        for (i, p) in decl.params.iter().enumerate() {
            if i == dec || !scrutinized(&decl.body, &p.name) {
                continue;
            }
            for depth in 1..=2 {
                let mut fresh = 0;
                let inner = Meaning(self).meaning_split(&dec_name, &dec_ty, depth, &mut fresh, span);
                let outer = Meaning(self).meaning_split(&p.name, &p.ty, 1, &mut fresh, span);
                plans.push(replace_refl(outer, &inner));
            }
        }
        // A type split no deeper than one level gives the same plan at every
        // depth; gate each distinct plan once.
        let mut seen = std::collections::HashSet::new();
        plans.retain(|p| seen.insert(format!("{p:?}")));
        let mut differs: Option<Verdict> = None;
        let mut undecided: Option<Verdict> = None;
        for (n, proof) in plans.into_iter().enumerate() {
            let statement = meaning_decl(decl, proof);
            let verdict = self.gate_and_forget(&statement, span);
            match verdict {
                Verdict::Holds => return Verdict::Holds,
                // Not stated, or out of fuel, at the cheapest plan: the
                // deeper ones state the same equation at more cost.
                Verdict::Undecided(_) if n == 0 => return verdict,
                Verdict::Differs(_) => {
                    differs.get_or_insert(verdict);
                }
                Verdict::Undecided(_) => {
                    undecided.get_or_insert(verdict);
                }
            }
        }
        differs.or(undecided).expect("at least one plan was tried")
    }

    /// Elaborate and gate `statement` as an ordinary declaration, then take
    /// every trace of it back: nothing is registered, and its diagnostics
    /// are dropped.
    fn gate_and_forget(&mut self, statement: &Decl, span: Span) -> Verdict {
        // Gated inline: at a wider pool the proof would be queued, `Ok` would
        // mean only that the statement elaborated, and a refusal would fail
        // the whole module's join. Always rolled back: the `Err` arm carries
        // the verdict out.
        let width = self.pass.kernel_pool.swap_width(1);
        let mut verdict = Verdict::Holds;
        let _ = self.session_transaction(|me| -> crate::R<()> {
            let warn_mark = me.pass.warnings.borrow().len();
            let r = me.elab_decl_one(statement, None);
            me.pass.warnings.borrow_mut().truncate(warn_mark);
            verdict = match r {
                Ok(()) => Verdict::Holds,
                Err(e @ ElabError::Kernel { err: TypeError::NotConvertible, .. }) => Verdict::Differs(e.message()),
                Err(e) => Verdict::Undecided(e.message()),
            };
            Err(ElabError::Elab { msg: String::new(), span })
        });
        self.pass.kernel_pool.swap_width(width);
        verdict
    }

    /// Check that the `fn` `decl`, just committed, means its source: a
    /// [`Verdict::Differs`] is the declaration's refusal, located at it; a
    /// [`Verdict::Undecided`] is no evidence either way, so it refuses
    /// nothing and is reported only in review mode (`heather check
    /// --review`), as the `recursion-meaning` lint. Only a `fn` whose
    /// self-calls were lowered under a guard (or at the top) has a recursion
    /// to check.
    pub(crate) fn check_recursion_meaning(&mut self, decl: &Decl) -> crate::R<()> {
        let decs = self.attempt.recursion_decs.borrow().clone();
        if decs.is_empty() || !(self.policy.meaning_check || self.policy.review_lints) {
            return Ok(());
        }
        let name = &decl.name;
        match self.recursion_meaning(decl, &decs) {
            Verdict::Holds => {}
            Verdict::Differs(why) => {
                let msg = format!(
                    "the compiled `{name}` does not unfold to its source: `{}` was refused ({}); \
                     the structural lowering computes something other than the body says, which is a \
                     compiler bug (issues/recursion-meaning-check.md); writing the recursion with \
                     `decreases` lowers it by measure instead",
                    meaning_name(name),
                    one_line(&why),
                );
                if self.policy.meaning_check {
                    return Err(ElabError::Elab { msg, span: decl.span });
                }
                self.emit_lint(Lint::RecursionMeaning, msg, decl.span);
            }
            Verdict::Undecided(why) if self.policy.review_lints => self.emit_lint(
                Lint::RecursionMeaning,
                format!(
                    "could not decide whether `{name}` unfolds to its source: `{}` was not settled ({}) \
                     (issues/recursion-meaning-check.md)",
                    meaning_name(name),
                    one_line(&why),
                ),
                decl.span,
            ),
            Verdict::Undecided(_) => {}
        }
        Ok(())
    }
}

fn one_line(s: &str) -> String {
    let first = s.lines().next().unwrap_or("").trim();
    if first.chars().count() > 240 {
        let cut: String = first.chars().take(240).collect();
        format!("{cut}…")
    } else {
        first.to_string()
    }
}

/// Whether some `match` in `body` scrutinizes the bare name `name` (a case
/// split on that parameter, unless a binder shadows it, which costs only a
/// plan that does not help).
fn scrutinized(body: &Block, name: &str) -> bool {
    let mut found = false;
    let whole = Expr {
        kind: ExprKind::Block(Box::new(Block {
            stmts: body.stmts.clone(),
            result: body.result.clone(),
            ons: Vec::new(),
            span: body.span,
        })),
        span: body.span,
    };
    visit(&whole, &mut |e| {
        if let ExprKind::Match { scrut, .. } = &e.kind
            && matches!(&scrut.kind, ExprKind::Var(v) if v == name)
        {
            found = true;
        }
    });
    found
}

fn visit(e: &Expr, f: &mut impl FnMut(&Expr)) {
    f(e);
    match &e.kind {
        ExprKind::Match { scrut, arms, .. } => {
            visit(scrut, f);
            arms.iter().for_each(|a| visit(&a.body, f));
        }
        ExprKind::Block(b) => {
            for st in &b.stmts {
                if let heather_syntax::ast::Stmt::Let { expr, .. } = st {
                    visit(expr, f);
                }
            }
            visit(&b.result, f);
        }
        _ => crate::surface::for_each_child(e, &mut |c| visit(c, f)),
    }
}
