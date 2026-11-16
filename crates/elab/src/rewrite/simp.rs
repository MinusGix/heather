//! `simp_only(r₁, …, rₙ)`: the goal normalised by a list of laws
//! (`docs/tactics/simp-design.md`, `issues/simp-tactic.md`).
//!
//! Each law is an equation `a = b`, a relation step `R(a, b)` or a law
//! between statements `P ↔ Q` (`statement.rs`), applied or not, used left to
//! right. The driver takes the first law that has an
//! instance in the goal, rewrites every occurrence of that instance exactly
//! as `rewrite` would (the `J` form for an equation, the relation walk with
//! its congruence evidence for a relation), and starts again from the first
//! law, until none fires. Both sides of a goal that is itself an equation or
//! a relation application are in the goal, so both are normalised.
//!
//! What is left is closed one of three ways. With nothing more written, by
//! reflexivity: the two sides have met (a *closing* call, and a *stated*
//! step of a `calc`, whose two ends are both written). With `using := h`,
//! by `h`, whose type is normalised the same way and must then be the
//! normalised goal. With `then := e`, by `e`, checked at the normal form.
//!
//! A law with a side condition (an argument its left side does not
//! determine and nothing after depends on) fires where the condition is a
//! hypothesis in scope, or where `discharge := e` checks at it.
//!
//! Nothing is trusted: every step is the term `rewrite` builds, and the
//! declaration gate checks the whole. A call that does not close reports
//! the route it took, the normal forms it reached and the laws that were
//! blocked; `simp_show` reports the same for a call that would have closed.

use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::rc::Rc;
use heather_kernel::term::{LocalSubst, LocalVar, Term, Type};
use heather_syntax::{Expr, ExprKind, Item, NamedArg, Span, parse_file};
use heather_syntax::ast::TyKind;

use super::relation::{Plan, Polarity, RelationRewrite, Relations};
use super::statement::{Leaf, StatementOutcome, StatementStep, Statements};
use super::{Equation, Miss, Rewrites};
use crate::relational_context::proof::Relation;
use crate::{Cx, ElabError, Elaborator, R};

/// The simplifier's part of the elaborator.
pub(crate) struct Simps<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for Simps<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

/// Steps one run may take. A set of laws that does not terminate (a law
/// whose right side its own left side matches) stops here, and the report
/// shows the steps that repeat.
const BUDGET: usize = 256;

/// The steps of a route a report prints: its first and last few.
const SHOWN: usize = 12;

const GOAL: &str = "the goal";

struct Rule<'x> {
    expr: &'x Expr,
    proof: Term,
    ty: Type,
    name: String,
    /// A law between statements, `P ↔ Q`.
    iff: bool,
    /// A definition named among the laws, by its position in Ψ: its calls
    /// are unfolded as the goal is computed, and it never fires as a
    /// rewrite.
    unfold: Option<usize>,
    /// A generated branch equation (`clamp::True`) a named definition
    /// brought: each binder its left side leaves open is a test hypothesis.
    branch: bool,
    /// A measured (`decreases`) definition whose branch equations stand in
    /// for its body: its calls are not unfolded, as its body is a
    /// well-founded recursion's (`f#body(…, f#rec(…))`) that no law reads
    /// and no proof should meet.
    kept: bool,
}

/// One step taken: what `rewrite` needs to build its proof.
enum Fired<'a> {
    Relation { step: Box<RelationRewrite<'a>>, plan: Plan },
    Equation { level: Level, ty: Rc<Type>, lhs: Rc<Term>, rhs: Rc<Term>, proof: Term, motive: Type },
    Statement(Box<StatementStep>),
}

/// The two sides of the instance a step rewrote, as a route prints them.
enum Sides {
    Terms(Rc<Term>, Rc<Term>),
    /// Already spelled, where the instance was found.
    Statements(String, String),
}

struct Step<'a> {
    rule: usize,
    fired: Fired<'a>,
    /// The instance's two sides, where they are scoped in the goal's
    /// context: what the route prints.
    sides: Option<Sides>,
}

/// A type normalised: the steps in the order taken, where they end, and the
/// laws that had an instance and did not fire, each with its reason.
struct Run<'a> {
    steps: Vec<Step<'a>>,
    end: Type,
    blocked: Vec<(usize, String)>,
    exhausted: bool,
    /// The steps return to the statement that stood after this many of
    /// them: a loop, found without spending the budget.
    cycle: Option<usize>,
}

enum Outcome<'a> {
    Fired(Fired<'a>, Type, Option<Sides>),
    Blocked(String),
    Miss,
}

impl Simps<'_> {
    /// `simp_only(r₁, …, rₙ)` at `goal`; `show` for `simp_show`, which
    /// reports the result and never closes.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn elab_simp(
        &self,
        cx: &Cx,
        show: bool,
        args: &[Expr],
        named: &[NamedArg],
        goal: &Type,
        lvl: &Level,
        span: Span,
    ) -> R<Term> {
        let form = if show { "simp_show" } else { "simp_only" };
        let (mut discharge, mut then, mut using) = (None, None, None);
        for arg in named {
            let slot = match arg.name.as_str() {
                "discharge" => &mut discharge,
                "then" => &mut then,
                "using" => &mut using,
                _ => {
                    return Err(ElabError::Elab {
                        msg: format!(
                            "`{form}` takes `discharge := e` (a proof tried at each side \
                             condition), `then := e` (the proof of what is left) and \
                             `using := h` (a fact that is the goal once both are simplified), \
                             and not `{} :=`",
                            arg.name
                        ),
                        span: arg.name_span,
                    });
                }
            };
            if slot.is_some() {
                return Err(ElabError::Elab { msg: format!("`{form}`: `{} :=` is given twice", arg.name), span: arg.name_span });
            }
            *slot = Some(&arg.expr);
        }
        if let (Some(_), Some(u)) = (then, using) {
            return Err(ElabError::Elab {
                msg: format!("`{form}` takes `then :=` or `using :=`, not both: each says how what is left is proved"),
                span: u.span,
            });
        }
        if args.is_empty() {
            return Err(ElabError::Elab {
                msg: format!("`{form}` takes the laws to simplify with: `{form}(h₁, …, hₙ)`"),
                span,
            });
        }
        // A definition named to unfold brings its branch equations
        // (`clamp::True`, `clamp::False::True`, …) as laws: a call whose
        // test the context decides takes that branch, its side condition
        // discharged like any law's, and a call whose test nothing decides
        // is unfolded as before (docs/tactics/program-proof-tactics-design.md §3 D).
        let mut branches: Vec<(Expr, String)> = Vec::new();
        let mut rules = Vec::with_capacity(args.len());
        for (i, h) in args.iter().enumerate() {
            let (proof, ty, _) = self.elab_infer(cx, h)?;
            let mut rule = self.law(cx, form, h, rule_name(h, i), proof, ty)?;
            if let Some(abs) = rule.unfold {
                let (found, measured) = self.branch_equation_names(abs, h.span);
                rule.kept = measured && !found.is_empty();
                branches.extend(found);
            }
            rules.push(rule);
        }
        for (e, designed) in &branches {
            let Ok((proof, ty, _)) = self.elab_infer(cx, e) else { continue };
            rules.push(Rule { expr: e, proof, ty, name: format!("`{designed}`"), iff: false, unfold: None, branch: true, kept: false });
        }
        self.run_simp(cx, form, show, &rules, discharge, then, using, goal, lvl, span)
    }

    /// The generated branch equations of the definition at Ψ position
    /// `abs`, each as a reference to its minted global and its designed
    /// spelling (`f::False::True`): every path of arms through the body's
    /// tests that names one, at any depth, in the order they should be
    /// tried (`branch_equations::test_paths`). With them, whether the
    /// definition is measured (`decreases`).
    fn branch_equation_names(&self, abs: usize, span: Span) -> (Vec<(Expr, String)>, bool) {
        let Some(key) = self.names.global_name_at(abs as u32).map(str::to_string) else { return (Vec::new(), false) };
        let decl = match key.split_once("::") {
            Some((module, name)) => self.names.surface_decl_in(module, name),
            None => self.names.surface_decl(&key),
        }
        .cloned();
        // A measured definition is registered as its lowering (a call of
        // its `#rec`), which says nothing of its tests: it is known by its
        // `f_unfold`.
        let measured = self.names.global(&crate::measure::unfold_name(&key)).is_some();
        if !measured && decl.as_ref().is_some_and(|decl| !crate::branch_equations::candidate(decl)) {
            return (Vec::new(), false);
        }
        let designed = |segments: &[&str]| crate::branch_equations::designed_name(key.split_once("::").map_or(key.as_str(), |(_, name)| name), segments);
        // The body's own tests say where an equation may be: every path of
        // arms through them, at any depth. A measured definition's body is
        // read off its `f_unfold`, `f(x̄) = body`.
        let body = if measured {
            let unfold = crate::measure::unfold_name(&key);
            match unfold.split_once("::") {
                Some((module, name)) => self.names.surface_decl_in(module, name),
                None => self.names.surface_decl(&unfold),
            }
            .and_then(|decl| match &decl.result.kind {
                TyKind::Eq(_, body) => Some((**body).clone()),
                _ => None,
            })
        } else {
            decl.map(|decl| Expr { kind: ExprKind::Block(Box::new(decl.body)), span })
        };
        if let Some(body) = &body {
            let mut found = Vec::new();
            for path in crate::branch_equations::test_paths(body) {
                let segments: Vec<&str> = path.iter().map(String::as_str).collect();
                let minted = crate::branch_equations::minted_name(&key, &segments);
                if self.names.global(&minted).is_some() {
                    found.push((Expr { kind: ExprKind::Var(minted), span }, designed(&segments)));
                }
            }
            return (found, measured);
        }
        // No body to read (registered without its surface): every path of
        // `True`/`False` below one that names no equation, six tests deep,
        // as a blind search doubles at each test.
        let mut found = Vec::new();
        let mut paths: Vec<Vec<String>> = vec![vec!["True".into()], vec!["False".into()]];
        while let Some(path) = paths.pop() {
            let segments: Vec<&str> = path.iter().map(String::as_str).collect();
            let minted = crate::branch_equations::minted_name(&key, &segments);
            if self.names.global(&minted).is_some() {
                found.push((Expr { kind: ExprKind::Var(minted), span }, designed(&segments)));
            } else if path.len() < 6 {
                for arm in ["True", "False"] {
                    let mut deeper = path.clone();
                    deeper.push(arm.to_string());
                    paths.push(deeper);
                }
            }
        }
        (found, measured)
    }

    /// The host's entry (`Req::Simp`, docs/tactics/simp-design.md §7): the goal
    /// closed by laws that are already terms, each with the name a report
    /// calls it by. What `simp_only(l₁, …, lₙ)` does, under the name `simp`.
    pub(crate) fn simp_terms(&self, cx: &Cx, laws: Vec<(String, Term, Type)>, goal: &Type, lvl: &Level, span: Span) -> R<Term> {
        let exprs: Vec<Expr> = laws.iter().map(|(name, ..)| Expr { kind: ExprKind::Var(name.clone()), span }).collect();
        let mut rules = Vec::with_capacity(laws.len());
        for (h, (name, proof, ty)) in exprs.iter().zip(laws) {
            rules.push(self.law(cx, "simp", h, format!("`{name}`"), proof, ty)?);
        }
        // The report is `simp_only`'s, under the caller's name.
        self.run_simp(cx, "simp", false, &rules, None, None, None, goal, lvl, span).map_err(|e| match e {
            ElabError::Elab { msg, span } => ElabError::Elab { msg: msg.replace("`simp_only`", "`simp`"), span },
            other => other,
        })
    }

    /// A list of laws checked as a rewrite system, as far as running it
    /// shows (docs/tactics/simp-design.md §4): each law's own statement, at its
    /// binders as fresh variables, is normalised by the whole list. A run
    /// that loops means the list has no normal form at that law's instances
    /// (a commuting law, two laws that undo each other); a run whose two
    /// sides do not meet means another law fired on the left side first and
    /// the two results do not join, an overlap the author closes with the
    /// equation named. Overlaps that need both left sides instantiated
    /// (associativity against a unit) are not found: that is unification of
    /// the two, which this does not do.
    pub(crate) fn check_terms(&self, cx: &Cx, laws: Vec<(String, Term, Type, Level)>, span: Span) -> R<()> {
        let exprs: Vec<Expr> = laws.iter().map(|(name, ..)| Expr { kind: ExprKind::Var(name.clone()), span }).collect();
        for (i, (name, _, law_ty, law_lvl)) in laws.iter().enumerate() {
            // The law's binders as locals, its conclusion under them.
            let mut here = cx.clone();
            let mut cur = self.whnf(&here, law_ty, span)?;
            let mut lvl = law_lvl.clone();
            let mut k = 0u32;
            while let Type::Pi { dom_level, cod_level, dom, cod } = cur {
                here.push(format!("x{k}"), (*dom).clone(), dom_level);
                lvl = cod_level;
                k += 1;
                cur = self.whnf(&here, &cod, span)?;
            }
            // The statement as written, not its head normal form: a
            // relation's application, not what the relation unfolds to.
            let mut written = law_ty;
            for _ in 0..k {
                let Type::Pi { cod, .. } = written else { break };
                written = cod;
            }
            let statement = if matches!(written, Type::Pi { .. }) { &cur } else { written };
            let mut rules = Vec::with_capacity(laws.len());
            for (h, (n, proof, ty, _)) in exprs.iter().zip(&laws) {
                rules.push(self.law(&here, "simp_check", h, format!("`{n}`"), proof.shift_local(k), ty.shift_local(k))?);
            }
            let relations = Relations(self.0);
            let run = self.normalise(&relations, &here, &rules, statement, &lvl, None, None)?;
            if run.cycle.is_some() || run.exhausted {
                return Err(ElabError::Elab {
                    msg: format!(
                        "`simp_check`: these laws have no normal form at an instance of law {} \
                         `{name}`: rewriting its own statement loops\n  note: a law whose right \
                         side its own left side matches (commutativity), or two laws that undo \
                         each other, cannot both be in a set{}",
                        i + 1,
                        self.report(&here, &rules, &run, None)
                    ),
                    span,
                });
            }
            let sides = match &run.end {
                Type::Id { lhs, rhs, .. } => Some((Rc::clone(lhs), Rc::clone(rhs))),
                end => Relation::of_type(self.0, &here, end, span).map(|rel| (rel.left, rel.right)),
            };
            // A law between statements: its two sides are statements.
            let apart = match (&sides, Statements(self.0).iff_sides(&here, &run.end)) {
                (Some((left, right)), _) => {
                    (left != right && !Rewrites(self.0).terms_convert(&here, left, right)).then(|| {
                        let shown = |t: &Term| self.spell_term_clean(&here, t).unwrap_or_else(|| "…".into());
                        (shown(left), shown(right))
                    })
                }
                (None, Some([(left, level), (right, _)])) => (left != right && !self.conv_types(&here, &left, &right, &level))
                    .then(|| (self.display_type(&here, &left), self.display_type(&here, &right))),
                (None, None) => None,
            };
            if let Some((left, right)) = apart {
                let shown = |t: &String| t.clone();
                return Err(ElabError::Elab {
                    msg: format!(
                        "`simp_check`: law {} `{name}` overlaps another law, and the two results \
                         do not join: its left side normalises to\n    {}\n  and its right side \
                         to\n    {}\n  note: a term these laws both rewrite has two normal \
                         forms; add the equation between them as a law, or drop one of the \
                         two{}",
                        i + 1,
                        shown(&left),
                        shown(&right),
                        self.report(&here, &rules, &run, None)
                    ),
                    span,
                });
            }
        }
        Ok(())
    }

    /// A law of the list: what it concludes is read where it fires; a proof
    /// of something that is no statement at all is refused here, used or
    /// not.
    fn law<'x>(&self, cx: &Cx, form: &str, h: &'x Expr, name: String, proof: Term, ty: Type) -> R<Rule<'x>> {
        let mut conclusion = &ty;
        while let Type::Pi { cod, .. } = conclusion {
            conclusion = cod;
        }
        let iff = Statements(self.0).is_law(cx, &ty, h.span);
        // A definition, not a proof: `simp_only(Node::step)` unfolds it.
        let definition = || {
            let Term::GlobalTm { var, .. } = &proof else { return None };
            let abs = self.global_abs_of(*var)?;
            self.goal_oracle().unfold(&cx.gamma, &proof, crate::oracle::Unfold::OneStep).next()?;
            Some(abs)
        };
        // A transparent definition (a theorem's proof is opaque) whose
        // result is not a statement: a function, not a law.
        if !iff && !matches!(conclusion, Type::Id { .. })
            && let Some(abs) = definition()
        {
            let mut below = cx.clone();
            let mut cur = &ty;
            while let Type::Pi { dom, dom_level, cod, .. } = cur {
                below.push("_".into(), (**dom).clone(), dom_level.clone());
                cur = cod;
            }
            // A type former of two types (`Mutated<Sha256, u64>`, what a
            // `mut self` function returns) has a relation's shape and is
            // no relation: its values are not related by it.
            if Relation::of_type(self.0, &below, cur, h.span).is_none_or(|rel| matches!(*rel.carrier, Type::Ty(_))) {
                return Ok(Rule { expr: h, proof, ty, name, iff, unfold: Some(abs), branch: false, kept: false });
            }
        }
        if !iff && !matches!(conclusion, Type::Id { .. } | Type::El { .. } | Type::M { .. }) {
            return Err(ElabError::Elab {
                msg: format!(
                    "`{form}`: {name} is not a law: a law is a proof of an equation `a = b`, of \
                     a relation `R(a, b)` or of `P ↔ Q`, under any hypotheses, or a definition \
                     to unfold, and this is of type `{}`",
                    self.display_type(cx, &ty)
                ),
                span: h.span,
            });
        }
        Ok(Rule { expr: h, proof, ty, name, iff, unfold: None, branch: false, kept: false })
    }

    /// The run and what closes it, for laws already elaborated.
    #[allow(clippy::too_many_arguments)]
    fn run_simp(
        &self,
        cx: &Cx,
        form: &str,
        show: bool,
        rules: &[Rule<'_>],
        discharge: Option<&Expr>,
        then: Option<&Expr>,
        using: Option<&Expr>,
        goal: &Type,
        lvl: &Level,
        span: Span,
    ) -> R<Term> {
        let relations = Relations(self.0);
        let closing = !show && then.is_none() && using.is_none();
        let mut run = self.normalise(&relations, cx, rules, goal, lvl, discharge, closing.then_some(span))?;
        if let Some(back) = run.cycle {
            let from = if back == 0 { "the goal as written".to_string() } else { format!("the statement after step {back}") };
            return Err(ElabError::Elab {
                msg: format!(
                    "`{form}`: these laws loop: step {} returns to {from},\n    {}\n  note: a \
                     law whose right side its own left side matches (commutativity), or two \
                     laws that undo each other, have no normal form; drop one, or apply it \
                     with `rewrite` at the one place it is wanted{}",
                    run.steps.len(),
                    self.display_type(cx, &run.end),
                    self.report(cx, rules, &run, None)
                ),
                span,
            });
        }
        if run.exhausted {
            return Err(ElabError::Elab {
                msg: format!(
                    "`{form}`: no normal form after {BUDGET} steps\n  note: a law whose right \
                     side its own left side matches (commutativity) rewrites for ever; the \
                     route's end shows which laws repeat{}",
                    self.report(cx, rules, &run, None)
                ),
                span,
            });
        }
        if show {
            return Err(ElabError::Elab {
                msg: format!(
                    "`simp_show`: the goal simplifies to\n    {}{}\n  note: `simp_show` never \
                     closes a goal; write `simp_only` once the result is what you expect",
                    self.display_type(cx, &run.end),
                    self.report(cx, rules, &run, None)
                ),
                span,
            });
        }
        let inner = if let Some(e) = then {
            self.elab_check(cx, e, &run.end, lvl)?
        } else if let Some(h) = using {
            let (fact, fact_ty, fact_lvl) = self.elab_infer(cx, h)?;
            let mut fact_run = self.normalise(&relations, cx, rules, &fact_ty, &fact_lvl, discharge, None)?;
            if fact_run.exhausted || fact_run.cycle.is_some() || !self.conv_types(cx, &fact_run.end, &run.end, lvl) {
                return Err(ElabError::Elab {
                    msg: format!(
                        "`simp_only`: the goal and the fact given by `using :=` do not simplify \
                         to the same statement\n  the goal:\n    {}\n  the fact:\n    {}{}{}",
                        self.display_type(cx, &run.end),
                        self.display_type(cx, &fact_run.end),
                        self.report(cx, rules, &run, Some("the goal's")),
                        self.report(cx, rules, &fact_run, Some("the fact's")),
                    ),
                    span: h.span,
                });
            }
            self.assemble(&mut fact_run, Polarity::Forward, fact, &fact_lvl)?
        } else {
            match self.close(&relations, cx, &run.end, lvl, span)? {
                Some(closed) => closed,
                None => return Err(self.open(cx, rules, &run, span)),
            }
        };
        self.assemble(&mut run, Polarity::Backward, inner, lvl)
    }

    /// `start` rewritten until no law fires.
    fn normalise<'a>(
        &self,
        relations: &'a Relations<'a>,
        cx: &'a Cx,
        rules: &[Rule<'_>],
        start: &Type,
        lvl: &Level,
        discharge: Option<&Expr>,
        closing: Option<Span>,
    ) -> R<Run<'a>> {
        // Each side condition is discharged once per context: a call's
        // branch equations share their tests' prefixes (`clamp::False::True`
        // and `clamp::False::False` both ask `¬(x < lo)`), and the laws are
        // tried at every step, so a discharger that fails (`bv_omega`
        // searching for a contradiction) would otherwise fail again at each.
        // Only at the call's own context: under a binder another subterm at
        // the same depth may bind other locals.
        //
        // A condition whose complement is already discharged is not tried:
        // the two arms of one test ask `P` and `¬P` (`clamp::True` and
        // `clamp::False`), at most one holds, and a discharger that fails
        // (`bv_omega` searching for a contradiction) costs several times one
        // that succeeds.
        let discharged: std::cell::RefCell<Vec<(Type, Option<Type>, Level, Option<Term>)>> = std::cell::RefCell::new(Vec::new());
        let premise = |at: &Cx, ty: &Type, level: &Level, _dependent: bool| {
            let top = at.gamma.len() == cx.gamma.len();
            let negated = if top { crate::omega_cert::negated_domain(self.0, at, ty) } else { None };
            if top {
                let known = discharged.borrow();
                if let Some((_, _, _, found)) = known.iter().find(|(t, _, l, _)| t == ty && l == level) {
                    return found.clone();
                }
                let complement = known.iter().any(|(t, not, l, found)| {
                    found.is_some()
                        && (negated.as_ref().is_some_and(|n| self.conv_types(at, n, t, l))
                            || not.as_ref().is_some_and(|n| self.conv_types(at, n, ty, level)))
                });
                if complement {
                    return None;
                }
            }
            // `¬P` where `P` is a hypothesis: the discharger would only
            // search for the contradiction.
            if discharge.is_some() && negated.as_ref().is_some_and(|p| self.discharge(at, p, level, None).is_some()) {
                if top {
                    discharged.borrow_mut().push((ty.clone(), negated, level.clone(), None));
                }
                return None;
            }
            let found = self.discharge(at, ty, level, discharge);
            if top {
                discharged.borrow_mut().push((ty.clone(), negated, level.clone(), found.clone()));
            }
            found
        };
        let mut run = Run { steps: Vec::new(), end: start.clone(), blocked: Vec::new(), exhausted: false, cycle: None };
        let unfolds: Vec<usize> = rules.iter().filter(|rule| !rule.kept).filter_map(|rule| rule.unfold).collect();
        // An applied law's left side names its terms (`zeroed(R, 0, 64).hash`
        // names `R`, a call whose body would compute): they stay as written
        // while the goal computes, so the law can meet them. A call of a
        // definition the call lists to unfold is not kept: listing it asks
        // for its body.
        let frozen: Vec<Rc<Term>> = rules
            .iter()
            .filter(|rule| rule.unfold.is_none() && !rule.iff)
            .filter_map(|rule| match &rule.ty {
                Type::Id { lhs, .. } => Some(Type::El { level: Level::Zero, tm: Rc::clone(lhs) }.root_terms()),
                _ => None,
            })
            .flatten()
            .filter(|t| crate::spelling::is_app(t) || crate::spelling::proj_of(t).is_some())
            .filter(|t| match crate::spelling::app_spine(t).0 {
                Term::GlobalTm { var, .. } => self.0.global_abs_of(*var).is_none_or(|abs| !unfolds.contains(&abs)),
                _ => true,
            })
            .collect();
        let mut seen = vec![start.clone()];
        let mut unfolded_blocked: Vec<(usize, String)> = Vec::new();
        'steps: loop {
            if run.steps.len() >= BUDGET {
                run.exhausted = true;
                return Ok(run);
            }
            // Calls at constructors compute (`simp(Seq(a, b))` is
            // `seq(simp(a), simp(b))`), as a split's goal does: a law's left
            // side is matched against what is written, and the definition's
            // own equations are not laws anyone should have to list.
            let computed = crate::goal_combinators::simplify_goal_unfolding(self.0, cx, &run.end, true, &unfolds, &frozen);
            if computed != run.end && self.conv_types(cx, &computed, &run.end, lvl) {
                // A law that fires on the goal and not on the computed goal
                // fires first: the computing would take its instance away, as
                // a law about a call (`Sha256::run_spec` at
                // `Sha256::run(s).after`) is lost once the call computes into
                // its body, a `mut self` function's calls in sequence. Only
                // such a law: one that fires on the computed goal fires
                // there, where the pattern children the computing names are
                // what other laws meet.
                for (i, rule) in rules.iter().enumerate() {
                    let outcome = self.fire(relations, cx, rule, &run.end, lvl, &premise)?;
                    // A branch equation blocked at the call, which the
                    // computing then unfolds: why its branch was not taken
                    // is what a failing report needs, and the normal form
                    // no longer holds the call to say it.
                    if rule.branch
                        && let Outcome::Blocked(why) = &outcome
                        && !unfolded_blocked.iter().any(|(j, _)| *j == i)
                    {
                        unfolded_blocked.push((i, format!("{why} (at the call, which was then unfolded)")));
                    }
                    if let Outcome::Fired(fired, next, sides) = outcome
                        && !matches!(self.fire(relations, cx, rule, &computed, lvl, &premise)?, Outcome::Fired(..))
                    {
                        run.steps.push(Step { rule: i, fired, sides });
                        run.end = next;
                        if let Some(back) = seen.iter().position(|ty| *ty == run.end) {
                            run.cycle = Some(back);
                            return Ok(run);
                        }
                        seen.push(run.end.clone());
                        continue 'steps;
                    }
                }
                run.end = computed;
            }
            // A closing call is done where the two sides are one term: a
            // law that still has an instance there (commutativity, at
            // `b + a = b + a`) would only move both.
            if let Some(span) = closing
                && self.met(cx, &run.end, span)
            {
                return Ok(run);
            }
            let mut blocked = Vec::new();
            for (i, rule) in rules.iter().enumerate() {
                match self.fire(relations, cx, rule, &run.end, lvl, &premise)? {
                    Outcome::Fired(fired, next, sides) => {
                        run.steps.push(Step { rule: i, fired, sides });
                        run.end = next;
                        if let Some(back) = seen.iter().position(|ty| *ty == run.end) {
                            run.cycle = Some(back);
                            return Ok(run);
                        }
                        seen.push(run.end.clone());
                        continue 'steps;
                    }
                    Outcome::Blocked(why) => blocked.push((i, why)),
                    Outcome::Miss => {}
                }
            }
            // What is blocked at the normal form is what the report is about.
            for (i, why) in &unfolded_blocked {
                if !blocked.iter().any(|(j, _)| j == i) {
                    blocked.push((*i, why.clone()));
                }
            }
            run.blocked = blocked;
            return Ok(run);
        }
    }

    /// Is `ty` an equation or a relation between one term and itself, as
    /// written?
    fn met(&self, cx: &Cx, ty: &Type, span: Span) -> bool {
        match ty {
            Type::Id { lhs, rhs, .. } => lhs == rhs,
            _ => {
                Relation::of_type(self.0, cx, ty, span).is_some_and(|rel| rel.left == rel.right)
                    || Statements(self.0).iff_sides(cx, ty).is_some_and(|[(l, _), (r, _)]| l == r)
            }
        }
    }

    /// One law at `ty`: every occurrence of its first instance rewritten.
    /// An equation or a relation step that has none at the goal as a whole
    /// is tried at the goal's operands, below `∧`, `∨`, `↔`, `¬`, `→` and
    /// `∀` (`statement.rs`): a connective's lowering holds an operand where
    /// a motive does not reach.
    fn fire<'a>(
        &self,
        relations: &'a Relations<'a>,
        cx: &'a Cx,
        rule: &Rule<'_>,
        ty: &Type,
        lvl: &Level,
        premise: super::Premise<'_>,
    ) -> R<Outcome<'a>> {
        if rule.unfold.is_some() {
            return Ok(Outcome::Miss);
        }
        // A side condition a later binder depends on is discharged only for
        // a definition's branch equation, where every binder matching leaves
        // open is the test the branch takes (`below: at < 64`, which the
        // arm passes on as its index's bound). Elsewhere such a binder may
        // be data, which no discharger should pick.
        let branch = rule.branch;
        let premise = &|at: &Cx, ty: &Type, level: &Level, dependent: bool| {
            if dependent && !branch { None } else { premise(at, ty, level, dependent) }
        };
        let direct = self.fire_at(relations, cx, rule, ty, lvl, premise)?;
        if rule.iff || matches!(direct, Outcome::Fired(..)) {
            return Ok(direct);
        }
        let leaf = |at: &Cx, depth: u32, operand: &Type, level: &Level| -> R<Result<Option<Leaf>, String>> {
            let deep = Rule {
                expr: rule.expr,
                proof: rule.proof.shift_local(depth),
                ty: rule.ty.shift_local(depth),
                name: rule.name.clone(),
                iff: false,
                unfold: None,
                branch: rule.branch,
                kept: false,
            };
            let relations = Relations(self.0);
            Ok(match self.fire_at(&relations, at, &deep, operand, level, premise)? {
                Outcome::Fired(mut fired, to, sides) => match self.directions(&mut fired, operand, &to, level) {
                    Ok((forward, backward)) => {
                        let sides = sides.and_then(|sides| match sides {
                            Sides::Terms(l, r) => Some((self.spell_term_clean(at, &l)?, self.spell_term_clean(at, &r)?)),
                            Sides::Statements(l, r) => Some((l, r)),
                        });
                        Ok(Some(Leaf { to, forward, backward, sides }))
                    }
                    Err(e) => Err(soft(e)?),
                },
                Outcome::Blocked(why) => Err(why),
                Outcome::Miss => Ok(None),
            })
        };
        Ok(match Statements(self.0).within(cx, ty, lvl, &leaf, rule.expr.span)? {
            StatementOutcome::Fired(mut step) => {
                let next = step.next.clone();
                let sides = step.sides.take().map(|(l, r)| Sides::Statements(l, r));
                Outcome::Fired(Fired::Statement(step), next, sides)
            }
            StatementOutcome::Blocked(why) if matches!(direct, Outcome::Miss) => Outcome::Blocked(why),
            _ => direct,
        })
    }

    /// The two directions of one step, `from → to` and `to → from`, as
    /// functions.
    fn directions(&self, fired: &mut Fired<'_>, from: &Type, to: &Type, lvl: &Level) -> R<(Term, Term)> {
        let lam = |dom: &Type, body: Term| Term::Lam {
            dom_level: lvl.clone(),
            cod_level: lvl.clone(),
            dom: Rc::new(dom.clone()),
            body: Rc::new(body),
        };
        let var = || Rc::new(Term::Var(LocalVar(0)));
        Ok(match fired {
            Fired::Statement(step) => (step.forward.0.clone(), step.backward.0.clone()),
            Fired::Relation { step, plan } => {
                let forward = step.emit(plan, Polarity::Forward, var(), 1)?;
                let backward = step.emit(plan, Polarity::Backward, var(), 1)?;
                (lam(from, Rc::unwrap_or_clone(forward)), lam(to, Rc::unwrap_or_clone(backward)))
            }
            // `J(h; y q. M[a] → M[y]; λ p. p) : M[a] → M[b]`, and the same
            // with the arrow turned round.
            Fired::Equation { level, ty, lhs, rhs, proof, motive } => {
                let arrow = |dom: Type, cod: Type| Type::Pi {
                    dom_level: lvl.clone(),
                    cod_level: lvl.clone(),
                    dom: Rc::new(dom),
                    cod: Rc::new(cod),
                };
                let transport = |motive: Type| Term::J {
                    ty_level: level.clone(),
                    motive_level: Level::max(lvl.clone(), lvl.clone()),
                    ty: Rc::clone(ty),
                    lhs: Rc::clone(lhs),
                    motive: Rc::new(motive),
                    case: Rc::new(lam(from, Term::Var(LocalVar(0)))),
                    rhs: Rc::clone(rhs),
                    proof: Rc::new(proof.clone()),
                };
                // Under `y`, `q`, and the arrow's own binder.
                let forward = transport(arrow(from.shift_local(2), motive.shift_local(2)));
                let backward = transport(arrow(motive.shift_local(1), from.shift_local(3)));
                (forward, backward)
            }
        })
    }

    /// [`Self::fire`] at `ty` as a whole.
    fn fire_at<'a>(
        &self,
        relations: &'a Relations<'a>,
        cx: &'a Cx,
        rule: &Rule<'_>,
        ty: &Type,
        lvl: &Level,
        premise: super::Premise<'_>,
    ) -> R<Outcome<'a>> {
        let missed = |miss: Miss| match miss {
            Miss::NoInstance => Ok(Outcome::Miss),
            Miss::Unbound { premise: Some((p, _)), .. } => Ok(Outcome::Blocked(format!(
                "its side condition `{}` is not a hypothesis here, and nothing discharged it",
                self.display_type(cx, &p)
            ))),
            Miss::Unbound { index, .. } => Ok(Outcome::Blocked(format!(
                "matching its left side does not determine its argument {index}; apply the law to it"
            ))),
            Miss::Hard(e) => {
                let msg = e.message();
                let Some(rest) = msg.strip_prefix("`rewrite` rewrites along an equation `a = b` or a relation `R(a, b)`, and this proof is of ") else {
                    return Err(e);
                };
                Err(ElabError::Elab {
                    msg: format!(
                        "`simp_only`: {} is not a law: a law is a proof of an equation `a = b`, \
                         of a relation `R(a, b)` or of `P ↔ Q`, under any hypotheses, and this \
                         is a proof of {rest}",
                        rule.name
                    ),
                    span: rule.expr.span,
                })
            }
        };
        if rule.iff {
            let outcome = Statements(self.0).step(cx, &rule.name, &rule.proof, &rule.ty, ty, lvl, Some(premise), rule.expr.span)?;
            return Ok(match outcome {
                StatementOutcome::Fired(mut step) => {
                    let next = step.next.clone();
                    let sides = step.sides.take().map(|(l, r)| Sides::Statements(l, r));
                    Outcome::Fired(Fired::Statement(step), next, sides)
                }
                StatementOutcome::Blocked(why) => Outcome::Blocked(why),
                StatementOutcome::Miss => Outcome::Miss,
            });
        }
        match relations.relation_step_or(cx, rule.expr, &rule.proof, &rule.ty, ty, Some(premise)) {
            Ok(Some(mut step)) => {
                step.refused = Some(Vec::new());
                return match step.goal(ty, GOAL) {
                    Ok((_, Plan::Same)) => Ok(Outcome::Miss),
                    Ok((next, plan)) => {
                        if step.occurrences() == 0 || next == *ty {
                            return Ok(Outcome::Miss);
                        }
                        let sides = step.sides().map(|(l, r)| Sides::Terms(l, r)).or_else(|| step.shown.clone().map(|(l, r)| Sides::Statements(l, r)));
                        Ok(Outcome::Fired(Fired::Relation { step: Box::new(step), plan }, next, sides))
                    }
                    Err(e) => soft(e).map(Outcome::Blocked),
                };
            }
            Ok(None) => {}
            Err(miss) => return missed(miss),
        }
        let rw = Rewrites(self.0);
        let (proof, Equation { level, ty: carrier, lhs, rhs }) =
            match rw.rewrite_instance_or(cx, rule.expr, rule.proof.clone(), &rule.ty, ty, Some(premise)) {
                Ok(found) => found,
                // No instance the transport reaches: one under a λ is
                // reached by the relation walk, at the identity relation.
                Err(Miss::NoInstance) => return self.fire_identity(relations, cx, rule, ty, premise),
                Err(miss) => return missed(miss),
            };
        if lhs == rhs {
            return Ok(Outcome::Miss);
        }
        let motive = match rw.rewrite_motive(cx, rule.expr, None, ty, GOAL, &carrier, &level, &lhs, &rhs, lvl) {
            Ok(motive) => motive,
            // An applied law whose left side the goal does not mention.
            Err(_) if rule_is_applied(&rule.ty) => return Ok(Outcome::Miss),
            Err(e) => return soft(e).map(Outcome::Blocked),
        };
        let next = motive.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&rhs)));
        if next == *ty {
            return Ok(Outcome::Miss);
        }
        let sides = Some(Sides::Terms(Rc::clone(&lhs), Rc::clone(&rhs)));
        Ok(Outcome::Fired(Fired::Equation { level, ty: carrier, lhs, rhs, proof, motive }, next, sides))
    }

    /// An equation at `ty` as a step of the identity relation
    /// (`Relations::identity_step_or`): the walk that crosses a λ. Tried
    /// where the transport found no instance, so a miss here is a miss.
    fn fire_identity<'a>(
        &self,
        relations: &'a Relations<'a>,
        cx: &'a Cx,
        rule: &Rule<'_>,
        ty: &Type,
        premise: super::Premise<'_>,
    ) -> R<Outcome<'a>> {
        let span = rule.expr.span;
        if !relations.below_binders(cx, ty) {
            return Ok(Outcome::Miss);
        }
        let Some(law) = relations.as_identity(cx, &rule.ty, span) else { return Ok(Outcome::Miss) };
        // An equation goal is the identity relation's application; any
        // other goal is walked as it is.
        let equation = matches!(ty, Type::Id { .. });
        let goal = if equation {
            let Some(goal) = relations.as_identity(cx, ty, span) else { return Ok(Outcome::Miss) };
            goal
        } else {
            ty.clone()
        };
        let mut step = match relations.identity_step_or(cx, rule.expr, &rule.proof, &law, &goal, Some(premise)) {
            Ok(Some(step)) => step,
            Ok(None) | Err(Miss::NoInstance) => return Ok(Outcome::Miss),
            Err(Miss::Unbound { index, .. }) => {
                return Ok(Outcome::Blocked(format!(
                    "matching its left side under a binder does not determine its argument {index}; apply the law to it"
                )));
            }
            Err(Miss::Hard(e)) => return soft(e).map(Outcome::Blocked),
        };
        step.refused = Some(Vec::new());
        let (next, plan) = match step.goal(&goal, GOAL) {
            Ok((_, Plan::Same)) => return Ok(Outcome::Miss),
            Ok(found) => found,
            Err(e) => return soft(e).map(Outcome::Blocked),
        };
        if step.occurrences() == 0 || next == goal {
            return Ok(Outcome::Miss);
        }
        let next = if equation {
            let (Type::Id { level, ty: carrier, .. }, Some(rel)) = (ty, Relation::of_type(self.0, cx, &next, span)) else {
                return Ok(Outcome::Miss);
            };
            Type::Id { level: level.clone(), ty: Rc::clone(carrier), lhs: rel.left, rhs: rel.right }
        } else {
            next
        };
        let sides = step.sides().map(|(l, r)| Sides::Terms(l, r)).or_else(|| step.shown.clone().map(|(l, r)| Sides::Statements(l, r)));
        Ok(Outcome::Fired(Fired::Relation { step: Box::new(step), plan }, next, sides))
    }

    /// A proof of the side condition `ty`: a hypothesis in scope whose type
    /// is `ty`, a parameter or a `let`, or `by` checked at it.
    fn discharge(&self, cx: &Cx, ty: &Type, level: &Level, by: Option<&Expr>) -> Option<Term> {
        let n = cx.gamma.len();
        for i in (0..n).rev() {
            let entry = cx.gamma.entries.get(i)?;
            if entry.level != *level {
                continue;
            }
            if self.conv_types(cx, &entry.ty.shift_local((n - i) as u32), ty, level) {
                return Some(Term::Var(LocalVar((n - 1 - i) as u32)));
            }
        }
        for alias in cx.aliases.iter() {
            let Some(by) = n.checked_sub(alias.depth) else { continue };
            if alias.level != *level {
                continue;
            }
            let (_, alias_ty) = alias.at(by as u32);
            if self.conv_types(cx, &alias_ty, ty, level) {
                return Some(alias.splice(by as u32).0);
            }
        }
        let by = by?;
        let mark = self.attempt.mark();
        let attempt = self.elab_check(cx, by, ty, level);
        match attempt {
            Ok(proof) if self.checks(cx, &proof, ty, level) => Some(proof),
            _ => {
                // A discharger that failed for want of a goal slot (an
                // `omega`'s atom list) asks for a restart with more; the
                // rollback forgets the request, so it is made again after
                // it, and the declaration restarts rather than reporting a
                // side condition nothing discharged.
                let wanted = self.attempt.goal_arena.requested_base();
                self.attempt.restore(mark);
                self.attempt.goal_arena.request_base(wanted);
                None
            }
        }
    }

    fn checks(&self, cx: &Cx, t: &Term, ty: &Type, level: &Level) -> bool {
        crate::stats::timed(crate::stats::Timer::KernelGate, || {
            // The goal region's Ψ: a discharger that is a tactic (`bv_omega`)
            // states its lemmas there.
            self.kernel_check_term(&self.goal_psi(), Layer::Prog, &cx.gamma, t, ty, level).is_ok()
        })
    }

    /// The normal form closed by reflexivity: an equation whose sides
    /// convert, or a relation application whose sides convert and whose
    /// relation has `Reflexive` evidence. `None` when the sides differ.
    fn close<'a>(&self, relations: &'a Relations<'a>, cx: &'a Cx, end: &Type, lvl: &Level, span: Span) -> R<Option<Term>> {
        let rw = Rewrites(self.0);
        if let Some(rel) = Relation::of_type(self.0, cx, end, span) {
            if *rel.left != *rel.right && !rw.terms_convert(cx, &rel.left, &rel.right) {
                return Ok(None);
            }
            let holds = match end {
                Type::El { level, .. } => level.clone(),
                Type::M { sig, .. } => sig.family_level(),
                _ => return Ok(None),
            };
            let left = Rc::clone(&rel.left);
            let mut step = RelationRewrite::new(relations, cx, span, rel, Term::Zero, 0, holds)?;
            step.refused = Some(Vec::new());
            return match step.reflexive_at(&left) {
                Ok(proof) => Ok(Some(Rc::unwrap_or_clone(proof))),
                Err(e) => Err(ElabError::Elab {
                    msg: format!(
                        "`simp_only`: the two sides meet, and closing the goal needs the \
                         relation to be reflexive: {}",
                        e.message()
                    ),
                    span,
                }),
            };
        }
        let Type::Id { level, ty, lhs, rhs } = self.whnf(cx, end, span)? else {
            // `P ↔ P`, a conjunction of two equations that each met, and
            // the like: the library's own closers, checked.
            for text in ["iff_refl()", "trivial", "And(refl, refl)"] {
                let source = format!("fn generated() -> Type {{ {text} }}");
                let Ok(mut file) = parse_file(&source) else { continue };
                let Some(Item::Decl(d)) = file.items.pop() else { continue };
                let mark = self.attempt.mark();
                match self.generated_scope(|e| e.elab_check(cx, &d.body.result, end, lvl)) {
                    Ok(proof) if self.checks(cx, &proof, end, lvl) => return Ok(Some(proof)),
                    _ => self.attempt.restore(mark),
                }
            }
            return Ok(None);
        };
        if *lhs != *rhs && !rw.terms_convert(cx, &lhs, &rhs) {
            return Ok(None);
        }
        Ok(Some(Term::Refl { level, ty, tm: lhs }))
    }

    /// The proof the steps of `run` make of their start from `inner`, a
    /// proof of their end (`Backward`), or of their end from `inner`, a
    /// proof of their start (`Forward`).
    fn assemble(&self, run: &mut Run<'_>, polarity: Polarity, inner: Term, lvl: &Level) -> R<Term> {
        let mut term = inner;
        let order: Vec<usize> = match polarity {
            Polarity::Backward => (0..run.steps.len()).rev().collect(),
            Polarity::Forward => (0..run.steps.len()).collect(),
        };
        for i in order {
            term = match &mut run.steps[i].fired {
                // `goal ↔ next`, by the direction asked for.
                Fired::Statement(step) => {
                    let (fun, ty) = match polarity {
                        Polarity::Forward => &step.forward,
                        Polarity::Backward => &step.backward,
                    };
                    let Type::Pi { dom_level, cod_level, dom, cod } = ty else {
                        unreachable!("a direction of `↔` is a function")
                    };
                    crate::spelling::checked_app(
                        Rc::new(fun.clone()),
                        dom_level.clone(),
                        cod_level.clone(),
                        Rc::clone(dom),
                        Rc::clone(cod),
                        Rc::new(term),
                    )
                }
                Fired::Relation { step, plan } => Rc::unwrap_or_clone(step.emit(plan, polarity, Rc::new(term), 0)?),
                Fired::Equation { level, ty, lhs, rhs, proof, motive } => match polarity {
                    // `J(h; y q. M; hyp) : M[b/y]`.
                    Polarity::Forward => Term::J {
                        ty_level: level.clone(),
                        motive_level: lvl.clone(),
                        ty: Rc::clone(ty),
                        lhs: Rc::clone(lhs),
                        motive: Rc::new(motive.shift_local(1)),
                        case: Rc::new(term),
                        rhs: Rc::clone(rhs),
                        proof: Rc::new(proof.clone()),
                    },
                    // `J(sym h; y q. M; e) : M[a/y]`, as `rewrite` builds it.
                    Polarity::Backward => {
                        let symmetric = Term::J {
                            ty_level: level.clone(),
                            motive_level: level.clone(),
                            ty: Rc::clone(ty),
                            lhs: Rc::clone(lhs),
                            motive: Rc::new(Type::Id {
                                level: level.clone(),
                                ty: Rc::new(ty.shift_local(2)),
                                lhs: Rc::new(Term::Var(LocalVar(1))),
                                rhs: Rc::new(lhs.shift_local(2)),
                            }),
                            case: Rc::new(Term::Refl { level: level.clone(), ty: Rc::clone(ty), tm: Rc::clone(lhs) }),
                            rhs: Rc::clone(rhs),
                            proof: Rc::new(proof.clone()),
                        };
                        Term::J {
                            ty_level: level.clone(),
                            motive_level: lvl.clone(),
                            ty: Rc::clone(ty),
                            lhs: Rc::clone(rhs),
                            motive: Rc::new(motive.shift_local(1)),
                            case: Rc::new(term),
                            rhs: Rc::clone(lhs),
                            proof: Rc::new(symmetric),
                        }
                    }
                },
            };
        }
        Ok(term)
    }

    /// The error of a call that did not close: where the two sides ended,
    /// the route there, and what was blocked.
    fn open(&self, cx: &Cx, rules: &[Rule<'_>], run: &Run<'_>, span: Span) -> ElabError {
        let ends = match Relation::of_type(self.0, cx, &run.end, span) {
            Some(rel) => Some((rel.left, rel.right)),
            None => match self.whnf(cx, &run.end, span) {
                Ok(Type::Id { lhs, rhs, .. }) => Some((lhs, rhs)),
                _ => None,
            },
        };
        // A side the source cannot spell is still shown, roughly: `…` marks
        // the nodes no surface syntax recovers, which is where to look.
        let shown = |t: &Term| {
            self.spell_term_clean(cx, t)
                .unwrap_or_else(|| format!("{}
    (no surface spelling: `…` marks what none recovers)", self.display_rough_term(cx, t, &[])))
        };
        let head = match ends {
            Some((l, r)) => format!(
                "`simp_only`: the two sides do not meet\n  left:\n    {}\n  right:\n    {}",
                shown(&l),
                shown(&r)
            ),
            None => format!(
                "`simp_only`: the goal simplifies to\n    {}\n  which reflexivity does not close\n  \
                 hint: `then := e` proves what is left, and `using := h` closes it from a fact \
                 that simplifies to the same statement",
                self.display_type(cx, &run.end)
            ),
        };
        ElabError::Elab { msg: format!("{head}{}", self.report(cx, rules, run, None)), span }
    }

    /// The route of `run` and its blocked laws, as lines of a message.
    fn report(&self, cx: &Cx, rules: &[Rule<'_>], run: &Run<'_>, whose: Option<&str>) -> String {
        let mut out = String::new();
        let label = whose.map_or_else(|| "route".to_string(), |w| format!("{w} route"));
        if run.steps.is_empty() {
            out.push_str(&format!("\n  {label}: no law fired"));
        } else {
            out.push_str(&format!("\n  {label} ({} step{}):", run.steps.len(), if run.steps.len() == 1 { "" } else { "s" }));
            let line = |k: usize, step: &Step<'_>| {
                let sides = step.sides.as_ref().and_then(|sides| match sides {
                    Sides::Terms(l, r) => {
                        Some(format!(": `{}` ⟶ `{}`", self.spell_term_clean(cx, l)?, self.spell_term_clean(cx, r)?))
                    }
                    Sides::Statements(l, r) => Some(format!(": `{l}` ⟶ `{r}`")),
                });
                format!("\n    {}. {}{}", k + 1, rules[step.rule].name, sides.unwrap_or_default())
            };
            let n = run.steps.len();
            for (k, step) in run.steps.iter().enumerate() {
                if n > 2 * SHOWN && k == SHOWN {
                    out.push_str(&format!("\n    … {} more …", n - 2 * SHOWN));
                }
                if n > 2 * SHOWN && (SHOWN..n - SHOWN).contains(&k) {
                    continue;
                }
                out.push_str(&line(k, step));
            }
        }
        if !run.blocked.is_empty() {
            out.push_str("\n  blocked at the normal form:");
            for (i, why) in &run.blocked {
                out.push_str(&format!("\n    {}: {why}", rules[*i].name));
            }
        }
        out
    }
}

/// An error of a step that is the step not applying here, as its reason;
/// an error of the elaboration itself (a declaration restart) is passed on.
fn soft(e: ElabError) -> R<String> {
    let msg = e.message();
    if msg.starts_with("internal:") {
        return Err(e);
    }
    Ok(msg.strip_prefix("`rewrite`: ").unwrap_or(&msg).to_string())
}

/// Is the law's type an equation or relation as given, with no arguments
/// left to instantiate?
fn rule_is_applied(ty: &Type) -> bool {
    !matches!(ty, Type::Pi { .. })
}

/// What a report calls a law: its name when it is one, its head when it is
/// a call, its position otherwise.
fn rule_name(e: &Expr, i: usize) -> String {
    match &e.kind {
        ExprKind::Var(name) => format!("`{name}`"),
        _ => match e.as_named() {
            Some((name, ..)) => format!("`{name}(…)`"),
            None => format!("law {}", i + 1),
        },
    }
}
