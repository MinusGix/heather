//! `simp_only(r₁, …, rₙ)`: the goal normalised by a list of laws
//! (`docs/simp-design.md`, `issues/simp-tactic.md`).
//!
//! Each law is an equation `a = b` or a relation step `R(a, b)`, applied or
//! not, used left to right. The driver takes the first law that has an
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

use super::relation::{Plan, Polarity, RelationRewrite, Relations};
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
}

/// One step taken: what `rewrite` needs to build its proof.
enum Fired<'a> {
    Relation { step: Box<RelationRewrite<'a>>, plan: Plan },
    Equation { level: Level, ty: Rc<Type>, lhs: Rc<Term>, rhs: Rc<Term>, proof: Term, motive: Type },
}

struct Step<'a> {
    rule: usize,
    fired: Fired<'a>,
    /// The instance's two sides, where they are scoped in the goal's
    /// context: what the route prints.
    sides: Option<(Rc<Term>, Rc<Term>)>,
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
    Fired(Fired<'a>, Type, Option<(Rc<Term>, Rc<Term>)>),
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
        let mut rules = Vec::with_capacity(args.len());
        for (i, h) in args.iter().enumerate() {
            let (proof, ty, _) = self.elab_infer(cx, h)?;
            rules.push(self.law(cx, form, h, rule_name(h, i), proof, ty)?);
        }
        self.run_simp(cx, form, show, &rules, discharge, then, using, goal, lvl, span)
    }

    /// The host's entry (`Req::Simp`, docs/simp-design.md §7): the goal
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

    /// A law of the list: what it concludes is read where it fires; a proof
    /// of something that is no statement at all is refused here, used or
    /// not.
    fn law<'x>(&self, cx: &Cx, form: &str, h: &'x Expr, name: String, proof: Term, ty: Type) -> R<Rule<'x>> {
        let mut conclusion = &ty;
        while let Type::Pi { cod, .. } = conclusion {
            conclusion = cod;
        }
        if !matches!(conclusion, Type::Id { .. } | Type::El { .. } | Type::M { .. }) {
            let shown = self.display_type(cx, &ty);
            return Err(ElabError::Elab {
                msg: format!(
                    "`{form}`: {name} is not a law: a law is a proof of an equation `a = b` or \
                     of a relation `R(a, b)`, under any hypotheses, and this is of type \
                     `{shown}`{}",
                    if shown.starts_with("Iff<") {
                        "\n  note: a law `P ↔ Q` between statements is not rewritten yet \
                         (issues/simp-iff-laws.md); use its direction, `h.mp(…)`, in `then :=`"
                    } else {
                        ""
                    }
                ),
                span: h.span,
            });
        }
        Ok(Rule { expr: h, proof, ty, name })
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
        let premise = |at: &Cx, ty: &Type, level: &Level| self.discharge(at, ty, level, discharge);
        let mut run = Run { steps: Vec::new(), end: start.clone(), blocked: Vec::new(), exhausted: false, cycle: None };
        let mut seen = vec![start.clone()];
        'steps: loop {
            if run.steps.len() >= BUDGET {
                run.exhausted = true;
                return Ok(run);
            }
            // Calls at constructors compute first (`simp(Seq(a, b))` is
            // `seq(simp(a), simp(b))`), as a split's goal does: a law's left
            // side is matched against what is written, and the definition's
            // own equations are not laws anyone should have to list.
            let computed = crate::goal_combinators::simplify_goal_with(self.0, cx, &run.end, true);
            if computed != run.end && self.conv_types(cx, &computed, &run.end, lvl) {
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
            run.blocked = blocked;
            return Ok(run);
        }
    }

    /// Is `ty` an equation or a relation between one term and itself, as
    /// written?
    fn met(&self, cx: &Cx, ty: &Type, span: Span) -> bool {
        match ty {
            Type::Id { lhs, rhs, .. } => lhs == rhs,
            _ => Relation::of_type(self.0, cx, ty, span).is_some_and(|rel| rel.left == rel.right),
        }
    }

    /// One law at `ty`: every occurrence of its first instance rewritten.
    fn fire<'a>(
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
                        "`simp_only`: {} is not a law: a law is a proof of an equation `a = b` \
                         or of a relation `R(a, b)`, under any hypotheses, and this is a proof \
                         of {rest}\n  note: a law `P ↔ Q` between statements is not rewritten \
                         yet (issues/simp-iff-laws.md); use its direction, `h.mp(…)`, in \
                         `then :=`",
                        rule.name
                    ),
                    span: rule.expr.span,
                })
            }
        };
        match relations.relation_step_or(cx, rule.expr, &rule.proof, &rule.ty, ty, Some(premise)) {
            Ok(Some(mut step)) => {
                step.refused = Some(Vec::new());
                return match step.goal(ty, GOAL) {
                    Ok((_, Plan::Same)) => Ok(Outcome::Miss),
                    Ok((next, plan)) => {
                        if step.occurrences() == 0 || next == *ty {
                            return Ok(Outcome::Miss);
                        }
                        let sides = step.sides();
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
        let sides = Some((Rc::clone(&lhs), Rc::clone(&rhs)));
        Ok(Outcome::Fired(Fired::Equation { level, ty: carrier, lhs, rhs, proof, motive }, next, sides))
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
        match self.elab_check(cx, by, ty, level) {
            Ok(proof) if self.checks(cx, &proof, ty, level) => Some(proof),
            _ => {
                self.attempt.restore(mark);
                None
            }
        }
    }

    fn checks(&self, cx: &Cx, t: &Term, ty: &Type, level: &Level) -> bool {
        crate::stats::timed(crate::stats::Timer::KernelGate, || {
            self.kernel_check_term(self.semantic_oracle().world(), Layer::Prog, &cx.gamma, t, ty, level).is_ok()
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
            // `P ↔ P` and the like: the library's own closers, checked.
            for text in ["iff_refl()", "trivial"] {
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
        let shown = |t: &Term| self.spell_term_clean(cx, t).unwrap_or_else(|| "(a term with no surface spelling)".into());
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
                let sides = step.sides.as_ref().and_then(|(l, r)| {
                    Some(format!(": `{}` ⟶ `{}`", self.spell_term_clean(cx, l)?, self.spell_term_clean(cx, r)?))
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
