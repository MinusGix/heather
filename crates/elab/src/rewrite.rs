//! `rewrite(h₁, …, hₙ, e)`: rewrite the goal along equations, without
//! writing `j`'s motive (`docs/equation-rewrite-design.md`,
//! `issues/equation-rewrite-in-goal.md`).
//!
//! At a checking position with goal `G`, each `hᵢ : aᵢ = bᵢ` in turn
//! replaces every occurrence of `aᵢ` in the goal by `bᵢ`, left to right as
//! written, and `e` is checked at what remains. The motive is the goal with
//! `aᵢ` abstracted (`Type::abstract_local`, the operation the match-motive
//! synthesis uses), and the step is one kernel `J` along `sym(hᵢ)`. Nothing
//! here is trusted: the abstraction only replaces positions that literally
//! held `aᵢ`, so the motive at `aᵢ` is the goal again, syntactically, and the
//! kernel checks the term like any other.
//!
//! Direction is the written one, never guessed: a goal that mentions `bᵢ`
//! and not `aᵢ` is an error whose hint is `sym(hᵢ)`.
//!
//! A step whose proof is a relation application `R(a, b)` rather than an
//! equation is a setoid rewrite (`rewrite/relation.rs`, design §9): the goal
//! is rebuilt bottom-up, one congruence step per changed node, and the proof
//! is chained by transitivity instead of `J`.

use heather_kernel::rc::Rc;

use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{LocalSubst, LocalVar, Term, Type};
use heather_kernel::typing;
use heather_syntax::{Expr, ExprKind, NamedArg, Span};

use crate::matching::MotiveSynthesisElab;
use crate::{Cx, ElabError, Elaborator, R};

mod relation;
pub(crate) use relation::Relations;

use relation::Polarity;
use crate::subst_local::LocalSubsts;
use crate::resolve::Resolution;

/// Rewriting's part of the elaborator.
pub(crate) struct Rewrites<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for Rewrites<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl Rewrites<'_> {
    /// `rewrite(h₁, …, hₙ, e)` at `goal`. `args` is the whole written
    /// argument list; the last one is the proof of the rewritten goal.
    /// `at := k` or `at := [k, …]` selects occurrences, and only with one
    /// equation: with several it could not say whose.
    pub(crate) fn elab_rewrite(
        &self,
        cx: &Cx,
        args: &[Expr],
        named: &[NamedArg],
        goal: &Type,
        lvl: &Level,
        span: Span,
    ) -> R<Term> {
        let Some((body, equations)) = args.split_last().filter(|(_, eqs)| !eqs.is_empty()) else {
            return Err(ElabError::Elab {
                msg: "`rewrite` takes one or more equations and then the proof of the rewritten \
                      goal: `rewrite(h, e)`, or `rewrite(h, refl)` when the rewrite closes it"
                    .into(),
                span,
            });
        };
        let mut at = None;
        for arg in named {
            if arg.name != "at" || at.is_some() {
                return Err(ElabError::Elab {
                    msg: format!(
                        "`rewrite` takes one named argument, `at := k` or `at := [k, …]`, \
                         and not `{} :=`",
                        arg.name
                    ),
                    span: arg.name_span,
                });
            }
            if equations.len() > 1 {
                return Err(ElabError::Elab {
                    msg: "`at :=` selects occurrences of one equation's left side; with several \
                          equations, nest the one it is for: `rewrite(h₁, rewrite(h₂, e, at := k))`"
                        .into(),
                    span: arg.span,
                });
            }
            at = Some(occurrences(&arg.expr)?);
        }
        self.rewrite_from(cx, equations, at.as_deref(), body, goal, lvl)
    }

    /// One equation, then the rest: `rewrite(h, …, e)` is
    /// `rewrite(h, rewrite(…, e))`, so each equation sees the goal its
    /// predecessors left.
    fn rewrite_from(
        &self,
        cx: &Cx,
        equations: &[Expr],
        at: Option<&[u32]>,
        body: &Expr,
        goal: &Type,
        lvl: &Level,
    ) -> R<Term> {
        let Some((h, rest)) = equations.split_first() else {
            return self.elab_check(cx, body, goal, lvl);
        };
        let (proof, proof_ty, _) = self.elab_infer(cx, h)?;
        if let Some(mut step) = Relations(self).relation_step(cx, h, &proof, &proof_ty, goal, GOAL)? {
            if at.is_some() {
                return Err(relation_at_refused(h.span));
            }
            let (next, plan) = step.goal(goal, GOAL)?;
            step.require_occurrence(goal, GOAL)?;
            let case = self.rewrite_from(cx, rest, None, body, &next, lvl)?;
            return Ok(Rc::unwrap_or_clone(step.emit(&plan, Polarity::Backward, Rc::new(case), 0)?));
        }
        let (proof, Equation { level, ty, lhs, rhs }) = self.rewrite_instance(cx, h, proof, &proof_ty, goal, GOAL)?;
        let (lhs, motive) = match self.rewrite_motive(cx, h, at, goal, GOAL, &ty, &level, &lhs, &rhs, lvl) {
            Ok(motive) => (lhs, motive),
            // A left side that is a pattern variable — a projection of the
            // matched value, which the goal mentions whole — is the local it
            // reduces to, or becomes one once the value is taken apart
            // (issues/pattern-variables-not-rewritable.md). Only here, where
            // the rewrite was about to refuse.
            Err(e) => {
                let local = LocalSubsts(self).reduces_to_local(cx, &lhs, h.span).and_then(|p| {
                    let x = Rc::new(Term::Var(LocalVar((cx.names.len() - 1 - p) as u32)));
                    let motive = self.rewrite_motive(cx, h, at, goal, GOAL, &ty, &level, &x, &rhs, lvl).ok()?;
                    Some((x, motive))
                });
                match local {
                    Some(found) => found,
                    None => {
                        let Some(split) = LocalSubsts(self).split_projection(cx, &lhs, goal, h.span) else {
                            return Err(e);
                        };
                        let term = self.rewrite_from(&split.cx, equations, at, body, &split.goal, lvl)?;
                        return Ok(split.close(&term));
                    }
                }
            }
        };
        // The goal after this step: `M[b/y]`.
        let next = motive.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&rhs)));
        let case = self.rewrite_from(cx, rest, None, body, &next, lvl)?;
        // `J(sym h; y q. M; e) : M[a/y]`, which is the goal. `sym h` is
        // `J(h; y q. y = a; refl a) : b = a`, written out so the rewrite needs
        // no library.
        let symmetric = Term::J {
            ty_level: level.clone(),
            motive_level: level.clone(),
            ty: Rc::clone(&ty),
            lhs: Rc::clone(&lhs),
            motive: Rc::new(Type::Id {
                level: level.clone(),
                ty: Rc::new(ty.shift_local(2)),
                lhs: Rc::new(Term::Var(LocalVar(1))),
                rhs: Rc::new(lhs.shift_local(2)),
            }),
            case: Rc::new(Term::Refl { level: level.clone(), ty: Rc::clone(&ty), tm: Rc::clone(&lhs) }),
            rhs: Rc::clone(&rhs),
            proof: Rc::new(proof),
        };
        Ok(Term::J {
            ty_level: level,
            motive_level: lvl.clone(),
            ty,
            lhs: rhs,
            // Weakened past `q`, which the motive does not mention.
            motive: Rc::new(motive.shift_local(1)),
            case: Rc::new(case),
            rhs: lhs,
            proof: Rc::new(symmetric),
        })
    }

    /// `rewrite(h₁, …, hₙ, in := hyp)`: `hyp : P` transported along each
    /// `hᵢ : aᵢ = bᵢ` in turn, every occurrence of `aᵢ` in its type turned
    /// into `bᵢ` — the goal form's direction, applied to a type that is
    /// proved rather than wanted, so the step is `J(hᵢ; y q. M; hyp) : M[b/y]`
    /// with no `sym` (docs/equation-rewrite-design.md §7). An inference form:
    /// the result's type is what the rewrite leaves.
    pub(crate) fn elab_rewrite_in(&self, cx: &Cx, args: &[Expr], named: &[NamedArg], span: Span) -> R<(Term, Type, Level)> {
        if args.is_empty() {
            return Err(ElabError::Elab {
                msg: "`rewrite(…, in := hyp)` takes one or more equations: `rewrite(h, in := hyp)`".into(),
                span,
            });
        }
        let (mut hyp, mut at) = (None, None);
        for arg in named {
            let slot = match arg.name.as_str() {
                "in" => hyp.is_none().then_some(&mut hyp),
                "at" => at.is_none().then_some(&mut at),
                _ => None,
            };
            let Some(slot) = slot else {
                return Err(ElabError::Elab {
                    msg: format!(
                        "`rewrite(…, in := hyp)` takes `in :=` once and at most one `at :=`, \
                         and not this `{} :=`",
                        arg.name
                    ),
                    span: arg.name_span,
                });
            };
            *slot = Some(arg);
        }
        let hyp = hyp.expect("routed here only with `in :=`");
        let at = match at {
            Some(arg) if args.len() > 1 => {
                return Err(ElabError::Elab {
                    msg: "`at :=` selects occurrences of one equation's left side; with several \
                          equations, rewrite one at a time: \
                          `rewrite(h₂, in := rewrite(h₁, in := hyp, at := k))`"
                        .into(),
                    span: arg.span,
                });
            }
            Some(arg) => Some(occurrences(&arg.expr)?),
            None => None,
        };
        let (mut term, mut ty_now, lvl) = self.elab_infer(cx, &hyp.expr)?;
        for h in args {
            let (proof, proof_ty, _) = self.elab_infer(cx, h)?;
            if let Some(mut step) = Relations(self).relation_step(cx, h, &proof, &proof_ty, &ty_now, HYPOTHESIS)? {
                if at.is_some() {
                    return Err(relation_at_refused(h.span));
                }
                let (next, plan) = step.goal(&ty_now, HYPOTHESIS)?;
                step.require_occurrence(&ty_now, HYPOTHESIS)?;
                term = Rc::unwrap_or_clone(step.emit(&plan, Polarity::Forward, Rc::new(term), 0)?);
                ty_now = next;
                continue;
            }
            let (proof, Equation { level, ty, lhs, rhs }) =
                self.rewrite_instance(cx, h, proof, &proof_ty, &ty_now, HYPOTHESIS)?;
            let motive =
                self.rewrite_motive(cx, h, at.as_deref(), &ty_now, HYPOTHESIS, &ty, &level, &lhs, &rhs, &lvl)?;
            ty_now = motive.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&rhs)));
            term = Term::J {
                ty_level: level,
                motive_level: lvl.clone(),
                ty,
                lhs,
                // Weakened past `q`, which the motive does not mention.
                motive: Rc::new(motive.shift_local(1)),
                case: Rc::new(term),
                rhs,
                proof: Rc::new(proof),
            };
        }
        Ok((term, ty_now, lvl))
    }

    /// The goal with `a` abstracted: a type over `Γ, y : S` whose instance at
    /// `a` is `goal`. The goal as written first, then its exposed form (the
    /// head and an equation's sides one weak-head step down, the
    /// match-motive synthesis's §4.3 rung) — and either way the motive must
    /// be a type, which abstracting a term that something else's type depends
    /// on can break.
    #[allow(clippy::too_many_arguments)]
    fn rewrite_motive(
        &self,
        cx: &Cx,
        h: &Expr,
        at: Option<&[u32]>,
        goal: &Type,
        what: &str,
        carrier: &Rc<Type>,
        carrier_level: &Level,
        lhs: &Rc<Term>,
        rhs: &Rc<Term>,
        lvl: &Level,
    ) -> R<Type> {
        let shown = |t: &Term| self.spell_term_clean(cx, t).map_or_else(String::new, |s| format!(" `{s}`"));
        let exposed = || crate::matching::expose(self.0, cx, goal, h.span);
        let spellings = |g: &Type| self.spellings(cx, g, lhs, carrier, carrier_level);
        let motive = match at {
            None => goal.abstract_local_any(&spellings(goal)).or_else(|| {
                let g = exposed()?;
                g.abstract_local_any(&spellings(&g))
            }),
            // Numbered against the goal as written, and only that: a number
            // that meant one thing as written and another after reduction
            // would be worse than a refusal.
            Some(at) => {
                let (motive, seen) = goal.abstract_local_at(&spellings(goal), at);
                if let Some(&past) = at.iter().find(|&&k| k > seen) {
                    return Err(ElabError::Elab {
                        msg: format!(
                            "`rewrite`: `at := {past}`, but {what} `{}` has {seen} occurrence(s) \
                             of the equation's left side{}",
                            self.display_type(cx, goal),
                            shown(lhs)
                        ),
                        span: h.span,
                    });
                }
                motive
            }
        };
        let Some(motive) = motive else {
            let reversed = goal.abstract_local(rhs).is_some()
                || exposed().is_some_and(|g| g.abstract_local(rhs).is_some());
            let hint = if reversed {
                format!(
                    "\n  hint: {what} mentions its right side{}; to rewrite right to left, \
                     write `sym(…)` around the equation",
                    shown(rhs)
                )
            } else {
                String::new()
            };
            return Err(ElabError::Elab {
                msg: format!(
                    "`rewrite`: {what} `{}` does not mention the equation's left side{}\n  \
                     note: an occurrence is a subterm with the left side's head that converts \
                     to it, as written or one unfolding of it{hint}",
                    self.display_type(cx, goal),
                    shown(lhs)
                ),
                span: h.span,
            });
        };
        let mut mcx = cx.clone();
        mcx.push("_".to_string(), (**carrier).clone(), carrier_level.clone());
        let psi = self.goal_psi();
        typing::check_type(&psi, 0, Layer::Prog, &mcx.gamma, &motive, lvl, self.policy.fuel).map_err(|_| {
            ElabError::Elab {
                msg: format!(
                    "`rewrite`: abstracting the left side{} from {what} does not leave a type: \
                     something else in it depends on it being exactly that term\n  \
                     hint: write the motive by hand with `j`",
                    shown(lhs)
                ),
                span: h.span,
            }
        })?;
        Ok(motive)
    }
    /// The equation `h` proves, instantiated. A proof whose type is a Π
    /// telescope ending in an equation — a lemma left unapplied, or applied
    /// to fewer arguments than it takes — has its remaining arguments found
    /// by matching the left side against the goal: the first subterm, in the
    /// order [`Type::root_terms`] meets them, that has the left side's head
    /// and matches it fixes them, and the proof is applied to them.
    fn rewrite_instance(
        &self,
        cx: &Cx,
        h: &Expr,
        proof: Term,
        proof_ty: &Type,
        goal: &Type,
        what: &str,
    ) -> R<(Term, Equation)> {
        let not_an_equation = |ty: &Type| ElabError::Elab {
            msg: format!(
                "`rewrite` rewrites along an equation `a = b` or a relation `R(a, b)`, and \
                 this proof is of `{}`",
                self.display_type(cx, ty)
            ),
            span: h.span,
        };
        // Open the telescope: `pcx` is Γ, x₁ … xₖ, and the equation is
        // scoped there.
        let mut pcx = cx.clone();
        let mut k = 0u32;
        let mut telescope = Vec::new();
        let mut cur = self.whnf(cx, proof_ty, h.span)?;
        let (level, ty, lhs, rhs) = loop {
            match cur {
                Type::Id { level, ty, lhs, rhs } => break (level, ty, lhs, rhs),
                Type::Pi { dom_level, dom, cod, .. } if k < MAX_OPEN => {
                    telescope.push(((*dom).clone(), dom_level.clone()));
                    pcx.push(format!("_{k}"), (*dom).clone(), dom_level);
                    k += 1;
                    cur = self.whnf(&pcx, &cod, h.span)?;
                }
                _ => return Err(not_an_equation(proof_ty)),
            }
        };
        if k == 0 {
            return Ok((proof, Equation { level, ty, lhs, rhs }));
        }
        if matches!(&*lhs, Term::Var(x) if x.0 < k) {
            return Err(ElabError::Elab {
                msg: "`rewrite`: this equation's left side is one of its own arguments, so it \
                      would match every subterm; apply it to that argument"
                    .into(),
                span: h.span,
            });
        }
        let found = goal_terms(goal, |t| same_key(&lhs, t, k), || crate::matching::expose(self.0, cx, goal, h.span))
            .into_iter()
            .take(CANDIDATES)
            .find_map(|t| {
                let mut binds = vec![None; k as usize];
                self.match_pattern(cx, &lhs, &t, k, &mut binds, &telescope, h.span).then_some(binds)
            });
        let Some(binds) = found else {
            return Err(ElabError::Elab {
                msg: format!(
                    "`rewrite`: no subterm of {what} `{}` is an instance of this equation's \
                     left side\n  note: an instance has the left side's head, and its other \
                     parts convert",
                    self.display_type(cx, goal)
                ),
                span: h.span,
            });
        };
        // Binder `j` (outermost first) is `Var(k - 1 - j)` in `pcx`.
        let mut args = Vec::with_capacity(k as usize);
        for j in 0..k {
            let Some(arg) = binds[(k - 1 - j) as usize].clone() else {
                return Err(ElabError::Elab {
                    msg: format!(
                        "`rewrite`: matching the left side does not determine this equation's \
                         argument {}, which only its right side mentions; give it explicitly",
                        j + 1
                    ),
                    span: h.span,
                });
            };
            args.push(arg);
        }
        let mut term = proof;
        let mut ty_now = proof_ty.clone();
        for arg in args {
            let Type::Pi { dom_level, cod_level, dom, cod } = self.whnf(cx, &ty_now, h.span)? else {
                return Err(not_an_equation(proof_ty));
            };
            ty_now = cod.inst_top(0, &arg);
            term = crate::spelling::checked_app(Rc::new(term), dom_level, cod_level, dom, cod, arg);
        }
        let Type::Id { level, ty, lhs, rhs } = self.whnf(cx, &ty_now, h.span)? else {
            return Err(not_an_equation(proof_ty));
        };
        Ok((term, Equation { level, ty, lhs, rhs }))
    }

    /// First-order matching of `pat` (scoped in Γ, x₁ … xₖ, the `x`s its
    /// variables) against `t` (scoped in Γ), along application spines. A part
    /// of `pat` that is not an application is compared once every variable
    /// it mentions is bound — instantiated, then equal to or convertible with
    /// its counterpart — so a type argument bound by one argument decides a
    /// constructor value's annotation in another. Annotations of the spines
    /// themselves are not read: the instance is built from the bindings, and
    /// the caller's abstraction re-checks it by conversion, which decides.
    ///
    /// `telescope` is the `x`s' types, outermost first, each scoped in Γ and
    /// the `x`s before it. A class dictionary among them that matching left
    /// unbound is resolved at its instantiated type
    /// ([`Self::bind_dictionaries`]).
    #[allow(clippy::too_many_arguments)]
    fn match_pattern(
        &self,
        cx: &Cx,
        pat: &Term,
        t: &Rc<Term>,
        k: u32,
        binds: &mut [Option<Rc<Term>>],
        telescope: &[(Type, Level)],
        span: Span,
    ) -> bool {
        let mut deferred = Vec::new();
        if !self.match_spine(cx, pat, t, k, binds, &mut deferred) {
            return false;
        }
        if !self.bind_dictionaries(cx, k, binds, telescope, span) {
            return false;
        }
        deferred.into_iter().all(|(p, t)| match instantiate(&cx.gamma, &p, k, binds) {
            Some(p) => p == *t || self.terms_convert(cx, &p, &t),
            None => false,
        })
    }

    /// Binds each class dictionary in `telescope` that matching left unbound
    /// by resolution, at its type instantiated by the arguments before it. A
    /// law stated in a class's section takes the section's dictionary, which
    /// its left side mentions only inside what it builds from it (`range`'s
    /// monoid, say), never as a part matching can bind. `false` when one does
    /// not resolve: the candidate is not an instance — its operation is not
    /// the class's.
    fn bind_dictionaries(
        &self,
        cx: &Cx,
        k: u32,
        binds: &mut [Option<Rc<Term>>],
        telescope: &[(Type, Level)],
        span: Span,
    ) -> bool {
        for (j, (dom, level)) in telescope.iter().enumerate() {
            let slot = k as usize - 1 - j;
            if binds[slot].is_some() {
                continue;
            }
            // Binder `i < j` is `Var(j - 1 - i)` in `dom`; extended outermost
            // first.
            let mut sigma = LocalSubst::id(&cx.gamma);
            let mut bound = true;
            for i in 0..j {
                match &binds[k as usize - 1 - i] {
                    Some(arg) => sigma = sigma.extended(Rc::clone(arg)),
                    None => {
                        bound = false;
                        break;
                    }
                }
            }
            if !bound {
                continue;
            }
            let ty = dom.apply_local(&sigma);
            let is_class = self.display_tag_of(&ty).is_some_and(|ind| {
                ind.is_record && self.traits.has_class(&crate::names::qkey(&ind.scope.module, &ind.name))
            });
            if !is_class {
                continue;
            }
            let shown = self.display_type(cx, &ty);
            match self.resolve_goal(cx, &ty, level, &shown, None, span, &mut Vec::new()) {
                Some(dict) => binds[slot] = Some(Rc::new(dict)),
                None => return false,
            }
        }
        true
    }

    fn match_spine(
        &self,
        cx: &Cx,
        pat: &Term,
        t: &Rc<Term>,
        k: u32,
        binds: &mut [Option<Rc<Term>>],
        deferred: &mut Vec<(Term, Rc<Term>)>,
    ) -> bool {
        if let Term::Var(x) = pat
            && x.0 < k
        {
            let slot = &mut binds[x.0 as usize];
            return match slot {
                Some(bound) => **bound == **t || self.terms_convert(cx, &bound.clone(), t),
                None => {
                    *slot = Some(Rc::clone(t));
                    true
                }
            };
        }
        if let Some(closed) = crate::strengthen_tm(&cx.gamma, pat, k) {
            return closed == **t || self.terms_convert(cx, &closed, t);
        }
        // A codata constructor is a `corec` whose signature holds the type's
        // parameters and whose step holds the fields: matched structurally,
        // binders and all (docs/equation-rewrite-design.md §11.2).
        if let Term::Corec { .. } = pat {
            return matches!(**t, Term::Corec { .. }) && self.match_deep(cx, pat, t, k, 0, binds);
        }
        // `λ z. g(z)` with `z` not in `g` is `g` (η): a law's `λ k. f(k)`
        // binds `f`, to what the goal's λ contracts to, or to the λ itself.
        if let Some(g) = eta(pat) {
            let t = eta(t).map_or_else(|| Rc::clone(t), Rc::new);
            return self.match_spine(cx, &g, &t, k, binds, deferred);
        }
        // A class carrier's parent dictionary, minted over the law's own
        // parameters (docs/traits-layer2-design.md §8.1), is what a written
        // record was before: compared by conversion once the dictionaries
        // are bound, not spine by spine against the goal's instance.
        if Resolution(self).is_open_app(pat) {
            deferred.push((pat.clone(), Rc::clone(t)));
            return true;
        }
        match (crate::spelling::app_of(pat), crate::spelling::app_of(t)) {
            (Some((pf, pa)), Some((tf, ta))) => {
                let (tf, ta) = (Rc::clone(tf), Rc::clone(ta));
                self.match_spine(cx, pf, &tf, k, binds, deferred) && self.match_spine(cx, pa, &ta, k, binds, deferred)
            }
            (Some(_), None) => false,
            _ => {
                deferred.push((pat.clone(), Rc::clone(t)));
                true
            }
        }
    }

    /// `pat` against `t`, both `d` binders below the match's context, node
    /// by node: a pattern variable (`Var(d)` … `Var(d + k - 1)`) binds the
    /// subterm it meets, which must not mention those `d` binders, and
    /// everything else must agree in shape. A part with no pattern variable
    /// is compared as written, or by conversion at depth 0. The forms a
    /// codata constructor is built from are walked; any other form with a
    /// pattern variable inside is no match.
    fn match_deep(&self, cx: &Cx, pat: &Term, t: &Term, k: u32, d: u32, binds: &mut [Option<Rc<Term>>]) -> bool {
        if let Term::Var(x) = pat {
            let x = x.0;
            if x >= d && x < d + k {
                let Some(lowered) = lower(t, 0, d) else { return false };
                let slot = &mut binds[(x - d) as usize];
                return match slot {
                    Some(bound) => **bound == lowered || self.terms_convert(cx, &bound.clone(), &lowered),
                    None => {
                        *slot = Some(Rc::new(lowered));
                        true
                    }
                };
            }
        }
        if let Some(closed) = lower(pat, d, k) {
            return closed == *t || (d == 0 && self.terms_convert(cx, &closed, t));
        }
        let deep = |p: &Term, s: &Term, by: u32, binds: &mut [Option<Rc<Term>>]| self.match_deep(cx, p, s, k, d + by, binds);
        let deep_ty = |p: &Type, s: &Type, by: u32, binds: &mut [Option<Rc<Term>>]| self.match_deep_ty(cx, p, s, k, d + by, binds);
        if let (Some((pf, pa)), Some((tf, ta))) = (crate::spelling::app_of(pat), crate::spelling::app_of(t)) {
            return deep(pf, tf, 0, binds) && deep(pa, ta, 0, binds);
        }
        match (pat, t) {
            // A binder's type is matched when it can be: the same type has
            // more than one spelling (a code decoded or not), and a λ's
            // domain is fixed by what it is applied in, which the caller's
            // statement checks.
            (Term::Lam { dom: pd, body: pb, .. }, Term::Lam { dom: td, body: tb, .. }) => {
                let mut tried = binds.to_vec();
                if deep_ty(pd, td, 0, &mut tried) {
                    binds.clone_from_slice(&tried);
                }
                deep(pb, tb, 1, binds)
            }
            (Term::Pair { fst_ty: pa, snd_ty: pb, fst: pf, snd: ps, .. }, Term::Pair { fst_ty: ta, snd_ty: tb, fst: tf, snd: ts, .. }) => {
                deep_ty(pa, ta, 0, binds) && deep_ty(pb, tb, 1, binds) && deep(pf, tf, 0, binds) && deep(ps, ts, 0, binds)
            }
            (Term::PairAt { fst: pf, snd: ps, ty: None }, Term::PairAt { fst: tf, snd: ts, ty: None }) => {
                deep(pf, tf, 0, binds) && deep(ps, ts, 0, binds)
            }
            (Term::InlAt { val: p, ty: None }, Term::InlAt { val: v, ty: None })
            | (Term::InrAt { val: p, ty: None }, Term::InrAt { val: v, ty: None }) => deep(p, v, 0, binds),
            (Term::Inl { lhs: pl, rhs: pr, val: p, .. }, Term::Inl { lhs: tl, rhs: tr, val: v, .. })
            | (Term::Inr { lhs: pl, rhs: pr, val: p, .. }, Term::Inr { lhs: tl, rhs: tr, val: v, .. }) => {
                deep_ty(pl, tl, 0, binds) && deep_ty(pr, tr, 0, binds) && deep(p, v, 0, binds)
            }
            (Term::SRefl { ty: pt, tm: p, .. }, Term::SRefl { ty: tt, tm: v, .. }) => deep_ty(pt, tt, 0, binds) && deep(p, v, 0, binds),
            (
                Term::Corec { sig: ps, carrier: pc, step: pst, index: pi, seed: pse, .. },
                Term::Corec { sig: ts, carrier: tc, step: tst, index: ti, seed: tse, .. },
            ) => {
                self.match_sig(cx, ps, ts, k, d, binds)
                    && deep_ty(pc, tc, 1, binds)
                    && deep(pst, tst, 2, binds)
                    && deep(pi, ti, 0, binds)
                    && deep(pse, tse, 0, binds)
            }
            // Any other form is compared once the variables it mentions are
            // bound (an `elim_Empty`'s motive, in a constructor with no
            // children, mentions only the type's parameters).
            _ => instantiate_at(pat, d, k, binds).is_some_and(|p| p == *t),
        }
    }

    fn match_sig(
        &self,
        cx: &Cx,
        p: &heather_kernel::term::MSig,
        t: &heather_kernel::term::MSig,
        k: u32,
        d: u32,
        binds: &mut [Option<Rc<Term>>],
    ) -> bool {
        // `M(I; i. S; i s. P; i s p. o)`.
        self.match_deep_ty(cx, &p.idx, &t.idx, k, d, binds)
            && self.match_deep_ty(cx, &p.shape, &t.shape, k, d + 1, binds)
            && self.match_deep_ty(cx, &p.pos, &t.pos, k, d + 2, binds)
            && self.match_deep(cx, &p.next, &t.next, k, d + 3, binds)
    }

    /// [`Self::match_deep`] over types.
    fn match_deep_ty(&self, cx: &Cx, pat: &Type, t: &Type, k: u32, d: u32, binds: &mut [Option<Rc<Term>>]) -> bool {
        if let Some(closed) = lower_ty(pat, d, k) {
            return closed == *t;
        }
        match (pat, t) {
            (Type::El { tm: p, .. }, Type::El { tm: s, .. }) => self.match_deep(cx, p, s, k, d, binds),
            (Type::Pi { dom: pd, cod: pc, .. }, Type::Pi { dom: td, cod: tc, .. })
            | (Type::Sigma { fst: pd, snd: pc, .. }, Type::Sigma { fst: td, snd: tc, .. }) => {
                self.match_deep_ty(cx, pd, td, k, d, binds) && self.match_deep_ty(cx, pc, tc, k, d + 1, binds)
            }
            (Type::Sum { lhs: pl, rhs: pr, .. }, Type::Sum { lhs: tl, rhs: tr, .. }) => {
                self.match_deep_ty(cx, pl, tl, k, d, binds) && self.match_deep_ty(cx, pr, tr, k, d, binds)
            }
            (Type::M { sig: ps, index: pi }, Type::M { sig: ts, index: ti }) => {
                self.match_sig(cx, ps, ts, k, d, binds) && self.match_deep(cx, pi, ti, k, d, binds)
            }
            _ => false,
        }
    }

    /// The spellings of `lhs` the goal uses: `lhs` itself, and every term
    /// under no binder with `lhs`'s head (a global's or a local variable's
    /// application, [`keyable_head`]) that converts to it, capped. Abstracting them all in one pass is the
    /// match-motive synthesis's §4.4 move: half a rewrite is worse than none.
    fn spellings(&self, cx: &Cx, goal: &Type, lhs: &Term, carrier: &Type, level: &Level) -> Vec<Term> {
        let mut out = vec![lhs.clone()];
        let (head, _) = crate::spelling::app_spine(lhs);
        if !keyable_head(head) {
            return out;
        }
        for t in goal.root_terms().into_iter().filter(|t| same_key(lhs, t, 0)).take(CANDIDATES) {
            if !out.iter().any(|o| *o == *t)
                && self.motive_candidate_converts(cx, &t, lhs, carrier, level)
            {
                out.push((*t).clone());
            }
        }
        out
    }

    /// Do two terms scoped in `cx` convert, at the first one's type?
    fn terms_convert(&self, cx: &Cx, a: &Term, b: &Term) -> bool {
        let oracle = self.goal_oracle();
        let Ok((ty, level)) = typing::infer_term(oracle.world(), 0, Layer::Prog, &cx.gamma, a, self.policy.fuel) else {
            return false;
        };
        self.motive_candidate_converts(cx, b, a, &ty, &level)
    }
}

/// `t` with its variables `at` … `at + n - 1` dropped, the ones above
/// lowered; `None` when it mentions one of them.
fn lower(t: &Term, at: u32, n: u32) -> Option<Term> {
    let mut cur = t.clone();
    for _ in 0..n {
        let dropped = cur.inst_top_above(0, at, &Term::Zero);
        if dropped.shift_local_above(1, at) != cur {
            return None;
        }
        cur = dropped;
    }
    Some(cur)
}

/// `t`, `d` binders below the match's context, with its pattern variables
/// (`Var(d)` … `Var(d + k - 1)`) replaced by `binds`; `None` when one it
/// mentions is unbound.
fn instantiate_at(t: &Term, d: u32, k: u32, binds: &[Option<Rc<Term>>]) -> Option<Term> {
    let mut cur = t.clone();
    // Each step substitutes `Var(d)` and lowers what is above it, so a
    // payload is raised first by the steps still to come after it.
    for (j, slot) in binds.iter().take(k as usize).enumerate() {
        let next = match slot {
            Some(b) => cur.inst_top_above(0, d, &b.shift_local(k - 1 - j as u32)),
            None => {
                let dropped = cur.inst_top_above(0, d, &Term::Zero);
                if dropped.shift_local_above(1, d) != cur {
                    return None;
                }
                dropped
            }
        };
        cur = next;
    }
    Some(cur)
}

/// [`lower`] over a type.
fn lower_ty(t: &Type, at: u32, n: u32) -> Option<Type> {
    let mut cur = t.clone();
    for _ in 0..n {
        let dropped = cur.inst_top_above(0, at, &Term::Zero);
        if dropped.shift_local_above(1, at) != cur {
            return None;
        }
        cur = dropped;
    }
    Some(cur)
}

/// `at :=` with a relation: occurrence numbers are tree positions, and the
/// relation walk visits each shared node once.
fn relation_at_refused(span: Span) -> ElabError {
    ElabError::Elab {
        msg: "`at :=` selects occurrences of an equation's left side; a relation rewrite \
              rewrites every occurrence (issues/relational-rewrite-controls.md)\n  \
              hint: rewrite with an instance of the lemma that only those occurrences match"
            .into(),
        span,
    }
}

/// The equation a rewrite step uses, instantiated, scoped in Γ.
struct Equation {
    level: Level,
    ty: Rc<Type>,
    lhs: Rc<Term>,
    rhs: Rc<Term>,
}

/// What a rewrite step's errors call the type it rewrites.
const GOAL: &str = "the goal";
const HYPOTHESIS: &str = "the hypothesis's type";

/// Arguments an unapplied equation may leave open.
const MAX_OPEN: u32 = 32;

/// Candidate subterms tried per equation, in either search: each costs a
/// match or a conversion call.
const CANDIDATES: usize = 256;

/// The goal's terms under no binder that `keep` accepts, and — only when the
/// goal as written has none — its exposed form's.
fn goal_terms(goal: &Type, keep: impl Fn(&Term) -> bool, exposed: impl FnOnce() -> Option<Type>) -> Vec<Rc<Term>> {
    let terms: Vec<_> = goal.root_terms().into_iter().filter(|t| keep(t)).collect();
    if !terms.is_empty() {
        return terms;
    }
    exposed().map_or_else(Vec::new, |g| g.root_terms().into_iter().filter(|t| keep(t)).collect())
}

/// `pat`, scoped in Γ, x₁ … xₖ, with every `x` replaced by its binding
/// (`binds[i]` is `Var(i)`'s); `None` while one it mentions is unbound —
/// told by instantiating the unbound ones at two different placeholders,
/// [`crate::mentions_binder`]'s marker trick.
fn instantiate(gamma: &heather_kernel::term::LocalCtx, pat: &Term, k: u32, binds: &[Option<Rc<Term>>]) -> Option<Term> {
    let at = |placeholder: &Term| {
        let mut sigma = LocalSubst::id(gamma);
        for i in (0..k).rev() {
            sigma = sigma.extended(binds[i as usize].clone().unwrap_or_else(|| Rc::new(placeholder.clone())));
        }
        pat.apply_local(&sigma)
    };
    let one = at(&Term::Zero);
    (binds.iter().all(Option::is_some) || one == at(&Term::Succ(Rc::new(Term::Zero)))).then_some(one)
}

/// `λ z. g(z)` contracted to `g`, when `z` does not occur in `g`.
fn eta(t: &Term) -> Option<Term> {
    let Term::Lam { body, .. } = t else { return None };
    let (g, arg) = crate::spelling::app_of(body)?;
    if !matches!(&**arg, Term::Var(x) if x.0 == 0) {
        return None;
    }
    let lowered = g.inst_top(0, &Term::Zero);
    (lowered.shift_local(1) == **g).then_some(lowered)
}

/// A left side whose occurrences are found by conversion, not `==` alone
/// (docs/equation-rewrite-design.md §6.2): one headed by a global, or by a
/// local variable. A variable converts to nothing but itself, but the
/// arguments it is applied to may be spelled differently in the goal: a
/// class law's operation is the caller's operator variable, and the
/// dictionary its left side builds from the class's (a sum's monoid) is
/// resolved at the law's section prefix, while the goal resolved it at its
/// own, minted per prefix as an `#open` global (traits-layer2-design.md
/// §8.1) or spelled by another compiler build in a replayed image.
fn keyable_head(head: &Term) -> bool {
    matches!(head, Term::GlobalTm { .. } | Term::Var(_))
}

/// The key a candidate must share with a pattern: the same application
/// head and the same number of arguments. `k` is how many binders the
/// pattern is scoped under beyond the candidate. A pattern headed by one of
/// its own variables — a class's operation, which a law stated in the
/// class's section takes as an argument — is keyed instead by its first
/// argument that is no variable of its own, which must share its key; a
/// pattern with no such argument has none, as it would match every
/// application.
fn same_key(pat: &Term, t: &Term, k: u32) -> bool {
    let (ph, pargs) = crate::spelling::app_spine(pat);
    let (th, targs) = crate::spelling::app_spine(t);
    if pargs.len() != targs.len() {
        return false;
    }
    let variable = |p: &Term| matches!(p, Term::Var(x) if x.0 < k);
    if variable(ph) {
        return pargs
            .iter()
            .zip(&targs)
            .find(|(p, _)| !variable(p))
            .is_some_and(|(p, t)| same_key(p, t, k));
    }
    match (ph, th) {
        (Term::GlobalTm { var: a, .. }, Term::GlobalTm { var: b, .. }) => a == b,
        // Codata constructors: whether they are the same one is the match's
        // to say (`match_deep`).
        (Term::Corec { .. }, Term::Corec { .. }) => true,
        (Term::Var(a), Term::Var(b)) => a.0 >= k && a.0 - k == b.0,
        _ => *ph == th.shift_local(k),
    }
}

/// `at := k` or `at := [k, …]`: positive numerals, as written.
fn occurrences(e: &Expr) -> R<Vec<u32>> {
    let one = |e: &Expr| match &e.kind {
        ExprKind::Num(n) => n.as_u64().and_then(|n| u32::try_from(n).ok()).filter(|&n| n > 0),
        _ => None,
    };
    let list = match &e.kind {
        ExprKind::CollectionLit(items) if !items.is_empty() => items.iter().map(one).collect(),
        _ => one(e).map(|k| vec![k]),
    };
    list.ok_or_else(|| ElabError::Elab {
        msg: "`at :=` takes occurrence numbers, counted from 1: `at := 2` or `at := [1, 3]`".into(),
        span: e.span,
    })
}
