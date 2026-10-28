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

use std::sync::Arc as Rc;

use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{LocalSubst, LocalVar, Term, Type};
use heather_kernel::typing;
use heather_syntax::{Expr, ExprKind, NamedArg, Span};

use crate::matching::MotiveSynthesisElab;
use crate::{Cx, ElabError, Elaborator, R};

mod relation;

use relation::Polarity;

impl Elaborator {
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
        if let Some(mut step) = self.relation_step(cx, h, &proof, &proof_ty, goal, GOAL)? {
            if at.is_some() {
                return Err(relation_at_refused(h.span));
            }
            let (next, plan) = step.goal(goal, GOAL)?;
            step.require_occurrence(goal, GOAL)?;
            let case = self.rewrite_from(cx, rest, None, body, &next, lvl)?;
            return Ok(Rc::unwrap_or_clone(step.emit(&plan, Polarity::Backward, Rc::new(case), 0)?));
        }
        let (proof, Equation { level, ty, lhs, rhs }) = self.rewrite_instance(cx, h, proof, &proof_ty, goal, GOAL)?;
        let motive = self.rewrite_motive(cx, h, at, goal, GOAL, &ty, &level, &lhs, &rhs, lvl)?;
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
            if let Some(mut step) = self.relation_step(cx, h, &proof, &proof_ty, &ty_now, HYPOTHESIS)? {
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
        let exposed = || crate::matching::expose(self, cx, goal, h.span);
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
        typing::check_type(&psi, 0, Layer::Prog, &mcx.gamma, &motive, lvl, self.fuel).map_err(|_| {
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
        let found = goal_terms(goal, |t| same_key(&lhs, t, k), || crate::matching::expose(self, cx, goal, h.span))
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
        // `λ z. g(z)` with `z` not in `g` is `g` (η): a law's `λ k. f(k)`
        // binds `f`, to what the goal's λ contracts to, or to the λ itself.
        if let Some(g) = eta(pat) {
            let t = eta(t).map_or_else(|| Rc::clone(t), Rc::new);
            return self.match_spine(cx, &g, &t, k, binds, deferred);
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

    /// The spellings of `lhs` the goal uses: `lhs` itself, and every term
    /// under no binder with `lhs`'s head (a global's application) that
    /// converts to it, capped. Abstracting them all in one pass is the
    /// match-motive synthesis's §4.4 move: half a rewrite is worse than none.
    fn spellings(&self, cx: &Cx, goal: &Type, lhs: &Term, carrier: &Type, level: &Level) -> Vec<Term> {
        let mut out = vec![lhs.clone()];
        let (head, _) = crate::spelling::app_spine(lhs);
        if !matches!(head, Term::GlobalTm { .. }) {
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
        let Ok((ty, level)) = typing::infer_term(oracle.world(), 0, Layer::Prog, &cx.gamma, a, self.fuel) else {
            return false;
        };
        self.motive_candidate_converts(cx, b, a, &ty, &level)
    }
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
