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

use std::sync::Arc as Rc;

use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{LocalSubst, LocalVar, Term, Type};
use heather_kernel::typing;
use heather_syntax::{Expr, ExprKind, NamedArg, Span};

use crate::{Cx, ElabError, Elaborator, R};

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
        let Type::Id { level, ty, lhs, rhs } = self.whnf(cx, &proof_ty, h.span)? else {
            let shown = self.display_type(cx, &proof_ty);
            return Err(ElabError::Elab {
                msg: format!(
                    "`rewrite` rewrites along an equation `a = b`, and this proof is of `{shown}`\n  \
                     hint: a relation other than `=` rewrites with `rel_cong(h)` or a `calc` step"
                ),
                span: h.span,
            });
        };
        let motive = self.rewrite_motive(cx, h, at, goal, &ty, &level, &lhs, &rhs, lvl)?;
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
        carrier: &Rc<Type>,
        carrier_level: &Level,
        lhs: &Rc<Term>,
        rhs: &Rc<Term>,
        lvl: &Level,
    ) -> R<Type> {
        let shown = |t: &Term| self.spell_term_clean(cx, t).map_or_else(String::new, |s| format!(" `{s}`"));
        let exposed = || crate::matching::expose(self, cx, goal, h.span);
        let motive = match at {
            None => goal
                .abstract_local(lhs)
                .or_else(|| exposed().and_then(|g| g.abstract_local(lhs))),
            // Numbered against the goal as written, and only that: a number
            // that meant one thing as written and another after reduction
            // would be worse than a refusal.
            Some(at) => {
                let (motive, seen) = goal.abstract_local_at(lhs, at);
                if let Some(&past) = at.iter().find(|&&k| k > seen) {
                    return Err(ElabError::Elab {
                        msg: format!(
                            "`rewrite`: `at := {past}`, but the goal `{}` has {seen} occurrence(s) \
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
                    "\n  hint: the goal mentions its right side{}; to rewrite right to left, \
                     write `sym(…)` around the equation",
                    shown(rhs)
                )
            } else {
                String::new()
            };
            return Err(ElabError::Elab {
                msg: format!(
                    "`rewrite`: the goal `{}` does not mention the equation's left side{}\n  \
                     note: occurrences are matched as elaborated, implicit arguments included, \
                     and through at most one unfolding of the goal{hint}",
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
                    "`rewrite`: abstracting the left side{} from the goal does not leave a type: \
                     something else in the goal depends on it being exactly that term\n  \
                     hint: write the motive by hand with `j`",
                    shown(lhs)
                ),
                span: h.span,
            }
        })?;
        Ok(motive)
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
