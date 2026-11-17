//! `known` at a Bool guard (issues/bool-guard-facts-by-known.md): a goal
//! `b.IsTrue()` or `b = True` is proved from the guards in scope taken apart
//! by structure, as `omega`'s guard round reads them.
//!
//! A guard in scope is `g.IsTrue()`, `g = True` or `True = g`, alone or
//! under a conjunction. Each is read as a list of facts `b.IsTrue()`, each
//! with its proof: `(x && y).IsTrue()` gives `x` and `y` through
//! `Bool::both`, and a guard headed by a Bool definition is opened to its
//! first reduct with a connective at its head (`omega_cert::unfold_guard`,
//! so `words_fit([a, b])` is `word_fits(a) && words_fit([b])`) and read
//! again, the proof unchanged since the two types convert. The goal is
//! taken apart the same way: a fact of its type, else `x && y` from its
//! sides by `Bool::is_true_and_intro`, else its definition's reduct.

use heather_kernel::level::Level;
use heather_kernel::rc::Rc;
use heather_kernel::term::{Term, Type};
use heather_syntax::{Expr, ExprKind, Span};

use crate::Cx;
use crate::context::Alias;
use crate::omega_cert::{GuardShape, bool_equation, guard_shape, is_true_arg, unfold_guard, with_arg_at};
use crate::tested::Tested;

/// Facts read off the guards in scope, at most: a guard is taken apart one
/// connective or one definition at a time, so this bounds the walk.
const FACTS: usize = 256;
/// Connectives and definitions the goal is taken apart through.
const GOAL_DEPTH: usize = 32;

/// A fact `b.IsTrue()` and its proof.
struct Fact {
    bit: Rc<Term>,
    proof: Term,
    ty: Type,
}

/// `name := term : ty` bound for an expression to name.
fn bound(cx: &Cx, name: &str, term: Term, ty: Type, level: Level) -> Cx {
    let mut cx = cx.clone();
    cx.aliases.push(Rc::new(Alias {
        name: name.to_string(),
        depth: cx.names.len(),
        term: Rc::new(term),
        ty,
        level,
        skel: None,
        spliced: None,
        shifted: Default::default(),
    }));
    cx
}

fn var(name: &str, span: Span) -> Expr {
    Expr { kind: ExprKind::Var(name.to_string()), span }
}

fn call(head: &str, args: Vec<Expr>, span: Span) -> Expr {
    Expr {
        kind: ExprKind::App { head: Box::new(var(head, span)), args, named: vec![], explicit: false, goal_oriented: false },
        span,
    }
}

/// `ty` with its guard `b.IsTrue()` replaced by `bit.IsTrue()`.
fn retyped(ty: &Type, bit: &Rc<Term>) -> Option<Type> {
    let Type::El { level, tm } = ty else { return None };
    Some(Type::El { level: level.clone(), tm: with_arg_at(tm, 0, bit) })
}

const GUARD: &str = "__known_guard";
const LEFT: &str = "__known_left";
const RIGHT: &str = "__known_right";
const BIT: &str = "__known_bit";
const X: &str = "__known_x";
const Y: &str = "__known_y";

impl Tested<'_> {
    /// A proof of `expected` when it is a Bool guard the guards in scope
    /// decide; `None` when it is no guard or they do not.
    pub(crate) fn known_guard(&self, cx: &Cx, names: &[String], expected: &Type, lvl: &Level, span: Span) -> Option<Term> {
        if self.key_of("bool::Bool::both").is_none() {
            return None;
        }
        if let Some(bit) = is_true_arg(self, expected) {
            let bit = Rc::clone(bit);
            let facts = self.guard_facts(cx, names, span);
            return self.prove_guard(cx, &facts, expected, &bit, lvl, span, GOAL_DEPTH);
        }
        // `b = True` (or `True = b`): `b.IsTrue()`, turned back.
        let (bit, true, flipped) = bool_equation(self, cx, expected)? else { return None };
        let decoded = crate::inductive::decoded(expected);
        let Type::Id { level: bit_level, ty: bool_ty, .. } = &*decoded else { return None };
        let with_bit = bound(cx, BIT, (*bit).clone(), (**bool_ty).clone(), bit_level.clone());
        let is_true = heather_syntax::Ty { kind: heather_syntax::TyKind::OfExpr(Box::new(call("bool::Bool::IsTrue", vec![var(BIT, span)], span))), span };
        let (goal, goal_level) = self.probe(|| self.elab_ty(&with_bit, &is_true).ok())?;
        let facts = self.guard_facts(cx, names, span);
        let proof = self.prove_guard(cx, &facts, &goal, &bit, &goal_level, span, GOAL_DEPTH)?;
        let held = bound(&with_bit, GUARD, proof, goal, goal_level);
        let turned = call("eq_true_of_is_true", vec![var(BIT, span), var(GUARD, span)], span);
        let turned = if flipped { call("sym", vec![turned], span) } else { turned };
        self.checked(&held, &turned, expected, lvl)
    }

    /// `e` checked at `expected`, or `None` when it does not check.
    fn checked(&self, cx: &Cx, e: &Expr, expected: &Type, lvl: &Level) -> Option<Term> {
        self.probe(|| self.elab_check(cx, e, expected, lvl).is_ok()).then(|| self.elab_check(cx, e, expected, lvl).ok()).flatten()
    }

    /// The facts the guards in scope give, innermost name first.
    fn guard_facts(&self, cx: &Cx, names: &[String], span: Span) -> Vec<Fact> {
        let mut facts = Vec::new();
        for name in names {
            let Ok((term, ty, level)) = self.resolve_reading(cx, name, span) else { continue };
            self.push_facts(cx, term, ty, level, span, &mut facts);
        }
        facts
    }

    /// `term: ty` read as facts: each side of a conjunction, a guard and
    /// what it is made of, a guard equation as its guard.
    fn push_facts(&self, cx: &Cx, term: Term, ty: Type, level: Level, span: Span, out: &mut Vec<Fact>) {
        if out.len() >= FACTS {
            return;
        }
        let ty = crate::spelling::beta_head_ty(&ty).unwrap_or(ty);
        if let Some(ind) = self.display_tag_of(&ty)
            && crate::goal_combinators::conjunction(&ind)
        {
            let term = Rc::new(term);
            for idx in 0..2 {
                if let Ok((side, side_ty, side_level)) = self.project_field(cx, &ind, &ty, Rc::clone(&term), idx, span) {
                    self.push_facts(cx, side, side_ty, side_level, span, out);
                }
            }
            return;
        }
        if let Some(bit) = is_true_arg(self, &ty) {
            let bit = Rc::clone(bit);
            self.push_guard(cx, bit, term, ty, level, span, out);
            return;
        }
        if let Some((_, true, flipped)) = bool_equation(self, cx, &ty) {
            let held = bound(cx, GUARD, term, ty, level);
            let h = if flipped { call("sym", vec![var(GUARD, span)], span) } else { var(GUARD, span) };
            let read = call("bool::Bool::is_true_of_eq", vec![h], span);
            if let Some((term, ty, level)) = self.inferred(&held, &read) {
                self.push_facts(cx, term, ty, level, span, out);
            }
        }
    }

    /// The fact `bit.IsTrue()`, then what it is made of: both sides of an
    /// `&&`, and a definition's reduct with a connective at its head.
    fn push_guard(&self, cx: &Cx, bit: Rc<Term>, proof: Term, ty: Type, level: Level, span: Span, out: &mut Vec<Fact>) {
        if out.len() >= FACTS {
            return;
        }
        // An induction hypothesis's call, `(λ i => g(…))(k)`, at its head.
        let (bit, ty) = match crate::spelling::beta_head(&bit) {
            Some(reduced) => {
                let reduced = Rc::new(reduced);
                let Some(ty) = retyped(&ty, &reduced) else { return };
                (reduced, ty)
            }
            None => (bit, ty),
        };
        out.push(Fact { bit: Rc::clone(&bit), proof: proof.clone(), ty: ty.clone() });
        match guard_shape(self, &bit) {
            GuardShape::And(..) => {
                let held = bound(cx, GUARD, proof, ty, level);
                if let Some((term, ty, level)) = self.inferred(&held, &call("bool::Bool::both", vec![var(GUARD, span)], span)) {
                    self.push_facts(cx, term, ty, level, span, out);
                }
            }
            // The same proof at the definition's reduct, a type the guard
            // converts to.
            GuardShape::Atom | GuardShape::Other => {
                if let Some(reduct) = self.opened(cx, &bit)
                    && let Some(opened) = retyped(&ty, &reduct)
                {
                    self.push_guard(cx, reduct, proof, opened, level, span, out);
                }
            }
            _ => {}
        }
    }

    /// A Bool definition's call opened to its first reduct that is an
    /// `&&`, where one is: only a conjunction has parts to read.
    /// A `match` on a constructor (a case arm's instance of its motive) is
    /// reduced the same way.
    fn opened(&self, cx: &Cx, bit: &Rc<Term>) -> Option<Rc<Term>> {
        let reduct = match guard_shape(self, bit) {
            GuardShape::Atom => unfold_guard(self, cx, bit)?,
            GuardShape::Other => {
                let oracle = self.goal_oracle();
                oracle.unfold(&cx.gamma, bit, crate::oracle::Unfold::Proposition).map(Rc::new).find(|reduct| {
                    !matches!(guard_shape(self, reduct), GuardShape::Other)
                })?
            }
            _ => return None,
        };
        matches!(guard_shape(self, &reduct), GuardShape::And(..)).then_some(reduct)
    }

    /// `e` inferred, or `None` when it does not infer.
    fn inferred(&self, cx: &Cx, e: &Expr) -> Option<(Term, Type, Level)> {
        self.probe(|| self.elab_infer(cx, e).is_ok()).then(|| self.elab_infer(cx, e).ok()).flatten()
    }

    /// A proof of `goal`, the guard `bit.IsTrue()`, from `facts`: one of its
    /// type, else its sides when it is an `&&`, else its definition's
    /// reduct.
    #[allow(clippy::too_many_arguments)]
    fn prove_guard(&self, cx: &Cx, facts: &[Fact], goal: &Type, bit: &Rc<Term>, lvl: &Level, span: Span, depth: usize) -> Option<Term> {
        if let Some(fact) = facts.iter().find(|fact| fact.bit == *bit) {
            return Some(fact.proof.clone());
        }
        if let Some(fact) = facts.iter().find(|fact| self.conv_types(cx, &fact.ty, goal, lvl)) {
            return Some(fact.proof.clone());
        }
        if let Ok(Type::Unit { level }) = self.goal_oracle().bounded(256).whnf_type(&cx.gamma, goal) {
            return Some(Term::Triv { level });
        }
        if depth == 0 {
            return None;
        }
        if let Some(reduced) = crate::spelling::beta_head(bit) {
            let reduced = Rc::new(reduced);
            return self.prove_guard(cx, facts, &retyped(goal, &reduced)?, &reduced, lvl, span, depth - 1);
        }
        match guard_shape(self, bit) {
            GuardShape::And(x, y) => {
                let (x, y) = (Rc::clone(x), Rc::clone(y));
                let left = self.prove_guard(cx, facts, &retyped(goal, &x)?, &x, lvl, span, depth - 1)?;
                let right = self.prove_guard(cx, facts, &retyped(goal, &y)?, &y, lvl, span, depth - 1)?;
                // `Bool::is_true_and_intro(x, y, left, right)`, its sides
                // named at `Bool`'s type, which `True` gives.
                let (_, bool_ty, bool_level) = self.inferred(cx, &var("bool::True", span)).or_else(|| self.inferred(cx, &var("True", span)))?;
                let held = bound(cx, X, (*x).clone(), bool_ty.clone(), bool_level.clone());
                let held = bound(&held, Y, (*y).clone(), bool_ty, bool_level);
                let held = bound(&held, LEFT, left, retyped(goal, &x)?, lvl.clone());
                let held = bound(&held, RIGHT, right, retyped(goal, &y)?, lvl.clone());
                let both = call("bool::Bool::is_true_and_intro", vec![var(X, span), var(Y, span), var(LEFT, span), var(RIGHT, span)], span);
                self.checked(&held, &both, goal, lvl)
            }
            GuardShape::Atom | GuardShape::Other => {
                let reduct = self.opened(cx, bit)?;
                self.prove_guard(cx, facts, &retyped(goal, &reduct)?, &reduct, lvl, span, depth - 1)
            }
            _ => None,
        }
    }
}
