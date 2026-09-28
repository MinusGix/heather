//! Checking-only goal-tree combinators.
//!
//! `split_all; all_goals { body }` is elaborator sugar for an ordinary nested
//! match whose leaves are copies of `body`. The generated proof remains an
//! ordinary term and crosses the declaration's normal kernel gate.

use std::sync::Arc as Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{Term, Type};
use heather_syntax::{Arm, Block, Expr, ExprKind, MatchForm, Pat, Span, Stmt};

use crate::{Cx, Elaborator};

/// Re-enter after each branch's motive has specialized the goal. Like the
/// parser marker, this head cannot collide with a source name.
pub(crate) const SPLIT_STUCK: &str = "\0split-stuck-comparison";

fn continuation(leaf: &Expr, span: Span) -> Expr {
    Expr {
        kind: ExprKind::App {
            head: Box::new(Expr {
                kind: ExprKind::Var(SPLIT_STUCK.into()),
                span,
            }),
            args: vec![leaf.clone()],
            named: vec![],
            explicit: false,
            goal_oriented: false,
        },
        span,
    }
}

struct FiniteLocal {
    name: String,
    constructors: Vec<(String, usize)>,
}

fn finite_locals(elab: &Elaborator, cx: &Cx) -> Vec<FiniteLocal> {
    cx.names
        .iter()
        .zip(cx.gamma.entries.iter())
        .filter_map(|(name, entry)| {
            let inductive = elab.tag_of(&entry.ty)?;
            // Recursive and indexed families are not finite case domains.
            // Non-recursive constructors may carry payloads; splitting still
            // creates finitely many goals and binds those payloads normally.
            if inductive.recursive || inductive.index.is_some() {
                return None;
            }
            Some(FiniteLocal {
                name: name.clone(),
                constructors: inductive
                    .ctors
                    .iter()
                    .map(|ctor| (ctor.name.clone(), ctor.fields.len()))
                    .collect(),
            })
        })
        .collect()
}

fn tree(locals: &[FiniteLocal], leaf: &Expr, span: Span, depth: usize) -> Expr {
    let Some((local, rest)) = locals.split_first() else {
        return leaf.clone();
    };
    let branch = tree(rest, leaf, span, depth + 1);
    Expr {
        kind: ExprKind::Match {
            form: MatchForm::Match,
            generated: true,
            scrut: Box::new(Expr {
                kind: ExprKind::Var(local.name.clone()),
                span,
            }),
            eqbind: None,
            motive: None,
            arms: local
                .constructors
                .iter()
                .enumerate()
                .map(|(ctor_index, (ctor, arity))| Arm {
                    ctor: ctor.clone(),
                    default: false,
                    binders: (0..*arity)
                        .map(|field| Pat::Var {
                            name: format!("__split_all_{depth}_{ctor_index}_{field}"),
                            span,
                        })
                        .collect(),
                    body: branch.clone(),
                    span,
                })
                .collect(),
        },
        span,
    }
}

pub(crate) fn split_all(elab: &Elaborator, cx: &Cx, leaf: &Expr, span: Span) -> Expr {
    tree(&finite_locals(elab, cx), &continuation(leaf, span), span, 0)
}

/// A transparent goal position together with its reduct abstracted over the
/// blocking comparison. The replacement lives under the comparison binder.
struct Blocked {
    original: Term,
    replacement: Rc<Term>,
    comparison: Rc<Term>,
}

fn term_type(term: Rc<Term>) -> Type {
    // Only the term is used after abstraction; this wrapper supplies the
    // kernel's binder-aware traversal without assigning the term a type.
    Type::El {
        level: Level::Zero,
        tm: term,
    }
}

fn payload(ty: Type) -> Rc<Term> {
    let Type::El { tm, .. } = ty else {
        unreachable!("abstraction preserves the wrapper")
    };
    tm
}

/// Inspect transparent heads and application arguments, but never enter a
/// recursor's motives or branches: those are not the current goal's blockers.
/// A shared step budget bounds speculative unfolding. Every replacement is
/// a transparent reduct with its comparison abstracted by the kernel's own
/// substitution traversal, so the motive specializes even below `toNat`.
fn stuck_comparison(elab: &Elaborator, cx: &Cx, term: &Term, budget: &mut u32) -> Option<Blocked> {
    if *budget == 0 {
        return None;
    }
    *budget -= 1;
    let (_, args) = crate::spelling::app_spine(term);
    for arg in args {
        if let Some(found) = stuck_comparison(elab, cx, arg, budget) {
            return Some(found);
        }
    }
    // A blocker below `toNat` was already sought in its word argument.
    // Unfolding the conversion itself only exposes the bit-level fold and
    // can spend the entire search budget before the other side of a goal.
    if crate::omega_cert::named_args(elab, term, "bitvec::BitVec::toNat").is_some() {
        return None;
    }
    if let Term::Succ(inner) = term {
        return stuck_comparison(elab, cx, inner, budget);
    }
    let oracle = elab.goal_oracle();
    for reduct in std::iter::once(term.clone()).chain(oracle.term_reducts(&cx.gamma, term, 64)) {
        if *budget == 0 {
            return None;
        }
        *budget -= 1;
        let scrut = match &reduct {
            Term::Case { scrut, .. } | Term::ElimNat { scrut, .. } => scrut,
            _ => continue,
        };
        let (replacement, comparison) =
            if crate::omega_cert::named_args(elab, scrut, "bitvec::BitVec::unsigned_lt_bit")
                .is_some()
            {
                (
                    payload(term_type(Rc::new(reduct.clone())).abstract_local(scrut)?),
                    scrut.clone(),
                )
            } else {
                let Some(found) = stuck_comparison(elab, cx, scrut, budget) else {
                    // A constructor scrutinee can compute to another match;
                    // keep stepping before handing the goal to the leaf.
                    continue;
                };
                (
                    payload(
                        term_type(Rc::new(reduct.clone()))
                            .abstract_local_with(&found.original, &found.replacement)?,
                    ),
                    found.comparison,
                )
            };
        return Some(Blocked {
            original: term.clone(),
            replacement,
            comparison,
        });
    }
    None
}

pub(crate) struct ComparisonSplit {
    pub scrut: Expr,
    pub equation: String,
    pub motive: Type,
    pub arms: Vec<Arm>,
}

/// Compute the constructor cases left by a previous split, including below
/// applications, while keeping library calls spelled as library calls.
pub(crate) fn simplify_goal(elab: &Elaborator, cx: &Cx, expected: &Type) -> Type {
    fn term(elab: &Elaborator, cx: &Cx, input: &Term, budget: &mut u32) -> Term {
        if *budget == 0 {
            return input.clone();
        }
        *budget -= 1;
        let mut output = input.clone();
        match &mut output {
            Term::App { fun, arg, .. } | Term::AppAt { fun, arg } => {
                *fun = Rc::new(term(elab, cx, fun, budget));
                *arg = Rc::new(term(elab, cx, arg, budget));
            }
            Term::Succ(inner) => *inner = Rc::new(term(elab, cx, inner, budget)),
            Term::Case { .. } | Term::ElimNat { .. } => {
                if let Ok(reduced) = elab
                    .goal_oracle()
                    .bounded(64)
                    .whnf_term_opaque(&cx.gamma, input)
                    && reduced != *input
                {
                    return term(elab, cx, &reduced, budget);
                }
            }
            _ => {}
        }
        output
    }
    let mut output = expected.clone();
    let mut budget = 512;
    match &mut output {
        Type::Id { lhs, rhs, .. } => {
            *lhs = Rc::new(term(elab, cx, lhs, &mut budget));
            *rhs = Rc::new(term(elab, cx, rhs, &mut budget));
        }
        Type::El { tm, .. } => *tm = Rc::new(term(elab, cx, tm, &mut budget)),
        _ => {}
    }
    output
}

pub(crate) fn split_stuck(
    elab: &Elaborator,
    cx: &Cx,
    expected: &Type,
    leaf: &Expr,
    span: Span,
) -> Option<ComparisonSplit> {
    let mut budget = 512;
    let found = match expected {
        Type::Id { lhs, rhs, .. } => stuck_comparison(elab, cx, lhs, &mut budget)
            .or_else(|| stuck_comparison(elab, cx, rhs, &mut budget)),
        Type::El { tm, .. } => stuck_comparison(elab, cx, tm, &mut budget),
        _ => None,
    }?;
    let source = elab.spell_term_source(cx, &found.comparison)?;
    let scrut = crate::omega_cert::parse_generated_expr(&source).ok()?;
    let motive = expected.abstract_local_with(&found.original, &found.replacement)?;
    let mut equation = "__split_comparison".to_string();
    while elab.shadowed(cx, &equation) {
        equation.push('_');
    }
    let mut order = format!("{equation}_nat");
    while elab.shadowed(cx, &order) {
        order.push('_');
    }
    let operands =
        crate::omega_cert::named_args(elab, &found.comparison, "bitvec::BitVec::unsigned_lt_bit")?
            .iter()
            .map(|term| elab.spell_term_source(cx, term))
            .collect::<Option<Vec<_>>>()?;
    let operands = operands.join(", ");
    let arms = [("True", "true"), ("False", "false")]
        .into_iter()
        .map(|(ctor, outcome)| {
            let mut body = continuation(leaf, span);
            // Keep the splitter useful without arithmetic imports. When the
            // bridge library is available, every leaf receives the Nat fact
            // directly, including leaves such as `omega` that do not read words.
            if elab.key_of("bitvec_omega::unsigned_true").is_some()
                && let Ok(expr) = crate::omega_cert::parse_generated_expr(&format!(
                    "bitvec_omega::unsigned_{outcome}({operands}, {equation})"
                ))
            {
                body = Expr {
                    kind: ExprKind::Block(Box::new(Block {
                        stmts: vec![Stmt::Let {
                            name: order.clone(),
                            ty: None,
                            expr,
                            span,
                            opaque: true,
                        }],
                        result: Box::new(body),
                        ons: vec![],
                        span,
                    })),
                    span,
                };
            }
            Arm {
                ctor: ctor.into(),
                default: false,
                binders: vec![],
                body,
                span,
            }
        })
        .collect();
    Some(ComparisonSplit {
        scrut,
        equation,
        motive,
        arms,
    })
}
