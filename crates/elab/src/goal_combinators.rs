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
pub(crate) const SPLIT_STUCK: &str = "\0split-stuck-case";

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
            // A match arm's own binders (`#scrut`) have no source name to
            // match on.
            if name.starts_with('#') {
                return None;
            }
            let inductive = elab.tag_of(&entry.ty)?;
            // Recursive and indexed families are not finite case domains, and
            // a record is one case. Non-recursive constructors may carry
            // payloads; splitting still creates finitely many goals and binds
            // those payloads normally.
            if !finite_inductive(&inductive) {
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
/// scrutinee that blocks it. The replacement lives under the scrutinee binder.
struct Blocked {
    original: Term,
    replacement: Rc<Term>,
    scrutinee: Rc<Term>,
    /// The scrutinee type's constructors, with their field counts.
    constructors: Vec<(String, usize)>,
    /// The word comparison the scrutinee is or unfolds to: each arm gets its
    /// Nat reading.
    comparison: Option<Rc<Term>>,
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

/// A finite case domain: finitely many constructors, more than one, none
/// recursive or indexed. A record is not one: splitting it adds no case, only
/// names for its fields, and a field the goal matches on is split where it
/// blocks.
fn finite_inductive(inductive: &crate::inductive::Inductive) -> bool {
    !inductive.recursive && inductive.index.is_none() && inductive.ctors.len() > 1
}

fn constructors(inductive: &crate::inductive::Inductive) -> Vec<(String, usize)> {
    inductive.ctors.iter().map(|ctor| (ctor.name.clone(), ctor.fields.len())).collect()
}

/// The inductive a match's left alternative belongs to, when it is a finite
/// case domain. The alternatives are spelled as their payload globals
/// (`El(Bool#True_payload)`), so the tag is read after decoding.
fn case_domain(elab: &Elaborator, cx: &Cx, lhs: &Type) -> Option<Rc<crate::inductive::Inductive>> {
    let inductive = type_inductive(elab, cx, lhs)?;
    finite_inductive(&inductive).then_some(inductive)
}

/// `logic`'s `And`: a goal the leaf proves one side at a time.
fn conjunction(inductive: &crate::inductive::Inductive) -> bool {
    matches!(inductive.name.as_str(), "And" | "logic::And") && inductive.ctors.len() == 1 && inductive.ctors[0].fields.len() == 2
}

/// The inductive a type is, reading through `El`-headed spellings that only
/// unfold to their encoding.
fn type_inductive(elab: &Elaborator, cx: &Cx, ty: &Type) -> Option<Rc<crate::inductive::Inductive>> {
    elab.tag_of(ty).or_else(|| elab.tag_of(&elab.goal_oracle().diagnostics(64).decode_type(&cx.gamma, ty)?))
}

/// The comparison a scrutinee is, or becomes within a few transparent steps:
/// a helper such as `lowb(x) = x.unsigned_lt_bit(10)` is its comparison.
fn comparison_of(elab: &Elaborator, cx: &Cx, scrut: &Term) -> Option<Rc<Term>> {
    let oracle = elab.goal_oracle();
    std::iter::once(scrut.clone())
        .chain(oracle.term_reducts(&cx.gamma, scrut, 8))
        .find(|reduct| {
            crate::omega_cert::named_args(elab, reduct, "bitvec::BitVec::unsigned_lt_bit").is_some()
        })
        .map(Rc::new)
}

/// A `bitvec::BitVec` operation applied: the search's atoms.
fn word_operation(elab: &Elaborator, term: &Term) -> bool {
    let mut head = term;
    while let Some((fun, _)) = crate::spelling::app_of(head) {
        head = fun;
    }
    let Term::GlobalTm { var, .. } = head else { return false };
    elab.global_abs_of(*var)
        .and_then(|abs| elab.global_qualified_name_at(abs))
        .is_some_and(|name| name.starts_with("bitvec::BitVec::"))
}

/// The match at a reduct's head, below any projections of it.
fn head_match(term: &Term) -> &Term {
    match crate::spelling::proj_of(term) {
        Some((_, pair)) => head_match(pair),
        None => term,
    }
}

/// Inspect transparent heads, projections and application arguments, but never
/// enter a recursor's motives or branches: those are not the current goal's
/// blockers. A shared step budget bounds speculative unfolding. Every
/// replacement is a transparent reduct with its scrutinee abstracted by the
/// kernel's own substitution traversal, so the motive specializes even below
/// `toNat`.
///
/// What blocks a match, in order: something deeper in its scrutinee; the
/// comparison the scrutinee is or unfolds to; the scrutinee itself, when it is
/// a neutral of a finite type the source can spell (`s.inside`, a Bool
/// local). A comparison is never unfolded: its bit-level fold is not the
/// goal's case analysis.
fn stuck_scrutinee(elab: &Elaborator, cx: &Cx, term: &Term, budget: &mut u32) -> Option<Blocked> {
    if *budget == 0 {
        return None;
    }
    *budget -= 1;
    let (_, args) = crate::spelling::app_spine(term);
    for arg in args {
        if let Some(found) = stuck_scrutinee(elab, cx, arg, budget) {
            return Some(found);
        }
    }
    // A blocker below a word operation was already sought in its
    // arguments. Unfolding the operation itself (`toNat`, `add`, a
    // comparison) only exposes its bit-level fold, which is not the goal's
    // case analysis — the arithmetic tactics read words as atoms — and can
    // spend the entire search budget before the other side of a goal.
    if word_operation(elab, term) {
        return None;
    }
    if let Term::Succ(inner) = term {
        return stuck_scrutinee(elab, cx, inner, budget);
    }
    let oracle = elab.goal_oracle();
    for reduct in std::iter::once(term.clone()).chain(oracle.term_reducts(&cx.gamma, term, 64)) {
        if *budget == 0 {
            return None;
        }
        *budget -= 1;
        let (scrut, domain) = match head_match(&reduct) {
            Term::Case { scrut, lhs, .. } => (scrut, case_domain(elab, cx, lhs)),
            Term::ElimNat { scrut, .. } => (scrut, None),
            // A call the definition unfolded to: what blocks it may be in
            // its arguments (`fold(step, rest, step(count, byte))`).
            _ if reduct != *term => {
                for arg in crate::spelling::app_spine(&reduct).1 {
                    if let Some(found) = stuck_scrutinee(elab, cx, arg, budget) {
                        let replacement = payload(term_type(Rc::new(reduct.clone())).abstract_local_with(&found.original, &found.replacement)?);
                        return Some(Blocked { original: term.clone(), replacement, ..found });
                    }
                }
                continue;
            }
            _ => continue,
        };
        let abstracted = |original: &Term, replacement: &Rc<Term>| {
            Some(payload(term_type(Rc::new(reduct.clone())).abstract_local_with(original, replacement)?))
        };
        if let Some(inductive) = &domain
            && let Some(comparison) = comparison_of(elab, cx, scrut)
        {
            return Some(Blocked {
                original: term.clone(),
                replacement: payload(term_type(Rc::new(reduct.clone())).abstract_local(scrut)?),
                scrutinee: scrut.clone(),
                constructors: constructors(inductive),
                comparison: Some(comparison),
            });
        }
        if let Some(found) = stuck_scrutinee(elab, cx, scrut, budget) {
            return Some(Blocked { original: term.clone(), replacement: abstracted(&found.original, &found.replacement)?, ..found });
        }
        // A scrutinee that computes to a constructor reduces the match at a
        // later step; keep stepping.
        if let Ok(whnf) = oracle.bounded(64).whnf_term(&cx.gamma, scrut)
            && crate::spelling::is_inj(&whnf)
        {
            continue;
        }
        let inductive = domain?;
        elab.spell_term_source(cx, scrut)?;
        return Some(Blocked {
            original: term.clone(),
            replacement: payload(term_type(Rc::new(reduct.clone())).abstract_local(scrut)?),
            scrutinee: scrut.clone(),
            constructors: constructors(&inductive),
            comparison: None,
        });
    }
    None
}

/// Positions of `term` that reach `scrut` only through transparent
/// definitions, each paired with a reduct that spells it, abstracted. A
/// position that already spells it, or is the search's own `found`, is left
/// to the abstraction itself.
fn co_occurrences(elab: &Elaborator, cx: &Cx, term: &Term, found: &Term, scrut: &Term, budget: &mut u32, out: &mut Vec<(Term, Term)>) {
    if *budget == 0 || term == found {
        return;
    }
    *budget -= 1;
    let spells = |t: &Term| term_type(Rc::new(t.clone())).abstract_local(scrut).map(payload);
    if spells(term).is_some() || word_operation(elab, term) {
        return;
    }
    let before = out.len();
    match term {
        Term::App { .. } | Term::AppAt { .. } => {
            for arg in crate::spelling::app_spine(term).1 {
                co_occurrences(elab, cx, arg, found, scrut, budget, out);
            }
        }
        Term::Succ(inner) | Term::Inl { val: inner, .. } | Term::InlAt { val: inner, .. }
        | Term::Inr { val: inner, .. } | Term::InrAt { val: inner, .. } => co_occurrences(elab, cx, inner, found, scrut, budget, out),
        Term::Pair { fst, snd, .. } | Term::PairAt { fst, snd, .. } => {
            co_occurrences(elab, cx, fst, found, scrut, budget, out);
            co_occurrences(elab, cx, snd, found, scrut, budget, out);
        }
        _ => {
            if let Some((_, pair)) = crate::spelling::proj_of(term) {
                co_occurrences(elab, cx, pair, found, scrut, budget, out);
            }
        }
    }
    if out.len() > before {
        return;
    }
    for reduct in elab.goal_oracle().term_reducts(&cx.gamma, term, 64) {
        if *budget == 0 {
            return;
        }
        *budget -= 1;
        if let Some(abstracted) = spells(&reduct) {
            out.push((term.clone(), (*abstracted).clone()));
            return;
        }
    }
}

pub(crate) struct StuckSplit {
    pub scrut: Expr,
    pub equation: String,
    pub motive: Type,
    pub arms: Vec<Arm>,
}

/// What a `split_all` leaf does with the goal in hand: introduce a binder,
/// prove a conjunction's two sides, split the match blocking it, or hand it
/// to the body.
pub(crate) enum Step {
    Intro(Expr),
    Conjoin(Expr),
    Split(StuckSplit),
    Leaf(Type),
}

/// A name no local and no global in scope has, from `base`.
fn fresh(elab: &Elaborator, cx: &Cx, base: String) -> String {
    let mut name = base;
    while elab.shadowed(cx, &name) || cx.names.iter().any(|n| *n == name) {
        name.push('_');
    }
    name
}

pub(crate) fn next_step(elab: &Elaborator, cx: &Cx, expected: &Type, leaf: &Expr, span: Span) -> Step {
    let var = |name: &str| Expr { kind: ExprKind::Var(name.into()), span };
    let whnf = elab.goal_oracle().bounded(256).whnf_type(&cx.gamma, expected);
    match whnf {
        // `(x: A) → B`: introduce `x`, and split it when `A` is finite.
        Ok(Type::Pi { dom, .. }) => {
            let name = fresh(elab, cx, format!("__split_all_x{}", cx.names.len()));
            let body = match type_inductive(elab, cx, &dom).filter(|inductive| finite_inductive(inductive)) {
                Some(inductive) => {
                    let local = FiniteLocal { name: name.clone(), constructors: constructors(&inductive) };
                    tree(std::slice::from_ref(&local), &continuation(leaf, span), span, cx.names.len())
                }
                None => continuation(leaf, span),
            };
            return Step::Intro(Expr {
                kind: ExprKind::Lam {
                    binders: vec![heather_syntax::LamBinder { name, ty: None, implicit: false, span }],
                    body: Box::new(body),
                },
                span,
            });
        }
        Ok(ty) if type_inductive(elab, cx, &ty).is_some_and(|inductive| conjunction(&inductive)) => {
            return Step::Conjoin(Expr {
                kind: ExprKind::App {
                    head: Box::new(var(heather_syntax::ANON_CTOR_ONLY)),
                    args: vec![continuation(leaf, span), continuation(leaf, span)],
                    named: vec![],
                    explicit: false,
                    goal_oriented: false,
                },
                span,
            });
        }
        _ => {}
    }
    // A goal reached through an introduced binder may still be spelled as
    // its code (`El(⌜Id …⌝)`); the search reads the decoded former.
    let goal = simplify_goal(elab, cx, &crate::inductive::decoded(expected));
    match split_stuck(elab, cx, &goal, leaf, span) {
        Some(split) => Step::Split(split),
        None => Step::Leaf(goal),
    }
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
        // Every occurrence alike: a split abstracts the goal's term
        // syntactically, so an occurrence left unsimplified inside a
        // constructor would keep its old match and miss the next motive.
        match &mut output {
            Term::App { fun, arg, .. } | Term::AppAt { fun, arg } => {
                *fun = Rc::new(term(elab, cx, fun, budget));
                *arg = Rc::new(term(elab, cx, arg, budget));
                // A function literal applied, such as a count `λ s => s.lines`
                // a definition passed along: β, so the leaf reads the field.
                if matches!(&**fun, Term::Lam { .. })
                    && let Ok(reduced) = elab.goal_oracle().bounded(64).whnf_term_opaque(&cx.gamma, &output)
                    && reduced != output
                {
                    return term(elab, cx, &reduced, budget);
                }
            }
            Term::Succ(inner) => *inner = Rc::new(term(elab, cx, inner, budget)),
            Term::Inl { val, .. } | Term::InlAt { val, .. } | Term::Inr { val, .. } | Term::InrAt { val, .. } => {
                *val = Rc::new(term(elab, cx, val, budget));
            }
            Term::Pair { fst, snd, .. } | Term::PairAt { fst, snd, .. } => {
                *fst = Rc::new(term(elab, cx, fst, budget));
                *snd = Rc::new(term(elab, cx, snd, budget));
            }
            Term::Fst { .. } | Term::FstAt { .. } | Term::Snd { .. } | Term::SndAt { .. } => {
                if let Ok(reduced) = elab
                    .goal_oracle()
                    .bounded(64)
                    .whnf_term_opaque(&cx.gamma, input)
                    && reduced != *input
                {
                    return term(elab, cx, &reduced, budget);
                }
                if let Term::Fst { pair, .. } | Term::FstAt { pair } | Term::Snd { pair, .. } | Term::SndAt { pair } = &mut output {
                    *pair = Rc::new(term(elab, cx, pair, budget));
                }
            }
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

fn split_stuck(
    elab: &Elaborator,
    cx: &Cx,
    expected: &Type,
    leaf: &Expr,
    span: Span,
) -> Option<StuckSplit> {
    let mut budget = 512;
    let found = match expected {
        Type::Id { lhs, rhs, .. } => stuck_scrutinee(elab, cx, lhs, &mut budget)
            .or_else(|| stuck_scrutinee(elab, cx, rhs, &mut budget)),
        Type::El { tm, .. } => stuck_scrutinee(elab, cx, tm, &mut budget),
        _ => None,
    };
    let found = found?;
    let source = elab.spell_term_source(cx, &found.scrutinee)?;
    // The scrutinee the search found on one side may be reached elsewhere
    // only through a definition (`wc_next(…, s)` beside a step that matched
    // on `s.inside`): abstract it there too, or the next split would case
    // on it again with no link to this one.
    let mut pairs = vec![(found.original.clone(), (*found.replacement).clone())];
    let mut co_budget = 256;
    // An equation's sides are values and may unfold; a relation such as
    // `Le(a, b)` keeps its own spelling for the leaf, so only its arguments
    // are searched.
    match expected {
        Type::Id { lhs, rhs, .. } => for term in [lhs, rhs] {
            co_occurrences(elab, cx, term, &found.original, &found.scrutinee, &mut co_budget, &mut pairs);
        },
        Type::El { tm, .. } => for arg in crate::spelling::app_spine(tm).1 {
            co_occurrences(elab, cx, arg, &found.original, &found.scrutinee, &mut co_budget, &mut pairs);
        },
        _ => {}
    }
    pairs.push((found.scrutinee.as_ref().clone(), Term::Var(heather_kernel::term::LocalVar(0))));
    let scrut = crate::omega_cert::parse_generated_expr(&source).ok()?;
    let motive = expected.abstract_local_with_all(&pairs)?;
    let equation = fresh(elab, cx, "__split_case".to_string());
    let order = fresh(elab, cx, format!("{equation}_nat"));
    // The comparison's operands, when the bridge library is there to read
    // them as Nats.
    let operands = found
        .comparison
        .as_ref()
        .filter(|_| elab.key_of("bitvec_omega::unsigned_true").is_some())
        .and_then(|comparison| crate::omega_cert::named_args(elab, comparison, "bitvec::BitVec::unsigned_lt_bit"))
        .and_then(|args| args.iter().map(|term| elab.spell_term_source(cx, term)).collect::<Option<Vec<_>>>())
        .map(|operands| operands.join(", "));
    let depth = cx.names.len();
    let arms = found
        .constructors
        .iter()
        .enumerate()
        .map(|(index, (ctor, arity))| {
            let mut body = continuation(leaf, span);
            // Keep the splitter useful without arithmetic imports. When the
            // bridge library is available, every leaf of a comparison receives
            // the Nat fact directly, including leaves such as `omega` that do
            // not read words.
            let outcome = match ctor.as_str() { "True" => Some("true"), "False" => Some("false"), _ => None };
            if let (Some(operands), Some(outcome)) = (&operands, outcome)
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
                ctor: ctor.clone(),
                default: false,
                binders: (0..*arity)
                    .map(|field| Pat::Var { name: format!("__split_case_{depth}_{index}_{field}"), span })
                    .collect(),
                body,
                span,
            }
        })
        .collect();
    Some(StuckSplit {
        scrut,
        equation,
        motive,
        arms,
    })
}
