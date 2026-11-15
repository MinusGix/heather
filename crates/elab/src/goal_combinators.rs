//! Checking-only goal-tree combinators.
//!
//! `split_all; all_goals { body }` is elaborator sugar for an ordinary nested
//! match whose leaves are copies of `body`. The generated proof remains an
//! ordinary term and crosses the declaration's normal kernel gate.

use heather_kernel::rc::Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{Term, Type};
use heather_syntax::{Arm, Block, Expr, ExprKind, MatchForm, Pat, Span, Stmt};

use crate::oracle::Unfold;
use crate::{Cx, Elaborator};
use crate::inductive::Inductives;
use crate::name_lookup::NameLookup;

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
                name: name.to_string(),
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
    inductive.flat()
        && inductive.index.is_none()
        && inductive.ctors.len() > 1
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
pub(crate) fn conjunction(inductive: &crate::inductive::Inductive) -> bool {
    matches!(inductive.name.as_str(), "And" | "logic::And") && inductive.ctors.len() == 1 && inductive.ctors[0].fields.len() == 2
}

/// The inductive a type is, reading through `El`-headed spellings that only
/// unfold to their encoding.
pub(crate) fn type_inductive(elab: &Elaborator, cx: &Cx, ty: &Type) -> Option<Rc<crate::inductive::Inductive>> {
    elab.tag_of(ty).or_else(|| elab.tag_of(&elab.goal_oracle().diagnostics(64).decode_type(&cx.gamma, ty)?))
}

/// The word comparisons a split states a Nat fact for, each with its
/// `bitvec_omega` readings at `True` and `False`.
const COMPARISONS: [(&str, &str, &str); 2] = [
    ("bitvec::BitVec::unsigned_lt_bit", "unsigned_true", "unsigned_false"),
    ("bitvec::BitVec::eq_bit", "equal_true", "equal_false"),
];

/// A comparison's operands, with its entry in `COMPARISONS`.
fn comparison_args<'a>(elab: &Elaborator, term: &'a Term) -> Option<(&'static (&'static str, &'static str, &'static str), Vec<&'a Rc<Term>>)> {
    COMPARISONS.iter().find_map(|entry| Some((entry, crate::omega_cert::named_args(elab, term, entry.0)?)))
}

/// The comparison a scrutinee is, or becomes within a few transparent steps:
/// a helper such as `lowb(x) = x.unsigned_lt_bit(10)` is its comparison, and
/// so is `newline(b) = b.eq_bit(10)`.
fn comparison_of(elab: &Elaborator, cx: &Cx, scrut: &Term) -> Option<Rc<Term>> {
    let oracle = elab.goal_oracle();
    std::iter::once(scrut.clone())
        .chain(oracle.unfold(&cx.gamma, scrut, Unfold::Comparison))
        .find(|reduct| comparison_args(elab, reduct).is_some())
        .map(|comparison| Rc::new(settled(elab, cx, &comparison)))
}

/// A comparison with each projected operand read off the pair it projects: a
/// recursive definition unfolded at `Cons(b, rest)` reaches its head as a
/// projection of the constructor's encoding, which the goal's other side
/// spells `b`. Likewise an operand that is a match an earlier split decided
/// (`eq_bit(match False { False => x, True => y }, 1)` is `eq_bit(x, 1)`),
/// or the goal's other side, which reaches `eq_bit(x, 1)` directly, would
/// keep a comparison this split does not abstract. The split abstracts the
/// comparison as the source spells it.
fn settled(elab: &Elaborator, cx: &Cx, term: &Term) -> Term {
    let mut output = term.clone();
    if let Term::App { fun, arg, .. } | Term::AppAt { fun, arg } = &mut output {
        *fun = Rc::new(settled(elab, cx, fun));
        if crate::spelling::proj_of(arg).is_some()
            && let Ok(whnf) = elab.goal_oracle().bounded(64).whnf_term(&cx.gamma, arg)
            && crate::spelling::proj_of(&whnf).is_none()
        {
            *arg = Rc::new(whnf);
        } else if eliminator_headed(arg)
            && let Ok(selected) = elab.goal_oracle().bounded(64).whnf_term_opaque(&cx.gamma, arg)
            && !eliminator_headed(&selected)
        {
            *arg = Rc::new(selected);
        }
    }
    output
}

/// A `bitvec::BitVec` operation applied: the search's atoms.
fn word_operation(elab: &Elaborator, term: &Term) -> bool {
    let mut head = term;
    while let Some((fun, _)) = crate::spelling::app_of(head) {
        head = fun;
    }
    let Term::GlobalTm { var, .. } = head else { return false };
    elab.global_abs_of(*var)
        .and_then(|abs| NameLookup(elab).global_qualified_name_at(abs))
        .is_some_and(|name| name.starts_with("bitvec::BitVec::"))
}

/// The match at a reduct's head, below any projections of it, and through
/// the `refl` a convoy is applied to.
pub(crate) fn head_match(term: &Term) -> &Term {
    match crate::spelling::proj_of(term) {
        Some((_, pair)) => head_match(pair),
        None => match term {
            Term::AppAt { fun, arg } if matches!(&**fun, Term::Case { .. }) && matches!(&**arg, Term::Refl { .. }) => fun,
            _ => term,
        },
    }
}

/// A convoy on `scrut`: `match scrut as λ z => (scrut = z) → T { … }`
/// applied to `refl`, which `match h: scrut { … }` elaborates to.
fn convoy_on(term: &Term, scrut: &Term) -> bool {
    matches!(term, Term::AppAt { fun, arg }
        if matches!(&**fun, Term::Case { scrut: s, .. } if **s == *scrut)
            && matches!(&**arg, Term::Refl { tm, .. } if **tm == *scrut))
}

/// The subterms of a goal's sides that `found` picks, under none of their
/// binders: the positions a split abstracts.
fn picked(ty: &Type, found: &dyn Fn(&Term) -> bool) -> Vec<Term> {
    fn walk(term: &Term, found: &dyn Fn(&Term) -> bool, out: &mut Vec<Term>) {
        if found(term) {
            if !out.contains(term) {
                out.push(term.clone());
            }
            return;
        }
        match term {
            Term::App { fun, arg, .. } | Term::AppAt { fun, arg } => {
                walk(fun, found, out);
                walk(arg, found, out);
            }
            Term::Succ(inner) | Term::Inl { val: inner, .. } | Term::InlAt { val: inner, .. }
            | Term::Inr { val: inner, .. } | Term::InrAt { val: inner, .. } => walk(inner, found, out),
            Term::Pair { fst, snd, .. } | Term::PairAt { fst, snd, .. } => {
                walk(fst, found, out);
                walk(snd, found, out);
            }
            Term::Case { scrut: inner, .. } | Term::ElimNat { scrut: inner, .. } => walk(inner, found, out),
            _ => {
                if let Some((_, pair)) = crate::spelling::proj_of(term) {
                    walk(pair, found, out);
                }
            }
        }
    }
    let mut out = Vec::new();
    match ty {
        Type::Id { lhs, rhs, .. } => {
            walk(lhs, found, &mut out);
            walk(rhs, found, &mut out);
        }
        Type::El { tm, .. } => walk(tm, found, &mut out),
        _ => {}
    }
    out
}

/// `ty` with `scrut` abstracted as the motive's `z`, and each of `pairs`
/// planted. A convoy on `scrut` keeps everything but its scrutinee: its
/// motive, arms and `refl` are typed by `scrut` itself, so they keep it and
/// only the match moves to `z`. That leaves the `refl` at the wrong type,
/// which [`dependent_motive`] mends with the split's own equation; abstracted
/// whole, an arm that uses its equation would be handed one about `z`, and
/// the kernel refuses the split.
fn abstract_scrutinee(ty: &Type, scrut: &Term, pairs: &[(Term, Term)]) -> Option<Type> {
    let mut all: Vec<(Term, Term)> = picked(ty, &|term| convoy_on(term, scrut)).into_iter().filter_map(|convoy| {
        let Term::AppAt { fun, arg } = &convoy else { return None };
        // Weakened whole, so that the match's own binders stay bound; then
        // its scrutinee is `z`.
        let Term::Case { lhs_level, rhs_level, motive_level, lhs, rhs, motive, case_l, case_r, .. } = fun.shift_local(1) else { return None };
        let moved = Term::AppAt {
            fun: Rc::new(Term::Case {
                lhs_level, rhs_level, motive_level, lhs, rhs, motive, case_l, case_r,
                scrut: Rc::new(Term::Var(heather_kernel::term::LocalVar(0))),
            }),
            arg: Rc::new(arg.shift_local(1)),
        };
        Some((convoy, moved))
    }).collect();
    all.extend(pairs.iter().cloned());
    all.push((scrut.clone(), Term::Var(heather_kernel::term::LocalVar(0))));
    ty.abstract_local_with_all(&all)
}

/// A motive [`abstract_scrutinee`] left with convoys whose match is on `z`
/// and whose argument is still `refl` at the scrutinee: the same motive under
/// the split's equation `q : scrut = z` as a second binder, each such convoy
/// applied to `q`. In the branch where `z` is a constructor the convoy then
/// takes its arm with the case's equation, the type the arm was written at.
/// `None` when there is no such convoy and the ordinary motive is right.
fn dependent_motive(motive: &Type) -> Option<Type> {
    let z = |term: &Term| matches!(term, Term::Var(heather_kernel::term::LocalVar(0)));
    let convoys = picked(motive, &|term| matches!(term, Term::AppAt { fun, arg }
        if matches!(&**fun, Term::Case { scrut, .. } if z(scrut)) && matches!(&**arg, Term::Refl { tm, .. } if !z(tm))));
    if convoys.is_empty() {
        return None;
    }
    let pairs: Vec<(Term, Term)> = convoys.into_iter().filter_map(|convoy| {
        let Term::AppAt { fun, .. } = &convoy else { return None };
        let applied = Term::AppAt {
            fun: Rc::new(fun.shift_local(1)),
            arg: Rc::new(Term::Var(heather_kernel::term::LocalVar(0))),
        };
        Some((convoy, applied))
    }).collect();
    motive.abstract_local_with_all(&pairs)
}

/// `reduct` with a blocker found below it abstracted: its position becomes
/// the blocker's replacement, and every other occurrence of the scrutinee
/// becomes `z` as well. Replacing the position alone left the scrutinee
/// standing wherever else the reduct spells it — in the type arguments an
/// unfolded call carries (`or_bit<s.inside = False, …>(eq_dec(s.inside,
/// False))` once `decide_bit` unfolds) — so the motive's own subterms
/// disagreed about their types under `z`, and the kernel refused the split
/// that the motive's instance at the scrutinee had passed
/// (issues/split-all-nested-if-omega-kernel-refusal.md).
fn lifted(reduct: &Term, found: &Blocked) -> Option<Rc<Term>> {
    let pairs = [(found.original.clone(), (*found.replacement).clone())];
    Some(payload(abstract_scrutinee(&term_type(Rc::new(reduct.clone())), &found.scrutinee, &pairs)?))
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
    for reduct in std::iter::once(term.clone()).chain(oracle.unfold(&cx.gamma, term, Unfold::StuckScrutinee)) {
        if *budget == 0 {
            return None;
        }
        *budget -= 1;
        // A helper that is a comparison (`newline(b) = b.eq_bit(10)`) stops
        // at it, as the comparison itself does above: the match it heads is
        // the enclosing one's to split.
        if reduct != *term && word_operation(elab, &reduct) {
            return None;
        }
        let (scrut, domain) = match head_match(&reduct) {
            Term::Case { scrut, lhs, .. } => (scrut, case_domain(elab, cx, lhs)),
            Term::ElimNat { scrut, .. } => (scrut, None),
            // A call the definition unfolded to: what blocks it may be in
            // its arguments (`fold(step, rest, step(count, byte))`).
            _ if reduct != *term => {
                for arg in crate::spelling::app_spine(&reduct).1 {
                    if let Some(found) = stuck_scrutinee(elab, cx, arg, budget) {
                        let replacement = lifted(&reduct, &found)?;
                        return Some(Blocked { original: term.clone(), replacement, ..found });
                    }
                }
                continue;
            }
            _ => continue,
        };
        // Deeper first: a comparison whose operand is itself a stuck match
        // (`eq_bit(64, match c { … }, 1)`) is split after that match, so the
        // comparison is cased on at each operand it actually has. Cased on
        // first, the inner split would then decide it, leaving one of its
        // cases a goal no run reaches.
        if let Some(found) = stuck_scrutinee(elab, cx, scrut, budget) {
            return Some(Blocked { original: term.clone(), replacement: lifted(&reduct, &found)?, ..found });
        }
        if let Some(inductive) = &domain
            && let Some(comparison) = comparison_of(elab, cx, scrut)
        {
            return Some(Blocked {
                original: term.clone(),
                replacement: payload(abstract_scrutinee(&term_type(Rc::new(reduct.clone())), scrut, &[])?),
                scrutinee: comparison.clone(),
                constructors: constructors(inductive),
                comparison: Some(comparison),
            });
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
            replacement: payload(abstract_scrutinee(&term_type(Rc::new(reduct.clone())), scrut, &[])?),
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
pub(crate) fn co_occurrences(elab: &Elaborator, cx: &Cx, term: &Term, found: &Term, scrut: &Term, budget: &mut u32, out: &mut Vec<(Term, Term)>) {
    if *budget == 0 || term == found {
        return;
    }
    *budget -= 1;
    let spells = |t: &Term| abstract_scrutinee(&term_type(Rc::new(t.clone())), scrut, &[]).map(payload);
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
    for reduct in elab.goal_oracle().unfold(&cx.gamma, term, Unfold::StuckScrutinee) {
        if *budget == 0 {
            return;
        }
        *budget -= 1;
        // A definition's body part-way through its β-steps (`(λ h => match
        // c { … }(refl))(h)`) spells the scrutinee under a binder, where a
        // convoy on it cannot be moved apart from its `refl`: read the
        // reduct its arguments are all substituted into.
        if crate::spelling::is_app(&reduct) && matches!(crate::spelling::app_spine(&reduct).0, Term::Lam { .. }) {
            continue;
        }
        if let Some(abstracted) = spells(&reduct) {
            out.push((term.clone(), (*abstracted).clone()));
            return;
        }
    }
    // A recursive definition at a constructor reaches the comparison with
    // its operand spelled through the constructor's encoding (`settled`):
    // the search's own blocker for this position, when it is the same
    // comparison once settled.
    let mut search = 128;
    if let Some(blocked) = stuck_scrutinee(elab, cx, term, &mut search)
        && *blocked.scrutinee == *scrut
    {
        out.push((blocked.original, (*blocked.replacement).clone()));
    }
}

pub(crate) struct StuckSplit {
    pub scrut: Expr,
    pub equation: String,
    pub motive: Type,
    /// The motive under the case's equation as well, when a convoy in the
    /// goal needs it (`dependent_motive`).
    pub dependent: Option<Type>,
    pub arms: Vec<Arm>,
}

/// What a `split_all` leaf does with the goal in hand: close a case that
/// computation refutes, introduce a binder, prove a conjunction's two sides,
/// split the match blocking it, or hand it to the body.
pub(crate) enum Step {
    Refuted(Expr),
    Closed(Expr),
    Intro(Expr),
    Conjoin(Expr),
    Split(StuckSplit),
    Leaf(Type),
}

/// A split's case equation (`__split_case`, made unique by trailing `_`s):
/// not its fields (`__split_case_0_1_0`) or its Nat reading (`…_nat`).
fn case_equation(name: &str) -> bool {
    name.strip_prefix("__split_case").is_some_and(|rest| rest.bytes().all(|b| b == b'_'))
}

/// `absurd(h)` for the innermost enclosing case equation `h` whose two sides
/// compute to different constructors. A split is taken on what blocks the
/// goal *then*; a later split can decide an earlier one's scrutinee (or the
/// scrutinee was a closed comparison all along, `unsigned_lt_bit(64, 0, 0)`),
/// and the case it contradicts is then no case of the program at all — its
/// goal can be false (`1 = 0`), and a leaf handed it is handed a goal it
/// cannot prove. Closing the case here is what keeps every goal a leaf sees
/// one that some run reaches (issues/split-all-nested-scrutinee-kernel-reject.md).
fn refuted_case(elab: &Elaborator, cx: &Cx, span: Span) -> Option<Expr> {
    if elab.shadowed(cx, "absurd") || cx.names.iter_inner().any(|name| name == "absurd") {
        return None;
    }
    let var = |name: &str| Expr { kind: ExprKind::Var(name.into()), span };
    let name = cx
        .names
        .iter()
        .rev()
        .filter(|name| case_equation(name))
        .find(|name| Inductives(elab).refuted_by_computation(cx, &var(name)))?;
    Some(Expr {
        kind: ExprKind::App {
            head: Box::new(var("absurd")),
            args: vec![var(name)],
            named: vec![],
            explicit: false,
            goal_oriented: false,
        },
        span,
    })
}

/// A name no local and no global in scope has, from `base`.
pub(crate) fn fresh(elab: &Elaborator, cx: &Cx, base: String) -> String {
    let mut name = base;
    while elab.shadowed(cx, &name) || cx.names.iter_inner().any(|n| *n == name) {
        name.push('_');
    }
    name
}

pub(crate) fn next_step(elab: &Elaborator, cx: &Cx, expected: &Type, leaf: &Expr, span: Span) -> Step {
    if let Some(absurd) = refuted_case(elab, cx, span) {
        return Step::Refuted(absurd);
    }
    let var = |name: &str| Expr { kind: ExprKind::Var(name.into()), span };
    let whnf = elab.goal_oracle().bounded(256).whnf_type(&cx.gamma, expected);
    match whnf {
        // `(x: A) → B`: introduce `x`, and split it when `A` is finite.
        Ok(Type::Pi { dom, .. }) => {
            let name = fresh(elab, cx, format!("__split_all_x{}", cx.names.len()));
            let finite = type_inductive(elab, cx, &dom).filter(|inductive| finite_inductive(inductive));
            let body = match finite {
                Some(inductive) => {
                    let local = FiniteLocal { name: name.clone(), constructors: constructors(&inductive) };
                    tree(std::slice::from_ref(&local), &continuation(leaf, span), span, cx.names.len())
                }
                // A hypothesis an earlier split decided in part is restated
                // at its simplified type, as the goal is, so the leaf reads
                // it at the spelling it reads the goal (`runs_start(False,
                // False)` is `1`). The binder keeps the goal's own domain.
                None => match simplified_binder(elab, cx, &dom, &name) {
                    Some(ty) => Expr {
                        kind: ExprKind::Block(Box::new(Block {
                            stmts: vec![Stmt::Let { name: name.clone(), ty: Some(ty), expr: var(&name), span, opaque: true }],
                            result: Box::new(continuation(leaf, span)),
                            ons: vec![],
                            span,
                        })),
                        span,
                    },
                    None => continuation(leaf, span),
                },
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
        None => match closed_by_split(elab, cx, &goal, span) {
            Some(refl) => Step::Closed(refl),
            None => Step::Leaf(goal),
        },
    }
}

/// `refl` for a goal the splitting itself has proved: an equation whose two
/// sides the simplification made the same term. The leaf is written for the
/// cases still open, and need not prove the ones that closed: a function
/// that answers a value in some arms and recurs in others meets a leaf
/// written for its recursions (`all_goals { hg }`, a hypothesis stating
/// them) at its answers as `acc = acc`, which only `refl` proves. As with a
/// refuted case, such a goal is closed here and not handed on. The sides are
/// compared as terms, not converted: a goal that holds only by computation is
/// still the leaf's.
fn closed_by_split(elab: &Elaborator, cx: &Cx, goal: &Type, span: Span) -> Option<Expr> {
    match goal {
        Type::Id { lhs, rhs, .. } if lhs == rhs && !elab.shadowed(cx, "refl") && !cx.names.iter_inner().any(|name| name == "refl") => {
            Some(Expr { kind: ExprKind::Refl, span })
        }
        _ => None,
    }
}

/// Fail unless `ty`, a goal the splitter built, is convertible to `goal`, the
/// one it stands for: the splitter's own check of its output, at each node,
/// so that a defect in its abstraction or simplification is reported as one
/// rather than as the kernel's rejection of the declaration after `split_all`
/// claimed the split. A conversion that runs out of fuel is left to the
/// kernel, which has the declaration's own budget.
pub(crate) fn restates(elab: &Elaborator, cx: &Cx, ty: &Type, goal: &Type, level: &Level, what: &str, span: Span) -> crate::R<()> {
    if ty == goal {
        return Ok(());
    }
    match elab.goal_oracle().convert_type(&cx.gamma, heather_kernel::layer::Layer::Prog, ty, goal, level) {
        Err(heather_kernel::conv::ConvError::NotConvertible) => crate::err(
            format!(
                "internal error: `split_all`'s {what} `{}` is not the goal `{}` it stands for (please report this)",
                elab.display_type(cx, ty),
                elab.display_type(cx, goal),
            ),
            span,
        ),
        Ok(()) | Err(heather_kernel::conv::ConvError::OutOfFuel) => Ok(()),
    }
}

/// Fail unless `motive`, scoped in `Γ, z` with `z` of the scrutinee's type,
/// is a type there. [`restates`] checks the motive at the scrutinee; this
/// checks it at every `z`. A motive that abstracted the scrutinee at some of
/// its occurrences and not at others (a term at `z` where its annotation
/// still says the scrutinee) restates the goal at the scrutinee itself and
/// is still no type, which the kernel then reported as a refusal of the
/// whole declaration with no site (issues/split-all-nested-if-omega-kernel-
/// refusal.md). Out of fuel, the kernel decides.
#[allow(clippy::too_many_arguments)]
pub(crate) fn motive_is_a_type(elab: &Elaborator, cx: &Cx, motive: &Type, dependent: Option<&Type>, goal: &Type, scrut: &Term, ty: &Type, scrut_level: &Level, level: &Level, span: Span) -> crate::R<()> {
    let mut zcx = cx.clone();
    zcx.push("z".to_string(), ty.clone(), scrut_level.clone());
    // A motive with convoys is a type only under the case's equation
    // `q : scrut = z` as well (`dependent_motive`): the convoys' `refl`
    // is at the scrutinee, and `q` is what moves them to `z`.
    let motive = match dependent {
        Some(dependent) => {
            zcx.push(
                "q".to_string(),
                Type::Id {
                    level: scrut_level.clone(),
                    ty: Rc::new(ty.shift_local(1)),
                    lhs: Rc::new(scrut.shift_local(1)),
                    rhs: Rc::new(Term::Var(heather_kernel::term::LocalVar(0))),
                },
                scrut_level.clone(),
            );
            dependent
        }
        None => motive,
    };
    match elab.kernel_check_type(&elab.goal_psi(), heather_kernel::layer::Layer::Prog, &zcx.gamma, motive, level) {
        Ok(()) | Err(heather_kernel::typing::TypeError::OutOfFuel) => Ok(()),
        Err(_) => crate::err(
            format!(
                "internal error: `split_all`'s case split on `{}` abstracts it from the goal `{}` into a motive that is not a type: some occurrence of it was left in place (please report this)",
                elab.spell_term_source(cx, scrut).unwrap_or_else(|| "its scrutinee".to_string()),
                elab.display_type(cx, goal),
            ),
            span,
        ),
    }
}

/// A `refl` leaf, checked where it stands. Everywhere else `refl` is a note
/// for the gate, not a check; under `split_all` that let a leaf the split
/// left unprovable read as a finished split until the kernel rejected the
/// whole declaration. A leaf whose sides do not convert is reported here,
/// with the cases that led to it. Out of fuel, the kernel decides.
pub(crate) fn check_refl_leaf(elab: &Elaborator, cx: &Cx, leaf: &Expr, goal: &Type, span: Span) -> crate::R<()> {
    let mut leaf = leaf;
    while let ExprKind::Block(block) = &leaf.kind
        && block.stmts.is_empty()
    {
        leaf = &block.result;
    }
    if !matches!(leaf.kind, ExprKind::Refl) || elab.shadowed(cx, "refl") {
        return Ok(());
    }
    let Ok(Type::Id { level, ty, lhs, rhs }) = elab.goal_oracle().whnf_type(&cx.gamma, goal) else {
        return Ok(());
    };
    match elab.goal_oracle().convert_term(&cx.gamma, heather_kernel::layer::Layer::Prog, &lhs, &rhs, &ty, &level) {
        Err(heather_kernel::conv::ConvError::NotConvertible) => {
            let cases: Vec<String> = cx
                .names
                .iter()
                .filter(|name| case_equation(name))
                .filter_map(|name| {
                    let (_, ty, _) = elab.elab_infer(cx, &Expr { kind: ExprKind::Var(name.to_string()), span }).ok()?;
                    Some(format!("`{}`", elab.display_type(cx, &ty)))
                })
                .collect();
            let when = if cases.is_empty() { String::new() } else { format!(" in the case {}", cases.join(", ")) };
            crate::err(
                format!(
                    "`split_all` leaves the goal `{}`{when}, which `refl` does not prove: its sides are not definitionally equal",
                    elab.display_type(cx, goal),
                ),
                span,
            )
        }
        Ok(()) | Err(heather_kernel::conv::ConvError::OutOfFuel) => Ok(()),
    }
}

/// A binder's type after the simplification the goal gets, spelled for an
/// annotation, when it differs and the source can spell it.
fn simplified_binder(elab: &Elaborator, cx: &Cx, dom: &Type, name: &str) -> Option<heather_syntax::ast::Ty> {
    let decoded = crate::inductive::decoded(dom);
    let simplified = simplify_goal(elab, cx, &decoded);
    if simplified == *decoded {
        return None;
    }
    let spelled = elab.spell_type_source(cx, &simplified)?;
    let ExprKind::Lam { mut binders, .. } = crate::omega_cert::parse_generated_expr(&format!("λ ({name}: {spelled}) => {name}")).ok()?.kind else {
        return None;
    };
    binders.pop()?.ty
}

/// The steps a match's scrutinee may take to reach its constructor: a
/// comparison of two closed words (`ofNat(0).eq_bit(ofNat(1))`, what a flag
/// read back from a written constant leaves, its literal perhaps still a
/// field of the node that wrote it) is decided by running it over the
/// width's bits, which a split's small budget does not reach; anything else
/// gets that small budget.
fn closed_comparison_steps(elab: &Elaborator, scrut: &Term) -> u64 {
    let closed = |t: &Rc<Term>| heather_kernel::subst::local_bound(t) == 0;
    let decided = crate::omega_cert::named_args(elab, scrut, "bitvec::BitVec::eq_bit")
        .is_some_and(|args| matches!(args.as_slice(), [width, a, b] if closed(width) && closed(a) && closed(b)));
    if decided { 1 << 18 } else { 64 }
}

/// A closed word literal's value, `ofNat(w, k)` with both literal and
/// `k < 2^w`, so its `toNat` is `k` by computation.
fn literal_word(elab: &Elaborator, term: &Term) -> Option<u64> {
    fn nat(term: &Term) -> Option<u64> {
        match term {
            Term::Zero => Some(0),
            Term::NatLit(value) => value.as_u64(),
            Term::Succ(inner) => nat(inner)?.checked_add(1),
            _ => None,
        }
    }
    let args = crate::omega_cert::named_args(elab, term, "bitvec::BitVec::ofNat")?;
    let [width, value] = args.as_slice() else { return None };
    let (width, value) = (nat(width)?, nat(value)?);
    (width == 64 || (width < 64 && value < (1u64 << width))).then_some(value)
}

/// A call of a definition whose body matches on an argument that is now a
/// constructor (`split_at(False, x, ps)`, or `Bool::and(False, b)` once a
/// split decided its operand): the arm the match selects, when the source can
/// spell it. Anything else stays a call: a library call such as `words(xs)`
/// unfolds to no match that selects an arm, and a recursive definition
/// selects one whose recursive calls are the raw recursor, which no source
/// spells (issues/split-all-through-recursive-definitions.md owns that case).
fn matched_at_constructor(elab: &Elaborator, cx: &Cx, call: &Term, simp: bool) -> Option<Term> {
    let (head, _) = crate::spelling::app_spine(call);
    if !matches!(head, Term::GlobalTm { .. }) || word_operation(elab, call) {
        return None;
    }
    let oracle = elab.goal_oracle();
    for reduct in oracle.unfold(&cx.gamma, call, Unfold::MatchedArm) {
        if !eliminator_headed(&reduct) {
            continue;
        }
        // The definition's match: it selects an arm only at a constructor,
        // and the arm is taken only when it is a value the source spells,
        // with no match left at its head. A match still stuck on a neutral
        // leaves the call as written.
        let selected = oracle.bounded(64).whnf_term_opaque(&cx.gamma, &reduct).ok()?;
        if selected == reduct || eliminator_headed(&selected) {
            return None;
        }
        // The arm's reads of the matched constructor's children are the
        // pattern's names where the goal has them (`rest`, not `fst(cs)`).
        if elab.spell_term_source(cx, &selected).is_some() {
            return Some(selected);
        }
        // An arm that reads the constructor's fields (`node_output(Const(64,
        // flag, 1))` is `Output(64, flag)`) reads them as projections out of
        // its label's payload, which no source spells: contracted, they are
        // the fields written. Only for `simp`, and only where the arm as
        // selected did not spell: either contraction elsewhere changes what
        // `omega` reads (`CReal::archimedean`'s `Rat` sum).
        if !simp {
            return None;
        }
        let contracted = contracted(elab, cx, &oracle, &selected, &mut 256);
        elab.spell_term_source(cx, &contracted)?;
        return Some(contracted);
    }
    None
}

/// A call of a structurally recursive definition at a constructor
/// (`simp(Seq(a, b))`): the arm its match selects, with the recursive calls
/// spelled as calls of the definition (`seq(simp(a), simp(b))`), which the
/// reduct walk's refolded firing gives and the kernel's own ι-step does not
/// (issues/split-all-through-recursive-definitions.md). `None` when the arm
/// is itself stuck on a match, or the source cannot spell it.
fn recursion_at_constructor(elab: &Elaborator, cx: &Cx, call: &Term) -> Option<Term> {
    let (head, _) = crate::spelling::app_spine(call);
    if !matches!(head, Term::GlobalTm { .. }) || word_operation(elab, call) {
        return None;
    }
    let oracle = elab.goal_oracle();
    let mut fired = false;
    for reduct in oracle.unfold(&cx.gamma, call, Unfold::RecursiveArm) {
        // A `decreases` function (`f` over `f#rec`) is stepped by its
        // generated equations (`f::step`, `f::done`), which are laws: run at
        // a closed count, its arm is `f#body(…)`, a lifted body no source
        // spells and no law about `f` meets again.
        if let Term::GlobalTm { var, .. } = crate::spelling::app_spine(&reduct).0
            && elab.global_abs_of(*var).and_then(|abs| elab.global_name_at(abs)).is_some_and(|name| name.ends_with("#rec"))
        {
            return None;
        }
        if eliminator_headed(&reduct) {
            // The recursion firing on a constructor selects an arm. Its
            // reduct may itself be the recursion, as a tail call on an
            // accumulator is (`foldl`'s arm is `t.foldl(f, f(z, a))`), so
            // that is read off the eliminator and not off the whnf.
            let fires = matches!(crate::spelling::app_spine(&reduct).0, Term::ElimWf { scrut, .. } if matches!(&**scrut, Term::Supf { .. }));
            if !fired && !fires {
                // The kernel's own answer says whether an arm is selected
                // at all: a match stuck on a neutral leaves the call.
                let selected = oracle.bounded(512).whnf_term_opaque(&cx.gamma, &reduct).ok()?;
                if selected == reduct || eliminator_headed(&selected) {
                    return None;
                }
            }
            fired = true;
            continue;
        }
        if !fired {
            continue;
        }
        if matches!(crate::spelling::app_spine(&reduct).0, Term::Lam { .. }) {
            continue;
        }
        let arm = contracted(elab, cx, &oracle, &reduct, &mut 256);
        elab.spell_term_source(cx, &arm)?;
        return Some(arm);
    }
    None
}

/// A call of a definition named for unfolding: its body at the call's
/// arguments, with the β-redexes that leaves contracted and no other
/// definition unfolded. `None` for any other head, or when the source
/// cannot spell the result.
fn unfolded_by_name(elab: &Elaborator, cx: &Cx, call: &Term, unfold: &[usize]) -> Option<Term> {
    if unfold.is_empty() {
        return None;
    }
    let Term::GlobalTm { var, .. } = crate::spelling::app_spine(call).0 else {
        return None;
    };
    if !unfold.contains(&elab.global_abs_of(*var)?) {
        return None;
    }
    let oracle = elab.goal_oracle();
    let unfolded = oracle.unfold(&cx.gamma, call, Unfold::OneStep).next()?;
    let body = contracted(elab, cx, &oracle, &unfolded, &mut 256);
    // A body that is a match on what its arguments do not decide yet
    // (`Tm::leave` matching on `after(64, flag).eq_bit(1)`) has no
    // surface spelling, but its scrutinee does, and that is what the other
    // laws rewrite until the match selects its arm. A recursive
    // definition's body is the recursor, never a `Case`, so this admits no
    // raw recursion.
    if elab.spell_term_source(cx, &body).is_none() {
        let Term::Case { scrut, .. } = &body else {
            return None;
        };
        elab.spell_term_source(cx, scrut)?;
    }
    Some(body)
}

/// `t` with every β-redex `(λ x. b)(a)` contracted, under binders too, and
/// nothing else reduced.
pub(crate) fn beta_below(t: &Term) -> Term {
    match t {
        Term::App { fun, arg, .. } | Term::AppAt { fun, arg } => {
            let fun = beta_below(fun);
            let arg = beta_below(arg);
            if let Term::Lam { body, .. } = &fun {
                return beta_below(&body.inst_top(0, &arg));
            }
            let mut out = t.clone();
            if let Term::App { fun: f, arg: a, .. } | Term::AppAt { fun: f, arg: a } = &mut out {
                *f = Rc::new(fun);
                *a = Rc::new(arg);
            }
            out
        }
        Term::Lam { .. } => {
            let mut out = t.clone();
            if let Term::Lam { body, .. } = &mut out {
                *body = Rc::new(beta_below(body));
            }
            out
        }
        _ => t.clone(),
    }
}

/// `t` with the β-redexes and projections of pairs a selected arm leaves
/// below its head contracted (`(λ i. g(nth(cs; i)))(0)` is `g(a)`), and no
/// definition unfolded.
fn contracted(elab: &Elaborator, cx: &Cx, oracle: &crate::oracle::SemanticOracle, t: &Term, budget: &mut u32) -> Term {
    let gamma = &cx.gamma;
    if *budget == 0 {
        return t.clone();
    }
    *budget -= 1;
    let reduced = match t {
        Term::App { .. } | Term::AppAt { .. }
            if !matches!(crate::spelling::app_spine(t).0, Term::GlobalTm { .. } | Term::Var(_)) =>
        {
            oracle.bounded(64).whnf_term_opaque(gamma, t).ok()
        }
        Term::Fst { .. } | Term::FstAt { .. } | Term::Snd { .. } | Term::SndAt { .. } | Term::Case { .. } | Term::ElimNat { .. } => {
            oracle.bounded(64).whnf_term_opaque(gamma, t).ok()
        }
        _ => None,
    };
    if let Some(reduced) = reduced
        && reduced != *t
    {
        return contracted(elab, cx, oracle, &reduced, budget);
    }
    // The child a refolded hypothesis reads, `nth(cs; i)`: a recursion on
    // the constructor's arity, which only δ computes. Taken when it reaches
    // a child, and left when it is a match of the arm's own.
    if eliminator_headed(t)
        && let Ok(reduced) = oracle.bounded(64).whnf_term(gamma, t)
        && !eliminator_headed(&reduced)
    {
        return pattern_name(elab, cx, &reduced).unwrap_or(reduced);
    }
    // A child the definition's own arm read directly (`Star(s)` rebuilt).
    if matches!(t, Term::Fst { .. } | Term::FstAt { .. })
        && let Some(named) = pattern_name(elab, cx, t)
    {
        return named;
    }
    let mut output = t.clone();
    match &mut output {
        Term::App { fun, arg, .. } | Term::AppAt { fun, arg } => {
            *fun = Rc::new(contracted(elab, cx, oracle, fun, budget));
            *arg = Rc::new(contracted(elab, cx, oracle, arg, budget));
        }
        Term::Succ(inner) => *inner = Rc::new(contracted(elab, cx, oracle, inner, budget)),
        Term::Pair { fst, snd, .. } | Term::PairAt { fst, snd, .. } => {
            *fst = Rc::new(contracted(elab, cx, oracle, fst, budget));
            *snd = Rc::new(contracted(elab, cx, oracle, snd, budget));
        }
        Term::Inl { val, .. } | Term::InlAt { val, .. } | Term::Inr { val, .. } | Term::InrAt { val, .. } => {
            *val = Rc::new(contracted(elab, cx, oracle, val, budget));
        }
        // A constructor's fields ride in its label's payload, its recursive
        // children in the tuple: both are read where the arm put them.
        Term::Supf { label, children, .. } => {
            *label = Rc::new(contracted(elab, cx, oracle, label, budget));
            *children = Rc::new(contracted(elab, cx, oracle, children, budget));
        }
        // A match left stuck (a body's `match` on what its arguments do not
        // decide, `let after = step(…)` read in its scrutinee): its
        // scrutinee, which is where it is scoped; the arms are below their
        // binders.
        Term::Case { scrut, .. } => *scrut = Rc::new(contracted(elab, cx, oracle, scrut, budget)),
        _ => {}
    }
    output
}

/// The pattern variable of `cx` that is `child`: a pattern's variable is
/// an alias of the scrutinee's child under its own spelling (the match's
/// `nth`, over the declared type), so an arm computed another way reads as
/// the pattern's names only where a child is replaced by the alias that
/// converts with it.
fn pattern_name(elab: &Elaborator, cx: &Cx, child: &Term) -> Option<Term> {
    cx.aliases.iter().rev().find_map(|alias| {
        let by = cx.gamma.len().checked_sub(alias.depth)? as u32;
        (eliminator_headed(&alias.term) && crate::rewrite::Rewrites(elab).terms_convert(cx, &alias.at(by).0, child))
            .then(|| alias.splice(by).0)
    })
}

/// A term whose head, below applications and projections, is an
/// eliminator: a match, a recursor, or `J`.
fn eliminator_headed(term: &Term) -> bool {
    let mut head = head_match(term);
    while let Some((fun, _)) = crate::spelling::app_of(head) {
        head = head_match(fun);
    }
    matches!(
        head,
        Term::Case { .. } | Term::ElimNat { .. } | Term::ElimW { .. } | Term::ElimWf { .. } | Term::J { .. }
            | Term::ElimEmpty { .. } | Term::ElimSEmpty { .. } | Term::ElimSquash { .. }
            | Term::ElimCodeTy { .. } | Term::ElimCodeTm { .. }
    )
}

/// Compute the constructor cases left by a previous split, including below
/// applications, while keeping library calls spelled as library calls.
pub(crate) fn simplify_goal(elab: &Elaborator, cx: &Cx, expected: &Type) -> Type {
    simplify_goal_with(elab, cx, expected, false)
}

/// [`simplify_goal`], and with `recursive` a structurally recursive
/// definition at a constructor computes too, its recursive calls spelled as
/// calls ([`recursion_at_constructor`]): what `simp_only` matches laws
/// against.
pub(crate) fn simplify_goal_with(elab: &Elaborator, cx: &Cx, expected: &Type, recursive: bool) -> Type {
    simplify_goal_unfolding(elab, cx, expected, recursive, &[], &[])
}

/// [`simplify_goal_with`], and every call of a definition in `unfold` (by
/// absolute position in Ψ) unfolded where it stands, its body applied to the
/// call's arguments: what `simp_only` does with a definition named among
/// its laws (docs/tactics/simp-design.md §14).
///
/// A term in `frozen` stays as written: a law's own term (`zeroed(R, 0,
/// 64).hash`'s `R`, a call whose body computes), which the law could no
/// longer meet once computed.
pub(crate) fn simplify_goal_unfolding(elab: &Elaborator, cx: &Cx, expected: &Type, recursive: bool, unfold: &[usize], frozen: &[Rc<Term>]) -> Type {
    fn term(elab: &Elaborator, cx: &Cx, input: &Term, budget: &mut (u32, bool, &[usize], &[Rc<Term>])) -> Term {
        if budget.0 == 0 {
            return input.clone();
        }
        budget.0 -= 1;
        if budget.3.iter().any(|f| **f == *input) {
            return input.clone();
        }
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
                if let Some(reduced) = matched_at_constructor(elab, cx, &output, budget.1) {
                    return term(elab, cx, &reduced, budget);
                }
                if budget.1
                    && let Some(reduced) = recursion_at_constructor(elab, cx, &output)
                {
                    return term(elab, cx, &reduced, budget);
                }
                if let Some(reduced) = unfolded_by_name(elab, cx, &output, budget.2) {
                    return term(elab, cx, &reduced, budget);
                }
            }
            Term::GlobalTm { .. } => {
                if let Some(reduced) = unfolded_by_name(elab, cx, &output, budget.2) {
                    return term(elab, cx, &reduced, budget);
                }
            }
            // A function literal a law's instance put a function literal
            // into (`λ ys => out(again(ys))` at `again := λ ys => into(…)`),
            // or a node's value read at its literal (`λ w => ofNat(fst(…))`):
            // its β-redexes and projections of pairs contracted, so a law
            // under the binder meets the body as written. Syntactic only:
            // nothing below a binder is scoped where the oracle is.
            Term::Lam { body, .. } if budget.1 => *body = crate::spelling::contract_projections(&Rc::new(beta_below(body))),
            Term::Succ(inner) => *inner = Rc::new(term(elab, cx, inner, budget)),
            // An equation's code, as a conjunction's operand holds it
            // (`And<block(…) = T ++ …, ….hash = s.hash>`), for `simp`: its
            // two sides compute as a goal's do.
            Term::TmId { lhs, rhs, .. } if budget.1 => {
                *lhs = Rc::new(term(elab, cx, lhs, budget));
                *rhs = Rc::new(term(elab, cx, rhs, budget));
            }
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
                    && (!budget.1 || elab.spell_term_source(cx, &reduced).is_some())
                {
                    return term(elab, cx, &reduced, budget);
                }
                if let Term::Fst { pair, .. } | Term::FstAt { pair } | Term::Snd { pair, .. } | Term::SndAt { pair } = &mut output {
                    // A field of a definition that unfolds to a constructor
                    // (`counting(g)(s, b).next` is `Filtered(g(s, b), None).next`):
                    // unfold the receiver as far as the constructor, and no
                    // further, so the field reads as what was put there.
                    if let Ok(unfolded) = elab.goal_oracle().bounded(64).whnf_term(&cx.gamma, pair)
                        && matches!(unfolded, Term::Pair { .. } | Term::PairAt { .. })
                    {
                        let kept = std::mem::replace(pair, Rc::new(unfolded));
                        // For `simp`, only a field the source can spell: a
                        // definition whose constructor is reached by running
                        // its body reads otherwise as raw projections, where
                        // no law meets it again; the call stays.
                        match elab.goal_oracle().bounded(64).whnf_term_opaque(&cx.gamma, &output) {
                            Ok(reduced) if reduced != *input && (!budget.1 || elab.spell_term_source(cx, &reduced).is_some()) => {
                                return term(elab, cx, &reduced, budget);
                            }
                            _ if budget.1 => {
                                if let Term::Fst { pair, .. } | Term::FstAt { pair } | Term::Snd { pair, .. } | Term::SndAt { pair } = &mut output {
                                    *pair = kept;
                                }
                            }
                            _ => {}
                        }
                    }
                    if let Term::Fst { pair, .. } | Term::FstAt { pair } | Term::Snd { pair, .. } | Term::SndAt { pair } = &mut output {
                        *pair = Rc::new(term(elab, cx, pair, budget));
                    }
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
                // A scrutinee a split decided only in part (`!b && c` once
                // `b` is known): simplify it, so the match selects its arm or
                // stays stuck on what the next split decides.
                if let Term::Case { scrut, .. } | Term::ElimNat { scrut, .. } = &mut output {
                    let simplified = term(elab, cx, scrut, budget);
                    if simplified != **scrut {
                        *scrut = Rc::new(simplified);
                        if let Ok(reduced) = elab.goal_oracle().bounded(64).whnf_term_opaque(&cx.gamma, &output)
                            && reduced != output
                        {
                            return term(elab, cx, &reduced, budget);
                        }
                    }
                }
                // A scrutinee a split decided through a definition: an
                // `if` on `i = False` matches on `decide_bit`'s bit, which
                // is `or_bit(eq_dec(i, False))` and stays a call once `i` is
                // a constructor, because its value (`Inl(refl)`) is evidence
                // no source spells. It computes to a constructor all the
                // same, and the match takes that arm: the arm is the goal's,
                // the scrutinee's value is not
                // (issues/split-all-nested-if-omega-kernel-refusal.md).
                if let Term::Case { scrut, .. } = &mut output
                    && let Ok(whnf) = elab.goal_oracle().bounded(closed_comparison_steps(elab, scrut)).whnf_term(&cx.gamma, scrut)
                    && crate::spelling::is_inj(&whnf)
                {
                    *scrut = Rc::new(whnf);
                    if let Ok(reduced) = elab.goal_oracle().bounded(64).whnf_term_opaque(&cx.gamma, &output)
                        && reduced != output
                    {
                        return term(elab, cx, &reduced, budget);
                    }
                }
                // A match that stays stuck, for `simp`: an arm that ignores
                // its constructor's payload (a `Bool` match's) is a term
                // where the match is, computed there, so the laws meet its
                // calls as they meet the scrutinee's.
                if budget.1
                    && let Term::Case { case_l, case_r, .. } = &mut output
                {
                    for arm in [case_l, case_r] {
                        // Below the arm's own binder: lowered past it when
                        // nothing reads it.
                        let outer = arm.inst_top(0, &Term::Zero);
                        if outer.shift_local(1) == **arm {
                            let computed = term(elab, cx, &outer, budget);
                            if computed != outer {
                                *arm = Rc::new(computed.shift_local(1));
                            }
                        }
                    }
                }
            }
            _ => {}
        }
        output
    }
    fn walk(elab: &Elaborator, cx: &Cx, ty: &Type, budget: &mut (u32, bool, &[usize], &[Rc<Term>])) -> Type {
        let mut output = ty.clone();
        match &mut output {
            Type::Id { lhs, rhs, .. } => {
                *lhs = Rc::new(term(elab, cx, lhs, budget));
                *rhs = Rc::new(term(elab, cx, rhs, budget));
            }
            // A relation (`Le(a, b)`) keeps its own spelling for the leaf: only
            // its arguments are simplified, never the relation's head, which
            // computes away at literals (`0 <= 1` is `True`).
            Type::El { tm, .. } => *tm = Rc::new(arguments(elab, cx, tm, budget)),
            // A conjunction, as a record decodes (`And<a = b, c = d>` is a
            // Σ of the two), for `simp`: each operand that its second does
            // not depend on, below the binder when nothing reads it.
            Type::Sigma { fst, snd, .. } if budget.1 => {
                *fst = Rc::new(walk(elab, cx, fst, budget));
                let outer = snd.inst_top(0, &Term::Zero);
                if outer.shift_local(1) == **snd {
                    let walked = walk(elab, cx, &outer, budget);
                    if walked != outer {
                        *snd = Rc::new(walked.shift_local(1));
                    }
                }
            }
            _ => {}
        }
        output
    }
    let mut budget = (512, recursive, unfold, frozen);
    let output = walk(elab, cx, expected, &mut budget);
    // A goal that is not an application (a match on a split comparison)
    // simplifies whole.
    fn arguments(elab: &Elaborator, cx: &Cx, input: &Term, budget: &mut (u32, bool, &[usize], &[Rc<Term>])) -> Term {
        let mut output = input.clone();
        match &mut output {
            Term::App { fun, arg, .. } | Term::AppAt { fun, arg } => {
                *fun = Rc::new(arguments(elab, cx, fun, budget));
                *arg = Rc::new(term(elab, cx, arg, budget));
                output
            }
            _ => term(elab, cx, input, budget),
        }
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
    let scrut = crate::omega_cert::parse_generated_expr(&source).ok()?;
    let motive = abstract_scrutinee(expected, &found.scrutinee, &pairs)?;
    let dependent = dependent_motive(&motive);
    let equation = fresh(elab, cx, "__split_case".to_string());
    let order = fresh(elab, cx, format!("{equation}_nat"));
    // The comparison's operands, when the bridge library is there to read
    // them as Nats.
    let compared = found.comparison.as_ref().and_then(|comparison| comparison_args(elab, comparison));
    let readings = compared.as_ref().map(|(entry, _)| (entry.1, entry.2));
    let equality = readings.is_some_and(|(yes, _)| yes == "equal_true");
    let operands = compared
        .as_ref()
        .filter(|(entry, _)| elab.key_of(&format!("bitvec_omega::{}", entry.1)).is_some())
        .and_then(|(_, args)| args.iter().map(|term| elab.spell_term_source(cx, term)).collect::<Option<Vec<_>>>())
        .map(|operands| operands.join(", "));
    // Each word operand as the Nat the fact is stated at: a literal
    // (`ofNat(8, 14)` is `14`) as its value, so that `omega`, which reads
    // `toNat(ofNat(14))` as an unknown, can compare two splits' constants.
    let sides = compared
        .as_ref()
        .map(|(_, args)| args)
        .filter(|args| args.len() == 3)
        .and_then(|args| {
            let side = |term: &Term| match literal_word(elab, term) {
                Some(value) => Some(value.to_string()),
                None => Some(format!("({}).toNat()", elab.spell_term_source(cx, term)?)),
            };
            let literal = literal_word(elab, args[1]).is_some() || literal_word(elab, args[2]).is_some();
            literal.then(|| Some((side(args[1])?, side(args[2])?))).flatten()
        });
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
            let stated = |fact: String| match (&sides, outcome, equality) {
                (Some((left, right)), Some("true"), false) => format!("{{ let __split_fact: ({left} < {right}) = {fact}; __split_fact }}"),
                (Some((left, right)), Some(_), false) => format!("{{ let __split_fact: ({right} <= {left}) = {fact}; __split_fact }}"),
                (Some((left, right)), Some("true"), true) => format!("{{ let __split_fact: ({left} = {right}) = {fact}; __split_fact }}"),
                (Some((left, right)), Some(_), true) => format!("{{ let __split_fact: ({left} ≠ {right}) = {fact}; __split_fact }}"),
                _ => fact,
            };
            let reading = readings.zip(outcome).map(|((yes, no), outcome)| if outcome == "true" { yes } else { no });
            if let (Some(operands), Some(reading)) = (&operands, reading)
                && let Ok(expr) = crate::omega_cert::parse_generated_expr(&stated(format!(
                    "bitvec_omega::{reading}({operands}, {equation})"
                )))
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
        dependent,
        arms,
    })
}
