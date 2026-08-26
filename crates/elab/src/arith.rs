//! Certifying arithmetic reconstruction.
//!
//! This is deliberately an elaborator component, not a kernel decision
//! procedure.  It reads a small fragment of an already elaborated goal,
//! constructs an ordinary Heather proof expression from the public `Nat`
//! lemma kit, and hands that expression back to ordinary elaboration.  A bug
//! here can therefore make `arith` fail, but cannot make a false theorem pass.
//!
//! The first fragment is additive equality over `Nat`: opaque atoms, `+`, and
//! `twice`.  Opaque really means opaque — `pow(2, n)` is one atom rather than
//! an invitation to reduce a closed power.  Both sides are flattened, the
//! atoms are compared as elaborated kernel terms, and an AC permutation proof
//! is reconstructed from `add_assoc`, `add_comm`, `cong_nat`, `twice_add`,
//! and, when coefficient expansion is required, `twice_add_self`.

use std::fmt;
use std::rc::Rc;

use heather_kernel::term::{LocalSubst, Term, Type};
use heather_syntax::{Arm, Expr, ExprKind, Item, MatchForm, Span, parse_file};

use crate::{Cx, Elaborator};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArithReport {
    pub atoms: usize,
    pub adjacent_swaps: usize,
    pub boolean_splits: usize,
    pub branches: usize,
    pub used_lemmas: Vec<&'static str>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ArithFailureKind {
    UnsupportedGoal,
    UnsupportedTerm,
    UnequalNormalForms,
    Reconstruction,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArithFailure {
    pub kind: ArithFailureKind,
    pub goal: String,
    pub normalized_lhs: Option<String>,
    pub normalized_rhs: Option<String>,
    pub detail: String,
}

impl fmt::Display for ArithFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "`arith` got stuck ({:?})\n  goal: {}", self.kind, self.goal)?;
        if let (Some(lhs), Some(rhs)) = (&self.normalized_lhs, &self.normalized_rhs) {
            write!(f, "\n  normalized lhs: {lhs}\n  normalized rhs: {rhs}")?;
        }
        write!(f, "\n  detail: {}", self.detail)
    }
}

pub(crate) struct Certificate {
    pub expr: Expr,
    pub report: ArithReport,
}

pub(crate) struct BooleanCertificate {
    pub expr: Expr,
    pub splits: usize,
}

/// This string cannot be produced by Heather's lexer. It marks leaves in an
/// elaborator-generated match tree without adding a surface AST form or a
/// user-spellable pseudo-declaration.
pub(crate) const BOOLEAN_LEAF: &str = "\0arith-boolean-leaf";

#[derive(Clone, PartialEq, Eq)]
enum AtomKey {
    Core(Rc<Term>),
    Twice(Box<AtomKey>),
}

#[derive(Clone)]
struct Atom {
    key: AtomKey,
    source: String,
}

impl Atom {
    fn same(&self, other: &Atom) -> bool {
        self.key == other.key
    }
}

#[derive(Clone)]
enum AddExpr {
    Atom(Atom),
    Add(Box<AddExpr>, Box<AddExpr>),
    Twice(Box<AddExpr>),
}

impl AddExpr {
    fn source(&self) -> String {
        match self {
            Self::Atom(a) => a.source.clone(),
            Self::Add(a, b) => format!("({} + {})", a.source(), b.source()),
            Self::Twice(a) => format!("nat::twice({})", a.source()),
        }
    }
}

struct Normalized {
    atoms: Vec<Atom>,
    source: String,
    proof: String,
}

#[derive(Clone, Copy)]
enum TwiceMode {
    Grouped,
    Expanded,
}

struct Build {
    twice_mode: TwiceMode,
    adjacent_swaps: usize,
    used_lemmas: Vec<&'static str>,
}

impl Build {
    fn new(twice_mode: TwiceMode) -> Self {
        Self { twice_mode, adjacent_swaps: 0, used_lemmas: Vec::new() }
    }

    fn used(&mut self, lemma: &'static str) {
        if !self.used_lemmas.contains(&lemma) {
            self.used_lemmas.push(lemma);
        }
    }

    fn normalize(&mut self, e: &AddExpr) -> Normalized {
        match e {
            AddExpr::Atom(a) => Normalized {
                atoms: vec![a.clone()],
                source: a.source.clone(),
                proof: "refl".to_string(),
            },
            AddExpr::Add(a, b) => self.normalize_add(a, b),
            AddExpr::Twice(a) if matches!(self.twice_mode, TwiceMode::Expanded) => {
                self.used("nat::twice_add_self");
                let expanded = self.normalize_add(a, a);
                let original = format!("nat::twice({})", a.source());
                let doubled = format!("({} + {})", a.source(), a.source());
                Normalized {
                    atoms: expanded.atoms,
                    source: expanded.source.clone(),
                    proof: trans_eq(
                        &original,
                        &doubled,
                        &expanded.source,
                        format!("nat::twice_add_self({})", a.source()),
                        expanded.proof,
                    ),
                }
            }
            AddExpr::Twice(a) => {
                let inner = self.normalize(a);
                let original_inner = a.source();
                let original = format!("nat::twice({original_inner})");
                let normalized_twice = format!("nat::twice({})", inner.source);
                let lifted = if inner.proof == "refl" {
                    "refl".to_string()
                } else {
                    self.used("nat::cong_nat");
                    cong(
                        "fun (q: Nat) => nat::twice(q)".to_string(),
                        &original_inner,
                        &inner.source,
                        inner.proof,
                    )
                };
                let distributed = self.distribute_twice(&inner.atoms);
                let atoms: Vec<Atom> = inner
                    .atoms
                    .into_iter()
                    .map(|a| Atom {
                        key: AtomKey::Twice(Box::new(a.key)),
                        source: format!("nat::twice({})", a.source),
                    })
                    .collect();
                let source = sum(&atoms);
                Normalized {
                    atoms,
                    source: source.clone(),
                    proof: trans_eq(
                        &original,
                        &normalized_twice,
                        &source,
                        lifted,
                        distributed,
                    ),
                }
            }
        }
    }

    /// `twice(sum xs) = sum(map twice xs)`.
    fn distribute_twice(&mut self, atoms: &[Atom]) -> String {
        debug_assert!(!atoms.is_empty());
        if atoms.len() == 1 {
            return "refl".to_string();
        }
        self.used("nat::twice_add");
        let head = &atoms[0].source;
        let tail = sum(&atoms[1..]);
        let first = format!("(nat::twice({head}) + nat::twice({tail}))");
        let rest = self.distribute_twice(&atoms[1..]);
        let wrapped_tail: Vec<Atom> = atoms[1..]
            .iter()
            .cloned()
            .map(|a| Atom {
                key: AtomKey::Twice(Box::new(a.key)),
                source: format!("nat::twice({})", a.source),
            })
            .collect();
        let target = format!("(nat::twice({head}) + {})", sum(&wrapped_tail));
        let second = if rest == "refl" {
            rest
        } else {
            self.used("nat::cong_nat");
            cong(
                format!("fun (q: Nat) => nat::twice({head}) + q"),
                &format!("nat::twice({tail})"),
                &sum(&wrapped_tail),
                rest,
            )
        };
        trans_eq(
            &format!("nat::twice({head} + {tail})"),
            &first,
            &target,
            format!("nat::twice_add({head}, {tail})"),
            second,
        )
    }

    fn normalize_add(&mut self, a: &AddExpr, b: &AddExpr) -> Normalized {
        let na = self.normalize(a);
        let nb = self.normalize(b);
        let original_a = a.source();
        let original_b = b.source();
        let children = self.cong_add(
            &original_a,
            &na.source,
            &original_b,
            &nb.source,
            na.proof,
            nb.proof,
        );
        let joined = self.concat_proof(&na.atoms, &nb.atoms);
        let original = format!("({original_a} + {original_b})");
        let children_rhs = format!("({} + {})", na.source, nb.source);
        let mut atoms = na.atoms;
        atoms.extend(nb.atoms);
        let source = sum(&atoms);
        let proof = trans_eq(&original, &children_rhs, &source, children, joined);
        Normalized { source, atoms, proof }
    }

    fn cong_add(
        &mut self,
        a: &str,
        na: &str,
        b: &str,
        nb: &str,
        pa: String,
        pb: String,
    ) -> String {
        if pa != "refl" || pb != "refl" {
            self.used("nat::cong_nat");
        }
        let left = cong(format!("fun (q: Nat) => q + {b}"), a, na, pa);
        let right = cong(format!("fun (q: Nat) => {na} + q"), b, nb, pb);
        trans_eq(
            &format!("({a} + {b})"),
            &format!("({na} + {b})"),
            &format!("({na} + {nb})"),
            left,
            right,
        )
    }

    /// `sum(a) + sum(b) = sum(a ++ b)`, where `sum` is right-associated.
    fn concat_proof(&mut self, a: &[Atom], b: &[Atom]) -> String {
        debug_assert!(!a.is_empty() && !b.is_empty());
        if a.len() == 1 {
            return "refl".to_string();
        }
        self.used("nat::add_assoc");
        let head = &a[0].source;
        let tail = sum(&a[1..]);
        let rhs = sum(b);
        let assoc = format!("nat::add_assoc({head}, {tail}, {rhs})");
        let rest = self.concat_proof(&a[1..], b);
        if rest != "refl" {
            self.used("nat::cong_nat");
        }
        let lhs = format!("(({head} + {tail}) + {rhs})");
        let middle = format!("({head} + ({tail} + {rhs}))");
        let target = sum(&[&a[..], b].concat());
        trans_eq(
            &lhs,
            &middle,
            &target,
            assoc,
            cong(
                format!("fun (q: Nat) => {head} + q"),
                &format!("({tail} + {rhs})"),
                &sum(&[&a[1..], b].concat()),
                rest,
            ),
        )
    }

    fn permutation(&mut self, from: &[Atom], to: &[Atom]) -> Option<String> {
        if from.len() != to.len() {
            return None;
        }
        let mut current = from.to_vec();
        let mut proof = "refl".to_string();
        let start = sum(from);
        for i in 0..to.len() {
            let found = (i..current.len()).find(|&j| current[j].same(&to[i]))?;
            for j in (i + 1..=found).rev() {
                let before = sum(&current);
                let step = self.adjacent_swap(&current, j - 1);
                current.swap(j - 1, j);
                let after = sum(&current);
                proof = trans_eq(&start, &before, &after, proof, step);
                self.adjacent_swaps += 1;
            }
        }
        current.iter().zip(to).all(|(a, b)| a.same(b)).then_some(proof)
    }

    /// Swap positions `at` and `at + 1` in a right-associated sum.
    fn adjacent_swap(&mut self, atoms: &[Atom], at: usize) -> String {
        if at > 0 {
            self.used("nat::cong_nat");
            let head = &atoms[0].source;
            let inner = self.adjacent_swap(&atoms[1..], at - 1);
            let before = sum(&atoms[1..]);
            let mut after_atoms = atoms[1..].to_vec();
            after_atoms.swap(at - 1, at);
            let after = sum(&after_atoms);
            return cong(format!("fun (q: Nat) => {head} + q"), &before, &after, inner);
        }
        let a = &atoms[0].source;
        let b = &atoms[1].source;
        if atoms.len() == 2 {
            self.used("nat::add_comm");
            return format!("nat::add_comm({a}, {b})");
        }
        let tail = sum(&atoms[2..]);
        self.used("nat::add_assoc");
        self.used("nat::add_comm");
        self.used("nat::cong_nat");
        let start = format!("({a} + ({b} + {tail}))");
        let first = format!("(({a} + {b}) + {tail})");
        let second = format!("(({b} + {a}) + {tail})");
        let finish = format!("({b} + ({a} + {tail}))");
        trans_eq(
            &start,
            &first,
            &finish,
            sym_eq(
                &first,
                &start,
                format!("nat::add_assoc({a}, {b}, {tail})"),
            ),
            trans_eq(
                &first,
                &second,
                &finish,
                cong(
                    format!("fun (q: Nat) => q + {tail}"),
                    &format!("({a} + {b})"),
                    &format!("({b} + {a})"),
                    format!("nat::add_comm({a}, {b})"),
                ),
                format!("nat::add_assoc({b}, {a}, {tail})"),
            ),
        )
    }
}

fn trans_eq(a: &str, b: &str, c: &str, p: String, q: String) -> String {
    if p == "refl" {
        return q;
    }
    if q == "refl" {
        return p;
    }
    format!("@trans<Nat>({a}, {b}, {c}, {p}, {q})")
}

fn sym_eq(a: &str, b: &str, p: String) -> String {
    if p == "refl" {
        return p;
    }
    format!("@sym<Nat>({a}, {b}, {p})")
}

fn cong(f: String, lhs: &str, rhs: &str, proof: String) -> String {
    if proof == "refl" {
        return proof;
    }
    format!(
        "nat::cong_nat({f}, a := {lhs}, b := {rhs}, p := {proof})"
    )
}

fn sum(atoms: &[Atom]) -> String {
    debug_assert!(!atoms.is_empty());
    if atoms.len() == 1 {
        atoms[0].source.clone()
    } else {
        format!("({} + {})", atoms[0].source, sum(&atoms[1..]))
    }
}

fn named_args<'a>(elab: &Elaborator, t: &'a Term, wanted: &str) -> Option<Vec<&'a Rc<Term>>> {
    let mut args = Vec::new();
    let mut head = t;
    while let Term::App { fun, arg, .. } = head {
        args.push(arg);
        head = fun;
    }
    args.reverse();
    let Term::GlobalTm { var, subst: LocalSubst { terms, .. } } = head else { return None };
    if !terms.is_empty() {
        return None;
    }
    let got = elab.global_abs_of(*var)?;
    let want = elab.global_abs(wanted)?;
    (got == want).then_some(args)
}

fn reify(elab: &Elaborator, cx: &Cx, t: &Rc<Term>) -> Result<AddExpr, String> {
    if let Some(args) = named_args(elab, t, "nat::add") {
        let [a, b] = args.as_slice() else {
            return Err("the resolved `nat::add` has an unexpected application spine".into());
        };
        return Ok(AddExpr::Add(
            Box::new(reify(elab, cx, a)?),
            Box::new(reify(elab, cx, b)?),
        ));
    }
    if let Some(args) = named_args(elab, t, "nat::twice") {
        let [a] = args.as_slice() else {
            return Err("the resolved `nat::twice` has an unexpected application spine".into());
        };
        return Ok(AddExpr::Twice(Box::new(reify(elab, cx, a)?)));
    }
    let source = elab
        .spell_term_clean(cx, t)
        .ok_or_else(|| format!("this arithmetic atom has no complete surface spelling: {t:?}"))?;
    Ok(AddExpr::Atom(Atom { key: AtomKey::Core(Rc::clone(t)), source }))
}

pub(crate) fn parse_generated_expr(source: &str) -> Result<Expr, String> {
    let wrapper = format!("theorem __arith_generated(): 0 = 0 {{ {source} }}");
    let mut file = parse_file(&wrapper).map_err(|e| e.msg)?;
    let Some(Item::Decl(decl)) = file.items.pop() else {
        return Err("the generated proof wrapper did not parse as a theorem".into());
    };
    Ok(*decl.body.result)
}

fn boolean_tree(names: &[String], span: Span) -> Expr {
    let Some((name, rest)) = names.split_first() else {
        return Expr { kind: ExprKind::Var(BOOLEAN_LEAF.to_string()), span };
    };
    let branch = boolean_tree(rest, span);
    Expr {
        kind: ExprKind::Match {
            form: MatchForm::Match,
            generated: true,
            scrut: Box::new(Expr { kind: ExprKind::Var(name.clone()), span }),
            eqbind: None,
            motive: None,
            arms: ["False", "True"]
                .into_iter()
                .map(|ctor| Arm {
                    ctor: ctor.to_string(),
                    default: false,
                    binders: Vec::new(),
                    body: branch.clone(),
                    span,
                })
                .collect(),
        },
        span,
    }
}

/// Build the finite split shell. Three inputs is the intentional first bound:
/// it is carry's complete truth table, while keeping a mistaken invocation
/// from silently manufacturing a large proof tree.
pub(crate) fn split_booleans(
    elab: &Elaborator,
    cx: &Cx,
    span: Span,
) -> Result<Option<BooleanCertificate>, String> {
    let names: Vec<String> = cx
        .names
        .iter()
        .zip(cx.gamma.entries.iter())
        .filter(|(_, entry)| elab.tag_of(&entry.ty).is_some_and(|ind| ind.name == "Bool"))
        .map(|(name, _)| name.clone())
        .collect();
    if names.is_empty() {
        return Ok(None);
    }
    if names.len() > 3 {
        return Err(format!(
            "Boolean splitting is bounded at 3 inputs in this fragment, but the context has {}",
            names.len()
        ));
    }
    Ok(Some(BooleanCertificate { expr: boolean_tree(&names, span), splits: names.len() }))
}

/// Fixed, deterministic leaf candidates for the carry threshold. Candidate
/// search is untrusted: the caller elaborates each on a clone and kernel-checks
/// it before selecting it for the real branch.
pub(crate) fn order_candidates(cx: &Cx) -> Result<Vec<(&'static str, Expr)>, String> {
    let nats: Vec<&str> = cx
        .names
        .iter()
        .zip(cx.gamma.entries.iter())
        .filter(|(_, entry)| matches!(&*crate::inductive::decoded(&entry.ty), Type::Nat))
        .map(|(name, _)| name.as_str())
        .collect();
    let mut out = Vec::new();
    // A relation normally compares distinct parameters. Try those pairs
    // first so carry's `(power, tail_sum)` does not kernel-check four
    // reflexive candidates in every branch before reaching the useful pair.
    for distinct in [true, false] {
        for (i, &left) in nats.iter().enumerate() {
            for (j, &right) in nats.iter().enumerate() {
                if (i != j) != distinct {
                    continue;
                }
                for (lemma, rhs) in [
                    ("nat::twice_le_twice_iff", right.to_string()),
                    ("nat::twice_le_succ_twice_iff", right.to_string()),
                    ("nat::twice_le_twice_iff", format!("Succ({right})")),
                    ("nat::twice_le_succ_twice_iff", format!("Succ({right})")),
                ] {
                    let source = format!("{lemma}({left}, {rhs})");
                    out.push((lemma, parse_generated_expr(&source)?));
                }
            }
        }
    }
    Ok(out)
}

pub(crate) fn reconstruct(
    elab: &Elaborator,
    cx: &Cx,
    expected: &Type,
) -> Result<Certificate, ArithFailure> {
    let goal = elab.display_type(cx, expected);
    let Type::Id { ty, lhs, rhs, .. } = expected else {
        return Err(ArithFailure {
            kind: ArithFailureKind::UnsupportedGoal,
            goal,
            normalized_lhs: None,
            normalized_rhs: None,
            detail: "the first arithmetic fragment solves only equality goals".into(),
        });
    };
    if !matches!(&**ty, Type::Nat) {
        return Err(ArithFailure {
            kind: ArithFailureKind::UnsupportedGoal,
            goal,
            normalized_lhs: None,
            normalized_rhs: None,
            detail: "the equality carrier is not `Nat`".into(),
        });
    }
    let lhs = reify(elab, cx, lhs).map_err(|detail| ArithFailure {
        kind: ArithFailureKind::UnsupportedTerm,
        goal: goal.clone(),
        normalized_lhs: None,
        normalized_rhs: None,
        detail,
    })?;
    let rhs = reify(elab, cx, rhs).map_err(|detail| ArithFailure {
        kind: ArithFailureKind::UnsupportedTerm,
        goal: goal.clone(),
        normalized_lhs: None,
        normalized_rhs: None,
        detail,
    })?;

    let attempt = |mode| {
        let mut build = Build::new(mode);
        let nl = build.normalize(&lhs);
        let nr = build.normalize(&rhs);
        let permutation = build.permutation(&nl.atoms, &nr.atoms);
        (build, nl, nr, permutation)
    };
    let (mut build, mut nl, mut nr, mut permutation) = attempt(TwiceMode::Grouped);
    if permutation.is_none() {
        (build, nl, nr, permutation) = attempt(TwiceMode::Expanded);
    }
    let Some(permutation) = permutation else {
        return Err(ArithFailure {
            kind: ArithFailureKind::UnequalNormalForms,
            goal,
            normalized_lhs: Some(nl.source),
            normalized_rhs: Some(nr.source),
            detail: "the two sides contain different opaque atoms or coefficients".into(),
        });
    };
    let lhs_source = lhs.source();
    let rhs_source = rhs.source();
    let backwards = sym_eq(&rhs_source, &nr.source, nr.proof);
    let middle = trans_eq(&nl.source, &nr.source, &rhs_source, permutation, backwards);
    let proof = trans_eq(&lhs_source, &nl.source, &rhs_source, nl.proof, middle);
    let expr = parse_generated_expr(&proof).map_err(|detail| ArithFailure {
        kind: ArithFailureKind::Reconstruction,
        goal,
        normalized_lhs: Some(nl.source),
        normalized_rhs: Some(nr.source),
        detail,
    })?;
    Ok(Certificate {
        expr,
        report: ArithReport {
            atoms: nl.atoms.len(),
            adjacent_swaps: build.adjacent_swaps,
            boolean_splits: 0,
            branches: 1,
            used_lemmas: build.used_lemmas,
        },
    })
}
