//! Reflection and proof reconstruction for the first kernel-certified Omega
//! slice.
//!
//! The frontend reflects affine `Int` inequalities, sharing arbitrary
//! unrecognized subterms as opaque atoms. Explicit `omega::dot` constraints
//! remain as a low-level diagnostic boundary. Direct `<=` and `<` goals are
//! closed by recursively certifying a contradiction under their negation.

use std::rc::Rc;

use heather_kernel::term::{LocalSubst, Term, Type};
use heather_syntax::Expr;

use crate::arith::parse_generated_expr;
use crate::omega::{Coeffs, Derivation, DerivationId, Interval, LinearExpr, Outcome, Problem, Z};
use crate::{Cx, Elaborator};

pub(crate) struct Certificate {
    pub expr: Expr,
    pub source: String,
    pub assumptions: usize,
    pub reachable_derivations: usize,
}

#[derive(Clone)]
struct ReflectedAssumption {
    name: String,
    coeffs: Coeffs,
    coeffs_source: String,
    interval: Interval,
    atoms: Rc<Term>,
    atoms_source: String,
}

#[derive(Clone)]
struct InitialAssumption {
    coeffs: Coeffs,
    row_source: String,
    interval: Interval,
    lower: Option<String>,
    upper: Option<String>,
}

#[derive(Clone)]
enum AffineSyntax {
    Const {
        value: Z,
        source: String,
    },
    Atom {
        index: usize,
        source: String,
    },
    Add {
        source: String,
        left: Box<AffineSyntax>,
        right: Box<AffineSyntax>,
    },
    Scale {
        source: String,
        factor: Z,
        factor_on_left: bool,
        inner: Box<AffineSyntax>,
    },
}

struct Normalized {
    source: String,
    linear: LinearExpr,
    row_source: String,
    proof: String,
}

#[derive(Clone)]
struct BoundProof {
    coeffs: Coeffs,
    row_source: String,
    interval: Interval,
    lower: Option<String>,
    upper: Option<String>,
}

fn named_args<'a>(elab: &Elaborator, t: &'a Term, wanted: &str) -> Option<Vec<&'a Rc<Term>>> {
    let mut args = Vec::new();
    let mut head = t;
    while let Term::App { fun, arg, .. } = head {
        args.push(arg);
        head = fun;
    }
    args.reverse();
    let Term::GlobalTm {
        var,
        subst: LocalSubst { terms, .. },
    } = head
    else {
        return None;
    };
    if !terms.is_empty() {
        return None;
    }
    (elab.global_abs_of(*var)? == elab.global_abs(wanted)?).then_some(args)
}

fn relation_args<'a>(elab: &Elaborator, ty: &'a Type) -> Option<(&'a Rc<Term>, &'a Rc<Term>)> {
    let Type::El { tm, .. } = ty else {
        return None;
    };
    let args = named_args(elab, tm, "int::Le")?;
    let [left, right] = args.as_slice() else {
        return None;
    };
    Some((left, right))
}

fn strict_relation_args<'a>(
    elab: &Elaborator,
    ty: &'a Type,
) -> Option<(&'a Rc<Term>, &'a Rc<Term>)> {
    let Type::El { tm, .. } = ty else {
        return None;
    };
    let args = named_args(elab, tm, "int::Lt")?;
    let [left, right] = args.as_slice() else {
        return None;
    };
    Some((left, right))
}

fn dot_args<'a>(elab: &Elaborator, tm: &'a Term) -> Option<(&'a Rc<Term>, &'a Rc<Term>)> {
    let args = named_args(elab, tm, "omega::dot")?;
    let [coeffs, atoms] = args.as_slice() else {
        return None;
    };
    Some((coeffs, atoms))
}

fn integer_source(source: &str) -> Option<Z> {
    let compact: String = source.chars().filter(|c| !c.is_whitespace()).collect();
    if let Ok(value) = compact.parse() {
        return Some(value);
    }
    if let Some(inner) = compact
        .strip_prefix("OfNat(")
        .and_then(|s| s.strip_suffix(')'))
    {
        return inner.parse().ok();
    }
    if let Some(inner) = compact
        .strip_prefix("NegSucc(")
        .and_then(|s| s.strip_suffix(')'))
    {
        let payload: Z = inner.parse().ok()?;
        return payload.checked_add(1)?.checked_neg();
    }
    None
}

struct ListParser<'a> {
    input: &'a [u8],
    cursor: usize,
}

impl<'a> ListParser<'a> {
    fn new(input: &'a str) -> Self {
        Self {
            input: input.as_bytes(),
            cursor: 0,
        }
    }

    fn spaces(&mut self) {
        while self
            .input
            .get(self.cursor)
            .is_some_and(u8::is_ascii_whitespace)
        {
            self.cursor += 1;
        }
    }

    fn token(&mut self, token: &[u8]) -> bool {
        self.spaces();
        if self.input.get(self.cursor..self.cursor + token.len()) == Some(token) {
            self.cursor += token.len();
            true
        } else {
            false
        }
    }

    fn signed_number(&mut self) -> Option<Z> {
        self.spaces();
        let start = self.cursor;
        if self.input.get(self.cursor) == Some(&b'-') {
            self.cursor += 1;
        }
        let digits = self.cursor;
        while self.input.get(self.cursor).is_some_and(u8::is_ascii_digit) {
            self.cursor += 1;
        }
        (self.cursor > digits).then(|| {
            std::str::from_utf8(&self.input[start..self.cursor])
                .ok()?
                .parse()
                .ok()
        })?
    }

    fn integer(&mut self) -> Option<Z> {
        if self.token(b"OfNat") {
            self.token(b"(").then_some(())?;
            let value = self.signed_number()?;
            if value < 0 || !self.token(b")") {
                return None;
            }
            return Some(value);
        }
        if self.token(b"NegSucc") {
            self.token(b"(").then_some(())?;
            let payload = self.signed_number()?;
            if payload < 0 || !self.token(b")") {
                return None;
            }
            return payload.checked_add(1)?.checked_neg();
        }
        self.signed_number()
    }

    fn list(&mut self, out: &mut Vec<Z>) -> Option<()> {
        if self.token(b"Nil") {
            return Some(());
        }
        if !self.token(b"Cons") || !self.token(b"(") {
            return None;
        }
        out.push(self.integer()?);
        if !self.token(b",") {
            return None;
        }
        self.list(out)?;
        self.token(b")").then_some(())
    }
}

fn coefficient_source(source: &str) -> Option<Vec<Z>> {
    let mut parser = ListParser::new(source);
    let mut out = Vec::new();
    parser.list(&mut out)?;
    parser.spaces();
    (parser.cursor == parser.input.len()).then_some(out)
}

fn reflect_assumption(
    elab: &Elaborator,
    cx: &Cx,
    pos: usize,
) -> Result<Option<ReflectedAssumption>, String> {
    let (_, ty, _) = elab.local(cx, pos);
    let Some((left, right)) = relation_args(elab, &ty) else {
        return Ok(None);
    };
    let (coeff_term, atoms, interval) = if let Some((coeffs, atoms)) = dot_args(elab, right) {
        let lower_source = elab.spell_term_clean(cx, left).ok_or_else(|| {
            format!(
                "Omega could not spell the lower bound in `{}`",
                cx.names[pos]
            )
        })?;
        let lower = integer_source(&lower_source)
            .ok_or_else(|| format!("Omega requires a literal lower bound, got `{lower_source}`"))?;
        (coeffs, atoms, Interval::lower(lower))
    } else if let Some((coeffs, atoms)) = dot_args(elab, left) {
        let upper_source = elab.spell_term_clean(cx, right).ok_or_else(|| {
            format!(
                "Omega could not spell the upper bound in `{}`",
                cx.names[pos]
            )
        })?;
        let upper = integer_source(&upper_source)
            .ok_or_else(|| format!("Omega requires a literal upper bound, got `{upper_source}`"))?;
        (coeffs, atoms, Interval::upper(upper))
    } else {
        return Ok(None);
    };
    let coeff_source = elab.spell_term_clean(cx, coeff_term).ok_or_else(|| {
        format!(
            "Omega could not spell the coefficient row in `{}`",
            cx.names[pos]
        )
    })?;
    let coeffs = coefficient_source(&coeff_source).ok_or_else(|| {
        format!(
            "Omega's first certificate frontend requires a literal `Cons`/`Nil` coefficient row, got `{coeff_source}`"
        )
    })?;
    if coeffs.contains(&Z::MIN) || interval.lower == Some(Z::MIN) || interval.upper == Some(Z::MIN)
    {
        return Err("Omega cannot reconstruct the minimum `i128` literal".into());
    }
    let atoms_source = elab
        .spell_term_clean(cx, atoms)
        .ok_or_else(|| format!("Omega could not spell the atom row in `{}`", cx.names[pos]))?;
    Ok(Some(ReflectedAssumption {
        name: cx.names[pos].clone(),
        coeffs: Coeffs::new(coeffs),
        coeffs_source: coeff_source,
        interval,
        atoms: Rc::clone(atoms),
        atoms_source,
    }))
}

fn affine_syntax(
    elab: &Elaborator,
    cx: &Cx,
    tm: &Rc<Term>,
    atoms: &mut Vec<Rc<Term>>,
) -> Result<AffineSyntax, String> {
    let source = elab
        .spell_term_clean(cx, tm)
        .ok_or("Omega could not spell an integer expression")?;
    if let Some(value) = integer_source(&source) {
        if value == Z::MIN {
            return Err("Omega cannot reconstruct the minimum `i128` literal".into());
        }
        return Ok(AffineSyntax::Const {
            value,
            source: int_ctor(value),
        });
    }
    if let Some(args) = named_args(elab, tm, "int::add") {
        if let [left, right] = args.as_slice() {
            return Ok(AffineSyntax::Add {
                source,
                left: Box::new(affine_syntax(elab, cx, left, atoms)?),
                right: Box::new(affine_syntax(elab, cx, right, atoms)?),
            });
        }
    }
    if let Some(args) = named_args(elab, tm, "int::mul") {
        if let [left, right] = args.as_slice() {
            let left_source = elab.spell_term_clean(cx, left);
            let right_source = elab.spell_term_clean(cx, right);
            if let Some(factor) = left_source.as_deref().and_then(integer_source) {
                if factor == Z::MIN {
                    return Err("Omega cannot reconstruct the minimum `i128` literal".into());
                }
                return Ok(AffineSyntax::Scale {
                    source,
                    factor,
                    factor_on_left: true,
                    inner: Box::new(affine_syntax(elab, cx, right, atoms)?),
                });
            }
            if let Some(factor) = right_source.as_deref().and_then(integer_source) {
                if factor == Z::MIN {
                    return Err("Omega cannot reconstruct the minimum `i128` literal".into());
                }
                return Ok(AffineSyntax::Scale {
                    source,
                    factor,
                    factor_on_left: false,
                    inner: Box::new(affine_syntax(elab, cx, left, atoms)?),
                });
            }
        }
    }

    let index = atoms
        .iter()
        .position(|atom| {
            **atom == **tm
                || elab
                    .spell_term_clean(cx, atom)
                    .is_some_and(|atom_source| atom_source == source)
        })
        .unwrap_or_else(|| {
            atoms.push(Rc::clone(tm));
            atoms.len() - 1
        });
    Ok(AffineSyntax::Atom { index, source })
}

fn atom_list_source(elab: &Elaborator, cx: &Cx, atoms: &[Rc<Term>]) -> Result<String, String> {
    atoms
        .iter()
        .rev()
        .try_fold("Nil".to_string(), |tail, atom| {
            let source = elab
                .spell_term_clean(cx, atom)
                .ok_or("Omega could not spell an opaque arithmetic atom")?;
            Ok(format!("Cons({source}, {tail})"))
        })
}

fn normalize_syntax(syntax: &AffineSyntax, atoms_source: &str) -> Result<Normalized, String> {
    match syntax {
        AffineSyntax::Const { value, source } => {
            let row_source = format!("omega::zeros({atoms_source})");
            Ok(Normalized {
                source: source.clone(),
                linear: LinearExpr::constant(*value),
                proof: format!("omega::normalize_const({}, {})", int(*value), atoms_source),
                row_source,
            })
        }
        AffineSyntax::Atom { index, source } => {
            let row_source = format!("omega::basis({index}, {atoms_source})");
            Ok(Normalized {
                source: source.clone(),
                linear: LinearExpr::atom(*index),
                proof: format!("omega::normalize_atom({index}, {atoms_source})"),
                row_source,
            })
        }
        AffineSyntax::Add {
            source,
            left,
            right,
        } => {
            let left = normalize_syntax(left, atoms_source)?;
            let right = normalize_syntax(right, atoms_source)?;
            let linear = left
                .linear
                .checked_add(&right.linear)
                .map_err(|failure| failure.to_string())?;
            let row_source = format!(
                "omega::add_coeffs({}, {})",
                left.row_source, right.row_source
            );
            let proof = format!(
                "omega::normalize_add({}, {}, {}, {}, {}, {}, {}, {}, {})",
                left.source,
                right.source,
                int(left.linear.constant),
                int(right.linear.constant),
                left.row_source,
                right.row_source,
                atoms_source,
                left.proof,
                right.proof,
            );
            Ok(Normalized {
                source: source.clone(),
                linear,
                row_source,
                proof,
            })
        }
        AffineSyntax::Scale {
            source,
            factor,
            factor_on_left,
            inner,
        } => {
            let inner = normalize_syntax(inner, atoms_source)?;
            let linear = inner
                .linear
                .checked_scale(*factor)
                .map_err(|failure| failure.to_string())?;
            let row_source = format!("omega::scale({}, {})", int(*factor), inner.row_source);
            let lemma = if *factor_on_left {
                "omega::normalize_scale"
            } else {
                "omega::normalize_scale_right"
            };
            let proof = format!(
                "{lemma}({}, {}, {}, {}, {}, {})",
                if *factor_on_left {
                    int(*factor)
                } else {
                    inner.source.clone()
                },
                if *factor_on_left {
                    inner.source.clone()
                } else {
                    int(*factor)
                },
                int(inner.linear.constant),
                inner.row_source,
                atoms_source,
                inner.proof,
            );
            Ok(Normalized {
                source: source.clone(),
                linear,
                row_source,
                proof,
            })
        }
    }
}

fn reflect_ordinary(
    elab: &Elaborator,
    cx: &Cx,
) -> Result<Option<(Vec<InitialAssumption>, String)>, String> {
    let mut atoms = Vec::new();
    let mut relations = Vec::new();
    for pos in 0..cx.names.len() {
        let (_, ty, _) = elab.local(cx, pos);
        let (left, right) = if let Some((left, right)) = relation_args(elab, &ty) {
            if dot_args(elab, left).is_some() || dot_args(elab, right).is_some() {
                return Ok(None);
            }
            (
                affine_syntax(elab, cx, left, &mut atoms)?,
                affine_syntax(elab, cx, right, &mut atoms)?,
            )
        } else if let Some((left, right)) = strict_relation_args(elab, &ty) {
            let left_source = elab
                .spell_term_clean(cx, left)
                .ok_or("Omega could not spell the left side of a strict inequality")?;
            let left = AffineSyntax::Add {
                source: format!("int::isucc({left_source})"),
                left: Box::new(affine_syntax(elab, cx, left, &mut atoms)?),
                right: Box::new(AffineSyntax::Const {
                    value: 1,
                    source: int(1),
                }),
            };
            (left, affine_syntax(elab, cx, right, &mut atoms)?)
        } else {
            continue;
        };
        relations.push((pos, left, right));
    }
    if relations.is_empty() {
        return Ok(None);
    }
    let atoms_source = atom_list_source(elab, cx, &atoms)?;
    let mut facts = Vec::with_capacity(relations.len());
    for (pos, left, right) in relations {
        let left = normalize_syntax(&left, &atoms_source)?;
        let right = normalize_syntax(&right, &atoms_source)?;
        let linear = left
            .linear
            .checked_sub(&right.linear)
            .map_err(|failure| failure.to_string())?;
        let upper = right
            .linear
            .constant
            .checked_sub(left.linear.constant)
            .ok_or("Omega bound arithmetic overflowed")?;
        let row_source = format!(
            "omega::sub_coeffs({}, {})",
            left.row_source, right.row_source
        );
        let proof = format!(
            "omega::normalized_le_upper({}, {}, {}, {}, {}, {}, {}, {}, {}, {})",
            left.source,
            right.source,
            int(left.linear.constant),
            int(right.linear.constant),
            left.row_source,
            right.row_source,
            atoms_source,
            left.proof,
            right.proof,
            cx.names[pos],
        );
        facts.push(InitialAssumption {
            coeffs: linear.coeffs,
            row_source,
            interval: Interval::upper(upper),
            lower: None,
            upper: Some(proof),
        });
    }
    Ok(Some((facts, atoms_source)))
}

fn int(value: Z) -> String {
    int_ctor(value)
}

fn int_ctor(value: Z) -> String {
    if value >= 0 {
        format!("OfNat({value})")
    } else {
        let payload = value.checked_neg().unwrap_or(Z::MAX) - 1;
        format!("NegSucc({payload})")
    }
}

fn literal_lt_proof(lower: Z, upper: Z) -> Result<String, String> {
    if lower >= upper {
        return Err(format!(
            "Omega cannot prove the false literal order {lower} < {upper}"
        ));
    }
    if lower >= 0 {
        return Ok(format!(
            "int::ofNat_lt_iff({}, {}).mp(trivial)",
            lower, upper
        ));
    }
    let lower_payload = lower
        .checked_neg()
        .and_then(|value| value.checked_sub(1))
        .ok_or("Omega cannot reconstruct the minimum `i128` literal")?;
    if upper >= 0 {
        return Ok(format!(
            "int::negsucc_lt_ofnat({}, {})",
            lower_payload, upper
        ));
    }
    let upper_payload = upper
        .checked_neg()
        .and_then(|value| value.checked_sub(1))
        .ok_or("Omega cannot reconstruct the minimum `i128` literal")?;
    Ok(format!(
        "int::negsucc_lt_of_lt({}, {}, trivial)",
        lower_payload, upper_payload
    ))
}

fn list(coeffs: &Coeffs) -> String {
    coeffs
        .as_slice()
        .iter()
        .rev()
        .fold("Nil".to_string(), |tail, value| {
            format!("Cons({}, {tail})", int_ctor(*value))
        })
}

fn parent<'a>(
    proofs: &'a [Option<BoundProof>],
    id: DerivationId,
) -> Result<&'a BoundProof, String> {
    proofs
        .get(id)
        .and_then(Option::as_ref)
        .ok_or_else(|| format!("Omega certificate parent {id} was not reconstructed"))
}

pub(crate) fn reconstruct(
    elab: &Elaborator,
    cx: &Cx,
    expected: &Type,
) -> Result<Certificate, String> {
    if let Some((left, right)) = strict_relation_args(elab, expected) {
        let left = elab
            .spell_term_clean(cx, left)
            .ok_or("Omega could not spell the left side of its `Int` strict goal")?;
        let right = elab
            .spell_term_clean(cx, right)
            .ok_or("Omega could not spell the right side of its `Int` strict goal")?;
        let source = format!(
            "int::lt_of_not_le({}, {}, (__omega_negated_goal: {} <= {}) ⊢ omega)",
            left, right, right, left,
        );
        return Ok(Certificate {
            expr: parse_generated_expr(&source)?,
            source,
            assumptions: 0,
            reachable_derivations: 0,
        });
    }
    if let Some((left, right)) = relation_args(elab, expected) {
        let left = elab
            .spell_term_clean(cx, left)
            .ok_or("Omega could not spell the left side of its `Int` goal")?;
        let right = elab
            .spell_term_clean(cx, right)
            .ok_or("Omega could not spell the right side of its `Int` goal")?;
        // `right < left` is definitionally `right + 1 <= left`. Writing the
        // latter lets the recursive `omega` invocation use the same affine
        // `Le` frontend as ordinary hypotheses.
        let source = format!(
            "int::le_of_not_lt({}, {}, (__omega_negated_goal: {} + OfNat(1) <= {}) ⊢ omega)",
            right, left, right, left,
        );
        return Ok(Certificate {
            expr: parse_generated_expr(&source)?,
            source,
            assumptions: 0,
            reachable_derivations: 0,
        });
    }
    if elab.display_type(cx, expected) != "False" {
        return Err(format!(
            "Omega currently expects `False` or an `Int` `<=` goal, got `{}`",
            elab.display_type(cx, expected)
        ));
    }

    let (reflected, atoms_source) = if let Some(ordinary) = reflect_ordinary(elab, cx)? {
        ordinary
    } else {
        let mut explicit = Vec::new();
        for pos in 0..cx.names.len() {
            if let Some(fact) = reflect_assumption(elab, cx, pos)? {
                explicit.push(fact);
            }
        }
        let Some(first) = explicit.first() else {
            return Err("Omega found no integer constraints".into());
        };
        if explicit.iter().any(|fact| *fact.atoms != *first.atoms) {
            return Err(
                "Omega's explicit certificate frontend requires one shared atom row".into(),
            );
        }
        let atoms_source = first.atoms_source.clone();
        let facts = explicit
            .into_iter()
            .map(|fact| InitialAssumption {
                coeffs: fact.coeffs,
                row_source: fact.coeffs_source,
                interval: fact.interval,
                lower: fact.interval.lower.map(|_| fact.name.clone()),
                upper: fact.interval.upper.map(|_| fact.name),
            })
            .collect();
        (facts, atoms_source)
    };

    let mut problem = Problem::new();
    let reflected_debug = reflected
        .iter()
        .map(|fact| format!("{:?} {:?}", fact.coeffs, fact.interval))
        .collect::<Vec<_>>()
        .join(", ");
    for fact in &reflected {
        problem
            .assume(fact.coeffs.as_slice().to_vec(), fact.interval)
            .map_err(|failure| failure.to_string())?;
    }
    let (problem, outcome) = problem.solve().map_err(|failure| failure.to_string())?;
    let Outcome::Contradiction {
        derivation,
        reachable_derivations,
        ..
    } = &outcome
    else {
        return Err(format!(
            "Omega's real shadow found no contradiction: {outcome:?}; locals {:?}; reflected [{reflected_debug}]",
            cx.names,
        ));
    };
    let derivation = *derivation;
    let reachable_derivations = reachable_derivations.clone();

    let mut proofs: Vec<Option<BoundProof>> = vec![None; problem.dag.nodes().len()];
    let mut bindings = Vec::new();
    for &id in &reachable_derivations {
        let fact = problem.replay(id).map_err(|failure| failure.to_string())?;
        let proof = match problem.dag.nodes()[id] {
            Derivation::Assumption { index } => {
                let source = reflected
                    .get(index)
                    .ok_or_else(|| format!("Omega assumption {index} was not reflected"))?;
                BoundProof {
                    coeffs: fact.coeffs,
                    row_source: source.row_source.clone(),
                    interval: fact.interval,
                    lower: source.lower.clone(),
                    upper: source.upper.clone(),
                }
            }
            Derivation::Positivize { parent: source } => {
                let source = parent(&proofs, source)?;
                let row_source = format!("omega::scale({}, {})", int(-1), source.row_source);
                let (lower, upper) = match (source.interval.lower, source.interval.upper) {
                    (None, Some(bound)) => (
                        Some(format!(
                            "omega::upper_to_negated_lower({}, {}, {}, {})",
                            source.row_source,
                            atoms_source,
                            int(bound),
                            source
                                .upper
                                .as_ref()
                                .ok_or("Omega positivization lost its upper proof")?,
                        )),
                        None,
                    ),
                    (Some(bound), None) => {
                        return Err(format!(
                            "Omega proof reconstruction cannot yet positivize lower bound {bound}"
                        ));
                    }
                    _ => return Err("Omega cannot positivize a two-sided interval yet".into()),
                };
                BoundProof {
                    coeffs: fact.coeffs,
                    row_source,
                    interval: fact.interval,
                    lower,
                    upper,
                }
            }
            Derivation::Intersect { left, right } => {
                let left = parent(&proofs, left)?;
                let right = parent(&proofs, right)?;
                let lower = match fact.interval.lower {
                    Some(bound) if left.interval.lower == Some(bound) => left.lower.clone(),
                    Some(bound) if right.interval.lower == Some(bound) => right.lower.clone(),
                    Some(bound) => {
                        return Err(format!("Omega could not source lower bound {bound}"));
                    }
                    None => None,
                };
                let upper = match fact.interval.upper {
                    Some(bound) if left.interval.upper == Some(bound) => left.upper.clone(),
                    Some(bound) if right.interval.upper == Some(bound) => right.upper.clone(),
                    Some(bound) => {
                        return Err(format!("Omega could not source upper bound {bound}"));
                    }
                    None => None,
                };
                BoundProof {
                    coeffs: fact.coeffs,
                    row_source: left.row_source.clone(),
                    interval: fact.interval,
                    lower,
                    upper,
                }
            }
            Derivation::Combo {
                left,
                left_scale,
                right,
                right_scale,
            } if left_scale > 0 && right_scale < 0 && fact.interval.upper.is_none() => {
                let left = parent(&proofs, left)?;
                let right = parent(&proofs, right)?;
                let lower = left
                    .lower
                    .as_ref()
                    .ok_or("Omega combination is missing its lower proof")?;
                let upper = right
                    .upper
                    .as_ref()
                    .ok_or("Omega combination is missing its upper proof")?;
                let l = left
                    .interval
                    .lower
                    .ok_or("Omega combination has no lower value")?;
                let u = right
                    .interval
                    .upper
                    .ok_or("Omega combination has no upper value")?;
                let magnitude = right_scale
                    .checked_neg()
                    .ok_or("Omega combination scale overflowed")?;
                let name = format!("__omega_generated_{id}");
                let row_source = format!(
                    "omega::combo({}, {}, {}, {})",
                    int(left_scale),
                    left.row_source,
                    int(right_scale),
                    right.row_source,
                );
                let expression = format!(
                    "omega::lower_upper_combo({}, {}, {}, {}, {}, {}, {}, int::zero_le_ofNat({}), int::zero_le_ofNat({}), {}, {})",
                    int(left_scale),
                    int(magnitude),
                    list(&left.coeffs),
                    list(&right.coeffs),
                    atoms_source,
                    int(l),
                    int(u),
                    left_scale,
                    magnitude,
                    lower,
                    upper,
                );
                bindings.push(format!("let {name} = {expression};"));
                BoundProof {
                    coeffs: fact.coeffs,
                    row_source,
                    interval: fact.interval,
                    lower: Some(name),
                    upper: None,
                }
            }
            Derivation::Constant {
                parent: source,
                impossible,
            } if impossible => {
                let source = parent(&proofs, source)?;
                BoundProof {
                    coeffs: fact.coeffs,
                    row_source: source.row_source.clone(),
                    interval: fact.interval,
                    lower: source.lower.clone(),
                    upper: source.upper.clone(),
                }
            }
            ref unsupported => {
                return Err(format!(
                    "Omega proof reconstruction does not yet support derivation {unsupported:?}"
                ));
            }
        };
        proofs[id] = Some(proof);
    }

    let root = parent(&proofs, derivation)?;
    let lower = root
        .interval
        .lower
        .ok_or("Omega contradiction has no lower bound")?;
    let upper = root
        .interval
        .upper
        .ok_or("Omega contradiction has no upper bound")?;
    if upper >= lower {
        return Err("Omega contradiction did not contain crossed bounds".into());
    }
    let lower_proof = root
        .lower
        .as_ref()
        .ok_or("Omega contradiction lost its lower proof")?;
    let upper_proof = root
        .upper
        .as_ref()
        .ok_or("Omega contradiction lost its upper proof")?;
    let row = &root.row_source;
    let trans = format!(
        "int::le_trans({}, omega::dot({}, {}), {}, {}, {})",
        int(lower),
        row,
        atoms_source,
        int(upper),
        lower_proof,
        upper_proof,
    );
    let result = format!(
        "int::not_lt_of_ge({}, {}, {}) ({})",
        int(lower),
        int(upper),
        trans,
        literal_lt_proof(upper, lower)?,
    );
    let source = if bindings.is_empty() {
        result
    } else {
        format!("{{ {} {} }}", bindings.join(" "), result)
    };
    let expr = parse_generated_expr(&source)?;
    Ok(Certificate {
        expr,
        source,
        assumptions: reflected.len(),
        reachable_derivations: reachable_derivations.len(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn coefficient_parser_accepts_only_the_generated_list_grammar() {
        assert_eq!(
            coefficient_source("Cons(3, Cons(-1, Nil))"),
            Some(vec![3, -1])
        );
        assert_eq!(
            coefficient_source("Cons(OfNat(3), Cons(NegSucc(0), Nil))"),
            Some(vec![3, -1])
        );
        assert_eq!(coefficient_source("Nil"), Some(vec![]));
        assert_eq!(coefficient_source("Cons(x, Nil)"), None);
        assert_eq!(coefficient_source("Cons(1, Nil) junk"), None);
    }
}
