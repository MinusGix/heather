//! Reflection and proof reconstruction for the first kernel-certified Omega
//! slice.
//!
//! The frontend reflects affine `Int` inequalities and equalities, sharing
//! arbitrary unrecognized subterms as opaque atoms. Explicit `omega::dot`
//! constraints remain as a low-level diagnostic boundary. Direct `<=`, `<`,
//! and `=` goals reuse recursively certified order consequences.

use std::rc::Rc;

use heather_kernel::term::{LocalSubst, Term, Type};
use heather_syntax::{Expr, Item, parse_file};

use crate::omega::{Coeffs, Derivation, DerivationId, Interval, LinearExpr, Outcome, Problem, Z};
use crate::{Cx, Elaborator};

pub(crate) struct Certificate {
    pub expr: Expr,
    pub source: String,
    pub report: OmegaReport,
}

fn parse_generated_expr(source: &str) -> Result<Expr, String> {
    let wrapper = format!("theorem __omega_generated(): 0 = 0 {{ {source} }}");
    let mut file = parse_file(&wrapper).map_err(|error| error.msg)?;
    let Some(Item::Decl(decl)) = file.items.pop() else {
        return Err("the generated Omega proof wrapper did not parse as a theorem".into());
    };
    Ok(*decl.body.result)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OmegaReport {
    pub atoms: usize,
    pub assumptions: usize,
    pub reachable_derivations: usize,
    pub logical_splits: usize,
    pub stats: crate::omega::Stats,
    pub used_lemmas: Vec<&'static str>,
}

fn wrapper_report(lemma: &'static str, logical_splits: usize) -> OmegaReport {
    OmegaReport {
        atoms: 0,
        assumptions: 0,
        reachable_derivations: 0,
        logical_splits,
        stats: crate::omega::Stats::default(),
        used_lemmas: vec![lemma],
    }
}

fn reconstruction_lemmas(source: &str) -> Vec<&'static str> {
    const CANDIDATES: &[&str] = &[
        "int::cong_ofnat",
        "int::le_trans",
        "int::negsucc_lt_of_lt",
        "int::negsucc_lt_ofnat",
        "int::not_lt_of_ge",
        "int::zero_le_ofNat",
        "omega::atom_nonnegative",
        "omega::divide_lower",
        "omega::divide_upper",
        "omega::impossible_constant_lower",
        "omega::impossible_constant_upper",
        "omega::lower_combo",
        "omega::lower_of_eq",
        "omega::lower_to_negated_upper",
        "omega::lower_upper_combo",
        "omega::nat_le_of_not_lt",
        "omega::nat_le_to_int",
        "omega::nat_lt_of_not_le",
        "omega::nat_lt_to_int",
        "omega::normalize_add",
        "omega::normalize_atom",
        "omega::normalize_const",
        "omega::normalize_nat_add",
        "omega::normalize_nat_scale_left",
        "omega::normalize_nat_scale_right",
        "omega::normalize_neg",
        "omega::normalize_scale",
        "omega::normalize_scale_right",
        "omega::normalized_eq_value",
        "omega::normalized_le_upper",
        "omega::upper_combo",
        "omega::upper_lower_combo",
        "omega::upper_of_eq",
        "omega::upper_to_negated_lower",
    ];
    CANDIDATES
        .iter()
        .copied()
        .filter(|lemma| source.contains(&format!("{lemma}(")))
        .collect()
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
        left: Box<AffineSyntax>,
        right: Box<AffineSyntax>,
    },
    Neg {
        inner: Box<AffineSyntax>,
    },
    NatAdd {
        left_nat: String,
        right_nat: String,
        left: Box<AffineSyntax>,
        right: Box<AffineSyntax>,
    },
    NatScale {
        factor: Z,
        factor_on_left: bool,
        factor_nat: String,
        inner_nat: String,
        inner: Box<AffineSyntax>,
    },
    Scale {
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

struct ReflectedAtom {
    term: Rc<Term>,
    source: String,
    nat_source: Option<String>,
}

#[derive(Clone)]
struct BoundProof {
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

fn nat_relation_args<'a>(elab: &Elaborator, ty: &'a Type) -> Option<(&'a Rc<Term>, &'a Rc<Term>)> {
    let Type::El { tm, .. } = ty else {
        return None;
    };
    let args = named_args(elab, tm, "nat::Le")?;
    let [left, right] = args.as_slice() else {
        return None;
    };
    Some((left, right))
}

fn nat_strict_relation_args<'a>(
    elab: &Elaborator,
    ty: &'a Type,
) -> Option<(&'a Rc<Term>, &'a Rc<Term>)> {
    let Type::El { tm, .. } = ty else {
        return None;
    };
    let args = named_args(elab, tm, "nat::Lt")?;
    let [left, right] = args.as_slice() else {
        return None;
    };
    Some((left, right))
}

fn equality_args<'a>(
    elab: &Elaborator,
    cx: &Cx,
    ty: &'a Type,
) -> Option<(&'a Rc<Term>, &'a Rc<Term>)> {
    let Type::Id { ty, lhs, rhs, .. } = ty else {
        return None;
    };
    (elab.display_type(cx, ty) == "Int").then_some((lhs, rhs))
}

fn nat_equality_args<'a>(
    elab: &Elaborator,
    cx: &Cx,
    ty: &'a Type,
) -> Option<(&'a Rc<Term>, &'a Rc<Term>)> {
    let Type::Id { ty, lhs, rhs, .. } = ty else {
        return None;
    };
    (elab.display_type(cx, ty) == "Nat").then_some((lhs, rhs))
}

fn negated_domain(elab: &Elaborator, cx: &Cx, ty: &Type) -> Option<Type> {
    if let Type::El { level, tm } = ty {
        let args = named_args(elab, tm, "logic::Not")?;
        let [domain] = args.as_slice() else {
            return None;
        };
        return Some(Type::El {
            level: level.clone(),
            tm: Rc::clone(domain),
        });
    }
    let Type::Pi { dom, .. } = ty else {
        return None;
    };
    elab.display_type(cx, ty)
        .ends_with(" -> False")
        .then(|| (**dom).clone())
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
    atoms: &mut Vec<ReflectedAtom>,
) -> Result<AffineSyntax, String> {
    let source = int_term_source(elab, cx, tm)?;
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
                left: Box::new(affine_syntax(elab, cx, left, atoms)?),
                right: Box::new(affine_syntax(elab, cx, right, atoms)?),
            });
        }
    }
    if let Some(args) = named_args(elab, tm, "int::sub") {
        if let [left, right] = args.as_slice() {
            return Ok(AffineSyntax::Add {
                left: Box::new(affine_syntax(elab, cx, left, atoms)?),
                right: Box::new(AffineSyntax::Neg {
                    inner: Box::new(affine_syntax(elab, cx, right, atoms)?),
                }),
            });
        }
    }
    if let Some(args) = named_args(elab, tm, "int::neg") {
        if let [inner] = args.as_slice() {
            return Ok(AffineSyntax::Neg {
                inner: Box::new(affine_syntax(elab, cx, inner, atoms)?),
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
                    factor,
                    factor_on_left: false,
                    inner: Box::new(affine_syntax(elab, cx, left, atoms)?),
                });
            }
        }
    }

    let index = atoms
        .iter()
        .position(|atom| *atom.term == **tm || atom.source == source)
        .unwrap_or_else(|| {
            atoms.push(ReflectedAtom {
                term: Rc::clone(tm),
                source: source.clone(),
                nat_source: None,
            });
            atoms.len() - 1
        });
    Ok(AffineSyntax::Atom { index, source })
}

fn int_term_source(elab: &Elaborator, cx: &Cx, tm: &Rc<Term>) -> Result<String, String> {
    for (name, arity) in [
        ("int::add", 2usize),
        ("int::sub", 2),
        ("int::mul", 2),
        ("int::neg", 1),
    ] {
        if let Some(args) = named_args(elab, tm, name)
            && args.len() == arity
        {
            let args = args
                .into_iter()
                .map(|arg| int_term_source(elab, cx, arg))
                .collect::<Result<Vec<_>, _>>()?;
            return Ok(format!("{}({})", name, args.join(", ")));
        }
    }
    elab.spell_term_clean(cx, tm)
        .ok_or_else(|| "Omega could not spell an integer expression".to_string())
}

fn nat_term_source(elab: &Elaborator, cx: &Cx, tm: &Rc<Term>) -> Result<String, String> {
    if let Some(args) = named_args(elab, tm, "nat::add")
        && let [left, right] = args.as_slice()
    {
        return Ok(format!(
            "nat::add({}, {})",
            nat_term_source(elab, cx, left)?,
            nat_term_source(elab, cx, right)?,
        ));
    }
    if let Some(args) = named_args(elab, tm, "nat::mul")
        && let [left, right] = args.as_slice()
    {
        return Ok(format!(
            "nat::mul({}, {})",
            nat_term_source(elab, cx, left)?,
            nat_term_source(elab, cx, right)?,
        ));
    }
    elab.spell_term_clean(cx, tm)
        .ok_or_else(|| "Omega could not spell a natural expression".to_string())
}

fn nat_affine_syntax(
    elab: &Elaborator,
    cx: &Cx,
    tm: &Rc<Term>,
    atoms: &mut Vec<ReflectedAtom>,
) -> Result<AffineSyntax, String> {
    let nat_source = nat_term_source(elab, cx, tm)?;
    if let Some(value) = integer_source(&nat_source).filter(|value| *value >= 0) {
        return Ok(AffineSyntax::Const {
            value,
            source: int(value),
        });
    }
    if let Some(args) = named_args(elab, tm, "nat::add") {
        if let [left, right] = args.as_slice() {
            let left_nat = nat_term_source(elab, cx, left)?;
            let right_nat = nat_term_source(elab, cx, right)?;
            return Ok(AffineSyntax::NatAdd {
                left_nat,
                right_nat,
                left: Box::new(nat_affine_syntax(elab, cx, left, atoms)?),
                right: Box::new(nat_affine_syntax(elab, cx, right, atoms)?),
            });
        }
    }
    if let Some(args) = named_args(elab, tm, "nat::mul") {
        if let [left, right] = args.as_slice() {
            let left_source = nat_term_source(elab, cx, left).ok();
            let right_source = nat_term_source(elab, cx, right).ok();
            if let Some(factor) = left_source
                .as_deref()
                .and_then(integer_source)
                .filter(|value| *value >= 0)
            {
                return Ok(AffineSyntax::NatScale {
                    factor,
                    factor_on_left: true,
                    factor_nat: left_source.unwrap(),
                    inner_nat: right_source
                        .ok_or("Omega could not spell a natural multiplication operand")?,
                    inner: Box::new(nat_affine_syntax(elab, cx, right, atoms)?),
                });
            }
            if let Some(factor) = right_source
                .as_deref()
                .and_then(integer_source)
                .filter(|value| *value >= 0)
            {
                return Ok(AffineSyntax::NatScale {
                    factor,
                    factor_on_left: false,
                    factor_nat: right_source.unwrap(),
                    inner_nat: left_source
                        .ok_or("Omega could not spell a natural multiplication operand")?,
                    inner: Box::new(nat_affine_syntax(elab, cx, left, atoms)?),
                });
            }
        }
    }
    let source = format!("OfNat({nat_source})");
    let index = atoms
        .iter()
        .position(|atom| atom.nat_source.as_deref() == Some(nat_source.as_str()))
        .unwrap_or_else(|| {
            atoms.push(ReflectedAtom {
                term: Rc::clone(tm),
                source: source.clone(),
                nat_source: Some(nat_source.clone()),
            });
            atoms.len() - 1
        });
    Ok(AffineSyntax::Atom { index, source })
}

fn atom_list_source(atoms: &[ReflectedAtom]) -> String {
    atoms.iter().rev().fold("Nil".to_string(), |tail, atom| {
        format!("Cons({}, {tail})", atom.source)
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
        AffineSyntax::Add { left, right } => {
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
                source: format!("int::add({}, {})", left.source, right.source),
                linear,
                row_source,
                proof,
            })
        }
        AffineSyntax::NatAdd {
            left_nat,
            right_nat,
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
                "omega::normalize_nat_add({}, {}, {}, {}, {}, {}, {}, {}, {})",
                left_nat,
                right_nat,
                int(left.linear.constant),
                int(right.linear.constant),
                left.row_source,
                right.row_source,
                atoms_source,
                left.proof,
                right.proof,
            );
            Ok(Normalized {
                source: format!("OfNat(nat::add({}, {}))", left_nat, right_nat),
                linear,
                row_source,
                proof,
            })
        }
        AffineSyntax::Neg { inner } => {
            let inner = normalize_syntax(inner, atoms_source)?;
            let linear = inner
                .linear
                .checked_scale(-1)
                .map_err(|failure| failure.to_string())?;
            let row_source = format!("omega::scale({}, {})", int(-1), inner.row_source);
            let proof = format!(
                "omega::normalize_neg({}, {}, {}, {}, {})",
                inner.source,
                int(inner.linear.constant),
                inner.row_source,
                atoms_source,
                inner.proof,
            );
            Ok(Normalized {
                source: format!("int::neg({})", inner.source),
                linear,
                row_source,
                proof,
            })
        }
        AffineSyntax::Scale {
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
                source: if *factor_on_left {
                    format!("int::mul({}, {})", int(*factor), inner.source)
                } else {
                    format!("int::mul({}, {})", inner.source, int(*factor))
                },
                linear,
                row_source,
                proof,
            })
        }
        AffineSyntax::NatScale {
            factor,
            factor_on_left,
            factor_nat,
            inner_nat,
            inner,
        } => {
            let inner = normalize_syntax(inner, atoms_source)?;
            let linear = inner
                .linear
                .checked_scale(*factor)
                .map_err(|failure| failure.to_string())?;
            let row_source = format!("omega::scale({}, {})", int(*factor), inner.row_source);
            let lemma = if *factor_on_left {
                "omega::normalize_nat_scale_left"
            } else {
                "omega::normalize_nat_scale_right"
            };
            let proof = format!(
                "{lemma}({}, {}, {}, {}, {}, {})",
                if *factor_on_left {
                    factor_nat
                } else {
                    inner_nat
                },
                if *factor_on_left {
                    inner_nat
                } else {
                    factor_nat
                },
                int(inner.linear.constant),
                inner.row_source,
                atoms_source,
                inner.proof,
            );
            Ok(Normalized {
                source: if *factor_on_left {
                    format!("OfNat(nat::mul({}, {}))", factor_nat, inner_nat)
                } else {
                    format!("OfNat(nat::mul({}, {}))", inner_nat, factor_nat)
                },
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
        let (left, right, exact, proof) = if let Some((left, right)) = relation_args(elab, &ty) {
            if dot_args(elab, left).is_some() || dot_args(elab, right).is_some() {
                return Ok(None);
            }
            (
                affine_syntax(elab, cx, left, &mut atoms)?,
                affine_syntax(elab, cx, right, &mut atoms)?,
                false,
                cx.names[pos].clone(),
            )
        } else if let Some((left, right)) = strict_relation_args(elab, &ty) {
            let left = AffineSyntax::Add {
                left: Box::new(affine_syntax(elab, cx, left, &mut atoms)?),
                right: Box::new(AffineSyntax::Const {
                    value: 1,
                    source: int(1),
                }),
            };
            (
                left,
                affine_syntax(elab, cx, right, &mut atoms)?,
                false,
                cx.names[pos].clone(),
            )
        } else if let Some((left, right)) = equality_args(elab, cx, &ty) {
            (
                affine_syntax(elab, cx, left, &mut atoms)?,
                affine_syntax(elab, cx, right, &mut atoms)?,
                true,
                cx.names[pos].clone(),
            )
        } else if let Some((left, right)) = nat_relation_args(elab, &ty) {
            let left_source = nat_term_source(elab, cx, left)?;
            let right_source = nat_term_source(elab, cx, right)?;
            (
                nat_affine_syntax(elab, cx, left, &mut atoms)?,
                nat_affine_syntax(elab, cx, right, &mut atoms)?,
                false,
                format!(
                    "omega::nat_le_to_int({}, {}, {})",
                    left_source, right_source, cx.names[pos]
                ),
            )
        } else if let Some((left, right)) = nat_strict_relation_args(elab, &ty) {
            let left_source = nat_term_source(elab, cx, left)?;
            let right_source = nat_term_source(elab, cx, right)?;
            let left = AffineSyntax::Add {
                left: Box::new(nat_affine_syntax(elab, cx, left, &mut atoms)?),
                right: Box::new(AffineSyntax::Const {
                    value: 1,
                    source: int(1),
                }),
            };
            (
                left,
                nat_affine_syntax(elab, cx, right, &mut atoms)?,
                false,
                format!(
                    "omega::nat_lt_to_int({}, {}, {})",
                    left_source, right_source, cx.names[pos]
                ),
            )
        } else if let Some((left, right)) = nat_equality_args(elab, cx, &ty) {
            (
                nat_affine_syntax(elab, cx, left, &mut atoms)?,
                nat_affine_syntax(elab, cx, right, &mut atoms)?,
                true,
                format!("int::cong_ofnat({})", cx.names[pos]),
            )
        } else if let Some(domain) = negated_domain(elab, cx, &ty) {
            if let Some((left, right)) = relation_args(elab, &domain) {
                let left_source = int_term_source(elab, cx, left)?;
                let right_source = int_term_source(elab, cx, right)?;
                let strict_left = AffineSyntax::Add {
                    left: Box::new(affine_syntax(elab, cx, right, &mut atoms)?),
                    right: Box::new(AffineSyntax::Const {
                        value: 1,
                        source: int(1),
                    }),
                };
                (
                    strict_left,
                    affine_syntax(elab, cx, left, &mut atoms)?,
                    false,
                    format!(
                        "int::lt_of_not_le({}, {}, {})",
                        right_source, left_source, cx.names[pos]
                    ),
                )
            } else if let Some((left, right)) = strict_relation_args(elab, &domain) {
                let left_source = int_term_source(elab, cx, left)?;
                let right_source = int_term_source(elab, cx, right)?;
                (
                    affine_syntax(elab, cx, right, &mut atoms)?,
                    affine_syntax(elab, cx, left, &mut atoms)?,
                    false,
                    format!(
                        "int::le_of_not_lt({}, {}, {})",
                        left_source, right_source, cx.names[pos]
                    ),
                )
            } else if let Some((left, right)) = nat_relation_args(elab, &domain) {
                let left_source = nat_term_source(elab, cx, left)?;
                let right_source = nat_term_source(elab, cx, right)?;
                let strict_left = AffineSyntax::Add {
                    left: Box::new(nat_affine_syntax(elab, cx, right, &mut atoms)?),
                    right: Box::new(AffineSyntax::Const {
                        value: 1,
                        source: int(1),
                    }),
                };
                (
                    strict_left,
                    nat_affine_syntax(elab, cx, left, &mut atoms)?,
                    false,
                    format!(
                        "omega::nat_lt_to_int({}, {}, omega::nat_lt_of_not_le({}, {}, {}))",
                        right_source, left_source, left_source, right_source, cx.names[pos],
                    ),
                )
            } else if let Some((left, right)) = nat_strict_relation_args(elab, &domain) {
                let left_source = nat_term_source(elab, cx, left)?;
                let right_source = nat_term_source(elab, cx, right)?;
                (
                    nat_affine_syntax(elab, cx, right, &mut atoms)?,
                    nat_affine_syntax(elab, cx, left, &mut atoms)?,
                    false,
                    format!(
                        "omega::nat_le_to_int({}, {}, omega::nat_le_of_not_lt({}, {}, {}))",
                        right_source, left_source, left_source, right_source, cx.names[pos],
                    ),
                )
            } else {
                continue;
            }
        } else {
            continue;
        };
        relations.push((left, right, exact, proof));
    }
    if relations.is_empty() {
        return Ok(None);
    }
    let atoms_source = atom_list_source(&atoms);
    let mut facts = Vec::with_capacity(relations.len());
    for (left, right, exact, relation_proof) in relations {
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
        if exact {
            let equality = format!(
                "omega::normalized_eq_value({}, {}, {}, {}, {}, {}, {}, {}, {}, {})",
                left.source,
                right.source,
                int(left.linear.constant),
                int(right.linear.constant),
                left.row_source,
                right.row_source,
                atoms_source,
                left.proof,
                right.proof,
                relation_proof,
            );
            facts.push(InitialAssumption {
                coeffs: linear.coeffs,
                row_source: row_source.clone(),
                interval: Interval::exact(upper),
                lower: Some(format!(
                    "omega::lower_of_eq({}, {}, {}, {})",
                    row_source,
                    atoms_source,
                    int(upper),
                    equality,
                )),
                upper: Some(format!(
                    "omega::upper_of_eq({}, {}, {}, {})",
                    row_source,
                    atoms_source,
                    int(upper),
                    equality,
                )),
            });
        } else {
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
                relation_proof,
            );
            facts.push(InitialAssumption {
                coeffs: linear.coeffs,
                row_source,
                interval: Interval::upper(upper),
                lower: None,
                upper: Some(proof),
            });
        }
    }
    for (index, atom) in atoms.iter().enumerate() {
        let Some(nat_source) = &atom.nat_source else {
            continue;
        };
        let row_source = format!("omega::basis({index}, {atoms_source})");
        facts.push(InitialAssumption {
            coeffs: LinearExpr::atom(index).coeffs,
            row_source: row_source.clone(),
            interval: Interval::lower(0),
            lower: Some(format!(
                "omega::atom_nonnegative({}, {}, int::zero_le_ofNat({}))",
                index, atoms_source, nat_source,
            )),
            upper: None,
        });
    }
    Ok(Some((facts, atoms_source)))
}

fn int(value: Z) -> String {
    int_ctor(value)
}

fn coeffs_source(coeffs: &Coeffs) -> String {
    coeffs
        .as_slice()
        .iter()
        .rev()
        .fold("Nil".to_string(), |tail, coefficient| {
            format!("Cons({}, {tail})", int(*coefficient))
        })
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
            "omega::nat_lt_to_int({}, {}, trivial)",
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

fn parent<'a>(
    proofs: &'a [Option<BoundProof>],
    id: DerivationId,
) -> Result<&'a BoundProof, String> {
    proofs
        .get(id)
        .and_then(Option::as_ref)
        .ok_or_else(|| format!("Omega certificate parent {id} was not reconstructed"))
}

fn split_disequality(elab: &Elaborator, cx: &Cx) -> Result<Option<Certificate>, String> {
    for pos in 0..cx.names.len() {
        if cx.names[pos + 1..]
            .iter()
            .any(|name| name == &cx.names[pos])
        {
            continue;
        }
        let (_, ty, _) = elab.local(cx, pos);
        let Some(domain) = negated_domain(elab, cx, &ty) else {
            continue;
        };
        let decoded = crate::inductive::decoded(&domain);
        let Some((left, right)) = equality_args(elab, cx, &decoded) else {
            continue;
        };
        let left = int_term_source(elab, cx, left)?;
        let right = int_term_source(elab, cx, right)?;
        let disequality = &cx.names[pos];
        let source = format!(
            "omega::diseq_elim({}, {}, {disequality}, (__omega_diseq_left: {} < {}) ⊢ __omega_diseq_branch, (__omega_diseq_right: {} < {}) ⊢ __omega_diseq_branch)",
            left, right, left, right, right, left,
        );
        return Ok(Some(Certificate {
            expr: parse_generated_expr(&source)?,
            source,
            report: OmegaReport {
                atoms: 0,
                assumptions: 0,
                reachable_derivations: 0,
                logical_splits: 1,
                stats: crate::omega::Stats::default(),
                used_lemmas: vec!["omega::diseq_elim"],
            },
        }));
    }
    Ok(None)
}

fn split_connective(elab: &Elaborator, cx: &Cx) -> Result<Option<Certificate>, String> {
    for pos in 0..cx.names.len() {
        let (_, ty, _) = elab.local(cx, pos);
        let Some(tag) = elab.display_tag_of(&ty) else {
            continue;
        };
        let source = match tag.name.as_str() {
            "And" => format!(
                "omega::and_elim_false({}, __omega_and_left __omega_and_right ⊢ __omega_connective_branch)",
                cx.names[pos]
            ),
            "Or" => format!(
                "omega::or_elim_false({}, __omega_or_left ⊢ __omega_connective_branch, __omega_or_right ⊢ __omega_connective_branch)",
                cx.names[pos]
            ),
            _ => continue,
        };
        return Ok(Some(Certificate {
            expr: parse_generated_expr(&source)?,
            source,
            report: OmegaReport {
                atoms: 0,
                assumptions: 0,
                reachable_derivations: 0,
                logical_splits: 1,
                stats: crate::omega::Stats::default(),
                used_lemmas: vec![match tag.name.as_str() {
                    "And" => "omega::and_elim_false",
                    _ => "omega::or_elim_false",
                }],
            },
        }));
    }
    Ok(None)
}

pub(crate) fn reconstruct(
    elab: &Elaborator,
    cx: &Cx,
    expected: &Type,
    allow_disequality_split: bool,
    allow_connective_split: bool,
) -> Result<Certificate, String> {
    if elab
        .display_tag_of(expected)
        .is_some_and(|tag| tag.name == "And")
    {
        let source = "And(left := omega, right := omega)".to_string();
        return Ok(Certificate {
            expr: parse_generated_expr(&source)?,
            source,
            report: wrapper_report("logic::And", 0),
        });
    }
    if let Some((left, right)) = equality_args(elab, cx, expected) {
        let left = int_term_source(elab, cx, left)?;
        let right = int_term_source(elab, cx, right)?;
        // Antisymmetry keeps equality goal closure inside the already
        // certified inequality frontend. Each recursive invocation builds and
        // kernel-checks its own contradiction under the opposite strict bound.
        let source = format!("int::le_antisym({}, {}, omega, omega)", left, right);
        return Ok(Certificate {
            expr: parse_generated_expr(&source)?,
            source,
            report: wrapper_report("int::le_antisym", 0),
        });
    }
    if let Some((left, right)) = nat_equality_args(elab, cx, expected) {
        let left = nat_term_source(elab, cx, left)?;
        let right = nat_term_source(elab, cx, right)?;
        let source = format!("nat::le_antisym({}, {}, omega, omega)", left, right);
        return Ok(Certificate {
            expr: parse_generated_expr(&source)?,
            source,
            report: wrapper_report("nat::le_antisym", 0),
        });
    }
    if let Some((left, right)) = strict_relation_args(elab, expected) {
        let left = int_term_source(elab, cx, left)?;
        let right = int_term_source(elab, cx, right)?;
        let source = format!(
            "int::lt_of_not_le({}, {}, (__omega_negated_goal: {} <= {}) ⊢ omega)",
            left, right, right, left,
        );
        return Ok(Certificate {
            expr: parse_generated_expr(&source)?,
            source,
            report: wrapper_report("int::lt_of_not_le", 0),
        });
    }
    if let Some((left, right)) = relation_args(elab, expected) {
        let left = int_term_source(elab, cx, left)?;
        let right = int_term_source(elab, cx, right)?;
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
            report: wrapper_report("int::le_of_not_lt", 0),
        });
    }
    if let Some((left, right)) = nat_strict_relation_args(elab, expected) {
        let left = nat_term_source(elab, cx, left)?;
        let right = nat_term_source(elab, cx, right)?;
        let source = format!(
            "omega::nat_lt_of_not_not_lt({}, {}, (__omega_negated_goal: ¬({} < {})) ⊢ omega)",
            left, right, left, right,
        );
        return Ok(Certificate {
            expr: parse_generated_expr(&source)?,
            source,
            report: wrapper_report("omega::nat_lt_of_not_not_lt", 0),
        });
    }
    if let Some((left, right)) = nat_relation_args(elab, expected) {
        let left = nat_term_source(elab, cx, left)?;
        let right = nat_term_source(elab, cx, right)?;
        let source = format!(
            "omega::nat_le_of_not_not_le({}, {}, (__omega_negated_goal: ¬({} <= {})) ⊢ omega)",
            left, right, left, right,
        );
        return Ok(Certificate {
            expr: parse_generated_expr(&source)?,
            source,
            report: wrapper_report("omega::nat_le_of_not_not_le", 0),
        });
    }
    if elab.display_type(cx, expected) != "False" {
        return Err(format!(
            "Omega currently expects `False` or an affine `Int`/`Nat` relation goal, got `{}`",
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
            if allow_disequality_split && let Some(certificate) = split_disequality(elab, cx)? {
                return Ok(certificate);
            }
            if allow_connective_split && let Some(certificate) = split_connective(elab, cx)? {
                return Ok(certificate);
            }
            let locals = (0..cx.names.len())
                .map(|pos| {
                    let (_, ty, _) = elab.local(cx, pos);
                    format!("{}: {}", cx.names[pos], elab.display_type(cx, &ty))
                })
                .collect::<Vec<_>>()
                .join(", ");
            return Err(format!(
                "Omega found no integer constraints among [{locals}]"
            ));
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
        stats,
    } = &outcome
    else {
        if allow_disequality_split && let Some(certificate) = split_disequality(elab, cx)? {
            return Ok(certificate);
        }
        if allow_connective_split && let Some(certificate) = split_connective(elab, cx)? {
            return Ok(certificate);
        }
        let local_types = (0..cx.names.len())
            .map(|pos| {
                let (_, ty, _) = elab.local(cx, pos);
                format!("{}: {}", cx.names[pos], elab.display_type(cx, &ty))
            })
            .collect::<Vec<_>>()
            .join(", ");
        return Err(format!(
            "Omega's real shadow found no contradiction: {outcome:?}; locals [{local_types}]; reflected [{reflected_debug}]",
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
                    (Some(bound), None) => (
                        None,
                        Some(format!(
                            "omega::lower_to_negated_upper({}, {}, {}, {})",
                            source.row_source,
                            atoms_source,
                            int(bound),
                            source
                                .lower
                                .as_ref()
                                .ok_or("Omega positivization lost its lower proof")?,
                        )),
                    ),
                    (Some(lower), Some(upper)) => (
                        Some(format!(
                            "omega::upper_to_negated_lower({}, {}, {}, {})",
                            source.row_source,
                            atoms_source,
                            int(upper),
                            source
                                .upper
                                .as_ref()
                                .ok_or("Omega positivization lost its upper proof")?,
                        )),
                        Some(format!(
                            "omega::lower_to_negated_upper({}, {}, {}, {})",
                            source.row_source,
                            atoms_source,
                            int(lower),
                            source
                                .lower
                                .as_ref()
                                .ok_or("Omega positivization lost its lower proof")?,
                        )),
                    ),
                    (None, None) => return Err("Omega cannot positivize an unbounded row".into()),
                };
                BoundProof {
                    row_source,
                    interval: fact.interval,
                    lower,
                    upper,
                }
            }
            Derivation::DivideGcd {
                parent: source,
                divisor,
            } => {
                let source = parent(&proofs, source)?;
                let row_source = coeffs_source(&fact.coeffs);
                let nonnegative = format!("int::zero_le_ofNat({divisor})");
                let lower = match (source.interval.lower, fact.interval.lower) {
                    (Some(original), Some(rounded)) => {
                        let before = rounded
                            .checked_sub(1)
                            .ok_or("Omega GCD lower predecessor overflowed")?;
                        let threshold = divisor
                            .checked_mul(before)
                            .ok_or("Omega GCD lower threshold overflowed")?;
                        Some(format!(
                            "omega::divide_lower({}, {}, {}, {}, {}, {}, refl, {}, {}, {})",
                            source.row_source,
                            row_source,
                            atoms_source,
                            int(divisor),
                            int(original),
                            int(rounded),
                            nonnegative,
                            literal_lt_proof(threshold, original)?,
                            source
                                .lower
                                .as_ref()
                                .ok_or("Omega GCD division lost its lower proof")?,
                        ))
                    }
                    (None, None) => None,
                    _ => return Err("Omega GCD division changed lower-bound presence".into()),
                };
                let upper = match (source.interval.upper, fact.interval.upper) {
                    (Some(original), Some(rounded)) => {
                        let after = rounded
                            .checked_add(1)
                            .ok_or("Omega GCD upper successor overflowed")?;
                        let threshold = divisor
                            .checked_mul(after)
                            .ok_or("Omega GCD upper threshold overflowed")?;
                        Some(format!(
                            "omega::divide_upper({}, {}, {}, {}, {}, {}, refl, {}, {}, {})",
                            source.row_source,
                            row_source,
                            atoms_source,
                            int(divisor),
                            int(original),
                            int(rounded),
                            nonnegative,
                            literal_lt_proof(original, threshold)?,
                            source
                                .upper
                                .as_ref()
                                .ok_or("Omega GCD division lost its upper proof")?,
                        ))
                    }
                    (None, None) => None,
                    _ => return Err("Omega GCD division changed upper-bound presence".into()),
                };
                BoundProof {
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
                    left.row_source,
                    right.row_source,
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
                    row_source,
                    interval: fact.interval,
                    lower: Some(name),
                    upper: None,
                }
            }
            Derivation::Combo {
                left,
                left_scale,
                right,
                right_scale,
            } if left_scale < 0 && right_scale > 0 && fact.interval.upper.is_none() => {
                let left = parent(&proofs, left)?;
                let right = parent(&proofs, right)?;
                let upper = left
                    .upper
                    .as_ref()
                    .ok_or("Omega equality combination is missing its upper proof")?;
                let lower = right
                    .lower
                    .as_ref()
                    .ok_or("Omega equality combination is missing its lower proof")?;
                let u = left
                    .interval
                    .upper
                    .ok_or("Omega equality combination has no upper value")?;
                let l = right
                    .interval
                    .lower
                    .ok_or("Omega equality combination has no lower value")?;
                let magnitude = left_scale
                    .checked_neg()
                    .ok_or("Omega equality combination scale overflowed")?;
                let name = format!("__omega_generated_{id}");
                // The certificate row is commuted so it matches the existing
                // positive-lower/negative-upper theorem. Its concrete
                // coefficients are the same row replayed by the solver.
                let row_source = format!(
                    "omega::combo({}, {}, {}, {})",
                    int(right_scale),
                    right.row_source,
                    int(left_scale),
                    left.row_source,
                );
                let expression = format!(
                    "omega::lower_upper_combo({}, {}, {}, {}, {}, {}, {}, int::zero_le_ofNat({}), int::zero_le_ofNat({}), {}, {})",
                    int(right_scale),
                    int(magnitude),
                    right.row_source,
                    left.row_source,
                    atoms_source,
                    int(l),
                    int(u),
                    right_scale,
                    magnitude,
                    lower,
                    upper,
                );
                bindings.push(format!("let {name} = {expression};"));
                BoundProof {
                    row_source,
                    interval: fact.interval,
                    lower: Some(name),
                    upper: None,
                }
            }
            Derivation::Combo {
                left,
                left_scale,
                right,
                right_scale,
            } if left_scale < 0 && right_scale > 0 && fact.interval.lower.is_none() => {
                let left = parent(&proofs, left)?;
                let right = parent(&proofs, right)?;
                let lower = left
                    .lower
                    .as_ref()
                    .ok_or("Omega upper equality combination is missing its lower proof")?;
                let upper = right
                    .upper
                    .as_ref()
                    .ok_or("Omega upper equality combination is missing its upper proof")?;
                let l = left
                    .interval
                    .lower
                    .ok_or("Omega upper equality combination has no lower value")?;
                let u = right
                    .interval
                    .upper
                    .ok_or("Omega upper equality combination has no upper value")?;
                let magnitude = left_scale
                    .checked_neg()
                    .ok_or("Omega upper equality combination scale overflowed")?;
                let name = format!("__omega_generated_{id}");
                let row_source = format!(
                    "omega::combo({}, {}, {}, {})",
                    int(left_scale),
                    left.row_source,
                    int(right_scale),
                    right.row_source,
                );
                let expression = format!(
                    "omega::upper_lower_combo({}, {}, {}, {}, {}, {}, {}, int::zero_le_ofNat({}), int::zero_le_ofNat({}), {}, {})",
                    int(magnitude),
                    int(right_scale),
                    left.row_source,
                    right.row_source,
                    atoms_source,
                    int(l),
                    int(u),
                    magnitude,
                    right_scale,
                    lower,
                    upper,
                );
                bindings.push(format!("let {name} = {expression};"));
                BoundProof {
                    row_source,
                    interval: fact.interval,
                    lower: None,
                    upper: Some(name),
                }
            }
            Derivation::Combo {
                left,
                left_scale,
                right,
                right_scale,
            } if left_scale > 0 && right_scale > 0 && fact.interval.upper.is_none() => {
                let left = parent(&proofs, left)?;
                let right = parent(&proofs, right)?;
                let left_lower = left
                    .lower
                    .as_ref()
                    .ok_or("Omega positive combination is missing its left lower proof")?;
                let right_lower = right
                    .lower
                    .as_ref()
                    .ok_or("Omega positive combination is missing its right lower proof")?;
                let l = left
                    .interval
                    .lower
                    .ok_or("Omega positive combination has no left lower value")?;
                let r = right
                    .interval
                    .lower
                    .ok_or("Omega positive combination has no right lower value")?;
                let name = format!("__omega_generated_{id}");
                let row_source = format!(
                    "omega::combo({}, {}, {}, {})",
                    int(left_scale),
                    left.row_source,
                    int(right_scale),
                    right.row_source,
                );
                let expression = format!(
                    "omega::lower_combo({}, {}, {}, {}, {}, {}, {}, int::zero_le_ofNat({}), int::zero_le_ofNat({}), {}, {})",
                    int(left_scale),
                    int(right_scale),
                    left.row_source,
                    right.row_source,
                    atoms_source,
                    int(l),
                    int(r),
                    left_scale,
                    right_scale,
                    left_lower,
                    right_lower,
                );
                bindings.push(format!("let {name} = {expression};"));
                BoundProof {
                    row_source,
                    interval: fact.interval,
                    lower: Some(name),
                    upper: None,
                }
            }
            Derivation::Combo {
                left,
                left_scale,
                right,
                right_scale,
            } if left_scale > 0 && right_scale > 0 && fact.interval.lower.is_none() => {
                let left = parent(&proofs, left)?;
                let right = parent(&proofs, right)?;
                let left_upper = left
                    .upper
                    .as_ref()
                    .ok_or("Omega positive combination is missing its left upper proof")?;
                let right_upper = right
                    .upper
                    .as_ref()
                    .ok_or("Omega positive combination is missing its right upper proof")?;
                let l = left
                    .interval
                    .upper
                    .ok_or("Omega positive combination has no left upper value")?;
                let r = right
                    .interval
                    .upper
                    .ok_or("Omega positive combination has no right upper value")?;
                let name = format!("__omega_generated_{id}");
                let row_source = format!(
                    "omega::combo({}, {}, {}, {})",
                    int(left_scale),
                    left.row_source,
                    int(right_scale),
                    right.row_source,
                );
                let expression = format!(
                    "omega::upper_combo({}, {}, {}, {}, {}, {}, {}, int::zero_le_ofNat({}), int::zero_le_ofNat({}), {}, {})",
                    int(left_scale),
                    int(right_scale),
                    left.row_source,
                    right.row_source,
                    atoms_source,
                    int(l),
                    int(r),
                    left_scale,
                    right_scale,
                    left_upper,
                    right_upper,
                );
                bindings.push(format!("let {name} = {expression};"));
                BoundProof {
                    row_source,
                    interval: fact.interval,
                    lower: None,
                    upper: Some(name),
                }
            }
            Derivation::Constant {
                parent: source,
                impossible,
            } if impossible => {
                let source = parent(&proofs, source)?;
                BoundProof {
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

    if let Derivation::Constant {
        parent: source_id,
        impossible: true,
    } = problem.dag.nodes()[derivation]
    {
        let constant = parent(&proofs, source_id)?;
        let result = if let Some(lower) = constant.interval.lower.filter(|lower| *lower > 0) {
            format!(
                "omega::impossible_constant_lower({}, {}, {}, {}, omega::dot_zeros({}), {})",
                constant.row_source,
                atoms_source,
                int(lower),
                constant
                    .lower
                    .as_ref()
                    .ok_or("Omega constant contradiction lost its lower proof")?,
                atoms_source,
                literal_lt_proof(0, lower)?,
            )
        } else if let Some(upper) = constant.interval.upper.filter(|upper| *upper < 0) {
            format!(
                "omega::impossible_constant_upper({}, {}, {}, {}, omega::dot_zeros({}), {})",
                constant.row_source,
                atoms_source,
                int(upper),
                constant
                    .upper
                    .as_ref()
                    .ok_or("Omega constant contradiction lost its upper proof")?,
                atoms_source,
                literal_lt_proof(upper, 0)?,
            )
        } else {
            return Err("Omega constant contradiction still contains zero".into());
        };
        let source = if bindings.is_empty() {
            result
        } else {
            format!("{{ {} {} }}", bindings.join(" "), result)
        };
        let expr = parse_generated_expr(&source)
            .map_err(|error| format!("{error}\n  generated Omega source: {source}"))?;
        let used_lemmas = reconstruction_lemmas(&source);
        return Ok(Certificate {
            expr,
            source,
            report: OmegaReport {
                atoms: atoms_source.matches("Cons(").count(),
                assumptions: reflected.len(),
                reachable_derivations: reachable_derivations.len(),
                logical_splits: 0,
                stats: *stats,
                used_lemmas,
            },
        });
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
    let expr = parse_generated_expr(&source)
        .map_err(|error| format!("{error}\n  generated Omega source: {source}"))?;
    let used_lemmas = reconstruction_lemmas(&source);
    Ok(Certificate {
        expr,
        source,
        report: OmegaReport {
            atoms: atoms_source.matches("Cons(").count(),
            assumptions: reflected.len(),
            reachable_derivations: reachable_derivations.len(),
            logical_splits: 0,
            stats: *stats,
            used_lemmas,
        },
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
