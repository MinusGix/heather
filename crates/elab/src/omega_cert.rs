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

use crate::arithmetic::{
    Affine, AtomId, AtomTable, Coeffs as AffineCoeffs, Domain, ReflectedConstraint, Relation,
};
use crate::cutsat::{
    Derivation as CutDerivation, DerivedConstraint, Limits as CutLimits, Outcome as CutOutcome,
    Problem as CutProblem,
};
use crate::omega::{Coeffs, Derivation, DerivationId, Interval, LinearExpr, Outcome, Problem, Z};
use crate::{Cx, Elaborator};

pub(crate) struct CertificateScope<'a> {
    depth: &'a std::cell::Cell<usize>,
    outer: usize,
}

impl<'a> CertificateScope<'a> {
    pub(crate) fn enter(depth: &'a std::cell::Cell<usize>) -> Self {
        let outer = depth.get();
        depth.set(outer + 1);
        Self { depth, outer }
    }
}

impl Drop for CertificateScope<'_> {
    fn drop(&mut self) {
        self.depth.set(self.outer);
    }
}

pub(crate) struct Certificate {
    pub expr: Expr,
    pub source: String,
    pub report: OmegaReport,
}

fn parse_generated_expr(source: &str) -> Result<Expr, String> {
    timed(|p| &mut p.parse_ns, || parse_generated_expr_untimed(source))
}

fn parse_generated_expr_untimed(source: &str) -> Result<Expr, String> {
    let wrapper = format!("theorem __omega_generated(): 0 = 0 {{ {source} }}");
    let mut file = parse_file(&wrapper).map_err(|error| error.msg)?;
    let Some(Item::Decl(decl)) = file.items.pop() else {
        return Err("the generated Omega proof wrapper did not parse as a theorem".into());
    };
    Ok(*decl.body.result)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OmegaResidualConstraint {
    pub coefficients: Vec<Z>,
    pub lower: Option<Z>,
    pub upper: Option<Z>,
    pub rendered: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OmegaReport {
    pub atoms: usize,
    pub atom_labels: Vec<String>,
    pub assumptions: usize,
    pub reachable_derivations: usize,
    pub total_derivations: usize,
    pub discarded_derivations: usize,
    pub logical_splits: usize,
    pub stats: crate::omega::Stats,
    pub used_lemmas: Vec<&'static str>,
    pub residual: Vec<OmegaResidualConstraint>,
    pub cutsat: Option<CutSatReport>,
    pub phases: OmegaPhases,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CutSatReport {
    pub reachable_derivations: usize,
    pub total_derivations: usize,
    pub stats: crate::cutsat::Stats,
}

/// Where one `omega` invocation's wall time went. Search phases are measured
/// inside [`reconstruct`]; `reconstruct_ns` and `check_ns` are stamped by the
/// dispatcher in `lib.rs` around the whole reconstruction and around the
/// checking of the generated certificate. `check_ns` is inclusive: a
/// certificate that re-invokes `omega` (`le_of_not_lt(… ⊢ omega)`, every
/// `__cutsat_linear_branch`) pays for those nested invocations inside it, so
/// `depth` says which reports are inner ones.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct OmegaPhases {
    pub depth: usize,
    pub source_len: usize,
    pub reflect_ns: u64,
    pub omega_search_ns: u64,
    pub cutsat_search_ns: u64,
    pub render_ns: u64,
    pub parse_ns: u64,
    pub reconstruct_ns: u64,
    pub check_ns: u64,
}

thread_local! {
    static PHASES: std::cell::Cell<OmegaPhases> = std::cell::Cell::new(OmegaPhases::default());
}

/// Run `f`, adding its duration to the named phase of the reconstruction in
/// progress. Reconstructions never nest (nested `omega` uses happen while the
/// outer certificate is *checked*, after its reconstruction returned), so one
/// thread-local accumulator per thread is enough.
fn timed<T>(phase: fn(&mut OmegaPhases) -> &mut u64, f: impl FnOnce() -> T) -> T {
    let start = std::time::Instant::now();
    let out = f();
    let ns = start.elapsed().as_nanos() as u64;
    PHASES.with(|c| {
        let mut phases = c.get();
        *phase(&mut phases) = phase(&mut phases).saturating_add(ns);
        c.set(phases);
    });
    out
}

/// Zero the phase accumulator; the dispatcher calls this before [`reconstruct`].
pub(crate) fn reset_phases() {
    PHASES.with(|c| c.set(OmegaPhases::default()));
}

/// The phases accumulated since [`reset_phases`].
pub(crate) fn phases() -> OmegaPhases {
    PHASES.with(|c| c.get())
}

fn wrapper_report(lemma: &'static str, logical_splits: usize) -> OmegaReport {
    OmegaReport {
        atoms: 0,
        atom_labels: Vec::new(),
        assumptions: 0,
        reachable_derivations: 0,
        total_derivations: 0,
        discarded_derivations: 0,
        logical_splits,
        stats: crate::omega::Stats::default(),
        used_lemmas: vec![lemma],
        residual: Vec::new(),
        cutsat: None,
        phases: OmegaPhases::default(),
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
        "omega::div_lower",
        "omega::div_lower_nonzero",
        "omega::div_upper",
        "omega::div_upper_nonzero",
        "omega::eq_of_bounds",
        "omega::exact_combo",
        "omega::impossible_constant_lower",
        "omega::impossible_constant_upper",
        "omega::lower_combo",
        "omega::lower_neg_combo",
        "omega::lower_of_eq",
        "omega::lower_to_negated_upper",
        "omega::normalize_mod",
        "omega::normalize_div_zero",
        "omega::normalize_mod_zero",
        "omega::nat_div_lower",
        "omega::nat_div_upper",
        "omega::nat_diseq_elim",
        "omega::normalize_nat_mod",
        "omega::normalize_nat_div_zero",
        "omega::normalize_nat_mod_zero",
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
        "omega::upper_neg_combo",
        "omega::upper_lower_combo",
        "omega::upper_lower_lower_combo",
        "omega::lower_upper_upper_combo",
        "omega::upper_of_eq",
        "omega::upper_to_negated_lower",
        "omega::cut_dvd_elim",
        "omega::cutsat_cooper_left",
        "omega::cutsat_cooper_right",
        "omega::cutsat_negative_remainder",
        "omega::cutsat_with_eq",
        "omega::cutsat_with_le",
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
    exact: Option<String>,
}

fn reflected_atom_count(facts: &[InitialAssumption]) -> usize {
    facts
        .iter()
        .map(|fact| fact.coeffs.as_slice().len())
        .max()
        .unwrap_or(0)
}

fn indexed_atom_labels(count: usize) -> Vec<String> {
    (0..count).map(|index| format!("atom[{index}]")).collect()
}

fn render_linear(coefficients: &[Z], atom_labels: &[String]) -> String {
    let mut rendered = String::new();
    for (index, &coefficient) in coefficients.iter().enumerate() {
        if coefficient == 0 {
            continue;
        }
        let atom = atom_labels
            .get(index)
            .cloned()
            .unwrap_or_else(|| format!("aux[{}]", index - atom_labels.len()));
        let magnitude = coefficient.unsigned_abs();
        let term = if magnitude == 1 {
            atom
        } else {
            format!("{magnitude} * {atom}")
        };
        if rendered.is_empty() {
            if coefficient < 0 {
                rendered.push('-');
            }
            rendered.push_str(&term);
        } else if coefficient < 0 {
            rendered.push_str(" - ");
            rendered.push_str(&term);
        } else {
            rendered.push_str(" + ");
            rendered.push_str(&term);
        }
    }
    if rendered.is_empty() {
        rendered.push('0');
    }
    rendered
}

fn render_residual(
    coefficients: &[Z],
    lower: Option<Z>,
    upper: Option<Z>,
    atom_labels: &[String],
) -> String {
    let linear = render_linear(coefficients, atom_labels);
    match (lower, upper) {
        (Some(lower), Some(upper)) if lower == upper => format!("{linear} = {lower}"),
        (Some(lower), Some(upper)) => format!("{lower} <= {linear} <= {upper}"),
        (Some(lower), None) => format!("{lower} <= {linear}"),
        (None, Some(upper)) => format!("{linear} <= {upper}"),
        (None, None) => linear,
    }
}

#[derive(Clone)]
enum AffineSyntax {
    Const {
        value: Z,
        source: String,
    },
    Atom {
        index: AtomId,
        source: String,
    },
    Mod {
        source: String,
        dividend_source: String,
        divisor_source: String,
        expanded: Box<AffineSyntax>,
    },
    DivZero {
        source: String,
        dividend_source: String,
    },
    ModZero {
        source: String,
        dividend_source: String,
        dividend: Box<AffineSyntax>,
    },
    NatMod {
        source: String,
        dividend_source: String,
        divisor_source: String,
        expanded: Box<AffineSyntax>,
    },
    NatDivZero {
        source: String,
        dividend_source: String,
    },
    NatModZero {
        source: String,
        dividend_source: String,
        dividend: Box<AffineSyntax>,
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
    division: Option<DivisionAtom>,
}

#[derive(Clone)]
struct DivisionAtom {
    dividend: AffineSyntax,
    dividend_source: String,
    divisor: Z,
    natural: bool,
}

#[derive(Clone)]
struct BoundProof {
    row_source: String,
    interval: Interval,
    lower: Option<String>,
    upper: Option<String>,
    exact: Option<String>,
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

fn int_divides_args<'a>(elab: &Elaborator, ty: &'a Type) -> Option<(&'a Rc<Term>, &'a Rc<Term>)> {
    let Type::El { tm, .. } = ty else {
        return None;
    };
    let args = named_args(elab, tm, "int::Divides")?;
    let [divisor, dividend] = args.as_slice() else {
        return None;
    };
    Some((divisor, dividend))
}

fn nat_divides_args<'a>(elab: &Elaborator, ty: &'a Type) -> Option<(&'a Rc<Term>, &'a Rc<Term>)> {
    let Type::El { tm, .. } = ty else {
        return None;
    };
    let args = named_args(elab, tm, "nat::Divides")?;
    let [divisor, dividend] = args.as_slice() else {
        return None;
    };
    Some((divisor, dividend))
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
    let source = source.strip_prefix("int::").unwrap_or(source);
    let compact: String = source.chars().filter(|c| !c.is_whitespace()).collect();
    if let Ok(value) = compact.parse() {
        return Some(value);
    }
    // `nat_term_source` deliberately preserves kernel constructors instead
    // of asking the surface printer to turn a numeral back into decimal.
    // Keep that stable spelling usable as a literal too: otherwise a
    // structural divisor becomes an opaque atom and never receives its
    // certified division bounds.
    let mut structural = compact.as_str();
    let mut value = 0i128;
    while let Some(inner) = structural
        .strip_prefix("Succ(")
        .and_then(|s| s.strip_suffix(')'))
    {
        value = value.checked_add(1)?;
        structural = inner;
    }
    if structural == "0" {
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
        if self.token(b"OfNat") || self.token(b"int::OfNat") {
            self.token(b"(").then_some(())?;
            let value = self.signed_number()?;
            if value < 0 || !self.token(b")") {
                return None;
            }
            return Some(value);
        }
        if self.token(b"NegSucc") || self.token(b"int::NegSucc") {
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
        if self.token(b"Nil") || self.token(b"list::Nil") {
            return Some(());
        }
        if !(self.token(b"Cons") || self.token(b"list::Cons")) || !self.token(b"(") {
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

// Resolve each visible name once through the same binder/alias precedence as
// ordinary expressions. Alias types are weakened to this context by resolve.
fn local_facts(elab: &Elaborator, cx: &Cx) -> Vec<(String, Type)> {
    let mut seen = std::collections::HashSet::new();
    cx.names
        .iter()
        .chain(cx.aliases.iter().map(|alias| &alias.name))
        .filter(|name| seen.insert((*name).clone()))
        .filter_map(|name| {
            elab.resolve(cx, name, heather_syntax::Span { start: 0, end: 0 })
                .ok()
                .map(|(_, ty, _)| (name.clone(), ty))
        })
        .collect()
}

fn reflect_assumption(
    elab: &Elaborator,
    cx: &Cx,
    name: &str,
    ty: &Type,
) -> Result<Option<ReflectedAssumption>, String> {
    let Some((left, right)) = relation_args(elab, ty) else {
        return Ok(None);
    };
    let (coeff_term, atoms, interval) = if let Some((coeffs, atoms)) = dot_args(elab, right) {
        let lower_source = elab
            .spell_term_clean(cx, left)
            .ok_or_else(|| format!("Omega could not spell the lower bound in `{}`", name))?;
        let lower = integer_source(&lower_source)
            .ok_or_else(|| format!("Omega requires a literal lower bound, got `{lower_source}`"))?;
        (coeffs, atoms, Interval::lower(lower))
    } else if let Some((coeffs, atoms)) = dot_args(elab, left) {
        let upper_source = elab
            .spell_term_clean(cx, right)
            .ok_or_else(|| format!("Omega could not spell the upper bound in `{}`", name))?;
        let upper = integer_source(&upper_source)
            .ok_or_else(|| format!("Omega requires a literal upper bound, got `{upper_source}`"))?;
        (coeffs, atoms, Interval::upper(upper))
    } else {
        return Ok(None);
    };
    let coeff_source = elab
        .spell_term_clean(cx, coeff_term)
        .ok_or_else(|| format!("Omega could not spell the coefficient row in `{}`", name))?;
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
        .ok_or_else(|| format!("Omega could not spell the atom row in `{}`", name))?;
    Ok(Some(ReflectedAssumption {
        name: name.to_string(),
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
    atoms: &mut AtomTable<ReflectedAtom>,
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
    if let Some(args) = named_args(elab, tm, "int::mod")
        && let [dividend, divisor] = args.as_slice()
    {
        let divisor_source = int_term_source(elab, cx, divisor)?;
        if let Some(divisor) = integer_source(&divisor_source) {
            let dividend_source = int_term_source(elab, cx, dividend)?;
            let dividend_syntax = affine_syntax(elab, cx, dividend, atoms)?;
            if divisor == 0 {
                return Ok(AffineSyntax::ModZero {
                    source,
                    dividend_source,
                    dividend: Box::new(dividend_syntax),
                });
            }
            divisor
                .checked_abs()
                .ok_or("Omega cannot reflect division by the minimum `i128` literal")?;
            let quotient_source = format!("int::div({}, {})", dividend_source, int(divisor));
            let quotient_index = atoms.intern_by(
                |atom| atom.source == quotient_source,
                || ReflectedAtom {
                    term: Rc::clone(tm),
                    source: quotient_source.clone(),
                    nat_source: None,
                    division: Some(DivisionAtom {
                        dividend: dividend_syntax.clone(),
                        dividend_source: dividend_source.clone(),
                        divisor,
                        natural: false,
                    }),
                },
            );
            let quotient = AffineSyntax::Atom {
                index: quotient_index,
                source: quotient_source,
            };
            let expanded = AffineSyntax::Add {
                left: Box::new(dividend_syntax),
                right: Box::new(AffineSyntax::Neg {
                    inner: Box::new(AffineSyntax::Scale {
                        factor: divisor,
                        factor_on_left: false,
                        inner: Box::new(quotient),
                    }),
                }),
            };
            return Ok(AffineSyntax::Mod {
                source,
                dividend_source,
                divisor_source: int(divisor),
                expanded: Box::new(expanded),
            });
        }
    }
    if let Some(args) = named_args(elab, tm, "int::div")
        && let [dividend, divisor] = args.as_slice()
    {
        let divisor_source = int_term_source(elab, cx, divisor)?;
        if let Some(divisor) = integer_source(&divisor_source) {
            let dividend_source = int_term_source(elab, cx, dividend)?;
            let dividend_syntax = affine_syntax(elab, cx, dividend, atoms)?;
            if divisor == 0 {
                return Ok(AffineSyntax::DivZero {
                    source,
                    dividend_source,
                });
            }
            divisor
                .checked_abs()
                .ok_or("Omega cannot reflect division by the minimum `i128` literal")?;
            let index = atoms.intern_by(
                |atom| *atom.term == **tm || atom.source == source,
                || ReflectedAtom {
                    term: Rc::clone(tm),
                    source: source.clone(),
                    nat_source: None,
                    division: Some(DivisionAtom {
                        dividend: dividend_syntax,
                        dividend_source,
                        divisor,
                        natural: false,
                    }),
                },
            );
            return Ok(AffineSyntax::Atom { index, source });
        }
    }

    let index = atoms.intern_by(
        |atom| *atom.term == **tm || atom.source == source,
        || ReflectedAtom {
            term: Rc::clone(tm),
            source: source.clone(),
            nat_source: None,
            division: None,
        },
    );
    Ok(AffineSyntax::Atom { index, source })
}

fn int_term_source(elab: &Elaborator, cx: &Cx, tm: &Rc<Term>) -> Result<String, String> {
    for (name, arity) in [
        ("int::add", 2usize),
        ("int::sub", 2),
        ("int::mul", 2),
        ("int::neg", 1),
        ("int::div", 2),
        ("int::mod", 2),
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
    match &**tm {
        Term::Zero => return Ok("0".into()),
        Term::Succ(inner) => {
            return Ok(format!("Succ({})", nat_term_source(elab, cx, inner)?));
        }
        _ => {}
    }
    for name in ["nat::add", "nat::mul", "nat::div", "nat::mod"] {
        if let Some(args) = named_args(elab, tm, name)
            && let [left, right] = args.as_slice()
        {
            return Ok(format!(
                "{name}({}, {})",
                nat_term_source(elab, cx, left)?,
                nat_term_source(elab, cx, right)?,
            ));
        }
    }
    elab.spell_term_clean(cx, tm)
        .ok_or_else(|| "Omega could not spell a natural expression".to_string())
}

fn nat_affine_syntax(
    elab: &Elaborator,
    cx: &Cx,
    tm: &Rc<Term>,
    atoms: &mut AtomTable<ReflectedAtom>,
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
    if let Some(args) = named_args(elab, tm, "nat::mod")
        && let [dividend, divisor] = args.as_slice()
    {
        let divisor_source = nat_term_source(elab, cx, divisor)?;
        if let Some(divisor) = integer_source(&divisor_source).filter(|value| *value >= 0) {
            let dividend_source = nat_term_source(elab, cx, dividend)?;
            let dividend_syntax = nat_affine_syntax(elab, cx, dividend, atoms)?;
            let source = format!("int::OfNat({nat_source})");
            if divisor == 0 {
                return Ok(AffineSyntax::NatModZero {
                    source,
                    dividend_source,
                    dividend: Box::new(dividend_syntax),
                });
            }
            let quotient_nat = format!("nat::div({}, {})", dividend_source, divisor_source);
            let quotient_source = format!("int::OfNat({quotient_nat})");
            let quotient_index = atoms.intern_by(
                |atom| atom.nat_source.as_deref() == Some(quotient_nat.as_str()),
                || ReflectedAtom {
                    term: Rc::clone(tm),
                    source: quotient_source.clone(),
                    nat_source: Some(quotient_nat.clone()),
                    division: Some(DivisionAtom {
                        dividend: dividend_syntax.clone(),
                        dividend_source: dividend_source.clone(),
                        divisor,
                        natural: true,
                    }),
                },
            );
            let expanded = AffineSyntax::Add {
                left: Box::new(dividend_syntax),
                right: Box::new(AffineSyntax::Neg {
                    inner: Box::new(AffineSyntax::Scale {
                        factor: divisor,
                        factor_on_left: false,
                        inner: Box::new(AffineSyntax::Atom {
                            index: quotient_index,
                            source: quotient_source,
                        }),
                    }),
                }),
            };
            return Ok(AffineSyntax::NatMod {
                source,
                dividend_source,
                divisor_source,
                expanded: Box::new(expanded),
            });
        }
    }
    if let Some(args) = named_args(elab, tm, "nat::div")
        && let [dividend, divisor] = args.as_slice()
    {
        let divisor_source = nat_term_source(elab, cx, divisor)?;
        if let Some(divisor) = integer_source(&divisor_source).filter(|value| *value >= 0) {
            let dividend_source = nat_term_source(elab, cx, dividend)?;
            let source = format!("int::OfNat({nat_source})");
            if divisor == 0 {
                return Ok(AffineSyntax::NatDivZero {
                    source,
                    dividend_source,
                });
            }
            let dividend_syntax = nat_affine_syntax(elab, cx, dividend, atoms)?;
            let index = atoms.intern_by(
                |atom| atom.nat_source.as_deref() == Some(nat_source.as_str()),
                || ReflectedAtom {
                    term: Rc::clone(tm),
                    source: source.clone(),
                    nat_source: Some(nat_source.clone()),
                    division: Some(DivisionAtom {
                        dividend: dividend_syntax,
                        dividend_source,
                        divisor,
                        natural: true,
                    }),
                },
            );
            return Ok(AffineSyntax::Atom { index, source });
        }
    }
    let source = format!("int::OfNat({nat_source})");
    let index = atoms.intern_by(
        |atom| atom.nat_source.as_deref() == Some(nat_source.as_str()),
        || ReflectedAtom {
            term: Rc::clone(tm),
            source: source.clone(),
            nat_source: Some(nat_source.clone()),
            division: None,
        },
    );
    Ok(AffineSyntax::Atom { index, source })
}

fn atom_list_source(atoms: &AtomTable<ReflectedAtom>) -> String {
    atoms
        .iter()
        .rev()
        .fold("list::Nil".to_string(), |tail, atom| {
            format!("list::Cons({}, {tail})", atom.source)
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
            let index = index.index();
            let row_source = format!("omega::basis({index}, {atoms_source})");
            Ok(Normalized {
                source: source.clone(),
                linear: LinearExpr::atom(index),
                proof: format!("omega::normalize_atom({index}, {atoms_source})"),
                row_source,
            })
        }
        AffineSyntax::Mod {
            source,
            dividend_source,
            divisor_source,
            expanded,
        } => {
            let expanded = normalize_syntax(expanded, atoms_source)?;
            let proof = format!(
                "omega::normalize_mod({}, {}, {}, {}, {}, {})",
                dividend_source,
                divisor_source,
                int(expanded.linear.constant),
                expanded.row_source,
                atoms_source,
                expanded.proof,
            );
            Ok(Normalized {
                source: source.clone(),
                linear: expanded.linear,
                row_source: expanded.row_source,
                proof,
            })
        }
        AffineSyntax::DivZero {
            source,
            dividend_source,
        } => {
            let row_source = format!("omega::zeros({atoms_source})");
            Ok(Normalized {
                source: source.clone(),
                linear: LinearExpr::constant(0),
                proof: format!(
                    "omega::normalize_div_zero({}, {})",
                    dividend_source, atoms_source
                ),
                row_source,
            })
        }
        AffineSyntax::ModZero {
            source,
            dividend_source,
            dividend,
        } => {
            let dividend = normalize_syntax(dividend, atoms_source)?;
            let proof = format!(
                "omega::normalize_mod_zero({}, {}, {}, {}, {})",
                dividend_source,
                int(dividend.linear.constant),
                dividend.row_source,
                atoms_source,
                dividend.proof,
            );
            Ok(Normalized {
                source: source.clone(),
                linear: dividend.linear,
                row_source: dividend.row_source,
                proof,
            })
        }
        AffineSyntax::NatMod {
            source,
            dividend_source,
            divisor_source,
            expanded,
        } => {
            let expanded = normalize_syntax(expanded, atoms_source)?;
            let proof = format!(
                "omega::normalize_nat_mod({}, {}, {}, {}, {}, {})",
                dividend_source,
                divisor_source,
                int(expanded.linear.constant),
                expanded.row_source,
                atoms_source,
                expanded.proof,
            );
            Ok(Normalized {
                source: source.clone(),
                linear: expanded.linear,
                row_source: expanded.row_source,
                proof,
            })
        }
        AffineSyntax::NatDivZero {
            source,
            dividend_source,
        } => {
            let row_source = format!("omega::zeros({atoms_source})");
            Ok(Normalized {
                source: source.clone(),
                linear: LinearExpr::constant(0),
                proof: format!(
                    "omega::normalize_nat_div_zero({}, {})",
                    dividend_source, atoms_source
                ),
                row_source,
            })
        }
        AffineSyntax::NatModZero {
            source,
            dividend_source,
            dividend,
        } => {
            let dividend = normalize_syntax(dividend, atoms_source)?;
            let proof = format!(
                "omega::normalize_nat_mod_zero({}, {}, {}, {}, {})",
                dividend_source,
                int(dividend.linear.constant),
                dividend.row_source,
                atoms_source,
                dividend.proof,
            );
            Ok(Normalized {
                source: source.clone(),
                linear: dividend.linear,
                row_source: dividend.row_source,
                proof,
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
                source: format!("int::OfNat(nat::add({}, {}))", left_nat, right_nat),
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
                    format!("int::OfNat(nat::mul({}, {}))", factor_nat, inner_nat)
                } else {
                    format!("int::OfNat(nat::mul({}, {}))", inner_nat, factor_nat)
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
) -> Result<Option<(Vec<InitialAssumption>, String, Vec<String>, Vec<String>)>, String> {
    let mut atoms = AtomTable::default();
    let mut relations = Vec::new();
    for (name, ty) in local_facts(elab, cx) {
        if name.starts_with("__cutsat_nat_eq_") || name.starts_with("__cutsat_int_eq_") {
            continue;
        }
        let decoded_ty = crate::inductive::decoded(&ty);
        let (domain, left, right, relation, proof) =
            if let Some((left, right)) = relation_args(elab, &ty) {
                if dot_args(elab, left).is_some() || dot_args(elab, right).is_some() {
                    return Ok(None);
                }
                (
                    Domain::Int,
                    affine_syntax(elab, cx, left, &mut atoms)?,
                    affine_syntax(elab, cx, right, &mut atoms)?,
                    Relation::Le,
                    name.clone(),
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
                    Domain::Int,
                    left,
                    affine_syntax(elab, cx, right, &mut atoms)?,
                    Relation::Le,
                    name.clone(),
                )
            } else if let Some((left, right)) =
                equality_args(elab, cx, &ty).or_else(|| equality_args(elab, cx, &decoded_ty))
            {
                (
                    Domain::Int,
                    affine_syntax(elab, cx, left, &mut atoms)?,
                    affine_syntax(elab, cx, right, &mut atoms)?,
                    Relation::Eq,
                    name.clone(),
                )
            } else if let Some((left, right)) = nat_relation_args(elab, &ty) {
                let left_source = nat_term_source(elab, cx, left)?;
                let right_source = nat_term_source(elab, cx, right)?;
                (
                    Domain::NatEmbedded,
                    nat_affine_syntax(elab, cx, left, &mut atoms)?,
                    nat_affine_syntax(elab, cx, right, &mut atoms)?,
                    Relation::Le,
                    format!(
                        "omega::nat_le_to_int({}, {}, {})",
                        left_source, right_source, name
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
                    Domain::NatEmbedded,
                    left,
                    nat_affine_syntax(elab, cx, right, &mut atoms)?,
                    Relation::Le,
                    format!(
                        "omega::nat_lt_to_int({}, {}, {})",
                        left_source, right_source, name
                    ),
                )
            } else if let Some((left, right)) = nat_equality_args(elab, cx, &ty)
                .or_else(|| nat_equality_args(elab, cx, &decoded_ty))
            {
                (
                    Domain::NatEmbedded,
                    nat_affine_syntax(elab, cx, left, &mut atoms)?,
                    nat_affine_syntax(elab, cx, right, &mut atoms)?,
                    Relation::Eq,
                    format!("int::cong_ofnat({})", name),
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
                        Domain::Int,
                        strict_left,
                        affine_syntax(elab, cx, left, &mut atoms)?,
                        Relation::Le,
                        format!(
                            "int::lt_of_not_le({}, {}, {})",
                            right_source, left_source, name
                        ),
                    )
                } else if let Some((left, right)) = strict_relation_args(elab, &domain) {
                    let left_source = int_term_source(elab, cx, left)?;
                    let right_source = int_term_source(elab, cx, right)?;
                    (
                        Domain::Int,
                        affine_syntax(elab, cx, right, &mut atoms)?,
                        affine_syntax(elab, cx, left, &mut atoms)?,
                        Relation::Le,
                        format!(
                            "int::le_of_not_lt({}, {}, {})",
                            left_source, right_source, name
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
                        Domain::NatEmbedded,
                        strict_left,
                        nat_affine_syntax(elab, cx, left, &mut atoms)?,
                        Relation::Le,
                        format!(
                            "omega::nat_lt_to_int({}, {}, omega::nat_lt_of_not_le({}, {}, {}))",
                            right_source, left_source, left_source, right_source, name,
                        ),
                    )
                } else if let Some((left, right)) = nat_strict_relation_args(elab, &domain) {
                    let left_source = nat_term_source(elab, cx, left)?;
                    let right_source = nat_term_source(elab, cx, right)?;
                    (
                        Domain::NatEmbedded,
                        nat_affine_syntax(elab, cx, right, &mut atoms)?,
                        nat_affine_syntax(elab, cx, left, &mut atoms)?,
                        Relation::Le,
                        format!(
                            "omega::nat_le_to_int({}, {}, omega::nat_le_of_not_lt({}, {}, {}))",
                            right_source, left_source, left_source, right_source, name,
                        ),
                    )
                } else {
                    continue;
                }
            } else {
                continue;
            };
        relations.push(ReflectedConstraint {
            domain,
            lhs: left,
            relation,
            rhs: right,
            evidence: proof,
        });
    }
    if relations.is_empty() {
        return Ok(None);
    }
    let divisions = atoms
        .iter_with_ids()
        .filter_map(|(index, atom)| atom.division.clone().map(|division| (index, division)))
        .collect::<Vec<_>>();
    for (index, division) in divisions {
        let quotient = AffineSyntax::Atom {
            index,
            source: atoms.get(index).source.clone(),
        };
        let product = AffineSyntax::Scale {
            factor: division.divisor,
            factor_on_left: false,
            inner: Box::new(quotient),
        };
        let magnitude = division
            .divisor
            .checked_abs()
            .ok_or("Omega cannot reconstruct the minimum `i128` divisor")?;
        let (lower_proof, upper_proof) = if division.natural {
            let divisor_pred = division
                .divisor
                .checked_sub(1)
                .ok_or("Omega positive natural divisor predecessor overflowed")?;
            (
                format!(
                    "omega::nat_div_lower({}, {})",
                    division.dividend_source, divisor_pred
                ),
                format!(
                    "omega::nat_div_upper({}, {})",
                    division.dividend_source, divisor_pred
                ),
            )
        } else {
            let nonzero = literal_int_nonzero(division.divisor)?;
            (
                format!(
                    "omega::div_lower_nonzero({}, {}, {})",
                    division.dividend_source,
                    int(division.divisor),
                    nonzero,
                ),
                format!(
                    "omega::div_upper_nonzero({}, {}, {})",
                    division.dividend_source,
                    int(division.divisor),
                    nonzero,
                ),
            )
        };
        let domain = if division.natural {
            Domain::NatEmbedded
        } else {
            Domain::Int
        };
        relations.push(ReflectedConstraint {
            domain,
            lhs: product.clone(),
            relation: Relation::Le,
            rhs: division.dividend.clone(),
            evidence: lower_proof,
        });
        relations.push(ReflectedConstraint {
            domain,
            lhs: AffineSyntax::Add {
                left: Box::new(division.dividend),
                right: Box::new(AffineSyntax::Const {
                    value: 1,
                    source: int(1),
                }),
            },
            rhs: AffineSyntax::Add {
                left: Box::new(product),
                right: Box::new(AffineSyntax::Const {
                    value: magnitude,
                    source: int(magnitude),
                }),
            },
            relation: Relation::Le,
            evidence: upper_proof,
        });
    }
    let atoms_source = atom_list_source(&atoms);
    let mut facts = Vec::with_capacity(relations.len());
    for reflected in relations {
        let left = normalize_syntax(&reflected.lhs, &atoms_source)?;
        let right = normalize_syntax(&reflected.rhs, &atoms_source)?;
        let reflected = ReflectedConstraint {
            domain: reflected.domain,
            lhs: left.linear.clone(),
            relation: reflected.relation,
            rhs: right.linear.clone(),
            evidence: reflected.evidence,
        };
        let linear = reflected
            .lhs
            .checked_sub(&reflected.rhs)
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
        if reflected.relation == Relation::Eq {
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
                reflected.evidence,
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
                exact: Some(equality),
            });
        } else if reflected.relation == Relation::Le {
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
                reflected.evidence,
            );
            facts.push(InitialAssumption {
                coeffs: linear.coeffs,
                row_source,
                interval: Interval::upper(upper),
                lower: None,
                upper: Some(proof),
                exact: None,
            });
        } else {
            return Err("Omega reflected a non-canonical affine relation".into());
        }
    }
    for (index, atom) in atoms.iter_with_ids() {
        let Some(nat_source) = &atom.nat_source else {
            continue;
        };
        let index = index.index();
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
            exact: None,
        });
    }
    let atom_labels = atoms
        .iter()
        .map(|atom| {
            atom.nat_source
                .clone()
                .unwrap_or_else(|| atom.source.clone())
        })
        .collect();
    let atom_sources = atoms.iter().map(|atom| atom.source.clone()).collect();
    Ok(Some((facts, atoms_source, atom_labels, atom_sources)))
}

fn int(value: Z) -> String {
    int_ctor(value)
}

fn literal_int_nonzero(value: Z) -> Result<String, String> {
    if value > 0 {
        return Ok(format!("omega::positive_int_nonzero({})", value - 1));
    }
    if value < 0 {
        let payload = value
            .checked_neg()
            .and_then(|magnitude| magnitude.checked_sub(1))
            .ok_or("Omega cannot reconstruct the minimum `i128` divisor")?;
        return Ok(format!("omega::negative_int_nonzero({payload})"));
    }
    Err("Omega requested a nonzero proof for zero".into())
}

fn coeffs_source(coeffs: &Coeffs) -> String {
    coeffs
        .as_slice()
        .iter()
        .rev()
        .fold("list::Nil".to_string(), |tail, coefficient| {
            format!("list::Cons({}, {tail})", int(*coefficient))
        })
}

fn affine_source(affine: &Affine, atom_sources: &[String]) -> String {
    affine
        .coeffs
        .as_slice()
        .iter()
        .enumerate()
        .filter(|(_, coefficient)| **coefficient != 0)
        .fold(int(affine.constant), |out, (index, coefficient)| {
            let atom = atom_sources
                .get(index)
                .cloned()
                .unwrap_or_else(|| format!("__cutsat_missing_atom_{index}"));
            let term = if *coefficient == 1 {
                atom
            } else {
                format!("int::mul({}, {atom})", int(*coefficient))
            };
            format!("int::add({out}, {term})")
        })
}

fn int_ctor(value: Z) -> String {
    if value >= 0 {
        format!("int::OfNat({value})")
    } else {
        let payload = value.checked_neg().unwrap_or(Z::MAX) - 1;
        format!("int::NegSucc({payload})")
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
    for (name, ty) in local_facts(elab, cx) {
        let Some(domain) = negated_domain(elab, cx, &ty) else {
            continue;
        };
        let decoded = crate::inductive::decoded(&domain);
        let disequality = &name;
        let (left, right, disequality, lemma) =
            if let Some((left, right)) = equality_args(elab, cx, &decoded) {
                (
                    int_term_source(elab, cx, left)?,
                    int_term_source(elab, cx, right)?,
                    disequality.clone(),
                    "omega::diseq_elim",
                )
            } else if let Some((divisor, dividend)) = int_divides_args(elab, &domain) {
                let divisor = int_term_source(elab, cx, divisor)?;
                let dividend = int_term_source(elab, cx, dividend)?;
                (
                    format!("int::mod({dividend}, {divisor})"),
                    int(0),
                    disequality.clone(),
                    "omega::diseq_elim",
                )
            } else if let Some((divisor, dividend)) = nat_divides_args(elab, &domain) {
                let divisor = nat_term_source(elab, cx, divisor)?;
                let dividend = nat_term_source(elab, cx, dividend)?;
                let remainder = format!("nat::mod({dividend}, {divisor})");
                (
                    remainder,
                    "0".to_string(),
                    disequality.clone(),
                    "omega::nat_diseq_elim",
                )
            } else {
                continue;
            };
        let source = format!(
            "{lemma}({}, {}, {disequality}, (__omega_diseq_left: {} < {}) ⊢ __omega_diseq_branch, (__omega_diseq_right: {} < {}) ⊢ __omega_diseq_branch)",
            left, right, left, right, right, left,
        );
        return Ok(Some(Certificate {
            expr: parse_generated_expr(&source)?,
            source,
            report: OmegaReport {
                atoms: 0,
                atom_labels: Vec::new(),
                assumptions: 0,
                reachable_derivations: 0,
                total_derivations: 0,
                discarded_derivations: 0,
                logical_splits: 1,
                stats: crate::omega::Stats::default(),
                used_lemmas: vec![lemma],
                residual: Vec::new(),
                cutsat: None,
                phases: OmegaPhases::default(),
            },
        }));
    }
    Ok(None)
}

fn split_connective(elab: &Elaborator, cx: &Cx) -> Result<Option<Certificate>, String> {
    for (name, ty) in local_facts(elab, cx) {
        let Some(tag) = elab.display_tag_of(&ty) else {
            continue;
        };
        let source = match tag.name.as_str() {
            "And" => format!(
                "omega::and_elim_false({}, __omega_and_left __omega_and_right ⊢ __omega_connective_branch)",
                name
            ),
            "Or" => format!(
                "omega::or_elim_false({}, __omega_or_left ⊢ __omega_connective_branch, __omega_or_right ⊢ __omega_connective_branch)",
                name
            ),
            _ => continue,
        };
        return Ok(Some(Certificate {
            expr: parse_generated_expr(&source)?,
            source,
            report: OmegaReport {
                atoms: 0,
                atom_labels: Vec::new(),
                assumptions: 0,
                reachable_derivations: 0,
                total_derivations: 0,
                discarded_derivations: 0,
                logical_splits: 1,
                stats: crate::omega::Stats::default(),
                used_lemmas: vec![match tag.name.as_str() {
                    "And" => "omega::and_elim_false",
                    _ => "omega::or_elim_false",
                }],
                residual: Vec::new(),
                cutsat: None,
                phases: OmegaPhases::default(),
            },
        }));
    }
    Ok(None)
}

#[derive(Clone)]
struct CutDvdEvidence {
    divisor: Z,
    value: String,
    proof: String,
}

fn cut_parent_le<'a>(problem: &'a CutProblem, id: usize) -> Result<&'a Affine, String> {
    match problem.derivations().conclusion(id) {
        Some(DerivedConstraint::Le(affine)) => Ok(affine),
        other => Err(format!(
            "CutSat certificate expected inequality node {id}, got {other:?}"
        )),
    }
}

fn open_cut_dvds(evidence: &[CutDvdEvidence], body: String, depth: usize) -> String {
    evidence
        .iter()
        .enumerate()
        .rev()
        .fold(body, |body, (index, dvd)| {
            format!(
                "omega::cut_dvd_elim({}, {}, {}, (__cutsat_witness_{depth}_{index}: Int) __cutsat_dvd_eq_{depth}_{index} ⊢ {body})",
                int(dvd.divisor), dvd.value, dvd.proof,
            )
        })
}

fn collect_cut_les(problem: &CutProblem, roots: &[usize]) -> Vec<usize> {
    fn visit(problem: &CutProblem, id: usize, seen: &mut [bool]) {
        if seen[id] {
            return;
        }
        seen[id] = true;
        for parent in problem.derivations().nodes()[id].parents() {
            visit(problem, parent, seen);
        }
    }
    let mut seen = vec![false; problem.derivations().nodes().len()];
    for &root in roots {
        visit(problem, root, &mut seen);
    }
    seen.into_iter()
        .enumerate()
        .filter_map(|(id, seen)| {
            (seen
                && matches!(
                    problem.derivations().conclusion(id),
                    Some(DerivedConstraint::Le(_))
                ))
            .then_some(id)
        })
        .collect()
}

fn wrap_cut_les(
    problem: &CutProblem,
    roots: &[usize],
    atom_sources: &[String],
    le_evidence: &[Option<String>],
    mut body: String,
) -> Result<String, String> {
    for id in collect_cut_les(problem, roots)
        .into_iter()
        .filter(|id| le_evidence.get(*id).is_none_or(Option::is_none))
        .rev()
    {
        let Some(DerivedConstraint::Le(affine)) = problem.derivations().conclusion(id) else {
            return Err(format!(
                "CutSat inequality dependency {id} has no conclusion"
            ));
        };
        let value = affine_source(affine, atom_sources);
        body = format!(
            "omega::cutsat_with_le({value}, __cutsat_linear_branch, (__cutsat_le_{id}: {value} <= int::OfNat(0)) ⊢ {body})"
        );
    }
    Ok(body)
}

fn cut_le_name(id: usize) -> String {
    format!("__cutsat_le_{id}")
}

fn cut_le_proof_name(id: usize, evidence: &[Option<String>]) -> String {
    evidence
        .get(id)
        .and_then(Option::as_ref)
        .cloned()
        .unwrap_or_else(|| cut_le_name(id))
}

fn hoisted_cut_les(problem: &CutProblem, reachable: &[usize]) -> (Vec<usize>, Vec<Option<String>>) {
    let mut is_reachable = vec![false; problem.derivations().nodes().len()];
    for &id in reachable {
        is_reachable[id] = true;
    }
    let mut is_static = vec![false; problem.derivations().nodes().len()];
    let mut canonical: Vec<(Affine, usize)> = Vec::new();
    let mut roots = Vec::new();
    let mut evidence = vec![None; problem.derivations().nodes().len()];
    for (id, node) in problem.derivations().nodes().iter().enumerate() {
        is_static[id] = match node {
            CutDerivation::Assumption { .. } => true,
            CutDerivation::RealProjection { lower, upper } => {
                is_static[*lower] && is_static[*upper]
            }
            _ => false,
        };
        if !is_reachable[id] || !is_static[id] {
            continue;
        }
        let Some(DerivedConstraint::Le(affine)) = problem.derivations().conclusion(id) else {
            continue;
        };
        let canonical_id = canonical
            .iter()
            .find_map(|(old, old_id)| (old == affine).then_some(*old_id))
            .unwrap_or_else(|| {
                canonical.push((affine.clone(), id));
                roots.push(id);
                id
            });
        evidence[id] = Some(cut_le_name(canonical_id));
    }
    (roots, evidence)
}

fn cut_nat_case_proof(split_id: usize, case: usize) -> String {
    let mut proof = format!("__cutsat_nat_eq_{split_id}_{case}");
    for index in (0..case).rev() {
        proof = format!("trans(__cutsat_nat_eq_{split_id}_{index}, cong_nat(Succ, {proof}))");
    }
    proof
}

fn reconstruct_cut_node(
    problem: &CutProblem,
    id: usize,
    atoms_source: &str,
    atom_labels: &[String],
    le_evidence: &[Option<String>],
    dvd_evidence: &[Option<CutDvdEvidence>],
    depth: usize,
) -> Result<String, String> {
    let node = problem
        .derivations()
        .nodes()
        .get(id)
        .ok_or_else(|| format!("CutSat certificate references absent node {id}"))?;
    match node {
        CutDerivation::ConstantInequality { constraint } => wrap_cut_les(
            problem,
            &[*constraint],
            atom_labels,
            le_evidence,
            "__cutsat_linear_branch".into(),
        ),
        CutDerivation::ConstantDivisibility { constraint } => {
            let dvd = dvd_evidence
                .get(*constraint)
                .and_then(Option::as_ref)
                .ok_or_else(|| {
                    format!("CutSat constant divisibility node {constraint} has no evidence")
                })?;
            Ok(open_cut_dvds(
                &[dvd.clone()],
                "__cutsat_linear_branch".into(),
                depth,
            ))
        }
        CutDerivation::BoundDivisibilityConflict {
            lower,
            upper,
            divisibility,
            ..
        } => {
            let dvd = dvd_evidence
                .get(*divisibility)
                .and_then(Option::as_ref)
                .ok_or_else(|| {
                    format!("CutSat bound conflict node {divisibility} has no evidence")
                })?;
            wrap_cut_les(
                problem,
                &[*lower, *upper],
                atom_labels,
                le_evidence,
                open_cut_dvds(&[dvd.clone()], "__cutsat_linear_branch".into(), depth),
            )
        }
        CutDerivation::DivisibilityConflict { left, right } => {
            let left = dvd_evidence
                .get(*left)
                .and_then(Option::as_ref)
                .ok_or_else(|| format!("CutSat divisibility node {left} has no evidence"))?;
            let right = dvd_evidence
                .get(*right)
                .and_then(Option::as_ref)
                .ok_or_else(|| format!("CutSat divisibility node {right} has no evidence"))?;
            Ok(open_cut_dvds(
                &[left.clone(), right.clone()],
                "__cutsat_linear_branch".into(),
                depth,
            ))
        }
        CutDerivation::CombinedCongruenceBoundConflict {
            lower,
            upper,
            divisibility,
        } => {
            let evidence = divisibility
                .iter()
                .map(|id| {
                    dvd_evidence
                        .get(*id)
                        .and_then(Option::as_ref)
                        .cloned()
                        .ok_or_else(|| {
                            format!("CutSat combined conflict node {id} has no evidence")
                        })
                })
                .collect::<Result<Vec<_>, _>>()?;
            wrap_cut_les(
                problem,
                &[*lower, *upper],
                atom_labels,
                le_evidence,
                open_cut_dvds(&evidence, "__cutsat_linear_branch".into(), depth),
            )
        }
        CutDerivation::CooperCase { contradiction, .. } => reconstruct_cut_node(
            problem,
            *contradiction,
            atoms_source,
            atom_labels,
            le_evidence,
            dvd_evidence,
            depth,
        ),
        CutDerivation::CooperExhausted { cases } => {
            let Some(&first_case) = cases.first() else {
                return Err("CutSat produced an empty Cooper split".into());
            };
            let CutDerivation::CooperCase {
                inequality: first_cut,
                divisibilities: first_dvds,
                ..
            } = &problem.derivations().nodes()[first_case]
            else {
                return Err("CutSat Cooper split does not point at case nodes".into());
            };
            if first_dvds.len() > 1 {
                return Err("CutSat reconstruction does not yet replay Cooper with an existing divisibility constraint".into());
            }
            let CutDerivation::CooperInequality {
                lower,
                upper,
                divisibility: None,
                ..
            } = &problem.derivations().nodes()[*first_cut]
            else {
                return Err("CutSat reconstruction currently expects a simple Cooper split".into());
            };
            let lower_affine = cut_parent_le(problem, *lower)?;
            let upper_affine = cut_parent_le(problem, *upper)?;
            let variable = lower_affine
                .coeffs
                .as_slice()
                .iter()
                .rposition(|coefficient| *coefficient != 0)
                .ok_or("CutSat Cooper lower bound has no variable")?;
            let a = lower_affine.coeffs.get(variable);
            let b = upper_affine.coeffs.get(variable);
            if a >= 0 || b <= 0 {
                return Err("CutSat Cooper parents are not opposing bounds".into());
            }
            let left = a
                .checked_abs()
                .ok_or("CutSat coefficient magnitude overflowed")?
                < b;
            let selected = if left { a } else { b };
            let selected_tail = if left { lower_affine } else { upper_affine };
            let mut tail = selected_tail.clone();
            tail.coeffs = tail.coeffs.with_coefficient(variable, 0);
            let x = atom_labels
                .get(variable)
                .ok_or_else(|| format!("CutSat has no source for atom {variable}"))?;
            let p = {
                let mut p = lower_affine.clone();
                p.coeffs = p.coeffs.with_coefficient(variable, 0);
                affine_source(&p, atom_labels)
            };
            let q = {
                let mut q = upper_affine.clone();
                q.coeffs = q.coeffs.with_coefficient(variable, 0);
                affine_source(&q, atom_labels)
            };
            let remainder_name = format!("__cutsat_remainder_{id}");
            let k_name = format!("__cutsat_k_{id}");
            let cut_name = format!("__cutsat_cut_{id}");
            let dvd_name = format!("__cutsat_dvd_{id}");
            let mut branches = Vec::with_capacity(cases.len());
            let mut branch_bindings = Vec::with_capacity(cases.len());
            for (case_index, &case_id) in cases.iter().enumerate() {
                let CutDerivation::CooperCase {
                    inequality,
                    divisibilities,
                    contradiction,
                } = &problem.derivations().nodes()[case_id]
                else {
                    return Err("CutSat Cooper split contains a non-case root".into());
                };
                let CutDerivation::CooperInequality {
                    lower: case_lower,
                    upper: case_upper,
                    divisibility: None,
                    case,
                } = &problem.derivations().nodes()[*inequality]
                else {
                    return Err("CutSat reconstruction found a non-simple Cooper case".into());
                };
                if *case_lower != *lower
                    || *case_upper != *upper
                    || *case != case_index as Z
                    || divisibilities.len() > 1
                {
                    return Err(
                        "CutSat Cooper cases are not a deterministic contiguous split".into(),
                    );
                }
                let mut branch_evidence = dvd_evidence.to_vec();
                let mut branch_le_evidence = le_evidence.to_vec();
                branch_le_evidence[*inequality] = Some(cut_name.clone());
                if let Some(&dvd_id) = divisibilities.first() {
                    let value = format!(
                        "int::add({}, {remainder_name})",
                        affine_source(&tail, atom_labels),
                    );
                    branch_evidence[dvd_id] = Some(CutDvdEvidence {
                        divisor: selected,
                        value,
                        proof: dvd_name.clone(),
                    });
                }
                let branch = reconstruct_cut_node(
                    problem,
                    *contradiction,
                    atoms_source,
                    atom_labels,
                    &branch_le_evidence,
                    &branch_evidence,
                    depth + 1,
                )?;
                let remainder_value = int(case_index as Z);
                let remainder_proof = format!(
                    "trans(__cutsat_int_eq_{id}, int::cong_ofnat({}))",
                    cut_nat_case_proof(id, case_index),
                );
                let close_name = format!("__cutsat_close_{id}_{case_index}");
                branch_bindings.push(format!(
                    "let {close_name}: ({remainder_name} = {remainder_value}) → logic::False = (__cutsat_remainder_value_{id}_{case_index}: {remainder_name} = {remainder_value}) ⊢ {branch};"
                ));
                branches.push(format!(
                    "omega::cutsat_with_eq({remainder_name}, {remainder_value}, {remainder_proof}, {close_name})"
                ));
            }
            let mut matched = "__cutsat_linear_branch".to_string();
            for (case_index, branch) in branches.into_iter().enumerate().rev() {
                let scrutinee = if case_index == 0 {
                    k_name.clone()
                } else {
                    format!("__cutsat_rest_{id}_{}", case_index - 1)
                };
                let rest = format!("__cutsat_rest_{id}_{case_index}");
                matched = format!(
                    "match __cutsat_nat_eq_{id}_{case_index} : {scrutinee} {{ Zero => {branch}, Succ({rest}) => {matched}, }}"
                );
            }
            matched = format!(
                "match __cutsat_int_eq_{id} : {remainder_name} {{ int::NegSucc(__cutsat_negative_{id}) => omega::cutsat_negative_remainder({remainder_name}, __cutsat_negative_{id}, __cutsat_int_eq_{id}, __cutsat_nonnegative_{id}), int::OfNat({k_name}) => {matched}, }}"
            );
            matched = format!("{{ {} {matched} }}", branch_bindings.join(" "));
            let lemma = if left {
                "omega::cutsat_cooper_left"
            } else {
                "omega::cutsat_cooper_right"
            };
            let a_pred = a
                .checked_abs()
                .and_then(|value| value.checked_sub(1))
                .ok_or("CutSat left coefficient predecessor overflowed")?;
            let b_pred = b
                .checked_sub(1)
                .ok_or("CutSat right coefficient predecessor overflowed")?;
            wrap_cut_les(
                problem,
                &[*lower, *upper],
                atom_labels,
                le_evidence,
                format!(
                    "{lemma}({a_pred}, {b_pred}, {x}, {p}, {q}, {}, {}, ({remainder_name}: Int) __cutsat_nonnegative_{id} __cutsat_bound_{id} {cut_name} {dvd_name} ⊢ {matched})",
                    cut_le_proof_name(*lower, le_evidence),
                    cut_le_proof_name(*upper, le_evidence),
                ),
            )
        }
        unsupported => Err(format!(
            "CutSat proof reconstruction does not yet support derivation {unsupported:?}"
        )),
    }
}

fn reconstruct_cutsat(
    reflected: &[InitialAssumption],
    atoms_source: &str,
    atom_sources: &[String],
) -> Result<Option<(String, usize, usize, crate::cutsat::Stats)>, String> {
    let mut problem = CutProblem::new();
    for fact in reflected {
        let row = Affine {
            constant: 0,
            coeffs: AffineCoeffs::new(fact.coeffs.as_slice().to_vec()),
        };
        if let Some(value) = fact
            .interval
            .lower
            .filter(|value| fact.interval.upper == Some(*value))
        {
            problem
                .assume(row, Relation::Eq, Affine::constant(value))
                .map_err(|failure| failure.to_string())?;
        } else {
            if let Some(lower) = fact.interval.lower {
                problem
                    .assume(Affine::constant(lower), Relation::Le, row.clone())
                    .map_err(|failure| failure.to_string())?;
            }
            if let Some(upper) = fact.interval.upper {
                problem
                    .assume(row.clone(), Relation::Le, Affine::constant(upper))
                    .map_err(|failure| failure.to_string())?;
            }
        }
    }
    let (problem, outcome) = timed(
        |p| &mut p.cutsat_search_ns,
        || problem.solve(CutLimits::default()),
    )
    .map_err(|failure| failure.to_string())?;
    let CutOutcome::Contradiction {
        root,
        reachable,
        stats,
    } = outcome
    else {
        return Ok(None);
    };
    let render_started = std::time::Instant::now();
    let (hoisted_roots, le_evidence) = hoisted_cut_les(&problem, &reachable);
    let evidence = vec![None; problem.derivations().nodes().len()];
    let body = reconstruct_cut_node(
        &problem,
        root,
        atoms_source,
        atom_sources,
        &le_evidence,
        &evidence,
        0,
    )?;
    let source = wrap_cut_les(
        &problem,
        &hoisted_roots,
        atom_sources,
        &vec![None; problem.derivations().nodes().len()],
        body,
    )?;
    let render_ns = render_started.elapsed().as_nanos() as u64;
    PHASES.with(|c| {
        let mut phases = c.get();
        phases.render_ns = phases.render_ns.saturating_add(render_ns);
        c.set(phases);
    });
    Ok(Some((
        source,
        reachable.len(),
        problem.derivations().nodes().len(),
        stats,
    )))
}

pub(crate) fn reconstruct(
    elab: &Elaborator,
    cx: &Cx,
    expected: &Type,
    allow_disequality_split: bool,
    allow_connective_split: bool,
    allow_cutsat: bool,
) -> Result<Certificate, String> {
    let decoded_expected = crate::inductive::decoded(expected);
    if elab
        .display_tag_of(expected)
        .is_some_and(|tag| tag.name == "And")
    {
        let source = "logic::And(left := omega, right := omega)".to_string();
        return Ok(Certificate {
            expr: parse_generated_expr(&source)?,
            source,
            report: wrapper_report("logic::And", 0),
        });
    }
    if let Some((divisor, dividend)) = int_divides_args(elab, expected) {
        let divisor = int_term_source(elab, cx, divisor)?;
        let dividend = int_term_source(elab, cx, dividend)?;
        let remainder = format!("int::mod({dividend}, {divisor})");
        let source = format!(
            "int::le_antisym({}, int::OfNat(0), omega, omega)",
            remainder
        );
        return Ok(Certificate {
            expr: parse_generated_expr(&source)?,
            source,
            report: wrapper_report("int::le_antisym", 0),
        });
    }
    if let Some((divisor, dividend)) = nat_divides_args(elab, expected) {
        let divisor = nat_term_source(elab, cx, divisor)?;
        let dividend = nat_term_source(elab, cx, dividend)?;
        let remainder = format!("nat::mod({dividend}, {divisor})");
        let source = format!("nat::le_antisym({}, 0, omega, omega)", remainder);
        return Ok(Certificate {
            expr: parse_generated_expr(&source)?,
            source,
            report: wrapper_report("nat::le_antisym", 0),
        });
    }
    if let Some((left, right)) =
        equality_args(elab, cx, expected).or_else(|| equality_args(elab, cx, &decoded_expected))
    {
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
    if let Some((left, right)) = nat_equality_args(elab, cx, expected)
        .or_else(|| nat_equality_args(elab, cx, &decoded_expected))
    {
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
            "int::le_of_not_lt({}, {}, (__omega_negated_goal: {} + int::OfNat(1) <= {}) ⊢ omega)",
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
            "omega::nat_lt_of_not_not_lt({}, {}, (__omega_negated_goal: logic::Not(nat::Lt({}, {}))) ⊢ omega)",
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
            "omega::nat_le_of_not_not_le({}, {}, (__omega_negated_goal: logic::Not(nat::Le({}, {}))) ⊢ omega)",
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

    let (reflected, atoms_source, atom_labels, cut_atom_sources) =
        if let Some(ordinary) = timed(|p| &mut p.reflect_ns, || reflect_ordinary(elab, cx))? {
            let (facts, atoms_source, atom_labels, atom_sources) = ordinary;
            (facts, atoms_source, atom_labels, Some(atom_sources))
        } else {
            let mut explicit = Vec::new();
            for (name, ty) in local_facts(elab, cx) {
                if let Some(fact) = reflect_assumption(elab, cx, &name, &ty)? {
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
                let locals = local_facts(elab, cx)
                    .into_iter()
                    .map(|(name, ty)| format!("{name}: {}", elab.display_type(cx, &ty)))
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
            let facts: Vec<_> = explicit
                .into_iter()
                .map(|fact| InitialAssumption {
                    coeffs: fact.coeffs,
                    row_source: fact.coeffs_source,
                    interval: fact.interval,
                    lower: fact.interval.lower.map(|_| fact.name.clone()),
                    upper: fact.interval.upper.map(|_| fact.name),
                    exact: None,
                })
                .collect();
            let atom_count = reflected_atom_count(&facts);
            (facts, atoms_source, indexed_atom_labels(atom_count), None)
        };
    let atom_count = atom_labels.len();

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
    let (problem, outcome) = timed(|p| &mut p.omega_search_ns, || problem.solve())
        .map_err(|failure| failure.to_string())?;
    let Outcome::Contradiction {
        derivation,
        reachable_derivations,
        stats,
    } = &outcome
    else {
        let Outcome::NoContradiction { residual, stats } = &outcome else {
            unreachable!()
        };
        if allow_cutsat
            && let Some(cut_atom_sources) = cut_atom_sources.as_deref()
            && let Some((source, cut_reachable, cut_total, cut_stats)) =
                reconstruct_cutsat(&reflected, &atoms_source, cut_atom_sources)?
        {
            let expr = parse_generated_expr(&source)
                .map_err(|error| format!("{error}\n  generated CutSat source: {source}"))?;
            let used_lemmas = reconstruction_lemmas(&source);
            return Ok(Certificate {
                expr,
                source,
                report: OmegaReport {
                    atoms: atom_count,
                    atom_labels: atom_labels.clone(),
                    assumptions: reflected.len(),
                    reachable_derivations: 0,
                    total_derivations: problem.dag.nodes().len(),
                    discarded_derivations: problem.dag.nodes().len(),
                    logical_splits: cut_stats.splits,
                    stats: *stats,
                    used_lemmas,
                    residual: Vec::new(),
                    cutsat: Some(CutSatReport {
                        reachable_derivations: cut_reachable,
                        total_derivations: cut_total,
                        stats: cut_stats,
                    }),
                    phases: OmegaPhases::default(),
                },
            });
        }
        if allow_disequality_split && let Some(certificate) = split_disequality(elab, cx)? {
            return Ok(certificate);
        }
        if allow_connective_split && let Some(certificate) = split_connective(elab, cx)? {
            return Ok(certificate);
        }
        let local_types = local_facts(elab, cx)
            .into_iter()
            .map(|(name, ty)| format!("{name}: {}", elab.display_type(cx, &ty)))
            .collect::<Vec<_>>()
            .join(", ");
        let residual = residual
            .iter()
            .map(|fact| {
                let coefficients = fact.coeffs.as_slice().to_vec();
                let lower = fact.interval.lower;
                let upper = fact.interval.upper;
                OmegaResidualConstraint {
                    rendered: render_residual(&coefficients, lower, upper, &atom_labels),
                    coefficients,
                    lower,
                    upper,
                }
            })
            .collect::<Vec<_>>();
        let residual_display = residual
            .iter()
            .map(|constraint| constraint.rendered.as_str())
            .collect::<Vec<_>>()
            .join(", ");
        let total_derivations = problem.dag.nodes().len();
        elab.record_omega_failure_report(OmegaReport {
            atoms: atom_count,
            atom_labels: atom_labels.clone(),
            assumptions: reflected.len(),
            reachable_derivations: 0,
            total_derivations,
            discarded_derivations: total_derivations,
            logical_splits: 0,
            stats: *stats,
            used_lemmas: Vec::new(),
            residual,
            cutsat: None,
            phases: OmegaPhases::default(),
        });
        return Err(format!(
            "Omega's real shadow found no contradiction; atoms [{}]; residual [{residual_display}]; locals [{local_types}]; reflected [{reflected_debug}]",
            atom_labels.join(", "),
        ));
    };
    let derivation = *derivation;
    let reachable_derivations = reachable_derivations.clone();

    let mut proofs: Vec<Option<BoundProof>> = vec![None; problem.dag.nodes().len()];
    let mut bindings = Vec::new();
    for &id in &reachable_derivations {
        let raw_fact = problem.replay(id).map_err(|failure| failure.to_string())?;
        let fact = problem
            .project_fact(&raw_fact)
            .map_err(|failure| failure.to_string())?;
        let mut proof = match problem.dag.nodes()[id] {
            Derivation::Assumption { index } => {
                let source = reflected
                    .get(index)
                    .ok_or_else(|| format!("Omega assumption {index} was not reflected"))?;
                let (lower, upper, exact) = if let Some(equality) = &source.exact {
                    let value = fact
                        .interval
                        .lower
                        .filter(|value| fact.interval.upper == Some(*value))
                        .ok_or("Omega exact assumption lost its value")?;
                    let name = format!("__omega_exact_{id}");
                    bindings.push(format!("let {name} = {equality};"));
                    (
                        Some(format!(
                            "omega::lower_of_eq({}, {}, {}, {})",
                            source.row_source,
                            atoms_source,
                            int(value),
                            name,
                        )),
                        Some(format!(
                            "omega::upper_of_eq({}, {}, {}, {})",
                            source.row_source,
                            atoms_source,
                            int(value),
                            name,
                        )),
                        Some(name),
                    )
                } else {
                    (source.lower.clone(), source.upper.clone(), None)
                };
                BoundProof {
                    row_source: source.row_source.clone(),
                    interval: fact.interval,
                    lower,
                    upper,
                    exact,
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
                    exact: None,
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
                    exact: None,
                }
            }
            Derivation::Balanced { parent: source, .. } => {
                let source_proof = parent(&proofs, source)?;
                let source_fact = problem
                    .replay(source)
                    .and_then(|fact| problem.project_fact(&fact))
                    .map_err(|failure| failure.to_string())?;
                if source_fact.coeffs != fact.coeffs || source_fact.interval != fact.interval {
                    return Err(format!(
                        "Omega balanced projection did not erase to its parent: {:?} {:?} versus {:?} {:?}",
                        source_fact.coeffs, source_fact.interval, fact.coeffs, fact.interval,
                    ));
                }
                source_proof.clone()
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
                    exact: None,
                }
            }
            Derivation::Combo {
                left,
                left_scale,
                right,
                right_scale,
            } if fact.interval.is_exact() => {
                let left = parent(&proofs, left)?;
                let right = parent(&proofs, right)?;
                let left_value = left
                    .interval
                    .lower
                    .filter(|value| left.interval.upper == Some(*value))
                    .ok_or("Omega exact combination has a non-exact left parent")?;
                let right_value = right
                    .interval
                    .lower
                    .filter(|value| right.interval.upper == Some(*value))
                    .ok_or("Omega exact combination has a non-exact right parent")?;
                let value = fact
                    .interval
                    .lower
                    .ok_or("Omega exact combination lost its value")?;
                let left_eq = left
                    .exact
                    .as_ref()
                    .ok_or("Omega exact combination lost its left equality proof")?;
                let right_eq = right
                    .exact
                    .as_ref()
                    .ok_or("Omega exact combination lost its right equality proof")?;
                let name = format!("__omega_exact_{id}");
                let row_source = format!(
                    "omega::combo({}, {}, {}, {})",
                    int(left_scale),
                    left.row_source,
                    int(right_scale),
                    right.row_source,
                );
                let expression = format!(
                    "omega::exact_combo({}, {}, {}, {}, {}, {}, {}, {}, {})",
                    int(left_scale),
                    int(right_scale),
                    left.row_source,
                    right.row_source,
                    atoms_source,
                    int(left_value),
                    int(right_value),
                    left_eq,
                    right_eq,
                );
                bindings.push(format!("let {name} = {expression};"));
                BoundProof {
                    row_source: row_source.clone(),
                    interval: fact.interval,
                    lower: Some(format!(
                        "omega::lower_of_eq({}, {}, {}, {})",
                        row_source,
                        atoms_source,
                        int(value),
                        name,
                    )),
                    upper: Some(format!(
                        "omega::upper_of_eq({}, {}, {}, {})",
                        row_source,
                        atoms_source,
                        int(value),
                        name,
                    )),
                    exact: Some(name),
                }
            }
            Derivation::Combo {
                left,
                left_scale,
                right,
                right_scale,
            } if left_scale > 0
                && right_scale < 0
                && fact.interval.lower.is_some()
                && fact.interval.upper.is_some() =>
            {
                let left = parent(&proofs, left)?;
                let right = parent(&proofs, right)?;
                let left_lower = left
                    .interval
                    .lower
                    .ok_or("Omega two-sided combination lost its left lower value")?;
                let left_upper = left
                    .interval
                    .upper
                    .ok_or("Omega two-sided combination lost its left upper value")?;
                let right_lower = right
                    .interval
                    .lower
                    .ok_or("Omega two-sided combination lost its right lower value")?;
                let right_upper = right
                    .interval
                    .upper
                    .ok_or("Omega two-sided combination lost its right upper value")?;
                let magnitude = right_scale
                    .checked_neg()
                    .ok_or("Omega combination scale overflowed")?;
                let row_source = format!(
                    "omega::combo({}, {}, {}, {})",
                    int(left_scale),
                    left.row_source,
                    int(right_scale),
                    right.row_source,
                );
                let lower_name = format!("__omega_generated_{id}_lower");
                bindings.push(format!(
                    "let {lower_name} = omega::lower_upper_combo({}, {}, {}, {}, {}, {}, {}, int::zero_le_ofNat({}), int::zero_le_ofNat({}), {}, {});",
                    int(left_scale), int(magnitude), left.row_source, right.row_source,
                    atoms_source, int(left_lower), int(right_upper), left_scale, magnitude,
                    left.lower.as_ref().ok_or("Omega two-sided combination lost its left lower proof")?,
                    right.upper.as_ref().ok_or("Omega two-sided combination lost its right upper proof")?,
                ));
                let upper_name = format!("__omega_generated_{id}_upper");
                bindings.push(format!(
                    "let {upper_name} = omega::lower_upper_upper_combo({}, {}, {}, {}, {}, {}, {}, int::zero_le_ofNat({}), int::zero_le_ofNat({}), {}, {});",
                    int(left_scale), int(magnitude), left.row_source, right.row_source,
                    atoms_source, int(right_lower), int(left_upper), left_scale, magnitude,
                    left.upper.as_ref().ok_or("Omega two-sided combination lost its left upper proof")?,
                    right.lower.as_ref().ok_or("Omega two-sided combination lost its right lower proof")?,
                ));
                BoundProof {
                    row_source,
                    interval: fact.interval,
                    lower: Some(lower_name),
                    upper: Some(upper_name),
                    exact: None,
                }
            }
            Derivation::Combo {
                left,
                left_scale,
                right,
                right_scale,
            } if left_scale < 0
                && right_scale > 0
                && fact.interval.lower.is_some()
                && fact.interval.upper.is_some() =>
            {
                let left = parent(&proofs, left)?;
                let right = parent(&proofs, right)?;
                let left_lower = left
                    .interval
                    .lower
                    .ok_or("Omega two-sided combination lost its left lower value")?;
                let left_upper = left
                    .interval
                    .upper
                    .ok_or("Omega two-sided combination lost its left upper value")?;
                let right_lower = right
                    .interval
                    .lower
                    .ok_or("Omega two-sided combination lost its right lower value")?;
                let right_upper = right
                    .interval
                    .upper
                    .ok_or("Omega two-sided combination lost its right upper value")?;
                let magnitude = left_scale
                    .checked_neg()
                    .ok_or("Omega combination scale overflowed")?;
                let row_source = format!(
                    "omega::combo({}, {}, {}, {})",
                    int(left_scale),
                    left.row_source,
                    int(right_scale),
                    right.row_source,
                );
                let lower_name = format!("__omega_generated_{id}_lower");
                bindings.push(format!(
                    "let {lower_name} = omega::upper_lower_lower_combo({}, {}, {}, {}, {}, {}, {}, int::zero_le_ofNat({}), int::zero_le_ofNat({}), {}, {});",
                    int(magnitude), int(right_scale), left.row_source, right.row_source,
                    atoms_source, int(right_lower), int(left_upper), magnitude, right_scale,
                    left.upper.as_ref().ok_or("Omega two-sided combination lost its left upper proof")?,
                    right.lower.as_ref().ok_or("Omega two-sided combination lost its right lower proof")?,
                ));
                let upper_name = format!("__omega_generated_{id}_upper");
                bindings.push(format!(
                    "let {upper_name} = omega::upper_lower_combo({}, {}, {}, {}, {}, {}, {}, int::zero_le_ofNat({}), int::zero_le_ofNat({}), {}, {});",
                    int(magnitude), int(right_scale), left.row_source, right.row_source,
                    atoms_source, int(left_lower), int(right_upper), magnitude, right_scale,
                    left.lower.as_ref().ok_or("Omega two-sided combination lost its left lower proof")?,
                    right.upper.as_ref().ok_or("Omega two-sided combination lost its right upper proof")?,
                ));
                BoundProof {
                    row_source,
                    interval: fact.interval,
                    lower: Some(lower_name),
                    upper: Some(upper_name),
                    exact: None,
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
                    exact: None,
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
                    exact: None,
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
                    exact: None,
                }
            }
            Derivation::Combo {
                left,
                left_scale,
                right,
                right_scale,
            } if left_scale < 0
                && right_scale < 0
                && fact.interval.lower.is_some()
                && fact.interval.upper.is_some() =>
            {
                let left = parent(&proofs, left)?;
                let right = parent(&proofs, right)?;
                let a = left_scale
                    .checked_neg()
                    .ok_or("Omega combination scale overflowed")?;
                let b = right_scale
                    .checked_neg()
                    .ok_or("Omega combination scale overflowed")?;
                let row_source = format!(
                    "omega::combo({}, {}, {}, {})",
                    int(left_scale),
                    left.row_source,
                    int(right_scale),
                    right.row_source,
                );
                let lower_name = format!("__omega_generated_{id}_lower");
                bindings.push(format!(
                    "let {lower_name} = omega::lower_neg_combo({}, {}, {}, {}, {}, {}, {}, int::zero_le_ofNat({}), int::zero_le_ofNat({}), {}, {});",
                    int(a), int(b), left.row_source, right.row_source, atoms_source,
                    int(left.interval.upper.ok_or("Omega negative combination lost its left upper value")?),
                    int(right.interval.upper.ok_or("Omega negative combination lost its right upper value")?),
                    a, b,
                    left.upper.as_ref().ok_or("Omega negative combination lost its left upper proof")?,
                    right.upper.as_ref().ok_or("Omega negative combination lost its right upper proof")?,
                ));
                let upper_name = format!("__omega_generated_{id}_upper");
                bindings.push(format!(
                    "let {upper_name} = omega::upper_neg_combo({}, {}, {}, {}, {}, {}, {}, int::zero_le_ofNat({}), int::zero_le_ofNat({}), {}, {});",
                    int(a), int(b), left.row_source, right.row_source, atoms_source,
                    int(left.interval.lower.ok_or("Omega negative combination lost its left lower value")?),
                    int(right.interval.lower.ok_or("Omega negative combination lost its right lower value")?),
                    a, b,
                    left.lower.as_ref().ok_or("Omega negative combination lost its left lower proof")?,
                    right.lower.as_ref().ok_or("Omega negative combination lost its right lower proof")?,
                ));
                BoundProof {
                    row_source,
                    interval: fact.interval,
                    lower: Some(lower_name),
                    upper: Some(upper_name),
                    exact: None,
                }
            }
            Derivation::Combo {
                left,
                left_scale,
                right,
                right_scale,
            } if left_scale < 0 && right_scale < 0 && fact.interval.upper.is_none() => {
                let left = parent(&proofs, left)?;
                let right = parent(&proofs, right)?;
                let a = left_scale
                    .checked_neg()
                    .ok_or("Omega combination scale overflowed")?;
                let b = right_scale
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
                bindings.push(format!(
                    "let {name} = omega::lower_neg_combo({}, {}, {}, {}, {}, {}, {}, int::zero_le_ofNat({}), int::zero_le_ofNat({}), {}, {});",
                    int(a), int(b), left.row_source, right.row_source, atoms_source,
                    int(left.interval.upper.ok_or("Omega negative combination lost its left upper value")?),
                    int(right.interval.upper.ok_or("Omega negative combination lost its right upper value")?),
                    a, b,
                    left.upper.as_ref().ok_or("Omega negative combination lost its left upper proof")?,
                    right.upper.as_ref().ok_or("Omega negative combination lost its right upper proof")?,
                ));
                BoundProof {
                    row_source,
                    interval: fact.interval,
                    lower: Some(name),
                    upper: None,
                    exact: None,
                }
            }
            Derivation::Combo {
                left,
                left_scale,
                right,
                right_scale,
            } if left_scale < 0 && right_scale < 0 && fact.interval.lower.is_none() => {
                let left = parent(&proofs, left)?;
                let right = parent(&proofs, right)?;
                let a = left_scale
                    .checked_neg()
                    .ok_or("Omega combination scale overflowed")?;
                let b = right_scale
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
                bindings.push(format!(
                    "let {name} = omega::upper_neg_combo({}, {}, {}, {}, {}, {}, {}, int::zero_le_ofNat({}), int::zero_le_ofNat({}), {}, {});",
                    int(a), int(b), left.row_source, right.row_source, atoms_source,
                    int(left.interval.lower.ok_or("Omega negative combination lost its left lower value")?),
                    int(right.interval.lower.ok_or("Omega negative combination lost its right lower value")?),
                    a, b,
                    left.lower.as_ref().ok_or("Omega negative combination lost its left lower proof")?,
                    right.lower.as_ref().ok_or("Omega negative combination lost its right lower proof")?,
                ));
                BoundProof {
                    row_source,
                    interval: fact.interval,
                    lower: None,
                    upper: Some(name),
                    exact: None,
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
                    exact: None,
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
                    exact: None,
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
                    exact: source.exact.clone(),
                }
            }
            ref unsupported => {
                return Err(format!(
                    "Omega proof reconstruction does not yet support derivation {unsupported:?}"
                ));
            }
        };
        if proof.interval.is_exact() && proof.exact.is_none() {
            let value = proof
                .interval
                .lower
                .ok_or("Omega exact proof lost its value")?;
            let name = format!("__omega_exact_{id}");
            bindings.push(format!(
                "let {name} = omega::eq_of_bounds({}, {}, {}, {}, {});",
                proof.row_source,
                atoms_source,
                int(value),
                proof
                    .lower
                    .as_ref()
                    .ok_or("Omega exact proof lost its lower bound")?,
                proof
                    .upper
                    .as_ref()
                    .ok_or("Omega exact proof lost its upper bound")?,
            ));
            proof.exact = Some(name);
        }
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
                atoms: atom_count,
                atom_labels: atom_labels.clone(),
                assumptions: reflected.len(),
                reachable_derivations: reachable_derivations.len(),
                total_derivations: problem.dag.nodes().len(),
                discarded_derivations: problem
                    .dag
                    .nodes()
                    .len()
                    .saturating_sub(reachable_derivations.len()),
                logical_splits: 0,
                stats: *stats,
                used_lemmas,
                residual: Vec::new(),
                cutsat: None,
                phases: OmegaPhases::default(),
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
            atoms: atom_count,
            atom_labels,
            assumptions: reflected.len(),
            reachable_derivations: reachable_derivations.len(),
            total_derivations: problem.dag.nodes().len(),
            discarded_derivations: problem
                .dag
                .nodes()
                .len()
                .saturating_sub(reachable_derivations.len()),
            logical_splits: 0,
            stats: *stats,
            used_lemmas,
            residual: Vec::new(),
            cutsat: None,
            phases: OmegaPhases::default(),
        },
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn integer_parser_accepts_structural_nat_literals() {
        assert_eq!(integer_source("0"), Some(0));
        assert_eq!(integer_source("Succ(Succ(Succ(0)))"), Some(3));
        assert_eq!(integer_source(" Succ( Succ(0) ) "), Some(2));
        assert_eq!(integer_source("Succ(x)"), None);
        assert_eq!(integer_source("Succ(0))"), None);
    }

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
        assert_eq!(
            coefficient_source("list::Cons(int::OfNat(3), list::Cons(int::NegSucc(0), list::Nil))"),
            Some(vec![3, -1])
        );
        assert_eq!(coefficient_source("Nil"), Some(vec![]));
        assert_eq!(coefficient_source("Cons(x, Nil)"), None);
        assert_eq!(coefficient_source("Cons(1, Nil) junk"), None);
    }

    #[test]
    fn residual_rendering_is_source_level_and_stable() {
        let labels = vec!["x".into(), "ignored".into(), "f(y)".into()];
        assert_eq!(
            render_residual(&[-1, 0, 3], Some(-2), Some(8), &labels),
            "-2 <= -x + 3 * f(y) <= 8"
        );
        assert_eq!(
            render_residual(&[0, 1], Some(4), Some(4), &labels),
            "ignored = 4"
        );
        assert_eq!(
            render_residual(&[0, 0, 0, -2], None, Some(7), &labels),
            "-2 * aux[0] <= 7"
        );
    }

    #[test]
    fn pugh_certificate_hoists_branch_invariant_inequalities() {
        fn row(coefficients: &[Z]) -> Affine {
            Affine {
                constant: 0,
                coeffs: AffineCoeffs::new(coefficients.to_vec()),
            }
        }

        fn interval(problem: &mut CutProblem, coefficients: &[Z], lower: Z, upper: Z) {
            let row = row(coefficients);
            problem
                .assume(Affine::constant(lower), Relation::Le, row.clone())
                .unwrap();
            problem
                .assume(row, Relation::Le, Affine::constant(upper))
                .unwrap();
        }

        let mut problem = CutProblem::new();
        interval(&mut problem, &[11, 13], 27, 45);
        interval(&mut problem, &[7, -9], -10, 4);
        interval(&mut problem, &[1, 0], -16, 16);
        interval(&mut problem, &[0, 1], -16, 16);
        let (problem, outcome) = problem.solve(CutLimits::default()).unwrap();
        let CutOutcome::Contradiction {
            root, reachable, ..
        } = outcome
        else {
            panic!("Pugh system did not contradict")
        };
        let (hoisted_roots, le_evidence) = hoisted_cut_les(&problem, &reachable);
        let body = reconstruct_cut_node(
            &problem,
            root,
            "atoms(x, y)",
            &["x".into(), "y".into()],
            &le_evidence,
            &vec![None; problem.derivations().nodes().len()],
            0,
        )
        .unwrap();
        let source = wrap_cut_les(
            &problem,
            &hoisted_roots,
            &["x".into(), "y".into()],
            &vec![None; problem.derivations().nodes().len()],
            body,
        )
        .unwrap();
        // Includes module-qualified dependency names in the generated source.
        assert_eq!(source.len(), 17_573);
        assert_eq!(source.matches("__cutsat_linear_branch").count(), 28);
        assert_eq!(source.matches("omega::cutsat_with_le").count(), 9);
        assert_eq!(source.matches("let __cutsat_close_").count(), 18);
    }
}
