//! Reflection and proof reconstruction for the first kernel-certified Omega
//! slice.
//!
//! The frontend reflects affine `Int` inequalities and equalities, sharing
//! arbitrary unrecognized subterms as opaque atoms. Explicit `omega::dot`
//! constraints remain as a low-level diagnostic boundary. Direct `<=`, `<`,
//! and `=` goals reuse recursively certified order consequences.

use std::sync::Arc as Rc;

use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{LocalSubst, Term, Type};
use heather_syntax::{Expr, Item, parse_file};

use crate::oracle::Unfold;
use crate::arithmetic::{
    Affine, AtomId, AtomTable, Coeffs as AffineCoeffs, Domain, ReflectedConstraint, Relation,
};
use crate::cutsat::{
    Limits as CutLimits, Outcome as CutOutcome,
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
    /// The atom list `source` names [`ATOMS`] for, spelled out: the caller
    /// binds it once, so the checker meets one list rather than one per row.
    /// `None` when `source` does not use the name.
    pub atoms: Option<String>,
    /// A Bool-guard round's facts (`split_bool_guards`): what the caller
    /// binds before checking, and the facts it settles while it does.
    pub guards: Option<GuardRound>,
}

/// A fact the caller binds before checking a certificate: `term` (a fact
/// already in scope) at `ty`, its guard's definition unfolded.
pub(crate) struct GuardAlias {
    pub name: String,
    pub term: Rc<Term>,
    pub ty: Type,
    pub level: Level,
}

pub(crate) struct GuardRound {
    pub aliases: Vec<GuardAlias>,
    /// The names of the facts the round reads: no `omega` inside the
    /// certificate reads them again.
    pub settles: Vec<String>,
}

/// The name a certificate uses for its atom list (`Certificate::atoms`).
pub(crate) const ATOMS: &str = "__omega_atoms";

pub(crate) fn parse_generated_expr(source: &str) -> Result<Expr, String> {
    timed(|p| &mut p.parse_ns, crate::stats::Timer::OmegaParse, || {
        parse_generated_expr_untimed(source)
    })
}

/// A certificate's atom list (`Certificate::atoms`) and the type it is
/// checked at: an empty list infers no element type.
pub(crate) fn parse_atom_list(literal: &str) -> Result<(heather_syntax::Ty, Expr), String> {
    let wrapper = format!("theorem __omega_generated(): list::List<int::Int> {{ {literal} }}");
    let mut file = parse_file(&wrapper).map_err(|error| error.msg)?;
    let Some(Item::Decl(decl)) = file.items.pop() else {
        return Err("the generated Omega atom list did not parse".into());
    };
    Ok((decl.result, *decl.body.result))
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
/// certificate that re-invokes `omega` (`le_of_not_lt(… ⊢ omega)`) pays for
/// those nested invocations inside it, so `depth` says which reports are
/// inner ones.
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
///
/// The bracket is the registry's (`docs/instrumentation-design.md` §3), read
/// twice: the registry gets the phase's **exclusive** self time, for the
/// per-declaration columns of the dump, and the per-invocation accumulator
/// keeps the **inclusive** elapsed time it always kept, so an `OmegaReport`
/// still says what it said.
fn timed<T>(
    phase: fn(&mut OmegaPhases) -> &mut u64,
    timer: crate::stats::Timer,
    f: impl FnOnce() -> T,
) -> T {
    let guard = crate::stats::guard(timer);
    let out = f();
    let ns = guard.finish();
    add_phase(phase, ns);
    out
}

/// Add `ns` to one field of the reconstruction in progress.
fn add_phase(phase: fn(&mut OmegaPhases) -> &mut u64, ns: u64) {
    PHASES.with(|c| {
        let mut phases = c.get();
        *phase(&mut phases) = phase(&mut phases).saturating_add(ns);
        c.set(phases);
    });
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
        "int::Int::cong_ofnat",
        "int::Int::le_trans",
        "int::Int::negsucc_lt_of_lt",
        "int::Int::negsucc_lt_ofnat",
        "int::Int::not_lt_of_ge",
        "int::Int::zero_le_ofNat",
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
        "omega::normalized_ne_value",
        "omega::upper_combo",
        "omega::upper_neg_combo",
        "omega::upper_lower_combo",
        "omega::upper_lower_lower_combo",
        "omega::lower_upper_upper_combo",
        "omega::upper_of_eq",
        "omega::upper_to_negated_lower",
        "omega::below_succ",
        "omega::cut_constant_diseq",
        "omega::cut_constant_dvd",
        "omega::cut_constant_upper",
        "omega::cut_cooper_left",
        "omega::cut_cooper_right",
        "omega::cut_diseq",
        "omega::cut_dvd_combo",
        "omega::cut_dvd_drop",
        "omega::cut_dvd_one",
        "omega::cut_resolve",
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
    /// A `≠` fact: no bounds, and a proof of
    /// `dot(row, atoms) + c ≠ 0` with `c = -interval`'s exact value. Only
    /// CutSat reads it; such facts come after every bounded one, so Omega's
    /// assumption indices are positions in the bounded prefix.
    disequality: Option<String>,
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

pub(crate) fn named_args<'a>(elab: &Elaborator, t: &'a Term, wanted: &str) -> Option<Vec<&'a Rc<Term>>> {
    let mut args = Vec::new();
    let mut head = t;
    while let Some((fun, arg)) = crate::spelling::app_of(head) {
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
    let args = named_args(elab, tm, "int::Int::Le")?;
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
    let args = named_args(elab, tm, "int::Int::Lt")?;
    let [left, right] = args.as_slice() else {
        return None;
    };
    Some((left, right))
}

fn nat_relation_args<'a>(elab: &Elaborator, ty: &'a Type) -> Option<(&'a Rc<Term>, &'a Rc<Term>)> {
    let Type::El { tm, .. } = ty else {
        return None;
    };
    let args = named_args(elab, tm, "nat::Nat::Le")?;
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
    let args = named_args(elab, tm, "nat::Nat::Lt")?;
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
    let args = named_args(elab, tm, "int::Int::Divides")?;
    let [divisor, dividend] = args.as_slice() else {
        return None;
    };
    Some((divisor, dividend))
}

fn nat_divides_args<'a>(elab: &Elaborator, ty: &'a Type) -> Option<(&'a Rc<Term>, &'a Rc<Term>)> {
    let Type::El { tm, .. } = ty else {
        return None;
    };
    let args = named_args(elab, tm, "nat::Nat::Divides")?;
    let [divisor, dividend] = args.as_slice() else {
        return None;
    };
    Some((divisor, dividend))
}

pub(crate) fn negated_domain(elab: &Elaborator, cx: &Cx, ty: &Type) -> Option<Type> {
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

/// Whether `ty` is a relation this frontend reflects as stated: `<=`, `<`
/// or `=` at `Int` or `Nat`, an equality possibly still a code.
fn reads_as_relation(elab: &Elaborator, cx: &Cx, ty: &Type) -> bool {
    let decoded = crate::inductive::decoded(ty);
    relation_args(elab, ty).is_some()
        || strict_relation_args(elab, ty).is_some()
        || nat_relation_args(elab, ty).is_some()
        || nat_strict_relation_args(elab, ty).is_some()
        || equality_args(elab, cx, &decoded).is_some()
        || nat_equality_args(elab, cx, &decoded).is_some()
}

/// An order at `Int` or `Nat` as written, not unfolded: whether it is at
/// `Nat`, whether it is strict, and its two sides. `nlinarith` multiplies
/// these (docs/nonlinear-arithmetic-design.md §4.4).
/// A head β-redex is read through its contractum, as [`push_conjuncts`] does.
pub(crate) fn integral_order(elab: &Elaborator, ty: &Type) -> Option<(bool, bool, Rc<Term>, Rc<Term>)> {
    let contracted = crate::spelling::beta_head_ty(ty);
    let ty = contracted.as_ref().unwrap_or(ty);
    let found = |nat, strict, sides: Option<(&Rc<Term>, &Rc<Term>)>| sides.map(|(l, r)| (nat, strict, Rc::clone(l), Rc::clone(r)));
    found(false, false, relation_args(elab, ty))
        .or_else(|| found(false, true, strict_relation_args(elab, ty)))
        .or_else(|| found(true, false, nat_relation_args(elab, ty)))
        .or_else(|| found(true, true, nat_strict_relation_args(elab, ty)))
}

/// The two sides of a relation this frontend reflects, as `linarith` at
/// `Int` and `Nat` reads them (docs/linarith-design.md §8): `<=`, `<` or `=`
/// at either, its negation, or a defined proposition that unfolds to one;
/// `true` for `Nat`. A head β-redex is read through its contractum, as
/// [`push_conjuncts`] does.
pub(crate) fn integral_sides(elab: &Elaborator, cx: &Cx, ty: &Type) -> Option<(bool, Rc<Term>, Rc<Term>)> {
    let contracted = crate::spelling::beta_head_ty(ty);
    let ty = contracted.as_ref().unwrap_or(ty);
    let stated = |ty: &Type| {
        let decoded = crate::inductive::decoded(ty);
        let int = relation_args(elab, ty)
            .or_else(|| strict_relation_args(elab, ty))
            .or_else(|| equality_args(elab, cx, &decoded));
        let nat = || {
            nat_relation_args(elab, ty)
                .or_else(|| nat_strict_relation_args(elab, ty))
                .or_else(|| nat_equality_args(elab, cx, &decoded))
        };
        match int {
            Some((l, r)) => Some((false, Rc::clone(l), Rc::clone(r))),
            None => nat().map(|(l, r)| (true, Rc::clone(l), Rc::clone(r))),
        }
    };
    let relation = |ty: &Type| {
        stated(ty).or_else(|| {
            unfolded_proposition(elab, cx, ty, |ty| reads_as_relation(elab, cx, ty)).and_then(|ty| stated(&ty))
        })
    };
    relation(ty).or_else(|| relation(&negated_domain(elab, cx, ty)?))
}


/// The relation a defined proposition unfolds to
/// (issues/omega-unfolds-defined-propositions.md): `Rat::Le(x, y)` is
/// `x.num * y.den.int() <= y.num * x.den.int()`. Its head is unfolded step by
/// step and the first reduct `reads` accepts is kept, not the weak head
/// normal form, which would unfold `Le` itself into its recursor; then the
/// arguments, which arrive as passed (`Rat::ofInt(0).num`), are simplified as a
/// goal's are. Only an applied global that is not a type former is asked: a
/// local `x: Rat` or `l: List<Int>` is data, and asking it would cost every
/// call a reduction per binder.
pub(crate) fn unfolded_proposition(
    elab: &Elaborator,
    cx: &Cx,
    ty: &Type,
    reads: impl Fn(&Type) -> bool,
) -> Option<Type> {
    let Type::El { level, tm } = ty else {
        return None;
    };
    if !head_is_global(tm) || elab.display_tag_of(ty).is_some() {
        return None;
    }
    let oracle = elab.goal_oracle();
    let unfolded = oracle.unfold_to(&cx.gamma, tm, Unfold::Proposition, |reduct| {
        let unfolded = Type::El { level: level.clone(), tm: Rc::new(reduct) };
        reads(&unfolded).then_some(unfolded)
    })?;
    let decoded = crate::inductive::decoded(&unfolded);
    Some(crate::goal_combinators::simplify_goal(elab, cx, &decoded))
}

fn dot_args<'a>(elab: &Elaborator, tm: &'a Term) -> Option<(&'a Rc<Term>, &'a Rc<Term>)> {
    let args = named_args(elab, tm, "omega::dot")?;
    let [coeffs, atoms] = args.as_slice() else {
        return None;
    };
    Some((coeffs, atoms))
}

pub(crate) fn integer_source(source: &str) -> Option<Z> {
    let source = source.strip_prefix("int::").unwrap_or(source);
    let compact: String = source.chars().filter(|c| !c.is_whitespace()).collect();
    if let Ok(value) = compact.parse() {
        return Some(value);
    }
    if let Some(value) = nat_lit_value(&compact) {
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
        return nat_lit_value(inner);
    }
    if let Some(inner) = compact
        .strip_prefix("NegSucc(")
        .and_then(|s| s.strip_suffix(')'))
    {
        let payload = nat_lit_value(inner)?;
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

    /// A [`nat_lit`] spelling up to the parenthesis that closes its
    /// constructor, which is left for the caller.
    fn nat_lit(&mut self) -> Option<Z> {
        let start = self.cursor;
        let mut depth = 0usize;
        while let Some(&byte) = self.input.get(self.cursor) {
            match byte {
                b'(' => depth += 1,
                b')' if depth == 0 => break,
                b')' => depth -= 1,
                _ => {}
            }
            self.cursor += 1;
        }
        let compact: String = std::str::from_utf8(&self.input[start..self.cursor])
            .ok()?
            .chars()
            .filter(|c| !c.is_whitespace())
            .collect();
        nat_lit_value(&compact)
    }

    fn integer(&mut self) -> Option<Z> {
        if self.token(b"OfNat") || self.token(b"int::OfNat") {
            self.token(b"(").then_some(())?;
            let value = self.nat_lit()?;
            if !self.token(b")") {
                return None;
            }
            return Some(value);
        }
        if self.token(b"NegSucc") || self.token(b"int::NegSucc") {
            self.token(b"(").then_some(())?;
            let payload = self.nat_lit()?;
            if !self.token(b")") {
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

/// Give shadowed binders source names for both reconstruction and checking.
/// Only the surface name table changes: the kernel context, alias terms and
/// goal keep their original de Bruijn indices. This lets a certificate use an
/// outer fact without spelling its variable as an unrelated inner binder.
pub(crate) fn source_context(cx: &Cx) -> std::borrow::Cow<'_, Cx> {
    let shadowed: Vec<_> = cx.names.iter().enumerate().filter_map(|(pos, name)| {
        (!name.starts_with('#')
            && (cx.names.iter().skip(pos + 1).any(|later| later == name)
                || cx.aliases.iter_inner().any(|alias| alias.name == *name && alias.depth > pos)))
            .then_some(pos)
    }).collect();
    if shadowed.is_empty() {
        return std::borrow::Cow::Borrowed(cx);
    }
    let mut used: std::collections::HashSet<String> = cx.names.iter().map(str::to_string)
        .chain(cx.aliases.iter_inner().map(|alias| alias.name.clone())).collect();
    let mut fresh = std::collections::HashMap::new();
    let mut next = 0;
    for pos in shadowed {
        loop {
            let name = format!("__omega_local_{next}");
            next += 1;
            if used.insert(name.clone()) {
                fresh.insert(pos, name);
                break;
            }
        }
    }
    let mut named = cx.clone();
    let mut pos = 0;
    named.names = cx.names.renamed(|name| {
        let new = fresh.remove(&pos).unwrap_or_else(|| name.to_string());
        pos += 1;
        new
    });
    std::borrow::Cow::Owned(named)
}

// Resolve each visible name once through the same binder/alias precedence as
// ordinary expressions. Alias types are weakened to this context by resolve.
// A hidden binder (`#ih`, a `match`'s induction hypothesis) is left out: a
// certificate is source, and source cannot name it. A conjunction is listed
// as its conjuncts, at every depth, each named by its projection path
// (`h.right.left`): a certificate cites only the ones it uses
// (issues/omega-nested-conjunction-facts.md).
pub(crate) fn local_facts(elab: &Elaborator, cx: &Cx) -> Vec<(String, Type)> {
    local_fact_entries(elab, cx).into_iter().map(|fact| (fact.name, fact.ty)).collect()
}

/// A fact `local_facts` lists, with its evidence and its type's level.
pub(crate) struct LocalFact {
    pub(crate) name: String,
    pub(crate) term: Rc<Term>,
    pub(crate) ty: Type,
    pub(crate) level: Level,
}

pub(crate) fn local_fact_entries(elab: &Elaborator, cx: &Cx) -> Vec<LocalFact> {
    let mut seen = std::collections::HashSet::new();
    let mut facts = Vec::new();
    for name in cx.names.iter().chain(cx.aliases.iter().map(|alias| alias.name.as_str())) {
        if name.starts_with('#') || !seen.insert(name.to_string()) {
            continue;
        }
        if let Ok((term, ty, level)) = elab.resolve_reading(cx, name, heather_syntax::Span { start: 0, end: 0 }) {
            push_conjuncts(elab, cx, name.to_string(), Rc::new(term), ty, level, &mut facts);
        }
    }
    facts
}

/// `name: ty`, or, when `ty` is `logic::And`, each side read through its
/// projection, recursively. A head β-redex is contracted first, as the
/// unifier does (`spelling::beta_head`): an `Exists`'s `.proof` is typed
/// `(λ k => P(k))(e.witness)`, and read raw no relation is visible in it
/// (issues/omega-redex-typed-fact-ignored.md).
fn push_conjuncts(elab: &Elaborator, cx: &Cx, name: String, term: Rc<Term>, ty: Type, level: Level, out: &mut Vec<LocalFact>) {
    let ty = crate::spelling::beta_head_ty(&ty).unwrap_or(ty);
    if let Some(ind) = elab.display_tag_of(&ty)
        && crate::goal_combinators::conjunction(&ind)
    {
        let sides: Option<Vec<_>> = ["left", "right"]
            .into_iter()
            .enumerate()
            .map(|(idx, field)| {
                elab.project_field(cx, &ind, &ty, Rc::clone(&term), idx, heather_syntax::Span { start: 0, end: 0 })
                    .ok()
                    .map(|(side, side_ty, side_level)| (format!("{name}.{field}"), Rc::new(side), side_ty, side_level))
            })
            .collect();
        if let Some(sides) = sides {
            for (side_name, side, side_ty, side_level) in sides {
                push_conjuncts(elab, cx, side_name, side, side_ty, side_level, out);
            }
            return;
        }
    }
    out.push(LocalFact { name, term, ty, level });
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
            .spell_term_source(cx, left)
            .ok_or_else(|| format!("Omega could not spell the lower bound in `{}`", name))?;
        let lower = integer_source(&lower_source)
            .ok_or_else(|| format!("Omega requires a literal lower bound, got `{lower_source}`"))?;
        (coeffs, atoms, Interval::lower(lower))
    } else if let Some((coeffs, atoms)) = dot_args(elab, left) {
        let upper_source = elab
            .spell_term_source(cx, right)
            .ok_or_else(|| format!("Omega could not spell the upper bound in `{}`", name))?;
        let upper = integer_source(&upper_source)
            .ok_or_else(|| format!("Omega requires a literal upper bound, got `{upper_source}`"))?;
        (coeffs, atoms, Interval::upper(upper))
    } else {
        return Ok(None);
    };
    let coeff_source = elab
        .spell_term_source(cx, coeff_term)
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
        .spell_term_source(cx, atoms)
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
    // An Int `OfNat(e)` is read through the Nat side, which is how a Nat fact
    // arrives: otherwise `OfNat(x)` in an Int fact and `x` in a Nat fact are
    // two unrelated atoms, and nothing links them.
    if let Some(inner) = of_nat_payload(elab, tm) {
        return nat_affine_syntax(elab, cx, inner, atoms);
    }
    if let Some(args) = named_args(elab, tm, "int::Int::add") {
        if let [left, right] = args.as_slice() {
            return Ok(AffineSyntax::Add {
                left: Box::new(affine_syntax(elab, cx, left, atoms)?),
                right: Box::new(affine_syntax(elab, cx, right, atoms)?),
            });
        }
    }
    // A sum at a successor bound, as at `Nat`.
    if let Some(peeled) = crate::range_sum::peel(elab, tm)
        && crate::range_sum::op_is(elab, &peeled.op, "int::Int::add")
    {
        return Ok(AffineSyntax::Add {
            left: Box::new(affine_syntax(elab, cx, &peeled.rest, atoms)?),
            right: Box::new(affine_syntax(elab, cx, &peeled.last, atoms)?),
        });
    }
    if let Some(args) = named_args(elab, tm, "int::Int::sub") {
        if let [left, right] = args.as_slice() {
            return Ok(AffineSyntax::Add {
                left: Box::new(affine_syntax(elab, cx, left, atoms)?),
                right: Box::new(AffineSyntax::Neg {
                    inner: Box::new(affine_syntax(elab, cx, right, atoms)?),
                }),
            });
        }
    }
    if let Some(args) = named_args(elab, tm, "int::Int::neg") {
        if let [inner] = args.as_slice() {
            return Ok(AffineSyntax::Neg {
                inner: Box::new(affine_syntax(elab, cx, inner, atoms)?),
            });
        }
    }
    if let Some(args) = named_args(elab, tm, "int::Int::mul") {
        if let [left, right] = args.as_slice() {
            let left_source = elab.spell_term_source(cx, left);
            let right_source = elab.spell_term_source(cx, right);
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
            // A factor that computes to a numeral is that numeral, as an
            // atom is (`x.num * Rat::ofInt(1).den.int()` is `x.num * 1`); the
            // checker's conversion computes it again.
            for (factor, inner, factor_on_left) in [(left, right, true), (right, left, false)] {
                if let Some(factor) = int_value(elab, cx, factor).filter(|value| *value != Z::MIN) {
                    return Ok(AffineSyntax::Scale {
                        factor,
                        factor_on_left,
                        inner: Box::new(affine_syntax(elab, cx, inner, atoms)?),
                    });
                }
            }
        }
    }
    if let Some(args) = named_args(elab, tm, "int::Int::mod")
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
            let quotient_source = format!("int::Int::div({}, {})", dividend_source, int(divisor));
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
    if let Some(args) = named_args(elab, tm, "int::Int::div")
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

    // The Nat side's two questions (issues/omega-int-atoms-up-to-computation.md),
    // asked only of a spelling the table has not met.
    if let Some(index) = atoms.find(|atom| *atom.term == **tm || atom.source == source) {
        return Ok(AffineSyntax::Atom { index, source });
    }
    if let Some(value) = int_value(elab, cx, tm) {
        return Ok(AffineSyntax::Const {
            value,
            source: int_ctor(value),
        });
    }
    if let Some(reduct) = computed_of_nat(elab, cx, tm) {
        return affine_syntax(elab, cx, &reduct, atoms);
    }
    // A field of a call that unfolds to a constructor (`(x + y).num`), read
    // as the expression put there when that spells.
    if is_field_read(elab, tm)
        && let Some(field) = field_as_put(elab, cx, tm)
        && int_term_source(elab, cx, &field).is_ok()
    {
        return affine_syntax(elab, cx, &field, atoms);
    }
    if let Some(index) = convertible_atom(elab, cx, tm, atoms, Carrier::Int) {
        return Ok(AffineSyntax::Atom { index, source });
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

/// The integer a global-headed Int term, or a field of one, computes to: its bounded weak head
/// is a constructor whose Nat payload computes to a numeral
/// ([`SemanticOracle::nat_value`](crate::oracle::SemanticOracle::nat_value)).
fn int_value(elab: &Elaborator, cx: &Cx, tm: &Rc<Term>) -> Option<Z> {
    // A field of a call (`Rat::ofInt(1).num`) computes as the call does.
    if !head_is_global(projection_path(tm).1) {
        return None;
    }
    let oracle = elab.goal_oracle();
    let head = oracle.bounded(ATOM_COMPUTATION_STEPS).whnf_term(&cx.gamma, tm).ok()?;
    let (of_nat, payload) = int_ctor_payload(elab, &head)?;
    let n = Z::try_from(oracle.nat_value(&cx.gamma, payload, ATOM_COMPUTATION_STEPS)?).ok()?;
    if of_nat { Some(n) } else { n.checked_add(1)?.checked_neg() }
}

/// `int::Int` as a kernel type, for comparing Int atoms by conversion: a
/// `Le`/`Lt` fact does not carry its carrier, so it is elaborated from its
/// name, and only once a comparison has passed every syntactic gate.
fn int_carrier(elab: &Elaborator, cx: &Cx) -> Option<(Type, Level)> {
    let file = parse_file("theorem __omega_generated(): int::Int { 0 }").ok()?;
    let Some(Item::Decl(decl)) = file.items.last() else {
        return None;
    };
    elab.elab_ty(cx, &decl.result).ok()
}

/// The Nat `e` of an Int constructor value `OfNat(e)`.
fn of_nat_payload<'a>(elab: &Elaborator, tm: &'a Term) -> Option<&'a Rc<Term>> {
    match int_ctor_payload(elab, tm)? {
        (true, inner) => Some(inner),
        (false, _) => None,
    }
}

/// An Int constructor value's side and Nat payload: `(true, e)` for
/// `OfNat(e)`, `(false, e)` for `NegSucc(e)`.
fn int_ctor_payload<'a>(elab: &Elaborator, tm: &'a Term) -> Option<(bool, &'a Rc<Term>)> {
    let ind = match tm {
        Term::Inl { lhs, .. } | Term::Inr { lhs, .. } => elab.display_tag_of(lhs)?,
        Term::InlAt { ty, .. } | Term::InrAt { ty, .. } => elab.display_tag_of(ty.as_deref()?)?,
        _ => return None,
    };
    if ind.ctors.len() != 2 || ind.ctors[0].name != "OfNat" || ind.ctors[1].name != "NegSucc" {
        return None;
    }
    let (of_nat, val) = crate::spelling::inj_of(tm)?;
    let (_, payload) = crate::spelling::pair_of(val)?;
    let (inner, _) = crate::spelling::pair_of(payload)?;
    Some((of_nat, inner))
}

fn int_term_source(elab: &Elaborator, cx: &Cx, tm: &Rc<Term>) -> Result<String, String> {
    for (name, arity) in [
        ("int::Int::add", 2usize),
        ("int::Int::sub", 2),
        ("int::Int::mul", 2),
        ("int::Int::neg", 1),
        ("int::Int::div", 2),
        ("int::Int::mod", 2),
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
    elab.spell_term_source(cx, tm)
        .ok_or_else(|| "Omega could not spell an integer expression".to_string())
}

pub(crate) fn nat_term_source(elab: &Elaborator, cx: &Cx, tm: &Rc<Term>) -> Result<String, String> {
    match &**tm {
        Term::Zero => return Ok("0".into()),
        Term::NatLit(n) => return Ok(n.to_string()),
        Term::Succ(inner) => {
            return Ok(format!("Succ({})", nat_term_source(elab, cx, inner)?));
        }
        _ => {}
    }
    for name in ["nat::Nat::add", "nat::Nat::mul", "nat::Nat::div", "nat::Nat::mod"] {
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
    elab.spell_term_source(cx, tm)
        .ok_or_else(|| "Omega could not spell a natural expression".to_string())
}

/// The arithmetic a projection out of a value computes to
/// (docs/omega-measure-reduction-design.md §10): a field read off a
/// constructor, or off a `match` on one — what a motive instantiated at
/// `False` leaves, `(match False { … }).words` — whose bounded weak head is
/// `Succ(s.words)` or `0`. Kept only on an arithmetic head whose leaves spell,
/// as §2 keeps a call's reduct: a projection out of a neutral is its own weak
/// head, and one out of a call that unfolds (`step_fold(…).bytes`) reduces to
/// an eliminator, and both intern as they always did (§5).
fn projection_reduct(elab: &Elaborator, cx: &Cx, tm: &Rc<Term>, depth: u32) -> Option<Rc<Term>> {
    if !is_field_read(elab, tm) {
        return None;
    }
    // A read at closed arguments whose field computes past the budget has no
    // weak head here; it is still read as put, below
    // (issues/omega-closed-field-value-atomised.md).
    if let Ok(reduct) = elab.goal_oracle().whnf_term_bounded(&cx.gamma, tm) {
        let reduct = Rc::new(reduct);
        if matches!(&*reduct, Term::NatLit(_)) {
            return Some(reduct);
        }
        if let Some(shaped) = named_arithmetic_shape(elab, cx, &reduct, &[], depth) {
            return Some(shaped);
        }
    }
    let field = field_as_put(elab, cx, tm)?;
    named_arithmetic_shape(elab, cx, &field, &[], depth).or_else(|| {
        // A field put as a plain atom (`P::of(n).pred` is `n`) is read as
        // that atom, so that it meets the goal's other mentions of it; a
        // stuck eliminator put there stays behind its projection
        // (issues/omega-nested-projection-of-call.md).
        let (head, _) = app_spine(&field);
        (matches!(head, Term::Var(_) | Term::GlobalTm { .. }) && nat_term_source(elab, cx, &field).is_ok())
            .then_some(field)
    })
}

/// A field of a call that unfolds to a constructor, read as what was put
/// there (issues/omega-unfolds-defined-propositions.md): `(x * y).den` is
/// `x.den * y.den`. The weak head of the whole read would
/// unfold that sum on into its recursor, so the receiver is unfolded only as
/// far as the constructor and the field projected without δ, as
/// `simplify_goal` does for a goal's fields. A field that is itself a
/// field of such a call (`Q::at(n).den.pred`, where `den` is put as
/// `P::of(n)`) is read on, up to [`FIELD_NESTING_DEPTH`] receivers deep.
fn field_as_put(elab: &Elaborator, cx: &Cx, tm: &Rc<Term>) -> Option<Rc<Term>> {
    field_as_put_within(elab, cx, tm, FIELD_NESTING_DEPTH)
}

/// The most receivers [`field_as_put`] unfolds for one read.
const FIELD_NESTING_DEPTH: u32 = 8;

fn field_as_put_within(elab: &Elaborator, cx: &Cx, tm: &Rc<Term>, depth: u32) -> Option<Rc<Term>> {
    fn with_receiver(tm: &Rc<Term>, receiver: &Rc<Term>) -> Rc<Term> {
        let mut out = (**tm).clone();
        match &mut out {
            Term::Fst { pair, .. } | Term::FstAt { pair } | Term::Snd { pair, .. } | Term::SndAt { pair } => {
                *pair = with_receiver(pair, receiver);
            }
            _ => return Rc::clone(receiver),
        }
        Rc::new(out)
    }
    // A read off a record constructed in place (a `decreases` measure at a
    // self-call's argument, `CdState(s.m - 1, …).m`) is the component as
    // put, by syntax: no receiver to unfold, and a weak head of the read
    // would unfold the field's value on into its eliminator
    // (issues/decreases-measure-record-field-unspelled.md).
    if let Some(field) = crate::spelling::project_value(tm) {
        if is_field_read(elab, field) {
            return field_as_put_within(elab, cx, field, depth.checked_sub(1)?);
        }
        return Some(Rc::clone(field));
    }
    let named = elab.named_field_read(tm);
    let (_, receiver) = named.clone().unwrap_or_else(|| projection_path(tm));
    if !head_is_global(receiver) {
        return None;
    }
    let oracle = elab.goal_oracle();
    let unfolded = Rc::new(oracle.whnf_term_bounded(&cx.gamma, receiver).ok()?);
    if !matches!(&*unfolded, Term::Pair { .. } | Term::PairAt { .. }) {
        return None;
    }
    // A named projection is read as the inline walk it names, so that the
    // walk, not the definition, meets the constructor.
    let read = match named {
        Some((path, _)) => path.into_iter().rev().fold(unfolded, |pair, first| {
            Rc::new(if first { Term::FstAt { pair } } else { Term::SndAt { pair } })
        }),
        None => with_receiver(tm, &unfolded),
    };
    let field = Rc::new(oracle.bounded(64).whnf_term_opaque(&cx.gamma, &read).ok()?);
    if is_field_read(elab, &field) {
        return field_as_put_within(elab, cx, &field, depth.checked_sub(1)?);
    }
    Some(field)
}

/// The most kernel steps a closed power may cost to be read as its value.
const POWER_EVALUATION_STEPS: Z = 4096;

/// The value of `pow(a, b)` at literal `a` and `b`, which is how a word's
/// bound is written (`pow(2, 64)`). The certificate states the value and the
/// kernel checks it by evaluation: `b` steps of the exponent, each a
/// multiplication recursing `a` times, so a power past
/// [`POWER_EVALUATION_STEPS`] stays an atom.
fn closed_power(elab: &Elaborator, cx: &Cx, tm: &Rc<Term>) -> Option<Z> {
    let args = named_args(elab, tm, "nat::Nat::pow")?;
    let [base, exponent] = args.as_slice() else {
        return None;
    };
    let literal = |arg: &Rc<Term>| {
        integer_source(&nat_term_source(elab, cx, arg).ok()?).filter(|value| *value >= 0)
    };
    let (base, exponent) = (literal(base)?, literal(exponent)?);
    if base.checked_add(1)?.checked_mul(exponent)? > POWER_EVALUATION_STEPS {
        return None;
    }
    base.checked_pow(u32::try_from(exponent).ok()?)
}

fn nat_affine_syntax(
    elab: &Elaborator,
    cx: &Cx,
    tm: &Rc<Term>,
    atoms: &mut AtomTable<ReflectedAtom>,
) -> Result<AffineSyntax, String> {
    nat_affine_syntax_within(elab, cx, tm, atoms, MEASURE_REDUCTION_DEPTH)
}

/// [`nat_affine_syntax`] with the budget the atom fallback's reduce-and-name
/// step spends (docs/omega-measure-reduction-design.md §2, §2.1): each
/// re-entry on a reduct costs one.
fn nat_affine_syntax_within(
    elab: &Elaborator,
    cx: &Cx,
    tm: &Rc<Term>,
    atoms: &mut AtomTable<ReflectedAtom>,
    depth: u32,
) -> Result<AffineSyntax, String> {
    // A projection out of a value is reflected as its reduct, so that a
    // field computing to `Succ(…)` or a sum keeps its arithmetic (§10).
    if depth > 0
        && let Some(reduct) = projection_reduct(elab, cx, tm, depth)
    {
        return nat_affine_syntax_within(elab, cx, &reduct, atoms, depth - 1);
    }
    let nat_source = nat_term_source(elab, cx, tm)?;
    if let Some(value) = integer_source(&nat_source)
        .filter(|value| *value >= 0)
        .or_else(|| closed_power(elab, cx, tm))
    {
        return Ok(AffineSyntax::Const {
            value,
            source: int(value),
        });
    }
    // An open successor is `inner + 1`: pattern variables arrive as `Succ(k)`
    // from every `match` on a `Nat`, and a measure obligation is nothing but
    // those (docs/termination-measures-design.md §3). `nat::Nat::add(k, 1)` reduces
    // to `Succ(k)`, so a certificate stated over the sum checks at the goal.
    if let Term::Succ(inner) = &**tm {
        let left_nat = nat_term_source(elab, cx, inner)?;
        return Ok(AffineSyntax::NatAdd {
            left_nat,
            right_nat: "1".into(),
            left: Box::new(nat_affine_syntax_within(elab, cx, inner, atoms, depth)?),
            right: Box::new(AffineSyntax::Const {
                value: 1,
                source: int(1),
            }),
        });
    }
    if let Some(args) = named_args(elab, tm, "nat::Nat::add") {
        if let [left, right] = args.as_slice() {
            let left_nat = nat_term_source(elab, cx, left)?;
            let right_nat = nat_term_source(elab, cx, right)?;
            return Ok(AffineSyntax::NatAdd {
                left_nat,
                right_nat,
                left: Box::new(nat_affine_syntax_within(elab, cx, left, atoms, depth)?),
                right: Box::new(nat_affine_syntax_within(elab, cx, right, atoms, depth)?),
            });
        }
    }
    if let Some(args) = named_args(elab, tm, "nat::Nat::mul") {
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
                    inner: Box::new(nat_affine_syntax_within(elab, cx, right, atoms, depth)?),
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
                    inner: Box::new(nat_affine_syntax_within(elab, cx, left, atoms, depth)?),
                });
            }
            // A factor that computes to a numeral (`Rat::ofInt(1).den`) is that
            // numeral, as on the Int side; it keeps its own spelling, which
            // the checker's conversion computes.
            if let (Some(left_nat), Some(right_nat)) = (left_source, right_source) {
                for (factor, factor_nat, inner, inner_nat, factor_on_left) in
                    [(left, &left_nat, right, &right_nat, true), (right, &right_nat, left, &left_nat, false)]
                {
                    if matches!(&***factor, Term::Var(_)) {
                        continue;
                    }
                    let Some(value) = elab
                        .goal_oracle()
                        .nat_value(&cx.gamma, factor, ATOM_COMPUTATION_STEPS)
                        .and_then(|value| Z::try_from(value).ok())
                    else {
                        continue;
                    };
                    return Ok(AffineSyntax::NatScale {
                        factor: value,
                        factor_on_left,
                        factor_nat: factor_nat.clone(),
                        inner_nat: inner_nat.clone(),
                        inner: Box::new(nat_affine_syntax_within(elab, cx, inner, atoms, depth)?),
                    });
                }
            }
        }
    }
    if let Some(args) = named_args(elab, tm, "nat::Nat::mod")
        && let [dividend, divisor] = args.as_slice()
    {
        let divisor_source = nat_term_source(elab, cx, divisor)?;
        if let Some(divisor) = integer_source(&divisor_source).filter(|value| *value >= 0) {
            let dividend_source = nat_term_source(elab, cx, dividend)?;
            let dividend_syntax = nat_affine_syntax_within(elab, cx, dividend, atoms, depth)?;
            let source = format!("int::OfNat({nat_source})");
            if divisor == 0 {
                return Ok(AffineSyntax::NatModZero {
                    source,
                    dividend_source,
                    dividend: Box::new(dividend_syntax),
                });
            }
            let quotient_nat = format!("nat::Nat::div({}, {})", dividend_source, divisor_source);
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
    if let Some(args) = named_args(elab, tm, "nat::Nat::div")
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
            let dividend_syntax = nat_affine_syntax_within(elab, cx, dividend, atoms, depth)?;
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
    // A sum at a successor bound is its last term added on, by its
    // definition (`crate::range_sum`); the certificate states the sum, which
    // converts to the range as written.
    if let Some(peeled) = crate::range_sum::peel(elab, tm)
        && crate::range_sum::op_is(elab, &peeled.op, "nat::Nat::add")
    {
        let left_nat = nat_term_source(elab, cx, &peeled.rest)?;
        let right_nat = nat_term_source(elab, cx, &peeled.last)?;
        return Ok(AffineSyntax::NatAdd {
            left_nat,
            right_nat,
            left: Box::new(nat_affine_syntax_within(elab, cx, &peeled.rest, atoms, depth)?),
            right: Box::new(nat_affine_syntax_within(elab, cx, &peeled.last, atoms, depth)?),
        });
    }
    let source = format!("int::OfNat({nat_source})");
    // An atom already met under this spelling was already asked everything
    // below, and answered "atom".
    if let Some(index) = atoms.find(|atom| atom.nat_source.as_deref() == Some(nat_source.as_str())) {
        return Ok(AffineSyntax::Atom { index, source });
    }
    // A term that computes to a numeral is that constant
    // (issues/omega-atoms-up-to-computation.md): `of_bit(True)` is `1`. The
    // certificate still spells the term, and the checker's conversion
    // computes it again.
    if head_is_global(tm)
        && let Some(value) = elab
            .goal_oracle()
            .nat_value(&cx.gamma, tm, ATOM_COMPUTATION_STEPS)
            .and_then(|value| Z::try_from(value).ok())
    {
        return Ok(AffineSyntax::Const {
            value,
            source: int(value),
        });
    }
    // The atom fallback (docs/omega-measure-reduction-design.md §2): before a
    // measure at a constructor pattern becomes an opaque atom, ask whether
    // reduction reaches arithmetic, and name the reduct's leaves by conversion
    // against the original's own spelling.
    if depth > 0
        && let Some(named) = reduce_and_name(elab, cx, tm, depth)
    {
        return nat_affine_syntax_within(elab, cx, &named, atoms, depth - 1);
    }
    // A call that computes to a successor of something the source names
    // (issues/omega-unfolds-defined-propositions.md): a shifted positive's
    // `p.val()` is `Succ(p.pred)`, so it is at least one, and `p.mul(q).val()`
    // reads on through the field to its arithmetic
    // (`crates/elab/tests/omega_defined_propositions.rs` declares one).
    if depth > 0
        && let Some(successor) = computed_successor(elab, cx, tm, depth)
    {
        return nat_affine_syntax_within(elab, cx, &successor, atoms, depth - 1);
    }
    if let Some(index) = convertible_atom(elab, cx, tm, atoms, Carrier::Nat) {
        return Ok(AffineSyntax::Atom { index, source });
    }
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

/// Evaluation steps an atom may spend proving it is a numeral, or that it
/// converts to an atom already in the table
/// (issues/omega-atoms-up-to-computation.md). Atoms are reflected per
/// hypothesis, so this is a probe's budget: past it, the atom stays opaque.
const ATOM_COMPUTATION_STEPS: u64 = 256;

fn head_is_global(tm: &Rc<Term>) -> bool {
    matches!(app_spine(tm).0, Term::GlobalTm { .. })
}

/// A plain atom of `carrier` already in the table that `tm` converts to: the same head
/// at the same arity, differing in arguments that may compute
/// (`f(append(Nil, Nil))` against `f(Nil)`). Arguments that are distinct
/// variables on both sides cannot meet by computation, so a pair differing
/// only there is never asked — every `toNat(w)` against `toNat(v)` in a word
/// proof. A field read is compared by its receiver, along the same
/// projection path: `step_fold(wc_region(), …).lines` against
/// `step_fold(ReadonlyLoop(wc_body), …).lines`.
fn convertible_atom(
    elab: &Elaborator,
    cx: &Cx,
    tm: &Rc<Term>,
    atoms: &AtomTable<ReflectedAtom>,
    carrier: Carrier,
) -> Option<AtomId> {
    let (path, receiver) = projection_path(tm);
    let (head, args) = app_spine(receiver);
    if args.is_empty() {
        return None;
    }
    let oracle = elab.goal_oracle().bounded(ATOM_COMPUTATION_STEPS);
    let mut carrier_ty: Option<Option<(Type, Level)>> = None;
    atoms.find(|atom| {
        if atom.nat_source.is_some() != (carrier == Carrier::Nat) || atom.division.is_some() {
            return false;
        }
        let (other_path, other_receiver) = projection_path(&atom.term);
        if other_path != path {
            return false;
        }
        let (other_head, other_args) = app_spine(other_receiver);
        if *other_head != *head || other_args.len() != args.len() {
            return false;
        }
        let may_meet = args.iter().zip(&other_args).any(|(a, b)| {
            a != b && !matches!((&***a, &***b), (Term::Var(_), Term::Var(_)))
        });
        if !may_meet {
            return false;
        }
        let Some((ty, level)) = carrier_ty
            .get_or_insert_with(|| match carrier {
                Carrier::Nat => Some((Type::Nat, Level::Zero)),
                Carrier::Int => int_carrier(elab, cx),
            })
            .as_ref()
        else {
            return false;
        };
        oracle.convert_term(&cx.gamma, Layer::Prog, tm, &atom.term, ty, level).is_ok()
    })
}

/// Is `tm` a field read: an inline projection, or a named one
/// ([`Elaborator::named_field_read`])?
fn is_field_read(elab: &Elaborator, tm: &Rc<Term>) -> bool {
    crate::spelling::proj_of(tm).is_some() || elab.named_field_read(tm).is_some()
}

/// The projections `tm` reads, outermost first (`true` for `fst`), and the
/// term they read from.
fn projection_path(tm: &Rc<Term>) -> (Vec<bool>, &Rc<Term>) {
    let mut path = Vec::new();
    let mut cur = tm;
    while let Some((first, pair)) = crate::spelling::proj_of(cur) {
        path.push(first);
        cur = pair;
    }
    (path, cur)
}

/// Which side of the table an atom lives on: a Nat atom carries its Nat
/// spelling, an Int atom does not.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Carrier {
    Nat,
    Int,
}

/// Re-entries the atom fallback may spend on a reduct
/// (docs/omega-measure-reduction-design.md §2.1). Two, so a measure whose
/// unfolding yields two successors still lands on a named leaf.
const MEASURE_REDUCTION_DEPTH: u32 = 2;

/// §2 steps 1–3. `None` leaves the original term to be interned unchanged,
/// which is every case where reduction bought nothing.
fn reduce_and_name(elab: &Elaborator, cx: &Cx, tm: &Rc<Term>, depth: u32) -> Option<Rc<Term>> {
    let (head, args) = app_spine(tm);
    // Cheap gate on step 1: the shape §2 is about is a call one of whose
    // arguments is a constructor value. Everything else — a call at a
    // variable, a projection out of a neutral — is left exactly as it was,
    // and pays no reduction.
    if !matches!(head, Term::GlobalTm { .. }) || !args.iter().any(|arg| is_ctor_value(arg)) {
        return None;
    }
    let candidates = recursive_field_candidates(elab, cx, tm);
    let named = named_arithmetic_reduct(elab, cx, tm, &candidates, depth)?;
    (*named != **tm).then_some(named)
}

/// The bounded weak head of a global call when it is `Succ` of a leaf that
/// spells, or reaches one by [`named_arithmetic_shape`]'s own reduction.
/// Anything else, a call stuck on a match among them, stays an atom.
fn computed_successor(elab: &Elaborator, cx: &Cx, tm: &Rc<Term>, depth: u32) -> Option<Rc<Term>> {
    if !head_is_global(tm) {
        return None;
    }
    let reduct = Rc::new(elab.goal_oracle().whnf_term_bounded(&cx.gamma, tm).ok()?);
    if !matches!(&*reduct, Term::Succ(_)) {
        return None;
    }
    named_arithmetic_shape(elab, cx, &reduct, &[], depth)
}

/// The Int constructor value `OfNat(e)` a global call computes to, when `e`
/// spells: `x.den.int()` is `OfNat(x.den)`. The Nat side then reads
/// `e`, so the call meets the same atoms a Nat fact about them states.
fn computed_of_nat(elab: &Elaborator, cx: &Cx, tm: &Rc<Term>) -> Option<Rc<Term>> {
    if !head_is_global(tm) {
        return None;
    }
    let reduct = Rc::new(elab.goal_oracle().whnf_term_bounded(&cx.gamma, tm).ok()?);
    let payload = of_nat_payload(elab, &reduct)?;
    nat_term_source(elab, cx, payload).ok()?;
    Some(reduct)
}

/// The applied spine of `tm`: its head and its arguments, outermost last.
fn app_spine(tm: &Rc<Term>) -> (&Term, Vec<&Rc<Term>>) {
    let mut args = Vec::new();
    let mut head = &**tm;
    while let Some((fun, arg)) = crate::spelling::app_of(head) {
        args.push(arg);
        head = fun;
    }
    args.reverse();
    (head, args)
}

fn is_ctor_value(tm: &Rc<Term>) -> bool {
    matches!(
        &**tm,
        Term::Supf { .. }
            | Term::Inl { .. }
            | Term::Inr { .. }
            | Term::InlAt { .. }
            | Term::InrAt { .. }
            | Term::Zero
            | Term::Succ(_)
    )
}

/// §2 step 3's candidates: `g(ā[C(f̄) ↦ fᵢ])` for each recursive field `fᵢ` of
/// each constructor argument. Built from the *original* term, so a candidate
/// spells under a name the rest of the goal produces too (§5); one that does
/// not spell is no use to interning and is dropped here.
fn recursive_field_candidates(elab: &Elaborator, cx: &Cx, tm: &Rc<Term>) -> Vec<Rc<Term>> {
    let (_, args) = app_spine(tm);
    let arity = args.len();
    let mut out = Vec::new();
    for (position, arg) in args.iter().enumerate() {
        let fields = match &***arg {
            Term::Supf { shape, label, children, .. } => {
                let Some(ind) = elab.display_tag_of(shape) else { continue };
                let index = crate::spelling::inj_path(label, ind.ctors.len()).ctor;
                let Some(ctor) = ind.ctors.get(index) else { continue };
                if ctor.container().is_some() { continue; }
                let Some(fields) = crate::spelling::tuple_fields(elab, cx, children, 0, ctor.arity(), 0) else {
                    continue;
                };
                fields
            }
            Term::Succ(inner) => vec![Rc::clone(inner)],
            _ => continue,
        };
        for field in fields {
            // `app_spine` counts from the head; `with_arg_at` from the outside.
            let candidate = with_arg_at(tm, arity - 1 - position, &field);
            if nat_term_source(elab, cx, &candidate).is_ok() {
                out.push(candidate);
            }
        }
    }
    out
}

/// `tm` with the argument `outward` applications from the outside replaced.
fn with_arg_at(tm: &Rc<Term>, outward: usize, new: &Rc<Term>) -> Rc<Term> {
    // The checked spelling carries no annotation that a replaced argument
    // could leave stale (docs/app-by-head-type-design.md §6.2).
    if let Term::AppAt { fun, arg } = &**tm {
        let (fun, arg) = if outward == 0 {
            (Rc::clone(fun), Rc::clone(new))
        } else {
            (with_arg_at(fun, outward - 1, new), Rc::clone(arg))
        };
        return Rc::new(Term::AppAt { fun, arg });
    }
    let Term::App {
        fun,
        dom_level,
        cod_level,
        dom,
        cod,
        arg,
    } = &**tm
    else {
        return Rc::clone(tm);
    };
    let (fun, arg) = if outward == 0 {
        (Rc::clone(fun), Rc::clone(new))
    } else {
        (with_arg_at(fun, outward - 1, new), Rc::clone(arg))
    };
    Rc::new(Term::App {
        fun,
        dom_level: dom_level.clone(),
        cod_level: cod_level.clone(),
        dom: Rc::clone(dom),
        cod: Rc::clone(cod),
        arg,
    })
}

/// §2 steps 1–2 on `tm`, with step 3 applied to each leaf: the reduct is kept
/// only when its head became arithmetic, and it is rebuilt so that every leaf
/// spells.
fn named_arithmetic_reduct(
    elab: &Elaborator,
    cx: &Cx,
    tm: &Rc<Term>,
    candidates: &[Rc<Term>],
    depth: u32,
) -> Option<Rc<Term>> {
    if depth == 0 {
        return None;
    }
    let reduct = Rc::new(elab.goal_oracle().whnf_term_bounded(&cx.gamma, tm).ok()?);
    named_arithmetic_shape(elab, cx, &reduct, candidates, depth)
}

/// §2 step 2's test and step 3's rebuild, on a term already in weak head
/// normal form: an arithmetic head is kept and each of its leaves named,
/// anything else declines.
fn named_arithmetic_shape(
    elab: &Elaborator,
    cx: &Cx,
    tm: &Rc<Term>,
    candidates: &[Rc<Term>],
    depth: u32,
) -> Option<Rc<Term>> {
    match &**tm {
        Term::Zero => return Some(Rc::clone(tm)),
        Term::Succ(inner) => {
            let named = name_leaf(elab, cx, inner, candidates, depth)?;
            return Some(Rc::new(Term::Succ(named)));
        }
        _ => {}
    }
    for name in ["nat::Nat::add", "nat::Nat::mul", "nat::Nat::div", "nat::Nat::mod"] {
        let Some(args) = named_args(elab, tm, name) else {
            continue;
        };
        let [left, right] = args.as_slice() else {
            continue;
        };
        let left = name_leaf(elab, cx, left, candidates, depth)?;
        let right = name_leaf(elab, cx, right, candidates, depth)?;
        let rebuilt = with_arg_at(tm, 0, &right);
        return Some(with_arg_at(&rebuilt, 1, &left));
    }
    None
}

/// §2 step 3 at one leaf of the reduct, plus §2.1: a leaf no candidate
/// converts against is reduced once more under the *same* candidates, since
/// they are the only spellings the rest of the goal shares.
fn name_leaf(
    elab: &Elaborator,
    cx: &Cx,
    leaf: &Rc<Term>,
    candidates: &[Rc<Term>],
    depth: u32,
) -> Option<Rc<Term>> {
    if nat_term_source(elab, cx, leaf).is_ok() {
        return Some(Rc::clone(leaf));
    }
    for candidate in candidates {
        if elab
            .goal_oracle()
            .convert_term(
                &cx.gamma,
                Layer::Prog,
                leaf,
                candidate,
                &Type::Nat,
                &Level::Zero,
            )
            .is_ok()
        {
            return Some(Rc::clone(candidate));
        }
    }
    // A leaf that is *already* arithmetic — `nat::Nat::add(u₁, u₂)` under the
    // successor of a branching measure — is decomposed where it stands.
    // Reducing it would only unfold `add` into its eliminator and lose the
    // head this reflection is looking for.
    if let Some(shaped) = named_arithmetic_shape(elab, cx, leaf, candidates, depth) {
        return Some(shaped);
    }
    named_arithmetic_reduct(elab, cx, leaf, candidates, depth - 1)
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
                source: format!("int::Int::add({}, {})", left.source, right.source),
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
                source: format!("int::OfNat(nat::Nat::add({}, {}))", left_nat, right_nat),
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
                source: format!("int::Int::neg({})", inner.source),
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
                    format!("int::Int::mul({}, {})", int(*factor), inner.source)
                } else {
                    format!("int::Int::mul({}, {})", inner.source, int(*factor))
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
                    format!("int::OfNat(nat::Nat::mul({}, {}))", factor_nat, inner_nat)
                } else {
                    format!("int::OfNat(nat::Nat::mul({}, {}))", inner_nat, factor_nat)
                },
                linear,
                row_source,
                proof,
            })
        }
    }
}

/// What an ordinary reflection read, before any of it is rendered: one
/// relation per local that states one, the local's name beside it, over one
/// atom table.
struct Collected {
    atoms: AtomTable<ReflectedAtom>,
    relations: Vec<ReflectedConstraint<AffineSyntax, String>>,
    names: Vec<String>,
    skipped: Vec<String>,
}

/// An ordinary reflection, rendered: the facts, the atom list's source, the
/// atoms' labels, and each atom's own source for CutSat.
/// The facts, the atom list's spelling in them, the atom labels, the atom
/// sources a CutSat fallback needs, and the literal list when the spelling
/// is [`ATOMS`].
type Reflection = (Vec<InitialAssumption>, String, Vec<String>, Option<Vec<String>>, Option<String>);

/// The relations among the locals, or only among those `keep` names.
/// `None` when a local is already a reflected `dot` row (the explicit
/// frontend's input) or no local states a relation.
fn collect_ordinary(
    elab: &Elaborator,
    cx: &Cx,
    keep: Option<&std::collections::HashSet<String>>,
) -> Result<Option<Collected>, String> {
    let mut atoms = AtomTable::default();
    let mut relations = Vec::new();
    let mut names = Vec::new();
    let mut skipped = Vec::new();
    for (name, ty) in local_facts(elab, cx) {
        if name.starts_with("__cutsat_nat_eq_") || name.starts_with("__cutsat_int_eq_") {
            continue;
        }
        if keep.is_some_and(|keep| !keep.contains(&name)) {
            continue;
        }
        if relation_args(elab, &ty).is_some_and(|(left, right)|
            dot_args(elab, left).is_some() || dot_args(elab, right).is_some()) {
            return Ok(None);
        }
        let saved_atoms = atoms.iter().len();
        let reflected = reflect_ordinary_relation(elab, cx, &name, &ty, &mut atoms);
        match reflected {
            Ok(Some(relation)) => relations.push(relation),
            Ok(None) => continue,
            Err(error) if error.contains("could not spell") => {
                atoms.truncate(saved_atoms);
                skipped.push(format!("{name}: {error}"));
                continue;
            }
            Err(error) => return Err(error),
        }

        names.push(name);
    }
    if relations.is_empty() && skipped.is_empty() {
        return Ok(None);
    }
    Ok(Some(Collected { atoms, relations, names, skipped }))
}

/// Reflect one fact. The caller rolls back its atoms if source spelling fails.
/// A fact whose head is a defined proposition is reflected as the relation
/// it unfolds to; its evidence is still the fact's name, which the checker
/// converts to the unfolded statement at every use.
fn reflect_ordinary_relation(
    elab: &Elaborator,
    cx: &Cx,
    name: &str,
    ty: &Type,
    atoms: &mut AtomTable<ReflectedAtom>,
) -> Result<Option<ReflectedConstraint<AffineSyntax, String>>, String> {
    let saved_atoms = atoms.iter().len();
    match reflect_stated_relation(elab, cx, name, ty, atoms) {
        Ok(Some(relation)) => return Ok(Some(relation)),
        Ok(None) => {}
        // A side the speller cannot name may be a redex it can once
        // simplified: `Int::cong(λ (t: Int) => e * t, p)` states
        // `(λ t => e * t)(a) = (λ t => e * t)(b)`.
        // Only that shape is retried: an unspellable fact is skipped on
        // every call, and simplifying one costs a reduction per node.
        Err(error) if error.contains("could not spell") => {
            let beta_redex = |tm: &Rc<Term>| {
                crate::spelling::app_of(tm).is_some_and(|(fun, _)| matches!(&**fun, Term::Lam { .. }))
            };
            let decoded = crate::inductive::decoded(ty);
            let Type::Id { lhs, rhs, .. } = &*decoded else {
                return Err(error);
            };
            if !beta_redex(lhs) && !beta_redex(rhs) {
                return Err(error);
            }
            let simplified = crate::goal_combinators::simplify_goal(elab, cx, &decoded);
            atoms.truncate(saved_atoms);
            return reflect_stated_relation(elab, cx, name, &simplified, atoms);
        }
        Err(error) => return Err(error),
    }
    let reads = |ty: &Type| reads_as_relation(elab, cx, ty) || negated_domain(elab, cx, ty).is_some();
    match unfolded_proposition(elab, cx, ty, reads) {
        Some(unfolded) => reflect_stated_relation(elab, cx, name, &unfolded, atoms),
        None => Ok(None),
    }
}

fn reflect_stated_relation(
    elab: &Elaborator,
    cx: &Cx,
    name: &str,
    ty: &Type,
    atoms: &mut AtomTable<ReflectedAtom>,
) -> Result<Option<ReflectedConstraint<AffineSyntax, String>>, String> {
    let decoded_ty = crate::inductive::decoded(&ty);
    let (domain, left, right, relation, proof) =
        if let Some((left, right)) = relation_args(elab, &ty) {
            (
                Domain::Int,
                affine_syntax(elab, cx, left, atoms)?,
                affine_syntax(elab, cx, right, atoms)?,
                Relation::Le,
                name.to_string(),
            )
        } else if let Some((left, right)) = strict_relation_args(elab, &ty) {
            let left = AffineSyntax::Add {
                left: Box::new(affine_syntax(elab, cx, left, atoms)?),
                right: Box::new(AffineSyntax::Const {
                    value: 1,
                    source: int(1),
                }),
            };
            (
                Domain::Int,
                left,
                affine_syntax(elab, cx, right, atoms)?,
                Relation::Le,
                name.to_string(),
            )
        } else if let Some((left, right)) =
            equality_args(elab, cx, &ty).or_else(|| equality_args(elab, cx, &decoded_ty))
        {
            (
                Domain::Int,
                affine_syntax(elab, cx, left, atoms)?,
                affine_syntax(elab, cx, right, atoms)?,
                Relation::Eq,
                name.to_string(),
            )
        } else if let Some((left, right)) = nat_relation_args(elab, &ty) {
            let left_source = nat_term_source(elab, cx, left)?;
            let right_source = nat_term_source(elab, cx, right)?;
            (
                Domain::NatEmbedded,
                nat_affine_syntax(elab, cx, left, atoms)?,
                nat_affine_syntax(elab, cx, right, atoms)?,
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
                left: Box::new(nat_affine_syntax(elab, cx, left, atoms)?),
                right: Box::new(AffineSyntax::Const {
                    value: 1,
                    source: int(1),
                }),
            };
            (
                Domain::NatEmbedded,
                left,
                nat_affine_syntax(elab, cx, right, atoms)?,
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
                nat_affine_syntax(elab, cx, left, atoms)?,
                nat_affine_syntax(elab, cx, right, atoms)?,
                Relation::Eq,
                format!("int::Int::cong_ofnat({})", name),
            )
        } else if let Some(domain) = negated_domain(elab, cx, &ty) {
            // `¬(x <= y)` at a defined `<=` reads the relation underneath.
            let domain = if reads_as_relation(elab, cx, &domain) {
                domain
            } else {
                unfolded_proposition(elab, cx, &domain, |ty| reads_as_relation(elab, cx, ty))
                    .unwrap_or(domain)
            };
            let decoded_domain = crate::inductive::decoded(&domain);
            if let Some((left, right)) = relation_args(elab, &domain) {
                let left_source = int_term_source(elab, cx, left)?;
                let right_source = int_term_source(elab, cx, right)?;
                let strict_left = AffineSyntax::Add {
                    left: Box::new(affine_syntax(elab, cx, right, atoms)?),
                    right: Box::new(AffineSyntax::Const {
                        value: 1,
                        source: int(1),
                    }),
                };
                (
                    Domain::Int,
                    strict_left,
                    affine_syntax(elab, cx, left, atoms)?,
                    Relation::Le,
                    format!(
                        "int::Int::lt_of_not_le({}, {}, {})",
                        right_source, left_source, name
                    ),
                )
            } else if let Some((left, right)) = strict_relation_args(elab, &domain) {
                let left_source = int_term_source(elab, cx, left)?;
                let right_source = int_term_source(elab, cx, right)?;
                (
                    Domain::Int,
                    affine_syntax(elab, cx, right, atoms)?,
                    affine_syntax(elab, cx, left, atoms)?,
                    Relation::Le,
                    format!(
                        "int::Int::le_of_not_lt({}, {}, {})",
                        left_source, right_source, name
                    ),
                )
            } else if let Some((left, right)) = nat_relation_args(elab, &domain) {
                let left_source = nat_term_source(elab, cx, left)?;
                let right_source = nat_term_source(elab, cx, right)?;
                let strict_left = AffineSyntax::Add {
                    left: Box::new(nat_affine_syntax(elab, cx, right, atoms)?),
                    right: Box::new(AffineSyntax::Const {
                        value: 1,
                        source: int(1),
                    }),
                };
                (
                    Domain::NatEmbedded,
                    strict_left,
                    nat_affine_syntax(elab, cx, left, atoms)?,
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
                    nat_affine_syntax(elab, cx, right, atoms)?,
                    nat_affine_syntax(elab, cx, left, atoms)?,
                    Relation::Le,
                    format!(
                        "omega::nat_le_to_int({}, {}, omega::nat_le_of_not_lt({}, {}, {}))",
                        right_source, left_source, left_source, right_source, name,
                    ),
                )
            } else if let Some((left, right)) = equality_args(elab, cx, &domain)
                .or_else(|| equality_args(elab, cx, &decoded_domain))
            {
                // A disequality goes to CutSat whole, in place of the two
                // strict cases an up-front split would re-run Omega on.
                (
                    Domain::Int,
                    affine_syntax(elab, cx, left, atoms)?,
                    affine_syntax(elab, cx, right, atoms)?,
                    Relation::Ne,
                    name.to_string(),
                )
            } else if let Some((left, right)) = nat_equality_args(elab, cx, &domain)
                .or_else(|| nat_equality_args(elab, cx, &decoded_domain))
            {
                (
                    Domain::NatEmbedded,
                    nat_affine_syntax(elab, cx, left, atoms)?,
                    nat_affine_syntax(elab, cx, right, atoms)?,
                    Relation::Ne,
                    format!("int::Int::ofnat_ne({})", name),
                )
            } else {
                return Ok(None);
            }
        } else {
            return Ok(None);
        };
    Ok(Some(ReflectedConstraint {
        domain,
        lhs: left,
        relation,
        rhs: right,
        evidence: proof,
    }))
}

/// How many times [`relevant_layers`] widens past the goal's own atoms
/// before the caller falls back to every fact.
const RELEVANCE_WIDENINGS: usize = 3;

/// The locals worth refuting the goal with, as widening layers, each fewer
/// than all of them (issues/omega-relevant-facts-only.md).
///
/// The goal is the negated-goal local every relation goal reduces to. The
/// first layer is the facts over the goal's atoms alone; each next layer
/// takes in the atoms of every fact that touches the previous layer's atoms,
/// then the facts over those. A division atom brings its dividend's atoms,
/// since its bounds are stated over them. A fact with no atoms is in every
/// layer, since `1 < 0` refutes anything.
///
/// Layers are an order of attempts, not a claim: a system can need a fact
/// no layer reaches (its contradiction among facts away from the goal, or a
/// chain longer than [`RELEVANCE_WIDENINGS`]), so the caller ends with every
/// fact. What they buy is the common case, a goal about a few atoms in a
/// context full of facts that share one of them (every word equation in a
/// proof mentions the same `v`), which connectivity alone keeps whole.
fn relevant_layers(collected: &Collected) -> Vec<std::collections::HashSet<String>> {
    use std::collections::HashSet;
    fn atoms_of(syntax: &AffineSyntax, out: &mut Vec<usize>) {
        match syntax {
            AffineSyntax::Atom { index, .. } => out.push(index.index()),
            AffineSyntax::Mod { expanded: inner, .. }
            | AffineSyntax::NatMod { expanded: inner, .. }
            | AffineSyntax::ModZero { dividend: inner, .. }
            | AffineSyntax::NatModZero { dividend: inner, .. }
            | AffineSyntax::Neg { inner }
            | AffineSyntax::NatScale { inner, .. }
            | AffineSyntax::Scale { inner, .. } => atoms_of(inner, out),
            AffineSyntax::Add { left, right } | AffineSyntax::NatAdd { left, right, .. } => {
                atoms_of(left, out);
                atoms_of(right, out);
            }
            AffineSyntax::Const { .. }
            | AffineSyntax::DivZero { .. }
            | AffineSyntax::NatDivZero { .. } => {}
        }
    }

    let Some(goal) = collected.names.iter().position(|name| name == "__omega_negated_goal") else {
        return Vec::new();
    };
    // Each atom with the atoms its division bounds bring along, closed.
    let atom_count = collected.atoms.iter().len();
    let mut brings: Vec<Vec<usize>> = vec![Vec::new(); atom_count];
    for (index, atom) in collected.atoms.iter_with_ids() {
        if let Some(division) = &atom.division {
            atoms_of(&division.dividend, &mut brings[index.index()]);
        }
    }
    let close = |seed: Vec<usize>| {
        let mut closed: HashSet<usize> = HashSet::new();
        let mut work = seed;
        while let Some(atom) = work.pop() {
            if closed.insert(atom) {
                work.extend(brings[atom].iter().copied());
            }
        }
        closed
    };
    let facts: Vec<HashSet<usize>> = collected
        .relations
        .iter()
        .map(|relation| {
            let mut atoms = Vec::new();
            atoms_of(&relation.lhs, &mut atoms);
            atoms_of(&relation.rhs, &mut atoms);
            close(atoms)
        })
        .collect();

    let mut layers = Vec::new();
    let mut reach = facts[goal].clone();
    for _ in 0..=RELEVANCE_WIDENINGS {
        let layer: HashSet<String> = facts
            .iter()
            .zip(&collected.names)
            .filter(|(atoms, _)| atoms.is_subset(&reach))
            .map(|(_, name)| name.clone())
            .collect();
        if layer.len() == collected.names.len() {
            break;
        }
        if layers.last().is_none_or(|last: &HashSet<String>| last.len() < layer.len()) {
            layers.push(layer);
        }
        let wider: HashSet<usize> = facts
            .iter()
            .filter(|atoms| !atoms.is_disjoint(&reach))
            .flat_map(|atoms| atoms.iter().copied())
            .collect();
        if wider.is_subset(&reach) {
            break;
        }
        reach.extend(wider);
    }
    layers
}

/// Render collected relations as Omega's initial facts over their atom list.
fn reflect_collected(collected: Collected) -> Result<Reflection, String> {
    let Collected { atoms, mut relations, .. } = collected;
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
                    division.dividend_source, nat_lit(divisor_pred)
                ),
                format!(
                    "omega::nat_div_upper({}, {})",
                    division.dividend_source, nat_lit(divisor_pred)
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
    let atoms_literal = atom_list_source(&atoms);
    let atoms_source = ATOMS.to_string();
    let mut facts = Vec::with_capacity(relations.len());
    let mut disequalities = Vec::new();
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
                disequality: None,
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
                disequality: None,
            });
        } else if reflected.relation == Relation::Ne {
            let proof = format!(
                "omega::normalized_ne_value({}, {}, {}, {}, {}, {}, {}, {}, {}, {})",
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
            disequalities.push(InitialAssumption {
                coeffs: linear.coeffs,
                row_source,
                interval: Interval::exact(upper),
                lower: None,
                upper: None,
                exact: None,
                disequality: Some(proof),
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
                "omega::atom_nonnegative({}, {}, int::Int::zero_le_ofNat({}))",
                index, atoms_source, nat_source,
            )),
            upper: None,
            exact: None,
            disequality: None,
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
    facts.extend(disequalities);
    Ok((facts, atoms_source, atom_labels, Some(atom_sources), Some(atoms_literal)))
}

pub(crate) fn int(value: Z) -> String {
    int_ctor(value)
}

fn literal_int_nonzero(value: Z) -> Result<String, String> {
    if value > 0 {
        return Ok(format!("omega::positive_int_nonzero({})", nat_lit(value - 1)));
    }
    if value < 0 {
        let payload = value
            .checked_neg()
            .and_then(|magnitude| magnitude.checked_sub(1))
            .ok_or("Omega cannot reconstruct the minimum `i128` divisor")?;
        return Ok(format!("omega::negative_int_nonzero({})", nat_lit(payload)));
    }
    Err("Omega requested a nonzero proof for zero".into())
}

/// A row at its atoms' full length. `Coeffs` drops trailing zeros, but the
/// rows it is compared with (`basis`, `scale` of a parent) keep one entry per
/// atom, and `dot` of a shorter row is not definitionally the same once a
/// dropped atom is neutral (`0 * x` does not reduce).
pub(crate) fn coeffs_source(coeffs: &Coeffs, atom_count: usize) -> String {
    let values = coeffs.as_slice();
    (0..atom_count.max(values.len()))
        .rev()
        .fold("list::Nil".to_string(), |tail, index| {
            format!("list::Cons({}, {tail})", int(values.get(index).copied().unwrap_or(0)))
        })
}

fn int_ctor(value: Z) -> String {
    if value >= 0 {
        format!("int::OfNat({})", nat_lit(value))
    } else {
        let payload = value.checked_neg().unwrap_or(Z::MAX) - 1;
        format!("int::NegSucc({})", nat_lit(payload))
    }
}

/// A natural constant as source: the numeral it is, at any size
/// (docs/wide-numerals-design.md). Before numerals were unbounded, a value
/// past a `u64` was spelled over its top word one byte at a time.
pub(crate) fn nat_lit(value: Z) -> String {
    debug_assert!(value >= 0, "a natural constant is nonnegative");
    value.to_string()
}

/// The value of a [`nat_lit`] spelling with its whitespace removed.
fn nat_lit_value(source: &str) -> Option<Z> {
    source.parse::<Z>().ok().filter(|value| *value >= 0)
}

pub(crate) fn literal_lt_proof(lower: Z, upper: Z) -> Result<String, String> {
    if lower >= upper {
        return Err(format!(
            "Omega cannot prove the false literal order {lower} < {upper}"
        ));
    }
    if lower >= 0 {
        return Ok(format!(
            "omega::nat_lt_to_int({}, {}, trivial)",
            nat_lit(lower), nat_lit(upper)
        ));
    }
    let lower_payload = lower
        .checked_neg()
        .and_then(|value| value.checked_sub(1))
        .ok_or("Omega cannot reconstruct the minimum `i128` literal")?;
    if upper >= 0 {
        return Ok(format!(
            "int::Int::negsucc_lt_ofnat({}, {})",
            nat_lit(lower_payload), nat_lit(upper)
        ));
    }
    let upper_payload = upper
        .checked_neg()
        .and_then(|value| value.checked_sub(1))
        .ok_or("Omega cannot reconstruct the minimum `i128` literal")?;
    Ok(format!(
        "int::Int::negsucc_lt_of_lt({}, {}, trivial)",
        nat_lit(lower_payload), nat_lit(upper_payload)
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

/// The first `≠` fact as a two-way split. `cutsat_read_equalities` skips
/// equation disequalities: CutSat already had them (`Relation::Ne`).
fn split_disequality(elab: &Elaborator, cx: &Cx, cutsat_read_equalities: bool) -> Result<Option<Certificate>, String> {
    for (name, ty) in local_facts(elab, cx) {
        let Some(domain) = negated_domain(elab, cx, &ty) else {
            continue;
        };
        let decoded = crate::inductive::decoded(&domain);
        let disequality = &name;
        if cutsat_read_equalities
            && (equality_args(elab, cx, &decoded).is_some() || nat_equality_args(elab, cx, &decoded).is_some())
        {
            continue;
        }
        let (left, right, disequality, lemma) =
            if let Some((left, right)) = equality_args(elab, cx, &decoded) {
                (
                    int_term_source(elab, cx, left)?,
                    int_term_source(elab, cx, right)?,
                    disequality.clone(),
                    "omega::diseq_elim",
                )
            } else if let Some((left, right)) = nat_equality_args(elab, cx, &decoded) {
                (
                    nat_term_source(elab, cx, left)?,
                    nat_term_source(elab, cx, right)?,
                    disequality.clone(),
                    "omega::nat_diseq_elim",
                )
            } else if let Some((divisor, dividend)) = int_divides_args(elab, &domain) {
                let divisor = int_term_source(elab, cx, divisor)?;
                let dividend = int_term_source(elab, cx, dividend)?;
                (
                    format!("int::Int::mod({dividend}, {divisor})"),
                    int(0),
                    disequality.clone(),
                    "omega::diseq_elim",
                )
            } else if let Some((divisor, dividend)) = nat_divides_args(elab, &domain) {
                let divisor = nat_term_source(elab, cx, divisor)?;
                let dividend = nat_term_source(elab, cx, dividend)?;
                let remainder = format!("nat::Nat::mod({dividend}, {divisor})");
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
            atoms: None,
            guards: None,
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
            atoms: None,
            guards: None,
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

/// The prefix of the facts a subtraction split binds: `__omega_sub{k}_case`
/// (`b <= a` or `a < b`) and `__omega_sub{k}_eq` (`(a - b) + b = a` or
/// `a - b = 0`), `k` counting the splits already around the goal.
const SUB_CASE: &str = "__omega_sub";

/// Subtraction splits one goal may sit under: each doubles the branches, and
/// a case equation whose subtraction no longer spells as it did when split
/// would otherwise be split again forever.
const SUB_SPLIT_LIMIT: usize = 6;

/// The truncated subtractions `a - b` at `Nat` that `tm` reads through the
/// arithmetic around them, outermost first; a binder's body is not entered.
fn nat_subtractions<'a>(elab: &Elaborator, tm: &'a Rc<Term>, out: &mut Vec<&'a Rc<Term>>) {
    if let Term::Succ(inner) = &**tm {
        return nat_subtractions(elab, inner, out);
    }
    if named_args(elab, tm, "nat::Nat::sub").is_some_and(|args| args.len() == 2) {
        out.push(tm);
    }
    let (head, args) = app_spine(tm);
    if matches!(head, Term::GlobalTm { .. }) {
        for arg in args {
            nat_subtractions(elab, arg, out);
        }
    }
}

/// A truncated subtraction `a - b` a fact reads as an atom, split into its two
/// cases by `omega::nat_sub_elim`, Lean's `omega`'s split: `b <= a` with
/// `(a - b) + b = a`, or `a < b` with `a - b = 0`. Each branch is `omega`
/// again with the case's two facts beside the rest, so the subtraction stays
/// one atom that both now constrain. The fact nearest the goal is asked
/// first; a subtraction a case equation already names is settled.
fn split_nat_subtraction(elab: &Elaborator, cx: &Cx) -> Result<Option<Certificate>, String> {
    if elab.key_of("omega::nat_sub_elim").is_none() {
        return Ok(None);
    }
    let facts = local_facts(elab, cx);
    let spelled_subtractions = |ty: &Type| {
        let mut found = Vec::new();
        if let Some((_, left, right)) = integral_sides(elab, cx, ty) {
            let mut terms = Vec::new();
            nat_subtractions(elab, &left, &mut terms);
            nat_subtractions(elab, &right, &mut terms);
            found.extend(terms.into_iter().filter_map(|tm| {
                let args = named_args(elab, tm, "nat::Nat::sub")?;
                Some((
                    nat_term_source(elab, cx, tm).ok()?,
                    nat_term_source(elab, cx, args[0]).ok()?,
                    nat_term_source(elab, cx, args[1]).ok()?,
                ))
            }));
        }
        found
    };
    let case_equations: Vec<_> = facts
        .iter()
        .filter(|(name, _)| name.starts_with(SUB_CASE) && name.ends_with("_eq"))
        .collect();
    if case_equations.len() >= SUB_SPLIT_LIMIT {
        return Ok(None);
    }
    let settled: std::collections::HashSet<String> = case_equations
        .iter()
        .filter_map(|(_, ty)| spelled_subtractions(ty).into_iter().next())
        .map(|(source, _, _)| source)
        .collect();
    let k = case_equations.len();
    for (_, ty) in facts.iter().rev() {
        let Some((_, minuend, subtrahend)) =
            spelled_subtractions(ty).into_iter().find(|(source, _, _)| !settled.contains(source))
        else {
            continue;
        };
        let source = format!(
            "omega::nat_sub_elim({minuend}, {subtrahend}, \
             {SUB_CASE}{k}_case {SUB_CASE}{k}_eq ⊢ omega, \
             {SUB_CASE}{k}_case {SUB_CASE}{k}_eq ⊢ omega)",
        );
        return Ok(Some(Certificate {
            atoms: None,
            guards: None,
            expr: parse_generated_expr(&source)?,
            source,
            report: wrapper_report("omega::nat_sub_elim", 1),
        }));
    }
    Ok(None)
}

/// The case facts an `Int::toNat` split binds (`__omega_tonat{k}_case`,
/// `__omega_tonat{k}_eq`).
const TO_NAT_CASE: &str = "__omega_tonat";

/// The `x.toNat()` reads in `tm`, outermost first, through any application
/// and an Int constructor's payload (`OfNat(x.toNat())`); a binder's body is
/// not entered.
fn int_to_nats<'a>(elab: &Elaborator, tm: &'a Rc<Term>, out: &mut Vec<&'a Rc<Term>>) {
    if let Term::Succ(inner) = &**tm {
        return int_to_nats(elab, inner, out);
    }
    if let Some((_, inner)) = int_ctor_payload(elab, tm) {
        return int_to_nats(elab, inner, out);
    }
    if named_args(elab, tm, "int::Int::toNat").is_some_and(|args| args.len() == 1) {
        out.push(tm);
    }
    let (head, args) = app_spine(tm);
    if !matches!(head, Term::Lam { .. }) {
        for arg in args {
            int_to_nats(elab, arg, out);
        }
    }
}

/// An `x.toNat()` a fact reads as an atom, split into its two cases by
/// `omega::int_to_nat_elim`, as `split_nat_subtraction` splits `a - b`:
/// `0 <= x` with `OfNat(x.toNat()) = x`, or `x < 0` with `x.toNat() = 0`.
/// Each branch is `omega` again, so the read stays one Nat atom that the
/// case ties to the integer `x`. A read a case equation names is settled.
fn split_int_to_nat(elab: &Elaborator, cx: &Cx) -> Result<Option<Certificate>, String> {
    if elab.key_of("omega::int_to_nat_elim").is_none() {
        return Ok(None);
    }
    let facts = local_facts(elab, cx);
    let spelled_reads = |ty: &Type| {
        let mut found = Vec::new();
        if let Some((_, left, right)) = integral_sides(elab, cx, ty) {
            let mut terms = Vec::new();
            int_to_nats(elab, &left, &mut terms);
            int_to_nats(elab, &right, &mut terms);
            found.extend(terms.into_iter().filter_map(|tm| {
                let args = named_args(elab, tm, "int::Int::toNat")?;
                Some((nat_term_source(elab, cx, tm).ok()?, int_term_source(elab, cx, args[0]).ok()?))
            }));
        }
        found
    };
    let case_equations: Vec<_> = facts
        .iter()
        .filter(|(name, _)| name.starts_with(TO_NAT_CASE) && name.ends_with("_eq"))
        .collect();
    if case_equations.len() >= SUB_SPLIT_LIMIT {
        return Ok(None);
    }
    let settled: std::collections::HashSet<String> = case_equations
        .iter()
        .filter_map(|(_, ty)| spelled_reads(ty).into_iter().next())
        .map(|(source, _)| source)
        .collect();
    let k = case_equations.len();
    for (_, ty) in facts.iter().rev() {
        let Some((_, x)) = spelled_reads(ty).into_iter().find(|(source, _)| !settled.contains(source)) else {
            continue;
        };
        let source = format!(
            "omega::int_to_nat_elim({x}, \
             {TO_NAT_CASE}{k}_case {TO_NAT_CASE}{k}_eq ⊢ omega, \
             {TO_NAT_CASE}{k}_case {TO_NAT_CASE}{k}_eq ⊢ omega)",
        );
        return Ok(Some(Certificate {
            atoms: None,
            guards: None,
            expr: parse_generated_expr(&source)?,
            source,
            report: wrapper_report("omega::int_to_nat_elim", 1),
        }));
    }
    Ok(None)
}

/// The case facts a `max`/`min` split binds (`__omega_mm{k}_case`, the
/// order of the two arguments, and `__omega_mm{k}_eq`, which of them the read
/// is).
const MAX_MIN_CASE: &str = "__omega_mm";

/// The `max`/`min` reads omega splits, at `Nat` and `Int`: the definition,
/// whether its arguments are integers, and the lemma that splits it.
const MAX_MIN_READS: [(&str, bool, &str); 4] = [
    ("nat::Nat::max", false, "omega::nat_max_elim"),
    ("nat::Nat::min", false, "omega::nat_min_elim"),
    ("int::Int::max", true, "omega::int_max_elim"),
    ("int::Int::min", true, "omega::int_min_elim"),
];

/// The `max`/`min` reads in `tm` (each with its `MAX_MIN_READS` row),
/// outermost first, through any application and an Int constructor's payload;
/// a binder's body is not entered.
fn max_min_reads<'a>(elab: &Elaborator, tm: &'a Rc<Term>, out: &mut Vec<(&'a Rc<Term>, usize)>) {
    if let Term::Succ(inner) = &**tm {
        return max_min_reads(elab, inner, out);
    }
    if let Some((_, inner)) = int_ctor_payload(elab, tm) {
        return max_min_reads(elab, inner, out);
    }
    if let Some(row) = MAX_MIN_READS
        .iter()
        .position(|(name, _, _)| named_args(elab, tm, name).is_some_and(|args| args.len() == 2))
    {
        out.push((tm, row));
    }
    let (head, args) = app_spine(tm);
    if !matches!(head, Term::Lam { .. }) {
        for arg in args {
            max_min_reads(elab, arg, out);
        }
    }
}

/// A `a.max(b)` or `a.min(b)` a fact reads as an atom, at `Nat` or `Int`,
/// split by its `omega::*_elim` lemma into the order of its arguments: `a <=
/// b` with the read equal to `b` (`max`) or `a` (`min`), or `b <= a` with the
/// other. Each branch is `omega` again, so the read stays one atom that the
/// case's equation names; the certificate cites the `max_eq_*`/`min_eq_*`
/// theorems and never unfolds the definition. A read a case equation names is
/// settled (issues/omega-reads-min-max.md, design §20).
fn split_max_min(elab: &Elaborator, cx: &Cx) -> Result<Option<Certificate>, String> {
    let facts = local_facts(elab, cx);
    let spelled_reads = |ty: &Type| {
        let mut found = Vec::new();
        if let Some((_, left, right)) = integral_sides(elab, cx, ty) {
            let mut terms = Vec::new();
            max_min_reads(elab, &left, &mut terms);
            max_min_reads(elab, &right, &mut terms);
            found.extend(terms.into_iter().filter_map(|(tm, row)| {
                let (name, int, _) = MAX_MIN_READS[row];
                let args = named_args(elab, tm, name)?;
                let spell = |tm: &Rc<Term>| if int { int_term_source(elab, cx, tm) } else { nat_term_source(elab, cx, tm) };
                Some((spell(tm).ok()?, row, spell(args[0]).ok()?, spell(args[1]).ok()?))
            }));
        }
        found
    };
    let case_equations: Vec<_> = facts
        .iter()
        .filter(|(name, _)| name.starts_with(MAX_MIN_CASE) && name.ends_with("_eq"))
        .collect();
    if case_equations.len() >= SUB_SPLIT_LIMIT {
        return Ok(None);
    }
    let settled: std::collections::HashSet<String> = case_equations
        .iter()
        .filter_map(|(_, ty)| spelled_reads(ty).into_iter().next())
        .map(|(source, _, _, _)| source)
        .collect();
    let k = case_equations.len();
    for (_, ty) in facts.iter().rev() {
        let Some((_, row, a, b)) =
            spelled_reads(ty).into_iter().find(|(source, _, _, _)| !settled.contains(source))
        else {
            continue;
        };
        let lemma = MAX_MIN_READS[row].2;
        if elab.key_of(lemma).is_none() {
            continue;
        }
        let source = format!(
            "{lemma}({a}, {b}, \
             {MAX_MIN_CASE}{k}_case {MAX_MIN_CASE}{k}_eq ⊢ omega, \
             {MAX_MIN_CASE}{k}_case {MAX_MIN_CASE}{k}_eq ⊢ omega)",
        );
        return Ok(Some(Certificate {
            atoms: None,
            guards: None,
            expr: parse_generated_expr(&source)?,
            source,
            report: wrapper_report(lemma, 1),
        }));
    }
    Ok(None)
}

/// The names a Bool-guard round binds (`split_bool_guards`): its parts
/// (`__omega_guard{k}_{i}`, read in the round, never again), the guards it
/// leaves for the next round (`__omega_open{k}_{i}`), and the facts it binds
/// at their definition's unfolding (`__omega_unfold{k}_{i}`).
const GUARD_PART: &str = "__omega_guard";
const GUARD_OPEN: &str = "__omega_open";
const GUARD_UNFOLD: &str = "__omega_unfold";

/// Guard rounds one goal may sit under: a round reads every guard in scope,
/// so another is only for what it left open.
const GUARD_ROUND_LIMIT: usize = 6;

/// Branches one round's disjunctions may make, `||` proved true and `&&`
/// proved false; a disjunction past them is left open for the next round,
/// which only a branch that fails without it reaches.
const GUARD_BRANCHES: usize = 8;

/// One connective off a Bool guard (`b` in `b.IsTrue()`).
enum GuardShape<'a> {
    And(&'a Rc<Term>, &'a Rc<Term>),
    Or(&'a Rc<Term>, &'a Rc<Term>),
    Not(&'a Rc<Term>),
    /// `n.leb(m)`, read as `n <= m`, at `Nat` or (`true`) `Int`.
    Leb(bool),
    /// `n.same(m)`, read as `n = m` (`!n.same(m)` as `n ≠ m`), at `Nat` or
    /// (`true`) `Int`.
    Same(bool),
    /// A variable, a call or a field: the atom `omega::bit(b)`, unless a definition
    /// unfolds it to a connective (`unfold_guard`).
    Atom,
    /// Anything else (a stuck `match`): not read.
    Other,
}

fn guard_shape<'a>(elab: &Elaborator, b: &'a Rc<Term>) -> GuardShape<'a> {
    let args = |name| named_args(elab, b, name);
    if let Some(args) = args("bool::Bool::and") && let [x, y] = args.as_slice() {
        return GuardShape::And(x, y);
    }
    if let Some(args) = args("bool::Bool::or") && let [x, y] = args.as_slice() {
        return GuardShape::Or(x, y);
    }
    if let Some(args) = args("bool::Bool::not") && let [x] = args.as_slice() {
        return GuardShape::Not(x);
    }
    for (int, leb, same) in [(false, "nat::Nat::leb", "nat::Nat::same"), (true, "int::Int::leb", "int::Int::same")] {
        if args(leb).is_some_and(|args| args.len() == 2) {
            return GuardShape::Leb(int);
        }
        if args(same).is_some_and(|args| args.len() == 2) {
            return GuardShape::Same(int);
        }
    }
    match app_spine(b).0 {
        Term::GlobalTm { .. } | Term::Var(_) => GuardShape::Atom,
        _ if is_field_read(elab, b) => GuardShape::Atom,
        _ => GuardShape::Other,
    }
}

/// Whether a guard has a connective or a comparison under its negations.
fn guard_reads_by_structure(elab: &Elaborator, b: &Rc<Term>) -> bool {
    match guard_shape(elab, b) {
        GuardShape::Not(x) => guard_reads_by_structure(elab, x),
        GuardShape::And(..) | GuardShape::Or(..) | GuardShape::Leb(_) | GuardShape::Same(_) => true,
        GuardShape::Atom | GuardShape::Other => false,
    }
}

/// `b` in a fact `b.IsTrue()`.
fn is_true_arg<'a>(elab: &Elaborator, ty: &'a Type) -> Option<&'a Rc<Term>> {
    let Type::El { tm, .. } = ty else {
        return None;
    };
    let args = named_args(elab, tm, "bool::Bool::IsTrue")?;
    let [b] = args.as_slice() else {
        return None;
    };
    Some(b)
}

/// A guard whose head is a Bool definition, unfolded one reduct at a time to
/// the first with a connective at its head (`F.canonical(mag, bexp)` through
/// its `let`s to its `&&` chain), under any negations; `None` when it has one
/// already or never reaches one. As §11 unfolds a defined proposition.
fn unfold_guard(elab: &Elaborator, cx: &Cx, b: &Rc<Term>) -> Option<Rc<Term>> {
    match guard_shape(elab, b) {
        GuardShape::Not(x) => Some(with_arg_at(b, 0, &unfold_guard(elab, cx, x)?)),
        GuardShape::Atom if head_is_global(b) && !is_ctor_value(b) => {
            let oracle = elab.goal_oracle();
            oracle.unfold(&cx.gamma, b, Unfold::Proposition).map(Rc::new).find(|reduct| {
                matches!(
                    guard_shape(elab, reduct),
                    GuardShape::And(..) | GuardShape::Or(..) | GuardShape::Not(_) | GuardShape::Leb(_) | GuardShape::Same(_)
                )
            })
        }
        _ => None,
    }
}

/// `(b, v)` for a fact `b = True` (`v`) or `b = False` at `Bool`: what a
/// `match h: n.leb(m) { … }` arm binds, read as the guard `b.IsTrue()` or
/// `(!b).IsTrue()` (issues/decreases-measure-record-field-unspelled.md).
/// A side that is itself a literal is no guard.
fn bool_equation(elab: &Elaborator, cx: &Cx, ty: &Type) -> Option<(Rc<Term>, bool)> {
    let decoded = crate::inductive::decoded(ty);
    let Type::Id { ty, lhs, rhs, .. } = &*decoded else {
        return None;
    };
    if elab.display_type(cx, ty) != "Bool" {
        return None;
    }
    let literal = |t: &Term| match elab.spell_term_clean(cx, t).as_deref() {
        Some("True") => Some(true),
        Some("False") => Some(false),
        _ => None,
    };
    if literal(lhs).is_some() {
        return None;
    }
    Some((Rc::clone(lhs), literal(rhs)?))
}

/// A guard a round reads: `evidence` proves `term.IsTrue()` when `positive`
/// and `(!term).IsTrue()` otherwise; `negated` evidence proves
/// `¬term.IsTrue()` instead.
#[derive(Clone)]
struct GuardItem {
    evidence: String,
    term: Rc<Term>,
    positive: bool,
    negated: bool,
    /// `evidence` is the equation `term = True` (`positive`) or
    /// `term = False`, what a `match h: b { … }` arm binds.
    equation: bool,
}

struct GuardEmitter<'a> {
    elab: &'a Elaborator,
    cx: &'a Cx,
    round: usize,
    fresh: usize,
    rules: Vec<&'static str>,
}

impl GuardEmitter<'_> {
    fn name(&mut self, prefix: &str) -> String {
        let name = format!("{prefix}{}_{}", self.round, self.fresh);
        self.fresh += 1;
        name
    }

    fn rule(&mut self, rule: &'static str) -> &'static str {
        if !self.rules.contains(&rule) {
            self.rules.push(rule);
        }
        rule
    }

    fn item(evidence: &str, term: &Rc<Term>, positive: bool) -> GuardItem {
        GuardItem { evidence: evidence.to_string(), term: Rc::clone(term), positive, negated: false, equation: false }
    }

    /// The guards in `items`, the first taken apart and the rest after it,
    /// as one source term that ends in `omega` at every branch; at most
    /// `budget` branches.
    fn emit(&mut self, mut items: Vec<GuardItem>, budget: usize) -> String {
        if items.is_empty() {
            return "omega".to_string();
        }
        let item = items.remove(0);
        let h = item.evidence.clone();
        let then = |front: Vec<GuardItem>, rest: &[GuardItem]| front.into_iter().chain(rest.iter().cloned()).collect::<Vec<_>>();
        if item.equation {
            let x = self.name(GUARD_PART);
            let body = self.emit(then(vec![Self::item(&x, &item.term, item.positive)], &items), budget);
            let rule = if item.positive { "omega::guard_eq_true" } else { "omega::guard_eq_false" };
            return format!("{}({h}, {x} ⊢ {body})", self.rule(rule));
        }
        if item.negated {
            let x = self.name(GUARD_PART);
            let body = self.emit(then(vec![Self::item(&x, &item.term, false)], &items), budget);
            return format!("{}({h}, {x} ⊢ {body})", self.rule("omega::guard_negated"));
        }
        match (item.positive, guard_shape(self.elab, &item.term)) {
            (true, GuardShape::And(a, b)) => {
                let (x, y) = (self.name(GUARD_PART), self.name(GUARD_PART));
                let body = self.emit(then(vec![Self::item(&x, a, true), Self::item(&y, b, true)], &items), budget);
                format!("{}({h}, {x} {y} ⊢ {body})", self.rule("omega::guard_and"))
            }
            (false, GuardShape::Or(a, b)) => {
                let (x, y) = (self.name(GUARD_PART), self.name(GUARD_PART));
                let body = self.emit(then(vec![Self::item(&x, a, false), Self::item(&y, b, false)], &items), budget);
                format!("{}({h}, {x} {y} ⊢ {body})", self.rule("omega::guard_nor"))
            }
            (positive, GuardShape::Or(a, b) | GuardShape::And(a, b)) if budget >= 2 => {
                let (x, y) = (self.name(GUARD_PART), self.name(GUARD_PART));
                let left = self.emit(then(vec![Self::item(&x, a, positive)], &items), budget / 2);
                let right = self.emit(then(vec![Self::item(&y, b, positive)], &items), budget / 2);
                let rule = if positive { "omega::guard_or" } else { "omega::guard_nand" };
                format!("{}({h}, {x} ⊢ {left}, {y} ⊢ {right})", self.rule(rule))
            }
            (true, GuardShape::Not(a)) => {
                self.emit(then(vec![Self::item(&h, a, false)], &items), budget)
            }
            (false, GuardShape::Not(a)) => {
                let x = self.name(GUARD_PART);
                let body = self.emit(then(vec![Self::item(&x, a, true)], &items), budget);
                format!("{}({h}, {x} ⊢ {body})", self.rule("omega::guard_not_not"))
            }
            (positive, GuardShape::Leb(int)) => {
                let x = self.name(GUARD_PART);
                let body = self.emit(items, budget);
                let rule = match (int, positive) {
                    (false, true) => "omega::guard_leb",
                    (false, false) => "omega::guard_not_leb",
                    (true, true) => "omega::guard_int_leb",
                    (true, false) => "omega::guard_int_not_leb",
                };
                format!("{}({h}, {x} ⊢ {body})", self.rule(rule))
            }
            (positive, GuardShape::Same(int)) => {
                let x = self.name(GUARD_PART);
                let body = self.emit(items, budget);
                let rule = match (int, positive) {
                    (false, true) => "omega::guard_same",
                    (false, false) => "omega::guard_not_same",
                    (true, true) => "omega::guard_int_same",
                    (true, false) => "omega::guard_int_not_same",
                };
                format!("{}({h}, {x} ⊢ {body})", self.rule(rule))
            }
            (positive, GuardShape::Atom) if unfold_guard(self.elab, self.cx, &item.term).is_none() => {
                let x = self.name(GUARD_PART);
                let body = self.emit(items, budget);
                let rule = if positive { "omega::guard_bit" } else { "omega::guard_not_bit" };
                format!("{}({h}, {x} ⊢ {body})", self.rule(rule))
            }
            // A disjunction past the budget, or a definition to unfold: the
            // next round reads it, where it is a fact in scope.
            (_, GuardShape::Or(..) | GuardShape::And(..) | GuardShape::Atom) => {
                let x = self.name(GUARD_OPEN);
                let body = self.emit(items, budget);
                format!("{}({h}, {x} ⊢ {body})", self.rule("omega::guard_open"))
            }
            (_, GuardShape::Other) => self.emit(items, budget),
        }
    }
}

/// The Bool guards among the facts, read by their structure
/// (issues/omega-reads-bool-guards.md, design §17): a fact `b.IsTrue()` or
/// `¬b.IsTrue()` is taken apart by the `omega::guard_*` rules, `&&` into
/// both sides, `||` into two branches, `!` by its operand's opposite rule,
/// `n.leb(m)` into `n <= m` (`!n.leb(m)` into `m < n`), `n.same(m)` into
/// `n = m` (`!n.same(m)` into `n ≠ m`), at `Nat` and at `Int`, and any
/// other Bool into the atom
/// `bit(b)`, `1` or `0`. A guard whose head is a definition is
/// read at its unfolding, a fact bound beside the original
/// (`GuardRound::aliases`). Every guard in scope is read in one round, ending
/// in `omega` at each branch; the facts it reads are settled for the omegas
/// inside it, and what it leaves open is the next round's. A round is
/// written only when some guard has a connective or a comparison to read:
/// a context of bare Bool atoms is left as it was.
fn split_bool_guards(elab: &Elaborator, cx: &Cx) -> Result<Option<Certificate>, String> {
    if elab.key_of("omega::guard_and").is_none() {
        return Ok(None);
    }
    let (round, settled) = {
        let rounds = elab.scope.omega_settled_guards.borrow();
        let settled: std::collections::HashSet<String> = rounds.iter().flatten().cloned().collect();
        (rounds.len(), settled)
    };
    if round >= GUARD_ROUND_LIMIT {
        return Ok(None);
    }
    let mut items = Vec::new();
    let mut aliases = Vec::new();
    let mut settles = Vec::new();
    let mut readable = false;
    for fact in local_fact_entries(elab, cx) {
        if fact.name.starts_with(GUARD_PART) || fact.name.starts_with(GUARD_UNFOLD) || settled.contains(&fact.name) {
            continue;
        }
        if let Some(b) = is_true_arg(elab, &fact.ty) {
            let (evidence, b) = match unfold_guard(elab, cx, b) {
                Some(unfolded) => {
                    let Type::El { level, tm } = &fact.ty else { unreachable!() };
                    let name = format!("{GUARD_UNFOLD}{round}_{}", aliases.len());
                    aliases.push(GuardAlias {
                        name: name.clone(),
                        term: Rc::clone(&fact.term),
                        ty: Type::El { level: level.clone(), tm: with_arg_at(tm, 0, &unfolded) },
                        level: fact.level.clone(),
                    });
                    (name, unfolded)
                }
                None => (fact.name.clone(), Rc::clone(b)),
            };
            readable |= guard_reads_by_structure(elab, &b);
            items.push(GuardItem { evidence, term: b, positive: true, negated: false, equation: false });
            settles.push(fact.name);
        } else if let Some(domain) = negated_domain(elab, cx, &fact.ty)
            && let Some(b) = is_true_arg(elab, &domain)
        {
            readable |= guard_reads_by_structure(elab, b) || unfold_guard(elab, cx, b).is_some();
            items.push(GuardItem { evidence: fact.name.clone(), term: Rc::clone(b), positive: false, negated: true, equation: false });
            settles.push(fact.name);
        } else if let Some((b, value)) = bool_equation(elab, cx, &fact.ty) {
            readable |= guard_reads_by_structure(elab, &b) || unfold_guard(elab, cx, &b).is_some();
            items.push(GuardItem { evidence: fact.name.clone(), term: b, positive: value, negated: false, equation: true });
            settles.push(fact.name);
        }
    }
    // Bare atoms alone: one fact `r.IsTrue()` beside `¬r.IsTrue()` still
    // meets as `bit(r)`; a single one has nothing to meet.
    if !readable && items.len() < 2 {
        return Ok(None);
    }
    let mut emitter = GuardEmitter { elab, cx, round, fresh: 0, rules: Vec::new() };
    let source = emitter.emit(items, GUARD_BRANCHES);
    let mut report = wrapper_report("omega::guard_and", 0);
    report.used_lemmas = emitter.rules;
    Ok(Some(Certificate {
        atoms: None,
        guards: Some(GuardRound { aliases, settles }),
        expr: parse_generated_expr(&source)?,
        source,
        report,
    }))
}

/// What CutSat said about a reflection Omega's real shadow left satisfiable.
enum CutAnswer {
    /// The certificate source, its reachable and total node counts, and the
    /// search's stats.
    Certificate(String, usize, usize, crate::cutsat::Stats),
    /// An integer point satisfying every reflected fact, `≠` included.
    Model(Vec<Z>),
    /// A budget ran out.
    Unknown,
}

/// CutSat over the facts Omega reflected, when Omega's real shadow left
/// them satisfiable: each fact's bounds become `p <= 0` rows, and each `≠`
/// fact a `p ≠ 0` row, whose proofs are the reflection's own; a
/// contradiction comes back as CutSat's certificate (`cutsat_cert`).
fn reconstruct_cutsat(
    reflected: &[InitialAssumption],
    atoms_source: &str,
    atom_count: usize,
) -> Result<CutAnswer, String> {
    let mut problem = CutProblem::new();
    let mut proofs = Vec::new();
    for fact in reflected {
        let row = Affine {
            constant: 0,
            coeffs: AffineCoeffs::new(fact.coeffs.as_slice().to_vec()),
        };
        if let Some(proof) = &fact.disequality {
            let value = fact.interval.upper.ok_or("CutSat: a reflected disequality has no value")?;
            problem
                .assume_ne(row.checked_sub(&Affine::constant(value)).map_err(|f| f.to_string())?, proofs.len())
                .map_err(|failure| failure.to_string())?;
            proofs.push(proof.clone());
            continue;
        }
        if let Some(upper) = fact.interval.upper {
            let proof = fact
                .upper
                .clone()
                .ok_or("CutSat: a reflected upper bound has no proof")?;
            problem
                .assume_le(row.checked_sub(&Affine::constant(upper)).map_err(|f| f.to_string())?, proofs.len())
                .map_err(|failure| failure.to_string())?;
            proofs.push(proof);
        }
        if let Some(lower) = fact.interval.lower {
            let proof = fact
                .lower
                .as_ref()
                .ok_or("CutSat: a reflected lower bound has no proof")?;
            problem
                .assume_le(Affine::constant(lower).checked_sub(&row).map_err(|f| f.to_string())?, proofs.len())
                .map_err(|failure| failure.to_string())?;
            proofs.push(format!(
                "omega::lower_to_negated_upper({}, {atoms_source}, {}, {proof})",
                fact.row_source,
                int(lower),
            ));
        }
    }
    let (problem, outcome) = timed(
        |p| &mut p.cutsat_search_ns,
        crate::stats::Timer::OmegaCutsat,
        || problem.solve(CutLimits::default()),
    )
    .map_err(|failure| failure.to_string())?;
    let (root, reachable, stats) = match outcome {
        CutOutcome::Contradiction { root, reachable, stats } => (root, reachable, stats),
        CutOutcome::Model { values, .. } => return Ok(CutAnswer::Model(values)),
        CutOutcome::ResourceLimit { .. } => return Ok(CutAnswer::Unknown),
    };
    let render_started = std::time::Instant::now();
    let source = crate::cutsat_cert::certificate(problem.derivations(), root, &reachable, &proofs, atom_count, atoms_source)?;
    let render_ns = render_started.elapsed().as_nanos() as u64;
    crate::stats::add(crate::stats::Timer::OmegaRender, render_ns);
    add_phase(|p| &mut p.render_ns, render_ns);
    Ok(CutAnswer::Certificate(
        source,
        reachable.len(),
        problem.derivations().nodes().len(),
        stats,
    ))
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
            atoms: None,
            guards: None,
            expr: parse_generated_expr(&source)?,
            source,
            report: wrapper_report("logic::And", 0),
        });
    }
    if let Some((divisor, dividend)) = int_divides_args(elab, expected) {
        let divisor = int_term_source(elab, cx, divisor)?;
        let dividend = int_term_source(elab, cx, dividend)?;
        let remainder = format!("int::Int::mod({dividend}, {divisor})");
        let source = format!(
            "int::Int::le_antisym({}, int::OfNat(0), omega, omega)",
            remainder
        );
        return Ok(Certificate {
            atoms: None,
            guards: None,
            expr: parse_generated_expr(&source)?,
            source,
            report: wrapper_report("int::Int::le_antisym", 0),
        });
    }
    if let Some((divisor, dividend)) = nat_divides_args(elab, expected) {
        let divisor = nat_term_source(elab, cx, divisor)?;
        let dividend = nat_term_source(elab, cx, dividend)?;
        let remainder = format!("nat::Nat::mod({dividend}, {divisor})");
        let source = format!("nat::Nat::le_antisym({}, 0, omega, omega)", remainder);
        return Ok(Certificate {
            atoms: None,
            guards: None,
            expr: parse_generated_expr(&source)?,
            source,
            report: wrapper_report("nat::Nat::le_antisym", 0),
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
        let source = format!("int::Int::le_antisym({}, {}, omega, omega)", left, right);
        return Ok(Certificate {
            atoms: None,
            guards: None,
            expr: parse_generated_expr(&source)?,
            source,
            report: wrapper_report("int::Int::le_antisym", 0),
        });
    }
    if let Some((left, right)) = nat_equality_args(elab, cx, expected)
        .or_else(|| nat_equality_args(elab, cx, &decoded_expected))
    {
        let left = nat_term_source(elab, cx, left)?;
        let right = nat_term_source(elab, cx, right)?;
        let source = format!("nat::Nat::le_antisym({}, {}, omega, omega)", left, right);
        return Ok(Certificate {
            atoms: None,
            guards: None,
            expr: parse_generated_expr(&source)?,
            source,
            report: wrapper_report("nat::Nat::le_antisym", 0),
        });
    }
    if let Some((left, right)) = strict_relation_args(elab, expected) {
        let left = int_term_source(elab, cx, left)?;
        let right = int_term_source(elab, cx, right)?;
        let source = format!(
            "int::Int::lt_of_not_le({}, {}, (__omega_negated_goal: int::Int::Le({}, {})) ⊢ omega)",
            left, right, right, left,
        );
        return Ok(Certificate {
            atoms: None,
            guards: None,
            expr: parse_generated_expr(&source)?,
            source,
            report: wrapper_report("int::Int::lt_of_not_le", 0),
        });
    }
    if let Some((left, right)) = relation_args(elab, expected) {
        let left = int_term_source(elab, cx, left)?;
        let right = int_term_source(elab, cx, right)?;
        // `right < left` is definitionally `right + 1 <= left`. Writing the
        // latter lets the recursive `omega` invocation use the same affine
        // `Le` frontend as ordinary hypotheses. Spelled qualified, as the
        // `lt` case above: a module need not import `int` for its operators.
        let source = format!(
            "int::Int::le_of_not_lt({}, {}, (__omega_negated_goal: int::Int::Le(int::Int::add({}, int::OfNat(1)), {})) ⊢ omega)",
            right, left, right, left,
        );
        return Ok(Certificate {
            atoms: None,
            guards: None,
            expr: parse_generated_expr(&source)?,
            source,
            report: wrapper_report("int::Int::le_of_not_lt", 0),
        });
    }
    if let Some((left, right)) = nat_strict_relation_args(elab, expected) {
        let left = nat_term_source(elab, cx, left)?;
        let right = nat_term_source(elab, cx, right)?;
        let source = format!(
            "omega::nat_lt_of_not_not_lt({}, {}, (__omega_negated_goal: logic::Not(nat::Nat::Lt({}, {}))) ⊢ omega)",
            left, right, left, right,
        );
        return Ok(Certificate {
            atoms: None,
            guards: None,
            expr: parse_generated_expr(&source)?,
            source,
            report: wrapper_report("omega::nat_lt_of_not_not_lt", 0),
        });
    }
    if let Some((left, right)) = nat_relation_args(elab, expected) {
        let left = nat_term_source(elab, cx, left)?;
        let right = nat_term_source(elab, cx, right)?;
        let source = format!(
            "omega::nat_le_of_not_not_le({}, {}, (__omega_negated_goal: logic::Not(nat::Nat::Le({}, {}))) ⊢ omega)",
            left, right, left, right,
        );
        return Ok(Certificate {
            atoms: None,
            guards: None,
            expr: parse_generated_expr(&source)?,
            source,
            report: wrapper_report("omega::nat_le_of_not_not_le", 0),
        });
    }
    // A negated relation (`¬(a <= b)`, `a ≠ b`): assume it and refute the
    // assumption, which the recursive invocation reads as a context fact.
    if let Some(domain) = negated_domain(elab, cx, expected)
        && (reads_as_relation(elab, cx, &domain) || is_true_arg(elab, &domain).is_some())
    {
        let source = "λ __omega_assumed => omega".to_string();
        return Ok(Certificate {
            atoms: None,
            guards: None,
            expr: parse_generated_expr(&source)?,
            source,
            report: wrapper_report("λ", 0),
        });
    }
    if elab.display_type(cx, expected) != "False" {
        // A goal a definition unfolds to (`counts_advance([c], next, s)` is
        // `c(next) <= Succ(c(s))`, and `counts_advance(Nil, …)` is `True`):
        // unfold its head step by step until it is a goal this frontend
        // reads, stopping there rather than at weak head normal form, which
        // would unfold `Le` itself into its recursor. `True` closes outright.
        if let Type::El { level, tm } = expected {
            let oracle = elab.goal_oracle();
            for reduct in oracle.unfold(&cx.gamma, tm, Unfold::Proposition) {
                if matches!(&reduct, Term::TmUnit { .. }) {
                    let source = "trivial".to_string();
                    return Ok(Certificate {
                        atoms: None,
                        guards: None,
                        expr: parse_generated_expr(&source)?,
                        source,
                        report: wrapper_report("trivial", 0),
                    });
                }
                let unfolded = Type::El { level: level.clone(), tm: Rc::new(reduct) };
                let reads = elab.display_tag_of(&unfolded).is_some_and(|tag| tag.name == "And")
                    || reads_as_relation(elab, cx, &unfolded)
                    || elab.display_type(cx, &unfolded) == "False";
                if reads {
                    // The definition's arguments arrive as passed: a count
                    // `λ s => s.lines` applied, a projection of a pair. An
                    // equation is decoded first, so its sides are simplified.
                    let unfolded = crate::inductive::decoded(&unfolded);
                    let unfolded = crate::goal_combinators::simplify_goal(elab, cx, &unfolded);
                    return reconstruct(elab, cx, &unfolded, allow_disequality_split, allow_connective_split, allow_cutsat);
                }
            }
        }
        // A guard goal that does not compute to a verdict: assume its
        // negation, which a guard round reads as a fact.
        if is_true_arg(elab, expected).is_some() && elab.key_of("omega::guard_goal").is_some() {
            let source = "omega::guard_goal(__omega_negated_goal ⊢ omega)".to_string();
            return Ok(Certificate {
                atoms: None,
                guards: None,
                expr: parse_generated_expr(&source)?,
                source,
                report: wrapper_report("omega::guard_goal", 0),
            });
        }
        return Err(format!(
            "Omega currently expects `False` or an affine `Int`/`Nat` relation goal, got `{}`",
            elab.display_type(cx, expected)
        ));
    }

    let ordinary = timed(|p| &mut p.reflect_ns, crate::stats::Timer::OmegaReflect, || {
        collect_ordinary(elab, cx, None)
    })?;
    let skipped = ordinary.as_ref().map(|all| all.skipped.clone()).unwrap_or_default();
    let flags = (allow_disequality_split, allow_connective_split, allow_cutsat);
    let reflection = if let Some(all) = ordinary {
        // The facts nearest the goal first, widening; every fact only if no
        // layer refutes it (see `relevant_layers`). Only the last attempt
        // records a failure: it is the one that answers.
        for keep in relevant_layers(&all) {
            let Some(relevant) = timed(|p| &mut p.reflect_ns, crate::stats::Timer::OmegaReflect, || {
                collect_ordinary(elab, cx, Some(&keep))
            })?
            else {
                continue;
            };
            let reflection = timed(|p| &mut p.reflect_ns, crate::stats::Timer::OmegaReflect, || {
                reflect_collected(relevant)
            })?;
            if let Ok(certificate) = refute(elab, cx, flags, reflection, false) {
                return Ok(certificate);
            }
        }
        timed(|p| &mut p.reflect_ns, crate::stats::Timer::OmegaReflect, || reflect_collected(all))?
    } else {
            let mut explicit = Vec::new();
            for (name, ty) in local_facts(elab, cx) {
                // A hypothesis this renderer cannot spell is one Omega cannot
                // use, not a reason to abandon the goal: skip it and reflect
                // the rest (issues/omega-renders-member-by-base-name.md). The
                // context of a generated body holds entries with no surface
                // form at all — a `decreases` group's ih is one.
                if let Ok(Some(fact)) = reflect_assumption(elab, cx, &name, &ty) {
                    explicit.push(fact);
                }
            }
            let Some(first) = explicit.first() else {
                if let Some(certificate) = split_bool_guards(elab, cx)? {
                    return Ok(certificate);
                }
                if allow_disequality_split && let Some(certificate) = split_disequality(elab, cx, false)? {
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
                    disequality: None,
                })
                .collect();
            let atom_count = reflected_atom_count(&facts);
            (facts, atoms_source, indexed_atom_labels(atom_count), None, None)
        };
    refute(elab, cx, flags, reflection, true).map_err(|error| {
        if skipped.is_empty() { error } else {
            format!("{error}; skipped unspellable facts [{}]", skipped.join(", "))
        }
    })
}

/// Omega's search and certificate over one reflection, with the splits it
/// falls back to. `record_failure` is off for an attempt that has a retry
/// behind it.
fn refute(
    elab: &Elaborator,
    cx: &Cx,
    flags: (bool, bool, bool),
    (reflected, atoms_source, atom_labels, cut_atom_sources, atoms_literal): Reflection,
    record_failure: bool,
) -> Result<Certificate, String> {
    let mut certificate =
        refute_spelled(elab, cx, flags, (reflected, atoms_source, atom_labels, cut_atom_sources), record_failure)?;
    if certificate.source.contains(ATOMS) {
        certificate.atoms = atoms_literal;
    }
    Ok(certificate)
}

fn refute_spelled(
    elab: &Elaborator,
    cx: &Cx,
    (allow_disequality_split, allow_connective_split, allow_cutsat): (bool, bool, bool),
    (reflected, atoms_source, atom_labels, cut_atom_sources): (Vec<InitialAssumption>, String, Vec<String>, Option<Vec<String>>),
    record_failure: bool,
) -> Result<Certificate, String> {
    let atom_count = atom_labels.len();

    let mut problem = Problem::new();
    let reflected_debug = reflected
        .iter()
        .map(|fact| format!("{:?} {:?}", fact.coeffs, fact.interval))
        .collect::<Vec<_>>()
        .join(", ");
    for fact in reflected.iter().filter(|fact| fact.disequality.is_none()) {
        problem
            .assume(fact.coeffs.as_slice().to_vec(), fact.interval)
            .map_err(|failure| failure.to_string())?;
    }
    let (problem, outcome) = timed(|p| &mut p.omega_search_ns, crate::stats::Timer::OmegaSearch, || problem.solve())
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
        let cut_answer = if allow_cutsat && cut_atom_sources.is_some() {
            reconstruct_cutsat(&reflected, &atoms_source, atom_count)?
        } else {
            CutAnswer::Unknown
        };
        let cut_model = match &cut_answer {
            CutAnswer::Model(values) => Some(values.clone()),
            _ => None,
        };
        if let CutAnswer::Certificate(source, cut_reachable, cut_total, cut_stats) = cut_answer {
            let expr = parse_generated_expr(&source)
                .map_err(|error| format!("{error}\n  generated CutSat source: {source}"))?;
            let used_lemmas = reconstruction_lemmas(&source);
            return Ok(Certificate {
                atoms: None,
                guards: None,
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
        // Bool guards first, and only in the attempt that answers: a round
        // reads every guard at once, and the splits below read its parts
        // inside it.
        if record_failure && let Some(certificate) = split_bool_guards(elab, cx)? {
            return Ok(certificate);
        }
        // A CutSat model already satisfies every `=`/`≠` it was given, so
        // splitting one of those would only re-find it; other disequality
        // shapes (`¬(d ∣ e)`) still split.
        if allow_disequality_split
            && let Some(certificate) = split_disequality(elab, cx, cut_model.is_some())?
        {
            return Ok(certificate);
        }
        if allow_connective_split && let Some(certificate) = split_connective(elab, cx)? {
            return Ok(certificate);
        }
        // Last, so a goal that closes today closes as it did; and only in the
        // attempt that answers, since its branches read every fact anyway.
        if record_failure && let Some(certificate) = split_nat_subtraction(elab, cx)? {
            return Ok(certificate);
        }
        if record_failure && let Some(certificate) = split_int_to_nat(elab, cx)? {
            return Ok(certificate);
        }
        if record_failure && let Some(certificate) = split_max_min(elab, cx)? {
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
        if record_failure {
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
        }
        let model_display = cut_model
            .map(|values| {
                let point = atom_labels
                    .iter()
                    .zip(values.iter().chain(std::iter::repeat(&0)))
                    .map(|(atom, value)| format!("{atom} = {value}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("; CutSat's integer model [{point}]")
            })
            .unwrap_or_default();
        return Err(format!(
            "Omega's real shadow found no contradiction{model_display}; atoms [{}]; residual [{residual_display}]; locals [{local_types}]; reflected [{reflected_debug}]",
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
                let row_source = coeffs_source(&fact.coeffs, atom_count);
                let nonnegative = format!("int::Int::zero_le_ofNat({})", nat_lit(divisor));
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
                    "let {lower_name} = omega::lower_upper_combo({}, {}, {}, {}, {}, {}, {}, int::Int::zero_le_ofNat({}), int::Int::zero_le_ofNat({}), {}, {});",
                    int(left_scale), int(magnitude), left.row_source, right.row_source,
                    atoms_source, int(left_lower), int(right_upper), nat_lit(left_scale), nat_lit(magnitude),
                    left.lower.as_ref().ok_or("Omega two-sided combination lost its left lower proof")?,
                    right.upper.as_ref().ok_or("Omega two-sided combination lost its right upper proof")?,
                ));
                let upper_name = format!("__omega_generated_{id}_upper");
                bindings.push(format!(
                    "let {upper_name} = omega::lower_upper_upper_combo({}, {}, {}, {}, {}, {}, {}, int::Int::zero_le_ofNat({}), int::Int::zero_le_ofNat({}), {}, {});",
                    int(left_scale), int(magnitude), left.row_source, right.row_source,
                    atoms_source, int(right_lower), int(left_upper), nat_lit(left_scale), nat_lit(magnitude),
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
                    "let {lower_name} = omega::upper_lower_lower_combo({}, {}, {}, {}, {}, {}, {}, int::Int::zero_le_ofNat({}), int::Int::zero_le_ofNat({}), {}, {});",
                    int(magnitude), int(right_scale), left.row_source, right.row_source,
                    atoms_source, int(right_lower), int(left_upper), nat_lit(magnitude), nat_lit(right_scale),
                    left.upper.as_ref().ok_or("Omega two-sided combination lost its left upper proof")?,
                    right.lower.as_ref().ok_or("Omega two-sided combination lost its right lower proof")?,
                ));
                let upper_name = format!("__omega_generated_{id}_upper");
                bindings.push(format!(
                    "let {upper_name} = omega::upper_lower_combo({}, {}, {}, {}, {}, {}, {}, int::Int::zero_le_ofNat({}), int::Int::zero_le_ofNat({}), {}, {});",
                    int(magnitude), int(right_scale), left.row_source, right.row_source,
                    atoms_source, int(left_lower), int(right_upper), nat_lit(magnitude), nat_lit(right_scale),
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
                    "omega::lower_upper_combo({}, {}, {}, {}, {}, {}, {}, int::Int::zero_le_ofNat({}), int::Int::zero_le_ofNat({}), {}, {})",
                    int(left_scale),
                    int(magnitude),
                    left.row_source,
                    right.row_source,
                    atoms_source,
                    int(l),
                    int(u),
                    nat_lit(left_scale),
                    nat_lit(magnitude),
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
                    "omega::lower_upper_combo({}, {}, {}, {}, {}, {}, {}, int::Int::zero_le_ofNat({}), int::Int::zero_le_ofNat({}), {}, {})",
                    int(right_scale),
                    int(magnitude),
                    right.row_source,
                    left.row_source,
                    atoms_source,
                    int(l),
                    int(u),
                    nat_lit(right_scale),
                    nat_lit(magnitude),
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
                    "omega::upper_lower_combo({}, {}, {}, {}, {}, {}, {}, int::Int::zero_le_ofNat({}), int::Int::zero_le_ofNat({}), {}, {})",
                    int(magnitude),
                    int(right_scale),
                    left.row_source,
                    right.row_source,
                    atoms_source,
                    int(l),
                    int(u),
                    nat_lit(magnitude),
                    nat_lit(right_scale),
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
                    "let {lower_name} = omega::lower_neg_combo({}, {}, {}, {}, {}, {}, {}, int::Int::zero_le_ofNat({}), int::Int::zero_le_ofNat({}), {}, {});",
                    int(a), int(b), left.row_source, right.row_source, atoms_source,
                    int(left.interval.upper.ok_or("Omega negative combination lost its left upper value")?),
                    int(right.interval.upper.ok_or("Omega negative combination lost its right upper value")?),
                    nat_lit(a), nat_lit(b),
                    left.upper.as_ref().ok_or("Omega negative combination lost its left upper proof")?,
                    right.upper.as_ref().ok_or("Omega negative combination lost its right upper proof")?,
                ));
                let upper_name = format!("__omega_generated_{id}_upper");
                bindings.push(format!(
                    "let {upper_name} = omega::upper_neg_combo({}, {}, {}, {}, {}, {}, {}, int::Int::zero_le_ofNat({}), int::Int::zero_le_ofNat({}), {}, {});",
                    int(a), int(b), left.row_source, right.row_source, atoms_source,
                    int(left.interval.lower.ok_or("Omega negative combination lost its left lower value")?),
                    int(right.interval.lower.ok_or("Omega negative combination lost its right lower value")?),
                    nat_lit(a), nat_lit(b),
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
                    "let {name} = omega::lower_neg_combo({}, {}, {}, {}, {}, {}, {}, int::Int::zero_le_ofNat({}), int::Int::zero_le_ofNat({}), {}, {});",
                    int(a), int(b), left.row_source, right.row_source, atoms_source,
                    int(left.interval.upper.ok_or("Omega negative combination lost its left upper value")?),
                    int(right.interval.upper.ok_or("Omega negative combination lost its right upper value")?),
                    nat_lit(a), nat_lit(b),
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
                    "let {name} = omega::upper_neg_combo({}, {}, {}, {}, {}, {}, {}, int::Int::zero_le_ofNat({}), int::Int::zero_le_ofNat({}), {}, {});",
                    int(a), int(b), left.row_source, right.row_source, atoms_source,
                    int(left.interval.lower.ok_or("Omega negative combination lost its left lower value")?),
                    int(right.interval.lower.ok_or("Omega negative combination lost its right lower value")?),
                    nat_lit(a), nat_lit(b),
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
            // Two bounded rows can combine into a bounded interval that
            // is not exact. Reconstruct each endpoint independently.
            Derivation::Combo { left, left_scale, right, right_scale }
                if left_scale > 0 && right_scale > 0
                    && fact.interval.lower.is_some() && fact.interval.upper.is_some() =>
            {
                let left = parent(&proofs, left)?;
                let right = parent(&proofs, right)?;
                let row_source = format!("omega::combo({}, {}, {}, {})",
                    int(left_scale), left.row_source, int(right_scale), right.row_source);
                let mut endpoints = Vec::new();
                for lower in [true, false] {
                    let (lv, rv, lp, rp, lemma) = if lower {
                        (left.interval.lower, right.interval.lower, &left.lower, &right.lower, "lower_combo")
                    } else {
                        (left.interval.upper, right.interval.upper, &left.upper, &right.upper, "upper_combo")
                    };
                    let name = format!("__omega_generated_{id}_{}", if lower { "lower" } else { "upper" });
                    bindings.push(format!(
                        "let {name} = omega::{lemma}({}, {}, {}, {}, {}, {}, {}, int::Int::zero_le_ofNat({}), int::Int::zero_le_ofNat({}), {}, {});",
                        int(left_scale), int(right_scale), left.row_source, right.row_source, atoms_source,
                        int(lv.ok_or("Omega bounded combination lost its left endpoint")?),
                        int(rv.ok_or("Omega bounded combination lost its right endpoint")?),
                        nat_lit(left_scale), nat_lit(right_scale),
                        lp.as_ref().ok_or("Omega bounded combination lost its left proof")?,
                        rp.as_ref().ok_or("Omega bounded combination lost its right proof")?,
                    ));
                    endpoints.push(name);
                }
                BoundProof {
                    row_source,
                    interval: fact.interval,
                    lower: Some(endpoints[0].clone()),
                    upper: Some(endpoints[1].clone()),
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
                    "omega::lower_combo({}, {}, {}, {}, {}, {}, {}, int::Int::zero_le_ofNat({}), int::Int::zero_le_ofNat({}), {}, {})",
                    int(left_scale),
                    int(right_scale),
                    left.row_source,
                    right.row_source,
                    atoms_source,
                    int(l),
                    int(r),
                    nat_lit(left_scale),
                    nat_lit(right_scale),
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
                    "omega::upper_combo({}, {}, {}, {}, {}, {}, {}, int::Int::zero_le_ofNat({}), int::Int::zero_le_ofNat({}), {}, {})",
                    int(left_scale),
                    int(right_scale),
                    left.row_source,
                    right.row_source,
                    atoms_source,
                    int(l),
                    int(r),
                    nat_lit(left_scale),
                    nat_lit(right_scale),
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
            atoms: None,
            guards: None,
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
        "int::Int::le_trans({}, omega::dot({}, {}), {}, {}, {})",
        int(lower),
        row,
        atoms_source,
        int(upper),
        lower_proof,
        upper_proof,
    );
    let result = format!(
        "int::Int::not_lt_of_ge({}, {}, {}) ({})",
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
        atoms: None,
        guards: None,
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
    fn a_constant_past_a_numeral_token_is_spelled_as_its_numeral_and_read_back() {
        let word = Z::from(u64::MAX);
        assert_eq!(nat_lit(word), "18446744073709551615");
        assert_eq!(nat_lit(word + 1), "18446744073709551616");
        for value in [0, 7, word, word + 1, word * 3 + 5, Z::MAX - 1, Z::MAX / 3] {
            let compact: String = nat_lit(value).chars().filter(|c| !c.is_whitespace()).collect();
            assert_eq!(nat_lit_value(&compact), Some(value), "{value}");
            assert_eq!(integer_source(&int_ctor(value)), Some(value), "{value}");
            assert_eq!(integer_source(&int_ctor(-value - 1)), Some(-value - 1), "{value}");
            assert_eq!(
                coefficient_source(&format!("list::Cons({}, list::Cons({}, list::Nil))", int_ctor(value), int_ctor(-value - 1))),
                Some(vec![value, -value - 1]),
                "{value}"
            );
        }
        // A spelling that is not a numeral is not a constant.
        assert_eq!(nat_lit_value("nat::Nat::add(nat::Nat::mul(1,256),0)"), None);
        assert_eq!(nat_lit_value("-1"), None);
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
    fn pugh_certificate_writes_each_reachable_node_once() {
        let mut problem = CutProblem::new();
        let mut proofs = Vec::new();
        for (coefficients, lower, upper) in [
            (vec![11, 13], 27, 45),
            (vec![7, -9], -10, 4),
            (vec![1, 0], -16, 16),
            (vec![0, 1], -16, 16),
        ] {
            let row = Affine {
                constant: 0,
                coeffs: AffineCoeffs::new(coefficients),
            };
            problem
                .assume_le(Affine::constant(lower).checked_sub(&row).unwrap(), proofs.len())
                .unwrap();
            proofs.push(format!("__pugh_{}", proofs.len()));
            problem
                .assume_le(row.checked_sub(&Affine::constant(upper)).unwrap(), proofs.len())
                .unwrap();
            proofs.push(format!("__pugh_{}", proofs.len()));
        }
        let (problem, outcome) = problem.solve(CutLimits::default()).unwrap();
        let CutOutcome::Contradiction { root, reachable, .. } = outcome else {
            panic!("Pugh system did not contradict")
        };
        let source = crate::cutsat_cert::certificate(problem.derivations(), root, &reachable, &proofs, 2, ATOMS)
            .unwrap();
        // One `have` per reachable node, and no nested `omega` to re-derive one.
        assert_eq!(source.matches("have __cut_n").count(), reachable.len());
        assert!(!source.contains("omega)") && !source.contains("⊢ omega"));
        assert!(source.contains("omega::cut_cooper_"));
    }
}
