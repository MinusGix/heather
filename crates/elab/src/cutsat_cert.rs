//! CutSat's certificate: one `have` per reachable derivation node.
//!
//! Every node concludes a closed row fact over the certificate's atom list
//! ([`ATOMS`]): `dot(row, atoms) <= bound`, `cut_dvd(d, dot(row, atoms) + c)`,
//! `dot(row, atoms) + c ≠ 0`, or `False`. Its `have` states that fact with
//! literal rows and constants and proves it by one `omega::cut_*` lemma (or
//! one of Omega's row lemmas) applied to its premises' names, with the closed
//! row arithmetic left to the kernel's evaluation (`refl`, `trivial`).
//!
//! A node is written once, in the scope its premises are visible from
//! ([`DerivationDag::scope_of`]); a split writes each case as a λ over the
//! case's hypotheses whose body is that scope's block. The kernel therefore
//! checks every shared derivation once, however many cases use it.

use std::collections::HashMap;

use crate::arithmetic::{Affine, Coeffs, Z};
use crate::cutsat::{CooperCase, Derivation, DerivationDag, DerivedConstraint, ROOT_SCOPE, SplitCase, cooper_period, extended_gcd, gcd, without_variable};
use crate::omega_cert::{ATOMS, coeffs_source, int, literal_lt_proof, nat_lit};

/// The certificate of `root`'s contradiction. `assumptions[i]` proves the
/// caller's fact `i` in any spelling convertible to its node's conclusion;
/// `atoms_source` spells the atom list the rows are over.
pub(crate) fn certificate(
    dag: &DerivationDag,
    root: usize,
    reachable: &[usize],
    assumptions: &[String],
    atom_count: usize,
    atoms_source: &str,
) -> Result<String, String> {
    let width = reachable
        .iter()
        .filter_map(|id| conclusion_affine(dag.conclusion(*id)?))
        .map(|affine| affine.coeffs.as_slice().len())
        .max()
        .unwrap_or(0)
        .max(atom_count);
    let mut by_scope: HashMap<usize, Vec<usize>> = HashMap::new();
    for &id in reachable {
        by_scope.entry(dag.scope_of(id)).or_default().push(id);
    }
    for ids in by_scope.values_mut() {
        ids.sort_unstable();
    }
    let writer = Writer {
        dag,
        assumptions,
        width,
        by_scope,
    };
    let source = writer.block(ROOT_SCOPE, root)?;
    Ok(if atoms_source == ATOMS { source } else { source.replace(ATOMS, atoms_source) })
}

fn conclusion_affine(conclusion: &DerivedConstraint) -> Option<&Affine> {
    match conclusion {
        DerivedConstraint::Le(affine) | DerivedConstraint::Ne(affine) => Some(affine),
        DerivedConstraint::Dvd { affine, .. } => Some(affine),
        DerivedConstraint::False => None,
    }
}

fn name(id: usize) -> String {
    format!("__cut_n{id}")
}

fn binder(id: usize) -> String {
    format!("__cut_h{id}")
}

fn nat(value: Z) -> Result<String, String> {
    if value < 0 {
        return Err(format!("CutSat needed a natural number, got {value}"));
    }
    Ok(nat_lit(value))
}

fn zero_le(value: Z) -> Result<String, String> {
    Ok(format!("int::Int::zero_le_ofNat({})", nat(value)?))
}

/// `Exists(witness, refl)` for `value = divisor * witness`, all closed.
fn closed_multiple(divisor: Z, value: Z) -> Result<String, String> {
    if divisor == 0 || value % divisor != 0 {
        return Err(format!("CutSat expected {divisor} to divide {value}"));
    }
    Ok(format!("Exists(witness := {}, proof := refl)", int(value / divisor)))
}

struct Writer<'a> {
    dag: &'a DerivationDag,
    assumptions: &'a [String],
    width: usize,
    by_scope: HashMap<usize, Vec<usize>>,
}

/// A row fact split at its pivot variable.
struct Pivot {
    row: Coeffs,
    rest: Coeffs,
    coefficient: Z,
    constant: Z,
}

impl Writer<'_> {
    fn row(&self, coeffs: &Coeffs) -> String {
        coeffs_source(coeffs, self.width)
    }

    fn zeros(&self) -> String {
        self.row(&Coeffs::default())
    }

    fn le(&self, id: usize) -> Result<&Affine, String> {
        match self.dag.conclusion(id) {
            Some(DerivedConstraint::Le(affine)) => Ok(affine),
            other => Err(format!("CutSat node {id} should conclude an inequality, not {other:?}")),
        }
    }

    fn dvd(&self, id: usize) -> Result<(Z, &Affine), String> {
        match self.dag.conclusion(id) {
            Some(DerivedConstraint::Dvd { divisor, affine }) => Ok((*divisor, affine)),
            other => Err(format!("CutSat node {id} should conclude a divisibility, not {other:?}")),
        }
    }

    fn ne(&self, id: usize) -> Result<&Affine, String> {
        match self.dag.conclusion(id) {
            Some(DerivedConstraint::Ne(affine)) => Ok(affine),
            other => Err(format!("CutSat node {id} should conclude a disequality, not {other:?}")),
        }
    }

    fn pivot(&self, affine: &Affine, variable: usize) -> Pivot {
        Pivot {
            row: affine.coeffs.clone(),
            rest: without_variable(affine, variable).coeffs,
            coefficient: affine.coeffs.get(variable),
            constant: affine.constant,
        }
    }

    fn ty(&self, id: usize) -> Result<String, String> {
        Ok(match self.dag.conclusion(id) {
            Some(DerivedConstraint::Le(affine)) => format!(
                "(omega::dot({}, {ATOMS}) <= {})",
                self.row(&affine.coeffs),
                int(-affine.constant)
            ),
            Some(DerivedConstraint::Dvd { divisor, affine }) => format!(
                "omega::cut_dvd({}, int::Int::add(omega::dot({}, {ATOMS}), {}))",
                int(*divisor),
                self.row(&affine.coeffs),
                int(affine.constant)
            ),
            Some(DerivedConstraint::Ne(affine)) => format!(
                "(int::Int::add(omega::dot({}, {ATOMS}), {}) ≠ int::OfNat(0))",
                self.row(&affine.coeffs),
                int(affine.constant)
            ),
            Some(DerivedConstraint::False) => "logic::False".into(),
            None => return Err(format!("CutSat references absent node {id}")),
        })
    }

    /// The `have`s of `scope`, ending in `last`'s name.
    fn block(&self, scope: usize, last: usize) -> Result<String, String> {
        let mut out = String::from("{ ");
        for &id in self.by_scope.get(&scope).map(Vec::as_slice).unwrap_or(&[]) {
            out.push_str(&format!("have {}: {} = {}; ", name(id), self.ty(id)?, self.proof(id)?));
        }
        out.push_str(&name(last));
        out.push_str(" }");
        Ok(out)
    }

    fn proof(&self, id: usize) -> Result<String, String> {
        let node = &self.dag.nodes()[id];
        match node {
            Derivation::Assumption {
                index,
                equality_side: None,
            }
            | Derivation::DiseqAssumption { index }
            | Derivation::DvdAssumption { index } => self
                .assumptions
                .get(*index)
                .cloned()
                .ok_or_else(|| format!("CutSat assumption {index} has no proof")),
            Derivation::Assumption { .. } => {
                Err("CutSat's certificate takes each side of an equation as its own assumption".into())
            }
            Derivation::Hypothesis { .. } => Ok(binder(id)),
            Derivation::Tighten { parent } => {
                let raw = self.le(*parent)?;
                let reduced = self.le(id)?;
                let g = raw.coeffs.coefficient_gcd().map_err(|e| e.to_string())?;
                let (upper, rounded) = (-raw.constant, -reduced.constant);
                Ok(format!(
                    "omega::divide_upper({}, {}, {ATOMS}, {}, {}, {}, refl, {}, {}, {})",
                    self.row(&raw.coeffs),
                    self.row(&reduced.coeffs),
                    int(g),
                    int(upper),
                    int(rounded),
                    zero_le(g)?,
                    literal_lt_proof(upper, checked(g.checked_mul(rounded + 1))?)?,
                    name(*parent),
                ))
            }
            Derivation::Resolve {
                lower,
                upper,
                variable,
            } => {
                let (l, u) = (self.le(*lower)?, self.le(*upper)?);
                let out = self.le(id)?;
                let a = -l.coeffs.get(*variable);
                let b = u.coeffs.get(*variable);
                let bound = -out.constant;
                Ok(format!(
                    "omega::cut_resolve({}, {}, int::OfNat(1), {}, {}, {}, {}, {ATOMS}, {}, {}, {}, {}, {}, refl, {}, {}, {})",
                    int(b),
                    int(a),
                    int(bound),
                    self.row(&l.coeffs),
                    self.row(&u.coeffs),
                    self.row(&out.coeffs),
                    int(-l.constant),
                    int(-u.constant),
                    zero_le(b)?,
                    zero_le(a)?,
                    zero_le(1)?,
                    literal_lt_proof(bound, bound + 1)?,
                    name(*lower),
                    name(*upper),
                ))
            }
            Derivation::SolveDiv {
                left,
                right,
                variable,
                main,
            } => {
                let (m, old) = self.dvd(*left)?;
                let (n, new) = self.dvd(*right)?;
                let (divisor, out) = self.dvd(id)?;
                let (a, b) = (old.coeffs.get(*variable), new.coeffs.get(*variable));
                let (g, u, v) = extended_gcd(a * n, b * m).map_err(|e| e.to_string())?;
                let (s1, s2, m1, m2) = if *main {
                    (u * n, v * m, u, v)
                } else {
                    (b, -a, b * m / g, -a * n / g)
                };
                if s1 * m != divisor * m1 || s2 * n != divisor * m2 {
                    return Err(format!("CutSat solve-div node {id} does not combine its parents"));
                }
                Ok(format!(
                    "omega::cut_dvd_combo({}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {ATOMS}, refl, refl, refl, refl, {}, {})",
                    int(m),
                    int(n),
                    int(divisor),
                    int(s1),
                    int(s2),
                    int(m1),
                    int(m2),
                    int(old.constant),
                    int(new.constant),
                    int(out.constant),
                    self.row(&old.coeffs),
                    self.row(&new.coeffs),
                    self.row(&out.coeffs),
                    name(*left),
                    name(*right),
                ))
            }
            Derivation::DvdDrop {
                divisibility,
                variable,
            } => {
                let (d, old) = self.dvd(*divisibility)?;
                let (g, out) = self.dvd(id)?;
                let a = old.coeffs.get(*variable);
                if gcd(a, d) != g {
                    return Err(format!("CutSat drop node {id} does not divide its parent"));
                }
                Ok(format!(
                    "omega::cut_dvd_drop({}, {}, {}, {}, {}, {}, {}, {}, {ATOMS}, refl, refl, {})",
                    nat(*variable as Z)?,
                    int(d),
                    int(g),
                    int(d / g),
                    int(a / g),
                    int(old.constant),
                    self.row(&old.coeffs),
                    self.row(&out.coeffs),
                    name(*divisibility),
                ))
            }
            Derivation::ConstantLe { constraint } => {
                let affine = self.le(*constraint)?;
                let bound = -affine.constant;
                Ok(format!(
                    "omega::cut_constant_upper({}, {ATOMS}, {}, refl, {}, {})",
                    self.row(&affine.coeffs),
                    int(bound),
                    literal_lt_proof(bound, 0)?,
                    name(*constraint),
                ))
            }
            Derivation::ConstantDvd { constraint } => {
                let (d, affine) = self.dvd(*constraint)?;
                let c = affine.constant;
                let q = c.div_euclid(d);
                Ok(format!(
                    "omega::cut_constant_dvd({}, {}, {}, {}, {ATOMS}, refl, {}, {}, {})",
                    nat(d - 1)?,
                    int(c),
                    int(q),
                    self.row(&affine.coeffs),
                    literal_lt_proof(d * q, c)?,
                    literal_lt_proof(c, d * (q + 1))?,
                    name(*constraint),
                ))
            }
            Derivation::ConstantDiseq { constraint } => {
                let affine = self.ne(*constraint)?;
                Ok(format!(
                    "omega::cut_constant_diseq({}, {ATOMS}, refl, {})",
                    self.row(&affine.coeffs),
                    name(*constraint),
                ))
            }
            Derivation::DiseqSplit { diseq, below, above } => {
                let affine = self.ne(*diseq)?;
                let c = affine.constant;
                let negated = Coeffs::new(affine.coeffs.as_slice().iter().map(|x| -x).collect());
                Ok(format!(
                    "omega::cut_diseq({}, {}, {ATOMS}, {}, {}, {}, refl, refl, refl, {}, {}, {})",
                    self.row(&affine.coeffs),
                    self.row(&negated),
                    int(c),
                    int(-c - 1),
                    int(c - 1),
                    name(*diseq),
                    self.split_case(below)?,
                    self.split_case(above)?,
                ))
            }
            Derivation::Cooper {
                lower,
                upper,
                divisibility,
                variable,
                left,
                period,
                cases,
            } => self.cooper(*lower, *upper, *divisibility, *variable, *left, *period, cases),
        }
    }

    fn split_case(&self, case: &SplitCase) -> Result<String, String> {
        Ok(format!(
            "λ {} => {}",
            binder(case.hypothesis),
            self.block(case.scope, case.contradiction)?
        ))
    }

    #[allow(clippy::too_many_arguments)]
    fn cooper(
        &self,
        lower: usize,
        upper: usize,
        divisibility: Option<usize>,
        variable: usize,
        left: bool,
        period: Z,
        cases: &[CooperCase],
    ) -> Result<String, String> {
        let lower_fact = self.pivot(self.le(lower)?, variable);
        let upper_fact = self.pivot(self.le(upper)?, variable);
        let (d, carried_fact) = match divisibility {
            Some(id) => {
                let (d, affine) = self.dvd(id)?;
                (d, self.pivot(affine, variable))
            }
            None => (
                1,
                Pivot {
                    row: Coeffs::default(),
                    rest: Coeffs::default(),
                    coefficient: 0,
                    constant: 0,
                },
            ),
        };
        let a = -lower_fact.coefficient;
        let b = upper_fact.coefficient;
        let c = carried_fact.coefficient;
        if a <= 0 || b <= 0 {
            return Err("CutSat Cooper parents are not opposing bounds".into());
        }
        let selected = if left { a } else { b };
        if cooper_period(selected, d, c).map_err(|e| e.to_string())? != period || cases.len() as Z != period {
            return Err("CutSat Cooper split has the wrong number of cases".into());
        }
        let (lower_bound, upper_bound) = (-lower_fact.constant, -upper_fact.constant);
        let cut_row = Coeffs::combo(b, &lower_fact.rest, a, &upper_fact.rest).map_err(|e| e.to_string())?;
        let cut_bound = b * lower_bound + a * upper_bound;
        let (selected_constant, carried_divisor, carried_out_row, carried_out_constant, period_c) = if left {
            (
                -lower_bound,
                a * d,
                Coeffs::combo(c, &lower_fact.rest, a, &carried_fact.rest).map_err(|e| e.to_string())?,
                c * -lower_bound + a * carried_fact.constant,
                closed_multiple(a * d, c * period)?,
            )
        } else {
            (
                -upper_bound,
                b * d,
                Coeffs::combo(-c, &upper_fact.rest, b, &carried_fact.rest).map_err(|e| e.to_string())?,
                -c * -upper_bound + b * carried_fact.constant,
                closed_multiple(b * d, -c * period)?,
            )
        };
        let carried_proof = match divisibility {
            Some(id) => name(id),
            None => format!("omega::cut_dvd_one(int::Int::add(omega::dot({}, {ATOMS}), int::OfNat(0)))", self.zeros()),
        };
        let mut chain = "omega::below_zero".to_string();
        for (k, case) in cases.iter().enumerate() {
            let carried_binder = match case.carried {
                Some(id) => binder(id),
                None => format!("__cut_unused{}", case.cut),
            };
            chain = format!(
                "omega::below_succ({}, {chain}, λ {} {} {carried_binder} => {})",
                nat(k as Z)?,
                binder(case.cut),
                binder(case.selected),
                self.block(case.scope, case.contradiction)?,
            );
        }
        Ok(format!(
            "omega::cut_cooper_{}({}, {ATOMS}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, refl, refl, refl, refl, refl, refl, refl, refl, refl, {}, {}, {}, {}, {}, {chain})",
            if left { "left" } else { "right" },
            nat(variable as Z)?,
            self.row(&lower_fact.row),
            self.row(&upper_fact.row),
            self.row(&carried_fact.row),
            self.row(&lower_fact.rest),
            self.row(&upper_fact.rest),
            self.row(&carried_fact.rest),
            self.row(&cut_row),
            self.row(&carried_out_row),
            nat(a - 1)?,
            nat(b - 1)?,
            nat(period - 1)?,
            int(d),
            int(c),
            int(lower_bound),
            int(upper_bound),
            int(carried_fact.constant),
            int(cut_bound),
            int(selected_constant),
            int(carried_divisor),
            int(carried_out_constant),
            closed_multiple(selected, period)?,
            period_c,
            name(lower),
            name(upper),
            carried_proof,
        ))
    }
}

fn checked(value: Option<Z>) -> Result<Z, String> {
    value.ok_or_else(|| "CutSat certificate arithmetic overflowed".to_string())
}
