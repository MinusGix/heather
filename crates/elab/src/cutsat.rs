//! A search-only CutSat kernel over shared affine arithmetic.
//!
//! This deliberately stops short of proof-term reconstruction.  It records a
//! typed derivation DAG so the search rules can be audited and later connected
//! to certificate generation without coupling reflection to either solver.

use crate::arithmetic::{Affine, Failure, Relation, Z, abs, add, mul, neg};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Derivation {
    Assumption {
        index: usize,
        equality_side: Option<bool>,
    },
    RealProjection {
        lower: usize,
        upper: usize,
    },
    DivisibilityProjection {
        divisibility: usize,
    },
    DivisibilityConflict {
        left: usize,
        right: usize,
    },
    CombinedCongruenceBoundConflict {
        lower: usize,
        upper: usize,
        divisibility: Vec<usize>,
    },
    CongruenceExclusion {
        constraints: Vec<usize>,
        variable: usize,
        value: Z,
        below: bool,
    },
    CooperInequality {
        lower: usize,
        upper: usize,
        divisibility: Option<usize>,
        case: Z,
    },
    CooperDivisibility {
        lower: usize,
        upper: usize,
        divisibility: Option<usize>,
        case: Z,
    },
    ConstantInequality {
        constraint: usize,
    },
    ConstantDivisibility {
        constraint: usize,
    },
    CooperExhausted {
        cases: Vec<usize>,
    },
    ExclusionExhausted {
        below: usize,
        above: usize,
    },
}

impl Derivation {
    fn parents(&self) -> Vec<usize> {
        match self {
            Self::Assumption { .. } => Vec::new(),
            Self::RealProjection { lower, upper } => vec![*lower, *upper],
            Self::DivisibilityProjection { divisibility } => vec![*divisibility],
            Self::DivisibilityConflict { left, right } => vec![*left, *right],
            Self::CombinedCongruenceBoundConflict {
                lower,
                upper,
                divisibility,
            } => {
                let mut out = vec![*lower, *upper];
                out.extend(divisibility.iter().copied());
                out
            }
            Self::CongruenceExclusion { constraints, .. } => constraints.clone(),
            Self::CooperInequality {
                lower,
                upper,
                divisibility,
                ..
            }
            | Self::CooperDivisibility {
                lower,
                upper,
                divisibility,
                ..
            } => {
                let mut out = vec![*lower, *upper];
                if let Some(id) = divisibility {
                    out.push(*id);
                }
                out
            }
            Self::ConstantInequality { constraint } | Self::ConstantDivisibility { constraint } => {
                vec![*constraint]
            }
            Self::CooperExhausted { cases } => cases.clone(),
            Self::ExclusionExhausted { below, above } => vec![*below, *above],
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct DerivationDag {
    nodes: Vec<Derivation>,
}

impl DerivationDag {
    pub fn nodes(&self) -> &[Derivation] {
        &self.nodes
    }

    fn push(&mut self, node: Derivation) -> usize {
        let id = self.nodes.len();
        self.nodes.push(node);
        id
    }

    fn reachable(&self, root: usize) -> Vec<usize> {
        let mut seen = vec![false; self.nodes.len()];
        let mut stack = vec![root];
        while let Some(id) = stack.pop() {
            if seen[id] {
                continue;
            }
            seen[id] = true;
            stack.extend(self.nodes[id].parents());
        }
        seen.into_iter()
            .enumerate()
            .filter_map(|(i, yes)| yes.then_some(i))
            .collect()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Limits {
    pub max_steps: usize,
    pub max_cases: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            max_steps: 100_000,
            max_cases: 10_000,
        }
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Stats {
    pub assignments: usize,
    pub projections: usize,
    pub splits: usize,
    pub cases: usize,
    pub derived_constraints: usize,
    pub steps: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResourceReason {
    StepLimit,
    CaseLimit,
    MultipleDivisibilityConstraints { variable: usize, count: usize },
    RepeatedConflict,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResidualConstraint {
    Le(Affine),
    Dvd { divisor: Z, affine: Affine },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    Contradiction {
        root: usize,
        reachable: Vec<usize>,
        stats: Stats,
    },
    Model {
        values: Vec<Z>,
        stats: Stats,
    },
    ResourceLimit {
        partial_model: Vec<Z>,
        residual: Vec<ResidualConstraint>,
        reason: ResourceReason,
        stats: Stats,
    },
}

#[derive(Debug, Clone)]
struct LeConstraint {
    p: Affine,
    derivation: usize,
}

#[derive(Debug, Clone)]
struct DvdConstraint {
    divisor: Z,
    p: Affine,
    derivation: usize,
}

#[derive(Debug, Clone, Default)]
struct Constraints {
    le: Vec<LeConstraint>,
    dvd: Vec<DvdConstraint>,
}

impl Constraints {
    fn insert_le(&mut self, mut p: Affine, derivation: usize) -> Result<bool, Failure> {
        let coefficient_gcd = p.coeffs.coefficient_gcd()?;
        if coefficient_gcd > 1 {
            p.constant = ceil_div(p.constant, coefficient_gcd)?;
            p.coeffs = p.coeffs.exact_div(coefficient_gcd)?;
        }
        if self.le.iter().any(|old| old.p == p) {
            return Ok(false);
        }
        self.le.push(LeConstraint { p, derivation });
        Ok(true)
    }

    fn insert_dvd(&mut self, divisor: Z, p: Affine, derivation: usize) -> Result<bool, Failure> {
        let divisor = abs(divisor)?;
        if divisor == 0 {
            return Err(Failure::InvalidConstraint {
                detail: "zero divisibility modulus".into(),
            });
        }
        if divisor == 1 {
            return Ok(false);
        }
        if self
            .dvd
            .iter()
            .any(|old| old.divisor == divisor && old.p == p)
        {
            return Ok(false);
        }
        self.dvd.push(DvdConstraint {
            divisor,
            p,
            derivation,
        });
        Ok(true)
    }

    fn residual(&self) -> Vec<ResidualConstraint> {
        self.le
            .iter()
            .map(|c| ResidualConstraint::Le(c.p.clone()))
            .chain(self.dvd.iter().map(|c| ResidualConstraint::Dvd {
                divisor: c.divisor,
                affine: c.p.clone(),
            }))
            .collect()
    }
}

#[derive(Debug, Clone, Default)]
pub struct Problem {
    constraints: Constraints,
    derivations: DerivationDag,
    assumptions: usize,
}

impl Problem {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn derivations(&self) -> &DerivationDag {
        &self.derivations
    }

    pub fn assume(&mut self, lhs: Affine, relation: Relation, rhs: Affine) -> Result<(), Failure> {
        if !matches!(relation, Relation::Eq | Relation::Le) {
            return Err(Failure::InvalidConstraint {
                detail: "CutSat's first slice accepts only equality and <= relations".into(),
            });
        }
        let index = self.assumptions;
        self.assumptions += 1;
        let p = lhs.checked_sub(&rhs)?;
        match relation {
            Relation::Le => {
                let d = self.derivations.push(Derivation::Assumption {
                    index,
                    equality_side: None,
                });
                self.constraints.insert_le(p, d)?;
            }
            Relation::Eq => {
                let forward = self.derivations.push(Derivation::Assumption {
                    index,
                    equality_side: Some(true),
                });
                self.constraints.insert_le(p.clone(), forward)?;
                let backward = self.derivations.push(Derivation::Assumption {
                    index,
                    equality_side: Some(false),
                });
                self.constraints.insert_le(p.checked_scale(-1)?, backward)?;
            }
            _ => unreachable!(),
        }
        Ok(())
    }

    pub fn solve(mut self, limits: Limits) -> Result<(Self, Outcome), Failure> {
        let mut stats = Stats::default();
        let outcome = search(
            &self.constraints,
            Vec::new(),
            &mut self.derivations,
            limits,
            &mut stats,
        )?;
        Ok((self, outcome))
    }
}

#[derive(Debug, Clone, Copy)]
struct Bound {
    value: Z,
    constraint: usize,
}

fn search(
    constraints: &Constraints,
    mut values: Vec<Z>,
    dag: &mut DerivationDag,
    limits: Limits,
    stats: &mut Stats,
) -> Result<Outcome, Failure> {
    stats.steps = stats.steps.saturating_add(1);
    if stats.steps > limits.max_steps {
        return Ok(resource(
            constraints,
            values,
            ResourceReason::StepLimit,
            *stats,
        ));
    }

    if let Some(c) = constraints
        .le
        .iter()
        .find(|c| c.p.coeffs.is_zero() && c.p.constant > 0)
    {
        let root = dag.push(Derivation::ConstantInequality {
            constraint: c.derivation,
        });
        return Ok(contradiction(root, dag, *stats));
    }
    if let Some(c) = constraints
        .dvd
        .iter()
        .find(|c| c.p.coeffs.is_zero() && c.p.constant.rem_euclid(c.divisor) != 0)
    {
        let root = dag.push(Derivation::ConstantDivisibility {
            constraint: c.derivation,
        });
        return Ok(contradiction(root, dag, *stats));
    }

    let variable_count = constraints
        .le
        .iter()
        .map(|c| c.p.coeffs.as_slice().len())
        .chain(constraints.dvd.iter().map(|c| c.p.coeffs.as_slice().len()))
        .max()
        .unwrap_or(0);
    if values.len() == variable_count {
        if !valid_model(constraints, &values)? {
            return Err(Failure::InvalidConstraint {
                detail: format!("CutSat constructed an invalid model: {values:?}"),
            });
        }
        return Ok(Outcome::Model {
            values,
            stats: *stats,
        });
    }
    let variable = values.len();
    let mut lower: Option<Bound> = None;
    let mut upper: Option<Bound> = None;
    for (id, c) in constraints.le.iter().enumerate() {
        if leading_variable(&c.p) != Some(variable) {
            continue;
        }
        let coefficient = c.p.coeffs.get(variable);
        let tail = eval_assigned(&c.p, &values)?;
        let numerator = neg(tail)?;
        if coefficient < 0 {
            let candidate = Bound {
                value: ceil_div(numerator, coefficient)?,
                constraint: id,
            };
            if lower.is_none_or(|old| candidate.value > old.value) {
                lower = Some(candidate);
            }
        } else if coefficient > 0 {
            let candidate = Bound {
                value: floor_div(numerator, coefficient)?,
                constraint: id,
            };
            if upper.is_none_or(|old| candidate.value < old.value) {
                upper = Some(candidate);
            }
        }
    }

    if let (Some(l), Some(u)) = (lower, upper) {
        if rational_conflict(constraints, l.constraint, u.constraint, &values)? {
            let mut next = constraints.clone();
            let derived = real_projection(
                &constraints.le[l.constraint].p,
                &constraints.le[u.constraint].p,
                variable,
            )?;
            let d = dag.push(Derivation::RealProjection {
                lower: constraints.le[l.constraint].derivation,
                upper: constraints.le[u.constraint].derivation,
            });
            if !next.insert_le(derived, d)? {
                return Ok(resource(
                    constraints,
                    values,
                    ResourceReason::RepeatedConflict,
                    *stats,
                ));
            }
            stats.projections += 1;
            stats.derived_constraints += 1;
            return search(&next, Vec::new(), dag, limits, stats);
        }
    }

    let active_dvd: Vec<usize> = constraints
        .dvd
        .iter()
        .enumerate()
        .filter_map(|(i, c)| (leading_variable(&c.p) == Some(variable)).then_some(i))
        .collect();
    let solved = active_dvd
        .iter()
        .map(|id| solve_congruence(&constraints.dvd[*id], variable, &values))
        .collect::<Result<Vec<_>, _>>()?;
    if let Some(position) = solved.iter().position(Option::is_none) {
        let id = active_dvd[position];
        let old = &constraints.dvd[id];
        let coefficient = old.p.coeffs.get(variable);
        let g = gcd(abs(coefficient)?, old.divisor);
        let projected = without_variable(&old.p, variable);
        let mut next = constraints.clone();
        let d = dag.push(Derivation::DivisibilityProjection {
            divisibility: old.derivation,
        });
        if !next.insert_dvd(g, projected, d)? {
            return Ok(resource(
                constraints,
                values,
                ResourceReason::RepeatedConflict,
                *stats,
            ));
        }
        stats.projections += 1;
        stats.derived_constraints += 1;
        return search(&next, Vec::new(), dag, limits, stats);
    }

    let mut residue: Option<(Z, Z)> = None;
    let mut residue_source: Option<usize> = None;
    for (position, solved) in solved.iter().copied().enumerate() {
        let Some(next) = solved else { unreachable!() };
        if let Some(old) = residue {
            let Some(combined) = combine_congruences(old, next)? else {
                if variable != 0 {
                    return Ok(resource(
                        constraints,
                        values,
                        ResourceReason::MultipleDivisibilityConstraints {
                            variable,
                            count: active_dvd.len(),
                        },
                        *stats,
                    ));
                }
                let left = constraints.dvd[active_dvd[residue_source.unwrap()]].derivation;
                let right = constraints.dvd[active_dvd[position]].derivation;
                let root = dag.push(Derivation::DivisibilityConflict { left, right });
                return Ok(contradiction(root, dag, *stats));
            };
            residue = Some(combined);
        } else {
            residue = Some(next);
            residue_source = Some(position);
        }
    }
    if let Some(value) = choose_value(lower.map(|b| b.value), upper.map(|b| b.value), residue)? {
        values.push(value);
        stats.assignments += 1;
        return search(constraints, values, dag, limits, stats);
    }

    let (lower, upper) = (
        lower.expect("integer conflict has a lower bound"),
        upper.expect("integer conflict has an upper bound"),
    );
    if active_dvd.len() > 1 {
        let individually_blocking = active_dvd.iter().zip(&solved).find_map(|(id, solution)| {
            let solution = solution.as_ref().copied()?;
            choose_value(Some(lower.value), Some(upper.value), Some(solution))
                .ok()
                .flatten()
                .is_none()
                .then_some(*id)
        });
        if let Some(dvd_id) = individually_blocking {
            return cooper_split(
                constraints,
                values,
                lower.constraint,
                upper.constraint,
                Some(dvd_id),
                dag,
                limits,
                stats,
            );
        }
        return exclude_tail_value(
            constraints,
            values,
            lower.constraint,
            upper.constraint,
            &active_dvd,
            dag,
            limits,
            stats,
        );
    }
    cooper_split(
        constraints,
        values,
        lower.constraint,
        upper.constraint,
        active_dvd.first().copied(),
        dag,
        limits,
        stats,
    )
}

fn exclude_tail_value(
    constraints: &Constraints,
    values: Vec<Z>,
    lower_id: usize,
    upper_id: usize,
    dvd_ids: &[usize],
    dag: &mut DerivationDag,
    limits: Limits,
    stats: &mut Stats,
) -> Result<Outcome, Failure> {
    if values.is_empty() {
        let root = dag.push(Derivation::CombinedCongruenceBoundConflict {
            lower: constraints.le[lower_id].derivation,
            upper: constraints.le[upper_id].derivation,
            divisibility: dvd_ids
                .iter()
                .map(|id| constraints.dvd[*id].derivation)
                .collect(),
        });
        return Ok(contradiction(root, dag, *stats));
    }
    if values.len() != 1 {
        let variable = values.len();
        return Ok(resource(
            constraints,
            values,
            ResourceReason::MultipleDivisibilityConstraints {
                variable,
                count: dvd_ids.len(),
            },
            *stats,
        ));
    }
    if stats.cases.saturating_add(2) > limits.max_cases {
        return Ok(resource(
            constraints,
            values,
            ResourceReason::CaseLimit,
            *stats,
        ));
    }
    let excluded = values[0];
    let mut parents = vec![
        constraints.le[lower_id].derivation,
        constraints.le[upper_id].derivation,
    ];
    parents.extend(dvd_ids.iter().map(|id| constraints.dvd[*id].derivation));
    let mut roots = Vec::new();
    for below in [true, false] {
        stats.cases += 1;
        let mut branch = constraints.clone();
        let cut = if below {
            Affine::atom(0).checked_sub(&Affine::constant(add(excluded, -1)?))?
        } else {
            Affine::constant(add(excluded, 1)?).checked_sub(&Affine::atom(0))?
        };
        let d = dag.push(Derivation::CongruenceExclusion {
            constraints: parents.clone(),
            variable: 0,
            value: excluded,
            below,
        });
        branch.insert_le(cut, d)?;
        stats.derived_constraints += 1;
        match search(&branch, Vec::new(), dag, limits, stats)? {
            outcome @ Outcome::Model { .. } | outcome @ Outcome::ResourceLimit { .. } => {
                return Ok(outcome);
            }
            Outcome::Contradiction { root, .. } => roots.push(root),
        }
    }
    stats.splits += 1;
    let root = dag.push(Derivation::ExclusionExhausted {
        below: roots[0],
        above: roots[1],
    });
    Ok(contradiction(root, dag, *stats))
}

fn cooper_split(
    constraints: &Constraints,
    values: Vec<Z>,
    lower_id: usize,
    upper_id: usize,
    dvd_id: Option<usize>,
    dag: &mut DerivationDag,
    limits: Limits,
    stats: &mut Stats,
) -> Result<Outcome, Failure> {
    let variable = values.len();
    let lower = &constraints.le[lower_id];
    let upper = &constraints.le[upper_id];
    let a = lower.p.coeffs.get(variable);
    let b = upper.p.coeffs.get(variable);
    debug_assert!(a < 0 && b > 0);
    let left = abs(a)? < abs(b)?;
    let count = cooper_case_count(a, b, dvd_id.map(|id| &constraints.dvd[id]))?;
    if stats
        .cases
        .saturating_add(usize::try_from(count).unwrap_or(usize::MAX))
        > limits.max_cases
    {
        return Ok(resource(
            constraints,
            values,
            ResourceReason::CaseLimit,
            *stats,
        ));
    }
    stats.splits += 1;
    let p = without_variable(&lower.p, variable);
    let q = without_variable(&upper.p, variable);
    let base = p
        .checked_scale(b)?
        .checked_add(&q.checked_scale(neg(a)?)?)?;
    let mut roots = Vec::new();
    for k in 0..count {
        stats.cases += 1;
        let shift = if left { mul(b, k)? } else { mul(neg(a)?, k)? };
        let cut = base.checked_add(&Affine::constant(shift))?;
        let mut branch = constraints.clone();
        let parent_dvd = dvd_id.map(|id| constraints.dvd[id].derivation);
        let cut_d = dag.push(Derivation::CooperInequality {
            lower: lower.derivation,
            upper: upper.derivation,
            divisibility: parent_dvd,
            case: k,
        });
        branch.insert_le(cut, cut_d)?;
        let selected = if left { a } else { b };
        if abs(selected)? != 1 {
            let selected_tail = if left { &p } else { &q };
            let affine = selected_tail.checked_add(&Affine::constant(k))?;
            let d = dag.push(Derivation::CooperDivisibility {
                lower: lower.derivation,
                upper: upper.derivation,
                divisibility: parent_dvd,
                case: k,
            });
            if branch.insert_dvd(selected, affine, d)? {
                stats.derived_constraints += 1;
            }
        }
        if let Some(dvd_id) = dvd_id {
            let old = &constraints.dvd[dvd_id];
            let c = old.p.coeffs.get(variable);
            let s = without_variable(&old.p, variable);
            let affine = if left {
                p.checked_scale(c)?
                    .checked_add(&s.checked_scale(neg(a)?)?)?
                    .checked_add(&Affine::constant(mul(c, k)?))?
            } else {
                q.checked_scale(neg(c)?)?
                    .checked_add(&s.checked_scale(b)?)?
                    .checked_add(&Affine::constant(neg(mul(c, k)?)?))?
            };
            let modulus = if left {
                mul(a, old.divisor)?
            } else {
                mul(b, old.divisor)?
            };
            let d = dag.push(Derivation::CooperDivisibility {
                lower: lower.derivation,
                upper: upper.derivation,
                divisibility: Some(old.derivation),
                case: k,
            });
            if branch.insert_dvd(modulus, affine, d)? {
                stats.derived_constraints += 1;
            }
        }
        stats.derived_constraints += 1;
        match search(&branch, Vec::new(), dag, limits, stats)? {
            model @ Outcome::Model { .. } | model @ Outcome::ResourceLimit { .. } => {
                return Ok(model);
            }
            Outcome::Contradiction { root, .. } => roots.push(root),
        }
    }
    let root = dag.push(Derivation::CooperExhausted { cases: roots });
    Ok(contradiction(root, dag, *stats))
}

fn contradiction(root: usize, dag: &DerivationDag, stats: Stats) -> Outcome {
    Outcome::Contradiction {
        root,
        reachable: dag.reachable(root),
        stats,
    }
}

fn resource(
    constraints: &Constraints,
    partial_model: Vec<Z>,
    reason: ResourceReason,
    stats: Stats,
) -> Outcome {
    Outcome::ResourceLimit {
        partial_model,
        residual: constraints.residual(),
        reason,
        stats,
    }
}

fn leading_variable(p: &Affine) -> Option<usize> {
    p.coeffs.as_slice().iter().rposition(|c| *c != 0)
}

fn without_variable(p: &Affine, variable: usize) -> Affine {
    Affine {
        constant: p.constant,
        coeffs: p.coeffs.with_coefficient(variable, 0),
    }
}

fn eval_assigned(p: &Affine, values: &[Z]) -> Result<Z, Failure> {
    values
        .iter()
        .enumerate()
        .try_fold(p.constant, |out, (i, value)| {
            add(out, mul(p.coeffs.get(i), *value)?)
        })
}

fn eval(p: &Affine, values: &[Z]) -> Result<Z, Failure> {
    p.coeffs
        .as_slice()
        .iter()
        .enumerate()
        .try_fold(p.constant, |out, (i, coefficient)| {
            add(out, mul(*coefficient, values[i])?)
        })
}

fn valid_model(constraints: &Constraints, values: &[Z]) -> Result<bool, Failure> {
    for constraint in &constraints.le {
        if eval(&constraint.p, values)? > 0 {
            return Ok(false);
        }
    }
    for constraint in &constraints.dvd {
        if eval(&constraint.p, values)?.rem_euclid(constraint.divisor) != 0 {
            return Ok(false);
        }
    }
    Ok(true)
}

fn floor_div(numerator: Z, denominator: Z) -> Result<Z, Failure> {
    let (numerator, denominator) = if denominator < 0 {
        (neg(numerator)?, neg(denominator)?)
    } else {
        (numerator, denominator)
    };
    numerator
        .checked_div_euclid(denominator)
        .ok_or(Failure::Overflow {
            operation: "dividing a bound",
        })
}

fn ceil_div(numerator: Z, denominator: Z) -> Result<Z, Failure> {
    neg(floor_div(neg(numerator)?, denominator)?)
}

fn rational_conflict(
    constraints: &Constraints,
    lower: usize,
    upper: usize,
    values: &[Z],
) -> Result<bool, Failure> {
    let p = &constraints.le[lower].p;
    let q = &constraints.le[upper].p;
    let a = p.coeffs.get(values.len());
    let b = q.coeffs.get(values.len());
    let projected = add(
        mul(eval_assigned(p, values)?, b)?,
        mul(eval_assigned(q, values)?, neg(a)?)?,
    )?;
    Ok(projected > 0)
}

fn real_projection(lower: &Affine, upper: &Affine, variable: usize) -> Result<Affine, Failure> {
    let a = lower.coeffs.get(variable);
    let b = upper.coeffs.get(variable);
    without_variable(lower, variable)
        .checked_scale(b)?
        .checked_add(&without_variable(upper, variable).checked_scale(neg(a)?)?)
}

fn solve_congruence(
    c: &DvdConstraint,
    variable: usize,
    values: &[Z],
) -> Result<Option<(Z, Z)>, Failure> {
    let a = c.p.coeffs.get(variable);
    let tail = eval_assigned(&c.p, values)?;
    let g = gcd(abs(a)?, c.divisor);
    if tail.rem_euclid(g) != 0 {
        return Ok(None);
    }
    let modulus = c.divisor / g;
    if modulus == 1 {
        return Ok(Some((0, 1)));
    }
    let reduced_a = a / g;
    let rhs = neg(tail / g)?.rem_euclid(modulus);
    let inverse = modular_inverse(reduced_a.rem_euclid(modulus), modulus)?.ok_or(
        Failure::InvalidConstraint {
            detail: "reduced congruence was not invertible".into(),
        },
    )?;
    Ok(Some((mul(rhs, inverse)?.rem_euclid(modulus), modulus)))
}

fn choose_value(
    lower: Option<Z>,
    upper: Option<Z>,
    congruence: Option<(Z, Z)>,
) -> Result<Option<Z>, Failure> {
    let (residue, modulus) = congruence.unwrap_or((0, 1));
    let candidate = if let Some(lower) = lower {
        let offset = add(lower, neg(residue)?)?.rem_euclid(modulus);
        add(lower, neg(offset)?.rem_euclid(modulus))?
    } else if let Some(upper) = upper {
        let offset = add(upper, neg(residue)?)?.rem_euclid(modulus);
        add(upper, neg(offset)?)?
    } else {
        residue
    };
    Ok(upper
        .is_none_or(|upper| candidate <= upper)
        .then_some(candidate))
}

fn combine_congruences(left: (Z, Z), right: (Z, Z)) -> Result<Option<(Z, Z)>, Failure> {
    let (left_residue, left_modulus) = left;
    let (right_residue, right_modulus) = right;
    let g = gcd(left_modulus, right_modulus);
    let difference = add(right_residue, neg(left_residue)?)?;
    if difference.rem_euclid(g) != 0 {
        return Ok(None);
    }
    let right_reduced = right_modulus / g;
    let factor = if right_reduced == 1 {
        0
    } else {
        let inverse = modular_inverse((left_modulus / g).rem_euclid(right_reduced), right_reduced)?
            .ok_or(Failure::InvalidConstraint {
                detail: "CRT moduli did not become coprime after dividing their GCD".into(),
            })?;
        mul(difference / g, inverse)?.rem_euclid(right_reduced)
    };
    let modulus = lcm(left_modulus, right_modulus)?;
    let residue = add(left_residue, mul(left_modulus, factor)?)?.rem_euclid(modulus);
    Ok(Some((residue, modulus)))
}

fn cooper_case_count(a: Z, b: Z, dvd: Option<&DvdConstraint>) -> Result<Z, Failure> {
    let selected = if abs(a)? < abs(b)? { a } else { b };
    let selected = abs(selected)?;
    let Some(dvd) = dvd else {
        return Ok(selected);
    };
    let c = dvd.p.coeffs.as_slice().last().copied().unwrap_or(0);
    let product = mul(selected, dvd.divisor)?;
    lcm(selected, product / gcd(abs(product)?, abs(c)?))
}

fn gcd(mut a: Z, mut b: Z) -> Z {
    while b != 0 {
        let r = a.rem_euclid(b);
        a = b;
        b = r;
    }
    a
}

fn lcm(a: Z, b: Z) -> Result<Z, Failure> {
    if a == 0 || b == 0 {
        return Ok(0);
    }
    abs(mul(a / gcd(abs(a)?, abs(b)?), b)?)
}

fn modular_inverse(a: Z, modulus: Z) -> Result<Option<Z>, Failure> {
    let (mut old_r, mut r) = (a, modulus);
    let (mut old_s, mut s) = (1, 0);
    while r != 0 {
        let q = old_r.div_euclid(r);
        (old_r, r) = (r, add(old_r, neg(mul(q, r)?)?)?);
        (old_s, s) = (s, add(old_s, neg(mul(q, s)?)?)?);
    }
    Ok((old_r == 1).then_some(old_s.rem_euclid(modulus)))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scaled_atom(index: usize, coefficient: Z) -> Affine {
        Affine::atom(index).checked_scale(coefficient).unwrap()
    }

    fn row(coefficients: &[Z]) -> Affine {
        coefficients
            .iter()
            .enumerate()
            .fold(Affine::constant(0), |out, (i, coefficient)| {
                out.checked_add(&scaled_atom(i, *coefficient)).unwrap()
            })
    }

    fn add_interval(problem: &mut Problem, coefficients: &[Z], lower: Z, upper: Z) {
        let affine = row(coefficients);
        problem
            .assume(Affine::constant(lower), Relation::Le, affine.clone())
            .unwrap();
        problem
            .assume(affine, Relation::Le, Affine::constant(upper))
            .unwrap();
    }

    #[test]
    fn finds_an_integer_model() {
        let x = Affine::atom(0);
        let mut problem = Problem::new();
        problem
            .assume(Affine::constant(2), Relation::Le, x.clone())
            .unwrap();
        problem
            .assume(x, Relation::Le, Affine::constant(5))
            .unwrap();
        let (_, outcome) = problem.solve(Limits::default()).unwrap();
        assert!(matches!(outcome, Outcome::Model { values, .. } if values == vec![2]));
    }

    #[test]
    fn equality_exposes_integrality_conflict() {
        let mut problem = Problem::new();
        problem
            .assume(scaled_atom(0, 2), Relation::Eq, Affine::constant(1))
            .unwrap();
        let (_, outcome) = problem.solve(Limits::default()).unwrap();
        assert!(matches!(outcome, Outcome::Contradiction { .. }));
    }

    #[test]
    fn limits_return_structured_partial_state() {
        let mut problem = Problem::new();
        problem
            .assume(Affine::constant(0), Relation::Le, Affine::atom(0))
            .unwrap();
        let (_, outcome) = problem
            .solve(Limits {
                max_steps: 0,
                max_cases: 0,
            })
            .unwrap();
        assert!(matches!(
            outcome,
            Outcome::ResourceLimit {
                reason: ResourceReason::StepLimit,
                partial_model,
                residual,
                ..
            } if partial_model.is_empty() && !residual.is_empty()
        ));

        let mut problem = Problem::new();
        add_interval(&mut problem, &[11, 13], 27, 45);
        add_interval(&mut problem, &[7, -9], -10, 4);
        add_interval(&mut problem, &[1, 0], -16, 16);
        add_interval(&mut problem, &[0, 1], -16, 16);
        let (_, outcome) = problem
            .solve(Limits {
                max_steps: 100,
                max_cases: 0,
            })
            .unwrap();
        assert!(matches!(
            outcome,
            Outcome::ResourceLimit {
                reason: ResourceReason::CaseLimit,
                ..
            }
        ));
    }

    #[test]
    fn closes_the_minimal_real_shadow_gap() {
        let x = Affine::atom(0);
        let y = Affine::atom(1);
        let first = scaled_atom(0, 2).checked_add(&scaled_atom(1, 3)).unwrap();
        let second = scaled_atom(0, 2).checked_add(&scaled_atom(1, 5)).unwrap();
        let mut problem = Problem::new();
        problem
            .assume(Affine::constant(-2), Relation::Le, first)
            .unwrap();
        problem
            .assume(second, Relation::Le, Affine::constant(0))
            .unwrap();
        problem
            .assume(Affine::constant(1), Relation::Le, y)
            .unwrap();
        let (_, outcome) = problem.solve(Limits::default()).unwrap();
        assert!(matches!(outcome, Outcome::Contradiction { .. }));
        let _ = x;
    }

    #[test]
    fn closes_pughs_nightmare() {
        let mut problem = Problem::new();
        add_interval(&mut problem, &[11, 13], 27, 45);
        add_interval(&mut problem, &[7, -9], -10, 4);
        add_interval(&mut problem, &[1, 0], -16, 16);
        add_interval(&mut problem, &[0, 1], -16, 16);
        let (_, outcome) = problem.solve(Limits::default()).unwrap();
        assert!(
            matches!(
                outcome,
                Outcome::Contradiction { stats, .. } if stats.splits > 0
            ),
            "{outcome:?}"
        );
    }

    #[test]
    fn seeded_bounded_systems_close_the_pinned_integrality_gap() {
        fn next(state: &mut u64) -> u64 {
            *state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            *state
        }

        let mut models = 0usize;
        let mut contradictions = 0usize;
        for seed in 0..20_000u64 {
            let mut state = seed;
            let mut generated = Vec::new();
            let mut problem = Problem::new();
            for _ in 0..4 {
                let mut coefficients = [
                    (next(&mut state) % 11) as Z - 5,
                    (next(&mut state) % 11) as Z - 5,
                ];
                if coefficients == [0, 0] {
                    coefficients[0] = 1;
                }
                let bound = (next(&mut state) % 17) as Z - 8;
                let lower = next(&mut state) & 1 == 0;
                let affine = row(&coefficients);
                if lower {
                    problem
                        .assume(Affine::constant(bound), Relation::Le, affine)
                        .unwrap();
                } else {
                    problem
                        .assume(affine, Relation::Le, Affine::constant(bound))
                        .unwrap();
                }
                generated.push((coefficients, bound, lower));
            }
            add_interval(&mut problem, &[1, 0], -4, 4);
            add_interval(&mut problem, &[0, 1], -4, 4);
            let exhaustive = (-4..=4).any(|x| {
                (-4..=4).any(|y| {
                    generated.iter().all(|(c, bound, lower)| {
                        let value = c[0] * x + c[1] * y;
                        if *lower {
                            *bound <= value
                        } else {
                            value <= *bound
                        }
                    })
                })
            });
            match problem.solve(Limits::default()).unwrap().1 {
                Outcome::Model { values, .. } => {
                    assert!(exhaustive, "spurious model at seed {seed}: {values:?}");
                    models += 1;
                }
                Outcome::Contradiction { .. } => {
                    assert!(!exhaustive, "spurious contradiction at seed {seed}");
                    contradictions += 1;
                }
                Outcome::ResourceLimit { reason, .. } => {
                    panic!("CutSat stopped at seed {seed}: {reason:?}")
                }
            }
        }
        assert_eq!((models, contradictions), (11_074, 8_926));
    }
}
