//! CutSat: a model-based decision procedure for linear integer arithmetic.
//!
//! The search assigns variables in order (lowest index first). A variable's
//! value must lie between the tightest bounds its constraints give under the
//! values already chosen, satisfy its one divisibility constraint, and avoid
//! the values its disequalities exclude. When no value fits, the search learns
//! a constraint over lower variables and starts again:
//!
//! - bounds that cross over the reals give their **resolvent** (Fourier–Motzkin
//!   on that one pair);
//! - a congruence with no solution gives the divisibility of the rest of its
//!   row (**drop**);
//! - bounds that admit a real but no integer (or no congruent) value split by
//!   **Cooper**'s rule into finitely many cases, each adding constraints free
//!   of the variable;
//! - a disequality that excludes the last candidate **splits** into its two
//!   strict sides.
//!
//! Divisibility constraints stay in solved form, at most one per leading
//! variable: a second one on the same variable is combined with the first
//! (**solve-div**) into one constraint on that variable and one without it.
//!
//! The search is untrusted. It records every learned constraint as a node of
//! a [`DerivationDag`] whose shape is the certificate: a node is made once,
//! however many branches use it, and each case of a split opens a scope its
//! hypotheses live in. `omega_cert` writes one `have` per reachable node and
//! the kernel checks the result.

use std::collections::HashMap;

use crate::arithmetic::{Affine, Failure, Relation, Z, abs, add, mul, neg};

/// One step of the search. Every node concludes a [`DerivedConstraint`]; the
/// splits (`Cooper`, `DiseqSplit`) and the constant conflicts conclude `False`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Derivation {
    /// The caller's fact `index`, as `p <= 0`; `equality_side` names one side
    /// of an equation.
    Assumption {
        index: usize,
        equality_side: Option<bool>,
    },
    /// The caller's fact `index`, as `p ≠ 0`.
    DiseqAssumption { index: usize },
    /// The caller's fact `index`, as `d ∣ p`.
    DvdAssumption { index: usize },
    /// `parent` with its coefficients divided by their gcd, the constant
    /// rounded toward the stronger bound.
    Tighten { parent: usize },
    /// `b·lower + a·upper`, which eliminates `variable` (coefficient `-a` in
    /// `lower`, `b` in `upper`).
    Resolve {
        lower: usize,
        upper: usize,
        variable: usize,
    },
    /// Two divisibilities whose leading variable is `variable`, combined:
    /// `main` keeps the variable, the other does not.
    SolveDiv {
        left: usize,
        right: usize,
        variable: usize,
        main: bool,
    },
    /// `d ∣ a·x + p` with no solution for `x`: `gcd(a, d) ∣ p`.
    DvdDrop { divisibility: usize, variable: usize },
    /// A case's hypothesis; its split names it.
    Hypothesis { scope: usize },
    /// Cooper's split of `variable` between `lower` and `upper` (and the
    /// variable's divisibility, if any): one case per `k < period`.
    Cooper {
        lower: usize,
        upper: usize,
        divisibility: Option<usize>,
        variable: usize,
        left: bool,
        period: Z,
        cases: Vec<CooperCase>,
    },
    /// `p ≠ 0` split into `p + 1 <= 0` and `-p + 1 <= 0`.
    DiseqSplit {
        diseq: usize,
        below: SplitCase,
        above: SplitCase,
    },
    /// `c <= 0` with `c > 0`.
    ConstantLe { constraint: usize },
    /// `d ∣ c` with `c` not a multiple of `d`.
    ConstantDvd { constraint: usize },
    /// `0 ≠ 0`.
    ConstantDiseq { constraint: usize },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CooperCase {
    pub scope: usize,
    /// The bound free of the variable.
    pub cut: usize,
    /// The selected side's divisibility.
    pub selected: usize,
    /// The variable's divisibility carried through, when it had one.
    pub carried: Option<usize>,
    pub contradiction: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SplitCase {
    pub scope: usize,
    pub hypothesis: usize,
    pub contradiction: usize,
}

impl Derivation {
    /// The nodes this one's proof uses. A split's cases are included through
    /// their contradictions; their hypotheses are bound by the split.
    pub(crate) fn parents(&self) -> Vec<usize> {
        match self {
            Self::Assumption { .. }
            | Self::DiseqAssumption { .. }
            | Self::DvdAssumption { .. }
            | Self::Hypothesis { .. } => Vec::new(),
            Self::Tighten { parent } => vec![*parent],
            Self::Resolve { lower, upper, .. } => vec![*lower, *upper],
            Self::SolveDiv { left, right, .. } => vec![*left, *right],
            Self::DvdDrop { divisibility, .. } => vec![*divisibility],
            Self::Cooper {
                lower,
                upper,
                divisibility,
                cases,
                ..
            } => {
                let mut out = vec![*lower, *upper];
                out.extend(divisibility.iter().copied());
                out.extend(cases.iter().map(|case| case.contradiction));
                out
            }
            Self::DiseqSplit { diseq, below, above } => {
                vec![*diseq, below.contradiction, above.contradiction]
            }
            Self::ConstantLe { constraint }
            | Self::ConstantDvd { constraint }
            | Self::ConstantDiseq { constraint } => vec![*constraint],
        }
    }

    /// The nodes whose scope bounds this one's: a split lives where the
    /// search made it, not where its premises do.
    fn premises(&self) -> Vec<usize> {
        match self {
            Self::Cooper { .. } | Self::DiseqSplit { .. } => Vec::new(),
            other => other.parents(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DerivedConstraint {
    /// `affine <= 0`.
    Le(Affine),
    /// `divisor ∣ affine`, `divisor > 0`.
    Dvd { divisor: Z, affine: Affine },
    /// `affine ≠ 0`.
    Ne(Affine),
    False,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Scope {
    pub parent: Option<usize>,
    pub depth: usize,
}

#[derive(Debug, Clone)]
pub struct DerivationDag {
    nodes: Vec<Derivation>,
    conclusions: Vec<DerivedConstraint>,
    scope_of: Vec<usize>,
    scopes: Vec<Scope>,
    memo: HashMap<Derivation, usize>,
}

impl Default for DerivationDag {
    fn default() -> Self {
        Self {
            nodes: Vec::new(),
            conclusions: Vec::new(),
            scope_of: Vec::new(),
            scopes: vec![Scope {
                parent: None,
                depth: 0,
            }],
            memo: HashMap::new(),
        }
    }
}

/// The scope every assumption lives in.
pub const ROOT_SCOPE: usize = 0;

impl DerivationDag {
    pub fn nodes(&self) -> &[Derivation] {
        &self.nodes
    }

    pub fn conclusion(&self, id: usize) -> Option<&DerivedConstraint> {
        self.conclusions.get(id)
    }

    /// The scope a node's proof is written in: the deepest scope among its
    /// premises', or for a split the scope the search made it in.
    pub fn scope_of(&self, id: usize) -> usize {
        self.scope_of[id]
    }

    pub fn scopes(&self) -> &[Scope] {
        &self.scopes
    }

    fn open_scope(&mut self, parent: usize) -> usize {
        let depth = self.scopes[parent].depth + 1;
        self.scopes.push(Scope {
            parent: Some(parent),
            depth,
        });
        self.scopes.len() - 1
    }

    fn push_in(&mut self, node: Derivation, conclusion: DerivedConstraint, scope: usize) -> usize {
        let id = self.nodes.len();
        self.nodes.push(node);
        self.conclusions.push(conclusion);
        self.scope_of.push(scope);
        id
    }

    /// A node determined by its premises: made once, whichever branch asks.
    fn derive(&mut self, node: Derivation, conclusion: impl FnOnce() -> DerivedConstraint) -> (usize, bool) {
        if let Some(&id) = self.memo.get(&node) {
            return (id, false);
        }
        let scope = node
            .premises()
            .into_iter()
            .map(|parent| self.scope_of[parent])
            .max_by_key(|scope| self.scopes[*scope].depth)
            .unwrap_or(ROOT_SCOPE);
        let id = self.push_in(node.clone(), conclusion(), scope);
        self.memo.insert(node, id);
        (id, true)
    }

    /// Every node the proof of `root` uses, in creation order (which is a
    /// topological order: a node's premises and its cases' contents come
    /// first).
    pub fn reachable(&self, root: usize) -> Vec<usize> {
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
    /// A learned constraint was already present: the search would loop.
    /// The invariant that every assigned variable satisfies the constraints
    /// it leads makes this unreachable; it is reported rather than trusted.
    RepeatedConflict,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResidualConstraint {
    Le(Affine),
    Dvd { divisor: Z, affine: Affine },
    Ne(Affine),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    Contradiction {
        root: usize,
        reachable: Vec<usize>,
        stats: Stats,
    },
    /// A value per variable satisfying every constraint the caller gave.
    Model { values: Vec<Z>, stats: Stats },
    ResourceLimit {
        partial_model: Vec<Z>,
        residual: Vec<ResidualConstraint>,
        reason: ResourceReason,
        stats: Stats,
    },
}

#[derive(Debug, Clone)]
struct Row {
    p: Affine,
    derivation: usize,
}

#[derive(Debug, Clone)]
struct DvdRow {
    divisor: Z,
    p: Affine,
    derivation: usize,
}

#[derive(Debug, Clone, Default)]
struct Constraints {
    le: Vec<Row>,
    dvd: Vec<DvdRow>,
    ne: Vec<Row>,
}

impl Constraints {
    fn residual(&self) -> Vec<ResidualConstraint> {
        self.le
            .iter()
            .map(|c| ResidualConstraint::Le(c.p.clone()))
            .chain(self.dvd.iter().map(|c| ResidualConstraint::Dvd {
                divisor: c.divisor,
                affine: c.p.clone(),
            }))
            .chain(self.ne.iter().map(|c| ResidualConstraint::Ne(c.p.clone())))
            .collect()
    }
}

/// Adds `p <= 0`, concluded by `derivation`, dividing it by its coefficients'
/// gcd first. Returns whether anything new was added.
fn insert_le(
    constraints: &mut Constraints,
    dag: &mut DerivationDag,
    stats: &mut Stats,
    p: Affine,
    derivation: usize,
) -> Result<bool, Failure> {
    let g = p.coeffs.coefficient_gcd()?;
    let (p, derivation) = if g > 1 {
        let tightened = Affine {
            constant: ceil_div(p.constant, g)?,
            coeffs: p.coeffs.exact_div(g)?,
        };
        let (id, fresh) = dag.derive(Derivation::Tighten { parent: derivation }, || {
            DerivedConstraint::Le(tightened.clone())
        });
        if fresh {
            stats.derived_constraints += 1;
        }
        (tightened, id)
    } else {
        (p, derivation)
    };
    if p.coeffs.is_zero() && p.constant <= 0 {
        return Ok(false);
    }
    if constraints.le.iter().any(|old| old.p == p) {
        return Ok(false);
    }
    constraints.le.push(Row { p, derivation });
    Ok(true)
}

/// Adds `divisor ∣ p`, keeping at most one divisibility per leading variable.
fn insert_dvd(
    constraints: &mut Constraints,
    dag: &mut DerivationDag,
    stats: &mut Stats,
    divisor: Z,
    p: Affine,
    derivation: usize,
) -> Result<bool, Failure> {
    debug_assert!(divisor > 0);
    if divisor == 1 {
        return Ok(false);
    }
    if p.coeffs.is_zero() && p.constant.rem_euclid(divisor) == 0 {
        return Ok(false);
    }
    if constraints
        .dvd
        .iter()
        .any(|old| old.divisor == divisor && old.p == p)
    {
        return Ok(false);
    }
    let Some(variable) = leading_variable(&p) else {
        constraints.dvd.push(DvdRow {
            divisor,
            p,
            derivation,
        });
        return Ok(true);
    };
    let Some(position) = constraints
        .dvd
        .iter()
        .position(|old| leading_variable(&old.p) == Some(variable))
    else {
        constraints.dvd.push(DvdRow {
            divisor,
            p,
            derivation,
        });
        return Ok(true);
    };
    // m ∣ a·x + p and n ∣ b·x + q, with g = gcd(a·n, b·m) = u·a·n + v·b·m:
    // m·n ∣ g·x + u·n·p + v·m·q, and g ∣ b·p − a·q.
    let old = constraints.dvd.remove(position);
    let (m, n) = (old.divisor, divisor);
    let (a, b) = (old.p.coeffs.get(variable), p.coeffs.get(variable));
    let (g, u, v) = extended_gcd(mul(a, n)?, mul(b, m)?)?;
    let main = old
        .p
        .checked_scale(mul(u, n)?)?
        .checked_add(&p.checked_scale(mul(v, m)?)?)?;
    let main_divisor = mul(m, n)?;
    let rest = old
        .p
        .checked_scale(b)?
        .checked_add(&p.checked_scale(neg(a)?)?)?;
    let (main_id, fresh_main) = dag.derive(
        Derivation::SolveDiv {
            left: old.derivation,
            right: derivation,
            variable,
            main: true,
        },
        || DerivedConstraint::Dvd {
            divisor: main_divisor,
            affine: main.clone(),
        },
    );
    let (rest_id, fresh_rest) = dag.derive(
        Derivation::SolveDiv {
            left: old.derivation,
            right: derivation,
            variable,
            main: false,
        },
        || DerivedConstraint::Dvd {
            divisor: g,
            affine: rest.clone(),
        },
    );
    stats.derived_constraints += usize::from(fresh_main) + usize::from(fresh_rest);
    insert_dvd(constraints, dag, stats, main_divisor, main, main_id)?;
    insert_dvd(constraints, dag, stats, g, rest, rest_id)?;
    Ok(true)
}

/// Adds `p ≠ 0`. A disequality no integer point can violate is dropped.
fn insert_ne(constraints: &mut Constraints, p: Affine, derivation: usize) -> Result<bool, Failure> {
    let g = p.coeffs.coefficient_gcd()?;
    if g > 1 && p.constant.rem_euclid(g) != 0 {
        return Ok(false);
    }
    if p.coeffs.is_zero() && p.constant != 0 {
        return Ok(false);
    }
    if constraints.ne.iter().any(|old| old.p == p) {
        return Ok(false);
    }
    constraints.ne.push(Row { p, derivation });
    Ok(true)
}

#[derive(Debug, Clone, Default)]
pub struct Problem {
    constraints: Constraints,
    derivations: DerivationDag,
    assumptions: usize,
    stats: Stats,
}

impl Problem {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn derivations(&self) -> &DerivationDag {
        &self.derivations
    }

    fn next_index(&mut self) -> usize {
        let index = self.assumptions;
        self.assumptions += 1;
        index
    }

    /// `lhs relation rhs` as the next assumption; an equation is its two
    /// inequalities.
    pub fn assume(&mut self, lhs: Affine, relation: Relation, rhs: Affine) -> Result<(), Failure> {
        let p = lhs.checked_sub(&rhs)?;
        match relation {
            Relation::Le => {
                let index = self.next_index();
                self.assume_le(p, index)
            }
            Relation::Eq => {
                let index = self.next_index();
                for (side, p) in [(true, p.clone()), (false, p.checked_scale(-1)?)] {
                    let d = self.derivations.push_in(
                        Derivation::Assumption {
                            index,
                            equality_side: Some(side),
                        },
                        DerivedConstraint::Le(p.clone()),
                        ROOT_SCOPE,
                    );
                    insert_le(&mut self.constraints, &mut self.derivations, &mut self.stats, p, d)?;
                }
                Ok(())
            }
            _ => Err(Failure::InvalidConstraint {
                detail: "CutSat reads `=` and `<=` here; `≠` and `∣` have their own entries".into(),
            }),
        }
    }

    /// `p <= 0` as the caller's fact `index`.
    pub fn assume_le(&mut self, p: Affine, index: usize) -> Result<(), Failure> {
        self.assumptions = self.assumptions.max(index + 1);
        let d = self.derivations.push_in(
            Derivation::Assumption {
                index,
                equality_side: None,
            },
            DerivedConstraint::Le(p.clone()),
            ROOT_SCOPE,
        );
        insert_le(&mut self.constraints, &mut self.derivations, &mut self.stats, p, d)?;
        Ok(())
    }

    /// `p ≠ 0` as the caller's fact `index`.
    pub fn assume_ne(&mut self, p: Affine, index: usize) -> Result<(), Failure> {
        self.assumptions = self.assumptions.max(index + 1);
        let d = self.derivations.push_in(
            Derivation::DiseqAssumption { index },
            DerivedConstraint::Ne(p.clone()),
            ROOT_SCOPE,
        );
        insert_ne(&mut self.constraints, p, d)?;
        Ok(())
    }

    /// `divisor ∣ p` as the caller's fact `index`.
    pub fn assume_dvd(&mut self, divisor: Z, p: Affine, index: usize) -> Result<(), Failure> {
        if divisor <= 0 {
            return Err(Failure::InvalidConstraint {
                detail: "a divisibility needs a positive divisor".into(),
            });
        }
        self.assumptions = self.assumptions.max(index + 1);
        let d = self.derivations.push_in(
            Derivation::DvdAssumption { index },
            DerivedConstraint::Dvd {
                divisor,
                affine: p.clone(),
            },
            ROOT_SCOPE,
        );
        insert_dvd(&mut self.constraints, &mut self.derivations, &mut self.stats, divisor, p, d)?;
        Ok(())
    }

    pub fn solve(mut self, limits: Limits) -> Result<(Self, Outcome), Failure> {
        let mut stats = self.stats;
        let constraints = std::mem::take(&mut self.constraints);
        let outcome = search(constraints, ROOT_SCOPE, &mut self.derivations, limits, &mut stats)?;
        Ok((self, outcome))
    }
}

#[derive(Debug, Clone, Copy)]
struct Bound {
    value: Z,
    constraint: usize,
}

/// What blocks the variable the search is assigning.
enum Blocked {
    /// The pair of bounds (and the divisibility) leave no integer.
    Cooper {
        lower: usize,
        upper: usize,
        divisibility: Option<usize>,
    },
    /// Every candidate is excluded; this disequality excludes one of them.
    Diseq(usize),
}

fn search(
    mut constraints: Constraints,
    scope: usize,
    dag: &mut DerivationDag,
    limits: Limits,
    stats: &mut Stats,
) -> Result<Outcome, Failure> {
    'restart: loop {
        stats.steps = stats.steps.saturating_add(1);
        if stats.steps > limits.max_steps {
            return Ok(resource(&constraints, Vec::new(), ResourceReason::StepLimit, *stats));
        }
        if let Some(c) = constraints
            .le
            .iter()
            .find(|c| c.p.coeffs.is_zero() && c.p.constant > 0)
        {
            let (root, _) = dag.derive(
                Derivation::ConstantLe {
                    constraint: c.derivation,
                },
                || DerivedConstraint::False,
            );
            return Ok(contradiction(root, dag, *stats));
        }
        if let Some(c) = constraints
            .dvd
            .iter()
            .find(|c| c.p.coeffs.is_zero() && c.p.constant.rem_euclid(c.divisor) != 0)
        {
            let (root, _) = dag.derive(
                Derivation::ConstantDvd {
                    constraint: c.derivation,
                },
                || DerivedConstraint::False,
            );
            return Ok(contradiction(root, dag, *stats));
        }
        if let Some(c) = constraints
            .ne
            .iter()
            .find(|c| c.p.coeffs.is_zero() && c.p.constant == 0)
        {
            let (root, _) = dag.derive(
                Derivation::ConstantDiseq {
                    constraint: c.derivation,
                },
                || DerivedConstraint::False,
            );
            return Ok(contradiction(root, dag, *stats));
        }

        let variable_count = constraints
            .le
            .iter()
            .chain(&constraints.ne)
            .map(|c| c.p.coeffs.as_slice().len())
            .chain(constraints.dvd.iter().map(|c| c.p.coeffs.as_slice().len()))
            .max()
            .unwrap_or(0);
        let mut values: Vec<Z> = Vec::with_capacity(variable_count);
        while values.len() < variable_count {
            let variable = values.len();
            let mut lower: Option<Bound> = None;
            let mut upper: Option<Bound> = None;
            for (id, c) in constraints.le.iter().enumerate() {
                if leading_variable(&c.p) != Some(variable) {
                    continue;
                }
                let coefficient = c.p.coeffs.get(variable);
                let numerator = neg(eval_assigned(&c.p, &values)?)?;
                if coefficient < 0 {
                    let value = ceil_div(numerator, coefficient)?;
                    if lower.is_none_or(|old| value > old.value) {
                        lower = Some(Bound { value, constraint: id });
                    }
                } else {
                    let value = floor_div(numerator, coefficient)?;
                    if upper.is_none_or(|old| value < old.value) {
                        upper = Some(Bound { value, constraint: id });
                    }
                }
            }

            if let (Some(l), Some(u)) = (lower, upper)
                && rational_conflict(&constraints.le[l.constraint].p, &constraints.le[u.constraint].p, &values)?
            {
                let lower_row = &constraints.le[l.constraint];
                let upper_row = &constraints.le[u.constraint];
                let resolvent = real_projection(&lower_row.p, &upper_row.p, variable)?;
                let (d, _) = dag.derive(
                    Derivation::Resolve {
                        lower: lower_row.derivation,
                        upper: upper_row.derivation,
                        variable,
                    },
                    || DerivedConstraint::Le(resolvent.clone()),
                );
                stats.projections += 1;
                stats.derived_constraints += 1;
                if !insert_le(&mut constraints, dag, stats, resolvent, d)? {
                    return Ok(resource(&constraints, values, ResourceReason::RepeatedConflict, *stats));
                }
                continue 'restart;
            }

            let dvd = constraints
                .dvd
                .iter()
                .position(|c| leading_variable(&c.p) == Some(variable));
            let congruence = match dvd {
                None => (0, 1),
                Some(id) => {
                    let row = &constraints.dvd[id];
                    match solve_congruence(row, variable, &values)? {
                        Some(congruence) => congruence,
                        None => {
                            let a = row.p.coeffs.get(variable);
                            let g = gcd(abs(a)?, row.divisor);
                            let projected = without_variable(&row.p, variable);
                            let (d, _) = dag.derive(
                                Derivation::DvdDrop {
                                    divisibility: row.derivation,
                                    variable,
                                },
                                || DerivedConstraint::Dvd {
                                    divisor: g,
                                    affine: projected.clone(),
                                },
                            );
                            stats.projections += 1;
                            stats.derived_constraints += 1;
                            if !insert_dvd(&mut constraints, dag, stats, g, projected, d)? {
                                return Ok(resource(
                                    &constraints,
                                    values,
                                    ResourceReason::RepeatedConflict,
                                    *stats,
                                ));
                            }
                            continue 'restart;
                        }
                    }
                }
            };

            let excluded: Vec<(usize, Option<Z>)> = constraints
                .ne
                .iter()
                .enumerate()
                .filter(|(_, c)| leading_variable(&c.p) == Some(variable))
                .map(|(id, c)| Ok((id, excluded_value(&c.p, variable, &values)?)))
                .collect::<Result<_, Failure>>()?;
            match choose_value(lower.map(|b| b.value), upper.map(|b| b.value), congruence, &excluded)? {
                Choice::Value(value) => {
                    values.push(value);
                    stats.assignments += 1;
                }
                Choice::Blocked(blocked) => {
                    let blocked = match blocked {
                        None => Blocked::Cooper {
                            lower: lower.expect("an empty range has a lower bound").constraint,
                            upper: upper.expect("an empty range has an upper bound").constraint,
                            divisibility: dvd,
                        },
                        Some(ne) => Blocked::Diseq(ne),
                    };
                    return split(constraints, blocked, variable, scope, dag, limits, stats);
                }
            }
        }
        if !valid_model(&constraints, &values)? {
            return Err(Failure::InvalidConstraint {
                detail: format!("CutSat constructed an invalid model: {values:?}"),
            });
        }
        return Ok(Outcome::Model {
            values,
            stats: *stats,
        });
    }
}

fn split(
    constraints: Constraints,
    blocked: Blocked,
    variable: usize,
    scope: usize,
    dag: &mut DerivationDag,
    limits: Limits,
    stats: &mut Stats,
) -> Result<Outcome, Failure> {
    match blocked {
        Blocked::Diseq(ne) => {
            if stats.cases.saturating_add(2) > limits.max_cases {
                return Ok(resource(&constraints, Vec::new(), ResourceReason::CaseLimit, *stats));
            }
            stats.splits += 1;
            let removed = constraints.ne[ne].clone();
            let mut cases = Vec::with_capacity(2);
            for side in [1, -1] {
                stats.cases += 1;
                let case_scope = dag.open_scope(scope);
                let bound = removed.p.checked_scale(side)?.checked_add(&Affine::constant(1))?;
                let hypothesis = dag.push_in(
                    Derivation::Hypothesis { scope: case_scope },
                    DerivedConstraint::Le(bound.clone()),
                    case_scope,
                );
                let mut branch = constraints.clone();
                branch.ne.remove(ne);
                insert_le(&mut branch, dag, stats, bound, hypothesis)?;
                match search(branch, case_scope, dag, limits, stats)? {
                    Outcome::Contradiction { root, .. } => cases.push(SplitCase {
                        scope: case_scope,
                        hypothesis,
                        contradiction: root,
                    }),
                    other => return Ok(other),
                }
            }
            let above = cases.pop().expect("two cases");
            let below = cases.pop().expect("two cases");
            let root = dag.push_in(
                Derivation::DiseqSplit {
                    diseq: removed.derivation,
                    below,
                    above,
                },
                DerivedConstraint::False,
                scope,
            );
            Ok(contradiction(root, dag, *stats))
        }
        Blocked::Cooper {
            lower: lower_id,
            upper: upper_id,
            divisibility,
        } => {
            let lower = constraints.le[lower_id].clone();
            let upper = constraints.le[upper_id].clone();
            let carried = divisibility.map(|id| constraints.dvd[id].clone());
            let a = abs(lower.p.coeffs.get(variable))?;
            let b = upper.p.coeffs.get(variable);
            debug_assert!(lower.p.coeffs.get(variable) < 0 && b > 0);
            let left = a < b;
            let selected = if left { a } else { b };
            let (d, c) = carried
                .as_ref()
                .map(|row| (row.divisor, row.p.coeffs.get(variable)))
                .unwrap_or((1, 0));
            let period = cooper_period(selected, d, c)?;
            if stats
                .cases
                .saturating_add(usize::try_from(period).unwrap_or(usize::MAX))
                > limits.max_cases
            {
                return Ok(resource(&constraints, Vec::new(), ResourceReason::CaseLimit, *stats));
            }
            stats.splits += 1;
            let p = without_variable(&lower.p, variable);
            let q = without_variable(&upper.p, variable);
            let s = carried
                .as_ref()
                .map(|row| without_variable(&row.p, variable))
                .unwrap_or_default();
            let base = p.checked_scale(b)?.checked_add(&q.checked_scale(a)?)?;
            let mut cases = Vec::new();
            for k in 0..period {
                stats.cases += 1;
                let case_scope = dag.open_scope(scope);
                let shift = if left { mul(b, k)? } else { mul(a, k)? };
                let cut = base.checked_add(&Affine::constant(shift))?;
                let selected_row = if left { &p } else { &q }.checked_add(&Affine::constant(k))?;
                let carried_row = if left {
                    p.checked_scale(c)?
                        .checked_add(&s.checked_scale(a)?)?
                        .checked_add(&Affine::constant(mul(c, k)?))?
                } else {
                    q.checked_scale(neg(c)?)?
                        .checked_add(&s.checked_scale(b)?)?
                        .checked_add(&Affine::constant(neg(mul(c, k)?)?))?
                };
                let carried_divisor = mul(selected, d)?;
                let cut_id = dag.push_in(
                    Derivation::Hypothesis { scope: case_scope },
                    DerivedConstraint::Le(cut.clone()),
                    case_scope,
                );
                let selected_id = dag.push_in(
                    Derivation::Hypothesis { scope: case_scope },
                    DerivedConstraint::Dvd {
                        divisor: selected,
                        affine: selected_row.clone(),
                    },
                    case_scope,
                );
                let carried_id = carried.as_ref().map(|_| {
                    dag.push_in(
                        Derivation::Hypothesis { scope: case_scope },
                        DerivedConstraint::Dvd {
                            divisor: carried_divisor,
                            affine: carried_row.clone(),
                        },
                        case_scope,
                    )
                });
                let mut branch = constraints.clone();
                insert_le(&mut branch, dag, stats, cut, cut_id)?;
                insert_dvd(&mut branch, dag, stats, selected, selected_row, selected_id)?;
                if let Some(id) = carried_id {
                    insert_dvd(&mut branch, dag, stats, carried_divisor, carried_row, id)?;
                }
                stats.derived_constraints += 2 + usize::from(carried_id.is_some());
                match search(branch, case_scope, dag, limits, stats)? {
                    Outcome::Contradiction { root, .. } => cases.push(CooperCase {
                        scope: case_scope,
                        cut: cut_id,
                        selected: selected_id,
                        carried: carried_id,
                        contradiction: root,
                    }),
                    other => return Ok(other),
                }
            }
            let root = dag.push_in(
                Derivation::Cooper {
                    lower: lower.derivation,
                    upper: upper.derivation,
                    divisibility: carried.map(|row| row.derivation),
                    variable,
                    left,
                    period,
                    cases,
                },
                DerivedConstraint::False,
                scope,
            );
            Ok(contradiction(root, dag, *stats))
        }
    }
}

/// The number of Cooper cases: a multiple of the selected coefficient
/// `selected` such that `selected·d` divides `c` times it.
pub(crate) fn cooper_period(selected: Z, d: Z, c: Z) -> Result<Z, Failure> {
    let scaled = mul(selected, d)?;
    lcm(selected, scaled / gcd(scaled, abs(c)?))
}

fn contradiction(root: usize, dag: &DerivationDag, stats: Stats) -> Outcome {
    Outcome::Contradiction {
        root,
        reachable: dag.reachable(root),
        stats,
    }
}

fn resource(constraints: &Constraints, partial_model: Vec<Z>, reason: ResourceReason, stats: Stats) -> Outcome {
    Outcome::ResourceLimit {
        partial_model,
        residual: constraints.residual(),
        reason,
        stats,
    }
}

pub(crate) fn leading_variable(p: &Affine) -> Option<usize> {
    p.coeffs.as_slice().iter().rposition(|c| *c != 0)
}

pub(crate) fn without_variable(p: &Affine, variable: usize) -> Affine {
    Affine {
        constant: p.constant,
        coeffs: p.coeffs.with_coefficient(variable, 0),
    }
}

fn eval_assigned(p: &Affine, values: &[Z]) -> Result<Z, Failure> {
    values
        .iter()
        .enumerate()
        .try_fold(p.constant, |out, (i, value)| add(out, mul(p.coeffs.get(i), *value)?))
}

fn valid_model(constraints: &Constraints, values: &[Z]) -> Result<bool, Failure> {
    for c in &constraints.le {
        if eval_assigned(&c.p, values)? > 0 {
            return Ok(false);
        }
    }
    for c in &constraints.dvd {
        if eval_assigned(&c.p, values)?.rem_euclid(c.divisor) != 0 {
            return Ok(false);
        }
    }
    for c in &constraints.ne {
        if eval_assigned(&c.p, values)? == 0 {
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

/// Whether `lower` (coefficient `-a`) and `upper` (coefficient `b`) cross
/// over the reals at the assigned values.
fn rational_conflict(lower: &Affine, upper: &Affine, values: &[Z]) -> Result<bool, Failure> {
    let a = neg(lower.coeffs.get(values.len()))?;
    let b = upper.coeffs.get(values.len());
    Ok(add(mul(eval_assigned(lower, values)?, b)?, mul(eval_assigned(upper, values)?, a)?)? > 0)
}

fn real_projection(lower: &Affine, upper: &Affine, variable: usize) -> Result<Affine, Failure> {
    let a = neg(lower.coeffs.get(variable))?;
    let b = upper.coeffs.get(variable);
    without_variable(lower, variable)
        .checked_scale(b)?
        .checked_add(&without_variable(upper, variable).checked_scale(a)?)
}

/// The congruence `x ≡ residue (mod modulus)` a divisibility leaves for its
/// leading variable, or `None` when it has no solution.
fn solve_congruence(c: &DvdRow, variable: usize, values: &[Z]) -> Result<Option<(Z, Z)>, Failure> {
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
    let rhs = neg(tail / g)?.rem_euclid(modulus);
    let inverse = modular_inverse((a / g).rem_euclid(modulus), modulus)?.ok_or(Failure::InvalidConstraint {
        detail: "reduced congruence was not invertible".into(),
    })?;
    Ok(Some((mul(rhs, inverse)?.rem_euclid(modulus), modulus)))
}

/// The one value of the leading variable that makes `p` zero, if integral.
fn excluded_value(p: &Affine, variable: usize, values: &[Z]) -> Result<Option<Z>, Failure> {
    let a = p.coeffs.get(variable);
    let tail = eval_assigned(p, values)?;
    Ok((tail.rem_euclid(abs(a)?) == 0).then(|| neg(tail).map(|t| t / a)).transpose()?)
}

enum Choice {
    Value(Z),
    /// No value: `None` when the bounds and congruence leave none at all,
    /// otherwise the disequality excluding the first candidate.
    Blocked(Option<usize>),
}

/// The least admissible value at or above `lower` (or the greatest at or
/// below `upper` when there is no lower bound), skipping excluded values.
fn choose_value(
    lower: Option<Z>,
    upper: Option<Z>,
    (residue, modulus): (Z, Z),
    excluded: &[(usize, Option<Z>)],
) -> Result<Choice, Failure> {
    let (mut candidate, step) = if let Some(lower) = lower {
        let offset = add(residue, neg(lower)?)?.rem_euclid(modulus);
        (add(lower, offset)?, modulus)
    } else if let Some(upper) = upper {
        let offset = add(upper, neg(residue)?)?.rem_euclid(modulus);
        (add(upper, neg(offset)?)?, neg(modulus)?)
    } else {
        (residue, modulus)
    };
    let in_range = |value: Z| lower.is_none_or(|l| value >= l) && upper.is_none_or(|u| value <= u);
    if !in_range(candidate) {
        return Ok(Choice::Blocked(None));
    }
    let mut first_blocker = None;
    // Each disequality excludes at most one value, so one more candidate than
    // there are disequalities is enough.
    for _ in 0..=excluded.len() {
        match excluded.iter().find(|(_, value)| *value == Some(candidate)) {
            None => return Ok(Choice::Value(candidate)),
            Some((id, _)) => {
                first_blocker.get_or_insert(*id);
            }
        }
        candidate = add(candidate, step)?;
        if !in_range(candidate) {
            break;
        }
    }
    Ok(Choice::Blocked(first_blocker))
}

pub(crate) fn gcd(mut a: Z, mut b: Z) -> Z {
    a = a.abs();
    b = b.abs();
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
    abs(mul(a / gcd(a, b), b)?)
}

/// `(g, u, v)` with `g = gcd(a, b) = u·a + v·b`.
pub(crate) fn extended_gcd(a: Z, b: Z) -> Result<(Z, Z, Z), Failure> {
    let (mut old_r, mut r) = (a, b);
    let (mut old_s, mut s) = (1, 0);
    let (mut old_t, mut t) = (0, 1);
    while r != 0 {
        let q = old_r.div_euclid(r);
        (old_r, r) = (r, add(old_r, neg(mul(q, r)?)?)?);
        (old_s, s) = (s, add(old_s, neg(mul(q, s)?)?)?);
        (old_t, t) = (t, add(old_t, neg(mul(q, t)?)?)?);
    }
    if old_r < 0 {
        Ok((neg(old_r)?, neg(old_s)?, neg(old_t)?))
    } else {
        Ok((old_r, old_s, old_t))
    }
}

fn modular_inverse(a: Z, modulus: Z) -> Result<Option<Z>, Failure> {
    let (g, u, _) = extended_gcd(a, modulus)?;
    Ok((g == 1).then(|| u.rem_euclid(modulus)))
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

    fn contradicts(problem: Problem) -> bool {
        match problem.solve(Limits::default()).unwrap().1 {
            Outcome::Contradiction { .. } => true,
            Outcome::Model { .. } => false,
            Outcome::ResourceLimit { reason, .. } => panic!("CutSat stopped: {reason:?}"),
        }
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
        assert!(contradicts(problem));
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
            .assume(Affine::constant(1), Relation::Le, Affine::atom(1))
            .unwrap();
        assert!(contradicts(problem));
    }

    #[test]
    fn closes_pughs_nightmare() {
        let mut problem = Problem::new();
        add_interval(&mut problem, &[11, 13], 27, 45);
        add_interval(&mut problem, &[7, -9], -10, 4);
        add_interval(&mut problem, &[1, 0], -16, 16);
        add_interval(&mut problem, &[0, 1], -16, 16);
        let (problem, outcome) = problem.solve(Limits::default()).unwrap();
        let Outcome::Contradiction { stats, reachable, .. } = &outcome else {
            panic!("{outcome:?}")
        };
        assert!(stats.splits > 0);
        // Every reachable node is written in a scope its premises are visible from.
        let dag = problem.derivations();
        for &id in reachable {
            let scope = dag.scope_of(id);
            for premise in dag.nodes()[id].premises() {
                let mut visible = scope;
                let target = dag.scope_of(premise);
                while visible != target {
                    visible = dag.scopes()[visible]
                        .parent
                        .unwrap_or_else(|| panic!("node {id} sees premise {premise} out of scope"));
                }
            }
        }
    }

    #[test]
    fn several_congruences_on_one_variable_combine() {
        // 4 ∣ x + y, 6 ∣ x + 2y, 0 <= x, y <= 5: the combination leaves solutions.
        let mut problem = Problem::new();
        problem.assume_dvd(4, row(&[1, 1]), 0).unwrap();
        problem.assume_dvd(6, row(&[1, 2]), 1).unwrap();
        add_interval(&mut problem, &[1, 0], 0, 5);
        add_interval(&mut problem, &[0, 1], 0, 5);
        let (_, outcome) = problem.solve(Limits::default()).unwrap();
        let Outcome::Model { values, .. } = outcome else {
            panic!("{outcome:?}")
        };
        assert_eq!((values[0] + values[1]) % 4, 0);
        assert_eq!((values[0] + 2 * values[1]) % 6, 0);

        // 2 ∣ x + y and 2 ∣ x + y + 1 cannot both hold.
        let mut problem = Problem::new();
        problem.assume_dvd(2, row(&[1, 1]), 0).unwrap();
        problem
            .assume_dvd(2, row(&[1, 1]).checked_add(&Affine::constant(1)).unwrap(), 1)
            .unwrap();
        assert!(contradicts(problem));
    }

    #[test]
    fn disequalities_exclude_values_and_split_when_cornered() {
        // 0 <= x <= 2, x ≠ 0, x ≠ 1, x ≠ 2.
        let mut problem = Problem::new();
        add_interval(&mut problem, &[1], 0, 2);
        for value in 0..3 {
            problem
                .assume_ne(row(&[1]).checked_add(&Affine::constant(-value)).unwrap(), 2 + value as usize)
                .unwrap();
        }
        assert!(contradicts(problem));

        // 0 <= x <= 2, x ≠ 0, x ≠ 2 leaves 1.
        let mut problem = Problem::new();
        add_interval(&mut problem, &[1], 0, 2);
        problem.assume_ne(row(&[1]), 2).unwrap();
        problem
            .assume_ne(row(&[1]).checked_add(&Affine::constant(-2)).unwrap(), 3)
            .unwrap();
        let (_, outcome) = problem.solve(Limits::default()).unwrap();
        assert!(matches!(outcome, Outcome::Model { values, .. } if values == vec![1]));
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
                        if *lower { *bound <= value } else { value <= *bound }
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

    /// Three variables with inequalities, divisibilities and disequalities,
    /// against enumeration of the box.
    #[test]
    fn seeded_mixed_systems_agree_with_enumeration() {
        fn next(state: &mut u64) -> u64 {
            *state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            *state >> 17
        }
        enum Fact {
            Le(Vec<Z>, Z),
            Dvd(Z, Vec<Z>, Z),
            Ne(Vec<Z>, Z),
        }
        let (mut models, mut contradictions) = (0usize, 0usize);
        for seed in 0..4_000u64 {
            let mut state = seed ^ 0x5eed;
            let mut facts = Vec::new();
            let mut problem = Problem::new();
            for index in 0..5 {
                let coefficients: Vec<Z> = (0..3).map(|_| (next(&mut state) % 9) as Z - 4).collect();
                let constant = (next(&mut state) % 13) as Z - 6;
                let p = row(&coefficients).checked_add(&Affine::constant(constant)).unwrap();
                match next(&mut state) % 4 {
                    0 | 1 => {
                        problem.assume_le(p, index).unwrap();
                        facts.push(Fact::Le(coefficients, constant));
                    }
                    2 => {
                        let divisor = (next(&mut state) % 5) as Z + 2;
                        problem.assume_dvd(divisor, p, index).unwrap();
                        facts.push(Fact::Dvd(divisor, coefficients, constant));
                    }
                    _ => {
                        problem.assume_ne(p, index).unwrap();
                        facts.push(Fact::Ne(coefficients, constant));
                    }
                }
            }
            for variable in 0..3 {
                let mut unit = vec![0; 3];
                unit[variable] = 1;
                add_interval(&mut problem, &unit, -3, 3);
            }
            let holds = |point: &[Z]| {
                facts.iter().all(|fact| {
                    let value = |c: &[Z], k: Z| c.iter().zip(point).map(|(c, x)| c * x).sum::<Z>() + k;
                    match fact {
                        Fact::Le(c, k) => value(c, *k) <= 0,
                        Fact::Dvd(d, c, k) => value(c, *k).rem_euclid(*d) == 0,
                        Fact::Ne(c, k) => value(c, *k) != 0,
                    }
                })
            };
            let exhaustive = (-3..=3).any(|x| (-3..=3).any(|y| (-3..=3).any(|z| holds(&[x, y, z]))));
            match problem.solve(Limits::default()).unwrap().1 {
                Outcome::Model { mut values, .. } => {
                    values.resize(3, 0);
                    assert!(holds(&values), "invalid model at seed {seed}: {values:?}");
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
        assert!(models > 0 && contradictions > 0, "{models} {contradictions}");
    }
}
