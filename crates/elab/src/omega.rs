//! Arithmetic core for the certifying Omega-style solver.
//!
//! This module deliberately contains no kernel or surface-language objects.
//! It is the deterministic, testable search layer: callers reflect Heather
//! terms into [`Fact`]s and, when [`Problem::solve`] finds a contradiction,
//! replay the returned derivation DAG into an ordinary proof term.  Keeping
//! search and reconstruction separate is what lets failed searches stay cheap
//! and lets successful certificates share every derived fact.

use std::collections::BTreeMap;
use std::fmt;

/// Checked arithmetic used by the first implementation slice.
///
/// Source numerals are currently machine sized, but elimination can grow
/// coefficients.  Every operation below is checked; exceeding this temporary
/// bound is a structured refusal, never a wrapped (and potentially unsound)
/// solver result.
pub type Z = i128;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Failure {
    Overflow { operation: &'static str },
    InvalidConstraint { detail: String },
}

impl fmt::Display for Failure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Overflow { operation } => {
                write!(f, "Omega coefficient overflow while {operation}")
            }
            Self::InvalidConstraint { detail } => write!(f, "invalid Omega constraint: {detail}"),
        }
    }
}

type R<T> = Result<T, Failure>;

fn add(a: Z, b: Z) -> R<Z> {
    a.checked_add(b).ok_or(Failure::Overflow {
        operation: "adding coefficients",
    })
}

fn mul(a: Z, b: Z) -> R<Z> {
    a.checked_mul(b).ok_or(Failure::Overflow {
        operation: "multiplying coefficients",
    })
}

fn neg(a: Z) -> R<Z> {
    a.checked_neg().ok_or(Failure::Overflow {
        operation: "negating a coefficient",
    })
}

fn abs(a: Z) -> R<Z> {
    a.checked_abs().ok_or(Failure::Overflow {
        operation: "taking a coefficient magnitude",
    })
}

fn gcd(mut a: Z, mut b: Z) -> Z {
    debug_assert!(a >= 0 && b >= 0);
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

fn floor_div(a: Z, positive: Z) -> Z {
    debug_assert!(positive > 0);
    a.div_euclid(positive)
}

fn ceil_div(a: Z, positive: Z) -> R<Z> {
    debug_assert!(positive > 0);
    neg(floor_div(neg(a)?, positive))
}

/// Centered quotient/remainder with `a = remainder + modulus * quotient`.
/// Ties are kept on the negative side, matching the balanced-remainder step
/// that turns a coefficient of magnitude `modulus - 1` into `±1`.
fn balanced_div_rem(a: Z, modulus: Z) -> R<(Z, Z)> {
    debug_assert!(modulus > 0);
    let quotient = a.div_euclid(modulus);
    let remainder = a.rem_euclid(modulus);
    if mul(2, remainder)? < modulus {
        Ok((quotient, remainder))
    } else {
        Ok((add(quotient, 1)?, add(remainder, neg(modulus)?)?))
    }
}

/// Dense signed coefficients, with trailing zeroes removed.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Coeffs(Vec<Z>);

impl Coeffs {
    pub fn new(mut values: Vec<Z>) -> Self {
        while values.last() == Some(&0) {
            values.pop();
        }
        Self(values)
    }

    pub fn as_slice(&self) -> &[Z] {
        &self.0
    }

    pub fn get(&self, index: usize) -> Z {
        self.0.get(index).copied().unwrap_or(0)
    }

    pub fn is_zero(&self) -> bool {
        self.0.is_empty()
    }

    fn leading(&self) -> Z {
        self.0.iter().copied().find(|&c| c != 0).unwrap_or(0)
    }

    fn coefficient_gcd(&self) -> R<Z> {
        self.0.iter().try_fold(0, |out, &c| Ok(gcd(out, abs(c)?)))
    }

    fn min_abs(&self) -> R<Option<Z>> {
        self.0
            .iter()
            .copied()
            .filter(|coefficient| *coefficient != 0)
            .try_fold(None, |best, coefficient| {
                let coefficient = abs(coefficient)?;
                Ok(Some(
                    best.map_or(coefficient, |old: Z| old.min(coefficient)),
                ))
            })
    }

    fn max_abs(&self) -> R<Option<Z>> {
        self.0
            .iter()
            .copied()
            .filter(|coefficient| *coefficient != 0)
            .try_fold(None, |best, coefficient| {
                let coefficient = abs(coefficient)?;
                Ok(Some(
                    best.map_or(coefficient, |old: Z| old.max(coefficient)),
                ))
            })
    }

    fn balanced(&self, modulus: Z) -> R<(Self, Self)> {
        let pairs = self
            .0
            .iter()
            .copied()
            .map(|coefficient| balanced_div_rem(coefficient, modulus))
            .collect::<R<Vec<_>>>()?;
        Ok((
            Self::new(pairs.iter().map(|(_, remainder)| *remainder).collect()),
            Self::new(pairs.iter().map(|(quotient, _)| *quotient).collect()),
        ))
    }

    fn with_coefficient(&self, index: usize, coefficient: Z) -> Self {
        let mut values = self.0.clone();
        values.resize(index + 1, 0);
        values[index] = coefficient;
        Self::new(values)
    }

    fn scale(&self, k: Z) -> R<Self> {
        self.0
            .iter()
            .map(|&c| mul(k, c))
            .collect::<R<Vec<_>>>()
            .map(Self::new)
    }

    fn exact_div(&self, divisor: Z) -> R<Self> {
        debug_assert!(divisor > 0);
        if self.0.iter().any(|c| c % divisor != 0) {
            return Err(Failure::InvalidConstraint {
                detail: "coefficient GCD did not divide every coefficient".into(),
            });
        }
        Ok(Self::new(self.0.iter().map(|c| c / divisor).collect()))
    }

    fn combo(a: Z, x: &Self, b: Z, y: &Self) -> R<Self> {
        let len = x.0.len().max(y.0.len());
        (0..len)
            .map(|i| add(mul(a, x.get(i))?, mul(b, y.get(i))?))
            .collect::<R<Vec<_>>>()
            .map(Self::new)
    }
}

/// A reflected affine expression `constant + sum(coeff[i] * atom[i])`.
///
/// Atom identity is owned by the elaborator frontend. Keeping only dense atom
/// indices here means the solver never inspects, reduces, or compares Heather
/// terms during search.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct LinearExpr {
    pub constant: Z,
    pub coeffs: Coeffs,
}

impl LinearExpr {
    pub fn constant(value: Z) -> Self {
        Self {
            constant: value,
            coeffs: Coeffs::default(),
        }
    }

    pub fn atom(index: usize) -> Self {
        let mut coeffs = vec![0; index + 1];
        coeffs[index] = 1;
        Self {
            constant: 0,
            coeffs: Coeffs::new(coeffs),
        }
    }

    pub fn checked_add(&self, other: &Self) -> R<Self> {
        Ok(Self {
            constant: add(self.constant, other.constant)?,
            coeffs: Coeffs::combo(1, &self.coeffs, 1, &other.coeffs)?,
        })
    }

    pub fn checked_sub(&self, other: &Self) -> R<Self> {
        Ok(Self {
            constant: add(self.constant, neg(other.constant)?)?,
            coeffs: Coeffs::combo(1, &self.coeffs, -1, &other.coeffs)?,
        })
    }

    pub fn checked_scale(&self, factor: Z) -> R<Self> {
        Ok(Self {
            constant: mul(factor, self.constant)?,
            coeffs: self.coeffs.scale(factor)?,
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Relation {
    Eq,
    Le,
    Lt,
    Ge,
    Gt,
}

/// Inclusive lower and upper bounds on the dot product of a coefficient
/// vector and the reflected atoms.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Interval {
    pub lower: Option<Z>,
    pub upper: Option<Z>,
}

impl Interval {
    pub const TRIVIAL: Self = Self {
        lower: None,
        upper: None,
    };

    pub fn lower(value: Z) -> Self {
        Self {
            lower: Some(value),
            upper: None,
        }
    }

    pub fn upper(value: Z) -> Self {
        Self {
            lower: None,
            upper: Some(value),
        }
    }

    pub fn exact(value: Z) -> Self {
        Self {
            lower: Some(value),
            upper: Some(value),
        }
    }

    pub fn bounded(lower: Z, upper: Z) -> Self {
        Self {
            lower: Some(lower),
            upper: Some(upper),
        }
    }

    pub fn is_impossible(self) -> bool {
        matches!((self.lower, self.upper), (Some(l), Some(u)) if u < l)
    }

    pub fn is_exact(self) -> bool {
        matches!((self.lower, self.upper), (Some(l), Some(u)) if l == u)
    }

    fn contains(self, value: Z) -> bool {
        self.lower.is_none_or(|l| l <= value) && self.upper.is_none_or(|u| value <= u)
    }

    fn intersect(self, other: Self) -> Self {
        Self {
            lower: match (self.lower, other.lower) {
                (Some(a), Some(b)) => Some(a.max(b)),
                (a, b) => a.or(b),
            },
            upper: match (self.upper, other.upper) {
                (Some(a), Some(b)) => Some(a.min(b)),
                (a, b) => a.or(b),
            },
        }
    }

    fn scale(self, k: Z) -> R<Self> {
        if k == 0 {
            return Ok(if self.is_impossible() {
                self
            } else {
                Self::exact(0)
            });
        }
        if k > 0 {
            Ok(Self {
                lower: self.lower.map(|x| mul(k, x)).transpose()?,
                upper: self.upper.map(|x| mul(k, x)).transpose()?,
            })
        } else {
            Ok(Self {
                lower: self.upper.map(|x| mul(k, x)).transpose()?,
                upper: self.lower.map(|x| mul(k, x)).transpose()?,
            })
        }
    }

    fn add(self, other: Self) -> R<Self> {
        Ok(Self {
            lower: match (self.lower, other.lower) {
                (Some(a), Some(b)) => Some(add(a, b)?),
                _ => None,
            },
            upper: match (self.upper, other.upper) {
                (Some(a), Some(b)) => Some(add(a, b)?),
                _ => None,
            },
        })
    }

    fn divide(self, divisor: Z) -> R<Self> {
        debug_assert!(divisor > 0);
        Ok(Self {
            lower: self.lower.map(|x| ceil_div(x, divisor)).transpose()?,
            upper: self.upper.map(|x| Ok(floor_div(x, divisor))).transpose()?,
        })
    }

    fn shift(self, amount: Z) -> R<Self> {
        Ok(Self {
            lower: self.lower.map(|value| add(value, amount)).transpose()?,
            upper: self.upper.map(|value| add(value, amount)).transpose()?,
        })
    }

    fn combo(a: Z, x: Self, b: Z, y: Self) -> R<Self> {
        x.scale(a)?.add(y.scale(b)?)
    }
}

pub type DerivationId = usize;

/// One node in the eventual proof certificate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Derivation {
    Assumption {
        index: usize,
    },
    Positivize {
        parent: DerivationId,
    },
    DivideGcd {
        parent: DerivationId,
        divisor: Z,
    },
    Balanced {
        parent: DerivationId,
        modulus: Z,
        fresh: usize,
    },
    Constant {
        parent: DerivationId,
        impossible: bool,
    },
    Intersect {
        left: DerivationId,
        right: DerivationId,
    },
    Combo {
        left: DerivationId,
        left_scale: Z,
        right: DerivationId,
        right_scale: Z,
    },
}

#[derive(Debug, Clone, Default)]
pub struct DerivationDag {
    nodes: Vec<Derivation>,
}

impl DerivationDag {
    pub fn nodes(&self) -> &[Derivation] {
        &self.nodes
    }

    fn push(&mut self, node: Derivation) -> DerivationId {
        let id = self.nodes.len();
        self.nodes.push(node);
        id
    }

    /// Return the topological, duplicate-free slice needed for one result.
    pub fn reachable(&self, root: DerivationId) -> Vec<DerivationId> {
        fn visit(dag: &DerivationDag, id: DerivationId, seen: &mut [bool], out: &mut Vec<usize>) {
            if seen[id] {
                return;
            }
            seen[id] = true;
            match dag.nodes[id] {
                Derivation::Assumption { .. } => {}
                Derivation::Positivize { parent }
                | Derivation::DivideGcd { parent, .. }
                | Derivation::Balanced { parent, .. }
                | Derivation::Constant { parent, .. } => visit(dag, parent, seen, out),
                Derivation::Intersect { left, right } | Derivation::Combo { left, right, .. } => {
                    visit(dag, left, seen, out);
                    visit(dag, right, seen, out);
                }
            }
            out.push(id);
        }

        let mut seen = vec![false; self.nodes.len()];
        let mut out = Vec::new();
        visit(self, root, &mut seen, &mut out);
        out
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Fact {
    pub coeffs: Coeffs,
    pub interval: Interval,
    pub derivation: DerivationId,
}

impl Fact {
    pub fn assumption(
        coeffs: Vec<Z>,
        interval: Interval,
        assumption: usize,
        dag: &mut DerivationDag,
    ) -> Self {
        Self {
            coeffs: Coeffs::new(coeffs),
            interval,
            derivation: dag.push(Derivation::Assumption { index: assumption }),
        }
    }

    fn combo(a: Z, x: &Self, b: Z, y: &Self, dag: &mut DerivationDag) -> R<Self> {
        Ok(Self {
            coeffs: Coeffs::combo(a, &x.coeffs, b, &y.coeffs)?,
            interval: Interval::combo(a, x.interval, b, y.interval)?,
            derivation: dag.push(Derivation::Combo {
                left: x.derivation,
                left_scale: a,
                right: y.derivation,
                right_scale: b,
            }),
        })
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Stats {
    pub inserted: usize,
    pub intersections: usize,
    pub positivizations: usize,
    pub gcd_divisions: usize,
    pub equality_eliminations: usize,
    pub hard_equality_splits: usize,
    pub fresh_variables: usize,
    pub fourier_motzkin_eliminations: usize,
    pub exact_eliminations: usize,
    pub combinations: usize,
}

#[derive(Debug, Clone)]
pub enum Outcome {
    Contradiction {
        derivation: DerivationId,
        reachable_derivations: Vec<DerivationId>,
        stats: Stats,
    },
    NoContradiction {
        /// The normalized real-shadow frontier at which search stopped, or
        /// the last nonempty frontier before projection erased the final
        /// variable. It is diagnostic state, not a model and not a
        /// satisfiability claim.
        residual: Vec<Fact>,
        stats: Stats,
    },
}

#[derive(Debug, Clone, Default)]
pub struct Problem {
    constraints: BTreeMap<Coeffs, Fact>,
    assumptions: Vec<(Coeffs, Interval)>,
    pub dag: DerivationDag,
    stats: Stats,
    contradiction: Option<DerivationId>,
    skip_gcd_reduction: bool,
    num_vars: usize,
    base_vars: Option<usize>,
    fresh_projections: Vec<(Coeffs, Z)>,
}

impl Problem {
    pub fn new() -> Self {
        Self::default()
    }

    /// Keep coefficient rows integral but non-primitive. This is a diagnostic
    /// opt-out for comparing search behavior; certificate frontends normally
    /// reconstruct [`Derivation::DivideGcd`] and retain the optimization.
    pub fn without_gcd_reduction(mut self) -> Self {
        self.skip_gcd_reduction = true;
        self
    }

    pub fn assume(&mut self, coeffs: Vec<Z>, interval: Interval) -> R<()> {
        let coeffs = Coeffs::new(coeffs);
        self.num_vars = self.num_vars.max(coeffs.as_slice().len());
        let index = self.assumptions.len();
        self.assumptions.push((coeffs.clone(), interval));
        let fact = Fact::assumption(coeffs.0, interval, index, &mut self.dag);
        self.insert(fact)
    }

    /// Lower a reflected relation between affine integer expressions.
    pub fn assume_relation(
        &mut self,
        lhs: &LinearExpr,
        relation: Relation,
        rhs: &LinearExpr,
    ) -> R<()> {
        let difference = lhs.checked_sub(rhs)?;
        let zero_bound = neg(difference.constant)?;
        let interval = match relation {
            Relation::Eq => Interval::exact(zero_bound),
            Relation::Le => Interval::upper(zero_bound),
            Relation::Lt => Interval::upper(add(zero_bound, -1)?),
            Relation::Ge => Interval::lower(zero_bound),
            Relation::Gt => Interval::lower(add(zero_bound, 1)?),
        };
        self.assume(difference.coeffs.0, interval)
    }

    pub fn assumptions(&self) -> &[(Coeffs, Interval)] {
        &self.assumptions
    }

    pub fn constraints(&self) -> impl Iterator<Item = &Fact> {
        self.constraints.values()
    }

    fn project_coeffs(&self, coeffs: &Coeffs) -> R<(Coeffs, Z)> {
        let Some(base_vars) = self.base_vars else {
            return Ok((coeffs.clone(), 0));
        };
        if coeffs.as_slice().len() > base_vars + self.fresh_projections.len() {
            return Err(Failure::InvalidConstraint {
                detail: "coefficient row mentions an unrecorded fresh variable".into(),
            });
        }
        let mut projected =
            Coeffs::new(coeffs.as_slice()[..coeffs.as_slice().len().min(base_vars)].to_vec());
        let mut constant = 0;
        for (offset, (row, value)) in self.fresh_projections.iter().enumerate() {
            let coefficient = coeffs.get(base_vars + offset);
            if coefficient == 0 {
                continue;
            }
            projected = Coeffs::combo(1, &projected, coefficient, row)?;
            constant = add(constant, mul(coefficient, *value)?)?;
        }
        Ok((projected, constant))
    }

    /// Erase search-only fresh variables by substituting their recorded
    /// affine definitions over the original reflected atoms.
    pub fn project_fact(&self, fact: &Fact) -> R<Fact> {
        let (coeffs, constant) = self.project_coeffs(&fact.coeffs)?;
        Ok(Fact {
            coeffs,
            interval: fact.interval.shift(neg(constant)?)?,
            derivation: fact.derivation,
        })
    }

    /// Replay one derivation from the recorded assumptions.
    ///
    /// This is deliberately separate from search. It catches malformed DAG
    /// edges and records the exact normalized fact that a future Heather proof
    /// reconstructor must establish at every shared `let` binding.
    pub fn replay(&self, root: DerivationId) -> R<Fact> {
        if root >= self.dag.nodes.len() {
            return Err(Failure::InvalidConstraint {
                detail: format!("derivation {root} is outside the DAG"),
            });
        }
        let mut facts: Vec<Option<Fact>> = vec![None; root + 1];
        for id in self.dag.reachable(root) {
            let fact = match self.dag.nodes[id] {
                Derivation::Assumption { index } => {
                    let Some((coeffs, interval)) = self.assumptions.get(index) else {
                        return Err(Failure::InvalidConstraint {
                            detail: format!("assumption {index} is not recorded"),
                        });
                    };
                    Fact {
                        coeffs: coeffs.clone(),
                        interval: *interval,
                        derivation: id,
                    }
                }
                Derivation::Positivize { parent } => {
                    let parent = replay_parent(&facts, parent, id)?;
                    Fact {
                        coeffs: parent.coeffs.scale(-1)?,
                        interval: parent.interval.scale(-1)?,
                        derivation: id,
                    }
                }
                Derivation::DivideGcd { parent, divisor } => {
                    if divisor <= 1 {
                        return Err(Failure::InvalidConstraint {
                            detail: format!("derivation {id} has invalid GCD divisor {divisor}"),
                        });
                    }
                    let parent = replay_parent(&facts, parent, id)?;
                    Fact {
                        coeffs: parent.coeffs.exact_div(divisor)?,
                        interval: parent.interval.divide(divisor)?,
                        derivation: id,
                    }
                }
                Derivation::Balanced {
                    parent,
                    modulus,
                    fresh,
                } => {
                    if modulus <= 1 {
                        return Err(Failure::InvalidConstraint {
                            detail: format!(
                                "derivation {id} has invalid balanced modulus {modulus}"
                            ),
                        });
                    }
                    let parent = replay_parent(&facts, parent, id)?;
                    let Some(value) = parent
                        .interval
                        .lower
                        .filter(|value| parent.interval.upper == Some(*value))
                    else {
                        return Err(Failure::InvalidConstraint {
                            detail: format!("derivation {id} balances a non-exact constraint"),
                        });
                    };
                    if fresh < parent.coeffs.as_slice().len() {
                        return Err(Failure::InvalidConstraint {
                            detail: format!("derivation {id} reuses existing variable {fresh}"),
                        });
                    }
                    let (remainders, _) = parent.coeffs.balanced(modulus)?;
                    let (_, remainder) = balanced_div_rem(value, modulus)?;
                    Fact {
                        coeffs: remainders.with_coefficient(fresh, modulus),
                        interval: Interval::exact(remainder),
                        derivation: id,
                    }
                }
                Derivation::Constant { parent, impossible } => {
                    let parent = replay_parent(&facts, parent, id)?;
                    if !parent.coeffs.is_zero() || impossible == parent.interval.contains(0) {
                        return Err(Failure::InvalidConstraint {
                            detail: format!("derivation {id} has an inconsistent constant result"),
                        });
                    }
                    Fact {
                        derivation: id,
                        ..parent.clone()
                    }
                }
                Derivation::Intersect { left, right } => {
                    let left = replay_parent(&facts, left, id)?;
                    let right = replay_parent(&facts, right, id)?;
                    if left.coeffs != right.coeffs {
                        return Err(Failure::InvalidConstraint {
                            detail: format!(
                                "derivation {id} intersects different coefficient rows"
                            ),
                        });
                    }
                    Fact {
                        coeffs: left.coeffs.clone(),
                        interval: left.interval.intersect(right.interval),
                        derivation: id,
                    }
                }
                Derivation::Combo {
                    left,
                    left_scale,
                    right,
                    right_scale,
                } => {
                    let left = replay_parent(&facts, left, id)?;
                    let right = replay_parent(&facts, right, id)?;
                    Fact::combo(
                        left_scale,
                        left,
                        right_scale,
                        right,
                        &mut DerivationDag::default(),
                    )?
                }
            };
            facts[id] = Some(Fact {
                derivation: id,
                ..fact
            });
        }
        facts[root].clone().ok_or(Failure::InvalidConstraint {
            detail: format!("derivation {root} was not reachable from itself"),
        })
    }

    fn tidy(&mut self, mut fact: Fact) -> R<Option<Fact>> {
        if fact.coeffs.is_zero() {
            let impossible = !fact.interval.contains(0);
            fact.derivation = self.dag.push(Derivation::Constant {
                parent: fact.derivation,
                impossible,
            });
            if impossible {
                fact.interval = Interval::exact(1).intersect(Interval::exact(0));
                return Ok(Some(fact));
            }
            return Ok(None);
        }

        if fact.coeffs.leading() < 0 {
            fact.coeffs = fact.coeffs.scale(-1)?;
            fact.interval = fact.interval.scale(-1)?;
            fact.derivation = self.dag.push(Derivation::Positivize {
                parent: fact.derivation,
            });
            self.stats.positivizations += 1;
        }

        if !self.skip_gcd_reduction {
            let divisor = fact.coeffs.coefficient_gcd()?;
            if divisor > 1 {
                fact.coeffs = fact.coeffs.exact_div(divisor)?;
                fact.interval = fact.interval.divide(divisor)?;
                fact.derivation = self.dag.push(Derivation::DivideGcd {
                    parent: fact.derivation,
                    divisor,
                });
                self.stats.gcd_divisions += 1;
            }
        }
        Ok(Some(fact))
    }

    fn insert(&mut self, fact: Fact) -> R<()> {
        if self.contradiction.is_some() {
            return Ok(());
        }
        let Some(mut fact) = self.tidy(fact)? else {
            return Ok(());
        };
        self.stats.inserted += 1;
        if fact.interval.is_impossible() {
            self.contradiction = Some(fact.derivation);
            return Ok(());
        }
        if let Some(old) = self.constraints.remove(&fact.coeffs) {
            let intersection = old.interval.intersect(fact.interval);
            let derivation = self.dag.push(Derivation::Intersect {
                left: old.derivation,
                right: fact.derivation,
            });
            self.stats.intersections += 1;
            fact.interval = intersection;
            fact.derivation = derivation;
            if intersection.is_impossible() {
                self.contradiction = Some(derivation);
                return Ok(());
            }
        }
        self.constraints.insert(fact.coeffs.clone(), fact);
        Ok(())
    }

    fn solve_easy_equality(&mut self) -> R<bool> {
        let equality = self.constraints.values().find_map(|f| {
            if !f.interval.is_exact() {
                return None;
            }
            f.coeffs
                .as_slice()
                .iter()
                .position(|c| c.unsigned_abs() == 1)
                .map(|var| (f.clone(), var))
        });
        let Some((equality, var)) = equality else {
            return Ok(false);
        };
        let sign = equality.coeffs.get(var);
        let old = std::mem::take(&mut self.constraints);
        self.stats.equality_eliminations += 1;
        for (_, fact) in old {
            if fact.derivation == equality.derivation {
                continue;
            }
            let coefficient = fact.coeffs.get(var);
            if coefficient == 0 {
                self.insert(fact)?;
            } else {
                let scale = neg(mul(sign, coefficient)?)?;
                let combined = Fact::combo(scale, &equality, 1, &fact, &mut self.dag)?;
                self.stats.combinations += 1;
                self.insert(combined)?;
            }
            if self.contradiction.is_some() {
                break;
            }
        }
        Ok(true)
    }

    fn select_hard_equality(&self) -> R<Option<Fact>> {
        let mut best: Option<(Z, Z, Fact)> = None;
        for fact in self
            .constraints
            .values()
            .filter(|fact| fact.interval.is_exact())
        {
            let Some(minimum) = fact.coeffs.min_abs()? else {
                continue;
            };
            if minimum == 1 {
                continue;
            }
            let maximum = fact.coeffs.max_abs()?.unwrap_or(minimum);
            if best
                .as_ref()
                .is_none_or(|(best_min, best_max, _)| (minimum, maximum) < (*best_min, *best_max))
            {
                best = Some((minimum, maximum, fact.clone()));
            }
        }
        Ok(best.map(|(_, _, fact)| fact))
    }

    fn split_hard_equality(&mut self, equality: Fact) -> R<()> {
        let minimum = equality
            .coeffs
            .min_abs()?
            .ok_or(Failure::InvalidConstraint {
                detail: "hard equality has no nonzero coefficient".into(),
            })?;
        let modulus = add(minimum, 1)?;
        let (remainders, quotients) = equality.coeffs.balanced(modulus)?;
        let value = equality.interval.lower.ok_or(Failure::InvalidConstraint {
            detail: "hard equality lost its exact value".into(),
        })?;
        let (value_quotient, remainder) = balanced_div_rem(value, modulus)?;
        let fresh = self.num_vars;
        let base_vars = *self.base_vars.get_or_insert(self.num_vars);
        debug_assert_eq!(fresh, base_vars + self.fresh_projections.len());
        let (projection, projection_constant) = self.project_coeffs(&quotients)?;
        self.fresh_projections
            .push((projection, add(projection_constant, neg(value_quotient)?)?));
        self.num_vars += 1;
        let derivation = self.dag.push(Derivation::Balanced {
            parent: equality.derivation,
            modulus,
            fresh,
        });
        self.stats.hard_equality_splits += 1;
        self.stats.fresh_variables += 1;
        self.insert(Fact {
            coeffs: remainders.with_coefficient(fresh, modulus),
            interval: Interval::exact(remainder),
            derivation,
        })
    }

    fn solve_equalities(&mut self) -> R<()> {
        while self.contradiction.is_none() {
            if self.solve_easy_equality()? {
                continue;
            }
            let Some(equality) = self.select_hard_equality()? else {
                break;
            };
            self.split_hard_equality(equality)?;
        }
        Ok(())
    }

    fn select_fourier_motzkin(&self) -> R<Option<(usize, bool, usize)>> {
        let num_vars = self
            .constraints
            .keys()
            .map(|c| c.as_slice().len())
            .max()
            .unwrap_or(0);
        let mut best: Option<(usize, bool, usize)> = None;
        for var in 0..num_vars {
            let mut lower = 0usize;
            let mut upper = 0usize;
            let mut lower_exact = true;
            let mut upper_exact = true;
            let mut mentioned = false;
            for fact in self.constraints.values() {
                let c = fact.coeffs.get(var);
                if c == 0 {
                    continue;
                }
                mentioned = true;
                let scaled = fact.interval.scale(c)?;
                if scaled.lower.is_some() {
                    lower += 1;
                    lower_exact &= c.unsigned_abs() == 1;
                }
                if scaled.upper.is_some() {
                    upper += 1;
                    upper_exact &= c.unsigned_abs() == 1;
                }
            }
            if !mentioned {
                continue;
            }
            let exact = lower_exact || upper_exact;
            let size = lower.saturating_mul(upper);
            let candidate = (var, exact, size);
            if best.is_none_or(|(_, best_exact, best_size)| {
                size == 0 || (!best_exact && exact) || best_exact == exact && size < best_size
            }) {
                best = Some(candidate);
                if size == 0 {
                    break;
                }
            }
        }
        Ok(best)
    }

    fn fourier_motzkin(&mut self, var: usize, exact: bool) -> R<()> {
        let old = std::mem::take(&mut self.constraints);
        let mut irrelevant = Vec::new();
        let mut lower = Vec::new();
        let mut upper = Vec::new();
        for (_, fact) in old {
            let coefficient = fact.coeffs.get(var);
            if coefficient == 0 {
                irrelevant.push(fact);
                continue;
            }
            let scaled = fact.interval.scale(coefficient)?;
            if scaled.lower.is_some() {
                lower.push((fact.clone(), coefficient));
            }
            if scaled.upper.is_some() {
                upper.push((fact, coefficient));
            }
        }
        self.stats.fourier_motzkin_eliminations += 1;
        self.stats.exact_eliminations += usize::from(exact);
        for fact in irrelevant {
            self.insert(fact)?;
        }
        for (low, b) in &lower {
            for (high, a) in &upper {
                let combined = Fact::combo(*a, low, neg(*b)?, high, &mut self.dag)?;
                debug_assert_eq!(combined.coeffs.get(var), 0);
                self.stats.combinations += 1;
                self.insert(combined)?;
                if self.contradiction.is_some() {
                    return Ok(());
                }
            }
        }
        Ok(())
    }

    pub fn solve(mut self) -> R<(Self, Outcome)> {
        self.solve_equalities()?;
        let mut last_nonempty = Vec::new();
        while self.contradiction.is_none() && !self.constraints.is_empty() {
            last_nonempty = self.constraints.values().cloned().collect();
            let Some((var, exact, _)) = self.select_fourier_motzkin()? else {
                break;
            };
            self.fourier_motzkin(var, exact)?;
            self.solve_equalities()?;
        }
        let outcome = if let Some(derivation) = self.contradiction {
            Outcome::Contradiction {
                derivation,
                reachable_derivations: self.dag.reachable(derivation),
                stats: self.stats,
            }
        } else {
            let mut residual: Vec<_> = self.constraints.values().cloned().collect();
            if residual.is_empty() {
                residual = last_nonempty;
            }
            residual.sort_by(|a, b| a.coeffs.as_slice().cmp(b.coeffs.as_slice()));
            Outcome::NoContradiction {
                residual,
                stats: self.stats,
            }
        };
        Ok((self, outcome))
    }
}

fn replay_parent(facts: &[Option<Fact>], parent: DerivationId, child: DerivationId) -> R<&Fact> {
    if parent >= child {
        return Err(Failure::InvalidConstraint {
            detail: format!("derivation {child} has non-preceding parent {parent}"),
        });
    }
    facts
        .get(parent)
        .and_then(Option::as_ref)
        .ok_or(Failure::InvalidConstraint {
            detail: format!("derivation {child} has unavailable parent {parent}"),
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn has_model(facts: &[(Vec<Z>, Interval)], radius: Z) -> bool {
        let vars = facts.iter().map(|(c, _)| c.len()).max().unwrap_or(0);
        fn go(facts: &[(Vec<Z>, Interval)], radius: Z, values: &mut Vec<Z>, vars: usize) -> bool {
            if values.len() == vars {
                return facts.iter().all(|(coeffs, interval)| {
                    let value = coeffs.iter().zip(values.iter()).map(|(a, b)| a * b).sum();
                    interval.contains(value)
                });
            }
            (-radius..=radius).any(|value| {
                values.push(value);
                let found = go(facts, radius, values, vars);
                values.pop();
                found
            })
        }
        go(facts, radius, &mut Vec::new(), vars)
    }

    fn solve(facts: &[(Vec<Z>, Interval)]) -> (Problem, Outcome) {
        let mut problem = Problem::new();
        for (coeffs, interval) in facts {
            problem.assume(coeffs.clone(), *interval).unwrap();
        }
        problem.solve().unwrap()
    }

    #[test]
    fn intersecting_bounds_finds_a_direct_contradiction() {
        let facts = vec![(vec![1], Interval::lower(3)), (vec![1], Interval::upper(2))];
        let (
            problem,
            Outcome::Contradiction {
                derivation,
                reachable_derivations,
                stats,
            },
        ) = solve(&facts)
        else {
            panic!("expected contradiction");
        };
        assert_eq!(stats.intersections, 1);
        assert_eq!(reachable_derivations, problem.dag.reachable(derivation));
        assert!(!has_model(&facts, 5));
    }

    #[test]
    fn affine_relations_lower_strict_bounds_without_losing_one() {
        let x = LinearExpr::atom(0);
        let two = LinearExpr::constant(2);
        let three = LinearExpr::constant(3);
        let mut problem = Problem::new();
        problem.assume_relation(&x, Relation::Lt, &three).unwrap();
        problem.assume_relation(&x, Relation::Ge, &three).unwrap();
        let (_, Outcome::Contradiction { .. }) = problem.solve().unwrap() else {
            panic!("x < 3 and x >= 3 must contradict");
        };

        let twice_x_plus_two = x.checked_scale(2).unwrap().checked_add(&two).unwrap();
        assert_eq!(twice_x_plus_two.constant, 2);
        assert_eq!(twice_x_plus_two.coeffs.as_slice(), &[2]);
    }

    #[test]
    fn unit_equality_is_substituted_before_inequalities() {
        // x - y = 0, y >= 2, x <= 1.
        let facts = vec![
            (vec![1, -1], Interval::exact(0)),
            (vec![0, 1], Interval::lower(2)),
            (vec![1], Interval::upper(1)),
        ];
        let (_, Outcome::Contradiction { stats, .. }) = solve(&facts) else {
            panic!("expected contradiction");
        };
        assert!(stats.equality_eliminations >= 1);
        assert!(!has_model(&facts, 4));
    }

    #[test]
    fn hard_equality_uses_a_balanced_fresh_variable() {
        // 2x + 3y = -1 is incompatible with x,y >= 0. Neither coefficient is
        // a unit, so equality elimination must first balance the row.
        let assumptions = vec![
            (vec![2, 3], Interval::exact(-1)),
            (vec![1, 0], Interval::lower(0)),
            (vec![0, 1], Interval::lower(0)),
        ];
        let mut problem = Problem::new();
        for (coeffs, interval) in &assumptions {
            problem.assume(coeffs.clone(), *interval).unwrap();
        }
        let (problem, outcome) = problem.solve().unwrap();
        let Outcome::Contradiction {
            derivation, stats, ..
        } = outcome
        else {
            panic!("hard equality should contradict nonnegative variables")
        };
        assert_eq!(stats.hard_equality_splits, 1);
        assert_eq!(stats.fresh_variables, 1);
        assert!(stats.equality_eliminations >= 1);
        for (id, node) in problem.dag.nodes().iter().enumerate() {
            if let Derivation::Balanced { parent, .. } = *node {
                let child = problem.project_fact(&problem.replay(id).unwrap()).unwrap();
                let parent = problem
                    .project_fact(&problem.replay(parent).unwrap())
                    .unwrap();
                assert_eq!(child.coeffs, parent.coeffs);
                assert_eq!(child.interval, parent.interval);
            }
        }
        let replayed = problem.replay(derivation).unwrap();
        assert!(replayed.interval.is_impossible());
        assert!(!has_model(&assumptions, 4));
    }

    #[test]
    fn satisfiable_hard_equality_remains_a_residual_not_a_verdict() {
        let mut problem = Problem::new();
        problem.assume(vec![2, 3], Interval::exact(1)).unwrap();
        let (_, outcome) = problem.solve().unwrap();
        let Outcome::NoContradiction { stats, .. } = outcome else {
            panic!("2x + 3y = 1 has integer models")
        };
        assert!(stats.hard_equality_splits >= 1);
        assert!(has_model(&[(vec![2, 3], Interval::exact(1))], 4));
    }

    #[test]
    fn chained_hard_equalities_flatten_fresh_substitutions() {
        // Eliminating x from the second row makes it mention the first search
        // variable. A second balanced split must flatten that dependency back
        // to the three original variables for certificate reconstruction.
        let assumptions = vec![
            (vec![2, 3, 0], Interval::exact(1)),
            (vec![5, 0, 7], Interval::exact(2)),
        ];
        let mut problem = Problem::new();
        for (coeffs, interval) in &assumptions {
            problem.assume(coeffs.clone(), *interval).unwrap();
        }
        let (problem, outcome) = problem.solve().unwrap();
        let Outcome::NoContradiction { stats, .. } = outcome else {
            panic!("the chained system has model x=-1, y=1, z=1")
        };
        assert!(stats.hard_equality_splits >= 2);
        for (id, node) in problem.dag.nodes().iter().enumerate() {
            if let Derivation::Balanced { parent, .. } = *node {
                let child = problem.project_fact(&problem.replay(id).unwrap()).unwrap();
                let parent = problem
                    .project_fact(&problem.replay(parent).unwrap())
                    .unwrap();
                assert_eq!(child.coeffs, parent.coeffs);
                assert_eq!(child.interval, parent.interval);
            }
        }
        assert!(has_model(&assumptions, 2));
    }

    #[test]
    fn fourier_motzkin_combines_non_unit_bounds() {
        // 2x + y >= 3, 3x + y <= 2, and x >= 0 have no real,
        // hence no integer, solution.  Every nontrivial row has GCD one, so
        // this genuinely reaches non-exact Fourier--Motzkin rather than being
        // settled by integer bound rounding during insertion.
        let facts = vec![
            (vec![2, 1], Interval::lower(3)),
            (vec![3, 1], Interval::upper(2)),
            (vec![1], Interval::lower(0)),
        ];
        let (_, Outcome::Contradiction { stats, .. }) = solve(&facts) else {
            panic!("expected contradiction");
        };
        assert!(stats.fourier_motzkin_eliminations >= 1);
        assert!(stats.combinations >= 1);
        assert!(!has_model(&facts, 6));
    }

    #[test]
    fn satisfiable_system_is_not_mislabeled() {
        let facts = vec![
            (vec![1, -1], Interval::lower(0)),
            (vec![0, 1], Interval::lower(2)),
            (vec![1], Interval::upper(5)),
        ];
        let (_, Outcome::NoContradiction { residual, .. }) = solve(&facts) else {
            panic!("a satisfiable real shadow is not a contradiction");
        };
        assert!(
            !residual.is_empty(),
            "the last diagnostic frontier is retained"
        );
        assert!(has_model(&facts, 5));
    }

    #[test]
    fn gcd_rounding_is_integer_sound() {
        // 2x >= 3 normalizes to x >= 2; pairing with x <= 1 contradicts.
        let facts = vec![(vec![2], Interval::lower(3)), (vec![1], Interval::upper(1))];
        let (_, Outcome::Contradiction { stats, .. }) = solve(&facts) else {
            panic!("expected contradiction");
        };
        assert!(stats.gcd_divisions >= 1);
        assert!(!has_model(&facts, 4));
    }

    #[test]
    fn proof_slice_drops_unrelated_search_nodes() {
        let facts = vec![
            (vec![1], Interval::lower(3)),
            (vec![1], Interval::upper(2)),
            (vec![0, 1], Interval::lower(-100)),
        ];
        let (
            problem,
            Outcome::Contradiction {
                reachable_derivations,
                ..
            },
        ) = solve(&facts)
        else {
            panic!("expected contradiction");
        };
        assert!(reachable_derivations.len() < problem.dag.nodes().len());
        let replayed = problem
            .replay(reachable_derivations[reachable_derivations.len() - 1])
            .unwrap();
        assert!(replayed.interval.is_impossible() || replayed.coeffs.is_zero());
    }

    #[test]
    fn elimination_and_derivation_order_are_deterministic() {
        let facts = vec![
            (vec![2, 1], Interval::lower(3)),
            (vec![3, 1], Interval::upper(2)),
            (vec![1], Interval::lower(0)),
        ];
        let (first, first_outcome) = solve(&facts);
        let (second, second_outcome) = solve(&facts);
        assert_eq!(first.dag.nodes(), second.dag.nodes());
        let (
            Outcome::Contradiction {
                derivation: first_root,
                ..
            },
            Outcome::Contradiction {
                derivation: second_root,
                ..
            },
        ) = (first_outcome, second_outcome)
        else {
            panic!("expected both runs to find a contradiction");
        };
        assert_eq!(first_root, second_root);
        assert_eq!(
            first.replay(first_root).unwrap(),
            second.replay(second_root).unwrap()
        );
    }

    #[test]
    fn generated_bounded_systems_classify_real_shadow_misses() {
        // A deterministic differential rail for the untrusted search layer.
        // Every generated problem includes the same bounds used by exhaustive
        // search, so the model check is complete rather than merely finding
        // small counterexamples. This lets the rail distinguish satisfiable
        // systems, contradictions found by the real shadow, and genuine
        // integer-unsatisfiable systems missed without dark/grey shadows.
        let rows = [
            vec![-2, -1],
            vec![-1, 1],
            vec![0, 1],
            vec![1, 0],
            vec![1, 1],
            vec![2, -1],
        ];
        let intervals = [
            Interval::lower(-1),
            Interval::lower(1),
            Interval::upper(-1),
            Interval::upper(1),
            Interval::exact(0),
        ];
        let bounds = [
            (vec![1, 0], Interval::bounded(-4, 4)),
            (vec![0, 1], Interval::bounded(-4, 4)),
        ];
        let mut satisfiable = 0usize;
        let mut contradicted = 0usize;
        let mut integrality_gaps = 0usize;
        let mut first_gap = None;
        for a in 0..rows.len() {
            for b in 0..rows.len() {
                for c in 0..rows.len() {
                    for ia in intervals {
                        for ib in intervals {
                            let mut facts = vec![
                                (rows[a].clone(), ia),
                                (rows[b].clone(), ib),
                                (rows[c].clone(), Interval::lower(0)),
                            ];
                            facts.extend(bounds.clone());
                            let has_model = has_model(&facts, 4);
                            let (_, outcome) = solve(&facts);
                            match (has_model, outcome) {
                                (true, Outcome::NoContradiction { .. }) => satisfiable += 1,
                                (false, Outcome::Contradiction { .. }) => contradicted += 1,
                                (false, Outcome::NoContradiction { .. }) => {
                                    integrality_gaps += 1;
                                    first_gap.get_or_insert_with(|| facts.clone());
                                }
                                (true, Outcome::Contradiction { .. }) => {
                                    panic!("solver contradicted a model of {facts:?}")
                                }
                            }
                        }
                    }
                }
            }
        }
        assert_eq!(
            (satisfiable, contradicted, integrality_gaps),
            (4_414, 986, 0)
        );
        assert_eq!(first_gap, None);
    }

    #[test]
    fn seeded_bounded_systems_pin_integrality_gap_rate_and_replay_seed() {
        fn next(state: &mut u64) -> u64 {
            *state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            *state
        }

        let mut satisfiable = 0usize;
        let mut contradicted = 0usize;
        let mut integrality_gaps = 0usize;
        let mut first_gap = None;
        for seed in 0..20_000u64 {
            let mut state = seed;
            let mut facts = Vec::new();
            for _ in 0..4 {
                let mut row = vec![
                    (next(&mut state) % 11) as Z - 5,
                    (next(&mut state) % 11) as Z - 5,
                ];
                if row == [0, 0] {
                    row[0] = 1;
                }
                let bound = (next(&mut state) % 17) as Z - 8;
                let interval = if next(&mut state) & 1 == 0 {
                    Interval::lower(bound)
                } else {
                    Interval::upper(bound)
                };
                facts.push((row, interval));
            }
            facts.extend([
                (vec![1, 0], Interval::bounded(-4, 4)),
                (vec![0, 1], Interval::bounded(-4, 4)),
            ]);
            let has_model = has_model(&facts, 4);
            match (has_model, solve(&facts).1) {
                (true, Outcome::NoContradiction { .. }) => satisfiable += 1,
                (false, Outcome::Contradiction { .. }) => contradicted += 1,
                (false, Outcome::NoContradiction { .. }) => {
                    integrality_gaps += 1;
                    first_gap.get_or_insert_with(|| (seed, facts));
                }
                (true, Outcome::Contradiction { .. }) => {
                    panic!("solver contradicted a model at seed {seed}: {facts:?}")
                }
            }
        }
        assert_eq!(
            (satisfiable, contradicted, integrality_gaps),
            (11_074, 8_835, 91)
        );
        assert_eq!(
            first_gap,
            Some((
                680,
                vec![
                    (vec![2, 3], Interval::lower(-2)),
                    (vec![-2, -5], Interval::lower(0)),
                    (vec![0, 3], Interval::lower(3)),
                    (vec![-5, 0], Interval::lower(-7)),
                    (vec![1, 0], Interval::bounded(-4, 4)),
                    (vec![0, 1], Interval::bounded(-4, 4)),
                ]
            ))
        );
    }

    #[test]
    fn minimal_thin_integer_slice_is_a_known_real_shadow_miss() {
        // The first two rows imply 2y <= 2, while the third gives y >= 1,
        // hence y = 1. The remaining bounds on 2x are then 2x >= -5 and
        // 2x <= -5: the real shadow contains x = -5/2, but no integer does.
        let facts = vec![
            (vec![2, 3], Interval::lower(-2)),
            (vec![2, 5], Interval::upper(0)),
            (vec![0, 1], Interval::lower(1)),
        ];
        let (_, Outcome::NoContradiction { .. }) = solve(&facts) else {
            panic!("the real-shadow baseline now closes the pinned gap")
        };
        assert!(!has_model(&facts, 4));
    }

    #[test]
    fn pughs_nightmare_is_classified_as_a_real_shadow_miss() {
        // Pugh's representative worst case. Explicit search bounds make the
        // exhaustive classifier complete without changing the thin region in
        // which the original system could have an integer point.
        let facts = vec![
            (vec![11, 13], Interval::bounded(27, 45)),
            (vec![7, -9], Interval::bounded(-10, 4)),
            (vec![1, 0], Interval::bounded(-16, 16)),
            (vec![0, 1], Interval::bounded(-16, 16)),
        ];
        let (_, Outcome::NoContradiction { .. }) = solve(&facts) else {
            panic!("the real-shadow baseline now closes Pugh's nightmare")
        };
        assert!(!has_model(&facts, 16));
    }

    #[test]
    fn overflow_is_a_refusal() {
        let mut problem = Problem::new();
        problem
            .assume(vec![Z::MAX, Z::MAX - 1], Interval::lower(0))
            .unwrap();
        problem
            .assume(vec![Z::MAX - 2, Z::MAX - 3], Interval::upper(-1))
            .unwrap();
        let err = problem.solve().unwrap_err();
        assert!(matches!(err, Failure::Overflow { .. }));
    }
}
