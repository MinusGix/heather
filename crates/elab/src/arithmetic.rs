//! Shared, untrusted arithmetic reflection data.
//!
//! Solvers own their search state and proof rules. This module owns only the
//! checked affine representation, deterministic atom identities, and the
//! carrier/relation metadata produced by reflection.

use std::fmt;

/// Checked integer coefficients used by arithmetic reflection and search.
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

pub(crate) type R<T> = Result<T, Failure>;

pub(crate) fn add(a: Z, b: Z) -> R<Z> {
    a.checked_add(b).ok_or(Failure::Overflow {
        operation: "adding coefficients",
    })
}

pub(crate) fn mul(a: Z, b: Z) -> R<Z> {
    a.checked_mul(b).ok_or(Failure::Overflow {
        operation: "multiplying coefficients",
    })
}

pub(crate) fn neg(a: Z) -> R<Z> {
    a.checked_neg().ok_or(Failure::Overflow {
        operation: "negating a coefficient",
    })
}

pub(crate) fn abs(a: Z) -> R<Z> {
    a.checked_abs().ok_or(Failure::Overflow {
        operation: "taking a coefficient magnitude",
    })
}

/// Dense signed coefficients, with trailing zeroes removed.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Coeffs(pub(crate) Vec<Z>);

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

    pub(crate) fn leading(&self) -> Z {
        self.0.iter().copied().find(|&c| c != 0).unwrap_or(0)
    }

    pub(crate) fn coefficient_gcd(&self) -> R<Z> {
        self.0.iter().try_fold(0, |out, &c| Ok(gcd(out, abs(c)?)))
    }

    pub(crate) fn min_abs(&self) -> R<Option<Z>> {
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

    pub(crate) fn max_abs(&self) -> R<Option<Z>> {
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

    pub(crate) fn balanced(&self, modulus: Z) -> R<(Self, Self)> {
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

    pub(crate) fn with_coefficient(&self, index: usize, coefficient: Z) -> Self {
        let mut values = self.0.clone();
        values.resize(index + 1, 0);
        values[index] = coefficient;
        Self::new(values)
    }

    pub(crate) fn scale(&self, k: Z) -> R<Self> {
        self.0
            .iter()
            .map(|&c| mul(k, c))
            .collect::<R<Vec<_>>>()
            .map(Self::new)
    }

    pub(crate) fn exact_div(&self, divisor: Z) -> R<Self> {
        debug_assert!(divisor > 0);
        if self.0.iter().any(|c| c % divisor != 0) {
            return Err(Failure::InvalidConstraint {
                detail: "coefficient GCD did not divide every coefficient".into(),
            });
        }
        Ok(Self::new(self.0.iter().map(|c| c / divisor).collect()))
    }

    pub(crate) fn combo(a: Z, x: &Self, b: Z, y: &Self) -> R<Self> {
        let len = x.0.len().max(y.0.len());
        (0..len)
            .map(|i| add(mul(a, x.get(i))?, mul(b, y.get(i))?))
            .collect::<R<Vec<_>>>()
            .map(Self::new)
    }
}

/// A reflected affine expression `constant + sum(coeff[i] * atom[i])`.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Affine {
    pub constant: Z,
    pub coeffs: Coeffs,
}

impl Affine {
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Domain {
    Int,
    NatEmbedded,
}

/// A reflected arithmetic relation with solver-independent evidence attached.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReflectedConstraint<A, E> {
    pub domain: Domain,
    pub lhs: A,
    pub relation: Relation,
    pub rhs: A,
    pub evidence: E,
}

impl<A, E> ReflectedConstraint<A, E> {
    pub fn map_affine<B>(self, mut f: impl FnMut(A) -> B) -> ReflectedConstraint<B, E> {
        ReflectedConstraint {
            domain: self.domain,
            lhs: f(self.lhs),
            relation: self.relation,
            rhs: f(self.rhs),
            evidence: self.evidence,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AtomId(usize);

impl AtomId {
    pub fn index(self) -> usize {
        self.0
    }
}

#[derive(Debug, Clone)]
pub struct AtomTable<T> {
    entries: Vec<T>,
}

impl<T> Default for AtomTable<T> {
    fn default() -> Self {
        Self {
            entries: Vec::new(),
        }
    }
}

impl<T> AtomTable<T> {
    pub fn intern_by(
        &mut self,
        mut equivalent: impl FnMut(&T) -> bool,
        make: impl FnOnce() -> T,
    ) -> AtomId {
        if let Some(index) = self.entries.iter().position(&mut equivalent) {
            AtomId(index)
        } else {
            let index = self.entries.len();
            self.entries.push(make());
            AtomId(index)
        }
    }

    pub fn get(&self, id: AtomId) -> &T {
        &self.entries[id.0]
    }

    pub fn iter(&self) -> impl DoubleEndedIterator<Item = &T> + ExactSizeIterator {
        self.entries.iter()
    }

    pub fn iter_with_ids(&self) -> impl ExactSizeIterator<Item = (AtomId, &T)> {
        self.entries
            .iter()
            .enumerate()
            .map(|(index, entry)| (AtomId(index), entry))
    }
}

fn gcd(mut a: Z, mut b: Z) -> Z {
    debug_assert!(a >= 0 && b >= 0);
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

pub(crate) fn balanced_div_rem(a: Z, modulus: Z) -> R<(Z, Z)> {
    debug_assert!(modulus > 0);
    let quotient = a.div_euclid(modulus);
    let remainder = a.rem_euclid(modulus);
    if mul(2, remainder)? < modulus {
        Ok((quotient, remainder))
    } else {
        Ok((add(quotient, 1)?, add(remainder, neg(modulus)?)?))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn affine_operations_are_checked_and_canonical() {
        let x = Affine::atom(0);
        let y = Affine::atom(1);
        let value = x
            .checked_scale(2)
            .unwrap()
            .checked_sub(&y)
            .unwrap()
            .checked_add(&Affine::constant(3))
            .unwrap();
        assert_eq!(value.constant, 3);
        assert_eq!(value.coeffs.as_slice(), [2, -1]);
        assert!(matches!(
            Affine::constant(Z::MAX).checked_add(&Affine::constant(1)),
            Err(Failure::Overflow { .. })
        ));
    }

    #[test]
    fn atom_ids_are_stable_under_frontend_defined_equivalence() {
        let mut atoms = AtomTable::default();
        let x = atoms.intern_by(|entry: &&str| *entry == "x", || "x");
        let y = atoms.intern_by(|entry| *entry == "y", || "y");
        let x_again = atoms.intern_by(|entry| *entry == "x", || "not inserted");
        assert_eq!(x, x_again);
        assert_eq!((x.index(), y.index()), (0, 1));
        assert_eq!(atoms.iter().copied().collect::<Vec<_>>(), ["x", "y"]);
    }

    #[test]
    fn reflected_relations_keep_domain_and_evidence_separate_from_affines() {
        let constraint = ReflectedConstraint {
            domain: Domain::NatEmbedded,
            lhs: Affine::atom(0),
            relation: Relation::Le,
            rhs: Affine::constant(4),
            evidence: "h",
        };
        assert_eq!(constraint.domain, Domain::NatEmbedded);
        assert_eq!(constraint.relation, Relation::Le);
        assert_eq!(constraint.evidence, "h");
    }
}
