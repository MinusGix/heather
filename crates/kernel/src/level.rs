//! Universe levels and their decidable equivalence (docs/delam/04,
//! §Universe Levels).
//!
//! Levels form an idempotent commutative monoid under `⊔` with a successor
//! that distributes over `⊔`. Equivalence is decided by normalizing to the
//! map `adjust(count(l))` — per universe variable, the count of `1+`s applied
//! over it, plus a constant part, with the constant dropped when some
//! variable's count dominates it — and comparing maps for equality.
//!
//! `ω` is checker-internal (the "type" of universe-polymorphic functions):
//! it is not well-formed as a programmer-written level, does not participate
//! in the lattice, and is equivalent only to itself.

use std::collections::BTreeMap;
use std::rc::Rc;

/// A universe variable: de Bruijn index into the universe context `L`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UnivVar(pub u32);

/// Universe levels `l := ℓ | 0 | 1 + l | l ⊔ l' | ω`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Level {
    Var(UnivVar),
    Zero,
    Succ(Rc<Level>),
    Max(Rc<Level>, Rc<Level>),
    Omega,
}

impl Level {
    pub fn succ(l: Level) -> Level {
        Level::Succ(Rc::new(l))
    }

    pub fn max(a: Level, b: Level) -> Level {
        Level::Max(Rc::new(a), Rc::new(b))
    }

    /// Constant level `n`.
    pub fn constant(n: u64) -> Level {
        let mut l = Level::Zero;
        for _ in 0..n {
            l = Level::succ(l);
        }
        l
    }

    /// Well-formedness `L ⊢ l : Level`: every variable is in scope and `ω`
    /// does not occur (`ω` is never programmer-writable).
    pub fn well_formed(&self, univ_ctx_len: u32) -> bool {
        match self {
            Level::Var(v) => v.0 < univ_ctx_len,
            Level::Zero => true,
            Level::Succ(l) => l.well_formed(univ_ctx_len),
            Level::Max(a, b) => a.well_formed(univ_ctx_len) && b.well_formed(univ_ctx_len),
            Level::Omega => false,
        }
    }

    /// Normal form `adjust(count(l))`, or `None` for `ω`.
    ///
    /// `count` maps each variable to the number of `1+`s over it (taking max
    /// at `⊔` merges) and tracks the constant part; `adjust` drops the
    /// constant when some variable's count is at least it, since `n + ℓ ⊒ n`.
    pub fn normalize(&self) -> LevelNf {
        match self.count() {
            None => LevelNf::Omega,
            Some((konst, vars)) => {
                let dominated = vars.values().any(|&n| konst <= n);
                LevelNf::Finite {
                    konst: if dominated { None } else { Some(konst) },
                    vars,
                }
            }
        }
    }

    /// `count`: constant part plus per-variable successor counts.
    /// `None` when `ω` occurs anywhere (ω is not part of the lattice, so any
    /// occurrence poisons the level).
    fn count(&self) -> Option<(u64, BTreeMap<UnivVar, u64>)> {
        match self {
            Level::Var(v) => Some((0, BTreeMap::from([(*v, 0)]))),
            Level::Zero => Some((0, BTreeMap::new())),
            Level::Succ(l) => {
                let (k, mut vars) = l.count()?;
                for n in vars.values_mut() {
                    *n += 1;
                }
                Some((k + 1, vars))
            }
            Level::Max(a, b) => {
                let (ka, mut vars) = a.count()?;
                let (kb, vars_b) = b.count()?;
                for (v, n) in vars_b {
                    let e = vars.entry(v).or_insert(n);
                    *e = (*e).max(n);
                }
                Some((ka.max(kb), vars))
            }
            Level::Omega => None,
        }
    }

    /// Decidable equivalence `L ⊢ l ≈ l' : Level` (extended so that
    /// `ω ≈ ω` only).
    pub fn equiv(&self, other: &Level) -> bool {
        self.normalize() == other.normalize()
    }

    /// The induced partial order `l ≤ l' := l' ≈ l ⊔ l'`. `ω` is
    /// incomparable (returns false unless both are `ω`-free and related, or
    /// both are exactly `ω`).
    pub fn le(&self, other: &Level) -> bool {
        if matches!(self, Level::Omega) || matches!(other, Level::Omega) {
            return self.equiv(other);
        }
        other.equiv(&Level::max(self.clone(), other.clone()))
    }

    /// Apply a universe substitution `φ`: variable `ℓᵢ` (innermost = 0) maps
    /// to `phi[i]`. Callers guarantee `phi` covers the level's context.
    pub fn subst(&self, phi: &[Level]) -> Level {
        self.subst_at(phi, 0)
    }

    /// Apply `φ` under `depth` universe binders: variables below `depth` are
    /// bound (left alone); variable `depth + i` maps to `phi[i]` shifted by
    /// `depth` so it does not capture the binders passed under.
    pub fn subst_at(&self, phi: &[Level], depth: u32) -> Level {
        match self {
            Level::Var(v) if v.0 < depth => Level::Var(*v),
            Level::Var(v) => phi[(v.0 - depth) as usize].shift(depth, 0),
            Level::Zero => Level::Zero,
            Level::Succ(l) => Level::succ(l.subst_at(phi, depth)),
            Level::Max(a, b) => Level::max(a.subst_at(phi, depth), b.subst_at(phi, depth)),
            Level::Omega => Level::Omega,
        }
    }

    /// Weakening: add `by` to every variable at or above `cutoff`.
    pub fn shift(&self, by: u32, cutoff: u32) -> Level {
        match self {
            Level::Var(v) if v.0 < cutoff => Level::Var(*v),
            Level::Var(v) => Level::Var(UnivVar(v.0 + by)),
            Level::Zero => Level::Zero,
            Level::Succ(l) => Level::succ(l.shift(by, cutoff)),
            Level::Max(a, b) => Level::max(a.shift(by, cutoff), b.shift(by, cutoff)),
            Level::Omega => Level::Omega,
        }
    }
}

/// Normal form of a level: canonical representative of its ≈-class.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LevelNf {
    /// `konst ⊔ ⨆ (n_i + ℓ_i)`; `konst` is `None` when dominated by some
    /// variable entry (the `adjust` step).
    Finite {
        konst: Option<u64>,
        vars: BTreeMap<UnivVar, u64>,
    },
    Omega,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(n: u32) -> Level {
        Level::Var(UnivVar(n))
    }

    #[test]
    fn monoid_laws() {
        let l = Level::max(var(0), Level::constant(2));
        // idempotence, commutativity, unit
        assert!(Level::max(l.clone(), l.clone()).equiv(&l));
        assert!(Level::max(var(0), var(1)).equiv(&Level::max(var(1), var(0))));
        assert!(Level::max(l.clone(), Level::Zero).equiv(&l));
        // associativity
        let a = Level::max(Level::max(var(0), var(1)), var(2));
        let b = Level::max(var(0), Level::max(var(1), var(2)));
        assert!(a.equiv(&b));
    }

    #[test]
    fn succ_distributes_and_absorbs() {
        // 1 + (l ⊔ l') ≈ (1 + l) ⊔ (1 + l')
        let lhs = Level::succ(Level::max(var(0), var(1)));
        let rhs = Level::max(Level::succ(var(0)), Level::succ(var(1)));
        assert!(lhs.equiv(&rhs));
        // ℓ ⊔ (1 + ℓ) ≈ 1 + ℓ  (absorption)
        assert!(Level::max(var(0), Level::succ(var(0))).equiv(&Level::succ(var(0))));
        // generalized absorption: ℓ ⊔ (n + ℓ) ≈ n + ℓ
        let n_plus = Level::succ(Level::succ(Level::succ(var(0))));
        assert!(Level::max(var(0), n_plus.clone()).equiv(&n_plus));
    }

    #[test]
    fn adjust_drops_dominated_constant() {
        // 2 ⊔ (2 + ℓ) ≈ 2 + ℓ: constant dominated, dropped.
        let two_plus = Level::succ(Level::succ(var(0)));
        assert!(Level::max(Level::constant(2), two_plus.clone()).equiv(&two_plus));
        // 2 ⊔ (1 + ℓ) is NOT ≈ 1 + ℓ: ℓ may be 0.
        let one_plus = Level::succ(var(0));
        assert!(!Level::max(Level::constant(2), one_plus.clone()).equiv(&one_plus));
    }

    #[test]
    fn order() {
        assert!(Level::Zero.le(&var(0)));
        assert!(var(0).le(&Level::succ(var(0))));
        assert!(!Level::succ(var(0)).le(&var(0)));
        // constants
        assert!(Level::constant(1).le(&Level::constant(3)));
        assert!(!Level::constant(3).le(&Level::constant(1)));
    }

    #[test]
    fn omega_only_equals_omega() {
        assert!(Level::Omega.equiv(&Level::Omega));
        assert!(!Level::Omega.equiv(&Level::Zero));
        // ω anywhere in a level poisons it: not equivalent even to plain ω
        // (such levels are ill-formed and never reach comparison).
        assert!(!Level::max(Level::Omega, Level::Zero).equiv(&Level::Zero));
        // ω is not well-formed as a source-level level
        assert!(!Level::Omega.well_formed(0));
    }
}
