//! Universe levels and their decidable equivalence (docs/delam/04,
//! §Universe Levels).
//!
//! Levels form an idempotent commutative monoid under `⊔` with a successor
//! that distributes over `⊔`. Equivalence is decided by normalizing to the
//! map `adjust(count(l))` — per universe variable, the count of `1+`s applied
//! over it, plus a constant part, with the constant dropped when some
//! variable's count dominates it — and comparing maps for equality.
//!
//! # Canonical by construction
//!
//! A [`Level`] *is* that normal form (`issues/kernel-compact-level.md`).
//! Every constructor ([`Level::succ`], [`Level::max`], [`Level::constant`],
//! the substitutions) returns the canonical representative of its ≈-class,
//! so `≈` is `==` and a term's levels never need a separate normalization
//! pass. The common forms are inline — `0`, `ℓ`, `k + 0`, `k + ℓ` and `ω` —
//! and only a genuine join of two or more components lives behind an `Rc`,
//! so a `Level` is 16 bytes with no allocation in the common case.
//!
//! **Why this is sound.** Every judgement the kernel makes about a level —
//! [`Level::equiv`], [`Level::le`], [`Level::well_formed`] — is a function of
//! its normal form (normalization never drops a variable, so the variables a
//! level mentions are those of its normal form, and any `ω` poisons both),
//! and substitution respects `≈` (the level equations are closed under
//! substituting levels for variables). So replacing a level by its
//! representative, anywhere, changes no verdict. What it changes is
//! *spelling*: `Ty (ℓ ⊔ ℓ')` and `Ty (ℓ' ⊔ ℓ)` are now the same syntax,
//! which is the quotient DeLaM ch. 05's Static Code lemma takes anyway.
//!
//! **Why it is possible at all** is a property of the level *algebra*; see
//! [`LevelNf::canonical`] for what would take it away.
//!
//! `ω` is checker-internal (the "type" of universe-polymorphic functions):
//! it is not well-formed as a programmer-written level, does not participate
//! in the lattice, and is equivalent only to itself. A level built with `ω`
//! anywhere in it is `ω`.

use std::collections::BTreeMap;
use std::num::NonZeroU32;
use crate::rc::Rc;

/// A universe variable: de Bruijn index into the universe context `L`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UnivVar(pub u32);

/// Universe levels `l := ℓ | 0 | 1 + l | l ⊔ l' | ω`, held as the canonical
/// representative of their ≈-class (see the module docs).
///
/// `Zero`, `Var` and `Omega` are written and matched directly. `Lift` and
/// `Join` carry types whose fields are private to this module, so outside
/// it they can be matched but only built through the constructors, which is
/// what keeps every `Level` canonical. Read a level's components with
/// [`Level::parts`].
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Level {
    Zero,
    Var(UnivVar),
    /// `k + 0` or `k + ℓ`, `k ≥ 1`.
    Lift(Lift),
    /// Every other finite level: two or more components, or an offset too
    /// large for [`Lift`].
    Join(Rc<Join>),
    Omega,
}

/// `by + base` (`base` absent for `0`). Inline in [`Level::Lift`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Lift {
    by: NonZeroU32,
    base: Option<UnivVar>,
}

/// `konst ⊔ ⨆ (n_i + ℓ_i)` after `adjust`: `vars` strictly ascending by
/// variable, `konst` `None` exactly when some `n_i ≥ konst`. Invariant: no
/// inline [`Level`] form can spell it (see `Level::from_count`).
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Join {
    konst: Option<u64>,
    vars: Box<[(UnivVar, u64)]>,
}

/// The variable terms of a level's canonical spelling, `(ℓ, n)` for `n + ℓ`,
/// in ascending variable order. See [`Level::parts`].
#[derive(Clone)]
pub struct Parts<'a> {
    one: Option<(UnivVar, u64)>,
    rest: std::slice::Iter<'a, (UnivVar, u64)>,
}

impl Iterator for Parts<'_> {
    type Item = (UnivVar, u64);

    fn next(&mut self) -> Option<(UnivVar, u64)> {
        self.one.take().or_else(|| self.rest.next().copied())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = self.one.is_some() as usize + self.rest.len();
        (n, Some(n))
    }
}

impl ExactSizeIterator for Parts<'_> {}

/// `a + b` on level offsets. Unreachable by any real term (offsets come from
/// numerals and from one `1+` per typing step), but a wrapped offset would
/// equate two different levels, so it is a panic, never a wrap.
fn offset_add(a: u64, b: u64) -> u64 {
    a.checked_add(b).expect("universe level offset overflows u64")
}

/// `adjust(count(·))` under construction: the constant part and the
/// per-variable offsets, unsorted, with `ω` poisoning the lot.
struct Count {
    konst: u64,
    vars: Vec<(UnivVar, u64)>,
    omega: bool,
}

impl Count {
    fn new(konst: u64) -> Count {
        Count { konst, vars: Vec::new(), omega: false }
    }

    /// Join in the components of `by + l`. A dominated constant that `l`
    /// dropped stays dropped: raised by `by` it is still at most the raised
    /// count of the variable that dominated it.
    fn add(&mut self, l: &Level, by: u64) {
        match l {
            Level::Zero => self.konst = self.konst.max(by),
            Level::Var(v) => self.vars.push((*v, by)),
            Level::Lift(x) => {
                let n = offset_add(u64::from(x.by.get()), by);
                match x.base {
                    None => self.konst = self.konst.max(n),
                    Some(v) => self.vars.push((v, n)),
                }
            }
            Level::Join(j) => {
                if let Some(k) = j.konst {
                    self.konst = self.konst.max(offset_add(k, by));
                }
                self.vars.extend(j.vars.iter().map(|&(v, n)| (v, offset_add(n, by))));
            }
            Level::Omega => self.omega = true,
        }
    }

    fn finish(mut self) -> Level {
        if self.omega {
            return Level::Omega;
        }
        // Sorted by (variable, offset), so the last entry of each variable
        // carries its maximum: `⊔` merges a variable's terms by max.
        self.vars.sort_unstable();
        let mut vars: Vec<(UnivVar, u64)> = Vec::with_capacity(self.vars.len());
        for (v, n) in self.vars {
            match vars.last_mut() {
                Some(last) if last.0 == v => last.1 = n,
                _ => vars.push((v, n)),
            }
        }
        Level::from_count(self.konst, vars)
    }
}

impl Level {
    /// `1 + l`.
    pub fn succ(l: Level) -> Level {
        l.plus(1)
    }

    /// `by + l`: `by` successors, in constant time.
    pub fn plus(&self, by: u64) -> Level {
        if by == 0 {
            return self.clone();
        }
        match self {
            Level::Zero => Level::lift(None, by),
            Level::Var(v) => Level::lift(Some(*v), by),
            Level::Lift(x) => Level::lift(x.base, offset_add(u64::from(x.by.get()), by)),
            Level::Join(_) => {
                let mut c = Count::new(0);
                c.add(self, by);
                c.finish()
            }
            Level::Omega => Level::Omega,
        }
    }

    /// `a ⊔ b`. With canonical levels there is one spelling of the result,
    /// so this and [`Level::join`] are the same operation.
    pub fn max(a: Level, b: Level) -> Level {
        match (&a, &b) {
            (Level::Omega, _) | (_, Level::Omega) => Level::Omega,
            (Level::Zero, _) => b,
            (_, Level::Zero) => a,
            _ if a == b => a,
            _ => {
                let mut c = Count::new(0);
                c.add(&a, 0);
                c.add(&b, 0);
                c.finish()
            }
        }
    }

    /// `a ⊔ b`; the same as [`Level::max`]. The name the inference sites
    /// use, from when `max` preserved a spelling and this one shrank it.
    pub fn join(a: Level, b: Level) -> Level {
        Level::max(a, b)
    }

    /// Constant level `n`.
    pub fn constant(n: u64) -> Level {
        Level::lift(None, n)
    }

    /// The level with constant part `konst` joined with `n + ℓ` for each
    /// `(ℓ, n)` in `vars`, in any order and with repeats: the canonical
    /// form of whatever the parts spell. How a decoder rebuilds a level, so
    /// that no input can produce a non-canonical one.
    pub fn of_parts(konst: Option<u64>, vars: impl IntoIterator<Item = (UnivVar, u64)>) -> Level {
        let mut c = Count::new(konst.unwrap_or(0));
        c.vars.extend(vars);
        c.finish()
    }

    /// `by + base` (`base` absent for `0`) in its canonical form.
    fn lift(base: Option<UnivVar>, by: u64) -> Level {
        if by == 0 {
            return base.map_or(Level::Zero, Level::Var);
        }
        match u32::try_from(by).ok().and_then(NonZeroU32::new) {
            Some(by) => Level::Lift(Lift { by, base }),
            None => Level::Join(Rc::new(match base {
                None => Join { konst: Some(by), vars: Box::new([]) },
                Some(v) => Join { konst: None, vars: Box::new([(v, by)]) },
            })),
        }
    }

    /// The canonical form of `adjust(konst, vars)`, `vars` strictly
    /// ascending: the one place a `Join` is built, and the inline form
    /// whenever one exists.
    fn from_count(konst: u64, vars: Vec<(UnivVar, u64)>) -> Level {
        let dominated = vars.iter().any(|&(_, n)| konst <= n);
        match (dominated, vars.as_slice()) {
            (_, []) => Level::lift(None, konst),
            (true, [(v, n)]) => Level::lift(Some(*v), *n),
            _ => Level::Join(Rc::new(Join {
                konst: (!dominated).then_some(konst),
                vars: vars.into_boxed_slice(),
            })),
        }
    }

    /// The canonical spelling's components: `None` for `ω`, else the
    /// constant part (absent when some variable term dominates it) and the
    /// variable terms. `0` is `(Some(0), [])` and `ℓ` is `(None, [(ℓ, 0)])`.
    pub fn parts(&self) -> Option<(Option<u64>, Parts<'_>)> {
        let empty: &[(UnivVar, u64)] = &[];
        let only = |konst: Option<u64>, one: Option<(UnivVar, u64)>| {
            Some((konst, Parts { one, rest: empty.iter() }))
        };
        match self {
            Level::Zero => only(Some(0), None),
            Level::Var(v) => only(None, Some((*v, 0))),
            Level::Lift(x) => {
                let by = u64::from(x.by.get());
                match x.base {
                    None => only(Some(by), None),
                    Some(v) => only(None, Some((v, by))),
                }
            }
            Level::Join(j) => Some((j.konst, Parts { one: None, rest: j.vars.iter() })),
            Level::Omega => None,
        }
    }

    /// The level as a closed constant, if it is one. Every variable-free
    /// level is: `2 ⊔ 1` is `2`.
    pub fn as_constant(&self) -> Option<u64> {
        match self.parts() {
            Some((Some(k), vars)) if vars.len() == 0 => Some(k),
            _ => None,
        }
    }

    /// Whether every variable the level mentions satisfies `pred`.
    fn vars_all(&self, mut pred: impl FnMut(UnivVar) -> bool) -> bool {
        self.parts().map_or(true, |(_, mut vars)| vars.all(|(v, _)| pred(v)))
    }

    /// Replace each variable `ℓ` by `f(ℓ)`, as the level algebra's
    /// homomorphism: `n + ℓ` becomes `n + f(ℓ)`, joined with the constant.
    fn map_vars(&self, f: impl Fn(UnivVar) -> Level) -> Level {
        match self {
            Level::Zero | Level::Omega => self.clone(),
            Level::Var(v) => f(*v),
            Level::Lift(x) => match x.base {
                None => self.clone(),
                Some(v) => f(v).plus(u64::from(x.by.get())),
            },
            Level::Join(j) => {
                let mut c = Count::new(j.konst.unwrap_or(0));
                for &(v, n) in j.vars.iter() {
                    c.add(&f(v), n);
                }
                c.finish()
            }
        }
    }

    /// Well-formedness `L ⊢ l : Level`: every variable is in scope and `ω`
    /// does not occur (`ω` is never programmer-writable).
    pub fn well_formed(&self, univ_ctx_len: u32) -> bool {
        !matches!(self, Level::Omega) && self.vars_all(|v| v.0 < univ_ctx_len)
    }

    /// Normal form `adjust(count(l))`, or `LevelNf::Omega` for `ω`: the
    /// level's own components, as a map.
    pub fn normalize(&self) -> LevelNf {
        match self.parts() {
            None => LevelNf::Omega,
            Some((konst, vars)) => LevelNf::Finite { konst, vars: vars.collect() },
        }
    }

    /// Decidable equivalence `L ⊢ l ≈ l' : Level` (extended so that
    /// `ω ≈ ω` only). Levels are canonical, so this is syntactic equality;
    /// `Rc`'s equality is pointer-first, so a shared join is decided at
    /// the root.
    pub fn equiv(&self, other: &Level) -> bool {
        self == other
    }

    /// The induced partial order `l ≤ l' := l' ≈ l ⊔ l'`. `ω` is
    /// incomparable (returns false unless both are `ω`-free and related, or
    /// both are exactly `ω`).
    pub fn le(&self, other: &Level) -> bool {
        if self == other {
            return true;
        }
        if matches!(self, Level::Omega) || matches!(other, Level::Omega) {
            return false;
        }
        *other == Level::max(self.clone(), other.clone())
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
        if self.vars_all(|v| v.0 < depth) {
            return self.clone();
        }
        self.map_vars(|v| if v.0 < depth { Level::Var(v) } else { phi[(v.0 - depth) as usize].shift(depth, 0) })
    }

    /// Instantiate the innermost `phi.len()` universe variables under
    /// `depth` binders (the universe mirror of [`crate::subst::GlobalSubst`]'s
    /// instantiation form): variable `depth + i` for `i < phi.len()` maps to
    /// `phi[i]` shifted by `depth`; variables beyond map down by `phi.len()`
    /// (the instantiated binders are consumed).
    pub fn inst_at(&self, phi: &[Level], depth: u32) -> Level {
        let n = phi.len() as u32;
        if n == 0 || self.vars_all(|v| v.0 < depth) {
            return self.clone();
        }
        self.map_vars(|v| {
            if v.0 < depth {
                Level::Var(v)
            } else if v.0 - depth < n {
                phi[(v.0 - depth) as usize].shift(depth, 0)
            } else {
                Level::Var(UnivVar(v.0 - n))
            }
        })
    }

    /// Weakening: add `by` to every variable at or above `cutoff`.
    pub fn shift(&self, by: u32, cutoff: u32) -> Level {
        if by == 0 || self.vars_all(|v| v.0 < cutoff) {
            return self.clone();
        }
        // Injective and order-preserving on variables, so the result is
        // canonical as it stands; going through `map_vars` re-derives that
        // rather than relying on it.
        self.map_vars(|v| Level::Var(if v.0 < cutoff { v } else { UnivVar(v.0 + by) }))
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

impl LevelNf {
    /// The [`Level`] of this ≈-class. Levels are canonical by construction,
    /// so `l.normalize().canonical() == l` for every `l`.
    ///
    /// # Canonical levels are a property of the level *algebra*, and a new sort could take it away
    ///
    /// A canonical representative exists because DeLaM's levels are a join
    /// semilattice with a successor (`ℓ | 0 | 1+l | l ⊔ l' | ω`): `⊔` is
    /// associative, commutative and idempotent, and `1+` distributes over it,
    /// so every level collapses to `max of (n + ℓᵢ)` plus a constant. Agda's
    /// `lzero`/`lsuc`/`_⊔_` is the same algebra and admits the same normal
    /// form.
    ///
    /// Lean cannot do this, because an impredicative `Prop` forces a second
    /// operator: `imax u v` is `0` when `v` is `0` and `max u v` otherwise.
    /// That is *conditional*, not a lattice operation, so there is no
    /// finitary canonical form — level equality has to be a decision
    /// procedure with case splits on whether a variable is `Zero` or
    /// `Succ p`. Lean's kernel does exactly that and is correct, but it
    /// cannot hand back a representative, so terms with equivalent-but-not-
    /// identical levels miss the structural fast path in its defeq check and
    /// fall through to unfolding (leanprover/lean4#12102, reproducer at 600×).
    ///
    /// **So: if Heather ever grows an impredicative or proof-irrelevant sort,
    /// [`Level`] stops being canonical**, `Level::equiv` stops being `==`,
    /// and every structural term comparison — [`crate::conv`]'s `code_eq`
    /// among them — silently becomes *too fine*: the exact defect `code_eq`
    /// once had (see `docs/ch05-06-lemma-audit.md`, §Static Code),
    /// reintroduced by a feature that looks unrelated. Any such sort must
    /// come with a decision procedure for level equality and a new
    /// representation, not just a new `Level` constructor.
    pub fn canonical(&self) -> Level {
        match self {
            LevelNf::Finite { konst, vars } => Level::of_parts(*konst, vars.iter().map(|(&v, &n)| (v, n))),
            LevelNf::Omega => Level::Omega,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(n: u32) -> Level {
        Level::Var(UnivVar(n))
    }

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn level_is_two_words() {
        assert_eq!(std::mem::size_of::<Level>(), 16);
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
        // ω is comparable only with itself
        assert!(Level::Omega.le(&Level::Omega));
        assert!(!Level::Zero.le(&Level::Omega));
        assert!(!Level::Omega.le(&Level::Zero));
    }

    #[test]
    fn omega_only_equals_omega() {
        assert!(Level::Omega.equiv(&Level::Omega));
        assert!(!Level::Omega.equiv(&Level::Zero));
        // ω anywhere in a level poisons it: the level *is* ω (it was always
        // `≈ ω`, and is ill-formed either way).
        assert_eq!(Level::max(Level::Omega, Level::Zero), Level::Omega);
        assert_eq!(Level::succ(Level::Omega), Level::Omega);
        assert_eq!(var(0).subst(&[Level::Omega]), Level::Omega);
        assert!(!Level::max(Level::Omega, Level::Zero).equiv(&Level::Zero));
        // ω is not well-formed as a source-level level
        assert!(!Level::Omega.well_formed(0));
    }

    /// Equivalent spellings are one value: the representation is the
    /// quotient, so `==` is `≈` without a normalization step.
    #[test]
    fn equivalent_spellings_are_equal() {
        let pairs = [
            (Level::max(var(0), var(0)), var(0)),
            (
                Level::succ(Level::max(var(0), var(1))),
                Level::max(Level::succ(var(0)), Level::succ(var(1))),
            ),
            (Level::max(var(1), var(0)), Level::max(var(0), var(1))),
            (Level::max(var(0), Level::Zero), var(0)),
            (
                Level::max(Level::constant(2), Level::succ(Level::succ(var(0)))),
                Level::succ(Level::succ(var(0))),
            ),
            (Level::max(Level::constant(1), Level::constant(3)), Level::constant(3)),
        ];
        for (a, b) in pairs {
            assert_eq!(a, b);
            assert!(a.le(&b) && b.le(&a));
        }
    }

    /// The inline forms are used whenever they can spell the level, so a
    /// `Join` is only ever a genuine join (or a huge offset).
    #[test]
    fn inline_forms_are_preferred() {
        assert!(matches!(Level::constant(0), Level::Zero));
        assert!(matches!(Level::constant(5), Level::Lift(_)));
        assert!(matches!(Level::max(Level::constant(1), Level::constant(5)), Level::Lift(_)));
        assert!(matches!(Level::max(var(3), Level::succ(var(3))), Level::Lift(_)));
        assert!(matches!(Level::max(var(0), Level::constant(1)), Level::Join(_)));
        assert!(matches!(Level::max(var(0), var(1)), Level::Join(_)));
        // a join that collapses back to one component returns to inline
        let j = Level::max(var(0), var(1));
        assert_eq!(j.subst(&[Level::Zero, Level::Zero]), Level::Zero);
        assert_eq!(j.subst(&[var(0), var(0)]), var(0));
    }

    /// Offsets past `u32` leave the inline form and stay exact.
    #[test]
    fn large_offsets_are_exact() {
        let edge = u64::from(u32::MAX);
        let top = Level::constant(edge);
        assert!(matches!(top, Level::Lift(_)));
        let past = Level::succ(top.clone());
        assert!(matches!(past, Level::Join(_)));
        assert_eq!(past, Level::constant(edge + 1));
        assert_ne!(past, top);
        assert_eq!(past.as_constant(), Some(edge + 1));
        assert!(top.le(&past) && !past.le(&top));
        let v = var(2).plus(edge + 7);
        assert_eq!(v, Level::succ(var(2).plus(edge + 6)));
        assert_eq!(Level::max(v.clone(), Level::constant(edge)), v);
        assert_eq!(v.normalize().canonical(), v);
    }

    // ---- reference model ------------------------------------------------
    //
    // The tree representation and the normalization this module used before
    // levels were canonical (`count`, `adjust`), kept as the oracle: every
    // operation on `Level` must agree with doing the same thing to the tree
    // and normalizing afterwards.

    #[derive(Clone, Debug)]
    enum T {
        Var(u32),
        Zero,
        Succ(Box<T>),
        Max(Box<T>, Box<T>),
        Omega,
    }

    fn count(t: &T) -> Option<(u64, BTreeMap<UnivVar, u64>)> {
        match t {
            T::Var(v) => Some((0, BTreeMap::from([(UnivVar(*v), 0)]))),
            T::Zero => Some((0, BTreeMap::new())),
            T::Succ(l) => {
                let (k, mut vars) = count(l)?;
                for n in vars.values_mut() {
                    *n += 1;
                }
                Some((k + 1, vars))
            }
            T::Max(a, b) => {
                let (ka, mut vars) = count(a)?;
                let (kb, vars_b) = count(b)?;
                for (v, n) in vars_b {
                    let e = vars.entry(v).or_insert(n);
                    *e = (*e).max(n);
                }
                Some((ka.max(kb), vars))
            }
            T::Omega => None,
        }
    }

    fn reference_nf(t: &T) -> LevelNf {
        match count(t) {
            None => LevelNf::Omega,
            Some((konst, vars)) => {
                let dominated = vars.values().any(|&n| konst <= n);
                LevelNf::Finite { konst: if dominated { None } else { Some(konst) }, vars }
            }
        }
    }

    fn reference_wf(t: &T, len: u32) -> bool {
        match t {
            T::Var(v) => *v < len,
            T::Zero => true,
            T::Succ(l) => reference_wf(l, len),
            T::Max(a, b) => reference_wf(a, len) && reference_wf(b, len),
            T::Omega => false,
        }
    }

    fn reference_shift(t: &T, by: u32, cutoff: u32) -> T {
        match t {
            T::Var(v) if *v < cutoff => T::Var(*v),
            T::Var(v) => T::Var(v + by),
            T::Zero => T::Zero,
            T::Succ(l) => T::Succ(Box::new(reference_shift(l, by, cutoff))),
            T::Max(a, b) => T::Max(Box::new(reference_shift(a, by, cutoff)), Box::new(reference_shift(b, by, cutoff))),
            T::Omega => T::Omega,
        }
    }

    /// Tree instantiation: the payloads for variables `depth..depth+n`,
    /// renumbering the rest down by `n` (`inst_at`); `subst_at` is the case
    /// where `phi` covers every free variable.
    fn reference_inst(t: &T, phi: &[T], depth: u32) -> T {
        let n = phi.len() as u32;
        match t {
            T::Var(v) if *v < depth => T::Var(*v),
            T::Var(v) if v - depth < n => reference_shift(&phi[(v - depth) as usize], depth, 0),
            T::Var(v) => T::Var(v - n),
            T::Zero => T::Zero,
            T::Succ(l) => T::Succ(Box::new(reference_inst(l, phi, depth))),
            T::Max(a, b) => T::Max(Box::new(reference_inst(a, phi, depth)), Box::new(reference_inst(b, phi, depth))),
            T::Omega => T::Omega,
        }
    }

    fn build(t: &T) -> Level {
        match t {
            T::Var(v) => var(*v),
            T::Zero => Level::Zero,
            T::Succ(l) => Level::succ(build(l)),
            T::Max(a, b) => Level::max(build(a), build(b)),
            T::Omega => Level::Omega,
        }
    }

    /// Zero-dependency generator (the kernel takes no dev-dependencies).
    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            self.0 >> 33
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    fn gen_level(r: &mut Rng, depth: u32, omega: bool) -> T {
        let leaf = depth == 0 || r.below(3) == 0;
        if leaf {
            return match r.below(if omega { 13 } else { 12 }) {
                0..=3 => T::Zero,
                4..=11 => T::Var(r.below(4) as u32),
                _ => T::Omega,
            };
        }
        if r.below(2) == 0 {
            T::Succ(Box::new(gen_level(r, depth - 1, omega)))
        } else {
            T::Max(Box::new(gen_level(r, depth - 1, omega)), Box::new(gen_level(r, depth - 1, omega)))
        }
    }

    const SEEDS: u64 = 300;

    /// Building a tree through the constructors yields exactly the tree's
    /// normal form, and that form is its own canonical representative.
    #[test]
    fn constructors_agree_with_the_reference_normal_form() {
        for seed in 0..SEEDS {
            let mut r = Rng(seed);
            for _ in 0..40 {
                let t = gen_level(&mut r, 6, true);
                let l = build(&t);
                assert_eq!(l.normalize(), reference_nf(&t), "seed {seed}");
                assert_eq!(l.normalize().canonical(), l, "seed {seed}");
                assert_eq!(reference_nf(&t).canonical(), l, "seed {seed}");
                for len in 0..5 {
                    assert_eq!(l.well_formed(len), reference_wf(&t, len), "seed {seed}");
                }
                if let Some((konst, vars)) = l.parts() {
                    assert_eq!(Level::of_parts(konst, vars), l, "seed {seed}");
                }
            }
        }
    }

    /// `==` (and so `equiv`) and `le` decide exactly what the reference's
    /// normal-form comparison decides, in both directions: no pair is
    /// merged that the reference keeps apart, and none kept apart that it
    /// merges.
    #[test]
    fn equality_and_order_agree_with_the_reference() {
        // ω (and any level with ω in it, which is ≈ ω) is comparable only
        // with itself, as `le` documents.
        let reference_le = |a: &T, b: &T| match (reference_nf(a), reference_nf(b)) {
            (LevelNf::Omega, LevelNf::Omega) => true,
            (LevelNf::Omega, _) | (_, LevelNf::Omega) => false,
            (_, nb) => nb == reference_nf(&T::Max(Box::new(a.clone()), Box::new(b.clone()))),
        };
        for seed in 0..SEEDS {
            let mut r = Rng(seed ^ 0x5eed);
            // shallow trees over few variables, so equivalent pairs are common
            let ts: Vec<T> = (0..24).map(|_| { let omega = r.below(8) == 0; gen_level(&mut r, 3, omega) }).collect();
            for a in &ts {
                for b in &ts {
                    let (la, lb) = (build(a), build(b));
                    assert_eq!(la == lb, reference_nf(a) == reference_nf(b), "seed {seed}: {a:?} vs {b:?}");
                    assert_eq!(la.le(&lb), reference_le(a, b), "seed {seed}: {a:?} ≤ {b:?}");
                }
            }
        }
    }

    /// Substitution, instantiation and shifting commute with building: the
    /// canonical result is the normal form of the tree operation's result.
    #[test]
    fn substitutions_agree_with_the_reference() {
        for seed in 0..SEEDS {
            let mut r = Rng(seed.wrapping_mul(31) + 7);
            for _ in 0..20 {
                let omega = r.below(10) == 0;
                let t = gen_level(&mut r, 5, omega);
                let depth = r.below(3) as u32;
                let phi: Vec<T> = (0..r.below(6)).map(|_| { let omega = r.below(12) == 0; gen_level(&mut r, 3, omega) }).collect();
                let lphi: Vec<Level> = phi.iter().map(build).collect();
                let l = build(&t);
                assert_eq!(l.inst_at(&lphi, depth), build(&reference_inst(&t, &phi, depth)), "seed {seed} inst");
                // `subst_at` needs `phi` to cover every free variable
                let full: Vec<T> = (0..8).map(|i| phi.get(i).cloned().unwrap_or(T::Var(i as u32))).collect();
                let lfull: Vec<Level> = full.iter().map(build).collect();
                assert_eq!(l.subst_at(&lfull, depth), build(&reference_inst(&t, &full, depth)), "seed {seed} subst");
                let (by, cutoff) = (r.below(4) as u32, r.below(4) as u32);
                assert_eq!(l.shift(by, cutoff), build(&reference_shift(&t, by, cutoff)), "seed {seed} shift");
            }
        }
    }
}
