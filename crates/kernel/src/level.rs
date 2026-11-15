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
//! pass.
//!
//! # One word
//!
//! A `Level` is one machine word, `Copy`, compared and hashed as an integer
//! (`issues/kernel-level-eight-bytes.md`). The forms terms are made of are
//! spelled in the word itself: a constant `k`, `n + ℓ` (so `ℓ`), and `ω`.
//! Every other level, a join of two or more components or an offset too
//! large for the word, is a [`Join`] in a process-wide table and the word is
//! its index ([`intern`]). A level has exactly one word: the table holds
//! each join once, and a level the word can spell is never put in the table.
//!
//! The table only grows. It holds the distinct joins the process has built,
//! which are a property of the declarations checked (a join is written by a
//! universe-polymorphic signature, not by a term's size), and an entry is
//! one small allocation that is never freed. An index is meaningful only in
//! the process that made it, so nothing that leaves the process may read
//! the word: [`Level::parts`] is the level's spelling, and `Hash` hashes
//! that spelling.
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

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::hash::{Hash, Hasher};
use std::num::NonZeroU64;
use std::sync::RwLock;

/// A universe variable: de Bruijn index into the universe context `L`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UnivVar(pub u32);

/// Universe levels `l := ℓ | 0 | 1 + l | l ⊔ l' | ω`, held as the canonical
/// representative of their ≈-class in one word (see the module docs).
///
/// [`Level::Zero`], [`Level::Var`] and [`Level::Omega`] are written directly
/// and `Zero` and `Omega` are matched directly; every other level is built
/// through the constructors, which is what keeps every `Level` canonical.
/// Read a level's components with [`Level::parts`].
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Level(NonZeroU64);

// The word: a tag in the low three bits (never zero, so `Option<Level>` is a
// word too) and a payload above it.

const TAG_BITS: u32 = 3;
/// The constant `k`, for `k < 2^61`: the payload is `k`.
const CONST: u64 = 1;
/// `n + ℓ`, for `n < 2^29`: the payload is `ℓ` in its low 32 bits and `n`
/// above them.
const LIFT: u64 = 2;
/// Any other finite level: the payload is its index in the join table.
const JOIN: u64 = 3;
const OMEGA: u64 = 4;

const CONST_LIMIT: u64 = 1 << (64 - TAG_BITS);
const OFFSET_LIMIT: u64 = 1 << (64 - TAG_BITS - 32);

/// What a word spells.
enum Form {
    Const(u64),
    /// `n + ℓ`.
    Lift(UnivVar, u64),
    Join(&'static Join),
    Omega,
}

/// `konst ⊔ ⨆ (n_i + ℓ_i)` after `adjust`: `vars` strictly ascending by
/// variable, `konst` `None` exactly when some `n_i ≥ konst`. Invariant: no
/// word spells it by itself (see `Level::from_count`).
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Join {
    konst: Option<u64>,
    vars: Box<[(UnivVar, u64)]>,
}

/// The joins of the process, by index and by content.
struct Joins {
    all: Vec<&'static Join>,
    ids: BTreeMap<&'static Join, u32>,
}

static JOINS: RwLock<Joins> = RwLock::new(Joins { all: Vec::new(), ids: BTreeMap::new() });

thread_local! {
    /// What this thread has read of [`JOINS`]: a prefix of `all` and the
    /// joins it interned or met in `ids`. Entries are never changed or
    /// removed, so a copy is never stale for an index it holds, and a
    /// thread takes the lock only for a join it has not seen.
    static SEEN: RefCell<Joins> = const { RefCell::new(Joins { all: Vec::new(), ids: BTreeMap::new() }) };
}

/// The word of `join`, which no word spells by itself: its index in the
/// table, entered on first sight. Equal joins get equal indices, which is
/// what makes `==` on words equivalence.
fn intern(join: Join) -> Level {
    let id = SEEN.with(|seen| {
        let mut seen = seen.borrow_mut();
        if let Some(&id) = seen.ids.get(&join) {
            return id;
        }
        let (kept, id) = {
            // A panic under the lock leaves the table as it was before the
            // entry or with the entry whole, so a poisoned lock is usable.
            let mut joins = JOINS.write().unwrap_or_else(|e| e.into_inner());
            match joins.ids.get_key_value(&join) {
                Some((&kept, &id)) => (kept, id),
                None => {
                    let id = u32::try_from(joins.all.len()).expect("more than 2^32 distinct universe joins");
                    let kept: &'static Join = Box::leak(Box::new(join));
                    joins.ids.insert(kept, id);
                    joins.all.push(kept);
                    (kept, id)
                }
            }
        };
        seen.ids.insert(kept, id);
        id
    });
    Level::word(JOIN, u64::from(id))
}

/// The join a [`JOIN`] word indexes. Out of line: no run measured holds a
/// join, and the three forms that are a word must not pay for this one's
/// frame ([`Level::form`]).
#[inline(never)]
fn interned(id: u64) -> &'static Join {
    SEEN.with(|seen| {
        let mut seen = seen.borrow_mut();
        if let Some(&join) = seen.all.get(id as usize) {
            return join;
        }
        let joins = JOINS.read().unwrap_or_else(|e| e.into_inner());
        let have = seen.all.len();
        seen.all.extend_from_slice(&joins.all[have..]);
        seen.all[id as usize]
    })
}

/// The variable terms of a level's canonical spelling, `(ℓ, n)` for `n + ℓ`,
/// in ascending variable order. See [`Level::parts`].
#[derive(Clone)]
pub struct Parts {
    one: Option<(UnivVar, u64)>,
    rest: std::slice::Iter<'static, (UnivVar, u64)>,
}

impl Iterator for Parts {
    type Item = (UnivVar, u64);

    #[inline]
    fn next(&mut self) -> Option<(UnivVar, u64)> {
        self.one.take().or_else(|| self.rest.next().copied())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = self.one.is_some() as usize + self.rest.len();
        (n, Some(n))
    }
}

impl ExactSizeIterator for Parts {}

/// By spelling, not by word: a join's index depends on the order the process
/// met its joins in, and a hash may be kept past the process.
impl Hash for Level {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self.form() {
            Form::Join(join) => {
                state.write_u64(JOIN);
                join.hash(state);
            }
            _ => state.write_u64(self.0.get()),
        }
    }
}

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
    fn add(&mut self, l: Level, by: u64) {
        match l.form() {
            Form::Const(k) => self.konst = self.konst.max(offset_add(k, by)),
            Form::Lift(v, n) => self.vars.push((v, offset_add(n, by))),
            Form::Join(j) => {
                if let Some(k) = j.konst {
                    self.konst = self.konst.max(offset_add(k, by));
                }
                self.vars.extend(j.vars.iter().map(|&(v, n)| (v, offset_add(n, by))));
            }
            Form::Omega => self.omega = true,
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

// `Zero`, `Var` and `Omega` keep the names they had as an enum's variants:
// they are written at every site that builds a sort.
#[allow(non_upper_case_globals, non_snake_case)]
impl Level {
    pub const Zero: Level = Level::word(CONST, 0);

    /// Checker-internal; see the module docs.
    pub const Omega: Level = Level::word(OMEGA, 0);

    /// The level `ℓ`.
    pub const fn Var(v: UnivVar) -> Level {
        Level::word(LIFT, v.0 as u64)
    }
}

impl Level {
    const fn word(tag: u64, payload: u64) -> Level {
        match NonZeroU64::new(payload << TAG_BITS | tag) {
            Some(word) => Level(word),
            None => panic!("a level's tag is never zero"),
        }
    }

    #[inline]
    fn form(self) -> Form {
        let word = self.0.get();
        let payload = word >> TAG_BITS;
        match word & ((1 << TAG_BITS) - 1) {
            CONST => Form::Const(payload),
            LIFT => Form::Lift(UnivVar(payload as u32), payload >> 32),
            JOIN => Form::Join(interned(payload)),
            _ => Form::Omega,
        }
    }

    /// `1 + l`.
    pub fn succ(l: Level) -> Level {
        l.plus(1)
    }

    /// `by + l`: `by` successors, in constant time.
    pub fn plus(&self, by: u64) -> Level {
        if by == 0 {
            return *self;
        }
        match self.form() {
            Form::Const(k) => Level::lift(None, offset_add(k, by)),
            Form::Lift(v, n) => Level::lift(Some(v), offset_add(n, by)),
            Form::Join(_) => {
                let mut c = Count::new(0);
                c.add(*self, by);
                c.finish()
            }
            Form::Omega => Level::Omega,
        }
    }

    /// `a ⊔ b`. With canonical levels there is one spelling of the result,
    /// so this and [`Level::join`] are the same operation.
    pub fn max(a: Level, b: Level) -> Level {
        if a == Level::Omega || b == Level::Omega {
            return Level::Omega;
        }
        if a == Level::Zero || a == b {
            return b;
        }
        if b == Level::Zero {
            return a;
        }
        let mut c = Count::new(0);
        c.add(a, 0);
        c.add(b, 0);
        c.finish()
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

    /// `by + base` (`base` absent for `0`) in its canonical form: the word
    /// that spells it when one does.
    fn lift(base: Option<UnivVar>, by: u64) -> Level {
        match base {
            None if by < CONST_LIMIT => Level::word(CONST, by),
            Some(v) if by < OFFSET_LIMIT => Level::word(LIFT, by << 32 | u64::from(v.0)),
            None => intern(Join { konst: Some(by), vars: Box::new([]) }),
            Some(v) => intern(Join { konst: None, vars: Box::new([(v, by)]) }),
        }
    }

    /// The canonical form of `adjust(konst, vars)`, `vars` strictly
    /// ascending: with `lift`, the only place a join is interned, and never
    /// for a level a word spells.
    fn from_count(konst: u64, vars: Vec<(UnivVar, u64)>) -> Level {
        let dominated = vars.iter().any(|&(_, n)| konst <= n);
        match (dominated, vars.as_slice()) {
            (_, []) => Level::lift(None, konst),
            (true, [(v, n)]) => Level::lift(Some(*v), *n),
            _ => intern(Join {
                konst: (!dominated).then_some(konst),
                vars: vars.into_boxed_slice(),
            }),
        }
    }

    /// The canonical spelling's components: `None` for `ω`, else the
    /// constant part (absent when some variable term dominates it) and the
    /// variable terms. `0` is `(Some(0), [])` and `ℓ` is `(None, [(ℓ, 0)])`.
    #[inline]
    pub fn parts(&self) -> Option<(Option<u64>, Parts)> {
        let only = |konst: Option<u64>, one: Option<(UnivVar, u64)>| {
            Some((konst, Parts { one, rest: [].iter() }))
        };
        match self.form() {
            Form::Const(k) => only(Some(k), None),
            Form::Lift(v, n) => only(None, Some((v, n))),
            Form::Join(j) => Some((j.konst, Parts { one: None, rest: j.vars.iter() })),
            Form::Omega => None,
        }
    }

    /// The level as a closed constant, if it is one. Every variable-free
    /// level is: `2 ⊔ 1` is `2`.
    pub fn as_constant(&self) -> Option<u64> {
        match self.form() {
            Form::Const(k) => Some(k),
            Form::Join(j) if j.vars.is_empty() => j.konst,
            _ => None,
        }
    }

    /// Whether every variable the level mentions satisfies `pred`.
    fn vars_all(&self, mut pred: impl FnMut(UnivVar) -> bool) -> bool {
        match self.form() {
            Form::Const(_) | Form::Omega => true,
            Form::Lift(v, _) => pred(v),
            Form::Join(j) => j.vars.iter().all(|&(v, _)| pred(v)),
        }
    }

    /// Replace each variable `ℓ` by `f(ℓ)`, as the level algebra's
    /// homomorphism: `n + ℓ` becomes `n + f(ℓ)`, joined with the constant.
    fn map_vars(&self, f: impl Fn(UnivVar) -> Level) -> Level {
        match self.form() {
            Form::Const(_) | Form::Omega => *self,
            Form::Lift(v, n) => f(v).plus(n),
            Form::Join(j) => {
                let mut c = Count::new(j.konst.unwrap_or(0));
                for &(v, n) in j.vars.iter() {
                    c.add(f(v), n);
                }
                c.finish()
            }
        }
    }

    /// Well-formedness `L ⊢ l : Level`: every variable is in scope and `ω`
    /// does not occur (`ω` is never programmer-writable).
    pub fn well_formed(&self, univ_ctx_len: u32) -> bool {
        *self != Level::Omega && self.vars_all(|v| v.0 < univ_ctx_len)
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
    /// `ω ≈ ω` only). Levels are canonical and each has one word, so this
    /// is equality of words.
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
        if *self == Level::Omega || *other == Level::Omega {
            return false;
        }
        *other == Level::max(*self, *other)
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
            return *self;
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
            return *self;
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
            return *self;
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
    /// once had (see `docs/kernel/ch05-06-lemma-audit.md`, §Static Code),
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

    fn is_join(l: Level) -> bool {
        matches!(l.form(), Form::Join(_))
    }

    #[test]
    fn level_is_one_word() {
        assert_eq!(std::mem::size_of::<Level>(), 8);
        assert_eq!(std::mem::size_of::<Option<Level>>(), 8);
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

    /// A word spells the level whenever one can, so the table holds only
    /// genuine joins (and huge offsets).
    #[test]
    fn words_are_preferred() {
        assert!(matches!(Level::constant(0), Level::Zero));
        assert!(!is_join(Level::constant(5)));
        assert!(!is_join(Level::max(Level::constant(1), Level::constant(5))));
        assert!(!is_join(Level::max(var(3), Level::succ(var(3)))));
        assert!(!is_join(var(u32::MAX).plus(OFFSET_LIMIT - 1)));
        assert!(is_join(Level::max(var(0), Level::constant(1))));
        assert!(is_join(Level::max(var(0), var(1))));
        // a join that collapses back to one component returns to inline
        let j = Level::max(var(0), var(1));
        assert_eq!(j.subst(&[Level::Zero, Level::Zero]), Level::Zero);
        assert_eq!(j.subst(&[var(0), var(0)]), var(0));
    }

    /// Offsets past what the word holds leave it and stay exact.
    #[test]
    fn large_offsets_are_exact() {
        let edge = CONST_LIMIT - 1;
        let top = Level::constant(edge);
        assert!(!is_join(top));
        let past = Level::succ(top);
        assert!(is_join(past));
        assert_eq!(past, Level::constant(edge + 1));
        assert_ne!(past, top);
        assert_eq!(past.as_constant(), Some(edge + 1));
        assert_eq!(past.plus(3).as_constant(), Some(edge + 4));
        assert!(top.le(&past) && !past.le(&top));
        let edge = OFFSET_LIMIT - 1;
        assert!(!is_join(var(2).plus(edge)));
        let v = var(2).plus(edge + 7);
        assert!(is_join(v));
        assert_eq!(v, Level::succ(var(2).plus(edge + 6)));
        assert_ne!(v, var(3).plus(edge + 7));
        assert_eq!(Level::max(v, Level::constant(edge)), v);
        assert_eq!(v.normalize().canonical(), v);
        assert_eq!(v.subst(&[var(0), var(1), Level::Zero]), Level::constant(edge + 7));
    }

    /// A variable and its offset do not run into each other in the word.
    #[test]
    fn the_word_keeps_variable_and_offset_apart() {
        for v in [0, 1, 7, u32::MAX - 1, u32::MAX] {
            for n in [0, 1, 2, OFFSET_LIMIT - 1, OFFSET_LIMIT, u64::from(u32::MAX) + 9] {
                let l = var(v).plus(n);
                let (konst, vars) = l.parts().unwrap();
                assert_eq!((konst, vars.collect::<Vec<_>>()), (None, vec![(UnivVar(v), n)]));
            }
        }
        assert_eq!(Level::Var(UnivVar(0)), Level::of_parts(None, [(UnivVar(0), 0)]));
        assert_ne!(Level::Var(UnivVar(0)), Level::Zero);
        assert_ne!(Level::Var(UnivVar(1)), Level::constant(1));
    }

    /// One join has one word, on whichever thread it is built or read, and
    /// a hash is of the spelling: threads that meet joins in different
    /// orders agree on both.
    #[test]
    fn joins_are_shared_between_threads() {
        use std::collections::hash_map::DefaultHasher;
        let hash = |l: Level| {
            let mut h = DefaultHasher::new();
            l.hash(&mut h);
            h.finish()
        };
        let build = |order: Vec<u32>| {
            order.into_iter().map(|i| (i, Level::max(var(900 + i), var(950 + 2 * i).plus(u64::from(i))))).collect::<Vec<_>>()
        };
        let forward: Vec<u32> = (0..40).collect();
        let backward: Vec<u32> = (0..40).rev().collect();
        let (a, b) = std::thread::scope(|s| {
            let a = s.spawn(|| build(forward.clone()));
            let b = s.spawn(|| build(backward.clone()));
            (a.join().unwrap(), b.join().unwrap())
        });
        // Read here, on a thread that built none of them.
        for (i, l) in &a {
            let (_, twin) = b.iter().find(|(j, _)| j == i).unwrap();
            assert_eq!(l, twin);
            assert_eq!(hash(*l), hash(*twin));
            let (konst, vars) = l.parts().unwrap();
            assert_eq!(konst, None);
            assert_eq!(vars.collect::<Vec<_>>(), vec![(UnivVar(900 + i), 0), (UnivVar(950 + 2 * i), u64::from(*i))]);
        }
        let distinct: std::collections::BTreeSet<u64> = a.iter().map(|(_, l)| l.0.get()).collect();
        assert_eq!(distinct.len(), a.len());
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
