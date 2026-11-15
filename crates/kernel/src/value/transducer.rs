//! Bit transducers: Mealy machines over a word, iterated natively
//! (`docs/kernel/native-bitvector-values-design.md` §§4, 5).
//!
//! A fold over a `Vec`'s *length* whose step reads one bit from each of `a`
//! vector arguments and a state from a finitely enumerable type, and whose
//! one application is
//!
//! ```text
//! step k ih  x⃗ s  ⇝  cons( out(b⃗, s) , ih( tail(x⃗) , next(b⃗, s) ) )
//! ```
//!
//! with `out` and `next` closed, is a Mealy machine. What lives here is the
//! machine and nothing else: a table over the `2^a × |S|` combinations, and
//! the loops that run it over a word. How a step *came* to be tabulated is
//! the evaluator's probe (`eval/transduce.rs`); nothing in this module
//! evaluates, and nothing in it names a library type — which is what keeps
//! the arithmetic testable against a reference semantics ([`tests`]) and the
//! trusted part small, exactly as `value/algebra.rs` is for the `Nat`
//! classes.
//!
//! Three output algebras, because the library's folds have three shapes
//! (design §§4.1, 5):
//!
//! - **cons** — one bit per step onto the recursive result: `bxor`, `add`,
//!   `concat`, `take_low`, `repeat_bit`;
//! - **pass** — the recursive result unchanged, the bit only driving the
//!   state: `drop_low`;
//! - **finite** — a value of a finitely enumerable type built from the bit,
//!   the state and the recursive result: `is_zero_bits`, `xor_bits`;
//! - **scaled** — a `Nat`-run endomorphism `ih ↦ q·ih + r`, which is
//!   `AffineTree::Leaf` with a coefficient: `toNat`;
//! - **`Nat` state** — not a machine at all: `cons(f(x), ih(g(x)))` over a
//!   `Nat` argument, `ofNat`. The state has infinitely many values, so the
//!   step is not tabulated; `f` and `g` are [`NatRead`]s, eliminations read
//!   off the probe as closed data, and the word is computed from them
//!   ([`Transducer::run_nat`]).
//!
//! The direction is fixed by the recursion: index 0 — the `Vec`'s head, the
//! least significant bit — is the outermost step, which is the direction
//! carries run in. A **state** therefore flows from bit 0 upwards, and an
//! output that reads `ih` flows from the top bit down; `finite` and `scaled`
//! need both passes, which is why they run the state forward first and the
//! output backward after.

use crate::rc::Rc;

use heather_numeral::Numeral;

use super::algebra::{add_increments, AffineTree, Increment, Path, Proj};
use super::program::ContextProgram;

/// How many closed combinations of head bits and state one probe may
/// tabulate (design §4.2: `2^a × |S| ≤ 16`). It bounds the probe's own cost
/// — the probe evaluates the step once per combination — as well as the
/// table's size.
pub const TABLE_CAP: u32 = 16;

/// How many values a *state* type may have (design §4.1). A state is
/// enumerated by building every one of its values, so this is also the bound
/// on that construction.
pub const STATE_CAP: u32 = 16;

/// A value of a finitely enumerable type, as the choices that identify it.
///
/// Enumerability is the bit criterion widened (design §4.1): `Unit` is one
/// value, a `Sum` of enumerables is the sum of theirs, a `Σ` of enumerables
/// the product. The *shape* is all that is kept, because that is all that
/// distinguishes two values of such a type: the payloads are unit-like and
/// therefore proof-irrelevant. Reading a computed value back into one of
/// these is how the probe learns which state a step moved to.
#[derive(Clone, PartialEq, Eq)]
pub enum EnumVal {
    Triv,
    Inl(Rc<EnumVal>),
    Inr(Rc<EnumVal>),
    Pair(Rc<EnumVal>, Rc<EnumVal>),
}

impl std::fmt::Debug for EnumVal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EnumVal::Triv => f.write_str("⟨⟩"),
            EnumVal::Inl(v) => write!(f, "inl({v:?})"),
            EnumVal::Inr(v) => write!(f, "inr({v:?})"),
            EnumVal::Pair(a, b) => write!(f, "⟨{a:?}, {b:?}⟩"),
        }
    }
}

/// Where one of the step's arguments comes from, in the step's own argument
/// order. Read off the eliminator's **motive**, never off a definition
/// (design §4.2 step 2).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ArgMode {
    /// A vector the step projects a head bit and a tail from. The `u32` is
    /// its position among the peeled arguments, which is its bit's position
    /// in a table index.
    Peeled(u32),
    /// An argument of a finitely enumerable type the step passes on changed.
    /// The `u32` is its position among the state arguments.
    State(u32),
    /// An argument passed to `ih` unchanged.
    Carried,
}

/// What one application of the step makes of its recursive result.
#[derive(Clone, Debug)]
pub enum Output {
    /// `cons(bit, ih(…))`: `bits[i]` is the bit produced at combination `i`.
    Cons { bits: Vec<bool> },
    /// `ih(…)`: the bit drives the state and nothing else.
    Pass,
    /// A value of a finitely enumerable type: `table[i * values.len() + ih]`
    /// is the index of the value produced at combination `i` when the
    /// recursive result is `values[ih]`.
    Finite { values: Vec<EnumVal>, table: Vec<u32> },
    /// `ih ↦ q·ih + r`, with `q` and `r` closed run programs: `maps[i]` is
    /// `(q, r)` at combination `i`. `AffineTree::Leaf`'s increment with a
    /// coefficient (design §5).
    Scaled { maps: Vec<(Increment, Increment)> },
    /// `cons(f(x), ih(g(x)))` over a `Nat` argument `x` — `bitvec::ofNat`'s
    /// shape. `x` has infinitely many values, so there is no table: `f` and
    /// `g` are [`NatRead`]s, chains of classified `Nat` folds read off the
    /// probe as arithmetic, and the word is the bits of the orbit
    /// `x, g(x), g(g(x)), …` under `f` ([`Transducer::run_nat`]).
    NatState { bit: NatRead, next: NatRead },
}

/// A closed value of the shapes an affine fold's base and result take: a
/// natural, a bit — an injection over a canonical unit-like payload, the
/// criterion `eval/bits.rs` decides — or a pair of them.
#[derive(Clone, Debug)]
pub enum Datum {
    Nat(Increment),
    Bit(bool),
    Pair(Rc<Datum>, Rc<Datum>),
}

impl Datum {
    fn at(&self, path: &[Proj]) -> Option<&Datum> {
        let mut cur = self;
        for step in path {
            let Datum::Pair(fst, snd) = cur else { return None };
            cur = match step {
                Proj::Fst => fst,
                Proj::Snd => snd,
            };
        }
        Some(cur)
    }

    /// `tree[ih := self]`. A successor on anything but a natural is
    /// ill-typed and declines, as [`AffineTree::compose`] does.
    fn under(&self, tree: &AffineTree) -> Option<Datum> {
        Some(match tree {
            AffineTree::Lit { inc } => Datum::Nat(inc.clone()),
            AffineTree::Leaf { inc, path } => match (self.at(path)?, inc) {
                (found, None) => found.clone(),
                (Datum::Nat(n), Some(_)) => Datum::Nat(add_increments(inc, n)),
                _ => return None,
            },
            AffineTree::Pair(fst, snd) => {
                Datum::Pair(Rc::new(self.under(fst)?), Rc::new(self.under(snd)?))
            }
        })
    }
}

impl Datum {
    /// `tree^{|count|}[self]`. The general route is the tree's own power
    /// ([`AffineTree::iterate`]) instantiated at `self`; when the count and
    /// every increment fit a `u128`, [`Datum::iterated_small`] answers
    /// without building the powers, which is what keeps a `Nat`-state word
    /// at one pass of arithmetic per bit rather than `2·log₂ x`
    /// compositions.
    fn iterated(&self, tree: &AffineTree, count: &Rc<ContextProgram<()>>) -> Option<Datum> {
        if let Some(done) = self.iterated_small(tree, count) {
            return Some(done);
        }
        self.under(&tree.iterate(count)?)
    }

    /// The same value read off the tree as a **functional graph** on the
    /// datum's leaf positions: one step sends position `i` to a literal, or
    /// to the value at position `src(i)` plus `inc(i)`. After `c` steps,
    /// position `i` holds `base[src^c(i)] + Σ_{t<c} inc(src^t(i))`, or the
    /// literal the walk reaches first plus the increments before it. The
    /// walk visits at most one position per leaf before it repeats one,
    /// and a repeat is a cycle whose whole turns are skipped by one
    /// multiplication — so this is `O(leaves)` whatever `c` is.
    ///
    /// `None` is "not this route": a tree whose shape is not the datum's
    /// (a component copied whole into another place), a count or increment
    /// past `u128`, or ill-typed input — the general route then decides.
    /// The reference test checks it against [`AffineTree::iterate`].
    fn iterated_small(&self, tree: &AffineTree, count: &Rc<ContextProgram<()>>) -> Option<Datum> {
        enum Src {
            Lit(u128),
            From(usize, u128),
        }
        let c = count.len().as_u128()?;
        let mut leaves: Vec<(Path, &Datum)> = Vec::new();
        self.leaves(&mut Vec::new(), &mut leaves);
        let mut srcs = Vec::with_capacity(leaves.len());
        for (path, _) in &leaves {
            srcs.push(match tree.at_exact(path)? {
                AffineTree::Lit { inc } => Src::Lit(inc_count(inc)?),
                AffineTree::Leaf { inc, path: from } => {
                    let j = leaves.iter().position(|(p, _)| p == from)?;
                    Src::From(j, inc_count(inc)?)
                }
                AffineTree::Pair(..) => return None,
            });
        }
        // Each position's value after `c` steps: a base leaf and the
        // increments above it, or a literal the walk met first plus those.
        let mut out: Vec<Datum> = Vec::with_capacity(leaves.len());
        for i in 0..leaves.len() {
            let (mut cur, mut steps, mut acc) = (i, 0u128, 0u128);
            let mut seen: Vec<Option<(u128, u128)>> = vec![None; leaves.len()];
            let mut skipped = false;
            let value = loop {
                if steps == c {
                    break match leaves[cur].1 {
                        Datum::Nat(n) => Datum::Nat(nat_count(inc_count(n)?.checked_add(acc)?)),
                        Datum::Bit(b) if acc == 0 => Datum::Bit(*b),
                        _ => return None,
                    };
                }
                match srcs[cur] {
                    Src::Lit(n) => break Datum::Nat(nat_count(n.checked_add(acc)?)),
                    Src::From(j, inc) => {
                        if !skipped {
                            if let Some((s0, a0)) = seen[cur] {
                                // A cycle: skip its whole turns at once.
                                let (period, gain) = (steps - s0, acc - a0);
                                let turns = (c - steps) / period;
                                steps += turns * period;
                                acc = acc.checked_add(turns.checked_mul(gain)?)?;
                                skipped = true;
                                continue;
                            }
                            seen[cur] = Some((steps, acc));
                        }
                        acc = acc.checked_add(inc)?;
                        cur = j;
                        steps += 1;
                    }
                }
            };
            // A position's kind is the motive's, so a step cannot change it.
            let same_kind = matches!(
                (leaves[i].1, &value),
                (Datum::Nat(_), Datum::Nat(_)) | (Datum::Bit(_), Datum::Bit(_))
            );
            if !same_kind {
                return None;
            }
            out.push(value);
        }
        let mut next = out.into_iter();
        self.rebuilt(&mut next)
    }

    fn leaves<'d>(&'d self, at: &mut Path, out: &mut Vec<(Path, &'d Datum)>) {
        match self {
            Datum::Pair(fst, snd) => {
                at.push(Proj::Fst);
                fst.leaves(at, out);
                at.pop();
                at.push(Proj::Snd);
                snd.leaves(at, out);
                at.pop();
            }
            leaf => out.push((at.clone(), leaf)),
        }
    }

    /// `self`'s shape with its leaves taken from `next`, in [`Datum::leaves`]
    /// order.
    fn rebuilt(&self, next: &mut impl Iterator<Item = Datum>) -> Option<Datum> {
        Some(match self {
            Datum::Pair(fst, snd) => {
                let a = fst.rebuilt(next)?;
                let b = snd.rebuilt(next)?;
                Datum::Pair(Rc::new(a), Rc::new(b))
            }
            _ => next.next()?,
        })
    }
}

/// `Succ^n` as an increment.
fn nat_count(n: u128) -> Increment {
    (n != 0).then(|| ContextProgram::of_count((), &Numeral::from_u128(n)))
}

/// An increment's count, when it fits a `u128`.
fn inc_count(inc: &Increment) -> Option<u128> {
    match inc {
        None => Some(0),
        Some(p) => p.len().as_u128(),
    }
}

/// One elimination of a [`NatRead`]'s spine.
#[derive(Clone, Debug)]
pub enum ReadElim {
    /// `elim_Nat` whose step classified as the affine `tree`
    /// (`value/algebra.rs`), over the closed `base`. `first` is the
    /// innermost step at `k = 0` applied to `base`, present exactly when
    /// the class is not uniform — the step `eval/runs.rs` takes as written.
    Fold { tree: AffineTree, uniform: bool, base: Datum, first: Option<Datum> },
    Proj(Proj),
}

/// A function of a closed natural read off a probe value: the eliminations
/// a neutral at the state variable carries, innermost first, under `outer`
/// successors. Nothing in it is a closure, which is the point — it is
/// applied to a closed state without substituting into anything
/// (`eval/transduce.rs`, the `Nat`-state probe).
#[derive(Clone, Debug)]
pub struct NatRead {
    pub elims: Vec<ReadElim>,
    pub outer: Increment,
}

impl NatRead {
    /// The value at `x`, which is `Succ^{x}(Zero)`.
    pub fn apply(&self, x: &Increment) -> Option<Datum> {
        let mut cur = Datum::Nat(x.clone());
        for elim in &self.elims {
            cur = match elim {
                ReadElim::Proj(p) => cur.at(&[*p])?.clone(),
                ReadElim::Fold { tree, uniform, base, first } => {
                    let Datum::Nat(count) = &cur else { return None };
                    // `eval/runs.rs`'s two cases at a zero tail: uniform is
                    // `tree^c[base]`; peeled is `tree^{c-1}[s(0, base)]`.
                    let (start, count) = match (count, uniform) {
                        (None, _) => (base.clone(), None),
                        (Some(c), true) => (base.clone(), Some(Rc::clone(c))),
                        (Some(c), false) => {
                            (first.clone()?, ContextProgram::uncons(c).1)
                        }
                    };
                    match count {
                        None => start,
                        Some(c) => start.iterated(tree, &c)?,
                    }
                }
            };
        }
        if self.outer.is_some() {
            let Datum::Nat(n) = cur else { return None };
            cur = Datum::Nat(add_increments(&self.outer, &n));
        }
        Some(cur)
    }
}

/// A step tabulated over the closed combinations of its head bits and its
/// state.
#[derive(Clone, Debug)]
pub struct Transducer {
    /// The step's arguments, in order. `modes.len()` is the arity at which
    /// the fold fires.
    pub modes: Vec<ArgMode>,
    /// `a`: how many arguments are peeled. A combination index is
    /// `state * 2^a + bits`, `bits` bit `j` being peeled argument `j`.
    pub peeled: u32,
    /// Per peeled argument, the projection path from its type to the `Vec`
    /// inside it — a record's wrapper, empty when the argument *is* a
    /// vector (`eval/transduce.rs`'s module doc).
    pub slots: Vec<Vec<Proj>>,
    /// The same for the fold's result; empty for the non-vector outputs,
    /// which have no vector to find.
    pub out_slot: Vec<Proj>,
    /// The state enumeration — one entry per combination of the state
    /// arguments' values, in the order the index counts them. Exactly one
    /// entry (`EnumVal::Triv`, standing for no state at all) when the step
    /// has no state argument.
    pub states: Vec<EnumVal>,
    /// Per state argument, its own enumeration — what a state index is
    /// decomposed into when the residual fold has to be handed one.
    pub state_enums: Vec<Vec<EnumVal>>,
    /// `next[state * 2^a + bits]`: the state the step moves to.
    pub next: Vec<u32>,
    pub output: Output,
}

impl Transducer {
    /// How many combinations the table has.
    pub fn combinations(&self) -> usize {
        self.states.len() << self.peeled
    }

    fn index(&self, state: u32, bits: u32) -> usize {
        ((state as usize) << self.peeled) | bits as usize
    }

    /// The bits the peeled arguments present at position `i`, as a
    /// combination's low half.
    fn column(&self, words: &[u64], i: u32) -> u32 {
        let mut out = 0u32;
        for (j, w) in words.iter().enumerate() {
            out |= (((w >> i) & 1) as u32) << j;
        }
        out
    }

    /// The state sequence: `states[i]` is the state the machine is in when
    /// it reads bit `i`, and the returned value is the state it leaves in.
    /// Runs from bit 0 — the `Vec`'s head — upwards.
    fn run_states(&self, width: u32, words: &[u64], start: u32, out: &mut Vec<u32>) -> u32 {
        let mut state = start;
        for i in 0..width {
            out.push(state);
            state = self.next[self.index(state, self.column(words, i))];
        }
        state
    }

    /// **Cons**: the word produced over `width` bits, and the state left in.
    /// `words[j]` is peeled argument `j`'s bits, LSB = index 0.
    pub fn run_cons(&self, width: u32, words: &[u64], start: u32) -> Option<(u64, u32)> {
        let Output::Cons { bits } = &self.output else { return None };
        let mut state = start;
        let mut produced = 0u64;
        for i in 0..width {
            let entry = self.index(state, self.column(words, i));
            produced |= u64::from(bits[entry]) << i;
            state = self.next[entry];
        }
        Some((produced, state))
    }

    /// **Pass**: only the state moves.
    pub fn run_pass(&self, width: u32, words: &[u64], start: u32) -> u32 {
        let mut seen = Vec::new();
        self.run_states(width, words, start, &mut seen)
    }

    /// Whether combination `i` answers the same whatever the recursive
    /// result is. A finite fold whose step short-circuits — `is_zero_bits`
    /// at a set bit — has such a row, and reaching one settles the fold
    /// without the bits above it ever being read (design §5: the structural
    /// path's early exit must not be lost).
    pub fn finite_constant(&self, entry: usize) -> Option<u32> {
        let Output::Finite { values, table } = &self.output else { return None };
        let row = &table[entry * values.len()..(entry + 1) * values.len()];
        let first = *row.first()?;
        row.iter().all(|v| *v == first).then_some(first)
    }

    /// **Finite**: the value the fold produces, given the value `base` the
    /// fold at the tail produced. The state runs up from bit 0 and the
    /// output runs back down from the top, because the output at a bit reads
    /// the recursive result *above* it.
    pub fn run_finite(&self, width: u32, words: &[u64], start: u32, base: u32) -> Option<u32> {
        let Output::Finite { values, table } = &self.output else { return None };
        let mut seen = Vec::with_capacity(width as usize);
        self.run_states(width, words, start, &mut seen);
        let mut acc = base;
        for i in (0..width).rev() {
            let entry = self.index(seen[i as usize], self.column(words, i));
            acc = table[entry * values.len() + acc as usize];
        }
        Some(acc)
    }

    /// The same fold, stopping at the lowest bit whose row is constant: the
    /// answer, and how many bits it had to read. `None` for the recursive
    /// result means no such row was reached, and the caller owes the fold at
    /// the tail.
    pub fn run_finite_short(&self, width: u32, words: &[u64], base: Option<u32>) -> Option<(u32, u32)> {
        let Output::Finite { values, table } = &self.output else { return None };
        let mut entries = Vec::with_capacity(width as usize);
        let mut acc = None;
        for i in 0..width {
            let entry = self.index(0, self.column(words, i));
            entries.push(entry);
            if let Some(c) = self.finite_constant(entry) {
                acc = Some(c);
                break;
            }
        }
        let taken = entries.len() as u32;
        let mut out = match acc {
            Some(c) => {
                entries.pop();
                c
            }
            None => base?,
        };
        for entry in entries.iter().rev() {
            out = table[entry * values.len() + out as usize];
        }
        Some((out, taken))
    }

    /// **Scaled**: the endomorphism `ih ↦ q·ih + r` the whole fold is, as
    /// the composition of the per-bit ones from the top bit down. Horner's
    /// rule, with the increments kept as programs so no count overflows
    /// (`value/algebra.rs`'s reason, unchanged).
    pub fn run_scaled(&self, width: u32, words: &[u64], start: u32) -> Option<(Increment, Increment)> {
        let Output::Scaled { maps } = &self.output else { return None };
        let mut seen = Vec::with_capacity(width as usize);
        self.run_states(width, words, start, &mut seen);
        // The identity, `ih ↦ 1·ih + 0`.
        let mut acc: (Increment, Increment) = (Some(ContextProgram::run((), ONE)), None);
        for i in (0..width).rev() {
            let entry = self.index(seen[i as usize], self.column(words, i));
            acc = compose_affine(&maps[entry], &acc)?;
        }
        Some(acc)
    }

    /// **`Nat`-state**: the bits `f(x), f(g(x)), …` for `width` steps from
    /// `x`, and the state after the last. `None` when a bit is not a bit or
    /// a state not a natural — ill-typed input, declined.
    pub fn run_nat(&self, width: u32, x: &Increment) -> Option<(u64, Increment)> {
        let Output::NatState { bit, next } = &self.output else { return None };
        let mut word = 0u64;
        let mut state = x.clone();
        for i in 0..width {
            let Datum::Bit(b) = bit.apply(&state)? else { return None };
            word |= u64::from(b) << i;
            let Datum::Nat(n) = next.apply(&state)? else { return None };
            state = n;
        }
        Some((word, state))
    }
}

const ONE: std::num::NonZeroU64 = match std::num::NonZeroU64::new(1) {
    Some(one) => one,
    None => unreachable!(),
};

/// `q·n` as a program: the successor algebra `x ↦ Succ^q(x)` iterated `n`
/// times, which is exactly `value/algebra.rs`'s run multiplication.
pub fn scale(q: &Increment, n: &Increment) -> Increment {
    let (Some(q), Some(n)) = (q, n) else { return None };
    let by = super::algebra::AffineTree::Leaf { inc: Some(Rc::clone(q)), path: Vec::new() };
    match by.iterate(n) {
        Some(super::algebra::AffineTree::Leaf { inc, .. }) => inc,
        _ => None,
    }
}

/// `outer ∘ inner`: `(q, r) ∘ (q', r') = (q·q', q·r' + r)`.
fn compose_affine(
    outer: &(Increment, Increment),
    inner: &(Increment, Increment),
) -> Option<(Increment, Increment)> {
    let (q, r) = outer;
    let (q2, r2) = inner;
    Some((scale(q, q2), add_increments(&scale(q, r2), r)))
}

#[cfg(test)]
mod tests {
    //! The reference semantics: a transducer is a function on a *list* of
    //! bit columns, applied one step at a time, and the native loops must
    //! agree with that at every width. This is the property the design's §8
    //! asks for ("the native loop agrees with iterating the probed table one
    //! bit at a time"), stated where it can be tested without an evaluator.

    use super::*;

    fn lcg(seed: &mut u64) -> u64 {
        *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        *seed >> 33
    }

    fn random(seed: &mut u64, peeled: u32, states: u32, output: u8) -> Transducer {
        let combos = (states as usize) << peeled;
        let next: Vec<u32> = (0..combos).map(|_| (lcg(seed) % u64::from(states)) as u32).collect();
        let output = match output {
            0 => Output::Cons { bits: (0..combos).map(|_| lcg(seed) & 1 == 1).collect() },
            1 => Output::Pass,
            2 => Output::Finite {
                values: (0..3).map(|_| EnumVal::Triv).collect(),
                table: (0..combos * 3).map(|_| (lcg(seed) % 3) as u32).collect(),
            },
            _ => Output::Scaled {
                maps: (0..combos)
                    .map(|_| {
                        let q = std::num::NonZeroU64::new(lcg(seed) % 3 + 1)
                            .map(|c| ContextProgram::run((), c));
                        let r = std::num::NonZeroU64::new(lcg(seed) % 3)
                            .map(|c| ContextProgram::run((), c));
                        (q, r)
                    })
                    .collect(),
            },
        };
        Transducer {
            modes: (0..peeled).map(ArgMode::Peeled).collect(),
            peeled,
            slots: vec![Vec::new(); peeled as usize],
            out_slot: Vec::new(),
            states: (0..states).map(|_| EnumVal::Triv).collect(),
            state_enums: Vec::new(),
            next,
            output,
        }
    }

    fn count(inc: &Increment) -> u128 {
        fn go(p: &Rc<ContextProgram<()>>) -> u128 {
            match &**p {
                ContextProgram::Run { count, .. } => u128::from(count.get()),
                ContextProgram::Compose { outer, inner, .. } => go(outer) + go(inner),
            }
        }
        inc.as_ref().map_or(0, go)
    }

    /// One step at a time, the definition the class is meant to denote.
    fn step_by_step(t: &Transducer, width: u32, words: &[u64], start: u32) -> (u64, u32, Vec<usize>) {
        let mut state = start;
        let mut produced = 0u64;
        let mut entries = Vec::new();
        for i in 0..width {
            let mut col = 0u32;
            for (j, w) in words.iter().enumerate() {
                col |= (((w >> i) & 1) as u32) << j;
            }
            let entry = ((state as usize) << t.peeled) | col as usize;
            entries.push(entry);
            if let Output::Cons { bits } = &t.output {
                produced |= u64::from(bits[entry]) << i;
            }
            state = t.next[entry];
        }
        (produced, state, entries)
    }

    #[test]
    fn the_cons_loop_is_the_step_taken_one_bit_at_a_time() {
        let mut seed = 3;
        for _ in 0..60 {
            let peeled = (lcg(&mut seed) % 3) as u32;
            let states = (lcg(&mut seed) % 4 + 1) as u32;
            let t = random(&mut seed, peeled, states, 0);
            let words: Vec<u64> = (0..peeled).map(|_| lcg(&mut seed)).collect();
            for width in [0u32, 1, 2, 7, 63, 64] {
                let start = (lcg(&mut seed) % u64::from(states)) as u32;
                let (bits, end, _) = step_by_step(&t, width, &words, start);
                assert_eq!(t.run_cons(width, &words, start), Some((bits, end)), "width {width}");
            }
        }
    }

    #[test]
    fn the_pass_loop_moves_the_state_and_nothing_else() {
        let mut seed = 5;
        for _ in 0..40 {
            let peeled = (lcg(&mut seed) % 3) as u32;
            let states = (lcg(&mut seed) % 4 + 1) as u32;
            let t = random(&mut seed, peeled, states, 1);
            let words: Vec<u64> = (0..peeled).map(|_| lcg(&mut seed)).collect();
            for width in [0u32, 1, 5, 64] {
                let start = (lcg(&mut seed) % u64::from(states)) as u32;
                let (_, end, _) = step_by_step(&t, width, &words, start);
                assert_eq!(t.run_pass(width, &words, start), end);
            }
        }
    }

    #[test]
    fn the_finite_loop_folds_from_the_top_bit_down() {
        let mut seed = 9;
        for _ in 0..40 {
            let peeled = (lcg(&mut seed) % 3) as u32;
            let states = (lcg(&mut seed) % 3 + 1) as u32;
            let t = random(&mut seed, peeled, states, 2);
            let Output::Finite { values, table } = &t.output else { unreachable!() };
            let words: Vec<u64> = (0..peeled).map(|_| lcg(&mut seed)).collect();
            for width in [0u32, 1, 3, 64] {
                let start = (lcg(&mut seed) % u64::from(states)) as u32;
                let (_, _, entries) = step_by_step(&t, width, &words, start);
                let base = (lcg(&mut seed) % 3) as u32;
                // The step's own recursion: the outermost application is at
                // bit 0 and reads the result of everything above it.
                let mut want = base;
                for entry in entries.iter().rev() {
                    want = table[entry * values.len() + want as usize];
                }
                assert_eq!(t.run_finite(width, &words, start, base), Some(want));
            }
        }
    }

    #[test]
    fn the_short_finite_loop_answers_what_the_long_one_does() {
        // The early exit must be an exit, not a different verdict.
        let mut seed = 29;
        for _ in 0..40 {
            let peeled = (lcg(&mut seed) % 3) as u32;
            let t = random(&mut seed, peeled, 1, 2);
            let words: Vec<u64> = (0..peeled).map(|_| lcg(&mut seed)).collect();
            for width in [0u32, 1, 3, 9, 64] {
                let base = (lcg(&mut seed) % 3) as u32;
                let long = t.run_finite(width, &words, 0, base).expect("finite");
                let (short, read) =
                    t.run_finite_short(width, &words, Some(base)).expect("finite");
                assert_eq!(long, short, "width {width}");
                assert!(read <= width);
                // When it stopped early the base was never needed.
                if read < width {
                    let (other, _) = t.run_finite_short(read, &words, None).expect("finite");
                    assert_eq!(other, short);
                }
            }
        }
    }

    #[test]
    fn the_scaled_loop_is_horner() {
        let mut seed = 13;
        for _ in 0..40 {
            let peeled = (lcg(&mut seed) % 2) as u32;
            let states = (lcg(&mut seed) % 3 + 1) as u32;
            let t = random(&mut seed, peeled, states, 3);
            let Output::Scaled { maps } = &t.output else { unreachable!() };
            let words: Vec<u64> = (0..peeled).map(|_| lcg(&mut seed)).collect();
            for width in [0u32, 1, 2, 5, 12] {
                let start = (lcg(&mut seed) % u64::from(states)) as u32;
                let (_, _, entries) = step_by_step(&t, width, &words, start);
                let base: u128 = 7;
                let mut want = base;
                for entry in entries.iter().rev() {
                    let (q, r) = &maps[*entry];
                    want = count(q) * want + count(r);
                }
                let (q, r) = t.run_scaled(width, &words, start).expect("scaled");
                assert_eq!(count(&q) * base + count(&r), want, "width {width}");
            }
        }
    }

    #[test]
    fn a_width_of_zero_is_the_identity_in_every_output_mode() {
        let mut seed = 17;
        for output in 0..4u8 {
            let t = random(&mut seed, 2, 2, output);
            assert_eq!(t.run_pass(0, &[0, 0], 1), 1);
            if matches!(t.output, Output::Cons { .. }) {
                assert_eq!(t.run_cons(0, &[0, 0], 1), Some((0, 1)));
            }
            if matches!(t.output, Output::Finite { .. }) {
                assert_eq!(t.run_finite(0, &[0, 0], 1, 2), Some(2));
            }
            if matches!(t.output, Output::Scaled { .. }) {
                let (q, r) = t.run_scaled(0, &[0, 0], 1).expect("scaled");
                assert_eq!((count(&q), count(&r)), (1, 0));
            }
        }
    }

    /// A datum as `(is a bit, value)` per leaf, for comparing.
    fn flat(d: &Datum, out: &mut Vec<(bool, u128)>) {
        match d {
            Datum::Pair(a, b) => {
                flat(a, out);
                flat(b, out);
            }
            Datum::Nat(n) => out.push((false, inc_count(n).expect("small"))),
            Datum::Bit(b) => out.push((true, u128::from(*b))),
        }
    }

    #[test]
    fn the_functional_graph_route_is_the_trees_own_power() {
        // Random windows of naturals and bits, random affine steps of the
        // window's own shape, random counts small and large: the
        // closed-form walk must agree with `AffineTree::iterate` and
        // instantiation, which `value/algebra.rs` tests against one-step
        // iteration.
        let nat = |n: u64| Datum::Nat(nat_count(u128::from(n)));
        let pair = |a: Datum, b: Datum| Datum::Pair(Rc::new(a), Rc::new(b));
        let mut seed = 0x5eed_u64;
        let shapes: Vec<Datum> = vec![
            pair(nat(0), nat(0)),
            pair(Datum::Bit(false), Datum::Bit(true)),
            pair(nat(3), pair(nat(1), nat(4))),
            pair(Datum::Bit(true), pair(nat(2), Datum::Bit(false))),
        ];
        let mut agreed = 0;
        for _ in 0..400 {
            let base = shapes[(lcg(&mut seed) % shapes.len() as u64) as usize].clone();
            let mut leaves = Vec::new();
            base.leaves(&mut Vec::new(), &mut leaves);
            let kinds: Vec<(Path, bool)> =
                leaves.iter().map(|(p, d)| (p.clone(), matches!(d, Datum::Bit(_)))).collect();
            let inc = |seed: &mut u64| nat_count(u128::from(lcg(seed) % 3));
            // A tree of the base's shape, each leaf a literal or a copy of a
            // position of its own kind.
            fn build(d: &Datum, at: &mut Path, kinds: &[(Path, bool)], seed: &mut u64,
                     inc: &dyn Fn(&mut u64) -> Increment) -> AffineTree {
                match d {
                    Datum::Pair(a, b) => {
                        at.push(Proj::Fst);
                        let x = build(a, at, kinds, seed, inc);
                        at.pop();
                        at.push(Proj::Snd);
                        let y = build(b, at, kinds, seed, inc);
                        at.pop();
                        AffineTree::Pair(Box::new(x), Box::new(y))
                    }
                    leaf => {
                        let bit = matches!(leaf, Datum::Bit(_));
                        if !bit && lcg(seed) % 4 == 0 {
                            return AffineTree::Lit { inc: inc(seed) };
                        }
                        let same: Vec<&Path> =
                            kinds.iter().filter(|(_, b)| *b == bit).map(|(p, _)| p).collect();
                        let from = same[(lcg(seed) % same.len() as u64) as usize].clone();
                        AffineTree::Leaf { inc: if bit { None } else { inc(seed) }, path: from }
                    }
                }
            }
            let tree = build(&base, &mut Vec::new(), &kinds, &mut seed, &inc);
            let c = match lcg(&mut seed) % 3 {
                0 => lcg(&mut seed) % 9 + 1,
                1 => lcg(&mut seed) % 300 + 1,
                _ => (lcg(&mut seed) << 20) | 1,
            };
            let count = ContextProgram::of_count((), &Numeral::from_u64(c));
            let fast = base.iterated_small(&tree, &count).expect("small route");
            let slow = base.under(&tree.iterate(&count).expect("iterates")).expect("instantiates");
            let (mut a, mut b) = (Vec::new(), Vec::new());
            flat(&fast, &mut a);
            flat(&slow, &mut b);
            assert_eq!(a, b, "tree {tree:?} at {c}");
            agreed += 1;
        }
        assert_eq!(agreed, 400);
    }

    #[test]
    fn xor_is_two_peeled_arguments_and_no_state() {
        // The table design §4.4 predicts for `bxor`: four entries, output
        // the exclusive or of the two bits, one state throughout.
        let t = Transducer {
            modes: vec![ArgMode::Peeled(0), ArgMode::Peeled(1)],
            peeled: 2,
            slots: vec![Vec::new(), Vec::new()],
            out_slot: Vec::new(),
            states: vec![EnumVal::Triv],
            state_enums: Vec::new(),
            next: vec![0; 4],
            output: Output::Cons { bits: vec![false, true, true, false] },
        };
        let (bits, _) = t.run_cons(64, &[0xdead_beef_cafe_f00d, 0x0123_4567_89ab_cdef], 0).unwrap();
        assert_eq!(bits, 0xdead_beef_cafe_f00d ^ 0x0123_4567_89ab_cdef);
    }

    #[test]
    fn a_carry_is_one_bit_of_state() {
        // `add_bits`: eight entries, the state the carry, the output the sum
        // bit. The table is not *recognized* as addition anywhere — it is
        // iterated — and this row is the evidence that iterating it is.
        let mut next = vec![0u32; 8];
        let mut bits = vec![false; 8];
        for carry in 0..2u32 {
            for combo in 0..4u32 {
                let (a, b) = (combo & 1, (combo >> 1) & 1);
                let total = a + b + carry;
                let entry = ((carry as usize) << 2) | combo as usize;
                bits[entry] = total & 1 == 1;
                next[entry] = total >> 1;
            }
        }
        let t = Transducer {
            modes: vec![ArgMode::Peeled(0), ArgMode::Peeled(1), ArgMode::State(0)],
            peeled: 2,
            slots: vec![Vec::new(), Vec::new()],
            out_slot: Vec::new(),
            states: vec![EnumVal::Triv, EnumVal::Triv],
            state_enums: vec![vec![EnumVal::Triv, EnumVal::Triv]],
            next,
            output: Output::Cons { bits },
        };
        let (x, y) = (0x0123_4567_89ab_cdefu64, 0xfedc_ba98_7654_3210u64);
        let (sum, carry) = t.run_cons(64, &[x, y], 0).unwrap();
        assert_eq!(sum, x.wrapping_add(y));
        assert_eq!(carry, u32::from(x.checked_add(y).is_none()));
    }
}
