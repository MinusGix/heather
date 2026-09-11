//! Successor-affine algebras, iterated over run programs.
//!
//! A `Nat` fold whose step does nothing to its induction hypothesis but
//! rearrange its components and put successors on them —
//! `λ k ih. su^q ih` (`add`, `twice`), `λ k ih. add(ih, a)` (`mul` by a
//! run), `λ k ih. ⟨su (π₁ ih), π₀ ih⟩` (the course-of-values window of
//! `half`) — is a function on tuples of naturals that can be iterated `c`
//! times without visiting `c` steps: it is an [`AffineTree`], iteration is
//! composition, and composition over a [`ContextProgram`] is one
//! multiplication per run and one composition per composed node.
//!
//! Nothing here knows how a step came to be classified as a tree; that is
//! the evaluator's probe (`eval/probe.rs`). Nothing here evaluates: the
//! tree is a piece of arithmetic with a reference semantics ([`tests`]),
//! which is what makes it the trusted part small.
//!
//! Increments are programs, not integers: a run over `u64::MAX` successors
//! and another merge into one saturated run when they fit and compose
//! otherwise ([`ContextProgram::append`]), so no count overflows and no
//! iteration has to be declined for size.

use std::collections::HashMap;
use std::sync::Arc as Rc;

use super::program::ContextProgram;

/// A successor program: `Succ^{|p|}`. `None` is no successors.
pub type Increment = Option<Rc<ContextProgram<()>>>;

/// One projection out of a pair.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Proj {
    Fst,
    Snd,
}

/// A projection path from the induction hypothesis, outermost first.
pub type Path = Vec<Proj>;

/// What one application of an affine step makes of its induction
/// hypothesis `ih`, as a tree shaped like the fold's motive value.
#[derive(Clone, Debug)]
pub enum AffineTree {
    /// `Succ^{inc}(ih.path)`.
    Leaf { inc: Increment, path: Path },
    /// `Succ^{inc}(Zero)`: a closed literal, the same at every step.
    Lit { inc: Increment },
    Pair(Box<AffineTree>, Box<AffineTree>),
}

/// What the evaluator's probe (`eval/probe.rs`) made of a fold's step.
#[derive(Clone, Debug)]
pub enum FoldClass {
    /// Folds one step at a time.
    Opaque,
    /// One application of the step is `tree[ih]`. `uniform` means at every
    /// step; otherwise at every step but the innermost, whose `k` is the
    /// run's tail and was matched on.
    Affine { tree: AffineTree, uniform: bool },
    /// The step is a function that, at `Succ x`, is `Succ^{inc}(ih x)`:
    /// one constructor from each counter reduces to the same fold at both
    /// predecessors, under `inc` successors.
    Sync { inc: Increment },
}

/// `Succ^{a}(Succ^{b}(-))` as one increment.
pub fn add_increments(outer: &Increment, inner: &Increment) -> Increment {
    match (outer, inner) {
        (None, other) | (other, None) => other.clone(),
        (Some(a), Some(b)) => Some(ContextProgram::append(Rc::clone(a), Rc::clone(b))),
    }
}

impl AffineTree {
    /// The identity algebra: `ih` itself.
    pub fn identity() -> AffineTree {
        AffineTree::Leaf { inc: None, path: Vec::new() }
    }

    fn is_identity(&self) -> bool {
        matches!(self, AffineTree::Leaf { inc: None, path } if path.is_empty())
    }

    /// The sub-tree at `path`, with the successors it is under. Descending
    /// *through* a leaf appends the remainder of the path to the leaf's own
    /// path — a copied component projected further — which is only
    /// well-typed when the leaf has no successors (a `Nat` has no
    /// projections). Stopping at a pair under successors is likewise
    /// ill-typed. Both return `None`: ill-typed input is declined, never
    /// guessed at.
    fn at(&self, path: &[Proj]) -> Option<AffineTree> {
        let mut cur = self;
        for (i, step) in path.iter().enumerate() {
            match cur {
                AffineTree::Pair(fst, snd) => {
                    cur = match step {
                        Proj::Fst => fst,
                        Proj::Snd => snd,
                    };
                }
                AffineTree::Leaf { inc: None, path: own } => {
                    let mut extended = own.clone();
                    extended.extend_from_slice(&path[i..]);
                    return Some(AffineTree::Leaf { inc: None, path: extended });
                }
                AffineTree::Leaf { inc: Some(_), .. } | AffineTree::Lit { .. } => return None,
            }
        }
        Some(cur.clone())
    }

    /// `outer ∘ inner`: the tree for two steps, the inner one first —
    /// `outer[ih := inner]`.
    pub fn compose(outer: &AffineTree, inner: &AffineTree) -> Option<AffineTree> {
        if outer.is_identity() {
            return Some(inner.clone());
        }
        if inner.is_identity() {
            return Some(outer.clone());
        }
        Some(match outer {
            AffineTree::Lit { inc } => AffineTree::Lit { inc: inc.clone() },
            AffineTree::Pair(fst, snd) => AffineTree::Pair(
                Box::new(Self::compose(fst, inner)?),
                Box::new(Self::compose(snd, inner)?),
            ),
            AffineTree::Leaf { inc, path } => match inner.at(path)? {
                AffineTree::Leaf { inc: inner_inc, path } => {
                    AffineTree::Leaf { inc: add_increments(inc, &inner_inc), path }
                }
                AffineTree::Lit { inc: inner_inc } => {
                    AffineTree::Lit { inc: add_increments(inc, &inner_inc) }
                }
                pair @ AffineTree::Pair(..) => {
                    if inc.is_some() {
                        return None;
                    }
                    pair
                }
            },
        })
    }

    /// `self^count` by binary exponentiation: at most `2·log₂(count)`
    /// compositions.
    fn power(&self, mut count: u64) -> Option<AffineTree> {
        let mut acc = AffineTree::identity();
        let mut base = self.clone();
        loop {
            if count & 1 == 1 {
                acc = Self::compose(&base, &acc)?;
            }
            count >>= 1;
            if count == 0 {
                return Some(acc);
            }
            base = Self::compose(&base, &base)?;
        }
    }

    /// `self^{|program|}`: the tree for as many steps as `program` has
    /// successors. A composed program `outer(inner(-))` is the fold over
    /// the inner successors first, so it is `self^outer ∘ self^inner`;
    /// shared nodes are computed once, so a depth-`d` doubling DAG costs
    /// `d` compositions.
    pub fn iterate(&self, program: &Rc<ContextProgram<()>>) -> Option<AffineTree> {
        // One successor per step (`add`) iterated over a program is that
        // program: hand back the same one, so a fold that only re-wraps a
        // run keeps its identity — the cheapest positive conversion case.
        if let AffineTree::Leaf { inc: Some(inc), path } = self {
            if path.is_empty()
                && matches!(&**inc, ContextProgram::Run { count, .. } if count.get() == 1)
            {
                return Some(AffineTree::Leaf { inc: Some(Rc::clone(program)), path: Vec::new() });
            }
        }
        let mut memo: HashMap<*const ContextProgram<()>, AffineTree> = HashMap::new();
        self.iterate_memo(program, &mut memo)
    }

    fn iterate_memo(
        &self,
        program: &Rc<ContextProgram<()>>,
        memo: &mut HashMap<*const ContextProgram<()>, AffineTree>,
    ) -> Option<AffineTree> {
        // The root retains the whole DAG while this runs, so a key is never
        // freed and reused underneath the memo.
        let key = Rc::as_ptr(program);
        if let Some(done) = memo.get(&key) {
            return Some(done.clone());
        }
        let out = match &**program {
            ContextProgram::Run { count, .. } => self.power(count.get())?,
            ContextProgram::Compose { outer, inner } => {
                let inner = self.iterate_memo(inner, memo)?;
                let outer = self.iterate_memo(outer, memo)?;
                Self::compose(&outer, &inner)?
            }
        };
        memo.insert(key, out.clone());
        Some(out)
    }
}

#[cfg(test)]
mod tests {
    //! The reference semantics: a tree is a function on *states*, a state
    //! being a tree of the same shape whose leaves are naturals — either a
    //! closed count or "the `i`-th original component plus a count". Applying
    //! a tree once reads each output leaf's input component and adds its
    //! increment. Iteration by program must agree with that many single
    //! applications, on every random tree, at every small count, across
    //! every program shape.

    use super::{AffineTree, Increment, Path, Proj};
    use crate::value::program::ContextProgram;
    use std::num::NonZeroU64;
    use std::sync::Arc as Rc;

    fn n(v: u64) -> NonZeroU64 {
        NonZeroU64::new(v).unwrap()
    }

    fn succ(v: u64) -> Increment {
        NonZeroU64::new(v).map(|v| ContextProgram::run((), v))
    }

    /// Exact count of a program, unbounded — the test may hold the whole
    /// `u128` where the kernel deliberately keeps a bounded `u64` run.
    /// Shared nodes are counted once: the DAG may denote `2^64`.
    fn count(program: &Rc<ContextProgram<()>>) -> u128 {
        fn go(
            program: &Rc<ContextProgram<()>>,
            memo: &mut std::collections::HashMap<*const ContextProgram<()>, u128>,
        ) -> u128 {
            if let Some(n) = memo.get(&Rc::as_ptr(program)) {
                return *n;
            }
            let n = match &**program {
                ContextProgram::Run { count, .. } => count.get() as u128,
                ContextProgram::Compose { outer, inner } => go(outer, memo) + go(inner, memo),
            };
            memo.insert(Rc::as_ptr(program), n);
            n
        }
        go(program, &mut std::collections::HashMap::new())
    }

    fn inc_count(inc: &Increment) -> u128 {
        inc.as_ref().map_or(0, count)
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    enum State {
        /// `Succ^count(original component `origin`)`; `None` is `Zero`.
        Leaf { origin: Option<Path>, count: u128 },
        Pair(Box<State>, Box<State>),
    }

    impl State {
        /// The initial state: every leaf is its own original component.
        fn initial(shape: &AffineTree, prefix: &mut Path) -> State {
            match shape {
                AffineTree::Pair(fst, snd) => {
                    prefix.push(Proj::Fst);
                    let f = Self::initial(fst, prefix);
                    prefix.pop();
                    prefix.push(Proj::Snd);
                    let s = Self::initial(snd, prefix);
                    prefix.pop();
                    State::Pair(Box::new(f), Box::new(s))
                }
                AffineTree::Leaf { .. } | AffineTree::Lit { .. } => {
                    State::Leaf { origin: Some(prefix.clone()), count: 0 }
                }
            }
        }

        fn at(&self, path: &[Proj]) -> &State {
            let mut cur = self;
            for step in path {
                let State::Pair(fst, snd) = cur else { panic!("projection of a leaf") };
                cur = match step {
                    Proj::Fst => fst,
                    Proj::Snd => snd,
                };
            }
            cur
        }

        fn add(&self, delta: u128) -> State {
            match self {
                State::Leaf { origin, count } => {
                    State::Leaf { origin: origin.clone(), count: count + delta }
                }
                State::Pair(..) => {
                    assert_eq!(delta, 0, "successors on a pair");
                    self.clone()
                }
            }
        }
    }

    fn apply(tree: &AffineTree, state: &State) -> State {
        match tree {
            AffineTree::Leaf { inc, path } => state.at(path).add(inc_count(inc)),
            AffineTree::Lit { inc } => State::Leaf { origin: None, count: inc_count(inc) },
            AffineTree::Pair(fst, snd) => {
                State::Pair(Box::new(apply(fst, state)), Box::new(apply(snd, state)))
            }
        }
    }

    fn apply_n(tree: &AffineTree, state: &State, times: u128) -> State {
        let mut cur = state.clone();
        for _ in 0..times {
            cur = apply(tree, &cur);
        }
        cur
    }

    /// A small deterministic generator; the kernel has no dev-dependencies.
    struct Lcg(u64);

    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            self.0 >> 33
        }

        fn below(&mut self, bound: u64) -> u64 {
            self.next() % bound
        }
    }

    /// The leaf paths of a shape, so random leaves refer to real components.
    fn leaves(shape: &AffineTree, prefix: &mut Path, out: &mut Vec<Path>) {
        match shape {
            AffineTree::Pair(fst, snd) => {
                prefix.push(Proj::Fst);
                leaves(fst, prefix, out);
                prefix.pop();
                prefix.push(Proj::Snd);
                leaves(snd, prefix, out);
                prefix.pop();
            }
            _ => out.push(prefix.clone()),
        }
    }

    fn random_shape(rng: &mut Lcg, depth: u32) -> AffineTree {
        if depth == 0 || rng.below(3) == 0 {
            AffineTree::Lit { inc: None }
        } else {
            AffineTree::Pair(
                Box::new(random_shape(rng, depth - 1)),
                Box::new(random_shape(rng, depth - 1)),
            )
        }
    }

    /// A random well-typed tree over `shape`: every leaf of the output is a
    /// `Nat` leaf, so every output leaf may carry successors.
    fn random_tree(rng: &mut Lcg, shape: &AffineTree, paths: &[Path]) -> AffineTree {
        match shape {
            AffineTree::Pair(fst, snd) => AffineTree::Pair(
                Box::new(random_tree(rng, fst, paths)),
                Box::new(random_tree(rng, snd, paths)),
            ),
            _ => {
                let increment = succ(rng.below(4));
                if rng.below(5) == 0 {
                    AffineTree::Lit { inc: increment }
                } else {
                    let path = paths[rng.below(paths.len() as u64) as usize].clone();
                    AffineTree::Leaf { inc: increment, path }
                }
            }
        }
    }

    #[test]
    fn iteration_over_a_run_agrees_with_repeated_application() {
        let mut rng = Lcg(7);
        for _ in 0..200 {
            let shape = random_shape(&mut rng, 3);
            let mut paths = Vec::new();
            leaves(&shape, &mut Vec::new(), &mut paths);
            let tree = random_tree(&mut rng, &shape, &paths);
            let initial = State::initial(&shape, &mut Vec::new());
            for times in 0..12u64 {
                let program = match NonZeroU64::new(times) {
                    Some(c) => ContextProgram::run((), c),
                    None => continue,
                };
                let iterated = tree.iterate(&program).expect("well-typed");
                assert_eq!(
                    apply(&iterated, &initial),
                    apply_n(&tree, &initial, times as u128),
                    "tree {tree:?} at {times}",
                );
            }
        }
    }

    #[test]
    fn composition_is_the_two_step_fold() {
        let mut rng = Lcg(11);
        for _ in 0..200 {
            let shape = random_shape(&mut rng, 3);
            let mut paths = Vec::new();
            leaves(&shape, &mut Vec::new(), &mut paths);
            let outer = random_tree(&mut rng, &shape, &paths);
            let inner = random_tree(&mut rng, &shape, &paths);
            let initial = State::initial(&shape, &mut Vec::new());
            let composed = AffineTree::compose(&outer, &inner).expect("well-typed");
            assert_eq!(apply(&composed, &initial), apply(&outer, &apply(&inner, &initial)));
        }
    }

    #[test]
    fn a_composed_program_folds_its_inner_successors_first() {
        // `⟨su (π₁ ih), π₀ ih⟩` — `half`'s window — over 3(2(-)): five steps.
        let tree = AffineTree::Pair(
            Box::new(AffineTree::Leaf { inc: succ(1), path: vec![Proj::Snd] }),
            Box::new(AffineTree::Leaf { inc: None, path: vec![Proj::Fst] }),
        );
        let program = ContextProgram::compose(
            ContextProgram::run((), n(3)),
            ContextProgram::run((), n(2)),
        );
        let shape = AffineTree::Pair(
            Box::new(AffineTree::Lit { inc: None }),
            Box::new(AffineTree::Lit { inc: None }),
        );
        let initial = State::initial(&shape, &mut Vec::new());
        let iterated = tree.iterate(&program).unwrap();
        assert_eq!(apply(&iterated, &initial), apply_n(&tree, &initial, 5));
    }

    #[test]
    fn a_shared_exponential_program_costs_its_depth() {
        // `su ih` over the depth-64 doubling DAG denoting 2^64 successors.
        let mut program = ContextProgram::run((), n(1));
        for _ in 0..64 {
            program = ContextProgram::compose(Rc::clone(&program), program);
        }
        let add = AffineTree::Leaf { inc: succ(1), path: Vec::new() };
        let iterated = add.iterate(&program).unwrap();
        let AffineTree::Leaf { inc, path } = iterated else { panic!("shape changed") };
        assert!(path.is_empty());
        assert_eq!(inc_count(&inc), 1u128 << 64);
        // And the doubled increment: `twice` over the same program.
        let twice = AffineTree::Leaf { inc: succ(2), path: Vec::new() };
        let AffineTree::Leaf { inc, .. } = twice.iterate(&program).unwrap() else { panic!() };
        assert_eq!(inc_count(&inc), 1u128 << 65);
    }

    #[test]
    fn increments_saturate_a_run_then_compose_instead_of_overflowing() {
        let add = AffineTree::Leaf { inc: succ(1), path: Vec::new() };
        let full = ContextProgram::run((), n(u64::MAX));
        let AffineTree::Leaf { inc, .. } = add.iterate(&full).unwrap() else { panic!() };
        assert!(matches!(inc.as_deref(),
            Some(ContextProgram::Run { count, .. }) if count.get() == u64::MAX));

        let twice = AffineTree::Leaf { inc: succ(2), path: Vec::new() };
        let AffineTree::Leaf { inc, .. } = twice.iterate(&full).unwrap() else { panic!() };
        assert!(matches!(inc.as_deref(), Some(ContextProgram::Compose { .. })));
        assert_eq!(inc_count(&inc), 2 * (u64::MAX as u128));
    }

    #[test]
    fn multiplication_of_two_runs_is_one_iteration() {
        // `mul(a, b)` over `b`: the step adds `a` — a leaf with increment
        // `|a|` — and iterating it `|b|` times is the product.
        let by = AffineTree::Leaf { inc: succ(1 << 32), path: Vec::new() };
        let AffineTree::Leaf { inc, .. } =
            by.iterate(&ContextProgram::run((), n(1 << 32))).unwrap()
        else {
            panic!()
        };
        assert_eq!(inc_count(&inc), 1u128 << 64);
        // A product that fits stays one saturated run.
        let AffineTree::Leaf { inc, .. } =
            by.iterate(&ContextProgram::run((), n(1 << 31))).unwrap()
        else {
            panic!()
        };
        assert!(matches!(inc.as_deref(),
            Some(ContextProgram::Run { count, .. }) if count.get() == 1 << 63));
    }

    #[test]
    fn ill_typed_shapes_are_declined_not_guessed() {
        // Successors on a copied pair.
        let pair_copy = AffineTree::Leaf { inc: succ(1), path: Vec::new() };
        let pair = AffineTree::Pair(
            Box::new(AffineTree::Lit { inc: None }),
            Box::new(AffineTree::Lit { inc: None }),
        );
        assert!(AffineTree::compose(&pair_copy, &pair).is_none());
        // A projection through a successor-bearing leaf.
        let deep = AffineTree::Leaf { inc: None, path: vec![Proj::Fst] };
        let nat = AffineTree::Leaf { inc: succ(1), path: Vec::new() };
        assert!(AffineTree::compose(&deep, &nat).is_none());
        // A projection out of a literal.
        assert!(AffineTree::compose(&deep, &AffineTree::Lit { inc: succ(3) }).is_none());
    }

    #[test]
    fn the_identity_is_neutral_for_composition_and_iteration() {
        let tree = AffineTree::Pair(
            Box::new(AffineTree::Leaf { inc: succ(2), path: vec![Proj::Snd] }),
            Box::new(AffineTree::Lit { inc: succ(1) }),
        );
        let id = AffineTree::identity();
        let shape = AffineTree::Pair(
            Box::new(AffineTree::Lit { inc: None }),
            Box::new(AffineTree::Lit { inc: None }),
        );
        let initial = State::initial(&shape, &mut Vec::new());
        let left = AffineTree::compose(&id, &tree).unwrap();
        let right = AffineTree::compose(&tree, &id).unwrap();
        assert_eq!(apply(&left, &initial), apply(&tree, &initial));
        assert_eq!(apply(&right, &initial), apply(&tree, &initial));
        let once = id.iterate(&ContextProgram::run((), n(1 << 40))).unwrap();
        assert_eq!(apply(&once, &initial), initial);
    }
}
