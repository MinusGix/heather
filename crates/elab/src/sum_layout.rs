//! **Where each constructor sits in a declaration's sum** — the one place
//! the shape of the `+` tree is decided.
//!
//! A declaration with `n` constructors lowers to a binary tree of `+` whose
//! leaves are the constructor payloads in declaration order. Every builder
//! (the lowering, the injections, the case trees, the spine codes) and every
//! reader (the spine, the displays, the constructor readers) asks this
//! module for the tree instead of assuming a shape, so the shape can change
//! in one place (`issues/wide-inductive-balanced-sum.md`).
//!
//! The tree over the constructor range `[lo, hi)` is a leaf when the range
//! holds one constructor and otherwise `[lo, mid) + [mid, hi)` with
//! `mid = split(n, lo, hi)`. [`split`] is the policy: a declaration with at
//! least [`BALANCED_FROM`] constructors halves every range, so each
//! constructor is about `log₂ n` injections deep and a `match` arm sits
//! under as many `Case`s; a narrower one stays right-nested (`lo + 1`,
//! constructor `k` is `k` deep), which is every small type's spelling from
//! before the tree existed and costs at most a few layers.
//!
//! Internal nodes are numbered in **preorder**: node 0 is the whole sum, and
//! a node's children come after it. On a right-nested tree node `j` is the
//! range `[j, n)`, which is what `Spine`'s former `tails[j - 1]` named.

use heather_kernel::rc::Rc;

/// The constructor count from which a sum is balanced rather than
/// right-nested.
pub(crate) const BALANCED_FROM: usize = 8;

/// The policy: where the range `[lo, hi)` of an `n`-constructor sum splits.
/// Callers never see it, only the tree it produces.
fn split(n: usize, lo: usize, hi: usize) -> usize {
    debug_assert!(hi - lo >= 2);
    if n >= BALANCED_FROM { lo + (hi - lo) / 2 } else { lo + 1 }
}

/// One side of a `+` node: a constructor's payload, or another `+`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Child {
    /// Constructor `k`'s payload.
    Leaf(usize),
    /// Internal node `j` (preorder).
    Node(usize),
}

/// One `+` node: the constructor range it covers and its two sides.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) struct Node {
    pub(crate) lo: usize,
    pub(crate) mid: usize,
    pub(crate) hi: usize,
    pub(crate) lhs: Child,
    pub(crate) rhs: Child,
}

impl Node {
    /// The side `side` names: `false` the left, `true` the right.
    pub(crate) fn side(&self, right: bool) -> Child {
        if right { self.rhs } else { self.lhs }
    }
}

/// The `+` tree of an `n`-constructor sum.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) struct Layout {
    n: usize,
    nodes: Vec<Node>,
}

impl Layout {
    pub(crate) fn new(n: usize) -> Layout {
        let mut nodes = Vec::with_capacity(n.saturating_sub(1));
        if n >= 2 {
            Self::build(n, 0, n, &mut nodes);
        }
        Layout { n, nodes }
    }

    fn build(n: usize, lo: usize, hi: usize, nodes: &mut Vec<Node>) -> Child {
        if hi - lo == 1 {
            return Child::Leaf(lo);
        }
        let j = nodes.len();
        let mid = split(n, lo, hi);
        // A placeholder, so the children number after their parent.
        nodes.push(Node { lo, mid, hi, lhs: Child::Leaf(lo), rhs: Child::Leaf(mid) });
        let lhs = Self::build(n, lo, mid, nodes);
        let rhs = Self::build(n, mid, hi, nodes);
        nodes[j] = Node { lo, mid, hi, lhs, rhs };
        Child::Node(j)
    }

    /// How many constructors.
    pub(crate) fn len(&self) -> usize {
        self.n
    }

    /// The `+` nodes in preorder; `nodes()[0]` is the whole sum.
    pub(crate) fn nodes(&self) -> &[Node] {
        &self.nodes
    }

    pub(crate) fn node(&self, j: usize) -> &Node {
        &self.nodes[j]
    }

    /// The whole sum: node 0, or the one payload when there is one
    /// constructor. `None` with no constructors (`Empty`).
    pub(crate) fn root(&self) -> Option<Child> {
        match self.n {
            0 => None,
            1 => Some(Child::Leaf(0)),
            _ => Some(Child::Node(0)),
        }
    }

    /// Constructor `i`'s injection path from the root: each `+` crossed and
    /// whether the path takes its right side, outermost first.
    pub(crate) fn path(&self, i: usize) -> Vec<(usize, bool)> {
        debug_assert!(i < self.n);
        let mut out = Vec::new();
        let mut cur = self.root();
        while let Some(Child::Node(j)) = cur {
            let node = &self.nodes[j];
            let right = i >= node.mid;
            out.push((j, right));
            cur = Some(node.side(right));
        }
        out
    }

    /// The constructor a path of sides (outermost first) reaches, and how
    /// many of the sides it used: a reader walking `inl`/`inr` stops at the
    /// first leaf. `None` when the sides run out before a leaf.
    pub(crate) fn index_of(&self, sides: impl IntoIterator<Item = bool>) -> Option<(usize, usize)> {
        let mut cur = self.root()?;
        let mut used = 0;
        let mut sides = sides.into_iter();
        loop {
            match cur {
                Child::Leaf(k) => return Some((k, used)),
                Child::Node(j) => {
                    cur = self.nodes[j].side(sides.next()?);
                    used += 1;
                }
            }
        }
    }

    /// Fold the leaves into the tree: `leaf(k)` for each payload, `join` for
    /// each `+` (left, right, in that order). `None` with no constructors.
    pub(crate) fn fold<T>(&self, leaf: impl FnMut(usize) -> T, join: impl FnMut(&Node, T, T) -> T) -> Option<T> {
        struct F<L, J> {
            leaf: L,
            join: J,
        }
        fn go<T, L: FnMut(usize) -> T, J: FnMut(&Node, T, T) -> T>(l: &Layout, f: &mut F<L, J>, c: Child) -> T {
            match c {
                Child::Leaf(k) => (f.leaf)(k),
                Child::Node(j) => {
                    let node = l.nodes[j];
                    let a = go(l, f, node.lhs);
                    let b = go(l, f, node.rhs);
                    (f.join)(&node, a, b)
                }
            }
        }
        let root = self.root()?;
        Some(go(self, &mut F { leaf, join }, root))
    }
}

/// The layout for `n` constructors, shared: every spine of a declaration
/// asks for the same one.
pub(crate) fn layout(n: usize) -> Rc<Layout> {
    thread_local! {
        static CACHE: std::cell::RefCell<Vec<Option<Rc<Layout>>>> = const { std::cell::RefCell::new(Vec::new()) };
    }
    CACHE.with(|c| {
        let mut c = c.borrow_mut();
        if c.len() <= n {
            c.resize(n + 1, None);
        }
        Rc::clone(c[n].get_or_insert_with(|| Rc::new(Layout::new(n))))
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_constructor_has_one_path_and_reads_back() {
        for n in 1..40 {
            let l = Layout::new(n);
            assert_eq!(l.nodes().len(), n - 1, "n = {n}");
            for i in 0..n {
                let path = l.path(i);
                let (k, used) = l.index_of(path.iter().map(|&(_, r)| r)).expect("a leaf");
                assert_eq!((k, used), (i, path.len()), "n = {n}, i = {i}");
            }
            // Preorder: a node's children number after it, and cover its
            // range exactly.
            for (j, node) in l.nodes().iter().enumerate() {
                for (c, lo, hi) in [(node.lhs, node.lo, node.mid), (node.rhs, node.mid, node.hi)] {
                    match c {
                        Child::Leaf(k) => assert!(hi - lo == 1 && k == lo),
                        Child::Node(m) => {
                            assert!(m > j);
                            assert_eq!((l.node(m).lo, l.node(m).hi), (lo, hi));
                        }
                    }
                }
            }
            // The fold visits the leaves in declaration order.
            let leaves = l.fold(|k| vec![k], |_, mut a, b| { a.extend(b); a }).unwrap();
            assert_eq!(leaves, (0..n).collect::<Vec<_>>());
        }
        // Narrow sums stay right-nested; wide ones are about log₂ n deep.
        for n in 2..BALANCED_FROM {
            assert!((0..n).all(|i| Layout::new(n).path(i).len() == i.min(n - 2) + 1), "n = {n}");
        }
        for n in [BALANCED_FROM, 100, 1024] {
            let l = Layout::new(n);
            let deepest = (0..n).map(|i| l.path(i).len()).max().unwrap();
            assert_eq!(deepest, n.next_power_of_two().trailing_zeros() as usize, "n = {n}");
        }
        // A path that runs out before a leaf reads nothing.
        assert_eq!(Layout::new(4).index_of([true]), None);
        assert_eq!(Layout::new(0).root(), None);
    }
}
