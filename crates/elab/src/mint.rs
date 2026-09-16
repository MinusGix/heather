//! One name per value: the free-variable-scoped mint
//! (`docs/name-per-value-design.md` §4 and §8.3).
//!
//! `rbemit.rs` hands this module a root `Type` whose interior is an `Rc`
//! **graph** — one node per distinct sub-value — but whose *meaning* is the
//! tree that graph expands to, because the term language has no `let`. This
//! module picks the nodes whose sharing is worth a Ψ definition, rebuilds the
//! graph with each of them replaced by a reference, and hands the bodies to a
//! `Minter` the caller installs.
//!
//! What separates it from `rbname.rs`'s spike — the whole of the measured
//! order of magnitude (design §3, §8.2) — is **what a name is scoped in**. The
//! spike scoped a mint in `Γ` extended by *every binder above the node*, which
//! is one name per depth and grows with the tower; here `Δ` is the node's own
//! **free variables**, closed up so that every entry's type is inside the
//! block too. A value that is one pointer under two chains cannot depend on
//! either chain's binders, so one body serves every occurrence and the
//! reference costs `1 + |Δ|` with `|Δ| ≤ 5` measured (design §2, §8.1).
//!
//! **One device, two spellings** (design §8.3). A chosen node of the term sort
//! is a Ψ term definition `Δ ⊢ body : T`, referenced `u^δ`. A chosen node of
//! the *type* sort is a Ψ term definition of its **code**, `Δ ⊢ ⌜T⌝ : Ty l`
//! (`code.rs`'s `code_of`, which reads a named child straight through because
//! `code_of (El t) = t`), referenced `El l (u^δ)`. The choice rule, the `Δ`,
//! the `δ` and the mint block are shared; only the body's encoder and the
//! occurrence's `El` differ.
//!
//! Three things can stop a chosen node from being named, and all three are
//! **declines** — the component stays inline, which is stage one's behaviour
//! and always safe:
//!
//! - a free variable this walk cannot resolve to a level (the abstract prefix
//!   `g`, or a scope `slots_tm`/`slots_ty` marks `Foreign`), so `Δ` cannot be
//!   written;
//! - two occurrences whose binder **types** differ at one of the node's own
//!   free variables, so one body cannot serve both;
//! - a body the minter refuses — the reserved block is full, the kernel will
//!   not type it, or a type node whose code `code_of` has no arm for.

use std::collections::{HashMap, HashSet};
use std::sync::Arc as Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{
    CtxBase, GlobalVar, LocalCtx, LocalSubst, LocalVar, SubstTail, Term, Type,
};
use heather_kernel::value::CloId;

use crate::rbname::{ANOTHER_CTX, Kid, Scope, rebuild_tm, rebuild_ty, slots_tm, slots_ty};

/// The unit of sharing: name a shared node when naming it saves at least this
/// many nodes.
///
/// `docs/name-per-value-design.md` §5 measured **64** three times, on the
/// *value* graph, and this device works on the emitter's **syntax** graph,
/// which splits a neutral into its spine and so has three times the nodes and
/// four times the shared ones. That alone would be a reason to re-ask the
/// unit; the reason it is answered **1 024** is the readers audit, and it is
/// an honest debt rather than a measurement:
///
/// - at 64 a small mint hides a record from `dispatch/member.rs`'s
///   `record_of_at` (`lib/std/relation.hthr`'s `compose_assoc`: "this is not
///   a record, so it has no field `witness`");
/// - at 256 the showcase's calculator stops converting `leb(2, 2)` against
///   `leb(2, len_append(…))` at an elaborator check.
///
/// Both are readers reconstituting a former against a changed spelling — the
/// 2026-09-10 lesson, and §4's audit list — and the threshold is not the fix
/// for either. What a name may hide from a *structural* reader is the round
/// this hands on; until then the device names only what is big enough that no
/// reader has been found to trip on it. The cost is §9's table.
pub(crate) const THRESHOLD: u64 = 1_024;

/// The threshold in force, overridable for the round's own sweep only.
pub(crate) fn threshold() -> u64 {
    static M: std::sync::OnceLock<u64> = std::sync::OnceLock::new();
    *M.get_or_init(|| {
        std::env::var("HEATHER_RB_T")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(THRESHOLD)
    })
}

/// What a minter answers with. `level` is the mint's own statement's level
/// when that statement is `Ty l` — which a **type** spelling needs for the
/// `El l` at its occurrence and a term spelling ignores.
pub(crate) struct MintReply {
    pub(crate) var: GlobalVar,
    pub(crate) ty_level: Option<Level>,
}

/// What the caller does with a chosen name: mint `Δ ⊢ body`, or **decline**.
///
/// Mints arrive in dependency order: every reference in `body` is to one the
/// minter has already accepted.
pub(crate) type Minter<'a> = dyn FnMut(&LocalCtx, &Rc<Term>) -> Option<MintReply> + 'a;

/// What the naming could not take, and why — the design's open questions as
/// counters rather than as prose.
#[derive(Default, Clone, Copy)]
pub(crate) struct Declines {
    /// Cleared the threshold but its `Δ` cannot be written: a free variable in
    /// the abstract prefix, a `Foreign` scope, an anonymous binder.
    pub(crate) unscoped: u64,
    /// Cleared the threshold but two occurrences disagree on a free variable's
    /// binder type.
    pub(crate) disagree: u64,
    /// Cleared the threshold and the minter refused (a full block, a body the
    /// kernel will not type, a type node `code_of` has no code for).
    pub(crate) refused: u64,
    /// The nodes the declines above would have saved, had they been minted.
    pub(crate) lost: u64,
}

pub(crate) struct Naming {
    /// The named spelling.
    pub(crate) root: Rc<Type>,
    /// The graph: distinct nodes, and how many of them have more than one
    /// parent. Against the instrument's `graph=`/`shared=` columns.
    pub(crate) graph: u64,
    pub(crate) shared: u64,
    pub(crate) chosen: u64,
    /// Names the minter accepted, split by spelling.
    pub(crate) minted_tm: u32,
    pub(crate) minted_ty: u32,
    /// The tree the root expands to with nothing named.
    pub(crate) naive: u64,
    /// The tree the root expands to *with* the names, plus every minted body.
    pub(crate) emitted: u64,
    /// The widest and the summed `|Δ|` over the names chosen.
    pub(crate) delta_sum: u64,
    pub(crate) delta_max: u32,
    pub(crate) declines: Declines,
}

// -- the binder frames -----------------------------------------------------

/// One binder chain. Interned so that two paths reaching the same node under
/// the same binders share a frame **by pointer**, which makes the agreement
/// test below O(1) in the common case.
struct Frame {
    parent: Option<Rc<Frame>>,
    /// The binder this frame adds, `None` for a frame that adds none and
    /// `Some((None, _))` for one whose type this walk cannot spell (a
    /// `Foreign` scope's own binders). An anonymous binder keeps the *levels*
    /// below it honest — which is what an ancestor's `Δ` is computed from —
    /// while refusing to be a `Δ` entry itself.
    binder: Option<Option<(Rc<Type>, Level)>>,
    depth: u32,
}

#[derive(Default)]
struct Frames {
    table: HashMap<(usize, usize, bool), Rc<Frame>>,
}

impl Frames {
    fn child(&mut self, parent: &Rc<Frame>, binder: Option<(Rc<Type>, Level)>) -> Rc<Frame> {
        let key = (
            Rc::as_ptr(parent) as usize,
            binder.as_ref().map_or(0, |(t, _)| Rc::as_ptr(t) as usize),
            binder.is_some(),
        );
        if let Some(f) = self.table.get(&key) {
            return Rc::clone(f);
        }
        let f = Rc::new(Frame {
            parent: Some(Rc::clone(parent)),
            depth: parent.depth + 1,
            binder: Some(binder),
        });
        self.table.insert(key, Rc::clone(&f));
        f
    }
}

/// The binder chain of a frame, **outermost first**, so that index `k` is the
/// binder at level `gamma_len + k`.
fn chain_of(frame: &Rc<Frame>) -> Vec<Option<(Rc<Type>, Level)>> {
    let mut chain = Vec::new();
    let mut cur: Option<&Rc<Frame>> = Some(frame);
    while let Some(f) = cur {
        if let Some(b) = f.binder.as_ref() {
            chain.push(b.clone());
        }
        cur = f.parent.as_ref();
    }
    chain.reverse();
    chain
}

/// How many nodes a type has, giving up at `budget` — the bound on the one
/// structural comparison this module makes (two binder types reached by
/// different pointers), so that two copies of an exponential annotation cannot
/// cost their own size to compare.
fn size_up_to(t: &Type, budget: &mut u32) -> bool {
    if *budget == 0 {
        return false;
    }
    *budget -= 1;
    for (kid, _) in slots_ty(t) {
        let ok = match kid {
            Kid::Ty(t) => size_up_to(&t, budget),
            Kid::Tm(_) => {
                if *budget == 0 {
                    return false;
                }
                *budget -= 1;
                true
            }
        };
        if !ok {
            return false;
        }
    }
    true
}

const COMPARE_BUDGET: u32 = 256;

fn binders_agree(a: &Option<(Rc<Type>, Level)>, b: &Option<(Rc<Type>, Level)>) -> bool {
    match (a, b) {
        // Two anonymous binders: nothing to compare, and a node whose `Δ`
        // would need one is refused by `entry_ty` anyway.
        (None, None) => true,
        (Some((x, lx)), Some((y, ly))) => {
            if Rc::ptr_eq(x, y) {
                return true;
            }
            let mut budget = COMPARE_BUDGET;
            size_up_to(x, &mut budget) && lx == ly && **x == **y
        }
        _ => false,
    }
}

// -- free variables --------------------------------------------------------

/// The free de Bruijn **indices** of a piece of syntax, relative to itself and
/// sorted. Memoized on `Rc` identity, so one pass over the graph costs the
/// graph rather than the tree it expands to. A child under `k` binders
/// contributes its own indices shifted down by `k`; a child scoped in a
/// context of its own ([`ANOTHER_CTX`]) contributes none.
///
/// The tail of a global reference's substitution is deliberately not read: it
/// pins the syntax to one ambient *length*, and re-scoping a body is exactly
/// what rewrites it.
fn free_idx(kid: &Kid, memo: &mut HashMap<(usize, bool), Rc<Vec<u32>>>) -> Rc<Vec<u32>> {
    let (key, slots, leaf) = match kid {
        Kid::Tm(t) => (
            (Rc::as_ptr(t) as usize, true),
            slots_tm(t),
            match &**t {
                Term::Var(v) => Some(v.0),
                _ => None,
            },
        ),
        Kid::Ty(t) => ((Rc::as_ptr(t) as usize, false), slots_ty(t), None),
    };
    if let Some(f) = memo.get(&key) {
        return Rc::clone(f);
    }
    let mut out: Vec<u32> = leaf.into_iter().collect();
    for (child, scope) in &slots {
        let under = match scope {
            Scope::Same => 0,
            Scope::Under(b) => b.len() as u32,
            Scope::Foreign(k) => *k,
        };
        if under == ANOTHER_CTX {
            continue;
        }
        for &i in free_idx(child, memo).iter() {
            if let Some(j) = i.checked_sub(under) {
                out.push(j);
            }
        }
    }
    out.sort_unstable();
    out.dedup();
    let out = Rc::new(out);
    memo.insert(key, Rc::clone(&out));
    out
}

// -- the plan --------------------------------------------------------------

struct Node {
    frame: Rc<Frame>,
    kids: Vec<u32>,
    is_tm: bool,
    indeg: u32,
    /// The node that carries this one's **name**. A 0-binder closure read at
    /// two depths is two pieces of syntax and one value: the copies share a
    /// representative, its in-degree counts every occurrence, and each copy
    /// spells the name with its own `δ`.
    rep: u32,
    /// The node's free variables as **absolute levels**, ascending. Empty for
    /// a closed node, which 302 of the showcase's 344 chosen values are.
    fv: Vec<u32>,
    /// Set when no `Δ` can be written for this node or anything under it: a
    /// free variable past the concrete entries, a `Foreign` scope, or two
    /// occurrences whose binder types differ at one of its free variables.
    spoiled: bool,
}

struct Plan<'a> {
    gamma: &'a LocalCtx,
    nodes: Vec<Node>,
    tm_ids: HashMap<usize, u32>,
    ty_ids: HashMap<usize, u32>,
    finish: Vec<u32>,
    frames: Frames,
    idx_memo: HashMap<(usize, bool), Rc<Vec<u32>>>,
    /// The value provenance `rbemit.rs` recorded, and the representative each
    /// value's copies share.
    prov: &'a HashMap<usize, (bool, CloId)>,
    reps: HashMap<(bool, CloId), u32>,
    /// The `Δ` of each node, computed on demand and cached: its free variables
    /// closed up so that every entry's type is scoped inside the block too.
    /// `None` for a node whose `Δ` cannot be written.
    delta: HashMap<u32, Option<Rc<Vec<u32>>>>,
}

impl<'a> Plan<'a> {
    fn gamma_len(&self) -> u32 {
        self.gamma.entries.len() as u32
    }

    fn visit(&mut self, kid: &Kid, frame: &Rc<Frame>) -> u32 {
        let (key, is_tm) = match kid {
            Kid::Tm(t) => (Rc::as_ptr(t) as usize, true),
            Kid::Ty(t) => (Rc::as_ptr(t) as usize, false),
        };
        let map = if is_tm { &self.tm_ids } else { &self.ty_ids };
        if let Some(&id) = map.get(&key) {
            let rep = self.nodes[id as usize].rep;
            self.nodes[rep as usize].indeg += 1;
            let seen = Rc::clone(&self.nodes[id as usize].frame);
            if !self.agrees(id, &seen, frame) {
                self.spoil(rep);
            }
            return id;
        }
        let depth = frame.depth;
        let indices = free_idx(kid, &mut self.idx_memo);
        let mut fv = Vec::new();
        let mut spoiled = false;
        for &i in indices.iter() {
            // Past the concrete entries: a variable of the abstract prefix
            // `g`, which no `Δ` this walk writes can hold. Measured zero on
            // every threshold-clearing value (design §1's `basevar` row).
            match depth.checked_sub(i + 1) {
                Some(l) => fv.push(l),
                None => spoiled = true,
            }
        }
        fv.sort_unstable();
        let id = self.nodes.len() as u32;
        // One value, one name: a copy joins its representative's class and
        // hands it the occurrence.
        let mut rep = id;
        if let Some(&pk) = self.prov.get(&key) {
            match self.reps.get(&pk) {
                Some(&r) => rep = r,
                None => {
                    self.reps.insert(pk, id);
                }
            }
        }
        self.nodes.push(Node {
            frame: Rc::clone(frame),
            kids: Vec::new(),
            is_tm,
            indeg: u32::from(rep == id),
            rep,
            fv,
            spoiled,
        });
        if rep != id {
            self.nodes[rep as usize].indeg += 1;
            // The copies of one value must read the same levels; anything
            // else and the provenance is not what it claims.
            if self.nodes[rep as usize].fv != self.nodes[id as usize].fv
                || self.nodes[rep as usize].is_tm != is_tm
            {
                self.spoil(rep);
            } else {
                let seen = Rc::clone(&self.nodes[rep as usize].frame);
                if !self.agrees(rep, &seen, frame) {
                    self.spoil(rep);
                }
            }
            if self.nodes[id as usize].spoiled {
                self.spoil(rep);
            }
        }
        if is_tm {
            self.tm_ids.insert(key, id);
        } else {
            self.ty_ids.insert(key, id);
        }
        let slots = match kid {
            Kid::Tm(t) => slots_tm(t),
            Kid::Ty(t) => slots_ty(t),
        };
        let mut kids = Vec::with_capacity(slots.len());
        for (child, scope) in &slots {
            let (child_frame, opaque) = match scope {
                Scope::Same => (Rc::clone(frame), false),
                Scope::Under(bs) => {
                    let mut f = Rc::clone(frame);
                    for b in bs {
                        f = self.frames.child(&f, Some(b.clone()));
                    }
                    (f, false)
                }
                // A child scoped in a context of its own: its variables do
                // not address this Γ at all, so nothing in it can be named
                // here and nothing above it may read its indices.
                Scope::Foreign(ANOTHER_CTX) => (Rc::clone(frame), true),
                // A scope whose binder **types** this walk does not spell —
                // an eliminator's step, a universe or context binder. Its
                // *levels* are still exact, so it gets `k` **anonymous**
                // binders and is not spoiled: a node under it is refused
                // precisely when its own `Δ` would need one of those types
                // (`entry_ty` answers `None`), which is where the tower's mass
                // actually is — spoiling the subtree instead threw away the
                // largest shared values the measurement is about.
                Scope::Foreign(k) => {
                    let mut f = Rc::clone(frame);
                    for _ in 0..*k {
                        f = self.frames.child(&f, None);
                    }
                    (f, false)
                }
            };
            let child = self.visit(child, &child_frame);
            if opaque {
                self.spoil(child);
            }
            kids.push(child);
        }
        self.nodes[id as usize].kids = kids;
        self.finish.push(id);
        id
    }

    /// Whether a second path into `id` binds the node's own free variables the
    /// same way. Only those levels matter: a descendant's free variables are
    /// this node's plus the ones opened inside it, and those are identical by
    /// construction — so agreement here is agreement for the whole subtree.
    fn agrees(&self, id: u32, a: &Rc<Frame>, b: &Rc<Frame>) -> bool {
        if Rc::ptr_eq(a, b) {
            return true;
        }
        let g = self.gamma_len();
        if !self.nodes[id as usize].fv.iter().any(|&l| l >= g) {
            return true;
        }
        let (ca, cb) = (chain_of(a), chain_of(b));
        self.nodes[id as usize]
            .fv
            .iter()
            .filter(|&&l| l >= g)
            .all(|&l| {
                let k = (l - g) as usize;
                match (ca.get(k), cb.get(k)) {
                    (Some(x), Some(y)) => binders_agree(x, y),
                    _ => false,
                }
            })
    }

    fn spoil(&mut self, id: u32) {
        if self.nodes[id as usize].spoiled {
            return;
        }
        self.nodes[id as usize].spoiled = true;
        let kids = self.nodes[id as usize].kids.clone();
        for k in kids {
            let r = self.nodes[k as usize].rep;
            self.spoil(r);
            if r != k {
                self.nodes[k as usize].spoiled = true;
            }
        }
    }

    /// The type of the entry at absolute level `l`, scoped in the length-`l`
    /// prefix, as the walk sees it: `Γ`'s own entry below `gamma_len`, and
    /// above it the binder the frame chain records — which for a `Π` codomain
    /// or a `λ` body is the domain the readback has just spelled off the
    /// *value*, and for a synthesized binder is what the slot table says.
    fn entry_ty(&self, frame: &Rc<Frame>, l: u32) -> Option<(Rc<Type>, Level)> {
        let g = self.gamma_len();
        if l < g {
            let e = self.gamma.entries.get(l as usize)?;
            return Some((Rc::clone(&e.ty), e.level.clone()));
        }
        chain_of(frame).get((l - g) as usize).cloned().flatten()
    }

    /// `Δ`: the node's free variables, closed up so that every entry's **type**
    /// is scoped inside the block too (an entry whose type mentions an outer
    /// one drags that one in). `None` when some entry has no writable type.
    fn delta_of(&mut self, id: u32) -> Option<Rc<Vec<u32>>> {
        if let Some(d) = self.delta.get(&id) {
            return d.clone();
        }
        let out = self.compute_delta(id);
        self.delta.insert(id, out.clone());
        out
    }

    fn compute_delta(&mut self, id: u32) -> Option<Rc<Vec<u32>>> {
        let node = &self.nodes[id as usize];
        if node.spoiled {
            return None;
        }
        let frame = Rc::clone(&node.frame);
        let mut want: Vec<u32> = node.fv.clone();
        let mut seen: HashSet<u32> = want.iter().copied().collect();
        let mut out: Vec<u32> = Vec::new();
        while let Some(l) = want.pop() {
            let (ty, _) = self.entry_ty(&frame, l)?;
            out.push(l);
            for &i in free_idx(&Kid::Ty(ty), &mut self.idx_memo).iter() {
                let parent = l.checked_sub(i + 1)?;
                if seen.insert(parent) {
                    want.push(parent);
                }
            }
        }
        out.sort_unstable();
        Some(Rc::new(out))
    }

    /// What a reference to a node costs where its body used to be spelled: the
    /// `GlobalTm` and one payload per `Δ` entry, plus the `El` when the
    /// occurrence is a type (design §8.2's `TC` column).
    fn ref_cost(&self, id: u32, delta: &[u32]) -> u64 {
        1 + delta.len() as u64 + u64::from(!self.nodes[id as usize].is_tm)
    }

    fn kids_of(&self, id: u32) -> Vec<u32> {
        self.nodes[id as usize].kids.clone()
    }

    fn rep_of(&self, id: u32) -> u32 {
        self.nodes[id as usize].rep
    }
}

/// `Δ` as a kernel context, and the substitution that carries a body scoped in
/// the length-`depth` context into it.
///
/// `Δ` keeps only the levels the body reads, so an entry's type has to be
/// re-indexed too: level `l` of the ambient context becomes position
/// `pos(l)` of `Δ`, and a level `Δ` does not hold cannot occur (the closure in
/// [`Plan::compute_delta`] is what makes that true).
struct Block {
    ctx: LocalCtx,
    /// The substitution from the length-`depth` context into `Δ`.
    into: LocalSubst,
}

fn block_of(plan: &Plan<'_>, frame: &Rc<Frame>, depth: u32, delta: &[u32]) -> Option<Block> {
    let base = plan.gamma.base;
    let mut ctx = LocalCtx::nil();
    if !matches!(base, CtxBase::Nil) {
        // A context with an abstract base is a `meta fn`'s, where `Δ` would
        // have to mention the context variable. Out of scope, and a decline.
        return None;
    }
    // `pos[l]` is the position of level `l` in `Δ`, for the levels it holds.
    let mut pos: HashMap<u32, u32> = HashMap::new();
    for (j, &l) in delta.iter().enumerate() {
        let (ty, level) = plan.entry_ty(frame, l)?;
        // The entry's type is scoped in the length-`l` prefix; re-index it
        // into `Δ`'s own prefix, which is the entries of `Δ` below `l`.
        let p = j as u32;
        let terms = (0..l)
            .map(|k| {
                Rc::new(match pos.get(&k) {
                    Some(&q) if q < p => Term::Var(LocalVar(p - 1 - q)),
                    // Unreachable by the closure, and `Zero` is the
                    // strengthening `apply_local` already writes for a slot
                    // nothing can read.
                    _ => Term::Zero,
                })
            })
            .collect();
        let ty = ty.apply_local(&LocalSubst {
            tail: SubstTail::Empty { len: p, base },
            terms,
        });
        ctx = ctx.extended(Rc::new(ty), level);
        pos.insert(l, p);
    }
    let m = delta.len() as u32;
    let terms = (0..depth)
        .map(|k| {
            Rc::new(match pos.get(&k) {
                Some(&q) => Term::Var(LocalVar(m - 1 - q)),
                None => Term::Zero,
            })
        })
        .collect();
    Some(Block {
        ctx,
        into: LocalSubst {
            tail: SubstTail::Empty { len: m, base },
            terms,
        },
    })
}

/// The reference `u^δ` at an occurrence of a node at `depth` whose `Δ` holds
/// `delta`: the identity of `Δ` read at that depth, which is one node plus one
/// payload per entry and carries no annotations (design §4).
fn reference(var: GlobalVar, base: CtxBase, depth: u32, delta: &[u32]) -> Term {
    Term::GlobalTm {
        var,
        subst: LocalSubst {
            tail: SubstTail::Empty { len: depth, base },
            terms: delta
                .iter()
                .map(|&l| Rc::new(Term::Var(LocalVar(depth - 1 - l))))
                .collect(),
        },
    }
}

// -- the choice ------------------------------------------------------------

struct Choice {
    named: Vec<Option<Rc<Vec<u32>>>>,
    naive: u64,
    emitted: u64,
}

/// Pick the nodes worth naming. One bottom-up fold over the graph: a node's
/// cost is its own node plus its children's, with a named child charged a
/// reference, and a node is named when the reference saves at least
/// `threshold` nodes over its occurrences past the first.
///
/// `allow_types` is the second spelling's switch — off, this is §4's mint
/// alone and its ceiling is design §8.2's `TM` column; on, it is that column's
/// `TC`.
fn choose(plan: &mut Plan<'_>, root_id: u32, threshold: u64, allow_types: bool) -> Choice {
    let n = plan.nodes.len();
    let mut naive = vec![0u64; n];
    let mut named: Vec<Option<Rc<Vec<u32>>>> = vec![None; n];
    let order = plan.finish.clone();
    // The tree each node expands to, which is also what naming it saves per
    // occurrence it takes away.
    for &x in &order {
        let x = x as usize;
        let mut tree = 1u64;
        for k in plan.kids_of(x as u32) {
            tree = tree.saturating_add(naive[k as usize]);
        }
        naive[x] = tree;
    }
    // The choice is **top-down**, over the value's own multiplicity in the
    // object being written rather than over its in-degree. The two agree only
    // while every parent is itself written once, and under a name they do not:
    // a node inside a minted body is written once however many edges reach it,
    // so an in-degree rule names it again for nothing. Measured: the same
    // emitted count with an order of magnitude fewer mints, and every mint is
    // a kernel-gated global (design §8.4's cost column).
    let mut mult = vec![0u64; n];
    mult[plan.rep_of(root_id) as usize] = 1;
    for &x in order.iter().rev() {
        let x = x as usize;
        if plan.rep_of(x as u32) as usize != x {
            continue;
        }
        let m = mult[x];
        let writes = if x as u32 != root_id
            && m > 1
            && (allow_types || plan.nodes[x].is_tm)
            && let Some(delta) = plan.delta_of(x as u32)
            && (m - 1).saturating_mul(naive[x].saturating_sub(plan.ref_cost(x as u32, &delta)))
                >= threshold
        {
            named[x] = Some(delta);
            1
        } else {
            m.max(1)
        };
        for k in plan.kids_of(x as u32) {
            let r = plan.rep_of(k) as usize;
            mult[r] = mult[r].saturating_add(writes);
        }
    }
    // What the named spelling then costs: a bottom-up fold with every named
    // child charged a reference, plus every minted body once.
    let mut cost = vec![0u64; n];
    for &x in &order {
        let x = x as usize;
        let mut c = 1u64;
        for k in plan.kids_of(x as u32) {
            let r = plan.rep_of(k) as usize;
            c = c.saturating_add(match &named[r] {
                Some(d) => plan.ref_cost(r as u32, d),
                None => cost[k as usize],
            });
        }
        cost[x] = c;
    }
    let mut emitted = cost[root_id as usize];
    for x in 0..n {
        if named[x].is_some() {
            emitted = emitted.saturating_add(cost[x]);
        }
    }
    Choice {
        named,
        naive: naive[root_id as usize],
        emitted,
    }
}

// -- the rebuild -----------------------------------------------------------

struct Build<'a, 'm> {
    plan: &'a Plan<'a>,
    named: &'a [Option<Rc<Vec<u32>>>],
    minter: &'a mut Minter<'m>,
    tm_out: HashMap<usize, Rc<Term>>,
    ty_out: HashMap<usize, Rc<Type>>,
    /// The code of an already-rebuilt type node, so that quoting a chosen type
    /// preserves the sharing under it instead of expanding it as a tree.
    code_memo: HashMap<usize, Option<Rc<Term>>>,
    /// The name each representative already has, so that a value read at two
    /// depths is minted once and referenced twice.
    taken: HashMap<u32, Option<(GlobalVar, Option<Level>)>>,
    minted_tm: u32,
    minted_ty: u32,
    delta_sum: u64,
    delta_max: u32,
    declines: Declines,
}

impl Build<'_, '_> {
    fn go(&mut self, kid: &Kid) -> Kid {
        match kid {
            Kid::Tm(t) => {
                let key = Rc::as_ptr(t) as usize;
                if let Some(out) = self.tm_out.get(&key) {
                    return Kid::Tm(Rc::clone(out));
                }
                let Some(&id) = self.plan.tm_ids.get(&key) else {
                    return Kid::Tm(Rc::clone(t));
                };
                let kids = self.kids(&slots_tm(t));
                let rebuilt = if kids.changed {
                    Rc::new(rebuild_tm(t, &kids.kids))
                } else {
                    Rc::clone(t)
                };
                let out = match self.mint(id, |_| Some(Rc::clone(&rebuilt)), false) {
                    Some((r, _)) => Rc::new(r),
                    None => rebuilt,
                };
                self.tm_out.insert(key, Rc::clone(&out));
                Kid::Tm(out)
            }
            Kid::Ty(t) => {
                let key = Rc::as_ptr(t) as usize;
                if let Some(out) = self.ty_out.get(&key) {
                    return Kid::Ty(Rc::clone(out));
                }
                let kids = self.kids(&slots_ty(t));
                let rebuilt = if kids.changed {
                    Rc::new(rebuild_ty(t, &kids.kids))
                } else {
                    Rc::clone(t)
                };
                // The **type** spelling: what is minted is the node's code,
                // and the occurrence is `El l (u^δ)` with `l` the level the
                // mint's own statement `Ty l` reports.
                let out = match self.plan.ty_ids.get(&key).copied() {
                    Some(id) if self.named[self.plan.rep_of(id) as usize].is_some() => {
                        // The body of a named **type** is its code, quoted
                        // over the graph (`code_of` reads a named child
                        // straight through, since `code_of (El t) = t`); the
                        // occurrence is `El l (u^δ)` with `l` off the mint's
                        // own statement. No code for this former, or for one
                        // under it, is a decline and the type stays inline.
                        let t = Rc::clone(&rebuilt);
                        match self.mint(id, move |me| me.code(&t), true) {
                            Some((r, Some(level))) => Rc::new(Type::El {
                                level,
                                tm: Rc::new(r),
                            }),
                            _ => rebuilt,
                        }
                    }
                    _ => rebuilt,
                };
                self.ty_out.insert(key, Rc::clone(&out));
                Kid::Ty(out)
            }
        }
    }

    /// `⌜T⌝` over the rebuilt graph, memoized on `Rc` identity so that a
    /// shared component is quoted once. `code_of (El t) = t` is what reads a
    /// **named** child straight through, so a type mint under a type mint
    /// costs one reference and no `El`.
    fn code(&mut self, t: &Rc<Type>) -> Option<Rc<Term>> {
        let key = Rc::as_ptr(t) as usize;
        if let Some(c) = self.code_memo.get(&key) {
            return c.clone();
        }
        // Guard the re-entry; syntax has no cycles.
        self.code_memo.insert(key, None);
        let mut kids: Vec<Rc<Term>> = Vec::new();
        let mut ok = true;
        for (kid, _) in slots_ty(t) {
            match kid {
                Kid::Ty(child) => match self.code(&child) {
                    Some(c) => kids.push(c),
                    None => {
                        ok = false;
                        break;
                    }
                },
                Kid::Tm(child) => kids.push(child),
            }
        }
        let out = if ok {
            crate::code::code_of_spliced(t, &kids).map(Rc::new)
        } else {
            None
        };
        self.code_memo.insert(key, out.clone());
        out
    }

    /// Offer `body` to the minter as the name for node `id`, and answer with
    /// the occurrence's spelling. `want_ty` asks for the **type** spelling,
    /// whose statement must be `Ty l`.
    fn mint(
        &mut self,
        id: u32,
        body: impl FnOnce(&mut Self) -> Option<Rc<Term>>,
        want_ty: bool,
    ) -> Option<(Term, Option<Level>)> {
        let rep = self.plan.rep_of(id);
        let delta = self.named[rep as usize].clone()?;
        let depth = self.plan.nodes[id as usize].frame.depth;
        let base = self.plan.gamma.base;
        // Already minted from another copy of this value: what differs at this
        // occurrence is only `δ`, which is the whole of §4's mechanism.
        if let Some(taken) = self.taken.get(&rep) {
            let &(var, ref level) = taken.as_ref()?;
            return Some((reference(var, base, depth, &delta), level.clone()));
        }
        let mut fail = |me: &mut Self, slot: usize| {
            me.taken.insert(rep, None);
            let d = &mut me.declines;
            *[&mut d.unscoped, &mut d.disagree, &mut d.refused][slot] += 1;
            d.lost += 1;
            None::<(Term, Option<Level>)>
        };
        let frame = Rc::clone(&self.plan.nodes[id as usize].frame);
        let Some(block) = block_of(self.plan, &frame, depth, &delta) else {
            return fail(self, 0);
        };
        let Some(body) = body(self) else {
            return fail(self, 2);
        };
        let body = Rc::new(body.apply_local(&block.into));
        let Some(reply) = (self.minter)(&block.ctx, &body) else {
            return fail(self, 2);
        };
        // A code whose statement is not a universe is not a code: decline
        // rather than write an `El` the kernel would refuse.
        if want_ty && reply.ty_level.is_none() {
            return fail(self, 2);
        }
        self.delta_sum += delta.len() as u64;
        self.delta_max = self.delta_max.max(delta.len() as u32);
        self.taken
            .insert(rep, Some((reply.var, reply.ty_level.clone())));
        if want_ty {
            self.minted_ty += 1;
        } else {
            self.minted_tm += 1;
        }
        Some((
            reference(reply.var, base, depth, &delta),
            reply.ty_level,
        ))
    }

    fn kids(&mut self, slots: &[(Kid, Scope)]) -> Kids {
        let mut out = Vec::with_capacity(slots.len());
        let mut changed = false;
        for (child, _) in slots {
            let new = self.go(child);
            changed |= !same(child, &new);
            out.push(new);
        }
        Kids { kids: out, changed }
    }
}

struct Kids {
    kids: Vec<Kid>,
    changed: bool,
}

fn same(a: &Kid, b: &Kid) -> bool {
    match (a, b) {
        (Kid::Tm(a), Kid::Tm(b)) => Rc::ptr_eq(a, b),
        (Kid::Ty(a), Kid::Ty(b)) => Rc::ptr_eq(a, b),
        _ => false,
    }
}

/// Plan, choose and rebuild in one call — the entry the device uses.
///
/// `allow_types` switches the second spelling on; with it off this is §4's
/// mint alone, which is the stage the round measures first.
pub(crate) fn name(
    root: &Rc<Type>,
    gamma: &LocalCtx,
    prov: &HashMap<usize, (bool, CloId)>,
    threshold: u64,
    allow_types: bool,
    minter: &mut Minter<'_>,
) -> Naming {
    let root_frame = Rc::new(Frame {
        parent: None,
        binder: None,
        depth: gamma.entries.len() as u32,
    });
    let mut plan = Plan {
        gamma,
        nodes: Vec::new(),
        tm_ids: HashMap::new(),
        ty_ids: HashMap::new(),
        finish: Vec::new(),
        frames: Frames::default(),
        idx_memo: HashMap::new(),
        prov,
        reps: HashMap::new(),
        delta: HashMap::new(),
    };
    let root_id = plan.visit(&Kid::Ty(Rc::clone(root)), &root_frame);
    let choice = choose(&mut plan, root_id, threshold, allow_types);
    let mut build = Build {
        plan: &plan,
        named: &choice.named,
        minter,
        tm_out: HashMap::new(),
        ty_out: HashMap::new(),
        code_memo: HashMap::new(),
        taken: HashMap::new(),
        minted_tm: 0,
        minted_ty: 0,
        delta_sum: 0,
        delta_max: 0,
        declines: Declines::default(),
    };
    let root_out = match build.go(&Kid::Ty(Rc::clone(root))) {
        Kid::Ty(t) => t,
        Kid::Tm(_) => unreachable!("the root is a type"),
    };
    let graph = plan.nodes.len() as u64;
    let shared = plan.nodes.iter().filter(|n| n.indeg > 1).count() as u64;
    let chosen = choice.named.iter().filter(|n| n.is_some()).count() as u64;
    let (minted_tm, minted_ty) = (build.minted_tm, build.minted_ty);
    let (delta_sum, delta_max, declines) = (build.delta_sum, build.delta_max, build.declines);
    Naming {
        root: root_out,
        graph,
        shared,
        chosen,
        minted_tm,
        minted_ty,
        naive: choice.naive,
        emitted: choice.emitted,
        delta_sum,
        delta_max,
        declines,
    }
}

// -- the Ψ block -----------------------------------------------------------
//
// `docs/projected-tuple-tower-design.md` §11.4 and §12.7: the mint block is
// reserved with the goal block, allocated through `&self` into a `RefCell`,
// and **realized** at commit — pushed into Ψ through the same gate
// `push_gen_def` uses, with the declaration's own term strengthened out of the
// slots nothing took.
//
// The block sits **below** the goal block in the padded Ψ, so that
// `GoalArena::allocate`'s `goal_base − 1 − k` and the `strengthen_global(…,
// goal_base)` at the `on` sites are unchanged; what moves is every site that
// renumbers by the padding, which now takes the **total**
// (`Elaborator::global_padding`).
//
// With `L = |Ψ| + mint_cap + goal_cap`, mint `j` is `bindings[|Ψ| + j]` and so
// is `GlobalVar(goal_cap + mint_cap − 1 − j)`; a body stored here is already
// strengthened by `goal_cap + mint_cap − j`, which is exactly what scopes it
// in `Ψ ++ mints[0..j]` — so realization is a push plus one strengthening, and
// the minter can type mint `j` against the mints before it.

use std::cell::{Cell, RefCell};

use heather_kernel::subst::{GlobalEntry, GlobalSubst};
use heather_kernel::term::GlobalBinding;

/// One reserved slot's content, scoped in `Ψ ++ mints[0..j]`.
#[derive(Clone)]
pub(crate) struct Minted {
    pub(crate) name: String,
    pub(crate) ctx: LocalCtx,
    pub(crate) ty: Rc<Type>,
    pub(crate) level: Level,
    pub(crate) body: Rc<Term>,
    /// What carries this entry back into the padded numbering the readback is
    /// written in: `goal_cap + mint_cap − j`.
    shift: u32,
}

/// All mint state whose lifetime is one declaration attempt.
#[derive(Clone, Default)]
pub(crate) struct MintArena {
    cap: u32,
    entries: RefCell<Vec<Minted>>,
    /// The padded Ψ with the minted **bodies** in it, cached between
    /// allocations. `delta_psi` is rebuilt only where the elaborator has
    /// `&mut self`, and a mint is allocated where it has `&self` — so without
    /// this the block the elaborator's own whnf and conversion read is the
    /// placeholder padding, a reference into it does not unfold, and a
    /// component that used to reduce to `True` stops (measured, on
    /// `lib/std/int.hthr`'s `divmod_negative_bounds`). This is §12.7's last
    /// bullet, and it is not optional.
    world: RefCell<Option<(usize, heather_kernel::term::GlobalCtx)>>,
    /// Set when a mint was wanted and the block was not reserved: the
    /// declaration is elaborated again with capacity, exactly as a promoted
    /// implicit parameter's goal slot is.
    wanted: Cell<bool>,
}

/// The reserved block's size once a declaration has asked for one. The whole
/// showcase mints 115 (term) / 143 (both) names over 944 declarations and the
/// largest single reduct wants 83, so this is a bound and not a budget; a mint
/// past it declines and its component stays inline.
pub(crate) const MINT_CAP: u32 = 512;

impl MintArena {
    pub(crate) fn cap(&self) -> u32 {
        self.cap
    }

    pub(crate) fn used(&self) -> u32 {
        self.entries.borrow().len() as u32
    }

    pub(crate) fn configure(&mut self, cap: u32) {
        self.cap = cap;
        *self.world.get_mut() = None;
    }

    pub(crate) fn clear(&mut self) {
        self.entries.get_mut().clear();
        *self.world.get_mut() = None;
    }

    /// Ψ padded with this block and `goal_cap` goal placeholders, as every
    /// reference minted here is numbered against it.
    pub(crate) fn world(
        &self,
        psi: &heather_kernel::term::GlobalCtx,
        goal_cap: u32,
    ) -> heather_kernel::term::GlobalCtx {
        let len = psi.bindings.len();
        if let Some((at, w)) = self.world.borrow().as_ref()
            && *at == len
        {
            return w.clone();
        }
        let mut bindings = psi.bindings.to_vec();
        bindings.extend(self.bindings());
        bindings.resize(
            bindings.len() + goal_cap as usize,
            GlobalBinding::Tm {
                ctx: LocalCtx::nil(),
                layer: heather_kernel::layer::Layer::Code,
                ty: Rc::new(Type::Nat),
                level: Level::Zero,
                body: None,
            },
        );
        let w = heather_kernel::term::GlobalCtx::new(bindings);
        *self.world.borrow_mut() = Some((len, w.clone()));
        w
    }

    pub(crate) fn finish(&mut self) {
        self.cap = 0;
        self.wanted.set(false);
        self.clear();
    }

    /// A rollback point for the elaborator's speculative probes: a mint taken
    /// inside a discarded attempt is a Ψ definition nothing references, and it
    /// would still face the kernel gate at commit.
    pub(crate) fn mark(&self) -> usize {
        self.entries.borrow().len()
    }

    pub(crate) fn rollback(&self, mark: usize) {
        let mut entries = self.entries.borrow_mut();
        if entries.len() > mark {
            entries.truncate(mark);
            *self.world.borrow_mut() = None;
        }
    }

    /// Whether the padded world has to be built at all.
    pub(crate) fn live(&self) -> bool {
        self.cap > 0
    }

    /// Whether a mint asked for a block this attempt did not have.
    pub(crate) fn take_wanted(&self) -> bool {
        self.wanted.replace(false)
    }

    pub(crate) fn want(&self) {
        self.wanted.set(true);
    }

    /// Allocate one slot through `&self`. `ctx`/`ty`/`body` arrive already
    /// scoped in `Ψ ++ mints[0..j]` — which is the world the caller typed them
    /// in, so the strengthening is done once rather than twice.
    pub(crate) fn allocate(
        &self,
        goal_cap: u32,
        name: String,
        ctx: LocalCtx,
        ty: Rc<Type>,
        level: Level,
        body: Rc<Term>,
    ) -> Option<GlobalVar> {
        let mut entries = self.entries.borrow_mut();
        let j = entries.len() as u32;
        if j >= self.cap {
            self.wanted.set(true);
            return None;
        }
        entries.push(Minted {
            name,
            ctx,
            ty,
            level,
            body,
            shift: goal_cap + self.cap - j,
        });
        *self.world.borrow_mut() = None;
        Some(GlobalVar(goal_cap + self.cap - 1 - j))
    }

    /// The bindings the padded Ψ carries for the block — with the minted
    /// **bodies**, which is what lets the elaborator's own whnf and conversion
    /// unfold a mint as soon as it exists (§12.7's last bullet).
    pub(crate) fn bindings(&self) -> Vec<GlobalBinding> {
        let entries = self.entries.borrow();
        (0..self.cap as usize)
            .map(|j| match entries.get(j) {
                // Re-scoped from `Ψ ++ mints[0..j]` back into the padded world
                // the readback is numbered in.
                Some(m) => GlobalBinding::Tm {
                    ctx: m.ctx.shift_global(m.shift),
                    layer: heather_kernel::layer::Layer::Code,
                    ty: Rc::new(m.ty.shift_global(m.shift)),
                    level: m.level.clone(),
                    body: Some(Rc::new(m.body.shift_global(m.shift))),
                },
                None => GlobalBinding::Tm {
                    ctx: LocalCtx::nil(),
                    layer: heather_kernel::layer::Layer::Code,
                    ty: Rc::new(Type::Nat),
                    level: Level::Zero,
                    body: None,
                },
            })
            .collect()
    }

    /// The realized block, in push order, and what the declaration's own term
    /// must then be strengthened by.
    pub(crate) fn realize(&self) -> (Vec<Minted>, u32) {
        let entries = self.entries.borrow();
        (entries.clone(), self.cap - entries.len() as u32)
    }
}

fn zeros(g: u32) -> GlobalSubst {
    GlobalSubst {
        entries: (0..g)
            .map(|_| GlobalEntry::Tm(Rc::new(Term::Zero)))
            .collect(),
    }
}

pub(crate) fn strengthen_tm(t: &Rc<Term>, g: u32) -> Term {
    if g == 0 {
        return (**t).clone();
    }
    t.apply_global(&zeros(g))
}

pub(crate) fn strengthen_ty(t: &Type, g: u32) -> Type {
    if g == 0 {
        return t.clone();
    }
    t.apply_global(&zeros(g))
}

pub(crate) fn strengthen_ctx(c: &LocalCtx, g: u32) -> LocalCtx {
    if g == 0 {
        return c.clone();
    }
    c.apply_global(&zeros(g))
}

// -- the site --------------------------------------------------------------

// The firing gate is the **declaration**, and its answer is the naming's.
//
// A node count on the rewriter's reduct cannot be the gate: that reduct is a
// weak head normal form and is small at every site, while the object this
// round exists to shrink is the *deep* one under it. So the question is asked
// of the object itself — does the naming take a name here — and the answer is
// then applied to the **whole declaration**, through the capacity restart: the
// first attempt has no mint block, asks for one if any site names anything,
// and the second attempt spells every site it can from the readback.
//
// Per *site* is the shape that does not work, measured: a declaration with the
// rewriter's reduct at some sites and a named deep normal form at others makes
// the kernel convert one spelling against the other, and `qt_pure`'s misses
// double where the uniform spelling of stage one divided them by thirty (the
// tower design's §11.3). One declaration, one spelling.
//
// The ~900 declarations with nothing worth naming never reach the second
// attempt, so they keep the rewriter's reduct **byte for byte** and stage
// one's fourteen `list::*` regressions are not inherited.

impl crate::Elaborator {
    /// The reduct `build_ctor` reads its components out of, with the readback
    /// of `docs/name-per-value-design.md` §4/§8.3 installed: the value the
    /// machine already produced, spelled back with its shared sub-values
    /// **named** — a term mint referenced `u^δ`, a type mint referenced
    /// `El l (u^δ)` over its code.
    ///
    /// Every failure is a **decline** and keeps `reduct`, which is the
    /// parent's behaviour at this site and always safe.
    pub(crate) fn mint_ctor_reduct(
        &self,
        cx: &crate::Cx,
        pre_whnf: &Type,
        reduct: Type,
        span: heather_syntax::Span,
    ) -> crate::R<Type> {
        if !firing() || !self.meta_pushed.borrow().is_empty() {
            return Ok(reduct);
        }
        if !matches!(cx.gamma.base, CtxBase::Nil) {
            return Ok(reduct);
        }
        // Already a name: the registry's copy of a registered lowering is the
        // spelling every structural reader anchors on, and reading it back
        // would throw that name away (§11.3's first rule).
        if self.unspell_here(pre_whnf).is_some() {
            return Ok(reduct);
        }
        let _phase = crate::stats::guard(crate::stats::Timer::ElabWhnf);
        let world = self.semantic_oracle().world().clone();
        let Some((root, prov)) =
            crate::rbemit::whnf_type_from_value_with_prov(&world, &cx.gamma, pre_whnf, self.fuel)
        else {
            crate::stats::count(crate::stats::Counter::MintsDeclined);
            if std::env::var("HEATHER_RB_MINTS").is_ok() {
                eprintln!("rb mint DECLINED span={}", span.start);
            }
            return Ok(reduct);
        };
        let root = Rc::new(root);
        let goal_cap = self.attempt.goal_arena.base();
        let cap = self.attempt.mint_arena.cap();
        let arena = &self.attempt.mint_arena;
        // With no block reserved this pass only *asks* for one: every chosen
        // name is refused, the naming rebuilds to the unnamed spelling, and
        // `elab_decl_one` elaborates the declaration again with capacity.
        if cap == 0 {
            let mut ask = |_: &LocalCtx, _: &Rc<Term>| -> Option<MintReply> {
                arena.want();
                None
            };
            let n = name(&root, &cx.gamma, &prov, threshold(), types_too(), &mut ask);
            if std::env::var("HEATHER_RB_MINTS").is_ok() {
                let d = n.declines;
                eprintln!(
                    "rb mint ASK span={} naive={} emitted={} graph={} shared={} chosen={} \
                     refused={} unscoped={}",
                    span.start, n.naive, n.emitted, n.graph, n.shared, n.chosen,
                    d.refused, d.unscoped
                );
            }
            // Capacity discovery is **speculative**, and the attempt that
            // discovers it must stop here rather than run to the kernel gate:
            // otherwise a declaration that names anything is gated twice, and
            // its whole conversion bill is counted twice with it (measured,
            // `qt_pure` at exactly 2× the parent's misses). `elab_decl_one`
            // reads the arena's request before it reads this error.
            if arena.take_wanted() {
                arena.want();
                return crate::err(
                    "internal: the readback wants a mint block (capacity discovery)",
                    span,
                );
            }
            return Ok(reduct);
        }
        // The mints are typed one at a time against `Ψ ++ mints[0..j]`, which
        // is what makes the *next* body checkable against this one: kernel
        // syntax is fully annotated, so `infer_term` gives the statement and
        // the readback supplies only `Δ` (the tower design's §12.6).
        // The mints are typed one at a time against `Ψ ++ mints[0..j]`, which
        // is what makes the *next* body checkable against this one: kernel
        // syntax is fully annotated, so `infer_term` gives the statement and
        // the readback supplies only `Δ` (the tower design's §12.6). Typing
        // them in the padded world instead — which carries the same bindings
        // — was tried and is worse on every column, measured: the goal block
        // between Ψ and the mints costs the kernel conversions it need not do.
        let owner = crate::stats::current_item().map_or_else(|| "-".to_string(), |(_, i)| i);
        let mut slots = self.psi.bindings.to_vec();
        let fuel = self.fuel;
        let mut untyped = 0u64;
        let mut minter = |ctx: &LocalCtx, body: &Rc<Term>| -> Option<MintReply> {
            let j = arena.used();
            let g = goal_cap + cap - j;
            let ctx_here = strengthen_ctx(ctx, g);
            let body_here = Rc::new(strengthen_tm(body, g));
            let here = heather_kernel::term::GlobalCtx::new(slots.clone());
            let (ty, level) = match heather_kernel::typing::infer_term(
                &here,
                0,
                heather_kernel::layer::Layer::Code,
                &ctx_here,
                &body_here,
                fuel,
            ) {
                Ok(r) => r,
                Err(_) => {
                    untyped += 1;
                    return None;
                }
            };
            let ty_level = match &ty {
                Type::Ty(l) => Some(l.clone()),
                _ => None,
            };
            let ty = Rc::new(ty);
            slots.push(heather_kernel::term::GlobalBinding::defined_tm(
                ctx_here.clone(),
                heather_kernel::layer::Layer::Code,
                Rc::clone(&ty),
                level.clone(),
                Rc::clone(&body_here),
            ));
            let var = arena.allocate(
                goal_cap,
                format!("mint{j}"),
                ctx_here,
                ty,
                level,
                body_here,
            )?;
            Some(MintReply { var, ty_level })
        };
        let mark = arena.mark();
        let named = name(&root, &cx.gamma, &prov, threshold(), types_too(), &mut minter);
        drop(minter);
        let d = named.declines;
        let minted = named.minted_tm + named.minted_ty;

        if std::env::var("HEATHER_RB_MINTS").is_ok() {
            eprintln!(
                "rb mint item={owner} span={} naive={} emitted={} tm={} ty={} \
                 dunscoped={} ddisagree={} drefused={} untyped={untyped} \
                 dsum={} dmax={} lost={}",
                span.start,
                named.naive,
                named.emitted,
                named.minted_tm,
                named.minted_ty,
                d.unscoped,
                d.disagree,
                d.refused,
                named.delta_sum,
                named.delta_max,
                d.lost,
            );
        }
        if minted == 0 {
            crate::stats::count(crate::stats::Counter::MintsDeclined);
        }
        // The kernel is the gate here too. Every mint is typed on its own, but
        // a well-typed name is not yet a well-typed *spelling*: the occurrence
        // carries the statement `infer_term` chose, and the site may want
        // another. So the named answer is typed as a whole before it is
        // handed to `build_ctor`, and a refusal is a **decline** — the block
        // rolls back and the rewriter's reduct stands, which is stage one's
        // behaviour and always safe. Without it the device writes a term the
        // kernel rejects at the declaration's own gate, with nothing to say
        // which name did it (measured, on `x86_64`'s `fetched_executes`).
        if minted > 0 && std::env::var("HEATHER_RB_NOROOTGATE").is_err() {
            // The **goal** world, not the arena's padded one: a readback's
            // answer may mention a goal, and the padding carries a
            // placeholder where the goal's real statement is. Typed against
            // the placeholder, a perfectly well-typed spelling is refused —
            // measured, as `qt_pure` declining every name it chose and paying
            // the restart for nothing.
            let here = self.goal_psi();
            let ok = heather_kernel::typing::infer_type(
                &here,
                0,
                heather_kernel::layer::Layer::Code,
                &cx.gamma,
                &named.root,
                self.fuel,
            );
            if ok.is_err() {
                arena.rollback(mark);
                crate::stats::count(crate::stats::Counter::MintsDeclined);
                if std::env::var("HEATHER_RB_MINTS").is_ok() {
                    eprintln!("rb mint UNTYPED-ROOT span={} err={:?}", span.start, ok.err());
                }
                return Ok(reduct);
            }
        }
        let t = (*named.root).clone();
        Ok(self
            .unspell_here(&t)
            .or_else(|| self.unspell_sum_components(&t))
            .unwrap_or(t))
    }
}

/// Whether the **type** spelling is on. Both spellings are one device
/// (design §8.3); the flag exists so the round can measure the term mint alone
/// first, which is the stage its sub-bars are stated for.
fn types_too() -> bool {
    static M: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *M.get_or_init(|| std::env::var("HEATHER_RB_TERMS_ONLY").is_err())
}

/// Whether the device is installed. **Opt-in** (`HEATHER_RB_MINT=1`), because
/// the round does not land it: at a threshold the structural readers tolerate
/// it declines on the items it exists for, and
/// `docs/name-per-value-design.md` §9.5 is the whole of that story. With the
/// variable unset the default path is the parent's byte for byte;
/// `HEATHER_RB` naming one of the two design passes' instruments also stands
/// the device down, so their runs stay reproducible.
pub(crate) fn firing() -> bool {
    static M: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *M.get_or_init(|| {
        std::env::var("HEATHER_RB_MINT").is_ok() && std::env::var("HEATHER_RB").is_err()
    })
}

#[cfg(test)]
mod tests {
    use heather_kernel::layer::Layer;
    use heather_kernel::term::{GlobalCtx, LocalVar};

    use super::*;

    const FUEL: u64 = 1 << 20;

    fn nat() -> Rc<Type> {
        Rc::new(Type::Nat)
    }

    /// A `Succ` chain over `base`: `n` nodes of shared mass, the smallest
    /// thing that can clear [`THRESHOLD`].
    /// The threshold these fixtures are written against. Deliberately not
    /// [`THRESHOLD`]: what they test is the device's rules — the `Δ`, the
    /// `δ`, the two spellings, the declines — and pinning them to the unit in
    /// force would only make every fixture bigger when it moves.
    const T: u64 = 64;

    /// Long enough that naming it clears [`T`] at two occurrences.
    const BIG: usize = 400;

    fn chain(n: usize, base: Term) -> Rc<Term> {
        let mut t = Rc::new(base);
        for _ in 0..n {
            t = Rc::new(Term::Succ(t));
        }
        t
    }

    fn id_of(lhs: &Rc<Term>, rhs: Term) -> Rc<Type> {
        Rc::new(Type::Id {
            level: Level::Zero,
            ty: nat(),
            lhs: Rc::clone(lhs),
            rhs: Rc::new(rhs),
        })
    }

    /// Two occurrences of one shared child, at the **same** depth.
    fn twice(shared: &Rc<Term>) -> Rc<Type> {
        Rc::new(Type::Sum {
            lhs_level: Level::Zero,
            rhs_level: Level::Zero,
            lhs: id_of(shared, Term::Zero),
            rhs: id_of(shared, Term::Succ(Rc::new(Term::Zero))),
        })
    }

    /// The harness's minter: type every body against the empty Ψ — which is
    /// the landed device's route too (the tower design's §12.6: kernel syntax
    /// is fully annotated, so the readback supplies only `Δ`) — and hand back
    /// a reference into a scratch block.
    fn named(root: &Rc<Type>, gamma: &LocalCtx) -> (Naming, Vec<(LocalCtx, Rc<Term>, Type)>) {
        let mut mints: Vec<(LocalCtx, Rc<Term>, Type)> = Vec::new();
        let prov = HashMap::new();
        let out = {
            let mut minter = |ctx: &LocalCtx, body: &Rc<Term>| {
                let (ty, _) = heather_kernel::typing::infer_term(
                    &GlobalCtx::default(),
                    0,
                    Layer::Code,
                    ctx,
                    body,
                    FUEL,
                )
                .ok()?;
                let ty_level = match &ty {
                    Type::Ty(l) => Some(l.clone()),
                    _ => None,
                };
                mints.push((ctx.clone(), Rc::clone(body), ty));
                Some(MintReply {
                    var: GlobalVar(mints.len() as u32 - 1),
                    ty_level,
                })
            };
            name(root, gamma, &prov, T, true, &mut minter)
        };
        (out, mints)
    }

    fn sides(root: &Type) -> (Rc<Term>, Rc<Term>) {
        let Type::Sum { lhs, rhs, .. } = root else {
            panic!("expected the fixture's `+`, got {root:?}");
        };
        let (Type::Id { lhs: a, .. }, Type::Id { lhs: b, .. }) = (&**lhs, &**rhs) else {
            panic!("expected the fixture's two `Id`s");
        };
        (Rc::clone(a), Rc::clone(b))
    }

    /// A **closed** shared value: one mint, `Δ` empty, and both occurrences
    /// are the same reference with an empty substitution.
    #[test]
    fn a_closed_shared_value_is_named_once_over_the_empty_context() {
        let gamma = LocalCtx::nil().extended(nat(), Level::Zero);
        let root = twice(&chain(BIG, Term::Zero));
        let (out, mints) = named(&root, &gamma);
        assert_eq!((out.minted_tm, out.minted_ty), (1, 0));
        assert_eq!(mints.len(), 1);
        assert_eq!(mints[0].0.entries.len(), 0, "a closed value needs no Δ");
        let (a, b) = sides(&out.root);
        assert_eq!(&*a, &*b);
        assert!(
            matches!(&*a, Term::GlobalTm { subst, .. } if subst.terms.is_empty()),
            "expected `u^δ` with an empty δ, got {a:?}"
        );
        // The emitted column is the **planned** one, as the spike's was: the
        // body once plus a reference per occurrence, against the tree.
        assert!(out.emitted < out.naive * 3 / 5, "{} / {}", out.emitted, out.naive);
    }

    /// An **open** shared value, against the closed control above: `Δ` is
    /// exactly the one entry the body reads — not the whole of `Γ` — and the
    /// occurrence's `δ` supplies it at that occurrence's own index.
    #[test]
    fn an_open_shared_value_is_scoped_in_the_variables_it_reads() {
        // `Γ = _ : Nat, _ : Nat`, and the body reads only the outer one.
        let gamma = LocalCtx::nil()
            .extended(nat(), Level::Zero)
            .extended(nat(), Level::Zero);
        let root = twice(&chain(BIG, Term::Var(LocalVar(1))));
        let (out, mints) = named(&root, &gamma);
        assert_eq!((out.minted_tm, out.minted_ty), (1, 0));
        assert_eq!(
            mints[0].0.entries.len(),
            1,
            "Δ is the value's free variables, not Γ: {:?}",
            mints[0].0.entries.len()
        );
        assert_eq!(out.delta_max, 1);
        let (a, _) = sides(&out.root);
        let Term::GlobalTm { subst, .. } = &*a else {
            panic!("expected `u^δ`, got {a:?}");
        };
        assert_eq!(subst.source_len(), 2, "δ̂ is the occurrence's own depth");
        assert_eq!(subst.terms.len(), 1);
        assert_eq!(&*subst.terms[0], &Term::Var(LocalVar(1)));
    }

    /// The same value read under a binder: the mint is **depth-independent**,
    /// so the body is the same and only the occurrence's `δ` moves.
    #[test]
    fn a_value_under_a_binder_is_named_in_that_binder_alone() {
        let gamma = LocalCtx::nil();
        let root = Rc::new(Type::Pi {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: nat(),
            cod: twice(&chain(BIG, Term::Var(LocalVar(0)))),
        });
        let (out, mints) = named(&root, &gamma);
        assert_eq!((out.minted_tm, out.minted_ty), (1, 0));
        assert_eq!(mints[0].0.entries.len(), 1);
        let Type::Pi { cod, .. } = &*out.root else {
            panic!("expected a `Π`");
        };
        let (a, _) = sides(cod);
        let Term::GlobalTm { subst, .. } = &*a else {
            panic!("expected `u^δ`, got {a:?}");
        };
        assert_eq!(subst.source_len(), 1);
        assert_eq!(&*subst.terms[0], &Term::Var(LocalVar(0)));
    }

    /// Below the threshold nothing is named: a name costs its body plus a
    /// reference per use, and most shared nodes are too small to pay for it.
    #[test]
    fn a_small_shared_value_stays_inline() {
        let gamma = LocalCtx::nil();
        let root = twice(&chain(10, Term::Zero));
        let (out, mints) = named(&root, &gamma);
        assert_eq!((out.minted_tm, out.minted_ty, mints.len()), (0, 0, 0));
        assert_eq!(out.emitted, out.naive);
    }

    /// The **negative control** the whole device rests on: a minter that
    /// refuses — a full block, a body the kernel will not type — leaves the
    /// component inline, and the answer is still the readback's own spelling.
    #[test]
    fn a_refused_mint_declines_to_the_inline_component() {
        let gamma = LocalCtx::nil();
        let root = twice(&chain(BIG, Term::Zero));
        let mut refuse = |_: &LocalCtx, _: &Rc<Term>| None;
        let out = name(&root, &gamma, &HashMap::new(), T, true, &mut refuse);
        assert_eq!((out.minted_tm, out.minted_ty), (0, 0));
        assert_eq!(out.declines.refused, 1);
        let (a, b) = sides(&out.root);
        assert!(Rc::ptr_eq(&a, &b), "the component is still shared, inline");
        assert!(matches!(&*a, Term::Succ(_)));
    }

    /// A shared **type**: what is minted is its code, and the occurrence is
    /// `El l (u^δ)` — the second spelling of the one device (design §8.3).
    #[test]
    fn a_shared_type_is_named_through_its_code() {
        let gamma = LocalCtx::nil();
        // A `Π` tower over `Nat`: a type with enough nodes to clear T.
        let mut big = nat();
        for _ in 0..80 {
            big = Rc::new(Type::Pi {
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom: nat(),
                cod: big,
            });
        }
        let root = Rc::new(Type::Sum {
            lhs_level: Level::Zero,
            rhs_level: Level::Zero,
            lhs: Rc::clone(&big),
            rhs: Rc::clone(&big),
        });
        let (out, mints) = named(&root, &gamma);
        assert_eq!((out.minted_tm, out.minted_ty), (0, 1));
        assert!(
            matches!(&mints[0].2, Type::Ty(_)),
            "a code's statement is a universe, got {:?}",
            mints[0].2
        );
        assert!(matches!(&*mints[0].1, Term::TmPi { .. }), "the body is ⌜T⌝");
        let Type::Sum { lhs, rhs, .. } = &*out.root else {
            panic!("expected a `+`");
        };
        for side in [lhs, rhs] {
            let Type::El { tm, .. } = &**side else {
                panic!("expected `El (u^δ)`, got {side:?}");
            };
            assert!(matches!(&**tm, Term::GlobalTm { .. }));
        }
        assert!(out.emitted < out.naive * 3 / 4, "{} / {}", out.emitted, out.naive);
    }

    /// The type spelling's own negative: a former `code_of` has no arm for
    /// declines to the inline type rather than writing an `El` of nothing.
    #[test]
    fn a_type_with_no_code_declines_to_the_inline_component() {
        let gamma = LocalCtx::nil();
        let mut big = nat();
        for _ in 0..80 {
            big = Rc::new(Type::Pi {
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom: nat(),
                cod: big,
            });
        }
        // `UPi` is layer m and has no code (`code.rs`'s last arm).
        let no_code = Rc::new(Type::UPi {
            num_vars: 1,
            level: Level::Zero,
            body: big,
        });
        let root = Rc::new(Type::Sum {
            lhs_level: Level::Zero,
            rhs_level: Level::Zero,
            lhs: Rc::clone(&no_code),
            rhs: Rc::clone(&no_code),
        });
        let (out, mints) = named(&root, &gamma);
        assert_eq!((out.minted_tm, out.minted_ty), (0, 0));
        assert!(mints.is_empty());
        assert_eq!(out.declines.refused, 1);
        let Type::Sum { lhs, .. } = &*out.root else {
            panic!("expected a `+`");
        };
        assert!(matches!(&**lhs, Type::UPi { .. }), "still inline");
    }

    /// `code_of_spliced` is `code_of` with its recursion supplied — the pairing
    /// the two are written to keep, checked rather than trusted.
    #[test]
    fn the_spliced_encoder_agrees_with_code_of() {
        let cases: Vec<Rc<Type>> = vec![
            nat(),
            Rc::new(Type::Ty(Level::Zero)),
            Rc::new(Type::Pi {
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom: nat(),
                cod: nat(),
            }),
            Rc::new(Type::Sigma {
                fst_level: Level::Zero,
                snd_level: Level::Zero,
                fst: nat(),
                snd: nat(),
            }),
            Rc::new(Type::Sum {
                lhs_level: Level::Zero,
                rhs_level: Level::Zero,
                lhs: nat(),
                rhs: nat(),
            }),
            Rc::new(Type::Vec {
                level: Level::Zero,
                elem: nat(),
                len: Rc::new(Term::Zero),
            }),
            Rc::new(Type::El {
                level: Level::Zero,
                tm: Rc::new(Term::TmNat),
            }),
            Rc::new(Type::UPi {
                num_vars: 1,
                level: Level::Zero,
                body: nat(),
            }),
        ];
        for t in cases {
            let kids: Option<Vec<Rc<Term>>> = slots_ty(&t)
                .into_iter()
                .map(|(kid, _)| match kid {
                    Kid::Ty(c) => crate::code::code_of(&c).map(Rc::new),
                    Kid::Tm(c) => Some(c),
                })
                .collect();
            let spliced = kids.and_then(|kids| crate::code::code_of_spliced(&t, &kids));
            assert_eq!(spliced, crate::code::code_of(&t), "at {t:?}");
        }
    }
}
