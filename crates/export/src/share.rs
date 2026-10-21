//! Sharing for the text route (design §5.6). A kernel term is a DAG, and the
//! translation unfolds it into a tree: the `List` closure's trees run to
//! hundreds of kilobytes per declaration, which Lean's parser does not get
//! through. The kernel route keeps the DAG in its node table; the text route
//! gets it back here, by hoisting every subterm that occurs more than once
//! into a reducible definition of its own.
//!
//! An open subterm is abstracted over the variables it uses and those their
//! types need, in context order, so its definition is well scoped by
//! construction: `fun (xa : Da) … (xk : Dk) => e`, used as `@s xa … xk`, and
//! keyed by that closed body: two occurrences share exactly when it is the
//! same term. Subterms with a hole stay where they are: a hole is recovered from
//! the expected type around it.
//!
//! The definitions are δ-equal to what they replace, and Lean checks them
//! like any other declaration, so sharing adds nothing to trust.

use crate::Hx;
use std::sync::Arc as Rc;
use std::collections::HashMap;

/// A node with its children interned.
#[derive(Hash, PartialEq, Eq)]
enum Key {
    Var(u32),
    Sort(u64),
    Pi(u32, u32),
    Lam(u32, u32),
    App(u32, u32),
    Const(&'static str, Vec<u64>),
    Global(usize),
    Named(String, Vec<u64>),
    Nat(String),
    Hole,
}

struct Info {
    size: u64,
    /// The de Bruijn indices the node leaves free, ascending.
    free: Vec<u32>,
    hole: bool,
}

/// Only subterms at least this large are worth a definition and its
/// arguments at every use.
const MIN_SIZE: u64 = 24;

#[derive(Default)]
pub(crate) struct Share {
    /// The key prefix the definitions are named under (`list::`).
    ns: String,
    ids: HashMap<Key, u32>,
    info: Vec<Info>,
    /// A context, interned: (enclosing context, binder domain) → id; 0 is
    /// the empty context.
    ctxs: HashMap<(u32, u32), u32>,
    /// Occurrences of each (node, context it needs).
    counts: HashMap<(u32, u32), u32>,
    /// Definitions made, by the id of their (closed) body.
    made: HashMap<u32, String>,
    /// Hoisted definitions not yet printed, in dependency order.
    pub(crate) fresh: Vec<(String, Hx)>,
    /// The two passes' results by (node address, context id): the input is
    /// a DAG, and a node met again in the same context is not walked again.
    /// Counting a shared node again counts its own site, not its subterms':
    /// those occur once inside its definition.
    counted: HashMap<(usize, u32), u32>,
    rewritten: HashMap<(usize, u32), (u32, Hx, Vec<u32>)>,
}

/// A binder on the way down: its context id, its domain as printed, and the
/// binder levels that domain uses.
struct Scope {
    ctx: u32,
    dom: Hx,
    levels: Vec<u32>,
}

impl Share {
    pub(crate) fn new(ns: &str) -> Share {
        Share { ns: ns.to_string(), ..Share::default() }
    }

    fn intern(&mut self, key: Key, info: impl FnOnce(&Self) -> Info) -> u32 {
        if let Some(&id) = self.ids.get(&key) {
            return id;
        }
        let info = info(self);
        let id = self.info.len() as u32;
        self.info.push(info);
        self.ids.insert(key, id);
        id
    }

    fn ctx(&mut self, outer: u32, dom: u32) -> u32 {
        let next = self.ctxs.len() as u32 + 1;
        *self.ctxs.entry((outer, dom)).or_insert(next)
    }

    fn leaf(&mut self, key: Key) -> u32 {
        let (free, hole) = match &key {
            Key::Var(i) => (vec![*i], false),
            Key::Hole => (vec![], true),
            _ => (vec![], false),
        };
        self.intern(key, |_| Info { size: 1, free, hole })
    }

    fn binder(&mut self, pi: bool, a: u32, b: u32) -> u32 {
        let key = if pi { Key::Pi(a, b) } else { Key::Lam(a, b) };
        self.intern(key, |s| {
            let (ia, ib) = (&s.info[a as usize], &s.info[b as usize]);
            let mut free: Vec<u32> = ia.free.iter().copied().chain(ib.free.iter().filter(|&&j| j > 0).map(|j| j - 1)).collect();
            free.sort_unstable();
            free.dedup();
            Info { size: 1 + ia.size + ib.size, free, hole: ia.hole || ib.hole }
        })
    }

    fn app(&mut self, f: u32, a: u32) -> u32 {
        self.intern(Key::App(f, a), |s| {
            let (i_f, ia) = (&s.info[f as usize], &s.info[a as usize]);
            let mut free: Vec<u32> = i_f.free.iter().chain(&ia.free).copied().collect();
            free.sort_unstable();
            free.dedup();
            Info { size: 1 + i_f.size + ia.size, free, hole: i_f.hole || ia.hole }
        })
    }

    fn leaf_key(t: &Hx) -> Key {
        match t {
            Hx::Var(i) => Key::Var(*i),
            Hx::Sort(l) => Key::Sort(l.0),
            Hx::Const(n, ls) => Key::Const(n, ls.iter().map(|l| l.0).collect()),
            Hx::Global(g) => Key::Global(*g),
            Hx::Named(k, ls) => Key::Named(k.clone(), ls.clone()),
            Hx::NatLit(n) => Key::Nat(n.clone()),
            Hx::Hole => Key::Hole,
            Hx::Pi(..) | Hx::Lam(..) | Hx::App(..) => unreachable!("not a leaf"),
        }
    }

    /// The (node, context) a node at this depth is shared by, when it is a
    /// candidate at all.
    fn site(&self, id: u32, ctxs: &[u32]) -> Option<(u32, u32)> {
        let info = &self.info[id as usize];
        if info.hole || info.size < MIN_SIZE {
            return None;
        }
        // The innermost variable used is the one with the smallest index.
        let ctx = match info.free.first() {
            None => 0,
            Some(&i) => ctxs[ctxs.len() - 1 - i as usize],
        };
        Some((id, ctx))
    }

    fn id_of(&mut self, t: &Hx, memo: &mut HashMap<usize, u32>) -> u32 {
        if let Some(&id) = memo.get(&(t as *const Hx as usize)) {
            return id;
        }
        let id = match t {
            Hx::Pi(a, b) | Hx::Lam(a, b) => {
                let (ia, ib) = (self.id_of(a, memo), self.id_of(b, memo));
                self.binder(matches!(t, Hx::Pi(..)), ia, ib)
            }
            Hx::App(f, a) => {
                let (i_f, ia) = (self.id_of(f, memo), self.id_of(a, memo));
                self.app(i_f, ia)
            }
            _ => self.leaf(Self::leaf_key(t)),
        };
        memo.insert(t as *const Hx as usize, id);
        id
    }

    /// First pass: count every candidate's occurrences. Returns the node's id.
    pub(crate) fn count(&mut self, t: &Hx) -> u32 {
        self.count_in(t, &mut Vec::new())
    }

    fn count_in(&mut self, t: &Hx, ctxs: &mut Vec<u32>) -> u32 {
        let key = (t as *const Hx as usize, ctxs.last().copied().unwrap_or(0));
        if let Some(&id) = self.counted.get(&key) {
            if let Some(site) = self.site(id, ctxs) {
                *self.counts.entry(site).or_default() += 1;
            }
            return id;
        }
        let id = match t {
            Hx::Pi(a, b) | Hx::Lam(a, b) => {
                let ia = self.count_in(a, ctxs);
                let outer = ctxs.last().copied().unwrap_or(0);
                let c = self.ctx(outer, ia);
                ctxs.push(c);
                let ib = self.count_in(b, ctxs);
                ctxs.pop();
                self.binder(matches!(t, Hx::Pi(..)), ia, ib)
            }
            Hx::App(f, a) => {
                let (i_f, ia) = (self.count_in(f, ctxs), self.count_in(a, ctxs));
                self.app(i_f, ia)
            }
            _ => self.leaf(Self::leaf_key(t)),
        };
        if let Some(site) = self.site(id, ctxs) {
            *self.counts.entry(site).or_default() += 1;
        }
        self.counted.insert(key, id);
        id
    }

    /// Second pass: `t` with every shared subterm replaced by a use of its
    /// definition; definitions made on the way are queued in `fresh`.
    pub(crate) fn rewrite(&mut self, t: &Hx) -> Hx {
        self.rewrite_in(t, &mut Vec::new()).1
    }

    /// The node's id, its rewrite, and the binder levels below it that the
    /// rewrite uses, ascending. A use of a shared definition passes the
    /// binders its domains need too, so the rewrite can use more than the
    /// original.
    fn rewrite_in(&mut self, t: &Hx, scopes: &mut Vec<Scope>) -> (u32, Hx, Vec<u32>) {
        let key = (t as *const Hx as usize, scopes.last().map_or(0, |s| s.ctx));
        if let Some(out) = self.rewritten.get(&key) {
            return out.clone();
        }
        let out = self.rewrite_node(t, scopes);
        self.rewritten.insert(key, out.clone());
        out
    }

    fn rewrite_node(&mut self, t: &Hx, scopes: &mut Vec<Scope>) -> (u32, Hx, Vec<u32>) {
        let depth = scopes.len();
        let (id, out, levels) = match t {
            Hx::Pi(a, b) | Hx::Lam(a, b) => {
                let (ia, ra, la) = self.rewrite_in(a, scopes);
                let outer = scopes.last().map_or(0, |s| s.ctx);
                let c = self.ctx(outer, ia);
                scopes.push(Scope { ctx: c, dom: ra, levels: la });
                let (ib, rb, lb) = self.rewrite_in(b, scopes);
                let Scope { dom: ra, levels: la, .. } = scopes.pop().unwrap();
                let pi = matches!(t, Hx::Pi(..));
                let out = if pi { Hx::Pi(Rc::new(ra), Rc::new(rb)) } else { Hx::Lam(Rc::new(ra), Rc::new(rb)) };
                (self.binder(pi, ia, ib), out, union(&la, lb.iter().copied().filter(|&l| (l as usize) < depth)))
            }
            Hx::App(f, a) => {
                let ((i_f, rf, lf), (ia, ra, la)) = (self.rewrite_in(f, scopes), self.rewrite_in(a, scopes));
                (self.app(i_f, ia), Hx::App(Rc::new(rf), Rc::new(ra)), union(&lf, la.into_iter()))
            }
            Hx::Var(i) => (self.leaf(Key::Var(*i)), t.clone(), vec![(depth - 1 - *i as usize) as u32]),
            _ => (self.leaf(Self::leaf_key(t)), t.clone(), vec![]),
        };
        let ctxs: Vec<u32> = scopes.iter().map(|s| s.ctx).collect();
        let Some(site) = self.site(id, &ctxs) else { return (id, out, levels) };
        if self.counts.get(&site).copied().unwrap_or(0) < 2 {
            return (id, out, levels);
        }
        // The definition abstracts the binders the rewrite uses and those
        // their domains need, in order; the rest drop out of its indices.
        // It is keyed by its own closed body, so the same definition met at
        // another depth is the same one.
        let mut keep = vec![false; depth];
        let mut todo = levels.clone();
        while let Some(l) = todo.pop() {
            if !std::mem::replace(&mut keep[l as usize], true) {
                todo.extend(&scopes[l as usize].levels);
            }
        }
        let kept: Vec<u32> = (0..depth as u32).filter(|&l| keep[l as usize]).collect();
        let mut map = vec![None; depth];
        for (j, &l) in kept.iter().enumerate() {
            map[l as usize] = Some(j as u32);
        }
        let mut body = remap(&out, depth, &map, kept.len() as u32, 0);
        for (j, &l) in kept.iter().enumerate().rev() {
            let dom = remap(&scopes[l as usize].dom, l as usize, &map, j as u32, 0);
            body = Hx::Lam(Rc::new(dom), Rc::new(body));
        }
        let key = self.id_of(&body, &mut HashMap::new());
        let name = match self.made.get(&key) {
            Some(n) => n.clone(),
            None => {
                let name = format!("{}share#{}", self.ns, self.made.len());
                self.fresh.push((name.clone(), body));
                self.made.insert(key, name.clone());
                name
            }
        };
        let mut use_ = Hx::Named(name, vec![]);
        for &l in &kept {
            use_ = Hx::App(Rc::new(use_), Rc::new(Hx::Var((depth - 1 - l as usize) as u32)));
        }
        (id, use_, kept)
    }
}

fn union(a: &[u32], b: impl Iterator<Item = u32>) -> Vec<u32> {
    let mut out: Vec<u32> = a.iter().copied().chain(b).collect();
    out.sort_unstable();
    out.dedup();
    out
}

/// `t`, a term under `outer` binders (and `cut` more of its own), moved
/// under `new_outer` binders: binder level `l` becomes level `map[l]`.
fn remap(t: &Hx, outer: usize, map: &[Option<u32>], new_outer: u32, cut: u32) -> Hx {
    fn go(t: &Hx, outer: usize, map: &[Option<u32>], new_outer: u32, cut: u32, memo: &mut HashMap<(usize, u32), Rc<Hx>>) -> Rc<Hx> {
        let key = (t as *const Hx as usize, cut);
        if let Some(out) = memo.get(&key) {
            return out.clone();
        }
        let out = Rc::new(match t {
            Hx::Var(i) if *i >= cut => {
                let level = outer - 1 - (i - cut) as usize;
                let new = map[level].expect("a kept binder");
                Hx::Var(cut + new_outer - 1 - new)
            }
            Hx::Pi(a, b) => Hx::Pi(go(a, outer, map, new_outer, cut, memo), go(b, outer, map, new_outer, cut + 1, memo)),
            Hx::Lam(a, b) => Hx::Lam(go(a, outer, map, new_outer, cut, memo), go(b, outer, map, new_outer, cut + 1, memo)),
            Hx::App(f, a) => Hx::App(go(f, outer, map, new_outer, cut, memo), go(a, outer, map, new_outer, cut, memo)),
            _ => t.clone(),
        });
        memo.insert(key, out.clone());
        out
    }
    (*go(t, outer, map, new_outer, cut, &mut HashMap::new())).clone()
}
