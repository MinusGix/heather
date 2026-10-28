//! `Greedy::colouring` (native_alloc) over a source read back as numbers
//! (`Source::spelled`): the words' homes `write-elf` compiles with, spelled
//! as `Homes::spelled` spells them. `Greedy::assign` checks the colouring
//! and falls back to the slots; that check is the parts' (`elf`), so a
//! colouring it refuses gives way to the fork's homes there. The allocator is untrusted, as every
//! read is, since the compile checks the homes it is given
//! (`Source::allocation_ok`); it runs here because evaluating it on the
//! fork keeps every value it forces until the read returns, so its memory
//! grew with the tool past the rail (issues/native-allocator-cost.md).
//!
//! It is the Heather allocator step for step, its lists kept in the same
//! order, so it proposes the same homes; `native_alloc.hthr` stays the
//! definition, and `tests` hold the two to agreeing.

/// Registers in the home pool (`home_pool`).
const POOL: u64 = 6;
/// The rows the graph is padded to (`Greedy::colouring`'s `put(63, …)`).
const ROWS: usize = 64;
/// Closure passes (`closure_fuel`).
const CLOSURE_FUEL: usize = 4096;
/// What a loop's body weighs more than what holds it (`Greedy::standard`).
const LOOP_WEIGHT: u64 = 7;

#[derive(Clone)]
struct Node { output: u64, reads: Vec<u64> }

enum Stmt {
    Leaf(Vec<Node>),
    Invoke { reads: Vec<u64>, result: u64 },
    Then(Box<Stmt>, Box<Stmt>),
    Branch(u64, Box<Stmt>, Box<Stmt>),
    Repeat(Box<Stmt>, u64),
    Exit(u64),
    Arg { index: u64, len: u64 },
}

struct Reader<'a> { numbers: &'a [u64], at: usize }

impl Reader<'_> {
    fn next(&mut self) -> Option<u64> {
        let n = *self.numbers.get(self.at)?;
        self.at += 1;
        Some(n)
    }

    fn take(&mut self, count: usize) -> Option<Vec<u64>> { (0..count).map(|_| self.next()).collect() }

    fn skip_ports(&mut self) -> Option<()> {
        let count = self.next()? as usize;
        self.take(2 * count).map(|_| ())
    }

    fn node(&mut self) -> Option<Node> {
        let tag = self.next()?;
        let f = self.take(match tag { 0 | 1 | 13 => 3, 2..=12 | 14 => 4, _ => return None })?;
        Some(match tag {
            0 => Node { output: f[1], reads: vec![] },
            1 | 7 | 8 | 9 => Node { output: f[1], reads: vec![f[2]] },
            13 => Node { output: f[0], reads: vec![f[2]] },
            14 => Node { output: f[0], reads: vec![f[2], f[3]] },
            _ => Node { output: f[1], reads: vec![f[2], f[3]] },
        })
    }

    fn stmt(&mut self) -> Option<Stmt> {
        Some(match self.next()? {
            0 => {
                self.skip_ports()?;
                let count = self.next()? as usize;
                let nodes = (0..count).map(|_| self.node()).collect::<Option<Vec<_>>>()?;
                self.skip_ports()?;
                Stmt::Leaf(nodes)
            }
            1 => {
                let tag = self.next()?;
                let f = self.take(match tag { 0 => 4, 1 => 5, 2 => 3, 3 => 2, 4 => 4, 5 => 3, _ => return None })?;
                let (reads, result) = match tag {
                    0 => (vec![f[0], f[2]], f[3]),
                    1 => (vec![f[0], f[2], f[3]], f[4]),
                    2 => (vec![f[1]], f[2]),
                    3 => (vec![f[0]], f[1]),
                    4 => (vec![f[1]], f[3]),
                    _ => (vec![f[0]], f[2]),
                };
                Stmt::Invoke { reads, result }
            }
            2 => Stmt::Then(Box::new(self.stmt()?), Box::new(self.stmt()?)),
            3 => {
                let condition = self.next()?;
                Stmt::Branch(condition, Box::new(self.stmt()?), Box::new(self.stmt()?))
            }
            4 => {
                let again = self.next()?;
                let body = self.stmt()?;
                Stmt::Repeat(Box::new(body), again)
            }
            5 => Stmt::Exit(self.next()?),
            6 => {
                let f = self.take(3)?;
                Stmt::Arg { index: f[0], len: f[2] }
            }
            _ => return None,
        })
    }
}

/// The statement of a spelled source; `None` for one spelled `[0]` (not a
/// builder's), or one that does not read back.
fn main_of(numbers: &[u64]) -> Option<Stmt> {
    let mut r = Reader { numbers, at: 0 };
    if r.next()? == 0 { return None; }
    for _ in 0..r.next()? {
        r.next()?;
        let len = r.next()? as usize;
        r.take(len)?;
    }
    let main = r.stmt()?;
    (r.at == numbers.len()).then_some(main)
}

// Sets of words as lists of ids, in `List::union`'s and `List::minus`'s
// orders.

fn holds(ids: &[u64], id: u64) -> bool { ids.contains(&id) }

fn union(a: &[u64], b: &[u64]) -> Vec<u64> {
    let mut out = a.to_vec();
    out.extend(b.iter().filter(|id| !holds(a, **id)));
    out
}

fn minus(a: &[u64], b: &[u64]) -> Vec<u64> { a.iter().copied().filter(|id| !holds(b, *id)).collect() }

fn live_before(reads: &[u64], written: u64, out: &[u64]) -> Vec<u64> { union(reads, &minus(out, &[written])) }

fn nodes_live_in(nodes: &[Node], out: &[u64]) -> Vec<u64> {
    nodes.iter().rev().fold(out.to_vec(), |after, node| live_before(&node.reads, node.output, &after))
}

fn loop_after(again: u64, set: &[u64], out: &[u64]) -> Vec<u64> {
    let mut v = vec![again];
    v.extend(union(set, out));
    v
}

/// `List::put`: the `i`-th entry replaced, `pad` filling out to it.
fn put<T: Clone>(xs: &mut Vec<T>, i: usize, x: T, pad: T) {
    if xs.len() <= i { xs.resize(i + 1, pad); }
    xs[i] = x;
}

struct Homes { of: Vec<Option<u64>>, loops: Vec<Vec<u64>> }

impl Homes {
    fn loop_set(&self, again: u64) -> &[u64] { self.loops.get(again as usize).map_or(&[], |s| &s[..]) }

    fn home(&self, id: u64) -> Option<u64> { self.of.get(id as usize).copied().flatten() }
}

/// `Stmt::needs`: the set live before, and the loop sets grown.
fn needs(s: &Stmt, homes: &Homes, out: &[u64], sets: &mut Vec<Vec<u64>>) -> Vec<u64> {
    match s {
        Stmt::Leaf(nodes) => nodes_live_in(nodes, out),
        Stmt::Invoke { reads, result } => live_before(reads, *result, out),
        Stmt::Then(first, rest) => {
            let after = needs(rest, homes, out, sets);
            needs(first, homes, &after, sets)
        }
        Stmt::Branch(condition, yes, no) => {
            let n = needs(no, homes, out, sets);
            let y = needs(yes, homes, out, sets);
            let mut v = vec![*condition];
            v.extend(union(&y, &n));
            v
        }
        Stmt::Repeat(body, again) => {
            let b = needs(body, homes, &loop_after(*again, homes.loop_set(*again), out), sets);
            let had = sets.get(*again as usize).cloned().unwrap_or_else(|| homes.loop_set(*again).to_vec());
            put(sets, *again as usize, union(&had, &b), vec![]);
            homes.loop_set(*again).to_vec()
        }
        Stmt::Exit(status) => vec![*status],
        Stmt::Arg { index, len } => live_before(&[*index], *len, out),
    }
}

fn sets_within(a: &[Vec<u64>], b: &[Vec<u64>]) -> bool {
    a.iter().enumerate().all(|(i, set)| { let other = b.get(i).map_or(&[][..], |o| &o[..]); set.iter().all(|id| holds(other, *id)) })
}

/// `Homes::slots`: every word in its slot, the least closed loop sets
/// (`Source::loop_sets`). Where the growth stops is not checked here, as
/// `Source::closed_or_wide` checks it: sets the check refuses leave the
/// colouring refused too, and the fork's homes stand in (`elf`).
fn slots(main: &Stmt) -> Homes {
    let mut homes = Homes { of: vec![], loops: vec![] };
    for _ in 0..CLOSURE_FUEL {
        let mut sets = homes.loops.clone();
        needs(main, &homes, &[], &mut sets);
        if sets_within(&sets, &homes.loops) { break; }
        homes.loops = sets;
    }
    homes
}

/// The interference rows, by id: row `a` flags each word live after some
/// write of `a` (`List::written`).
fn written(of: &mut Vec<Vec<bool>>, id: u64, out: &[u64]) {
    let mut row = of.get(id as usize).cloned().unwrap_or_default();
    for o in out { put(&mut row, *o as usize, true, false); }
    put(of, id as usize, row, vec![]);
}

/// `Stmt::graph`: the set live before, the rows grown.
fn graph(s: &Stmt, homes: &Homes, out: &[u64], of: &mut Vec<Vec<bool>>) -> Vec<u64> {
    match s {
        Stmt::Leaf(nodes) => {
            for node in nodes { written(of, node.output, out); }
            nodes.iter().rev().fold(out.to_vec(), |after, node| {
                let live = live_before(&node.reads, node.output, &after);
                written(of, node.output, &after);
                live
            })
        }
        Stmt::Invoke { reads, result } => {
            written(of, *result, out);
            live_before(reads, *result, out)
        }
        Stmt::Then(first, rest) => {
            let after = graph(rest, homes, out, of);
            graph(first, homes, &after, of)
        }
        Stmt::Branch(condition, yes, no) => {
            let n = graph(no, homes, out, of);
            let y = graph(yes, homes, out, of);
            let mut v = vec![*condition];
            v.extend(union(&y, &n));
            v
        }
        Stmt::Repeat(body, again) => {
            graph(body, homes, &loop_after(*again, homes.loop_set(*again), out), of);
            homes.loop_set(*again).to_vec()
        }
        Stmt::Exit(status) => vec![*status],
        Stmt::Arg { index, len } => {
            written(of, *len, out);
            live_before(&[*index], *len, out)
        }
    }
}

fn bump(weights: &mut Vec<u64>, id: u64, by: u64) {
    let w = weights.get(id as usize).copied().unwrap_or(0);
    put(weights, id as usize, w + by, 0);
}

/// `Stmt::weights`: reads and writes counted, a loop's body `LOOP_WEIGHT` more than
/// what holds it.
fn weights(s: &Stmt, scale: u64, w: &mut Vec<u64>) {
    match s {
        Stmt::Leaf(nodes) => for node in nodes {
            bump(w, node.output, scale);
            for r in &node.reads { bump(w, *r, scale); }
        },
        Stmt::Invoke { reads, result } => {
            bump(w, *result, scale);
            for r in reads { bump(w, *r, scale); }
        }
        Stmt::Then(first, rest) => { weights(first, scale, w); weights(rest, scale, w); }
        Stmt::Branch(condition, yes, no) => { bump(w, *condition, scale); weights(yes, scale, w); weights(no, scale, w); }
        Stmt::Repeat(body, again) => { bump(w, *again, scale + LOOP_WEIGHT); weights(body, scale + LOOP_WEIGHT, w); }
        Stmt::Exit(status) => bump(w, *status, scale),
        Stmt::Arg { index, len } => { bump(w, *index, scale); bump(w, *len, scale); }
    }
}

/// `List::heaviest`: ids with a weight, heaviest first, an equal weight's
/// later id before (`insert_by`).
fn heaviest(w: &[u64]) -> Vec<u64> {
    let mut sorted: Vec<u64> = vec![];
    for (id, &weight) in w.iter().enumerate() {
        if weight == 0 { continue; }
        let at = sorted.iter().position(|&other| w[other as usize] <= weight).unwrap_or(sorted.len());
        sorted.insert(at, id as u64);
    }
    sorted
}

fn flag(of: &[Vec<bool>], row: usize, k: usize) -> bool { of.get(row).and_then(|r| r.get(k)).copied().unwrap_or(false) }

/// `List::colour`: each word in turn given the first register none of its
/// neighbours has, a word live at the start kept in its slot.
fn colour(order: &[u64], entry: &[u64], rows: &[Vec<bool>], homes: &mut Homes) {
    for &id in order {
        if holds(entry, id) { continue; }
        let used: Vec<u64> = (0..rows.len())
            .filter(|&at| flag(rows, id as usize, at) || flag(rows, at, id as usize))
            .filter_map(|at| homes.home(at as u64))
            .collect();
        let home = (0..POOL).find(|k| !used.contains(k));
        put(&mut homes.of, id as usize, home, None);
    }
}

/// `Greedy::standard().colouring`'s homes of the spelled source, spelled as
/// `Homes::spelled`; `None` when the source does not read back as a
/// builder's.
pub(super) fn homes_spelled(spelled: &[u64]) -> Option<Vec<u64>> {
    let main = main_of(spelled)?;
    let mut homes = slots(&main);
    let mut rows = vec![];
    let entry = graph(&main, &homes, &[], &mut rows);
    let last = rows.get(ROWS - 1).cloned().unwrap_or_default();
    put(&mut rows, ROWS - 1, last, vec![]);
    let mut w = vec![];
    weights(&main, 1, &mut w);
    colour(&heaviest(&w), &entry, &rows, &mut homes);
    let mut out = vec![homes.of.len() as u64];
    out.extend(homes.of.iter().map(|h| h.map_or(0, |k| k + 1)));
    for set in &homes.loops {
        out.push(set.len() as u64);
        out.extend(set);
    }
    Some(out)
}
