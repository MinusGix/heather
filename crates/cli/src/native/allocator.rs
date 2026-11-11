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
//! order, so it proposes the same homes, structured regions included
//! (`Homes::region_needs`, `region_graph`, `StructuredRegion::weighed`;
//! issues/native-region-spelling.md); `native_alloc.hthr` stays the
//! definition, and `tests` hold the two to agreeing.

/// Registers in the home pool (`home_pool`).
const POOL: u64 = 6;
/// What a loop's body weighs more than what holds it (`Greedy::standard`).
const LOOP_WEIGHT: u64 = 7;

#[derive(Clone)]
struct Node { output: u64, reads: Vec<u64> }

/// A structured region (`StructuredRegion`), as the allocator reads it:
/// a dataflow leaf is its nodes.
enum Region {
    Leaf(Vec<Node>),
    Sequence(Vec<Node>, Box<Region>),
    Compose(Box<Region>, Box<Region>),
    Conditional(u64, Box<Region>, Box<Region>),
    Call { arguments: Vec<u64>, result: u64 },
    Loop { inputs: Vec<u64>, bound: u64, parameters: Vec<u64>, count: u64, body: Box<Region>, exit: u64, next: Vec<u64>, outputs: Vec<u64>, exhausted: u64 },
}

enum Stmt {
    Leaf(Vec<Node>),
    Region(Region),
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

    fn ids(&mut self) -> Option<Vec<u64>> {
        let count = self.next()? as usize;
        self.take(count)
    }

    /// A leaf's nodes, its ports skipped (`Region::spelled_body`).
    fn body(&mut self) -> Option<Vec<Node>> {
        self.skip_ports()?;
        let count = self.next()? as usize;
        let nodes = (0..count).map(|_| self.node()).collect::<Option<Vec<_>>>()?;
        self.skip_ports()?;
        Some(nodes)
    }

    /// `StructuredRegion::spelled_tagged`.
    fn region(&mut self) -> Option<Region> {
        Some(match self.next()? {
            0 => Region::Leaf(self.body()?),
            1 => Region::Sequence(self.body()?, Box::new(self.region()?)),
            2 => Region::Compose(Box::new(self.region()?), Box::new(self.region()?)),
            3 => {
                self.skip_ports()?;
                let condition = self.next()?;
                self.skip_ports()?;
                self.skip_ports()?;
                Region::Conditional(condition, Box::new(self.region()?), Box::new(self.region()?))
            }
            4 => {
                self.next()?;
                let arguments = self.ids()?;
                Region::Call { arguments, result: self.next()? }
            }
            5 => {
                let inputs = self.ids()?;
                let bound = self.next()?;
                let parameters = self.ids()?;
                let count = self.next()?;
                let body = Box::new(self.region()?);
                let exit = self.next()?;
                let next = self.ids()?;
                let outputs = self.ids()?;
                Region::Loop { inputs, bound, parameters, count, body, exit, next, outputs, exhausted: self.next()? }
            }
            _ => return None,
        })
    }

    fn stmt(&mut self) -> Option<Stmt> {
        Some(match self.next()? {
            0 => Stmt::Leaf(self.body()?),
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
            7 => Stmt::Region(self.region()?),
            _ => return None,
        })
    }
}

/// The words and the statement of a spelled source; `None` for one spelled
/// `[0]` (not a builder's), or one that does not read back.
fn main_of(numbers: &[u64]) -> Option<(u64, Stmt)> {
    let mut r = Reader { numbers, at: 0 };
    // A source with procedures (`[2]`, or `[3]` with any) is allocated on
    // the fork: this mirror walks `main` only. The functions a source calls
    // (`[3]`) take no part: a call reads and writes the words it names.
    let tag = r.next()?;
    if tag != 1 && tag != 3 { return None; }
    let words = r.next()?;
    if tag == 3 { r.next()?; }
    for _ in 0..r.next()? {
        r.next()?;
        let len = r.next()? as usize;
        r.take(len)?;
    }
    if tag == 3 {
        for _ in 0..r.next()? {
            r.ids()?;
            r.region()?;
            // Its result, and how many buffers it is lent.
            r.next()?;
            r.next()?;
        }
        if r.next()? != 0 { return None; }
    }
    let main = r.stmt()?;
    (r.at == numbers.len()).then_some((words, main))
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

// A loop's code, as native_alloc spells it: `moves`, `loop_entry`,
// `loop_zero`, `loop_down`, `loop_stop`.
fn moves(to: &[u64], from: &[u64]) -> Vec<Node> { to.iter().zip(from).map(|(&t, &f)| Node { output: t, reads: vec![f] }).collect() }

fn loop_entry(bound: u64, count: u64, inputs: &[u64], parameters: &[u64]) -> Vec<Node> {
    let mut v = vec![Node { output: count, reads: vec![bound] }];
    v.extend(moves(parameters, inputs));
    v
}

fn loop_zero(count: u64, exhausted: u64) -> Vec<Node> {
    vec![Node { output: exhausted, reads: vec![] }, Node { output: exhausted, reads: vec![count, exhausted] }]
}

fn loop_down(count: u64, exhausted: u64) -> Vec<Node> {
    vec![Node { output: exhausted, reads: vec![] }, Node { output: count, reads: vec![count, exhausted] }]
}

fn loop_stop(exhausted: u64) -> Vec<Node> { vec![Node { output: exhausted, reads: vec![] }] }

fn with_head(head: u64, rest: Vec<u64>) -> Vec<u64> {
    let mut v = vec![head];
    v.extend(rest);
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

/// `Homes::region_needs`: the set live before, a loop's head set (its
/// count's) joined with what its head needs.
fn region_needs(r: &Region, homes: &Homes, out: &[u64], sets: &mut Vec<Vec<u64>>) -> Vec<u64> {
    match r {
        Region::Leaf(nodes) => nodes_live_in(nodes, out),
        Region::Sequence(prefix, rest) => {
            let after = region_needs(rest, homes, out, sets);
            nodes_live_in(prefix, &after)
        }
        Region::Compose(prefix, rest) => {
            let after = region_needs(rest, homes, out, sets);
            region_needs(prefix, homes, &after, sets)
        }
        Region::Conditional(condition, yes, no) => {
            let n = region_needs(no, homes, out, sets);
            let y = region_needs(yes, homes, out, sets);
            with_head(*condition, union(&y, &n))
        }
        Region::Call { arguments, result } => live_before(arguments, *result, out),
        Region::Loop { inputs, bound, parameters, count, body, exit, next, outputs, exhausted } => {
            let set = homes.loop_set(*count).to_vec();
            let done = nodes_live_in(&moves(outputs, parameters), out);
            let stop = nodes_live_in(&loop_stop(*exhausted), &done);
            let down = nodes_live_in(&loop_down(*count, *exhausted), &set);
            let b = region_needs(body, homes, &nodes_live_in(&moves(parameters, next), &with_head(*exit, union(&stop, &down))), sets);
            let head = nodes_live_in(&loop_zero(*count, *exhausted), &with_head(*exhausted, union(&b, &done)));
            let had = sets.get(*count as usize).cloned().unwrap_or_else(|| set.clone());
            put(sets, *count as usize, union(&had, &head), vec![]);
            nodes_live_in(&loop_entry(*bound, *count, inputs, parameters), &set)
        }
    }
}

/// `Stmt::needs`: the set live before, and the loop sets grown.
fn needs(s: &Stmt, homes: &Homes, out: &[u64], sets: &mut Vec<Vec<u64>>) -> Vec<u64> {
    match s {
        Stmt::Leaf(nodes) => nodes_live_in(nodes, out),
        Stmt::Region(r) => region_needs(r, homes, out, sets),
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
/// (`Source::loop_sets`), in at most `Source::closure_fuel` passes. Where
/// the growth stops is not checked here, as `Source::closed_or_wide` checks
/// it: sets the check refuses leave the colouring refused too, and the
/// fork's homes stand in (`elf`).
fn slots(words: u64, main: &Stmt) -> Homes {
    let mut homes = Homes { of: vec![], loops: vec![] };
    for _ in 0..words * words + 1 {
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

/// `leaf_graph`: a leaf's writes both ways, a node at a time and its
/// results last; the set live before it.
fn leaf_graph(nodes: &[Node], out: &[u64], of: &mut Vec<Vec<bool>>) -> Vec<u64> {
    for node in nodes { written(of, node.output, out); }
    nodes.iter().rev().fold(out.to_vec(), |after, node| {
        let live = live_before(&node.reads, node.output, &after);
        written(of, node.output, &after);
        live
    })
}

/// `Homes::region_graph`.
fn region_graph(r: &Region, homes: &Homes, out: &[u64], of: &mut Vec<Vec<bool>>) -> Vec<u64> {
    match r {
        Region::Leaf(nodes) => leaf_graph(nodes, out, of),
        Region::Sequence(prefix, rest) => {
            let after = region_graph(rest, homes, out, of);
            leaf_graph(prefix, &after, of)
        }
        Region::Compose(prefix, rest) => {
            let after = region_graph(rest, homes, out, of);
            region_graph(prefix, homes, &after, of)
        }
        Region::Conditional(condition, yes, no) => {
            let n = region_graph(no, homes, out, of);
            let y = region_graph(yes, homes, out, of);
            with_head(*condition, union(&y, &n))
        }
        Region::Call { arguments, result } => {
            written(of, *result, out);
            live_before(arguments, *result, out)
        }
        Region::Loop { inputs, bound, parameters, count, body, exit, next, outputs, exhausted } => {
            let set = homes.loop_set(*count).to_vec();
            let done = leaf_graph(&moves(outputs, parameters), out, of);
            let stop = leaf_graph(&loop_stop(*exhausted), &done, of);
            let down = leaf_graph(&loop_down(*count, *exhausted), &set, of);
            let moved = leaf_graph(&moves(parameters, next), &with_head(*exit, union(&stop, &down)), of);
            let b = region_graph(body, homes, &moved, of);
            leaf_graph(&loop_zero(*count, *exhausted), &with_head(*exhausted, union(&b, &done)), of);
            leaf_graph(&loop_entry(*bound, *count, inputs, parameters), &set, of)
        }
    }
}

/// `Stmt::graph`: the set live before, the rows grown.
fn graph(s: &Stmt, homes: &Homes, out: &[u64], of: &mut Vec<Vec<bool>>) -> Vec<u64> {
    match s {
        Stmt::Leaf(nodes) => leaf_graph(nodes, out, of),
        Stmt::Region(r) => region_graph(r, homes, out, of),
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

fn nodes_weights(nodes: &[Node], scale: u64, w: &mut Vec<u64>) {
    for node in nodes {
        bump(w, node.output, scale);
        for r in &node.reads { bump(w, *r, scale); }
    }
}

/// `StructuredRegion::weighed`: a loop's body and its count's ticking
/// `LOOP_WEIGHT` heavier.
fn region_weights(r: &Region, scale: u64, w: &mut Vec<u64>) {
    match r {
        Region::Leaf(nodes) => nodes_weights(nodes, scale, w),
        Region::Sequence(prefix, rest) => { nodes_weights(prefix, scale, w); region_weights(rest, scale, w); }
        Region::Compose(prefix, rest) => { region_weights(prefix, scale, w); region_weights(rest, scale, w); }
        Region::Conditional(condition, yes, no) => { bump(w, *condition, scale); region_weights(yes, scale, w); region_weights(no, scale, w); }
        Region::Call { arguments, result } => { bump(w, *result, scale); for a in arguments { bump(w, *a, scale); } }
        Region::Loop { inputs, bound, parameters, count, body, exit, next, outputs, exhausted } => {
            let inner = scale + LOOP_WEIGHT;
            nodes_weights(&loop_entry(*bound, *count, inputs, parameters), scale, w);
            region_weights(body, inner, w);
            bump(w, *exit, inner);
            let mut passes = loop_zero(*count, *exhausted);
            passes.extend(moves(parameters, next));
            passes.extend(loop_down(*count, *exhausted));
            nodes_weights(&passes, inner, w);
            let mut after = loop_stop(*exhausted);
            after.extend(moves(outputs, parameters));
            nodes_weights(&after, scale, w);
        }
    }
}

/// `Stmt::weights`: reads and writes counted, a loop's body `LOOP_WEIGHT` more than
/// what holds it.
fn weights(s: &Stmt, scale: u64, w: &mut Vec<u64>) {
    match s {
        Stmt::Leaf(nodes) => nodes_weights(nodes, scale, w),
        Stmt::Region(r) => region_weights(r, scale, w),
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
    let (words, main) = main_of(spelled)?;
    let mut homes = slots(words, &main);
    let mut rows = vec![];
    let entry = graph(&main, &homes, &[], &mut rows);
    // A row for every word the source declares (`Greedy::colouring`'s `put`).
    let top = words.saturating_sub(1) as usize;
    let last = rows.get(top).cloned().unwrap_or_default();
    put(&mut rows, top, last, vec![]);
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
