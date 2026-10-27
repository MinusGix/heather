//! `write-elf`'s program, read back and stated a part of the statement tree
//! at a time.
//!
//! A read keeps every value it forces until it returns, and one `refl` over
//! a whole program's `Stmt::emit` has one declaration's fuel, so a program a
//! few times cat's size outgrew both when it was read and stated whole
//! (issues/native-compile-capacity.md). Here the tree's shape is read first
//! (`Source::shape`, native_compile), which lowers nothing; then each part
//! small enough to evaluate whole is read on its own (`Stmt::emission_reading`,
//! at `Start`, which `emit` never looks into), and so are the items a
//! `Repeat` or `Branch` puts around its parts. In the certificate each whole
//! part is one `refl`, and every larger one is joined from its parts'
//! statements by `Stmt::emit_then_of`, `emit_repeat_of` or `emit_branch_of`
//! (native_compile_correct). A part is named by its parent's (`Stmt::left`,
//! `right`), so no statement spells a part of the tree it does not
//! evaluate, and the program's literal is cut wherever a part starts or
//! ends, so each statement's programs are definitions.
//!
//! The reads are untrusted, like everything a fork reads: a misreading makes
//! a statement the kernel refuses, never a wrong one it accepts. The items
//! around a `Repeat`'s or `Branch`'s parts are read from expressions that
//! spell what `Stmt::emit` puts there; if the two ever differ, the joining
//! lemma's statement is what the kernel refuses.

use std::collections::BTreeSet;

use super::verified;

/// A part with at most this many leaves is read and stated whole.
const LEAVES: usize = 8;
/// Items in each definition of the program's literal, at most.
const STRETCH: usize = 32;

/// A node of `Source::shape`'s tree.
struct Shape { kind: u64, names: u64, then: u64, children: Vec<Shape>, leaves: usize }

impl Shape {
    fn read(records: &mut std::slice::Iter<'_, [u64; 3]>) -> Result<Shape, String> {
        let &[kind, names, then] = records.next().ok_or_else(malformed)?;
        let arity = match kind { 0 => 0, 1 | 3 => 2, 2 => 1, _ => return Err(malformed()) };
        let children = (0..arity).map(|_| Shape::read(records)).collect::<Result<Vec<_>, _>>()?;
        let leaves = if arity == 0 { 1 } else { children.iter().map(|c| c.leaves).sum() };
        Ok(Shape { kind, names, then, children, leaves })
    }
}

fn malformed() -> String { "the statement tree's shape is malformed".into() }

fn out_of_order() -> String { "the program's parts did not read back in order".into() }

/// How a part is read and stated; the numbers are reads, in program order.
enum Part {
    Whole { id: usize, names: u64, read: usize },
    Then { id: usize, names: u64, first: Box<Part>, rest: Box<Part> },
    Repeat { id: usize, names: u64, open: usize, body: Box<Part>, close: usize },
    Branch { id: usize, names: u64, open: usize, yes: Box<Part>, middle: usize, no: Box<Part>, close: usize },
}

impl Part {
    fn id(&self) -> usize {
        match self { Part::Whole { id, .. } | Part::Then { id, .. } | Part::Repeat { id, .. } | Part::Branch { id, .. } => *id }
    }
}

/// The reads to make, on a fork that has elaborated `text`: each a nullary
/// `List<Nat>`, in program order, the first the entry `Source::compile`
/// emits the main statement after, the last the exit it puts after it. `whole[r]` says whether read `r` is a part's
/// (`Stmt::emission_reading`, the label name after it first) or the items
/// around parts (`Prog::reading`).
pub(super) struct Plan { pub text: String, pub reads: Vec<String>, pub whole: Vec<bool>, root: Part }

/// `shape` is `Source::shape`'s list (the preorder reversed, three numbers a
/// node); `source`, `entry` and `layout` spell the main statement, the
/// program it is emitted after, and the layout.
pub(super) fn plan(p: &str, source: &str, entry: &str, layout: &str, shape: &[u64]) -> Result<Plan, String> {
    if shape.len() % 3 != 0 { return Err(malformed()); }
    let records: Vec<[u64; 3]> = shape.rchunks(3).map(|r| [r[2], r[1], r[0]]).collect();
    let mut at = records.iter();
    let tree = Shape::read(&mut at)?;
    if at.next().is_some() || tree.names != 0 { return Err(malformed()); }
    let mut planner = Planner { p, layout, text: format!("fn {p}_s_0() → Stmt {{ {source} }}\n"), reads: Vec::new(), whole: Vec::new(), parts: 1 };
    planner.read("entry", false, format!("{entry}.reading()"));
    let root = planner.part(&tree, 0)?;
    planner.read("exit", false, "then(then(Start, Block([MovRI(Rdi, BitVec::ofNat(0)), MovRI(Rax, BitVec::ofNat(60))])), Syscall).reading()".into());
    Ok(Plan { text: planner.text, reads: planner.reads, whole: planner.whole, root })
}

struct Planner<'a> { p: &'a str, layout: &'a str, text: String, reads: Vec<String>, whole: Vec<bool>, parts: usize }

impl Planner<'_> {
    fn read(&mut self, what: &str, whole: bool, body: String) -> usize {
        let name = format!("{}_read_{}_{what}", self.p, self.reads.len());
        self.text.push_str(&format!("fn {name}() → List<Nat> {{ {body} }}\n"));
        self.reads.push(name);
        self.whole.push(whole);
        self.reads.len() - 1
    }

    fn child(&mut self, id: usize, side: &str) -> usize {
        let child = self.parts;
        self.parts += 1;
        self.text.push_str(&format!("fn {p}_s_{child}() → Stmt {{ {p}_s_{id}().{side}() }}\n", p = self.p));
        child
    }

    fn part(&mut self, shape: &Shape, id: usize) -> Result<Part, String> {
        let (p, layout, names) = (self.p, self.layout, shape.names);
        if shape.leaves <= LEAVES {
            let read = self.read("part", true, format!("{p}_s_{id}().emission_reading({layout}, {names})"));
            return Ok(Part::Whole { id, names, read });
        }
        let (s, ss) = (names + 1, names + 2);
        let word = format!("{p}_s_{id}().word()");
        Ok(match (shape.kind, &shape.children[..]) {
            (1, [first, rest]) if shape.then == names => {
                let (f, r) = (self.child(id, "left"), self.child(id, "right"));
                Part::Then { id, names, first: Box::new(self.part(first, f)?), rest: Box::new(self.part(rest, r)?) }
            }
            (2, [body]) if shape.then == ss => {
                let b = self.child(id, "left");
                let open = self.read("open", false, format!("Start.label({s}).reading()"));
                let body = Box::new(self.part(body, b)?);
                let close = self.read("close", false, format!("then(Start.tests({layout}, {word}, {ss}), Jmp({s})).label({ss}).reading()"));
                Part::Repeat { id, names, open, body, close }
            }
            (3, [yes, no]) if shape.then == ss => {
                let (y, n) = (self.child(id, "left"), self.child(id, "right"));
                let open = self.read("open", false, format!("Start.tests({layout}, {word}, {s}).reading()"));
                let yes = Box::new(self.part(yes, y)?);
                let middle = self.read("middle", false, format!("Start.else_label({s}, {ss}).reading()"));
                let no = Box::new(self.part(no, n)?);
                let close = self.read("close", false, format!("Start.join_label({ss}).reading()"));
                Part::Branch { id, names, open, yes, middle, no, close }
            }
            _ => return Err(malformed()),
        })
    }
}

/// One read: the label name after it (a whole part's only), its items as
/// literals and their lengths.
pub(super) struct Reading { names: Option<u64>, items: Vec<(u64, String)>, lens: Vec<u64> }

impl Reading {
    /// A read's numbers; `None` for a part that does not emit.
    pub(super) fn of(numbers: &[u64], whole: bool, word: &dyn Fn(u32, u64) -> String) -> Result<Option<Reading>, String> {
        let bad = || "a part of the program did not read back".to_string();
        let (names, rest) = match (whole, numbers) {
            (true, []) => return Ok(None),
            (true, [names, rest @ ..]) => (Some(*names), rest),
            (false, rest) => (None, rest),
        };
        let [count, rest @ ..] = rest else { return Err(bad()) };
        let count = usize::try_from(*count).ok().filter(|&c| c <= rest.len()).ok_or_else(bad)?;
        let items = verified::read_items_with(&rest[..count], word)?;
        let lens = rest[count..].to_vec();
        if lens.len() != items.len() { return Err(bad()); }
        Ok(Some(Reading { names, items, lens }))
    }
}

/// The program's literal, cut where each statement's programs start and
/// end, ending in `{p}_code()`; the statements, ending in `{p}_e_0`, the
/// main statement's emission from `entry` (`{p}_entry` states the entry's
/// literal); and the items and their lengths.
pub(super) struct Stated { pub code: String, pub theorems: String, pub items: Vec<(u64, String)>, pub lens: Vec<u64> }

/// `readings` are `plan`'s reads, read.
pub(super) fn state(p: &str, entry: &str, layout: &str, plan: Plan, readings: Vec<Reading>) -> Result<Stated, String> {
    if readings.len() != plan.reads.len() { return Err(out_of_order()); }
    let mut starts = Vec::with_capacity(readings.len());
    let (mut items, mut lens) = (Vec::new(), Vec::new());
    for reading in &readings {
        starts.push(items.len());
        items.extend(reading.items.iter().cloned());
        lens.extend(reading.lens.iter().copied());
    }
    let (entered, main) = (starts[1], *starts.last().unwrap());
    let parts: String = plan.text.lines().filter(|line| line.starts_with(&format!("fn {p}_s_"))).map(|line| format!("{line}\n")).collect();
    let mut writer = Writer { p, layout, readings: &readings, starts: &starts, cuts: BTreeSet::from([0, entered, main, items.len()]), theorems: parts };
    writer.theorems.push_str(&format!("theorem {p}_entry(): {entry} = {} {{ refl }}\n", writer.program(entered)));
    let (start, end, _) = writer.part(&plan.root)?;
    if start != entered || end != main { return Err(out_of_order()); }
    for k in (0..items.len()).step_by(STRETCH) { writer.cuts.insert(k); }
    let mut code = String::new();
    let mut earlier = 0;
    for &cut in writer.cuts.iter().skip(1) {
        let mut at = writer.program(earlier);
        for (name, item) in &items[earlier..cut] { at = format!("At({at},\n    {name}, {item})"); }
        code.push_str(&format!("fn {p}_at_{cut}() → Prog {{\n    {at}\n}}\n"));
        earlier = cut;
    }
    code.push_str(&format!("fn {p}_code() → Prog {{ {p}_at_{}() }}\n", items.len()));
    Ok(Stated { code, theorems: writer.theorems, items, lens })
}

struct Writer<'a> {
    p: &'a str,
    layout: &'a str,
    readings: &'a [Reading],
    /// Where each read's items start in the program.
    starts: &'a [usize],
    /// The item counts the literal is cut at.
    cuts: BTreeSet<usize>,
    theorems: String,
}

impl Writer<'_> {
    /// The program of the first `k` items.
    fn program(&self, k: usize) -> String {
        if k == 0 { "Start".into() } else { format!("{}_at_{k}()", self.p) }
    }

    /// Where read `r`'s items end.
    fn end(&self, r: usize) -> usize { self.starts[r] + self.readings[r].items.len() }

    /// States `part` as `{p}_e_{id}`: its emission from where its items
    /// start to where they end. Returns the two, and the label name after it.
    fn part(&mut self, part: &Part) -> Result<(usize, usize, u64), String> {
        let (p, layout) = (self.p, self.layout);
        let (id, names, start, end, after, proof) = match part {
            Part::Whole { id, names, read } => {
                let after = self.readings[*read].names.ok_or_else(out_of_order)?;
                (*id, *names, self.starts[*read], self.end(*read), after, "refl".to_string())
            }
            Part::Then { id, names, first, rest } => {
                let (start, middle, between) = self.part(first)?;
                let (rest_start, end, after) = self.part(rest)?;
                if rest_start != middle { return Err(out_of_order()); }
                let proof = format!("trans(Stmt::emit_then_of({p}_s_{id}(), trivial, {}, {layout}, {names}, Compiled({}, {between}), {p}_e_{}()), {p}_e_{}())",
                    self.program(start), self.program(middle), first.id(), rest.id());
                (*id, *names, start, end, after, proof)
            }
            Part::Repeat { id, names, open, body, close } => {
                let (body_start, body_end, after) = self.part(body)?;
                if self.end(*open) != body_start || self.starts[*close] != body_end { return Err(out_of_order()); }
                let start = self.starts[*open];
                let proof = format!("Stmt::emit_repeat_of({p}_s_{id}(), trivial, trivial, {}, {layout}, {names}, Compiled({}, {after}), {p}_e_{}())",
                    self.program(start), self.program(body_end), body.id());
                (*id, *names, start, self.end(*close), after, proof)
            }
            Part::Branch { id, names, open, yes, middle, no, close } => {
                let (yes_start, yes_end, between) = self.part(yes)?;
                let (no_start, no_end, after) = self.part(no)?;
                if self.end(*open) != yes_start || self.starts[*middle] != yes_end || self.end(*middle) != no_start || self.starts[*close] != no_end {
                    return Err(out_of_order());
                }
                let start = self.starts[*open];
                let proof = format!("Stmt::emit_branch_of({p}_s_{id}(), trivial, trivial, {}, {layout}, {names}, Compiled({}, {between}), Compiled({}, {after}), {p}_e_{}(), {p}_e_{}())",
                    self.program(start), self.program(yes_end), self.program(no_end), yes.id(), no.id());
                (*id, *names, start, self.end(*close), after, proof)
            }
        };
        self.cuts.insert(start);
        self.cuts.insert(end);
        let (from, to) = (self.program(start), self.program(end));
        self.theorems.push_str(&format!("theorem {p}_e_{id}(): {p}_s_{id}().emit({from}, {layout}, {names}) = Some(Compiled({to}, {after})) {{ {proof} }}\n"));
        Ok((start, end, after))
    }
}
