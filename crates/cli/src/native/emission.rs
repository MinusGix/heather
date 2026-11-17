//! `write-elf`'s program, read back and stated a part of the statement tree
//! at a time.
//!
//! A read keeps every value it forces until it returns, and one `refl` over
//! a whole program's `Stmt::emit` has one declaration's fuel, so a program a
//! few times cat's size outgrew both when it was read and stated whole
//! (issues/native-compile-capacity.md). Here the tree's shape is read first
//! (`Source::shape`, native_compile), which lowers nothing; then each part
//! small enough to evaluate whole is read on its own (`Stmt::emission_reading`,
//! at `Start`, which `emits` never looks into), and so are the items a
//! `Repeat` or `Branch` puts around its parts. In the certificate each whole
//! part is one `refl`, and every larger one is joined from its parts'
//! statements by `Stmt::emits_then_of`, `emits_repeat_of` or `emits_branch_of`
//! (native_compile_correct); a sequence whose rest reads no known word, in
//! the main statement, by `Stmt::emits_then_checked`, which takes the set
//! live between its parts from the allocation's check (`{p}_ck_`) where
//! `emits_then_of` has the kernel work it out from the rest
//! (issues/native-emission-join-liveness.md). A part is named by its parent's (`Stmt::left`,
//! `right`), and so are what is live after it (`{p}_o_`: the parent's, but
//! `right().live_with(…)` for a `Then`'s first part and `loop_out` for a
//! loop's body) and what is known as it starts (`{p}_kn_`: nothing, but for
//! a `Then`'s parts `left().first_known` and `left().carried`), as
//! `Stmt::emits` passes them, so no statement spells a part of the
//! tree it does not evaluate, and the program's literal is cut wherever a
//! part starts or ends, so each statement's programs are definitions.
//!
//! The reads are made in the plan's order, in sessions that share what
//! they force (`function_ir_source::read_sharing`): a part's statement, set
//! and known words are a step from its parent's, and a read on its own
//! worked each of them out from the root again, which was most of what the
//! reads of a tool cost. A whole part's read gives its bytes with its
//! items, from the one evaluation of its emission (`Prog::unlinked`: a
//! jump's displacement is the only thing in an item's bytes that reads the
//! labels, and `labels::link` writes each once the program is laid out);
//! only the items around parts have their bytes read apart (`byte_reads`).
//!
//! The compile's check of the homes (`Stmt::checked`) is stated over the
//! same parts (`Checks`), from the sets it finds before each statement,
//! read on the fork (`Source::checked_spelled`); and the entry's stores of
//! the buffers' initial bytes a definition of them at a time (`Inits`).
//!
//! The reads are untrusted, like everything a fork reads: a misreading makes
//! a statement the kernel refuses, never a wrong one it accepts. The items
//! around a `Repeat`'s or `Branch`'s parts are read from expressions that
//! spell what `Stmt::emits` puts there; if the two ever differ, the joining
//! lemma's statement is what the kernel refuses.

use std::collections::BTreeSet;

use super::{lowered, verified};

/// A part with at most this many leaves is read and stated whole.
const LEAVES: usize = 8;
/// Items in each definition of the program's literal, at most.
const STRETCH: usize = 32;

/// A node of `Source::shape`'s tree.
/// `index` is its place in the preorder.
struct Shape { kind: u64, names: u64, then: u64, children: Vec<Shape>, leaves: usize, index: usize }

impl Shape {
    fn read(records: &mut std::slice::Iter<'_, [u64; 3]>, count: &mut usize) -> Result<Shape, String> {
        let &[kind, names, then] = records.next().ok_or_else(malformed)?;
        let index = *count;
        *count += 1;
        let arity = match kind { 0 => 0, 1 | 3 => 2, 2 => 1, _ => return Err(malformed()) };
        let children = (0..arity).map(|_| Shape::read(records, count)).collect::<Result<Vec<_>, _>>()?;
        let leaves = if arity == 0 { 1 } else { children.iter().map(|c| c.leaves).sum() };
        Ok(Shape { kind, names, then, children, leaves, index })
    }

    /// The label name after it: a leaf's own count, else its last part's.
    fn end(&self) -> u64 { self.children.last().map_or(self.then, Shape::end) }
}

fn malformed() -> String { "the statement tree's shape is malformed".into() }

fn out_of_order() -> String { "the program's parts did not read back in order".into() }

/// `Source::shape` counts a leaf's label names without emitting it; a count
/// the emission does not take is a join the kernel would refuse.
fn miscounted() -> String { "the statement tree's shape counts label names its emission does not take".into() }

/// How a part is read and stated; the numbers are reads, in program order.
enum Part {
    Whole { id: usize, names: u64, read: usize, index: usize },
    Then { id: usize, names: u64, first: Box<Part>, rest: Box<Part>, index: usize },
    Repeat { id: usize, names: u64, open: usize, body: Box<Part>, close: usize, index: usize },
    Branch { id: usize, names: u64, open: usize, yes: Box<Part>, middle: usize, no: Box<Part>, close: usize, index: usize },
}

impl Part {
    fn id(&self) -> usize {
        match self { Part::Whole { id, .. } | Part::Then { id, .. } | Part::Repeat { id, .. } | Part::Branch { id, .. } => *id }
    }

    /// Where it is in the statement tree's preorder.
    fn index(&self) -> usize {
        match self { Part::Whole { index, .. } | Part::Then { index, .. } | Part::Repeat { index, .. } | Part::Branch { index, .. } => *index }
    }

    /// The label name the shape says it starts at.
    fn names(&self) -> u64 {
        match self { Part::Whole { names, .. } | Part::Then { names, .. } | Part::Repeat { names, .. } | Part::Branch { names, .. } => *names }
    }
}

/// The reads to make, on a fork that has elaborated `text`: each a nullary
/// `List<Nat>`, in program order, the first the entry `Source::compile`
/// emits the main statement after, the last the exit it puts after it. `whole[r]` says whether read `r` is a part's
/// (`Stmt::emission_reading`, the label name after it first and its bytes
/// last) or the items around parts (`Prog::reading`). `programs[r]` spells
/// read `r`'s program, at `Start`, for reading the bytes of a read that did
/// not give them (`byte_reads`).
/// `joins` are the sequences stated as joins, by the id of each one's rest,
/// which `{p}_plain` reads in the same order: 1 where the rest does not start
/// with a call or an exit (`Stmt::reads_known`), and the join can take the set
/// live before it from the allocation's check (`Stmt::emits_then_checked`).
pub(super) struct Plan { pub text: String, pub reads: Vec<String>, pub whole: Vec<bool>, programs: Vec<String>, root: Part, exit: usize, calls: Option<Calls>, joins: Vec<usize> }

/// A source with procedures or functions: each procedure's way in, its
/// body's parts and its way out, read after the exit, then the shared exit,
/// then the functions' code (`Prog::links`) when it has any.
struct Calls { src: String, homes: String, bodies: Vec<Body>, deep: usize, functions: Option<usize>, count: usize }

/// What `plan` takes of such a source: its spelling and its homes', its
/// procedures' shapes (`List::procedures_shapes`), and whether it has
/// functions.
pub(super) struct CallsOf<'a> { pub src: &'a str, pub homes: &'a str, pub shapes: &'a [u64], pub functions: usize }

/// Procedure `index`'s reads: its way in (`Procedure::entry_code`), its
/// body, and its way out (`Procedure::exit_code`).
struct Body { entry: usize, root: Part, exit: usize }

/// A statement tree from `Source::shape`'s list, which must start at label
/// name `first` when it is given.
fn tree_of(shape: &[u64], first: Option<u64>) -> Result<Shape, String> {
    if shape.len() % 3 != 0 { return Err(malformed()); }
    let records: Vec<[u64; 3]> = shape.rchunks(3).map(|r| [r[2], r[1], r[0]]).collect();
    let mut at = records.iter();
    let tree = Shape::read(&mut at, &mut 0)?;
    if at.next().is_some() || first.is_some_and(|first| tree.names != first) { return Err(malformed()); }
    Ok(tree)
}

/// The name of procedure `index`'s layout (`elf::frames_literal` defines it).
pub(super) fn body_layout(p: &str, index: usize) -> String { format!("{p}_layout_b{index}()") }

/// Procedure `index` of the source `src` spells.
fn procedure(src: &str, index: usize) -> String { format!("{src}().procedures.procedure_or({index})") }

/// `shape` is `Source::shape`'s list (the preorder reversed, three numbers a
/// node); `source`, `entry` and `layout` spell the main statement, the
/// program it is emitted after, and the layout. With `calls` (for a source
/// with procedures or functions) the main statement
/// starts at label name `first` (`Source::main_names`), and each
/// procedure is read after the exit, its body a part at a time from its
/// shape (`List::procedures_shapes`), then the shared exit, then the
/// functions' code, whose inner labels start after the last name the
/// shapes count.
pub(super) fn plan(p: &str, source: &str, entry: &str, layout: &str, shape: &[u64], first: u64, calls: Option<CallsOf<'_>>) -> Result<Plan, String> {
    let tree = tree_of(shape, Some(first))?;
    let text = format!("fn {p}_s_0() → Stmt {{ {source} }}\nfn {p}_o_0() → List<Nat> {{ [] }}\nfn {p}_kn_0() → List<Fact> {{ [] }}\n");
    let mut planner = Planner { p, layout: layout.to_string(), text, reads: Vec::new(), whole: Vec::new(), programs: Vec::new(), parts: 1, joins: Vec::new() };
    planner.read("entry", entry.to_string());
    let root = planner.part(&tree, 0)?;
    let exit = planner.read("exit", "then(then(Start, Block([MovRI(Rdi, BitVec::ofNat(0)), MovRI(Rax, BitVec::ofNat(60))])), Syscall)".into());
    let calls = match calls {
        None => None,
        Some(CallsOf { src, homes, mut shapes, functions }) => {
            let mut bodies = Vec::new();
            let mut after = tree.end();
            while let [count, rest @ ..] = shapes {
                let count = usize::try_from(*count).ok().filter(|&c| c <= rest.len()).ok_or_else(malformed)?;
                let tree = tree_of(&rest[..count], None)?;
                after = tree.end();
                shapes = &rest[count..];
                let (index, proc_) = (bodies.len(), procedure(src, bodies.len()));
                let id = planner.parts;
                planner.parts += 1;
                planner.text.push_str(&format!("fn {p}_s_{id}() → Stmt {{ {proc_}.body }}\nfn {p}_o_{id}() → List<Nat> {{ {proc_}.results }}\nfn {p}_kn_{id}() → List<Fact> {{ [] }}\n"));
                // Each procedure under its own layout (`Layout::body`), a
                // literal the certificate holds to the computed one.
                let body_layout = body_layout(p, index);
                planner.layout = body_layout.clone();
                let entry = planner.read("in", format!("{proc_}.entry_code(Start, {body_layout}, {index})"));
                let root = planner.part(&tree, id)?;
                let exit = planner.read("out", format!("{proc_}.exit_code(Start, {body_layout})"));
                planner.layout = layout.to_string();
                bodies.push(Body { entry, root, exit });
            }
            let deep = planner.read("deep", format!("Start.deep_exit({layout})"));
            let count = functions;
            let functions = (count > 0).then(|| planner.read("functions", format!("Start.links({src}().functions, {homes}.places, {homes}.room_table({src}().functions), {after}).unwrap_or(Start)")));
            Some(Calls { src: src.to_string(), homes: homes.to_string(), bodies, deep, functions, count })
        }
    };
    let plain: Vec<String> = planner.joins.iter().map(|rest| format!("match {p}_s_{rest}().reads_known() {{ True => 0, False => 1 }}")).collect();
    planner.text.push_str(&format!("fn {p}_plain() → List<Nat> {{ [{}] }}\n", plain.join(", ")));
    Ok(Plan { text: planner.text, reads: planner.reads, whole: planner.whole, programs: planner.programs, root, exit, calls, joins: planner.joins })
}

struct Planner<'a> { p: &'a str, layout: String, text: String, reads: Vec<String>, whole: Vec<bool>, programs: Vec<String>, parts: usize, joins: Vec<usize> }

impl Planner<'_> {
    /// The items around parts, of the program `program` spells.
    fn read(&mut self, what: &str, program: String) -> usize {
        self.push(what, false, format!("{program}.reading()"), program)
    }

    fn push(&mut self, what: &str, whole: bool, body: String, program: String) -> usize {
        let name = format!("{}_read_{}_{what}", self.p, self.reads.len());
        self.text.push_str(&format!("fn {name}() → List<Nat> {{ {body} }}\n"));
        self.reads.push(name);
        self.whole.push(whole);
        self.programs.push(program);
        self.reads.len() - 1
    }

    /// A part of part `id`, what is live after it (`out`) and what is known
    /// as it starts (`known`), spelled from its parent's.
    fn child(&mut self, id: usize, side: &str, out: String, known: String) -> usize {
        let child = self.parts;
        self.parts += 1;
        self.text.push_str(&format!("fn {p}_s_{child}() → Stmt {{ {p}_s_{id}().{side}() }}\nfn {p}_o_{child}() → List<Nat> {{ {out} }}\n\
            fn {p}_kn_{child}() → List<Fact> {{ {known} }}\n", p = self.p));
        child
    }

    fn part(&mut self, shape: &Shape, id: usize) -> Result<Part, String> {
        let (p, layout, names) = (self.p, self.layout.clone(), shape.names);
        if shape.leaves <= LEAVES {
            let read = self.push("part", true, format!("{p}_s_{id}().emission_reading({layout}, {p}_o_{id}(), {p}_kn_{id}(), {names})"),
                format!("{p}_s_{id}().emits(Start, {layout}, {p}_o_{id}(), {p}_kn_{id}(), {names}).map(λ (c: Compiled) => c.prog).unwrap_or(Start)"));
            return Ok(Part::Whole { id, names, read, index: shape.index });
        }
        let (s, ss) = (names + 1, names + 2);
        let word = format!("{p}_s_{id}().word()");
        Ok(match (shape.kind, &shape.children[..]) {
            (1, [first, rest]) if shape.then == names => {
                let carried = format!("{p}_s_{id}().left().carried({p}_s_{id}().right(), {layout}.homes, {p}_o_{id}())");
                let f = self.child(id, "left", format!("{p}_s_{id}().right().live_with({layout}.homes, {carried}, {p}_o_{id}())"),
                    format!("{p}_s_{id}().left().first_known({p}_kn_{id}())"));
                let r = self.child(id, "right", format!("{p}_o_{id}()"), carried);
                self.joins.push(r);
                Part::Then { id, names, first: Box::new(self.part(first, f)?), rest: Box::new(self.part(rest, r)?), index: shape.index }
            }
            (2, [body]) if shape.then == ss => {
                let b = self.child(id, "left", format!("{p}_s_{id}().loop_out({layout}.homes, {p}_o_{id}())"), "[]".into());
                let open = self.read("open", format!("Start.label({s})"));
                let body = Box::new(self.part(body, b)?);
                let close = self.read("close", format!("then(Start.tests({layout}, {word}, {ss}), Jmp({s})).label({ss})"));
                Part::Repeat { id, names, open, body, close, index: shape.index }
            }
            (3, [yes, no]) if shape.then == ss => {
                let y = self.child(id, "left", format!("{p}_o_{id}()"), "[]".into());
                let n = self.child(id, "right", format!("{p}_o_{id}()"), "[]".into());
                let open = self.read("open", format!("Start.tests({layout}, {word}, {s})"));
                let yes = Box::new(self.part(yes, y)?);
                let middle = self.read("middle", format!("Start.else_label({s}, {ss})"));
                let no = Box::new(self.part(no, n)?);
                let close = self.read("close", format!("Start.join_label({ss})"));
                Part::Branch { id, names, open, yes, middle, no, close, index: shape.index }
            }
            _ => return Err(malformed()),
        })
    }
}

/// One read: the label name after it (a whole part's only), its items as
/// literals, their lengths, and a whole part's bytes, unlinked
/// (`Prog::unlinked`, native_compile: read in the evaluation that emitted
/// the part, so its bytes do not emit it a second time).
pub(super) struct Reading { names: Option<u64>, items: Vec<(u64, String)>, lens: Vec<u64>, bytes: Option<Vec<u8>> }

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
        let rest = &rest[count..];
        if !whole {
            if rest.len() != items.len() { return Err(bad()); }
            return Ok(Some(Reading { names, items, lens: rest.to_vec(), bytes: None }));
        }
        if rest.len() < items.len() { return Err(bad()); }
        let (lens, bytes) = rest.split_at(items.len());
        let bytes = bytes.iter().map(|&b| u8::try_from(b)).collect::<Result<Vec<u8>, _>>().map_err(|_| bad())?;
        if bytes.len() as u64 != lens.iter().sum::<u64>() { return Err(bad()); }
        Ok(Some(Reading { names, items, lens: lens.to_vec(), bytes: Some(bytes) }))
    }
}

/// The statements, ending in `{p}_e_0`, the main statement's emission from
/// `entry` (`{p}_entry` states the entry's literal); the items and their
/// lengths; the item counts the program's literal must be cut at, where
/// each statement's programs start and end (`code` writes the literal); and
/// each read's program and items, for reading the bytes (`byte_reads`).
pub(super) struct Stated { pub theorems: String, pub items: Vec<(u64, String)>, pub lens: Vec<u64>, pub cuts: BTreeSet<usize>, pub spans: Vec<Span>, pub calls: Option<CallsStated> }

/// With procedures or functions: `{p}_e_0`'s program and the label name
/// after it, `{p}_procedures` (the procedures' code after its exit, each by
/// `Procedure::code_of` from its parts, joined by
/// `List::procedures_code_of`) and the label name after them, and
/// `{p}_deep` (the shared exit after them, and then the functions linked,
/// is `{p}_code()`; the functions' lowering is that one statement, so a
/// function is as large as one declaration's fuel lowers).
pub(super) struct CallsStated { pub main: String, pub names: u64, pub procedures: String, pub after: u64 }

/// A read's program, spelled at `Start`, where its items are in the
/// whole (the first, and how many), and its bytes if the read gave them.
pub(super) struct Span { program: String, pub start: usize, pub count: usize, pub bytes: Option<Vec<u8>> }

/// A literal source's buffers (`lowered::Buffers`), for stating the entry's
/// stores of their initial bytes a definition of them at a time: the
/// source, the homes, and each buffer's capacity and initial length.
pub(super) struct Inits<'a> { pub src: &'a str, pub homes: &'a str, pub frames: &'a str, pub shapes: &'a [(u64, usize)] }

/// `readings` are `plan`'s reads, read. With `inits`, the entry is stated
/// from its parts (`Inits::state`); without, by one `refl` over the set
/// live as `main` starts, which the allocation's check found
/// (`Source::entry_at`): the entry zeroes those words of `main`'s frame.
pub(super) fn state(p: &str, entry: &str, layout: &str, plan: Plan, plain: &[u64], readings: Vec<Reading>, inits: Option<Inits<'_>>, checks: Checks<'_>) -> Result<Stated, String> {
    if readings.len() != plan.reads.len() { return Err(out_of_order()); }
    let mut starts = Vec::with_capacity(readings.len());
    let (mut items, mut lens) = (Vec::new(), Vec::new());
    for reading in &readings {
        starts.push(items.len());
        items.extend(reading.items.iter().cloned());
        lens.extend(reading.lens.iter().copied());
    }
    let (entered, main) = (starts[1], starts[plan.exit]);
    let parts: String = plan.text.lines().filter(|line| line.starts_with(&format!("fn {p}_s_")) || line.starts_with(&format!("fn {p}_o_")) || line.starts_with(&format!("fn {p}_kn_")))
        .map(|line| format!("{line}\n")).collect();
    if plain.len() != plan.joins.len() { return Err(out_of_order()); }
    let plain: BTreeSet<usize> = plan.joins.iter().zip(plain).filter(|&(_, &flag)| flag == 1).map(|(&rest, _)| rest).collect();
    let mut writer = Writer { p, layout: layout.to_string(), readings: &readings, starts: &starts, cuts: BTreeSet::from([0, entered, main, items.len()]), theorems: parts, plain: &plain, checked: false };
    // The allocation's check first: the entry reads the set it found
    // before `main` (`{p}_ck_0`), and the main statement's joins cite its
    // verdicts.
    let (checked, live) = checks.state(p, &plan.root)?;
    writer.theorems.push_str(&checked);
    writer.checked = true;
    match inits {
        Some(inits) => inits.state(&mut writer, entered, &live)?,
        None => writer.theorems.push_str(&format!("theorem {p}_entry(): {entry} = {} {{\n    \
            {src}().entry_at({LOW}, {homes}, {frames}, {live}, {}, {p}_ck_0(), refl)\n}}\n", writer.program(entered), writer.program(entered),
            src = checks.src, homes = checks.homes, frames = checks.frames, LOW = super::elf::LOW)),
    }
    let (start, end, names) = writer.part(&plan.root)?;
    writer.checked = false;
    if start != entered || end != main { return Err(out_of_order()); }
    let calls = match &plan.calls {
        None => None,
        Some(Calls { src, homes, bodies, deep, functions, count }) => {
            let from = writer.end(plan.exit);
            let (mut at, mut label) = (from, names);
            // Each procedure's start, end, label names before and after.
            let mut spans = Vec::with_capacity(bodies.len());
            for (i, body) in bodies.iter().enumerate() {
                if writer.starts[body.entry] != at { return Err(out_of_order()); }
                let entered = writer.end(body.entry);
                let lb = body_layout(p, i);
                writer.layout = lb.clone();
                let (start, end, after) = writer.part(&body.root)?;
                writer.layout = layout.to_string();
                if start != entered || writer.starts[body.exit] != end { return Err(out_of_order()); }
                if body.root.names() != label { return Err(miscounted()); }
                let out = writer.end(body.exit);
                writer.cuts.extend([at, entered, out]);
                let proc_ = procedure(src, i);
                let (a, e, b, o) = (writer.program(at), writer.program(entered), writer.program(end), writer.program(out));
                writer.theorems.push_str(&format!("theorem {p}_pf_{i}(): {proc_}.fits({lb}) = True {{ refl }}\n\
                    theorem {p}_pe_{i}(): {proc_}.entry_code({a}, {lb}, {i}) = {e} {{ refl }}\n\
                    theorem {p}_px_{i}(): {proc_}.exit_code({b}, {lb}) = {o} {{ refl }}\n\
                    theorem {p}_pkb_{i}(): {proc_}.code({a}, {lb}, {i}, {label}) = Some(Compiled({o}, {after})) {{\n    \
                    Procedure::code_of({proc_}, {a}, {e}, {b}, {o}, {lb}, {i}, {label}, {after}, {p}_pf_{i}(), {p}_pe_{i}(), {p}_e_{}(), {p}_px_{i}())\n}}\n\
                    theorem {p}_pk_{i}(): {proc_}.code({a}, {layout}.body({i}), {i}, {label}) = Some(Compiled({o}, {after})) {{\n    \
                    j({p}_layout_b{i}_is(), λ l _ => {proc_}.code({a}, l, {i}, {label}) = Some(Compiled({o}, {after})), {p}_pkb_{i}())\n}}\n",
                    body.root.id()));
                spans.push((at, out, label, after));
                (at, label) = (out, after);
            }
            let exited = writer.end(*deep);
            let linked = match functions { None => exited, Some(read) => { if writer.starts[*read] != exited { return Err(out_of_order()); } writer.end(*read) } };
            if writer.starts[*deep] != at || linked != items.len() { return Err(out_of_order()); }
            writer.cuts.extend([at, exited]);
            let (end, last) = (writer.program(at), label);
            let n = bodies.len();
            writer.theorems.push_str(&format!("theorem {p}_pl_{n}(): {src}().procedures.drop({n}).procedures_code({end}, {layout}, {n}, {last}) = Some(Compiled({end}, {last})) {{ refl }}\n"));
            for (i, &(start, out, before, after)) in spans.iter().enumerate().rev() {
                let (a, o) = (writer.program(start), writer.program(out));
                writer.theorems.push_str(&format!("theorem {p}_pl_{i}(): {src}().procedures.drop({i}).procedures_code({a}, {layout}, {i}, {before}) = Some(Compiled({end}, {last})) {{\n    \
                    List::procedures_code_of({src}().procedures.drop({i}), {}, {src}().procedures.drop({}), refl, {a}, {layout}, {i}, {before}, Compiled({o}, {after}), Compiled({end}, {last}), {p}_pk_{i}(), {p}_pl_{}())\n}}\n",
                    procedure(src, i), i + 1, i + 1));
            }
            writer.theorems.push_str(&format!("theorem {p}_procedures(): {src}().procedures.procedures_code({}, {layout}, 0, {names}) = Some(Compiled({end}, {last})) {{ {p}_pl_0() }}\n\
", writer.program(from)));
            writer.theorems.push_str(&deep_text(p, src, homes, layout, &end, last, *count));
            Some(CallsStated { main: writer.program(main), names, procedures: end, after: last })
        }
    };
    for k in (0..items.len()).step_by(STRETCH) { writer.cuts.insert(k); }
    let spans = plan.programs.into_iter().zip(&readings).zip(&starts)
        .map(|((program, reading), &start)| Span { program, start, count: reading.items.len(), bytes: reading.bytes.clone() }).collect();
    Ok(Stated { theorems: writer.theorems, items, lens, cuts: writer.cuts, spans, calls })
}

/// Items a byte read takes at most.
const READ: usize = 256;

/// The live-out set a line of the plan's definitions defines, by name.
fn live_name(p: &str, line: &str) -> Option<String> {
    let (id, _) = line.strip_prefix("fn ")?.strip_prefix(p)?.strip_prefix("_o_")?.split_once("()")?;
    id.bytes().all(|b| b.is_ascii_digit()).then(|| format!("{p}_o_{id}"))
}

/// What the fork reads of a plan: a part's live-out set (`{p}_o_{id}`, by
/// name), or one of the plan's reads (by its place in `Plan::reads`).
pub(super) enum Read { Live(String), Items(usize) }

/// The plan's reads and the live-out sets it defines, in the order the plan
/// defines them: a parent's set before its parts', and a part's set before
/// its emission. Read in one session (`function_ir_source::read_sharing`),
/// each is then a step from what was read before it.
pub(super) fn reads(p: &str, plan: &Plan) -> Vec<Read> {
    let read = format!("fn {p}_read_");
    let mut next = 0;
    plan.text.lines().filter_map(|line| match live_name(p, line) {
        Some(name) => Some(Read::Live(name)),
        None if line.starts_with(&read) => { next += 1; Some(Read::Items(next - 1)) }
        None => None,
    }).collect()
}

/// The plan's definitions with every part's live-out set replaced by the
/// literal read for it (`sets`, in the plan's order), so no declaration
/// works a set out from the root again.
pub(super) fn live_literals(p: &str, text: &str, sets: &[Vec<u64>]) -> Result<String, String> {
    let mut sets = sets.iter();
    let mut out = String::with_capacity(text.len());
    for line in text.split_inclusive('\n') {
        match live_name(p, line) {
            Some(name) => {
                let set: Vec<String> = sets.next().ok_or_else(out_of_order)?.iter().map(u64::to_string).collect();
                out.push_str(&format!("fn {name}() → List<Nat> {{ [{}] }}\n", set.join(", ")));
            }
            None => out.push_str(line),
        }
    }
    Ok(out)
}

/// The bytes of the reads that did not give theirs (the items around
/// parts), a read at a time on the fork that read the parts: each read's
/// program at `Start` again, encoded unlinked as a part's are
/// (`asm_code_ending_onto` at no labels, x86_64_asm_table: consed from the
/// back, so a long read is linear). So the fork needs no literal of the
/// program, and the literal is elaborated once, in the certificate
/// (issues/write-elf-build-constants.md); bytes read wrong are a piece the
/// kernel refuses. The reads, named in program order, with the items they
/// read.
pub(super) fn byte_reads(p: &str, spans: &[Span]) -> (String, Vec<(String, std::ops::Range<usize>)>) {
    let mut text = String::new();
    let mut reads = Vec::new();
    for (r, span) in spans.iter().enumerate().filter(|(_, span)| span.count > 0 && span.bytes.is_none()) {
        // A long read (the entry's stores of a buffer's initial bytes) a
        // window at a time, from the back, so a read's memory is its
        // window's.
        let end = span.start + span.count;
        for (w, from) in (span.start..end).step_by(READ).enumerate() {
            let to = (from + READ).min(end);
            let name = format!("{p}_bytes_{r}_{w}");
            text.push_str(&format!("fn {name}() → List<Nat> {{ asm_code_ending_onto(no_fills(), λ (_: Nat) => 0, asm_back({}, {}), {}, 0, Nil).map(λ (b: BitVec(8)) => b.toNat()) }}\n",
                span.program, end - to, to - from));
            reads.push((name, from..to));
        }
    }
    (text, reads)
}

/// The program's literal: a definition `{p}_at_{k}` of its first `k` items
/// at each cut, each on the one before, and `{p}_code()`, the whole.
pub(super) fn code(p: &str, items: &[(u64, String)], cuts: &BTreeSet<usize>) -> String {
    let program = |k: usize| if k == 0 { "Start".to_string() } else { format!("{p}_at_{k}()") };
    let mut code = String::new();
    let mut earlier = 0;
    for &cut in cuts.iter().filter(|&&cut| cut > 0) {
        let mut at = program(earlier);
        for (name, item) in &items[earlier..cut] { at = format!("At({at},\n    {name}, {item})"); }
        code.push_str(&format!("fn {p}_at_{cut}() → Prog {{\n    {at}\n}}\n"));
        earlier = cut;
    }
    code.push_str(&format!("fn {p}_code() → Prog {{ {} }}\n", program(items.len())));
    code
}

/// The allocation's check, stated over the same parts as the emission
/// (`Stmt::checked_then_of`, `checked_branch_of`, `checked_repeat_of`,
/// native_compile_correct): the source, the homes, and
/// `Source::checked_spelled`'s read, each statement's `out` and the set
/// `Stmt::checked` finds before it, in preorder.
pub(super) struct Checks<'a> { pub src: &'a str, pub homes: &'a str, pub frames: &'a str, pub sets: &'a [u64] }

impl Checks<'_> {
    /// `{p}_ck_{id}` for each part, and `{p}_allocation_is`, that the
    /// compile's check of the homes passes; and the set live before the
    /// root, spelled.
    fn state(&self, p: &str, root: &Part) -> Result<(String, String), String> {
        let bad = || "the allocation's sets did not read back".to_string();
        // A set at `at`, after its length, and where the next starts.
        let set = |at: usize| -> Result<(String, usize), String> {
            let len = *self.sets.get(at).ok_or_else(bad)? as usize;
            let ids = self.sets.get(at + 1..at + 1 + len).ok_or_else(bad)?;
            Ok((format!("[{}]", ids.iter().map(u64::to_string).collect::<Vec<_>>().join(", ")), at + 1 + len))
        };
        let mut sets = Vec::new();
        let mut at = 0;
        while at < self.sets.len() {
            let (out, next) = set(at)?;
            let (live, next) = set(next)?;
            sets.push((out, live));
            at = next;
        }
        let mut text = String::new();
        self.part(p, root, &sets, &mut text)?;
        let (src, homes) = (self.src, self.homes);
        let live = sets.first().ok_or_else(bad)?.1.clone();
        text.push_str(&format!("theorem {p}_allocation_is(): {src}().allocation_ok({homes}) = True {{\n    \
            {src}().allocation_of({homes}, {live}, refl, {p}_ck_0(), refl)\n}}\n"));
        Ok((text, live))
    }

    fn part(&self, p: &str, part: &Part, sets: &[(String, String)], text: &mut String) -> Result<(), String> {
        let homes = self.homes;
        let (out, live) = sets.get(part.index()).ok_or("the allocation's sets are fewer than the statements")?;
        let set = |part: &Part| sets.get(part.index()).map(|(_, live)| live.as_str()).ok_or("the allocation's sets are fewer than the statements");
        let proof = match part {
            Part::Whole { .. } => "refl".to_string(),
            Part::Then { id, first, rest, .. } => {
                self.part(p, first, sets, text)?;
                self.part(p, rest, sets, text)?;
                format!("Stmt::checked_then_of({p}_s_{id}(), trivial, {homes}, {out}, {}, {live}, {p}_ck_{}(), {p}_ck_{}())", set(rest)?, rest.id(), first.id())
            }
            Part::Branch { id, yes, no, .. } => {
                self.part(p, yes, sets, text)?;
                self.part(p, no, sets, text)?;
                format!("Stmt::checked_branch_of({p}_s_{id}(), trivial, {homes}, {out}, {}, {}, {p}_ck_{}(), {p}_ck_{}())", set(yes)?, set(no)?, yes.id(), no.id())
            }
            Part::Repeat { id, body, .. } => {
                self.part(p, body, sets, text)?;
                format!("Stmt::checked_repeat_of({p}_s_{id}(), trivial, {homes}, {out}, {}, {p}_ck_{}(), refl)", set(body)?, body.id())
            }
        };
        text.push_str(&format!("theorem {p}_ck_{}(): {p}_s_{}().checked({homes}, {out}) = Some({live}) {{ {proof} }}\n", part.id(), part.id()));
        Ok(())
    }
}

impl Inits<'_> {
    /// The entry, `Source::entry`: RSP saved and `main`'s frame opened,
    /// the words of it in `live` (the set live as `main` starts) zeroed
    /// (`{p}_entry_saved`), then each buffer's initial bytes stored
    /// (`{p}_in_{j}`), a definition of them at a time (`{p}_ib_{j}_{k}_is`,
    /// joined by `Prog::bytes_init_append_of` as `{p}_it_{j}_{k}_is`). The
    /// literal is cut where each starts and ends.
    fn state(&self, writer: &mut Writer<'_>, entered: usize, live: &str) -> Result<(), String> {
        let (p, layout) = (writer.p, writer.layout.clone());
        let chunk = lowered::CHUNK as u64;
        // Two items store each initial byte while there is room, and the
        // entry's items before them save RSP and the depth
        // (`Prog::saves_rsp`, four), open the frame (`Prog::frames_main`,
        // one) and zero each live word of it (two a word).
        const SAVED: usize = 4;
        let stores: usize = self.shapes.iter().map(|&(capacity, len)| 2 * (len as u64).min(capacity) as usize).sum();
        let framed = entered.checked_sub(stores).filter(|&framed| framed > SAVED && (framed - SAVED) % 2 == 1)
            .ok_or_else(|| format!("the entry's initial bytes are {stores} items, and the entry read {entered}"))?;
        let mut at = framed;
        let mut text = format!("theorem {p}_entry_saved(): Start.saves_rsp({layout}, {}().depth).frames_main({layout}, {live}) = {} {{ refl }}\n", self.src, writer.program(at));
        let mut starts = Vec::with_capacity(self.shapes.len());
        for (j, &(capacity, len)) in self.shapes.iter().enumerate() {
            starts.push(at);
            let chunks = len.div_ceil(lowered::CHUNK);
            // Where definition `k` of the bytes starts, and the room left there.
            let offset = |k: usize| (k as u64 * chunk).min(len as u64);
            let room = |k: usize| capacity.saturating_sub(offset(k));
            let mut bounds = vec![at];
            for k in 0..chunks {
                at += 2 * (offset(k + 1) - offset(k)).min(room(k)) as usize;
                bounds.push(at);
                writer.cuts.insert(at);
                text.push_str(&format!("theorem {p}_ib_{j}_{k}_is(): {}.bytes_init({layout}, {p}_ib_{j}_{k}(), {}, {j}, {}) = {} {{ refl }}\n",
                    writer.program(bounds[k]), room(k), offset(k), writer.program(at)));
            }
            let end = writer.program(at);
            text.push_str(&format!("theorem {p}_it_{j}_{chunks}_is(): {end}.bytes_init({layout}, {p}_it_{j}_{chunks}(), {}, {j}, {}) = {end} {{ refl }}\n",
                room(chunks), offset(chunks)));
            for k in (0..chunks).rev() {
                let (from, to) = (writer.program(bounds[k]), writer.program(bounds[k + 1]));
                text.push_str(&format!("theorem {p}_it_{j}_{k}_is(): {from}.bytes_init({layout}, {p}_it_{j}_{k}(), {room}, {j}, {offset}) = {end} {{\n    \
                    Prog::bytes_init_append_of({layout}, {j}, {p}_ib_{j}_{k}(), {p}_it_{j}_{next}(), {room}, {offset}, {from}, {to}, {end}, {p}_ib_{j}_{k}_is(), {p}_it_{j}_{next}_is())\n}}\n",
                    room = room(k), offset = offset(k), next = k + 1));
            }
        }
        if at != entered {
            return Err(format!("the entry's initial bytes are {} items, and the entry read {entered}", at));
        }
        let end = writer.program(at);
        let count = self.shapes.len();
        text.push_str(&format!("theorem {p}_in_{count}_is(): {end}.inits({layout}, {p}_bl_{count}(), {count}) = {end} {{ refl }}\n"));
        for (j, &(capacity, _)) in self.shapes.iter().enumerate().rev() {
            let from = writer.program(starts[j]);
            let to = writer.program(starts.get(j + 1).copied().unwrap_or(at));
            text.push_str(&format!("theorem {p}_in_{j}_is(): {from}.inits({layout}, {p}_bl_{j}(), {j}) = {end} {{\n    \
                Prog::inits_of({layout}, Buffer({capacity}, {p}_it_{j}_0()), {p}_bl_{}(), {j}, {from}, {to}, {end}, {p}_it_{j}_0_is(), {p}_in_{}_is())\n}}\n",
                j + 1, j + 1));
        }
        let start = writer.program(framed);
        text.push_str(&format!("theorem {p}_entry(): {src}().entry({LOW}, {homes}, {frames}) = {end} {{\n    \
            {src}().entry_of({LOW}, {homes}, {frames}, {live}, {start}, {end}, {p}_ck_0(), {p}_entry_saved(), {p}_in_0_is())\n}}\n", src = self.src, homes = self.homes, frames = self.frames, LOW = super::elf::LOW));
        writer.cuts.insert(framed);
        writer.theorems.push_str(&text);
        Ok(())
    }
}

struct Writer<'a> {
    p: &'a str,
    /// The layout of the statement being written: `main`'s, or a
    /// procedure's own.
    layout: String,
    readings: &'a [Reading],
    /// Where each read's items start in the program.
    starts: &'a [usize],
    /// The item counts the literal is cut at.
    cuts: BTreeSet<usize>,
    theorems: String,
    /// The rests (by id) that do not start with a call or an exit.
    plain: &'a BTreeSet<usize>,
    /// Whether the statement being written has the allocation's check
    /// stated over its parts (`{p}_ck_{id}`): the main statement's.
    checked: bool,
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
        let (p, layout) = (self.p, self.layout.clone());
        let (id, names, start, end, after, proof) = match part {
            Part::Whole { id, names, read, .. } => {
                let after = self.readings[*read].names.ok_or_else(out_of_order)?;
                (*id, *names, self.starts[*read], self.end(*read), after, "refl".to_string())
            }
            Part::Then { id, names, first, rest, .. } => {
                let (start, middle, between) = self.part(first)?;
                let (rest_start, end, after) = self.part(rest)?;
                if rest_start != middle { return Err(out_of_order()); }
                if rest.names() != between { return Err(miscounted()); }
                // The set live between the two: from the check's verdict on
                // the rest where that is stated and the rest reads nothing
                // known, otherwise worked out by the kernel from the rest.
                let proof = if self.checked && self.plain.contains(&rest.id()) {
                    format!("trans(Stmt::emits_then_checked({p}_s_{id}(), trivial, {}, {layout}, {p}_o_{id}(), {p}_kn_{id}(), {names}, Compiled({}, {between}), {p}_o_{}(), refl, {p}_ck_{}(), {p}_e_{}()), {p}_e_{}())",
                        self.program(start), self.program(middle), first.id(), rest.id(), first.id(), rest.id())
                } else {
                    format!("trans(Stmt::emits_then_of({p}_s_{id}(), trivial, {}, {layout}, {p}_o_{id}(), {p}_kn_{id}(), {names}, Compiled({}, {between}), {p}_e_{}()), {p}_e_{}())",
                        self.program(start), self.program(middle), first.id(), rest.id())
                };
                (*id, *names, start, end, after, proof)
            }
            Part::Repeat { id, names, open, body, close, .. } => {
                let (body_start, body_end, after) = self.part(body)?;
                if self.end(*open) != body_start || self.starts[*close] != body_end { return Err(out_of_order()); }
                let start = self.starts[*open];
                let proof = format!("Stmt::emits_repeat_of({p}_s_{id}(), trivial, {}, {layout}, trivial, {p}_o_{id}(), {p}_kn_{id}(), {names}, Compiled({}, {after}), {p}_e_{}())",
                    self.program(start), self.program(body_end), body.id());
                (*id, *names, start, self.end(*close), after, proof)
            }
            Part::Branch { id, names, open, yes, middle, no, close, .. } => {
                let (yes_start, yes_end, between) = self.part(yes)?;
                let (no_start, no_end, after) = self.part(no)?;
                if no.names() != between { return Err(miscounted()); }
                if self.end(*open) != yes_start || self.starts[*middle] != yes_end || self.end(*middle) != no_start || self.starts[*close] != no_end {
                    return Err(out_of_order());
                }
                let start = self.starts[*open];
                let proof = format!("Stmt::emits_branch_of({p}_s_{id}(), trivial, {}, {layout}, trivial, {p}_o_{id}(), {p}_kn_{id}(), {names}, Compiled({}, {between}), Compiled({}, {after}), {p}_e_{}(), {p}_e_{}())",
                    self.program(start), self.program(yes_end), self.program(no_end), yes.id(), no.id());
                (*id, *names, start, self.end(*close), after, proof)
            }
        };
        self.cuts.insert(start);
        self.cuts.insert(end);
        let (from, to) = (self.program(start), self.program(end));
        self.theorems.push_str(&format!("theorem {p}_e_{id}(): {p}_s_{id}().emits({from}, {layout}, {p}_o_{id}(), {p}_kn_{id}(), {names}) = Some(Compiled({to}, {after})) {{ {proof} }}\n"));
        Ok((start, end, after))
    }
}

/// `{p}_deep`: the shared exit, then the functions linked, is the code.
/// `Prog::links` checks the functions linkable and emits them; each check
/// is its own declaration (`Prog::links_of`), and evaluability a function at
/// a time (`verified::evaluable_text_over`), so the kernel's
/// per-declaration fuel pays for the largest function and not for all of
/// them at once.
fn deep_text(p: &str, src: &str, homes: &str, layout: &str, end: &str, last: u64, count: usize) -> String {
    let functions = format!("{src}().functions");
    let exit = format!("{end}.deep_exit({layout})");
    if count == 0 {
        return format!("theorem {p}_deep(): {exit}.links({functions}, {homes}.places, {homes}.room_table({functions}), {last}) = Some({p}_code()) {{ refl }}\n");
    }
    let evaluable = super::verified::evaluable_text_over(p, &functions, count, &format!("{functions}.map(λ (f: Function) => f.parameters.len())"));
    format!("{evaluable}
theorem {p}_placeless(): program_placeless({functions}).IsTrue() {{ trivial }}
theorem {p}_rowed(): program_rowed({functions}).IsTrue() {{ trivial }}
theorem {p}_linked(): emit_functions_after_lent({exit}, {functions}, {homes}.places, {last}, program_counts({functions}), table_room({homes}.room_table({functions}))).map(λ out => out.prog) = Some({p}_code()) {{ refl }}
theorem {p}_deep(): {exit}.links({functions}, {homes}.places, {homes}.room_table({functions}), {last}) = Some({p}_code()) {{
    {exit}.links_of({functions}, {homes}.places, {homes}.room_table({functions}), {last}, {p}_code(), {p}_evaluable(), {p}_placeless(), {p}_rowed(), {p}_linked())
}}
")
}
