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
//! (native_compile_correct). A part is named by its parent's (`Stmt::left`,
//! `right`), and so are what is live after it (`{p}_o_`: the parent's, but
//! `right().live_with(…)` for a `Then`'s first part and `loop_out` for a
//! loop's body) and what is known as it starts (`{p}_kn_`: nothing, but for
//! a `Then`'s parts `left().first_known` and `left().carried`), as
//! `Stmt::emits` passes them, so no statement spells a part of the
//! tree it does not evaluate, and the program's literal is cut wherever a
//! part starts or ends, so each statement's programs are definitions.
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
/// (`Stmt::emission_reading`, the label name after it first) or the items
/// around parts (`Prog::reading`). `programs[r]` spells read `r`'s program,
/// at `Start`, for reading its bytes once the labels are known (`bytes`).
pub(super) struct Plan { pub text: String, pub reads: Vec<String>, pub whole: Vec<bool>, programs: Vec<String>, root: Part, exit: usize, calls: Option<Calls> }

/// A source with procedures: each procedure's way in, its body's parts and
/// its way out, read after the exit, then the shared exit.
struct Calls { src: String, bodies: Vec<Body>, deep: usize }

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

/// Procedure `index` of the source `src` spells.
fn procedure(src: &str, index: usize) -> String { format!("{src}().procedures.procedure_or({index})") }

/// `shape` is `Source::shape`'s list (the preorder reversed, three numbers a
/// node); `source`, `entry` and `layout` spell the main statement, the
/// program it is emitted after, and the layout. With `procedures` (the
/// source's spelling, for a source with procedures) the main statement
/// starts at label name `first` (`Source::main_names`), and each
/// procedure is read after the exit, its body a part at a time from its
/// shape (`List::procedures_shapes`), then the shared exit.
pub(super) fn plan(p: &str, source: &str, entry: &str, layout: &str, shape: &[u64], first: u64, procedures: Option<(&str, &[u64])>) -> Result<Plan, String> {
    let tree = tree_of(shape, Some(first))?;
    let text = format!("fn {p}_s_0() → Stmt {{ {source} }}\nfn {p}_o_0() → List<Nat> {{ [] }}\nfn {p}_kn_0() → List<Fact> {{ [] }}\n");
    let mut planner = Planner { p, layout, text, reads: Vec::new(), whole: Vec::new(), programs: Vec::new(), parts: 1 };
    planner.read("entry", entry.to_string());
    let root = planner.part(&tree, 0)?;
    let exit = planner.read("exit", "then(then(Start, Block([MovRI(Rdi, BitVec::ofNat(0)), MovRI(Rax, BitVec::ofNat(60))])), Syscall)".into());
    let calls = match procedures {
        None => None,
        Some((src, mut shapes)) => {
            let mut bodies = Vec::new();
            while let [count, rest @ ..] = shapes {
                let count = usize::try_from(*count).ok().filter(|&c| c <= rest.len()).ok_or_else(malformed)?;
                let tree = tree_of(&rest[..count], None)?;
                shapes = &rest[count..];
                let (index, proc_) = (bodies.len(), procedure(src, bodies.len()));
                let id = planner.parts;
                planner.parts += 1;
                planner.text.push_str(&format!("fn {p}_s_{id}() → Stmt {{ {proc_}.body }}\nfn {p}_o_{id}() → List<Nat> {{ {proc_}.results }}\nfn {p}_kn_{id}() → List<Fact> {{ [] }}\n"));
                let entry = planner.read("in", format!("{proc_}.entry_code(Start, {layout}, {index})"));
                let root = planner.part(&tree, id)?;
                let exit = planner.read("out", format!("{proc_}.exit_code(Start, {layout})"));
                bodies.push(Body { entry, root, exit });
            }
            let deep = planner.read("deep", format!("Start.deep_exit({layout})"));
            Some(Calls { src: src.to_string(), bodies, deep })
        }
    };
    Ok(Plan { text: planner.text, reads: planner.reads, whole: planner.whole, programs: planner.programs, root, exit, calls })
}

struct Planner<'a> { p: &'a str, layout: &'a str, text: String, reads: Vec<String>, whole: Vec<bool>, programs: Vec<String>, parts: usize }

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
        let (p, layout, names) = (self.p, self.layout, shape.names);
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

/// The statements, ending in `{p}_e_0`, the main statement's emission from
/// `entry` (`{p}_entry` states the entry's literal); the items and their
/// lengths; the item counts the program's literal must be cut at, where
/// each statement's programs start and end (`code` writes the literal); and
/// each read's program and items, for reading the bytes (`byte_reads`).
pub(super) struct Stated { pub theorems: String, pub items: Vec<(u64, String)>, pub lens: Vec<u64>, pub cuts: BTreeSet<usize>, pub spans: Vec<Span>, pub calls: Option<CallsStated> }

/// With procedures: `{p}_e_0`'s program and the label name after it,
/// `{p}_procedures` (the procedures' code after its exit, each by
/// `Procedure::code_of` from its parts, joined by
/// `List::procedures_code_of`) and the label name after them, and
/// `{p}_deep` (the shared exit after them is `{p}_code()`).
pub(super) struct CallsStated { pub main: String, pub names: u64, pub procedures: String, pub after: u64 }

/// A read's program, spelled at `Start`, and where its items are in the
/// whole: the first, and how many.
pub(super) struct Span { program: String, pub start: usize, pub count: usize }

/// A literal source's buffers (`lowered::Buffers`), for stating the entry's
/// stores of their initial bytes a definition of them at a time: the
/// source, the homes, and each buffer's capacity and initial length.
pub(super) struct Inits<'a> { pub src: &'a str, pub homes: &'a str, pub shapes: &'a [(u64, usize)] }

/// `readings` are `plan`'s reads, read. With `inits`, the entry is stated
/// from its parts (`Inits::state`); without, by one `refl`.
pub(super) fn state(p: &str, entry: &str, layout: &str, plan: Plan, readings: Vec<Reading>, inits: Option<Inits<'_>>, checks: Option<Checks<'_>>) -> Result<Stated, String> {
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
    let mut writer = Writer { p, layout, readings: &readings, starts: &starts, cuts: BTreeSet::from([0, entered, main, items.len()]), theorems: parts };
    match inits {
        Some(inits) => inits.state(&mut writer, entered)?,
        None => writer.theorems.push_str(&format!("theorem {p}_entry(): {entry} = {} {{ refl }}\n", writer.program(entered))),
    }
    let (start, end, names) = writer.part(&plan.root)?;
    if start != entered || end != main { return Err(out_of_order()); }
    let calls = match &plan.calls {
        None => None,
        Some(Calls { src, bodies, deep }) => {
            let from = writer.end(plan.exit);
            let (mut at, mut label) = (from, names);
            // Each procedure's start, end, label names before and after.
            let mut spans = Vec::with_capacity(bodies.len());
            for (i, body) in bodies.iter().enumerate() {
                if writer.starts[body.entry] != at { return Err(out_of_order()); }
                let entered = writer.end(body.entry);
                let (start, end, after) = writer.part(&body.root)?;
                if start != entered || writer.starts[body.exit] != end { return Err(out_of_order()); }
                if body.root.names() != label { return Err(miscounted()); }
                let out = writer.end(body.exit);
                writer.cuts.extend([at, entered, out]);
                let proc_ = procedure(src, i);
                let (a, e, b, o) = (writer.program(at), writer.program(entered), writer.program(end), writer.program(out));
                writer.theorems.push_str(&format!("theorem {p}_pf_{i}(): {proc_}.fits({layout}) = True {{ refl }}\n\
                    theorem {p}_pe_{i}(): {proc_}.entry_code({a}, {layout}, {i}) = {e} {{ refl }}\n\
                    theorem {p}_px_{i}(): {proc_}.exit_code({b}, {layout}) = {o} {{ refl }}\n\
                    theorem {p}_pk_{i}(): {proc_}.code({a}, {layout}, {i}, {label}) = Some(Compiled({o}, {after})) {{\n    \
                    Procedure::code_of({proc_}, {a}, {e}, {b}, {o}, {layout}, {i}, {label}, {after}, {p}_pf_{i}(), {p}_pe_{i}(), {p}_e_{}(), {p}_px_{i}())\n}}\n",
                    body.root.id()));
                spans.push((at, out, label, after));
                (at, label) = (out, after);
            }
            if writer.starts[*deep] != at || writer.end(*deep) != items.len() { return Err(out_of_order()); }
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
                theorem {p}_deep(): {end}.deep_exit({layout}) = {p}_code() {{ refl }}\n", writer.program(from)));
            Some(CallsStated { main: writer.program(main), names, procedures: end, after: last })
        }
    };
    if let Some(checks) = checks { writer.theorems.push_str(&checks.state(p, &plan.root)?); }
    for k in (0..items.len()).step_by(STRETCH) { writer.cuts.insert(k); }
    let spans = plan.programs.into_iter().zip(&readings).zip(&starts)
        .map(|((program, reading), &start)| Span { program, start, count: reading.items.len() }).collect();
    Ok(Stated { theorems: writer.theorems, items, lens, cuts: writer.cuts, spans, calls })
}

/// Items a byte read takes at most.
const READ: usize = 256;

/// The plan's definitions with every part's live-out set (`{p}_o_{id}`)
/// replaced by the literal `read` gives for it, so no declaration works a
/// set out from the root again.
pub(super) fn live_literals(p: &str, text: &str, mut read: impl FnMut(&str) -> Result<Vec<u64>, String>) -> Result<String, String> {
    let prefix = format!("fn {p}_o_");
    let mut out = String::with_capacity(text.len());
    for line in text.split_inclusive('\n') {
        match line.strip_prefix(&prefix).and_then(|rest| rest.split_once("()")) {
            Some((id, _)) if id.bytes().all(|b| b.is_ascii_digit()) => {
                let name = format!("{p}_o_{id}");
                let set: Vec<String> = read(&name)?.iter().map(u64::to_string).collect();
                out.push_str(&format!("fn {name}() → List<Nat> {{ [{}] }}\n", set.join(", ")));
            }
            _ => out.push_str(line),
        }
    }
    Ok(out)
}

/// The bytes a read at a time, on the fork that read the parts, once the
/// labels are known: each read's program at `Start` again, encoded with its
/// offsets carried down from where its items end in the whole
/// (`asm_code_ending_onto`, x86_64_asm_table: consed from the back, so a
/// long read is linear) and its jumps by the table
/// `{p}_table()` the text must also define (`labels::table`). So the fork
/// needs no literal of the program, and the literal is elaborated once, in
/// the certificate (issues/write-elf-build-constants.md); bytes read wrong
/// are a piece the kernel refuses. The reads, named in program order, with
/// the spans they read.
pub(super) fn byte_reads(p: &str, spans: &[Span], offsets: &[u64]) -> (String, Vec<(String, std::ops::Range<usize>)>) {
    let mut text = String::new();
    let mut reads = Vec::new();
    for (r, span) in spans.iter().enumerate().filter(|(_, span)| span.count > 0) {
        // A long read (the entry's stores of a buffer's initial bytes) a
        // window at a time, from the back: the fork's value cache keeps
        // all of one read, so a read's memory is its window's.
        let end = span.start + span.count;
        for (w, from) in (span.start..end).step_by(READ).enumerate() {
            let to = (from + READ).min(end);
            let name = format!("{p}_bytes_{r}_{w}");
            text.push_str(&format!("fn {name}() → List<Nat> {{ asm_code_ending_onto(no_fills(), {p}_table().labels(), asm_back({}, {}), {}, {}, Nil).map(λ (b: BitVec(8)) => b.toNat()) }}\n",
                span.program, end - to, to - from, offsets[to]));
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
pub(super) struct Checks<'a> { pub src: &'a str, pub homes: &'a str, pub sets: &'a [u64] }

impl Checks<'_> {
    /// `{p}_ck_{id}` for each part, and `{p}_allocation_is`, that the
    /// compile's check of the homes passes.
    fn state(&self, p: &str, root: &Part) -> Result<String, String> {
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
        text.push_str(&format!("theorem {p}_allocation_is(): {src}().allocation_ok({homes}) = True {{\n    \
            {src}().allocation_of({homes}, {}, refl, {p}_ck_0(), refl)\n}}\n", sets.first().ok_or_else(bad)?.1));
        Ok(text)
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
    /// The entry, `Source::entry`: RSP saved (`{p}_entry_saved`), then
    /// each buffer's initial bytes stored (`{p}_in_{j}`), a definition of
    /// them at a time (`{p}_ib_{j}_{k}_is`, joined by
    /// `Prog::bytes_init_append_of` as `{p}_it_{j}_{k}_is`). The literal is
    /// cut where each starts and ends.
    fn state(&self, writer: &mut Writer<'_>, entered: usize) -> Result<(), String> {
        let (p, layout) = (writer.p, writer.layout);
        let chunk = lowered::CHUNK as u64;
        // Six items save RSP twice and the depth (`Prog::saves_rsp`), and two
        // store each byte while there is room.
        const SAVED: usize = 6;
        let mut at = SAVED;
        let mut text = format!("theorem {p}_entry_saved(): Start.saves_rsp({layout}, {}().depth) = {} {{ refl }}\n", self.src, writer.program(at));
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
        let start = writer.program(SAVED);
        text.push_str(&format!("theorem {p}_entry(): {src}().entry({LOW}, {homes}) = {end} {{\n    \
            {src}().entry_of({LOW}, {homes}, {start}, {end}, {p}_entry_saved(), {p}_in_0_is())\n}}\n", src = self.src, homes = self.homes, LOW = super::elf::LOW));
        writer.cuts.insert(SAVED);
        writer.theorems.push_str(&text);
        Ok(())
    }
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
            Part::Whole { id, names, read, .. } => {
                let after = self.readings[*read].names.ok_or_else(out_of_order)?;
                (*id, *names, self.starts[*read], self.end(*read), after, "refl".to_string())
            }
            Part::Then { id, names, first, rest, .. } => {
                let (start, middle, between) = self.part(first)?;
                let (rest_start, end, after) = self.part(rest)?;
                if rest_start != middle { return Err(out_of_order()); }
                if rest.names() != between { return Err(miscounted()); }
                let proof = format!("trans(Stmt::emits_then_of({p}_s_{id}(), trivial, {}, {layout}, {p}_o_{id}(), {p}_kn_{id}(), {names}, Compiled({}, {between}), {p}_e_{}()), {p}_e_{}())",
                    self.program(start), self.program(middle), first.id(), rest.id());
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
