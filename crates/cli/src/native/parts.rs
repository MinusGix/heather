//! A builder tool's lowering stated a part of its statement tree at a time
//! (lib/native/native_build_parts.hthr, issues/native-tool-certificate-budget.md).
//!
//! One `refl` of `Tool::source` costs about the tool's size, and a
//! declaration has a fixed fuel, so a tool past cat FILE's size did not
//! check. Here the tool's statement tree is read first (`Act::shape`, which
//! lowers nothing), each part small enough is marked to be packed whole, and
//! one read (`Act::traced`) packs the tool along that plan and spells what
//! each whole part, `Let`'s word, and test adds. In the certificate a whole
//! part's packing is one `refl` with what was done before it a variable
//! (`d`), and every larger part is joined from its parts by
//! `Act::packs_seq_of`, `packs_let_of`, `packs_when_of`, `packs_while_of`
//! or `packs_do_while_of`. A branch's arms and a loop's body are lowered
//! alone, and named (`{p}_w_`) where their branch or loop is.
//!
//! Every statement a packing does is a definition of its own (`{p}_u_`),
//! named by the packings that do it and the statements that chain them, so
//! a join compares names. The literal source the certificate compiles is
//! made of the same definitions.
//!
//! The reads are untrusted: a misreading is a statement the kernel refuses.

use super::lowered::{self, Printer, Reader};

/// A part whose statements and values together are at most this many is
/// packed whole by one `refl`.
const WEIGHT: u64 = 48;
/// Statements a chain's definition holds before the rest is a definition.
const CHAIN: usize = 32;

/// A statement of `Act::shape`'s tree.
struct Shape { kind: u64, next: u64, children: Vec<Shape>, weight: u64 }

impl Shape {
    fn read(records: &mut std::slice::Iter<'_, [u64; 3]>) -> Result<Shape, String> {
        let &[kind, next, own] = records.next().ok_or("the tool's shape ended early")?;
        let arity = match kind { 1 | 5 => 2, 2 | 6 | 7 => 1, 0 | 3 | 4 | 8..=14 => 0, _ => return Err(format!("statement kind {kind}")) };
        let children = (0..arity).map(|_| Shape::read(records)).collect::<Result<Vec<_>, _>>()?;
        let weight = 1 + own + children.iter().map(|c| c.weight).sum::<u64>();
        Ok(Shape { kind, next, children, weight })
    }

    fn whole(&self) -> bool { self.children.is_empty() || self.weight <= WEIGHT }

    /// `Act::traced`'s plan: a flag a statement, in preorder, a whole
    /// statement's parts left out.
    fn plan(&self, flags: &mut Vec<&'static str>) {
        if self.whole() {
            flags.push("1");
        } else {
            flags.push("0");
            for child in &self.children { child.plan(flags); }
        }
    }
}

/// The text for a tool's shape: `fn {p}_a_0` and the read of its shape.
pub(super) fn shape_text(p: &str, tool: &str) -> String {
    format!("fn {p}_a_0() → Act {{ {tool}.opened(0).main }}\nfn {p}_shape() → List<Nat> {{ {p}_a_0().shape(0) }}\n\
        fn {p}_buffers_spelled() → List<Nat> {{ Cons({tool}.opened(0).buffers.len(), {tool}.opened(0).buffers.spell_buffers()) }}\n")
}

/// What the plan reads: `Act::traced` along the plan `shape` gives.
pub(super) struct Plan { root: Shape, pub text: String }

pub(super) fn plan(p: &str, shape: &[u64]) -> Result<Plan, String> {
    if shape.len() % 3 != 0 { return Err("the tool's shape is malformed".into()); }
    let records: Vec<[u64; 3]> = shape.chunks(3).map(|r| [r[0], r[1], r[2]]).collect();
    let mut at = records.iter();
    let root = Shape::read(&mut at)?;
    if at.next().is_some() || root.next != 0 { return Err("the tool's shape is malformed".into()); }
    let mut flags = Vec::new();
    root.plan(&mut flags);
    let text = format!("fn {p}_trace() → List<Nat> {{ {p}_a_0().traced(0, Packing::start(), [{}]).out }}\n", flags.join(", "));
    Ok(Plan { root, text })
}

/// The definitions of a tool's literal source (`{p}_lowered()`, with the
/// parts' names `{p}_a_` and everything their statements name), the
/// theorems that the tool lowers to it, `{p}_lowered_is` last, and its
/// buffers' capacities and initial lengths.
pub(super) struct Stated { pub defs: String, pub theorems: String, pub shapes: Vec<(u64, usize)> }

/// `tool` spells the tool, `trace` is `{p}_trace`'s read, `buffers` is
/// `{p}_buffers_spelled`'s.
pub(super) fn state(p: &str, tool: &str, plan: Plan, trace: &[u64], buffers: &[u64]) -> Result<Stated, String> {
    let mut reader = Reader { numbers: buffers, at: 0 };
    let count = reader.next()? as usize;
    let buffers = lowered::buffers(p, &mut reader, count)?;
    if reader.at != reader.numbers.len() {
        return Err("the tool's buffers ran past their spelling".into());
    }
    let mut writer = Writer { p, printer: Printer { reader: Reader { numbers: trace, at: 0 }, p, defs: String::new(), count: 0 },
        defs: String::new(), theorems: String::new(), parts: 1, units: 0, chains: 0 };
    let (units, group) = writer.part(&plan.root, 0, "[]")?;
    if writer.printer.reader.at != trace.len() {
        return Err("the tool's packing ran past its plan".into());
    }
    writer.lowered_alone(0, 0, &units, &group)?;
    let Writer { mut defs, mut theorems, printer, .. } = writer;
    defs.insert_str(0, &printer.defs);
    defs.insert_str(0, &format!("fn {p}_a_0() → Act {{ {tool}.opened(0).main }}\n"));
    defs.push_str(&buffers.defs);
    defs.push_str(&format!("fn {p}_lowered() → Source {{ Source::of({list}, {p}_w_0()) }}\n", list = buffers.list));
    theorems.push_str(&format!("theorem {p}_buffers_is(): {tool}.opened(0).buffers = {list} {{ refl }}\n\
        theorem {p}_lowered_is(): {tool}.source() = {p}_lowered() {{ {tool}.source_of({list}, {p}_w_0(), refl, {p}_buffers_is(), {p}_l_0(), refl) }}\n", list = buffers.list));
    Ok(Stated { defs, theorems, shapes: buffers.shapes })
}

struct Writer<'a> { p: &'a str, printer: Printer<'a>, defs: String, theorems: String, parts: usize, units: usize, chains: usize }

impl Writer<'_> {
    /// A statement done, a definition of its own.
    fn unit(&mut self, text: &str) -> String {
        let name = format!("{}_u_{}()", self.p, self.units);
        self.units += 1;
        self.defs.push_str(&format!("fn {name} → Stmt {{ {text} }}\n"));
        name
    }

    /// A packing `Packing::spelled` read from nothing done: its statements
    /// done as definitions, in the order they were done, and its leaf.
    fn packing(&mut self) -> Result<(Vec<String>, String), String> {
        let count = self.printer.reader.next()? as usize;
        let mut done = Vec::with_capacity(count);
        for _ in 0..count {
            let (text, _) = self.printer.stmt()?;
            done.push(text);
        }
        let len = self.printer.reader.next()? as usize;
        let group = (0..len).map(|_| self.printer.reader.node()).collect::<Result<Vec<_>, String>>()?;
        // Spelled the last first; named in the order done.
        let units = done.iter().rev().map(|text| self.unit(text)).collect();
        Ok((units, format!("[{}]", group.join(", "))))
    }

    /// The statements done, the last first, onto `d`.
    fn onto(units: &[String], d: &str) -> String {
        units.iter().fold(d.to_string(), |rest, unit| format!("Cons({unit}, {rest})"))
    }

    fn child(&mut self, id: usize, next: u64, side: bool) -> usize {
        let child = self.parts;
        self.parts += 1;
        self.defs.push_str(&format!("fn {p}_a_{child}() → Act {{ {p}_a_{id}().part({next}, {}) }}\n", if side { "True" } else { "False" }, p = self.p));
        child
    }

    /// Part `id` packed from the leaf `g_in`: `{p}_f_{id}` and
    /// `{p}_t_{id}`, the statements it does in order, and the leaf after it.
    fn part(&mut self, shape: &Shape, id: usize, g_in: &str) -> Result<(Vec<String>, String), String> {
        let (p, next) = (self.p, shape.next);
        let statement = |g_out: &str| format!("theorem {p}_t_{id}(d: List<Stmt>): {p}_a_{id}().packs({next}, Packing(d, {g_in})) = Packing({p}_f_{id}(d), {g_out})");
        if shape.whole() {
            let (units, g_out) = self.packing()?;
            self.defs.push_str(&format!("fn {p}_f_{id}(d: List<Stmt>) → List<Stmt> {{ {} }}\n", Self::onto(&units, "d")));
            self.theorems.push_str(&format!("{} {{ refl }}\n", statement(&g_out)));
            return Ok((units, g_out));
        }
        match (shape.kind, &shape.children[..]) {
            (1, [first, second]) => {
                let (a, b) = (self.child(id, next, true), self.child(id, next, false));
                let (mut units, g_mid) = self.part(first, a, g_in)?;
                let (more, g_out) = self.part(second, b, &g_mid)?;
                units.extend(more);
                self.defs.push_str(&format!("fn {p}_f_{id}(d: List<Stmt>) → List<Stmt> {{ {p}_f_{b}({p}_f_{a}(d)) }}\n"));
                self.theorems.push_str(&format!("{} {{\n    {p}_a_{id}().packs_seq_of(trivial, {next}, {g_in}, {g_mid}, {g_out}, {p}_f_{a}, {p}_f_{b}, {p}_t_{a}, {p}_t_{b}, d)\n}}\n",
                    statement(&g_out)));
                Ok((units, g_out))
            }
            (2, [body]) => {
                let (mut units, g_mid) = self.packing()?;
                self.defs.push_str(&format!("fn {p}_h_{id}(d: List<Stmt>) → List<Stmt> {{ {} }}\n", Self::onto(&units, "d")));
                self.theorems.push_str(&format!("theorem {p}_i_{id}(d: List<Stmt>): {p}_a_{id}().init_items({next}).pack(Packing(d, {g_in})) = Packing({p}_h_{id}(d), {g_mid}) {{ refl }}\n"));
                let b = self.child(id, next, true);
                let (more, g_out) = self.part(body, b, &g_mid)?;
                units.extend(more);
                self.defs.push_str(&format!("fn {p}_f_{id}(d: List<Stmt>) → List<Stmt> {{ {p}_f_{b}({p}_h_{id}(d)) }}\n"));
                self.theorems.push_str(&format!("{} {{\n    {p}_a_{id}().packs_let_of(trivial, {next}, {g_in}, {g_mid}, {g_out}, {p}_h_{id}, {p}_f_{b}, {p}_i_{id}, {p}_t_{b}, d)\n}}\n",
                    statement(&g_out)));
                Ok((units, g_out))
            }
            (5, [yes, no]) => {
                let (y, n) = (self.child(id, next, true), self.child(id, next, false));
                let (units_y, g_y) = self.part(yes, y, "[]")?;
                let (units_n, g_n) = self.part(no, n, "[]")?;
                self.lowered_alone(y, next, &units_y, &g_y)?;
                self.lowered_alone(n, next, &units_n, &g_n)?;
                let test = self.printer.reader.next()?;
                let (mut units, g_test) = self.packing()?;
                let branch = format!("Branch({test}, {p}_w_{y}(), {p}_w_{n}())");
                self.close(&mut units, &g_test);
                units.push(self.unit(&branch));
                self.defs.push_str(&format!("fn {p}_f_{id}(d: List<Stmt>) → List<Stmt> {{ {} }}\n", Self::onto(&units, "d")));
                self.theorems.push_str(&format!("theorem {p}_tw_{id}(d: List<Stmt>): {p}_a_{id}().tested({next}).nodes.ops().pack(Packing(d, {g_in}))\
                    .step(Do(Branch({p}_a_{id}().tested({next}).id, {p}_w_{y}(), {p}_w_{n}()))) = Packing({p}_f_{id}(d), []) {{ refl }}\n"));
                self.theorems.push_str(&format!("{} {{\n    trans({p}_a_{id}().packs_when_of(trivial, {next}, {p}_w_{y}(), {p}_w_{n}(), {p}_l_{y}(), {p}_l_{n}(), Packing(d, {g_in})), {p}_tw_{id}(d))\n}}\n",
                    statement("[]")));
                Ok((units, "[]".into()))
            }
            (kind @ (6 | 7), [body]) => {
                let b = self.child(id, next, true);
                let (units_b, g_b) = self.part(body, b, "[]")?;
                let test = self.printer.reader.next()?;
                let (closing, last) = self.packing()?;
                let mut pass = units_b;
                pass.extend(closing);
                self.chain(b, &pass, &last);
                self.theorems.push_str(&format!("theorem {p}_k_{b}(): {p}_a_{id}().tested({next}).nodes.ops().pack(Packing({p}_f_{b}([]), {g_b})).stmt() = {p}_w_{b}() {{ refl }}\n\
                    theorem {p}_l_{b}(): List::append({p}_a_{id}().part({next}, True).items({}), {p}_a_{id}().tested({next}).nodes.ops()).lowered() = {p}_w_{b}() {{\n    \
                    {p}_a_{id}().pass_of({next}, Packing({p}_f_{b}([]), {g_b}), {p}_w_{b}(), {p}_t_{b}([]), {p}_k_{b}())\n}}\n", next + 1));
                let (mut units, tw, lemma) = if kind == 6 {
                    let (mut units, g_test) = self.packing()?;
                    self.close(&mut units, &g_test);
                    (units, format!("{p}_a_{id}().tested({next}).nodes.ops().pack(Packing(d, {g_in}))\
                        .step(Do(Branch({p}_a_{id}().tested({next}).id, Repeat({p}_w_{b}(), {p}_a_{id}().tested({next}).id), Stmt::leaf([]))))"), "packs_while_of")
                } else {
                    let mut units = Vec::new();
                    self.close(&mut units, g_in);
                    (units, format!("Packing(d, {g_in}).step(Do(Repeat({p}_w_{b}(), {p}_a_{id}().tested({next}).id)))"), "packs_do_while_of")
                };
                let looped = if kind == 6 { format!("Branch({test}, Repeat({p}_w_{b}(), {test}), Stmt::leaf([]))") } else { format!("Repeat({p}_w_{b}(), {test})") };
                units.push(self.unit(&looped));
                self.defs.push_str(&format!("fn {p}_f_{id}(d: List<Stmt>) → List<Stmt> {{ {} }}\n", Self::onto(&units, "d")));
                self.theorems.push_str(&format!("theorem {p}_tw_{id}(d: List<Stmt>): {tw} = Packing({p}_f_{id}(d), []) {{ refl }}\n"));
                self.theorems.push_str(&format!("{} {{\n    trans({p}_a_{id}().{lemma}(trivial, {next}, {p}_w_{b}(), {p}_l_{b}(), Packing(d, {g_in})), {p}_tw_{id}(d))\n}}\n",
                    statement("[]")));
                Ok((units, "[]".into()))
            }
            _ => Err(format!("a statement of kind {} is not joined from parts", shape.kind)),
        }
    }

    /// The leaf `group` closed onto what is done, if it has nodes.
    fn close(&mut self, units: &mut Vec<String>, group: &str) {
        if group != "[]" { units.push(self.unit(&format!("Stmt::leaf({group})"))); }
    }

    /// `{p}_w_{id}`: the statements done, then the leaf `group` closed, each
    /// then the next (`Packing::stmt`), cut into definitions.
    fn chain(&mut self, id: usize, units: &[String], group: &str) {
        let mut all = units.to_vec();
        self.close(&mut all, group);
        let p = self.p;
        if all.is_empty() {
            self.defs.push_str(&format!("fn {p}_w_{id}() → Stmt {{ Stmt::leaf([]) }}\n"));
            return;
        }
        // From the end: each definition is its statements then the next.
        let mut rest: Option<String> = None;
        let chunks: Vec<&[String]> = all.chunks(CHAIN).collect();
        for (i, chunk) in chunks.iter().enumerate().rev() {
            let mut text = rest.take();
            for unit in chunk.iter().rev() {
                text = Some(match text { None => unit.clone(), Some(t) => format!("Then({unit}, {t})") });
            }
            let text = text.unwrap();
            if i == 0 {
                self.defs.push_str(&format!("fn {p}_w_{id}() → Stmt {{ {text} }}\n"));
            } else {
                let name = format!("{p}_wc_{}()", self.chains);
                self.chains += 1;
                self.defs.push_str(&format!("fn {name} → Stmt {{ {text} }}\n"));
                rest = Some(name);
            }
        }
    }

    /// Part `id` lowered alone, from nothing done: `{p}_w_{id}`, `{p}_k_`
    /// (its statement from its packing) and `{p}_l_{id}`.
    fn lowered_alone(&mut self, id: usize, next: u64, units: &[String], group: &str) -> Result<(), String> {
        let p = self.p;
        self.chain(id, units, group);
        self.theorems.push_str(&format!("theorem {p}_k_{id}(): Packing({p}_f_{id}([]), {group}).stmt() = {p}_w_{id}() {{ refl }}\n\
            theorem {p}_l_{id}(): {p}_a_{id}().lowered_at({next}) = {p}_w_{id}() {{\n    \
            {p}_a_{id}().lowered_of({next}, {group}, {p}_f_{id}, {p}_w_{id}(), {p}_t_{id}, {p}_k_{id}())\n}}\n"));
        Ok(())
    }
}
