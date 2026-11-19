//! A source read back as a literal (`Source::spelled`, native_source_spelled): its
//! words, its buffers, the functions it calls, and its statement tree with
//! each leaf's nodes. `write-elf`
//! states the literal, checks it equal to the source by `refl`, and
//! compiles it, so a source a builder lowers is evaluated once rather than
//! in every statement of the certificate.
//!
//! The tree is cut into definitions as it is printed: a subtree past
//! `LIMIT` statements and nodes becomes a definition of its own, so no
//! declaration nests as deep as a long program's statement chain does.

/// Statements and nodes a printed subtree holds before it is a definition.
const LIMIT: usize = 48;

pub(super) struct Reader<'a> {
    pub numbers: &'a [u64],
    pub at: usize,
}

// `Operation`'s constructors in the order `Operation::code` numbers them.
const OPERATIONS: &[&str] = &["Mul", "ShlBy", "ShrBy", "UDiv", "URem"];

impl Reader<'_> {
    pub fn next(&mut self) -> Result<u64, String> {
        let n = *self.numbers.get(self.at).ok_or("the spelled source ended early")?;
        self.at += 1;
        Ok(n)
    }

    fn take(&mut self, count: usize) -> Result<Vec<u64>, String> { (0..count).map(|_| self.next()).collect() }

    fn ports(&mut self) -> Result<String, String> {
        let count = self.next()? as usize;
        let ports = (0..count).map(|_| Ok(format!("Port({}, {})", self.next()?, self.next()?))).collect::<Result<Vec<_>, String>>()?;
        Ok(format!("Ports([{}])", ports.join(", ")))
    }

    pub fn node(&mut self) -> Result<String, String> {
        let (name, fields) = match self.next()? {
            0 => ("Const", 3),
            1 => ("Move", 3),
            2 => ("Add", 4),
            3 => ("Sub", 4),
            4 => ("BitAnd", 4),
            5 => ("BitOr", 4),
            6 => ("BitXor", 4),
            7 => ("ShiftLeft", 4),
            8 => ("LogicalShiftRight", 4),
            9 => ("ArithmeticShiftRight", 4),
            10 => ("UnsignedLessThan", 4),
            11 => ("SignedLessThan", 4),
            12 => ("Equal", 4),
            13 => ("BufferLoad", 3),
            14 => ("BufferStore", 4),
            15 => ("Resize", 4),
            16 => ("SignResize", 4),
            // A table read: four fields, then its entries as a counted list.
            17 => {
                let fields = join(&self.take(4)?);
                return Ok(format!("TableRead({fields}, {})", self.ids()?));
            }
            18 => ("WideLoad", 4),
            19 => ("WideStore", 5),
            20 => ("ByteSwap", 3),
            21 => ("RotateRight", 4),
            // An operation's row (`function_ir_operation`): its constructor
            // by `Operation::code`, then four fields.
            22 => {
                let op = *OPERATIONS.get(self.next()? as usize).ok_or_else(|| "operation code".to_string())?;
                return Ok(format!("Apply({op}, {})", join(&self.take(4)?)));
            }
            tag => return Err(format!("node tag {tag}")),
        };
        Ok(format!("{name}({})", join(&self.take(fields)?)))
    }

    fn ids(&mut self) -> Result<String, String> {
        let count = self.next()? as usize;
        Ok(format!("[{}]", join(&self.take(count)?)))
    }

    /// A dataflow leaf's ports and nodes (`Region::spelled_body`), and how
    /// many nodes it has.
    fn body(&mut self) -> Result<(String, usize), String> {
        let inputs = self.ports()?;
        let count = self.next()? as usize;
        let nodes = (0..count).map(|_| self.node()).collect::<Result<Vec<_>, String>>()?;
        let outputs = self.ports()?;
        Ok((format!("Region({inputs}, [{}], {outputs})", nodes.join(", ")), count))
    }

    /// A region as `StructuredRegion::spelled_tagged` spells it, and how
    /// many regions and nodes it holds.
    fn region(&mut self) -> Result<(String, usize), String> {
        Ok(match self.next()? {
            0 => {
                let (body, n) = self.body()?;
                (format!("Dataflow({body})"), 1 + n)
            }
            1 => {
                let (prefix, n) = self.body()?;
                let (rest, m) = self.region()?;
                (format!("Sequence({prefix}, {rest})"), 1 + n + m)
            }
            2 => {
                let (first, n) = self.region()?;
                let (rest, m) = self.region()?;
                (format!("Compose({first}, {rest})"), 1 + n + m)
            }
            3 => {
                let inputs = self.ports()?;
                let condition = self.next()?;
                let arguments = self.ports()?;
                let outputs = self.ports()?;
                let (yes, n) = self.region()?;
                let (no, m) = self.region()?;
                (format!("Conditional({inputs}, {condition}, {arguments}, {outputs}, {yes}, {no})"), 1 + n + m)
            }
            4 => {
                let callee = self.next()?;
                let arguments = self.ids()?;
                (format!("Call({callee}, {arguments}, {})", self.next()?), 1)
            }
            5 => {
                let inputs = self.ids()?;
                let bound = self.next()?;
                let parameters = self.ids()?;
                let count = self.next()?;
                let (body, n) = self.region()?;
                let exit = self.next()?;
                let next = self.ids()?;
                let outputs = self.ids()?;
                let exhausted = self.next()?;
                (format!("Loop({inputs}, {bound}, {parameters}, {count}, {body}, {exit}, {next}, {outputs}, {exhausted})"), 1 + n)
            }
            6 => {
                let count = self.next()? as usize;
                let views = (0..count).map(|_| {
                    let f = self.take(7)?;
                    let written = match f[4] { 0 => "False", 1 => "True", mark => return Err(format!("view mark {mark}")) };
                    Ok(format!("View({}, {}, {}, {}, {written}, {}, {})", f[0], f[1], f[2], f[3], f[5], f[6]))
                }).collect::<Result<Vec<_>, String>>()?;
                let callee = self.next()?;
                let arguments = self.ids()?;
                (format!("Lend([{}], {callee}, {arguments}, {})", views.join(", "), self.next()?), 1)
            }
            tag => return Err(format!("region tag {tag}")),
        })
    }

    fn call(&mut self) -> Result<String, String> {
        let (name, fields) = match self.next()? {
            0 => ("Reads", 5),
            1 => ("Writes", 5),
            2 => ("Opens", 3),
            3 => ("Closes", 2),
            4 => ("StatsPath", 4),
            5 => ("StatsFd", 3),
            tag => return Err(format!("call tag {tag}")),
        };
        Ok(format!("{name}({})", join(&self.take(fields)?)))
    }
}

fn join(numbers: &[u64]) -> String { numbers.iter().map(u64::to_string).collect::<Vec<_>>().join(", ") }

pub(super) struct Printer<'a> {
    pub reader: Reader<'a>,
    pub p: &'a str,
    pub defs: String,
    pub count: usize,
}

impl Printer<'_> {
    /// The next statement, and how many statements and nodes it holds as
    /// printed (a definition's call holds one).
    pub fn stmt(&mut self) -> Result<(String, usize), String> {
        let (text, size) = match self.reader.next()? {
            0 => {
                let (body, count) = self.reader.body()?;
                (format!("Compute(Dataflow({body}))"), 1 + count)
            }
            1 => (format!("Invoke({})", self.reader.call()?), 1),
            2 => {
                let (first, a) = self.stmt()?;
                let (rest, b) = self.stmt()?;
                (format!("Then({first}, {rest})"), 1 + a + b)
            }
            3 => {
                let condition = self.reader.next()?;
                let (yes, a) = self.stmt()?;
                let (no, b) = self.stmt()?;
                (format!("Branch({condition}, {yes}, {no})"), 1 + a + b)
            }
            4 => {
                let again = self.reader.next()?;
                let (body, a) = self.stmt()?;
                (format!("Repeat({body}, {again})"), 1 + a)
            }
            5 => (format!("Exit({})", self.reader.next()?), 1),
            6 => (format!("Arg({})", join(&self.reader.take(3)?)), 1),
            7 => {
                let (region, size) = self.reader.region()?;
                (format!("Compute({region})"), size)
            }
            8 => {
                let procedure = self.reader.next()?;
                let args = self.reader.ids()?;
                (format!("Perform({procedure}, {args}, {})", self.reader.ids()?), 1)
            }
            tag => return Err(format!("statement tag {tag}")),
        };
        if size <= LIMIT { return Ok((text, size)); }
        let name = format!("{}_lowered_{}", self.p, self.count);
        self.count += 1;
        self.defs.push_str(&format!("fn {name}() → Stmt {{ {text} }}\n"));
        Ok((format!("{name}()"), 1))
    }
}

/// The definitions of `{p}_lowered()`, the source `numbers` spell, and its
/// buffers' capacities and initial lengths; `None` when the source spelled
/// itself `[0]`, which is compiled as it is.
/// A source with procedures spells itself `[2]`, its room after its words
/// and its procedures after its buffers; one with functions `[3]`, as `[2]`
/// with its functions before its procedures, each a definition
/// (`{p}_fn_{k}()`) and each ending with how many buffers it is lent.
pub(super) fn literal(p: &str, numbers: &[u64]) -> Result<Option<(String, Vec<(u64, usize)>)>, String> {
    let mut printer = Printer { reader: Reader { numbers, at: 0 }, p, defs: String::new(), count: 0 };
    let tag = printer.reader.next()?;
    if tag == 0 { return Ok(None); }
    if tag > 3 { return Err(format!("source tag {tag}")); }
    let words = printer.reader.next()?;
    let room = if tag >= 2 { Some(printer.reader.next()?) } else { None };
    let count = printer.reader.next()? as usize;
    let buffers = buffers(p, &mut printer.reader, count)?;
    let mut functions = Vec::new();
    if tag == 3 {
        for k in 0..printer.reader.next()? {
            let parameters = printer.reader.ids()?;
            let (body, _) = printer.reader.region()?;
            let result = printer.reader.next()?;
            // How many buffers it is lent: said only where it is lent any,
            // so a program of functions over words is the literal it was.
            let lent = match printer.reader.next()? { 0 => String::new(), lent => format!(", lent := {lent}") };
            printer.defs.push_str(&format!("fn {p}_fn_{k}() → Function {{ Function({parameters}, {body}, {result}{lent}) }}\n"));
            functions.push(format!("{p}_fn_{k}()"));
        }
    }
    let mut calls = String::new();
    if let Some(room) = room {
        let count = printer.reader.next()? as usize;
        let mut procedures = Vec::with_capacity(count);
        for _ in 0..count {
            let params = printer.reader.ids()?;
            let results = printer.reader.ids()?;
            let (body, _) = printer.stmt()?;
            procedures.push(format!("Procedure(params := {params}, results := {results}, body := {body})"));
        }
        calls = format!(", procedures := [{}], room := {room}", procedures.join(", "));
    }
    let (main, _) = printer.stmt()?;
    if printer.reader.at != numbers.len() {
        return Err("the spelled source ran past its statement".into());
    }
    Ok(Some((format!("{}{}fn {p}_lowered() → Source {{ Source(functions := [{}], buffers := {}, words := {words}, main := {main}{calls}) }}\n",
        buffers.defs, printer.defs, functions.join(", "), buffers.list), buffers.shapes)))
}

/// Initial bytes in each definition of a buffer's bytes: `write-elf`
/// states the entry's stores of them a definition at a time
/// (`emission::Inits`).
pub(super) const CHUNK: usize = 32;

/// A source's buffers as definitions: buffer `j` is `{p}_bl_{j}()`'s first,
/// its initial bytes `{p}_it_{j}_0()`, each `{p}_it_{j}_{k}()` the
/// `CHUNK` bytes `{p}_ib_{j}_{k}()` and then the next; and each buffer's
/// capacity and how many initial bytes it has.
pub(super) struct Buffers { pub defs: String, pub list: String, pub shapes: Vec<(u64, usize)> }

/// `count` buffers as `List::spell_buffers` spells them.
pub(super) fn buffers(p: &str, reader: &mut Reader<'_>, count: usize) -> Result<Buffers, String> {
    // Each definition before the ones that name it: the last buffer's
    // first, and a buffer's last bytes first.
    let mut texts = Vec::with_capacity(count);
    let mut shapes = Vec::with_capacity(count);
    for j in 0..count {
        let capacity = reader.next()?;
        let len = reader.next()? as usize;
        let bytes = reader.take(len)?.iter().map(|&b| super::word_literal(8, u64::from(b))).collect::<Vec<_>>();
        let chunks: Vec<&[String]> = bytes.chunks(CHUNK).collect();
        let mut text = format!("fn {p}_it_{j}_{}() → List<BitVec(8)> {{ [] }}\n", chunks.len());
        for (k, chunk) in chunks.iter().enumerate().rev() {
            text.push_str(&format!("fn {p}_ib_{j}_{k}() → List<BitVec(8)> {{ [{}] }}\n\
                fn {p}_it_{j}_{k}() → List<BitVec(8)> {{ List::append({p}_ib_{j}_{k}(), {p}_it_{j}_{}()) }}\n", chunk.join(", "), k + 1));
        }
        text.push_str(&format!("fn {p}_bl_{j}() → List<Buffer> {{ Cons(Buffer({capacity}, {p}_it_{j}_0()), {p}_bl_{}()) }}\n", j + 1));
        texts.push(text);
        shapes.push((capacity, len));
    }
    let mut defs = format!("fn {p}_bl_{count}() → List<Buffer> {{ [] }}\n");
    for text in texts.iter().rev() { defs.push_str(text); }
    Ok(Buffers { defs, list: format!("{p}_bl_0()"), shapes })
}
