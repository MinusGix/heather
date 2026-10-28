//! A source read back as a literal (`Source::spelled`, native_source_spelled): its
//! words, its buffers, and its statement tree with each leaf's nodes. `write-elf`
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
            tag => return Err(format!("node tag {tag}")),
        };
        Ok(format!("{name}({})", join(&self.take(fields)?)))
    }

    fn call(&mut self) -> Result<String, String> {
        let (name, fields) = match self.next()? {
            0 => ("Reads", 4),
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
                let inputs = self.reader.ports()?;
                let count = self.reader.next()? as usize;
                let nodes = (0..count).map(|_| self.reader.node()).collect::<Result<Vec<_>, String>>()?;
                let outputs = self.reader.ports()?;
                (format!("Compute(Dataflow(Region({inputs}, [{}], {outputs})))", nodes.join(", ")), 1 + count)
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
/// itself `[0]` (functions, or a region past a dataflow leaf), which is
/// compiled as it is.
pub(super) fn literal(p: &str, numbers: &[u64]) -> Result<Option<(String, Vec<(u64, usize)>)>, String> {
    let mut printer = Printer { reader: Reader { numbers, at: 0 }, p, defs: String::new(), count: 0 };
    if printer.reader.next()? == 0 { return Ok(None); }
    let words = printer.reader.next()?;
    let count = printer.reader.next()? as usize;
    let buffers = buffers(p, &mut printer.reader, count)?;
    let (main, _) = printer.stmt()?;
    if printer.reader.at != numbers.len() {
        return Err("the spelled source ran past its statement".into());
    }
    Ok(Some((format!("{}{}fn {p}_lowered() → Source {{ Source(functions := [], buffers := {}, words := {words}, main := {main}) }}\n",
        buffers.defs, printer.defs, buffers.list), buffers.shapes)))
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
        let bytes = reader.take(len)?.iter().map(|b| format!("@bitvec::BitVec::ofNat(8, {b})")).collect::<Vec<_>>();
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
