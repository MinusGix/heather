//! What `compile-x86`'s reads answered, remembered across runs
//! (issues/optimizer-search-answers-memo.md).
//!
//! The optimizer's searches and the planner, emitter and layout after them
//! are reads: a module of definitions elaborated on a fork of the session,
//! then a nullary `List<Nat>` evaluated and read back. A warm compile used
//! to evaluate every one again, though the store already replayed the
//! library and the certificate; the reads were most of its time.
//!
//! Nothing a read answers is trusted. A search's plan and the function it
//! made, a placement, an emission, the bytes: each is stated in the
//! certificate as a literal and the kernel checks what is claimed of it. So
//! an answer can be remembered without trusting the store: a wrong or stale
//! one is a certificate that does not check, never a wrong program. To keep
//! even that from sticking, answers are written only once the certificate
//! they went into has checked ([`Answers::save`]).
//!
//! An answer's key is everything the read could depend on: the elaborator
//! and kernel this binary is (`SemanticsIdentity`), the sources the session
//! loaded (the bundled proof library and the program's closure, by name and
//! text), every module the fork defined before the read, in order, and the
//! name read. So a hit is a read whose whole world is the same text, and a
//! changed library module, lowering or generator is a miss.
//!
//! A [`Reading`] defines its modules lazily: a module is elaborated only
//! when a read misses, and then with every module queued before it. A
//! compile whose reads all hit elaborates none of them.

use std::cell::{Cell, RefCell};
use std::path::{Path, PathBuf};
use std::time::{Duration, SystemTime};

use heather_cache::sha256::{Sha256, hex};
use heather_elab::{Elaborator, function_ir_source};

/// An answer not read for this long is removed when answers are saved.
const KEPT: Duration = Duration::from_secs(14 * 24 * 60 * 60);

/// The answers of one compile: those remembered under `dir`, and the ones
/// evaluated by this run, which [`Answers::save`] adds.
pub(super) struct Answers {
    dir: Option<PathBuf>,
    base: [u8; 32],
    evaluated: RefCell<Vec<(String, Vec<u64>)>>,
    hits: Cell<usize>,
}

impl Answers {
    /// Answers over the store at `cache` (`<cache>/native-answers`), or
    /// none remembered without one. `sources` are the modules the session
    /// loaded, by name and text.
    pub(super) fn new<'s>(cache: Option<&Path>, sources: impl IntoIterator<Item = (&'s str, &'s str)>) -> Answers {
        let mut h = Sha256::new();
        h.update(b"heather compile-x86 answers v1\0");
        h.update(&heather_cache::module_image::SemanticsIdentity::current().bytes());
        for (name, text) in sources {
            put(&mut h, name.as_bytes());
            put(&mut h, text.as_bytes());
        }
        Answers { dir: cache.map(|dir| dir.join("native-answers")), base: h.finish(), evaluated: RefCell::new(Vec::new()), hits: Cell::new(0) }
    }

    /// How many reads were answered from the store, and how many evaluated.
    pub(super) fn counts(&self) -> (usize, usize) { (self.hits.get(), self.evaluated.borrow().len()) }

    fn path(&self, key: &str) -> Option<PathBuf> { self.dir.as_ref().map(|dir| dir.join(format!("{key}.txt"))) }

    /// A remembered answer, its file's time renewed so the sweep keeps it.
    /// A file that does not parse is a miss.
    fn get(&self, key: &str) -> Option<Vec<u64>> {
        let path = self.path(key)?;
        let text = std::fs::read_to_string(&path).ok()?;
        let numbers = text.split_ascii_whitespace().map(|n| n.parse::<u64>().ok()).collect::<Option<Vec<u64>>>()?;
        if let Ok(file) = std::fs::File::options().append(true).open(&path) { let _ = file.set_modified(SystemTime::now()); }
        self.hits.set(self.hits.get() + 1);
        Some(numbers)
    }

    /// Writes this run's answers, each to a file of its own (a temporary
    /// name, then renamed, so a reader sees a whole answer or none), and
    /// removes the answers no run has read for [`KEPT`]. Called only once
    /// the certificate has checked.
    pub(super) fn save(&self) -> std::io::Result<()> {
        let Some(dir) = &self.dir else { return Ok(()) };
        std::fs::create_dir_all(dir)?;
        for (key, numbers) in self.evaluated.borrow().iter() {
            let mut text = String::with_capacity(numbers.len() * 4);
            for n in numbers {
                text.push_str(&n.to_string());
                text.push(' ');
            }
            let path = dir.join(format!("{key}.txt"));
            let partial = dir.join(format!("{key}.{}.partial", std::process::id()));
            std::fs::write(&partial, text)?;
            std::fs::rename(&partial, &path)?;
        }
        let now = SystemTime::now();
        for entry in std::fs::read_dir(dir)?.flatten() {
            let old = entry.metadata().and_then(|m| m.modified()).is_ok_and(|at| now.duration_since(at).is_ok_and(|age| age > KEPT));
            if old { let _ = std::fs::remove_file(entry.path()); }
        }
        Ok(())
    }
}

fn put(h: &mut Sha256, bytes: &[u8]) {
    h.update(&(bytes.len() as u64).to_le_bytes());
    h.update(bytes);
}

/// A fork of the session that reads, its definitions queued until a read
/// misses.
pub(super) struct Reading<'a> {
    fork: Elaborator,
    answers: &'a Answers,
    /// Every module defined so far, in order.
    chain: Sha256,
    /// Defined and not yet elaborated, in order.
    queued: Vec<(String, String)>,
    /// The machine the reads that miss run on, started by the first: a
    /// read spelled from an earlier one's definitions finds them evaluated.
    machine: Option<function_ir_source::RunSession>,
}

impl<'a> Reading<'a> {
    pub(super) fn new(elab: &Elaborator, answers: &'a Answers) -> Reading<'a> {
        let mut chain = Sha256::new();
        chain.update(&answers.base);
        Reading { fork: elab.fork(), answers, chain, queued: Vec::new(), machine: None }
    }

    /// Defines a module: elaborated before the first read that misses, and
    /// never if none does. A module that does not elaborate is that read's
    /// error.
    pub(super) fn define(&mut self, module: &str, text: &str) {
        put(&mut self.chain, module.as_bytes());
        put(&mut self.chain, text.as_bytes());
        self.queued.push((module.to_string(), text.to_string()));
    }

    /// Defines a module and elaborates it now, with every module queued
    /// before it.
    pub(super) fn define_now(&mut self, module: &str, text: &str) -> Result<(), String> {
        self.define(module, text);
        self.elaborate()
    }

    fn elaborate(&mut self) -> Result<(), String> {
        for (module, text) in std::mem::take(&mut self.queued) {
            self.fork.elab_module_source(&module, &text).map_err(|e| e.render(&text))?;
        }
        Ok(())
    }

    /// The nullary `List<Nat>` `name` (`module::item`), remembered or
    /// evaluated.
    pub(super) fn read(&mut self, name: &str) -> Result<Vec<u64>, String> {
        let mut h = self.chain.clone();
        put(&mut h, name.as_bytes());
        let key = hex(&h.finish());
        if let Some(numbers) = self.answers.get(&key) { return Ok(numbers); }
        self.elaborate()?;
        let machine = self.machine.get_or_insert_with(|| function_ir_source::RunSession::new(&self.fork));
        let numbers = function_ir_source::evaluate_numbers_in(machine, &self.fork, name).map_err(|e| e.to_string())?;
        self.answers.evaluated.borrow_mut().push((key, numbers.clone()));
        Ok(numbers)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn store(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("heather-answers-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        dir
    }

    // A read is answered from the store only when everything before it is
    // the same text: the sources, each module defined, the name read. A
    // remembered answer elaborates nothing, so a module that would not
    // elaborate is not noticed; a changed module is a miss and is.
    #[test]
    fn an_answer_is_remembered_only_over_the_same_text() {
        let dir = store("same-text");
        let elab = Elaborator::with_prelude().unwrap();
        let sources = [("m", "fn f() → Nat { 1 }")];
        let one = "fn x() → List<Nat> { Cons(1, Cons(2, Nil)) }";
        let read = |answers: &Answers, text: &str| {
            let mut reading = Reading::new(&elab, answers);
            reading.define("probe_a", &format!("inductive List<A> {{ Nil, Cons(head: A, tail: List<A>) }}\n{text}"));
            reading.read("probe_a::x")
        };
        let first = Answers::new(Some(&dir), sources);
        assert_eq!(read(&first, one), Ok(vec![1, 2]));
        assert_eq!(first.counts(), (0, 1));
        // Nothing is kept until the caller says what it stood on checked.
        assert_eq!(read(&Answers::new(Some(&dir), sources), one), Ok(vec![1, 2]));
        first.save().unwrap();

        let again = Answers::new(Some(&dir), sources);
        assert_eq!(read(&again, one), Ok(vec![1, 2]));
        assert_eq!(again.counts(), (1, 0));
        // Another module before the read: a miss.
        let other = "fn x() → List<Nat> { Cons(3, Nil) }";
        assert_eq!(read(&again, other), Ok(vec![3]));
        assert_eq!(again.counts(), (1, 1));
        // Another source: a miss, and the module's error is the read's.
        let changed = Answers::new(Some(&dir), [("m", "fn f() → Nat { 2 }")]);
        let refused = read(&changed, "fn x() → List<Nat> { undefined_name }");
        assert!(refused.as_ref().is_err_and(|why| why.contains("undefined_name")), "{refused:?}");
        assert_eq!(changed.counts(), (0, 0));
        // Without a store nothing is remembered.
        let none = Answers::new(None, sources);
        assert_eq!(read(&none, one), Ok(vec![1, 2]));
        none.save().unwrap();
        assert_eq!(none.counts(), (0, 1));
        let _ = std::fs::remove_dir_all(&dir);
    }
}
