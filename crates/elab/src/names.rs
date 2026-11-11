//! Modules and name resolution (docs/modules-design.md §4–5).
//!
//! Ψ is nameless — a `GlobalVar` is a de Bruijn index into one flat telescope
//! — so a module system lives entirely here: every name table keys
//! `(module, name)`, and a *reference* is resolved against the referring
//! module's visibility (its own declarations, its imports, and the implicitly
//! imported prelude).
//!
//! The regime, in one paragraph, because every function below is a corollary
//! of it: a name that resolves uniquely across everything visible just works,
//! unqualified; a name declared in two visible modules is **ambiguous at
//! use**, an error naming both origins rather than a silent first-match; a
//! file's own declaration beats an unlisted imported name (the file you are
//! reading beats the file you are not); a name written in an `import`'s list
//! is a standing disambiguation, so it beats an unlisted collision and
//! *conflicts* with a local declaration of the same name. Import order never
//! decides anything. The consequence that pays for it: library growth can
//! introduce errors, never reinterpretations.

use std::collections::HashMap;
use heather_kernel::rc::Rc;

use heather_syntax::Decl;

use super::ParamMeta;
use crate::layered::{Layer, Layered, NameMap, NameSet, index_hash};

thread_local! {
    /// While recording: the last `::` segment of every name and module this
    /// thread looked up, the early cutoff's account of what an elaboration
    /// could have observed of the world's names beyond what its source
    /// spells — an operator's fallback name, a tactic's lemma
    /// (`docs/module-interface-cutoff-design.md` §2).
    ///
    /// Every lookup of every name in a file comes through here, most of them
    /// for a name already in the record, so the question "is it noted" is
    /// one hash of the segment and the record is sorted once, when taken
    /// (`issues/name-lookup-record-cost.md`).
    static QUERIED: std::cell::RefCell<Option<NameSet<String>>> =
        const { std::cell::RefCell::new(None) };
}

/// The last `::` segment of `name`: what follows its last `::`, or all of it.
fn last_segment(name: &str) -> &str {
    let bytes = name.as_bytes();
    let mut at = bytes.len();
    while at >= 2 {
        if bytes[at - 1] == b':' && bytes[at - 2] == b':' {
            // `:` is one byte and never part of another character's encoding.
            return &name[at..];
        }
        at -= 1;
    }
    name
}

fn note(name: &str) {
    QUERIED.with(|q| {
        if let Some(set) = q.borrow_mut().as_mut() {
            let last = last_segment(name);
            if !set.contains(last) {
                set.insert(last.to_string());
            }
        }
    });
}

/// Start recording this thread's name lookups, dropping any earlier record.
pub fn record_name_lookups() {
    RECORD.with(|r| r.set(r.get() + 1));
    QUERIED.with(|q| *q.borrow_mut() = Some(Default::default()));
}

/// Stop recording and return what was looked up since
/// [`record_name_lookups`]; `None` when nothing was recording.
pub fn take_name_lookups() -> Option<std::collections::BTreeSet<String>> {
    RECORD.with(|r| r.set(r.get() + 1));
    QUERIED.with(|q| q.borrow_mut().take()).map(|noted| noted.into_iter().collect())
}

thread_local! {
    /// Which record [`QUERIED`] is: stepped whenever one starts or is taken,
    /// so that a lookup answered from a table ([`CommonClosure`]) knows
    /// whether this record already has the names its walk would have noted.
    static RECORD: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    /// The record, the closure and how much of that closure's walk has been
    /// noted in the record ([`CommonClosure::note_walk`]).
    static WALK_NOTED: std::cell::Cell<(u64, u64, usize)> = const { std::cell::Cell::new((0, 0, 0)) };
}

/// Which table a name lives in. Resolution is by name first and kind second —
/// two modules that declare the same name are ambiguous whatever the two
/// declarations *are*, and a module never declares one name twice — so this
/// exists to answer "is this global a global?" after the module is known, and
/// to phrase duplicate-declaration errors.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum NameKind {
    /// A `fn` or `theorem`.
    Global,
    /// An `inductive`/`record` declaration (including a machine-named
    /// skeleton).
    Inductive,
    /// A constructor. Keyed by its *own* name, and qualified by its **type**
    /// (`Option::None`), which is how constructors are already keyed
    /// per-inductive.
    Ctor,
    /// A `meta fn`.
    Meta,
}

/// One import of one module.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ImportSpec {
    pub module: String,
    /// The `::{…}` list, if written. Empty for a plain `import m;`.
    pub listed: Vec<String>,
    /// Selected public names, including constructors of selected inductives.
    pub exported: Vec<String>,
}

/// The visibility of the module currently being elaborated.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Scope {
    pub module: String,
    pub imports: Vec<ImportSpec>,
}

impl Scope {
    pub fn new(module: impl Into<String>) -> Self {
        Scope {
            module: module.into(),
            imports: Vec::new(),
        }
    }

    /// Every module a *reference* here may reach, own module first. The
    /// prelude is an implicit import of every module and is appended by the
    /// caller (it is not in `imports`, so that a file's written imports stay
    /// exactly what it wrote).
    pub fn imports_module(&self, m: &str) -> bool {
        self.imports.iter().any(|i| i.module == m)
    }
}

/// The module a name was declared in, plus what kind of declaration it was.
#[derive(Clone, Debug)]
struct NameEntry {
    module: String,
    /// Canonical declaration module; `module` may be a reexporting facade.
    origin: String,
    kind: NameKind,
}

/// Name → every declaration of it, across all modules elaborated so far.
///
/// The tables themselves stay keyed by the qualified string `module::name`
/// ([`qkey`]); this is the index that makes "which modules declare `sub`?" a
/// lookup rather than a scan, and it is the only place ambiguity is visible.
#[derive(Clone, Default)]
struct NameIndex {
    by_name: NameMap<String, Vec<NameEntry>>,
}

/// One module-sized name-registry delta. Sealed layers are immutable and
/// shared; only the current layer is detached when a suffix commits a name.
#[derive(Clone, Default)]
struct NameLayer {
    module_scopes: NameMap<String, Scope>,
    index: NameIndex,
    globals: NameMap<String, GlobalInfo>,
    by_abs: HashMap<u32, String>,
    member_bases: NameSet<String>,
    surface_decls: NameMap<String, Decl>,
}

/// [`NameLayer`]'s tables, as the layer index numbers them.
const SCOPES: usize = 0;
const NAMES: usize = 1;
const GLOBALS: usize = 2;
const BY_ABS: usize = 3;
const MEMBER_BASES: usize = 4;
const SURFACE: usize = 5;

impl Layer for NameLayer {
    const TABLES: usize = 6;

    fn keys(&self, table: usize, out: &mut dyn FnMut(u64)) {
        match table {
            SCOPES => self.module_scopes.keys().for_each(|k| out(index_hash(k.as_str()))),
            NAMES => self.index.by_name.keys().for_each(|k| out(index_hash(k.as_str()))),
            GLOBALS => self.globals.keys().for_each(|k| out(index_hash(k.as_str()))),
            BY_ABS => self.by_abs.keys().for_each(|k| out(index_hash(k))),
            MEMBER_BASES => self.member_bases.iter().for_each(|k| out(index_hash(k.as_str()))),
            SURFACE => self.surface_decls.keys().for_each(|k| out(index_hash(k.as_str()))),
            _ => unreachable!("NameLayer has {} tables", Self::TABLES),
        }
    }
}

impl NameLayer {
    fn is_empty(&self) -> bool {
        self.module_scopes.is_empty()
            && self.index.by_name.is_empty()
            && self.globals.is_empty()
            && self.by_abs.is_empty()
            && self.member_bases.is_empty()
            && self.surface_decls.is_empty()
    }
}

/// Committed ordinary declarations and the indexes that make them nameable.
///
/// These tables are one invariant, not four independent caches: a global is
/// visible only when its ambiguity entry, Ψ coordinate, member fast-path and
/// restatable surface signature have landed together. Keeping the fields
/// private makes [`Names::commit_global`] the only way to create that state.
#[derive(Clone)]
pub(crate) struct Names {
    scope: Scope,
    tables: Layered<NameLayer>,
    /// The common prelude's import closure as [`common_reaches`] walks it,
    /// made at the first asking. It is a function of the module scopes, so
    /// [`Names::enter_scope`], their one writer, drops it when it writes one;
    /// a snapshot carries the closure of the tables it carries.
    common: std::sync::OnceLock<Rc<CommonClosure>>,
}

/// The walk of the common prelude's import closure, kept
/// ([`Names::common`]): which modules it pops, in order, and for each module
/// some popped module imports, how many had been popped when it was first
/// met. That is everything [`common_reaches`] reads off the walk, the names
/// it notes included.
struct CommonClosure {
    id: u64,
    popped: Vec<String>,
    met_after: NameMap<String, usize>,
}

impl CommonClosure {
    /// The walk [`common_reaches`] did per asking, done once, to its end.
    fn walk(names: &Names) -> CommonClosure {
        static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
        let mut popped: Vec<String> = Vec::new();
        let mut met_after: NameMap<String, usize> = NameMap::default();
        let mut seen: NameSet<&str> = NameSet::default();
        seen.insert(COMMON_MODULE);
        let mut stack: Vec<&str> = vec![COMMON_MODULE];
        while let Some(m) = stack.pop() {
            popped.push(m.to_string());
            let Some(s) = names.tables.find(SCOPES, m, |layer| layer.module_scopes.get(m)) else { continue };
            for i in &s.imports {
                // The root is never met: asked for, it is the answer only if
                // a module of the closure imports it.
                if i.module == COMMON_MODULE {
                    met_after.entry(i.module.clone()).or_insert(popped.len());
                }
                if seen.insert(&i.module) {
                    met_after.entry(i.module.clone()).or_insert(popped.len());
                    stack.push(&i.module);
                }
            }
        }
        CommonClosure { id: NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed), popped, met_after }
    }

    /// Note the first `upto` modules of the walk in the record, as the walk
    /// would have: once per record, since a noted name stays noted.
    fn note_walk(&self, upto: usize) {
        QUERIED.with(|q| {
            let mut q = q.borrow_mut();
            let Some(set) = q.as_mut() else { return };
            let record = RECORD.with(|r| r.get());
            let done = match WALK_NOTED.with(|n| n.get()) {
                (r, id, done) if r == record && id == self.id => done,
                _ => 0,
            };
            for m in self.popped.iter().take(upto).skip(done) {
                let last = last_segment(m);
                if !set.contains(last) {
                    set.insert(last.to_string());
                }
            }
            WALK_NOTED.with(|n| n.set((record, self.id, done.max(upto))));
        });
    }
}

/// A callable global's Ψ coordinate and surface parameter metadata.
///
/// Functions and theorems are both referenced as `u^δ`; their Ψ binding says
/// whether a body is transparent, while this registry supplies only the
/// coordinate and the surface calling convention.
#[derive(Clone)]
pub(crate) struct GlobalInfo {
    pub(crate) abs: u32,
    pub(crate) params: Rc<Vec<ParamMeta>>,
}

/// Everything the name registry installs for one ordinary declaration.
#[derive(Clone)]
pub(crate) struct GlobalRegistration {
    pub(crate) name: String,
    pub(crate) key: String,
    pub(crate) params: Rc<Vec<ParamMeta>>,
    pub(crate) member_base: Option<String>,
    pub(crate) surface: Decl,
}

/// The result of resolving one written name against one scope.
pub(crate) enum NameRes {
    /// The module the name resolves to. The table lookup is
    /// `qkey(module, base)`.
    Found(String),
    /// Declared in two or more visible modules and not disambiguated: an
    /// error at the *use*, listing origins.
    Ambiguous(Vec<String>),
    /// Nothing visible declares it.
    NotFound,
    /// Written `m::n` where `m` is neither a visible module nor a visible
    /// type: the diagnostic wants to say which half is wrong.
    NoSuchQualifier(String),
    /// A name the surface does not have, with the sentence that says so: a
    /// generated name written in user source, or an access path naming no
    /// declaration (`access.rs`,
    /// `docs/repr-access-spellings-design.md` §6). Never produced by
    /// [`resolve`] — the elaborator decides it before consulting the tables,
    /// because the name may well *be* in them.
    Restricted(String),
}

/// The key every name table uses: `module::name`. Deliberately the same
/// string the surface writes for a qualified reference, so a table dump and a
/// diagnostic read alike.
///
/// Built by hand, at its final size: `format!` goes through the formatting
/// machinery and grows the string as it writes, and every keyed lookup
/// builds one of these.
pub(crate) fn qkey(module: &str, name: &str) -> String {
    let mut key = String::with_capacity(module.len() + 2 + name.len());
    key.push_str(module);
    key.push_str("::");
    key.push_str(name);
    key
}

/// Split a written reference into its qualifier and base name. `None` for an
/// unqualified name.
///
/// The split is at the **first** `::`, and that is the whole reading of a
/// three-segment name: module names are single-segment, so `int::Le::Decide`
/// is the module `int` and the declared name `Le::Decide` — which is exactly
/// how a member of a type's namespace was already keyed
/// (`Elaborator::key_of_declared_kinds`). The lexer joins a chain as of
/// 2026-08-17 (`docs/instance-resolved-key-design.md` §5); nothing here had to
/// move for it.
///
/// A byte scan, not `split_once("::")`: a two-byte pattern builds a
/// `StrSearcher` (the two-way algorithm's preprocessing) per call, which
/// costs more than reading a name of this length does, and resolution asks
/// this of every name it keys.
pub(crate) fn split_qual(name: &str) -> Option<(&str, &str)> {
    let at = name.as_bytes().windows(2).position(|w| w == b"::")?;
    Some((&name[..at], &name[at + 2..]))
}

impl NameIndex {
    pub fn insert(&mut self, module: &str, name: &str, kind: NameKind) {
        self.by_name
            .entry(name.to_string())
            .or_default()
            .push(NameEntry {
                module: module.to_string(),
                origin: module.to_string(),
                kind,
            });
    }

    pub fn entries(&self, name: &str) -> &[NameEntry] {
        self.by_name.get(name).map(|v| v.as_slice()).unwrap_or(&[])
    }
}

impl Names {
    pub(crate) fn new(module: impl Into<String>) -> Self {
        Names {
            scope: Scope::new(module),
            tables: Layered::default(),
            common: std::sync::OnceLock::new(),
        }
    }

    pub(crate) fn scope(&self) -> &Scope {
        &self.scope
    }

    pub(crate) fn module(&self) -> &str {
        &self.scope.module
    }

    pub(crate) fn module_scope(&self, module: &str) -> Option<&Scope> {
        note(module);
        self.tables.find(SCOPES, module, |layer| layer.module_scopes.get(module))
    }

    pub(crate) fn has_module(&self, module: &str) -> bool {
        self.module_scope(module).is_some()
    }

    /// Is `module` this file's own, or in its import closure: imported, or
    /// imported by a module it reaches? What decides whether a declaration
    /// the file never names can still be cited on its behalf, as an evidence
    /// rule the search found is (`Elaborator::resolve_declared_kinds`).
    pub(crate) fn reaches(&self, module: &str) -> bool {
        if self.scope.module == module || self.scope.imports_module(module) {
            return true;
        }
        let mut seen: Vec<&str> = self.scope.imports.iter().map(|i| i.module.as_str()).collect();
        let mut stack = seen.clone();
        while let Some(m) = stack.pop() {
            let Some(s) = self.module_scope(m) else { continue };
            for i in &s.imports {
                if i.module == module {
                    return true;
                }
                if !seen.contains(&i.module.as_str()) {
                    seen.push(&i.module);
                    stack.push(&i.module);
                }
            }
        }
        false
    }

    pub(crate) fn enter_scope(&mut self, scope: Scope) {
        // Re-entering the same module is an additive source chunk (a REPL and
        // many tests rely on this). Keep one delta for all of its chunks;
        // otherwise lookup depth would grow with declarations submitted one
        // at a time rather than with modules in the import closure.
        if scope.module != self.scope.module {
            self.seal_current();
        }
        if self.module_scope(&scope.module) != Some(&scope) {
            self.tables.current_mut()
                .module_scopes
                .insert(scope.module.clone(), scope.clone());
            self.common = std::sync::OnceLock::new();
        }
        // Publish aliases only in the visibility index: global coordinates,
        // nominal tags, signatures and proof provenance stay at their origin.
        for import in &scope.imports {
            for name in &import.exported {
                let entries: Vec<_> = self.entries(name)
                    .filter(|e| e.module == import.module).cloned().collect();
                for mut entry in entries {
                    if self.entries(name).any(|e| e.module == scope.module
                        && e.origin == entry.origin && e.kind == entry.kind) { continue; }
                    entry.module = scope.module.clone();
                    self.tables.current_mut().index.by_name
                        .entry(name.clone()).or_default().push(entry);
                }
            }
        }
        self.scope = scope;
    }

    /// Freeze the current module delta and start an empty suffix layer without
    /// copying any declaration-sized table.
    pub(crate) fn semantic_snapshot(&self) -> Self {
        let mut names = self.clone();
        names.seal_current();
        names
    }

    fn seal_current(&mut self) {
        if self.tables.current().is_empty() {
            return;
        }
        self.tables.seal_current();
    }

    fn entries<'a>(&'a self, name: &'a str) -> impl Iterator<Item = &'a NameEntry> + 'a {
        note(name);
        self.tables
            .candidates(NAMES, name)
            .flat_map(move |layer| layer.index.entries(name))
    }

    /// Is `name` visible in `scope` only through the import of `via` (and not
    /// declared by the module itself, nor reached by any other import)?
    pub(crate) fn seen_only_through(&self, scope: Option<&Scope>, name: &str, via: &str) -> bool {
        let scope = scope.unwrap_or(&self.scope);
        let mut seen = false;
        for e in self.entries(name) {
            if e.module == scope.module || e.module == PRELUDE_MODULE {
                return false;
            }
            if scope.imports_module(&e.module) {
                if e.module != via {
                    return false;
                }
                seen = true;
            }
        }
        seen
    }

    pub(crate) fn declares(&self, module: &str, name: &str) -> bool {
        self.entries(name).any(|e| e.module == module)
    }

    /// Original owner of a public name, including a transitive reexport.
    pub(crate) fn origin(&self, module: &str, name: &str) -> Option<&str> {
        note(name);
        self.tables.find(NAMES, name, |layer| layer.index.entries(name).iter()
            .find(|e| e.module == module).map(|e| e.origin.as_str()))
    }

    /// Replay must validate aliases against the already accepted dependency world.
    pub(crate) fn valid_exports(&self, scope: &Scope) -> bool {
        let mut exported = HashMap::new();
        for import in &scope.imports {
            for name in &import.exported {
                if import.module == scope.module { return false; }
                let Some(origin) = self.origin(&import.module, name) else { return false; };
                if let Some(previous) = exported.insert(name, origin)
                    && previous != origin { return false; }
                if let Some(previous) = self.origin(&scope.module, name)
                    && previous != origin { return false; }
            }
        }
        true
    }

    /// Does *any* module, visible from the current scope or not, declare
    /// `name` with one of `kinds`? The scope-free question a route asks before
    /// paying for evidence it could only use if some such declaration exists.
    pub(crate) fn declares_any_as(&self, name: &str, kinds: &[NameKind]) -> bool {
        self.entries(name).any(|e| kinds.contains(&e.kind))
    }

    pub(crate) fn declares_as(&self, module: &str, name: &str, kinds: &[NameKind]) -> bool {
        self.entries(name)
            .any(|e| e.module == module && kinds.contains(&e.kind))
    }

    /// Declared *by* `module`, not merely visible through it: a reexported
    /// alias is not the module's own declaration, so a facade that also
    /// declares the name gets the listed-collision diagnostic, not "duplicate".
    pub(crate) fn declares_own(&self, module: &str, name: &str, kinds: &[NameKind]) -> bool {
        self.entries(name)
            .any(|e| e.module == module && e.origin == module && kinds.contains(&e.kind))
    }

    pub(crate) fn visible_entries_are(
        &self,
        scope: Option<&Scope>,
        name: &str,
        kinds: &[NameKind],
    ) -> bool {
        let scope = scope.unwrap_or(&self.scope);
        self.entries(name).all(|e| {
            let visible = e.module == scope.module
                || scope.imports_module(&e.module)
                || e.module == PRELUDE_MODULE;
            !visible || kinds.contains(&e.kind)
        })
    }

    pub(crate) fn insert_current(&mut self, name: &str, kind: NameKind) {
        self.tables.current_mut()
            .index
            .insert(&self.scope.module, name, kind);
    }

    pub(crate) fn resolve_kinds(
        &self,
        scope: Option<&Scope>,
        name: &str,
        kinds: &[NameKind],
        is_ctor_of: impl Fn(&str, &str, &str) -> bool,
    ) -> NameRes {
        let scope = scope.unwrap_or(&self.scope);
        resolve_kinds(self, scope, name, kinds, is_ctor_of)
    }

    /// Every name `wanted` accepts, with its entries as `(module, origin,
    /// kind)`, sorted and deduplicated: what a lookup of that name could see
    /// (`NameWorld::observations`).
    pub(crate) fn observe(
        &self,
        wanted: &dyn Fn(&str) -> bool,
    ) -> std::collections::BTreeMap<String, Vec<(String, String, u8)>> {
        let mut out: std::collections::BTreeMap<String, Vec<(String, String, u8)>> = Default::default();
        for layer in self.tables.layers() {
            for (name, entries) in &layer.index.by_name {
                if !wanted(name) {
                    continue;
                }
                let seen = out.entry(name.clone()).or_default();
                for e in entries {
                    let kind = match e.kind {
                        NameKind::Global => 0,
                        NameKind::Inductive => 1,
                        NameKind::Ctor => 2,
                        NameKind::Meta => 3,
                    };
                    seen.push((e.module.clone(), e.origin.clone(), kind));
                }
            }
        }
        for entries in out.values_mut() {
            entries.sort();
            entries.dedup();
        }
        out
    }

    pub(crate) fn global(&self, key: &str) -> Option<&GlobalInfo> {
        note(key);
        self.tables.find(GLOBALS, key, |layer| layer.globals.get(key))
    }

    pub(crate) fn global_name_at(&self, abs: u32) -> Option<&str> {
        self.tables.find(BY_ABS, &abs, |layer| layer.by_abs.get(&abs).map(String::as_str))
    }

    pub(crate) fn params_at(&self, abs: u32) -> Option<Rc<Vec<ParamMeta>>> {
        let key = self.global_name_at(abs)?;
        Some(Rc::clone(&self.global(key)?.params))
    }

    pub(crate) fn has_member_base(&self, name: &str) -> bool {
        note(name);
        self.tables
            .find(MEMBER_BASES, name, |layer| layer.member_bases.contains(name).then_some(()))
            .is_some()
    }

    pub(crate) fn surface_decl(&self, name: &str) -> Option<&Decl> {
        note(name);
        self.tables.find(SURFACE, name, |layer| layer.surface_decls.get(name))
    }

    /// The surface declaration of the global `module`'s `name`, read off the
    /// layer that registered it (so a same-named declaration of another
    /// module is never consulted).
    pub(crate) fn surface_decl_in(&self, module: &str, name: &str) -> Option<&Decl> {
        self.registering_layer(module, name)
            .and_then(|layer| layer.surface_decls.get(name))
    }

    /// The layer that registered the global `module`'s `name`.
    fn registering_layer(&self, module: &str, name: &str) -> Option<&NameLayer> {
        let key = qkey(module, name);
        self.tables.find(GLOBALS, key.as_str(), |layer| layer.globals.contains_key(&key).then_some(layer))
    }

    /// Is the global `module`'s `name` a `def` used as a value: a
    /// [`Decl::value`] whose parameters, if any, are all implicit
    /// (docs/value-definitions-design.md §2.3)? Read off the layer that
    /// registered it, so a same-named declaration of another module is never
    /// consulted.
    pub(crate) fn is_value(&self, module: &str, name: &str) -> bool {
        self.registering_layer(module, name)
            .and_then(|layer| layer.surface_decls.get(name))
            .is_some_and(|d| d.value && d.params.iter().all(|p| p.implicit))
    }

    pub(crate) fn commit_global(&mut self, abs: u32, reg: GlobalRegistration) {
        let GlobalRegistration {
            name,
            key,
            params,
            member_base,
            surface,
        } = reg;
        debug_assert!(self.global(&key).is_none());
        debug_assert!(self.global_name_at(abs).is_none());
        let current = self.tables.current_mut();
        current
            .index
            .insert(&self.scope.module, &name, NameKind::Global);
        current.by_abs.insert(abs, key.clone());
        current.globals.insert(key, GlobalInfo { abs, params });
        if let Some(base) = member_base {
            current.member_bases.insert(base);
        }
        current.surface_decls.insert(name, surface);
    }
}

/// The prelude's module name. Implicitly imported by every module and by
/// nothing else special: it is an ordinary module that happens to be
/// elaborated first (docs/modules-design.md §3.2).
pub(crate) const PRELUDE_MODULE: &str = "prelude";
/// The library's common prelude (`lib/std/common.hthr`): a facade that every
/// module later than it in a run's order imports implicitly, by name only
/// (its `export` lists). The modules it exports from come before it, so they
/// never see it (issues/std-prelude-facade.md).
pub(crate) const COMMON_MODULE: &str = "common";

/// The module name a bare `check_source`/`elab_source` call elaborates into —
/// the degenerate one-module program every test and every pre-modules caller
/// was already writing.
pub(crate) const DEFAULT_MODULE: &str = "main";

/// Resolve one written name against one scope, by the §4 regime, with the
/// candidate set optionally restricted by declaration kind.
///
/// Every kind — the unfiltered candidate set.
pub(crate) const ANY_KIND: &[NameKind] = &[];

/// `is_ctor_of` answers "does the inductive `t` (already resolved) have a
/// constructor `c`?", which is what makes `Option::None` a *type*-qualified
/// constructor rather than a module path. It is a callback because the
/// inductive table lives on the elaborator and this function must stay
/// testable on its own.
///
/// `kinds` restricts the candidate set; [`ANY_KIND`] is the unfiltered
/// regime every caller but one uses.
///
/// The one caller is *type position* (`kinds = [Inductive]`), and the licence
/// is impossibility rather than preference: a constructor is not a type, so a
/// `TyKind::Named` that resolved to one could never have elaborated. Dropping
/// it from the candidate set is therefore a **shrink** and not a
/// reinterpretation — the invariant `docs/modules-design.md` §8 states for the
/// expected-type route, applied to the syntactic position instead of the
/// checked type.
///
/// Expression position deliberately does **not** get this treatment, and the
/// asymmetry is the whole point: there a type name and a constructor are
/// *both* legal readings, so shrinking would be choosing.
fn resolve_kinds(
    names: &Names,
    scope: &Scope,
    name: &str,
    kinds: &[NameKind],
    is_ctor_of: impl Fn(&str, &str, &str) -> bool,
) -> NameRes {
    let Some((qual, base)) = split_qual(name) else {
        return resolve_bare_kinds(names, scope, name, kinds);
    };
    // `nat::Nat::le_add` — a module path. Visibility is required: qualification
    // names which visible module you meant, it does not reach into a module
    // this file never imported.
    let visible_module = qual == scope.module
        || scope.imports_module(qual)
        || qual == PRELUDE_MODULE
        || common_reaches(names, scope, qual);
    if visible_module && names.declares(qual, base) {
        // ... unless a visible module also declares the whole string as a
        // member — `f::pos` of a function `f` named like the module `f`
        // (issues/function-owned-members.md). A function shares a module's
        // lower-case spelling, so the module path winning here would let the
        // module growing a `pos` silently reinterpret a member reference. Two
        // readings are an ambiguity, as everywhere else; the member's own
        // module comes first so the advice's `m::f::pos` reaches it.
        if let NameRes::Found(m) = resolve_bare_kinds(names, scope, name, kinds) {
            return NameRes::Ambiguous(vec![m, qual.to_string()]);
        }
        return NameRes::Found(names.origin(qual, base).unwrap().to_string());
    }
    // `Option::None` — a constructor qualified by its *type*. The type name is
    // itself resolved by the same regime, so `Option` may come from an import.
    if let NameRes::Found(m) = resolve_bare(names, scope, qual)
        && is_ctor_of(&m, qual, base)
    {
        return NameRes::Found(m);
    }
    // `List::nth` — a *member* of a type's namespace
    // (issues/type-owned-members-receiver-slice.md). The whole written string
    // is the declared name, so the §4 regime applies to it unchanged: locals
    // beat unlisted imports, and two visible modules attaching the same member
    // to the same type are ambiguous at use with both origins named. Tried
    // after the module-path and constructor readings, so nothing that resolved
    // before can be reinterpreted by one.
    match resolve_bare_kinds(names, scope, name, kinds) {
        NameRes::Found(m) => return NameRes::Found(m),
        NameRes::Ambiguous(origins) => return NameRes::Ambiguous(origins),
        NameRes::NotFound | NameRes::NoSuchQualifier(_) | NameRes::Restricted(_) => {}
    }
    // `List::map` where `List` is visible only through a facade's export
    // (`common`'s `export list::{List}`): exporting a type exports the
    // members its own module declares on it, as it exports its constructors
    // (issues/std-prelude-facade.md). Read here, at the lookup, and not
    // materialized at the export, so a member added later is reached without
    // the facade being elaborated again, and the lookup records the member's
    // name as every other lookup does.
    if let NameRes::Found(origin) = resolve_bare(names, scope, qual)
        && names.entries(qual).any(|e| e.origin == origin && e.module != origin && scope.imports_module(&e.module))
        && names.entries(name).any(|e| e.module == origin && e.origin == origin && (kinds.is_empty() || kinds.contains(&e.kind)))
    {
        return NameRes::Found(origin);
    }
    if visible_module {
        return NameRes::NotFound;
    }
    NameRes::NoSuchQualifier(qual.to_string())
}

/// Is `module` in the common prelude's closure, in a scope that imports the
/// prelude? Such a module is visible **qualified only** there: `list::x`
/// resolves, a bare `x` does not unless the prelude exports it. That is what
/// the elaborator's own spellings need — an instance's global
/// (`list::List::CollectionLiteral`), a designated operation
/// (`bool::Bool::and`) — and it keeps the core's lemma names out of the bare
/// namespace (issues/std-prelude-facade.md,
/// issues/feature-implicit-module-dependencies.md). Read off the prelude's
/// own scope, so nothing about it is stored in the importer's.
///
/// Asked of every qualified name whose qualifier is not a module the scope
/// imports, which is every `Type::member`, and for those the answer is no
/// only after the whole closure has been walked. So the walk is done once
/// ([`CommonClosure`]) and an asking reads it: whether `module` was met, and
/// how far the walk had got, which is how many of its modules the asking
/// notes ([`note`], the early cutoff's account).
fn common_reaches(names: &Names, scope: &Scope, module: &str) -> bool {
    if scope.module == COMMON_MODULE || !scope.imports_module(COMMON_MODULE) {
        return false;
    }
    let closure = names.common.get_or_init(|| Rc::new(CommonClosure::walk(names)));
    #[cfg(debug_assertions)]
    if crate::readback::sampled() {
        let (found, popped) = common_walk_per_asking(names, module);
        let kept = closure.met_after.get(module).copied();
        assert!(
            found == kept.is_some() && popped.iter().eq(closure.popped.iter().take(kept.unwrap_or(usize::MAX))),
            "the kept walk of the prelude's closure is not the walk for `{module}`"
        );
    }
    match closure.met_after.get(module) {
        Some(&popped) => {
            closure.note_walk(popped);
            true
        }
        None => {
            closure.note_walk(closure.popped.len());
            false
        }
    }
}

/// [`common_reaches`]' walk as it was done per asking, for the debug check
/// and the tests: the answer, and the modules it popped, each of which it
/// noted.
#[cfg(any(debug_assertions, test))]
fn common_walk_per_asking<'a>(names: &'a Names, module: &str) -> (bool, Vec<&'a str>) {
    let mut popped: Vec<&str> = Vec::new();
    let mut seen: Vec<&str> = vec![COMMON_MODULE];
    let mut stack: Vec<&str> = vec![COMMON_MODULE];
    while let Some(m) = stack.pop() {
        popped.push(m);
        let Some(s) = names.tables.find(SCOPES, m, |layer| layer.module_scopes.get(m)) else { continue };
        for i in &s.imports {
            if i.module == module {
                return (true, popped);
            }
            if !seen.contains(&i.module.as_str()) {
                seen.push(&i.module);
                stack.push(&i.module);
            }
        }
    }
    (false, popped)
}

fn resolve_bare(names: &Names, scope: &Scope, name: &str) -> NameRes {
    resolve_bare_kinds(names, scope, name, ANY_KIND)
}

fn resolve_bare_kinds(names: &Names, scope: &Scope, name: &str, kinds: &[NameKind]) -> NameRes {
    // The filter is applied at each use rather than collected once: this
    // function is on the hot path of every name in every file, and an
    // allocation per resolution is not worth saving three predicate calls.
    // `kinds.is_empty()` is the unfiltered regime, so the closure costs one
    // branch when nobody is filtering.
    let of_kind = |e: &NameEntry| kinds.is_empty() || kinds.contains(&e.kind);
    if !names.entries(name).any(of_kind) {
        return NameRes::NotFound;
    }
    // A listed name is a standing disambiguation and wins outright. Two
    // imports listing the same name is an error at the import (see
    // `Elaborator::set_scope`), so at most one survives here.
    let mut listed: Vec<(String, String)> = scope
        .imports
        .iter()
        .filter(|i| {
            i.listed.iter().any(|n| n == name)
                && names
                    .entries(name)
                    .any(|e| e.module == i.module && of_kind(e))
        })
        .map(|i| (names.origin(&i.module, name).unwrap().to_string(), i.module.clone()))
        .collect();
    listed.sort_by(|a, b| a.0.cmp(&b.0));
    listed.dedup_by(|a, b| a.0 == b.0);
    if let Some((origin, _)) = listed.first() {
        if listed.len() > 1 {
            return NameRes::Ambiguous(listed.into_iter().map(|(_, visible)| visible).collect());
        }
        return NameRes::Found(origin.clone());
    }
    // Locals beat unlisted imports: the file you are reading beats the file
    // you are not. This is the one precedence in the system.
    if names
        .entries(name)
        .any(|e| e.module == scope.module && of_kind(e))
    {
        return NameRes::Found(names.origin(&scope.module, name).unwrap().to_string());
    }
    let mut hits: Vec<(String, String)> = Vec::new();
    for e in names.entries(name).filter(|e| of_kind(e)) {
        let visible = scope.imports_module(&e.module) || e.module == PRELUDE_MODULE;
        if visible && !hits.iter().any(|(origin, _)| origin == &e.origin) {
            hits.push((e.origin.clone(), e.module.clone()));
        }
    }
    match hits.len() {
        0 => NameRes::NotFound,
        1 => NameRes::Found(hits.remove(0).0),
        _ => NameRes::Ambiguous(hits.into_iter().map(|(_, visible)| visible).collect()),
    }
}

/// The ambiguity message: both origins named, and the fix spelled out.
pub(crate) fn ambiguity_msg(name: &str, origins: &[String]) -> String {
    let list = origins
        .iter()
        .map(|m| format!("`{m}`"))
        .collect::<Vec<_>>()
        .join(" and ");
    let first = origins.first().map(String::as_str).unwrap_or("m");
    format!(
        "`{name}` is ambiguous: it is declared in {list} — qualify it (`{first}::{name}`) \
         or list it in the import (`import {first}::{{{name}}};`)"
    )
}

/// Where a name resolution went wrong, as a sentence. Used by every site that
/// only wanted an `Option` and has to report the miss: an ambiguous name must
/// not be reported as an unknown one.
pub(crate) fn miss_msg(res: &NameRes, name: &str, fallback: String) -> Option<String> {
    match res {
        NameRes::Ambiguous(origins) => Some(ambiguity_msg(name, origins)),
        NameRes::NoSuchQualifier(q) => Some(format!(
            "`{name}` is qualified by `{q}`, which is neither an imported module nor a \
             type or function in scope here with a member by that name{}",
            // The one name the parser writes on the reader's behalf: `∑` and
            // `∏` desugar to it, so say where it comes from.
            if name == "MonoidRel::range" {
                ". A `∑`/`∏` big operator is a call to `MonoidRel::range`: write \
                 `import big_operator;`"
            } else {
                ""
            }
        )),
        NameRes::Restricted(msg) => Some(msg.clone()),
        NameRes::NotFound => Some(fallback),
        NameRes::Found(_) => None,
    }
}

#[cfg(test)]
mod layered_tests {
    use super::*;

    /// `split_qual` is `split_once("::")`, written as a scan: the first `::`
    /// splits, whatever is around it.
    #[test]
    fn a_name_splits_at_its_first_double_colon() {
        for name in [
            "", ":", "::", ":::", "a", "a:", "a:b", "a::b", "a::b::c", "::a", "a::", "a:::b",
            "int::Le::Decide", "naïve::é", "é::naïve::x", "x#1::y", "a: :b",
        ] {
            assert_eq!(split_qual(name), name.split_once("::"), "{name:?}");
        }
    }

    /// `last_segment` is `rsplit("::").next()`, written as a scan: what
    /// follows the last `::`.
    #[test]
    fn a_names_last_segment_follows_its_last_double_colon() {
        for name in [
            "", ":", "::", ":::", "::::", "a", "a:", "a:b", "a::b", "a::b::c", "::a", "a::", "a:::b",
            "int::Le::Decide", "naïve::é", "é::naïve::x", "x#1::y", "a: :b", "a::b:", "a::b:c",
        ] {
            assert_eq!(Some(last_segment(name)), name.rsplit("::").next(), "{name:?}");
        }
    }

    /// The record is what was looked up, by last segment, each once and in
    /// order, whatever order the lookups came in.
    #[test]
    fn the_lookup_record_is_the_sorted_last_segments() {
        record_name_lookups();
        for name in ["list::List::map", "zeta", "nat::Nat", "map", "alpha::zeta", "Nat", "b::"] {
            note(name);
        }
        let noted: Vec<String> = take_name_lookups().expect("recording").into_iter().collect();
        assert_eq!(noted, ["", "Nat", "map", "zeta"]);
        note("unrecorded");
        assert_eq!(take_name_lookups(), None, "nothing records after the record is taken");
    }

    fn scope(module: &str, imports: &[&str]) -> Scope {
        Scope {
            module: module.to_string(),
            imports: imports
                .iter()
                .map(|m| ImportSpec { module: m.to_string(), listed: Vec::new(), exported: Vec::new() })
                .collect(),
        }
    }

    /// The prelude's closure is walked once and read at each asking: the
    /// answer and the names noted are the per-asking walk's, for a module in
    /// the closure, one outside it, one never entered and the root; a record
    /// started later is told again; and entering a scope makes a new walk.
    #[test]
    fn the_preludes_closure_is_walked_once_and_reads_as_the_walk() {
        let mut names = Names::new(DEFAULT_MODULE);
        // A diamond with a cycle back to the top, a module imported and never
        // entered, and one the prelude does not reach.
        names.enter_scope(scope("d", &["b", "ghost"]));
        names.enter_scope(scope("b", &["d"]));
        names.enter_scope(scope("c", &["d", "b"]));
        names.enter_scope(scope("apart", &["d"]));
        names.enter_scope(scope(COMMON_MODULE, &["b", "c"]));
        let user = scope("user", &[COMMON_MODULE]);
        names.enter_scope(user.clone());

        let asked = ["b", "c", "d", "ghost", "apart", "user", COMMON_MODULE, "Nat"];
        let noted = |names: &Names, module: &str| {
            record_name_lookups();
            let found = common_reaches(names, &user, module);
            (found, take_name_lookups().expect("recording"))
        };
        for module in asked {
            let (found, popped) = common_walk_per_asking(&names, module);
            let (kept, record) = noted(&names, module);
            assert_eq!(kept, found, "{module}");
            assert_eq!(record, popped.iter().map(|m| m.to_string()).collect(), "{module}");
            // The same record, asked twice, and then for the whole walk.
            record_name_lookups();
            assert_eq!(common_reaches(&names, &user, module), found);
            assert_eq!(common_reaches(&names, &user, module), found);
            assert!(!common_reaches(&names, &user, "Nat"));
            let whole = common_walk_per_asking(&names, "Nat").1;
            assert_eq!(take_name_lookups().expect("recording"), whole.iter().map(|m| m.to_string()).collect());
        }
        assert!(common_reaches(&names, &user, "d") && !common_reaches(&names, &user, "apart"));
        assert!(!common_reaches(&names, &scope("other", &[]), "d"), "a scope that does not import the prelude");

        // A snapshot keeps the walk of its own tables; the registry that
        // enters a scope walks again.
        let before = names.clone();
        names.enter_scope(scope("d", &["b", "ghost", "apart"]));
        names.enter_scope(user.clone());
        assert!(common_reaches(&names, &user, "apart"));
        assert!(!common_reaches(&before, &user, "apart"));
        assert_eq!(noted(&names, "apart").1, common_walk_per_asking(&names, "apart").1.iter().map(|m| m.to_string()).collect());
    }

    #[test]
    fn semantic_snapshot_seals_modules_and_suffix_mutates_only_an_empty_delta() {
        let mut names = Names::new(DEFAULT_MODULE);
        for i in 0..64 {
            let module = format!("m{i}");
            names.enter_scope(Scope::new(&module));
            names.insert_current("shared", NameKind::Global);
            names.insert_current(&format!("only_{i}"), NameKind::Global);
        }

        let image = names.semantic_snapshot();
        assert_eq!(image.tables.sealed_len(), 64);
        assert_eq!(image.tables.run_count(), 1);
        assert!(image.tables.current().is_empty());
        for i in 0..64 {
            assert!(image.declares(&format!("m{i}"), "shared"));
            assert!(image.declares(&format!("m{i}"), &format!("only_{i}")));
        }

        let mut suffix = image.clone();
        suffix.enter_scope(Scope::new("m63"));
        assert!(image.tables.shares_sealed_with(&suffix.tables));
        suffix.insert_current("suffix", NameKind::Global);
        assert!(image.tables.shares_sealed_with(&suffix.tables));
        assert!(image.tables.current().is_empty());
        assert_eq!(suffix.tables.current().index.entries("suffix").len(), 1);
        assert!(!image.declares(image.module(), "suffix"));
        assert!(suffix.declares(suffix.module(), "suffix"));
    }
}
