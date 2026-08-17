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
#[derive(Clone, Debug)]
pub(crate) struct ImportSpec {
    pub module: String,
    /// The `::{…}` list, if written. Empty for a plain `import m;`.
    pub listed: Vec<String>,
}

/// The visibility of the module currently being elaborated.
#[derive(Clone, Debug)]
pub(crate) struct Scope {
    pub module: String,
    pub imports: Vec<ImportSpec>,
}

impl Scope {
    pub fn new(module: impl Into<String>) -> Self {
        Scope { module: module.into(), imports: Vec::new() }
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
pub(crate) struct NameEntry {
    pub module: String,
    pub kind: NameKind,
}

/// Name → every declaration of it, across all modules elaborated so far.
///
/// The tables themselves stay keyed by the qualified string `module::name`
/// ([`qkey`]); this is the index that makes "which modules declare `sub`?" a
/// lookup rather than a scan, and it is the only place ambiguity is visible.
#[derive(Clone, Default)]
pub(crate) struct NameIndex {
    by_name: HashMap<String, Vec<NameEntry>>,
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
pub(crate) fn qkey(module: &str, name: &str) -> String {
    format!("{module}::{name}")
}

/// Split a written reference into its qualifier and base name. `None` for an
/// unqualified name. There is exactly one `::` at most: module names are
/// single-segment and the lexer joins only one pair.
pub(crate) fn split_qual(name: &str) -> Option<(&str, &str)> {
    name.split_once("::")
}

impl NameIndex {
    pub fn insert(&mut self, module: &str, name: &str, kind: NameKind) {
        self.by_name
            .entry(name.to_string())
            .or_default()
            .push(NameEntry { module: module.to_string(), kind });
    }

    pub fn entries(&self, name: &str) -> &[NameEntry] {
        self.by_name.get(name).map(|v| v.as_slice()).unwrap_or(&[])
    }

    /// Is `name` declared in `module`, as any kind?
    pub fn declares(&self, module: &str, name: &str) -> bool {
        self.entries(name).iter().any(|e| e.module == module)
    }

    /// Is `name` declared in `module` as one of `kinds`?
    pub fn declares_as(&self, module: &str, name: &str, kinds: &[NameKind]) -> bool {
        self.entries(name).iter().any(|e| e.module == module && kinds.contains(&e.kind))
    }
}

/// The prelude's module name. Implicitly imported by every module and by
/// nothing else special: it is an ordinary module that happens to be
/// elaborated first (docs/modules-design.md §3.2).
pub(crate) const PRELUDE_MODULE: &str = "prelude";

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
pub(crate) fn resolve_kinds(
    index: &NameIndex,
    scope: &Scope,
    name: &str,
    kinds: &[NameKind],
    is_ctor_of: impl Fn(&str, &str, &str) -> bool,
) -> NameRes {
    let Some((qual, base)) = split_qual(name) else {
        return resolve_bare_kinds(index, scope, name, kinds);
    };
    // `nat::le_add` — a module path. Visibility is required: qualification
    // names which visible module you meant, it does not reach into a module
    // this file never imported.
    let visible_module = qual == scope.module
        || scope.imports_module(qual)
        || qual == PRELUDE_MODULE;
    if visible_module && index.declares(qual, base) {
        return NameRes::Found(qual.to_string());
    }
    // `Option::None` — a constructor qualified by its *type*. The type name is
    // itself resolved by the same regime, so `Option` may come from an import.
    if let NameRes::Found(m) = resolve_bare(index, scope, qual)
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
    match resolve_bare_kinds(index, scope, name, kinds) {
        NameRes::Found(m) => return NameRes::Found(m),
        NameRes::Ambiguous(origins) => return NameRes::Ambiguous(origins),
        NameRes::NotFound | NameRes::NoSuchQualifier(_) | NameRes::Restricted(_) => {}
    }
    if visible_module {
        return NameRes::NotFound;
    }
    NameRes::NoSuchQualifier(qual.to_string())
}

fn resolve_bare(index: &NameIndex, scope: &Scope, name: &str) -> NameRes {
    resolve_bare_kinds(index, scope, name, ANY_KIND)
}

fn resolve_bare_kinds(
    index: &NameIndex,
    scope: &Scope,
    name: &str,
    kinds: &[NameKind],
) -> NameRes {
    // The filter is applied at each use rather than collected once: this
    // function is on the hot path of every name in every file, and an
    // allocation per resolution is not worth saving three predicate calls.
    // `kinds.is_empty()` is the unfiltered regime, so the closure costs one
    // branch when nobody is filtering.
    let of_kind = |e: &NameEntry| kinds.is_empty() || kinds.contains(&e.kind);
    let entries = index.entries(name);
    if !entries.iter().any(of_kind) {
        return NameRes::NotFound;
    }
    // A listed name is a standing disambiguation and wins outright. Two
    // imports listing the same name is an error at the import (see
    // `Elaborator::set_scope`), so at most one survives here.
    let listed: Vec<String> = scope
        .imports
        .iter()
        .filter(|i| {
            i.listed.iter().any(|n| n == name)
                && entries.iter().any(|e| e.module == i.module && of_kind(e))
        })
        .map(|i| i.module.clone())
        .collect();
    if let Some(m) = listed.first() {
        if listed.len() > 1 {
            return NameRes::Ambiguous(listed);
        }
        return NameRes::Found(m.clone());
    }
    // Locals beat unlisted imports: the file you are reading beats the file
    // you are not. This is the one precedence in the system.
    if entries.iter().any(|e| e.module == scope.module && of_kind(e)) {
        return NameRes::Found(scope.module.clone());
    }
    let mut hits: Vec<String> = Vec::new();
    for e in entries.iter().filter(|e| of_kind(e)) {
        let visible = scope.imports_module(&e.module) || e.module == PRELUDE_MODULE;
        if visible && !hits.contains(&e.module) {
            hits.push(e.module.clone());
        }
    }
    match hits.len() {
        0 => NameRes::NotFound,
        1 => NameRes::Found(hits.remove(0)),
        _ => NameRes::Ambiguous(hits),
    }
}

/// The ambiguity message: both origins named, and the fix spelled out.
pub(crate) fn ambiguity_msg(name: &str, origins: &[String]) -> String {
    let list = origins.iter().map(|m| format!("`{m}`")).collect::<Vec<_>>().join(" and ");
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
             type in scope here"
        )),
        NameRes::Restricted(msg) => Some(msg.clone()),
        NameRes::NotFound => Some(fallback),
        NameRes::Found(_) => None,
    }
}
