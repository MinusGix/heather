//! The import loader (docs/modules-design.md §3): from a root file, the
//! transitive closure of its imports, deduplicated and topologically ordered.
//!
//! One module is one file and its name is the file stem; there are no
//! compound paths, so resolving `import nat;` is a search over directories:
//! the importing file's own directory first, then each `-L <dir>`, then any
//! fallback directories supplied for a directory target. The walk is
//! depth-first with a path stack, which is what makes a cycle reportable *as*
//! a cycle rather than as a stack overflow.
//!
//! The loader does no elaboration and holds no elaborator: it returns the
//! modules in the order they must be fed to one. That is also why it parses
//! each file only to read its `import` items — the elaborator parses the
//! source again for real, and paying one extra parse per file keeps the two
//! from having to share a cache.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use heather_syntax::{parse_file, Item};

/// One module of the closure, ready to elaborate.
pub struct Module {
    pub name: String,
    pub path: PathBuf,
    pub src: String,
}

/// A failure of the *run*, not of a file's contents: an unreadable file, an
/// unresolvable import, a cycle. Every message names the paths it is about,
/// so there is nothing to carry beside it.
pub struct LoadError {
    pub msg: String,
}

impl LoadError {
    fn new(msg: impl Into<String>) -> Self {
        LoadError { msg: msg.into() }
    }

    fn at(msg: impl Into<String>, _path: &Path) -> Self {
        LoadError::new(msg)
    }
}

/// Load `root` and everything it imports, transitively.
///
/// The result is in **topological order**, dependencies first, with the root
/// last: exactly the order the elaborator's single accumulator needs, since an
/// `import m;` requires `m` to have already landed in it.
pub fn load(root: &Path, search: &[PathBuf]) -> Result<Vec<Module>, LoadError> {
    load_many(std::slice::from_ref(&root), search)
}

/// Load one root from an in-memory source buffer while reading its imports
/// from disk. Resident editor clients use this so diagnostics describe the
/// text the user can see, including changes that have not been saved yet.
pub fn load_overlay(
    root: &Path,
    search: &[PathBuf],
    source: &str,
) -> Result<Vec<Module>, LoadError> {
    let root = root
        .canonicalize()
        .map_err(|e| LoadError::at(format!("cannot read `{}`: {e}", root.display()), root))?;
    let mut overlays = HashMap::new();
    overlays.insert(root.clone(), source.to_string());
    load_many_inner(&[root.as_path()], search, &[], &overlays)
}

/// Load several roots as one import closure.
///
/// This is the directory-checking form's important semantic detail: a module
/// imported by two files is elaborated once, so declarations and warnings are
/// neither duplicated. Roots retain their supplied order, modulo dependencies
/// appearing before the root that needs them.
pub fn load_many(roots: &[&Path], search: &[PathBuf]) -> Result<Vec<Module>, LoadError> {
    load_many_with_fallback(roots, search, &[])
}

/// Load several roots, consulting `fallback` only when neither the importing
/// file's directory nor an explicit search directory contains the module.
/// Directory targets use this for implementation modules below a facade:
/// their descendants must be discoverable without competing with public
/// modules in the target's own directory.
pub fn load_many_with_fallback(
    roots: &[&Path],
    search: &[PathBuf],
    fallback: &[PathBuf],
) -> Result<Vec<Module>, LoadError> {
    load_many_inner(roots, search, fallback, &HashMap::new())
}

fn load_many_inner(
    roots: &[&Path],
    search: &[PathBuf],
    fallback: &[PathBuf],
    overlays: &HashMap<PathBuf, String>,
) -> Result<Vec<Module>, LoadError> {
    let mut w = Walk {
        search,
        search_fallback: fallback,
        overlays,
        done: HashMap::new(),
        stack: Vec::new(),
        out: Vec::new(),
        by_name: HashMap::new(),
    };
    for root in roots {
        w.visit(root)?;
    }
    Ok(w.out)
}

struct Walk<'a> {
    search: &'a [PathBuf],
    search_fallback: &'a [PathBuf],
    /// Canonical path → editor buffer. At present the public editor API
    /// overlays one root; keeping it a map makes recursive visits unambiguous.
    overlays: &'a HashMap<PathBuf, String>,
    /// Canonical path → module name. Dedup is by **path**, so a diamond costs
    /// one elaboration and two spellings of one file are one module.
    done: HashMap<PathBuf, String>,
    /// The DFS path, for the cycle report.
    stack: Vec<(PathBuf, String)>,
    out: Vec<Module>,
    /// Module name → the file that claimed it. Two files with one stem are an
    /// error: names are how imports refer to each other, so a duplicate makes
    /// every reference to it ambiguous in a way qualification cannot fix.
    by_name: HashMap<String, PathBuf>,
}

impl Walk<'_> {
    fn visit(&mut self, path: &Path) -> Result<(), LoadError> {
        let canon = path
            .canonicalize()
            .map_err(|e| LoadError::at(format!("cannot read `{}`: {e}", path.display()), path))?;
        if self.done.contains_key(&canon) {
            return Ok(());
        }
        if let Some(i) = self.stack.iter().position(|(p, _)| *p == canon) {
            let mut cycle: Vec<&str> =
                self.stack[i..].iter().map(|(_, n)| n.as_str()).collect();
            let head = cycle[0].to_string();
            cycle.push(&head);
            return Err(LoadError::at(
                format!("import cycle: {}", cycle.join(" -> ")),
                path,
            ));
        }
        let name = module_name(&canon)?;
        if let Some(other) = self.by_name.get(&name)
            && *other != canon
        {
            return Err(LoadError::at(
                format!(
                    "two files claim the module name `{name}`: `{}` and `{}` — a module \
                     is named by its file stem, so one of them has to be renamed",
                    other.display(),
                    canon.display()
                ),
                path,
            ));
        }
        let src = match self.overlays.get(&canon) {
            Some(src) => src.clone(),
            None => std::fs::read_to_string(&canon).map_err(|e| {
                LoadError::at(format!("cannot read `{}`: {e}", canon.display()), path)
            })?,
        };
        // A parse error is the elaborator's to report, with a snippet: here it
        // only means "no imports readable", and the module still gets fed on so
        // the real diagnostic comes out where it belongs.
        let imports: Vec<(String, PathBuf)> = match parse_file(&src) {
            Ok(file) => {
                let mut v = Vec::new();
                for item in &file.items {
                    let Item::Import(imp) = item else { continue };
                    if imp.module == heather_elab::PRELUDE_MODULE {
                        continue;
                    }
                    v.push((imp.module.clone(), self.resolve(&imp.module, &canon)?));
                }
                v
            }
            Err(_) => Vec::new(),
        };
        self.stack.push((canon.clone(), name.clone()));
        for (_, dep) in &imports {
            self.visit(dep)?;
        }
        self.stack.pop();
        self.by_name.insert(name.clone(), canon.clone());
        self.done.insert(canon.clone(), name.clone());
        self.out.push(Module { name, path: canon, src });
        Ok(())
    }

    /// `import m;` from `from`: the importing file's directory, then the `-L`
    /// dirs, then the directory target's descendant fallback dirs. A fallback
    /// tier is consulted only after a miss in the primary tier. Within either
    /// tier, a module found in **two** dirs is an error rather than a
    /// precedence, since which one a build got would otherwise depend on
    /// directory enumeration or flag order.
    fn resolve(&self, module: &str, from: &Path) -> Result<PathBuf, LoadError> {
        let file = format!("{module}.hthr");
        if let Some(dir) = from.parent() {
            let p = dir.join(&file);
            if p.is_file() {
                return Ok(p);
            }
        }
        let mut hits: Vec<PathBuf> =
            self.search.iter().map(|d| d.join(&file)).filter(|p| p.is_file()).collect();
        if hits.is_empty() {
            hits = self
                .search_fallback
                .iter()
                .map(|d| d.join(&file))
                .filter(|p| p.is_file())
                .collect();
        }
        match hits.len() {
            0 => Err(LoadError::at(
                format!(
                    "cannot find module `{module}`: no `{file}` beside `{}`{}",
                    from.display(),
                    if self.search.is_empty() && self.search_fallback.is_empty() {
                        " and no `-L` search directory was given".to_string()
                    } else {
                        format!(
                            " or in {}",
                            self.search
                                .iter()
                                .chain(self.search_fallback)
                                .map(|d| format!("`{}`", d.display()))
                                .collect::<Vec<_>>()
                                .join(", ")
                        )
                    }
                ),
                from,
            )),
            1 => Ok(hits.into_iter().next().expect("one hit")),
            _ => Err(LoadError::at(
                format!(
                    "module `{module}` is in two search directories ({}) — that is an \
                     error, not a precedence: remove one copy or drop one `-L`",
                    hits.iter().map(|p| format!("`{}`", p.display())).collect::<Vec<_>>().join(", ")
                ),
                from,
            )),
        }
    }
}

/// The module name of a file: its stem, which must be an identifier.
fn module_name(path: &Path) -> Result<String, LoadError> {
    let stem = path
        .file_stem()
        .and_then(|s| s.to_str())
        .ok_or_else(|| LoadError::new(format!("`{}` has no file name", path.display())))?;
    let ok = !stem.is_empty()
        && stem.chars().next().is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && stem.chars().all(|c| c.is_ascii_alphanumeric() || c == '_');
    if !ok {
        return Err(LoadError::at(
            format!(
                "`{}` cannot be a module: a module is named by its file stem, which \
                 must be an identifier",
                path.display()
            ),
            path,
        ));
    }
    Ok(stem.to_string())
}
