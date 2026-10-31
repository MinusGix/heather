//! The import loader (docs/modules-design.md §3): from a root file, the
//! transitive closure of its imports, deduplicated and topologically ordered.
//!
//! One module is one file and its name is the file stem; there are no
//! compound paths, so resolving `import nat;` is a search over directories:
//! the importing file's own directory first, then each `-L <dir>`, then the
//! directories below those search directories. The walk is
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

use heather_elab::LintProfile;
use heather_syntax::{parse_file, Item};

/// One module of the closure, ready to elaborate.
#[derive(Clone)]
pub struct Module {
    pub name: String,
    pub path: PathBuf,
    pub src: String,
}

impl Module {
    /// The lints this module is checked under: [`LintProfile::Stdlib`] for a
    /// file under `lib/std` (from the working directory), the default
    /// otherwise. Heather's own library has a house style; accepting the
    /// ASCII aliases is a language promise and warning about them is not.
    /// Canonical paths make this depend on the actual `lib/std` tree rather
    /// than a coincidental directory name.
    ///
    /// A property of the module, not of the root that pulled it in: the
    /// profile is part of the module's image key, so a profile taken from the
    /// root gave `nat` one image when `lib/std/num` was checked and another
    /// when `lib/native` was, and neither process could use the other's
    /// (`docs/library-world-design.md` §1).
    pub fn lint_profile(&self) -> LintProfile {
        let Ok(stdlib) = Path::new(STDLIB_DIR).canonicalize() else {
            return LintProfile::Default;
        };
        match self.path.canonicalize() {
            Ok(path) if path.starts_with(stdlib) => LintProfile::Stdlib,
            _ => LintProfile::Default,
        }
    }
}

/// The standard library's folder, from the working directory: what
/// [`Module::lint_profile`] reads as library code.
pub const STDLIB_DIR: &str = "lib/std";

/// A failure of the *run*, not of a file's contents: an unreadable file, an
/// unresolvable import, a cycle. Every message names the paths it is about,
/// so there is nothing to carry beside it.
pub struct LoadError {
    pub msg: String,
}

impl LoadError {
    pub(crate) fn new(msg: impl Into<String>) -> Self {
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

/// Load one root whose imports may also name modules the caller supplies
/// itself (the native builder's bundled proof library): an import of a
/// `provided` name that no file answers is left for the caller, which checks
/// those modules before the closure. A file that does answer is loaded as
/// usual, so the caller can still compare it with its own copy; and a name
/// that is ambiguous on the search path stays an error, since the caller's
/// copy would otherwise stand in for files the program's author can't tell
/// apart.
pub fn load_providing(root: &Path, search: &[PathBuf], provided: &[&str]) -> Result<Vec<Module>, LoadError> {
    let mut w = Walk {
        search,
        below: None,
        overlays: &HashMap::new(),
        provided,
        done: HashMap::new(),
        stack: Vec::new(),
        out: Vec::new(),
        imports: Vec::new(),
        by_name: HashMap::new(),
    };
    w.visit(root)?;
    Ok(w.out)
}

/// Load `root`'s closure, then the modules named by `extra` (resolved as
/// imports of `root` would be) and theirs: a tool that writes modules of its
/// own over the root (`write-elf`'s probes and certificate) imports them
/// without the root's author having to. The root's closure keeps
/// [`load`]'s order, so its images are the ones a `check` of it wrote.
pub fn load_with(root: &Path, search: &[PathBuf], extra: &[&str]) -> Result<Vec<Module>, LoadError> {
    load_after_with(&[], root, search, extra)
}

/// [`load_with`] after `first`'s closures, in [`load_many`]'s order: a world's
/// prefix (`world.rs`), which keeps the images a `check --world` wrote.
pub fn load_after_with(
    first: &[&Path],
    root: &Path,
    search: &[PathBuf],
    extra: &[&str],
) -> Result<Vec<Module>, LoadError> {
    let none = HashMap::new();
    let roots: Vec<&Path> = first.iter().copied().chain([root]).collect();
    let mut w = load_many_inner(&roots, search, &none)?;
    let from = root
        .canonicalize()
        .map_err(|e| LoadError::at(format!("cannot read `{}`: {e}", root.display()), root))?;
    for module in extra {
        match w.resolve(module, &from) {
            Ok(path) => w.visit(&path)?,
            Err(Unresolved::Missing(e) | Unresolved::Refused(e)) => return Err(e),
        }
    }
    Ok(w.out)
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
    load_many_inner(&[root.as_path()], search, &overlays).map(|w| w.out)
}

/// Load several roots as one import closure.
///
/// This is the directory-checking form's important semantic detail: a module
/// imported by two files is elaborated once, so declarations and warnings are
/// neither duplicated. Roots retain their supplied order, modulo dependencies
/// appearing before the root that needs them.
pub fn load_many(roots: &[&Path], search: &[PathBuf]) -> Result<Vec<Module>, LoadError> {
    load_many_inner(roots, search, &HashMap::new()).map(|w| w.out)
}

/// [`load_many`]'s modules with the import edges between them.
pub struct Graph {
    /// In [`load_many`]'s order.
    pub modules: Vec<Module>,
    /// Per module, the modules it imports (indices into `modules`), in the
    /// order its source writes them.
    pub imports: Vec<Vec<usize>>,
}

/// [`load_many`], keeping the import graph.
pub fn load_graph(roots: &[&Path], search: &[PathBuf]) -> Result<Graph, LoadError> {
    let none = HashMap::new();
    let w = load_many_inner(roots, search, &none)?;
    let at: HashMap<&str, usize> = w.out.iter().enumerate().map(|(i, m)| (m.name.as_str(), i)).collect();
    let imports = w.imports.iter().map(|names| names.iter().map(|n| at[n.as_str()]).collect()).collect();
    Ok(Graph { modules: w.out, imports })
}

fn load_many_inner<'a>(
    roots: &[&Path],
    search: &'a [PathBuf],
    overlays: &'a HashMap<PathBuf, String>,
) -> Result<Walk<'a>, LoadError> {
    let mut w = Walk {
        search,
        below: None,
        overlays,
        provided: &[],
        done: HashMap::new(),
        stack: Vec::new(),
        out: Vec::new(),
        imports: Vec::new(),
        by_name: HashMap::new(),
    };
    for root in roots {
        w.visit(root)?;
    }
    Ok(w)
}

struct Walk<'a> {
    search: &'a [PathBuf],
    /// The directories below the search directories, walked on the first
    /// import the search directories themselves miss (a hit never pays for
    /// the walk).
    below: Option<Vec<PathBuf>>,
    /// Canonical path → editor buffer. At present the public editor API
    /// overlays one root; keeping it a map makes recursive visits unambiguous.
    overlays: &'a HashMap<PathBuf, String>,
    /// Module names supplied by the caller, never resolved to files.
    provided: &'a [&'a str],
    /// Canonical path → module name. Dedup is by **path**, so a diamond costs
    /// one elaboration and two spellings of one file are one module.
    done: HashMap<PathBuf, String>,
    /// The DFS path, for the cycle report.
    stack: Vec<(PathBuf, String)>,
    out: Vec<Module>,
    /// Per module of `out`, the names of the modules it imports.
    imports: Vec<Vec<String>>,
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
                    match self.resolve(&imp.module, &canon) {
                        Ok(path) => v.push((imp.module.clone(), path)),
                        Err(Unresolved::Missing(_)) if self.provided.contains(&imp.module.as_str()) => {}
                        Err(Unresolved::Missing(e) | Unresolved::Refused(e)) => return Err(e),
                    }
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
        self.imports.push(imports.into_iter().map(|(_, dep)| self.done[&dep.canonicalize().expect("visited")].clone()).collect());
        Ok(())
    }

    /// `import m;` from `from`: the importing file's directory, then the `-L`
    /// dirs, then the directories below them. The lower tier is consulted only
    /// after a miss in the upper one, so a module kept below a facade can't
    /// shadow or conflict with a public module of the same name. Within either
    /// tier, a module found in **two** dirs is an error rather than a
    /// precedence, since which one a build got would otherwise depend on
    /// directory enumeration or flag order.
    fn resolve(&mut self, module: &str, from: &Path) -> Result<PathBuf, Unresolved> {
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
            if self.below.is_none() {
                self.below = Some(directories_below(self.search).map_err(Unresolved::Refused)?);
            }
            hits = self.below.iter().flatten().map(|d| d.join(&file)).filter(|p| p.is_file()).collect();
        }
        match hits.len() {
            0 => Err(Unresolved::Missing(LoadError::at(
                format!(
                    "cannot find module `{module}`: no `{file}` beside `{}`{}",
                    from.display(),
                    if self.search.is_empty() {
                        " and no `-L` search directory was given".to_string()
                    } else {
                        format!(
                            " or in {} or below",
                            self.search
                                .iter()
                                .map(|d| format!("`{}`", d.display()))
                                .collect::<Vec<_>>()
                                .join(", ")
                        )
                    }
                ),
                from,
            ))),
            1 => Ok(hits.into_iter().next().expect("one hit")),
            _ => Err(Unresolved::Refused(LoadError::at(
                format!(
                    "module `{module}` is in two search directories ({}) — that is an \
                     error, not a precedence: remove one copy or drop one `-L`",
                    hits.iter().map(|p| format!("`{}`", p.display())).collect::<Vec<_>>().join(", ")
                ),
                from,
            ))),
        }
    }
}

/// Why an import did not resolve. Only a `Missing` name may be left to a
/// caller that provides it; an ambiguous one, or a directory that couldn't be
/// read, is refused whoever provides the name.
enum Unresolved {
    Missing(LoadError),
    Refused(LoadError),
}

/// Every directory below the search directories, depth-first in name order,
/// leaving out those that are search directories themselves (which already
/// answered in the upper tier) and hidden ones: a dot-directory is a tool's
/// (`.git`, a cache, a worktree checkout holding a second copy of the whole
/// library), never a module family.
fn directories_below(search: &[PathBuf]) -> Result<Vec<PathBuf>, LoadError> {
    let canonical = |d: &Path| d.canonicalize().unwrap_or_else(|_| d.to_path_buf());
    let mut seen: std::collections::HashSet<PathBuf> = search.iter().map(|d| canonical(d)).collect();
    let mut below: Vec<PathBuf> = Vec::new();
    for root in search {
        let mut pending = child_directories(root)?;
        pending.reverse();
        while let Some(dir) = pending.pop() {
            if seen.insert(canonical(&dir)) {
                below.push(dir.clone());
            }
            pending.extend(child_directories(&dir)?.into_iter().rev());
        }
    }
    Ok(below)
}

fn child_directories(dir: &Path) -> Result<Vec<PathBuf>, LoadError> {
    // A search directory that doesn't exist has nothing below it: the upper
    // tier already treats it as holding no modules.
    if !dir.is_dir() {
        return Ok(Vec::new());
    }
    let mut children = std::fs::read_dir(dir)
        .map_err(|e| LoadError::new(format!("cannot read directory `{}`: {e}", dir.display())))?
        .filter_map(|entry| match entry {
            Ok(entry) => match entry.file_type() {
                Ok(kind) if kind.is_dir() && !entry.file_name().to_string_lossy().starts_with('.') => {
                    Some(Ok(entry.path()))
                }
                Ok(_) => None,
                Err(e) => Some(Err(LoadError::new(format!(
                    "cannot inspect entry in directory `{}`: {e}",
                    dir.display()
                )))),
            },
            Err(e) => Some(Err(LoadError::new(format!("cannot read directory `{}`: {e}", dir.display())))),
        })
        .collect::<Result<Vec<_>, _>>()?;
    children.sort();
    Ok(children)
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
