//! A library's canonical world (`heather check --world <dir>`,
//! `docs/archive/library-world-design.md`).
//!
//! A module's image is keyed by every module loaded before it in its process,
//! in order: Ψ positions are absolute, and an inductive's nominal tag is the
//! number of inductives before it, which its constructors carry in their
//! kernel types. So the same module checked by two processes that loaded
//! different modules before it is two different elaborations, and neither
//! process can replay the other's image. The library gate checks one folder
//! per process, and each folder's load order put the standard library's
//! modules over a different prefix: from a cold store every folder rebuilt
//! the part of `std` it needed (`issues/early-cutoff-registry-and-order-granularity.md`).
//!
//! The world fixes the prefix instead. It is one order of the library's
//! **shared** modules (those another module of the library imports), and a
//! check over it loads that order up to the last shared module its closure
//! needs, then its own modules. Every process that names the same world gives
//! a shared module the same prefix, so its image has one key, which the first
//! process to need it builds and every other one replays. The price is the
//! shared modules a process loads without needing them, which it replays.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use crate::loader::{self, LoadError, Module};

/// The modules `heather write-elf` loads besides its source's closure
/// (`native/elf.rs`): the probes and the certificate import them. Every one,
/// with the closure of the tools it compiles, must be a module of `lib`'s
/// world, or it is loaded after a prefix of `write-elf`'s own and its image
/// is keyed apart from the one the library gate built
/// (`issues/native-process-fixed-cost.md`); the gate's
/// `write_elf_loads_only_world_modules` holds it so.
pub const WRITE_ELF_IMPORTS: &[&str] = &["native_source", "native_source_spelled", "native_build", "native_build_parts", "native_alloc", "native_compile", "native_compile_correct", "native_compile_elf", "native_contract", "function_ir", "function_ir_eval", "function_ir_lower", "function_ir_lower_calls", "function_ir_pass", "function_ir_placeless", "function_ir_rows",
    "linux_x86_64_byte_memory", "linux_x86_64_image", "linux_x86_64_io", "linux_x86_64_sim", "x86_64", "x86_64_asm", "x86_64_asm_runs",
    "x86_64_asm_table", "x86_64_block",
    "x86_64_byte_memory", "x86_64_data_read", "x86_64_store", "bitvec", "bool", "list", "logic", "nat", "option"];

/// The shared modules of a library, in the order every check over it loads
/// them.
pub struct World {
    /// Canonical paths.
    order: Vec<PathBuf>,
    at: HashMap<PathBuf, usize>,
    /// The library's folders in the order they placed their modules.
    folders: Vec<PathBuf>,
}

impl World {
    /// The world of the library under `dir`, its imports resolved over
    /// `search` as a check of `dir` resolves them.
    ///
    /// The order is built folder by folder ([`folders`]): repeatedly, the
    /// folder whose closure needs the fewest shared modules not yet placed
    /// (the earlier folder on a tie) places them, in its own load order. A
    /// folder with a small closure therefore finds it near the front instead
    /// of behind modules it never reads, which keeps the replays a check pays
    /// for its prefix close to its own closure. It is a function of the tree
    /// alone: adding a module nothing imports leaves it unchanged.
    pub fn of(dir: &Path, search: &[PathBuf]) -> Result<World, LoadError> {
        let names = folders(dir)?;
        let units: Vec<Vec<PathBuf>> = names.iter().map(|f| files_below(f)).collect::<Result<_, _>>()?;
        let roots: Vec<&Path> = units.iter().flatten().map(PathBuf::as_path).collect();
        let graph = loader::load_graph(&roots, search)?;
        let shared: HashSet<usize> = graph.imports.iter().flatten().copied().collect();
        let index: HashMap<&Path, usize> =
            graph.modules.iter().enumerate().map(|(i, m)| (m.path.as_path(), i)).collect();
        // Each folder's closure in the loader's order: its files as roots,
        // dependencies first.
        let closures: Vec<Vec<usize>> = units
            .iter()
            .map(|files| {
                let mut seen = HashSet::new();
                let mut out = Vec::new();
                for file in files {
                    let canon = file.canonicalize().map_err(|e| LoadError::new(format!("cannot read `{}`: {e}", file.display())))?;
                    post_order(&graph.imports, index[canon.as_path()], &mut seen, &mut out);
                }
                Ok(out.into_iter().filter(|m| shared.contains(m)).collect())
            })
            .collect::<Result<_, LoadError>>()?;
        let mut placed = HashSet::new();
        let mut order = Vec::new();
        let mut placing = Vec::new();
        let mut pending: Vec<usize> = (0..closures.len()).collect();
        while !pending.is_empty() {
            let new = |u: usize| closures[u].iter().filter(|m| !placed.contains(*m)).count();
            let (k, &u) = pending.iter().enumerate().min_by_key(|&(_, &u)| (new(u), u)).expect("pending");
            pending.remove(k);
            placing.push(names[u].clone());
            for &m in &closures[u] {
                if placed.insert(m) {
                    order.push(graph.modules[m].path.clone());
                }
            }
        }
        let at = order.iter().enumerate().map(|(i, p)| (p.clone(), i)).collect();
        Ok(World { order, at, folders: placing })
    }

    /// The library's folders ([`folders`]) in the order they placed their
    /// modules: checked in this order, each folder's process finds the
    /// shared modules before its own already built by the ones before it.
    pub fn folders(&self) -> &[PathBuf] {
        &self.folders
    }

    /// The world's modules a check of `modules` (a loader closure) loads
    /// first: the world's order up to the last module of `modules` in it.
    /// Empty when the closure needs none of them.
    pub fn prefix(&self, modules: &[Module]) -> &[PathBuf] {
        let end = modules.iter().filter_map(|m| self.at.get(&m.path)).map(|&i| i + 1).max().unwrap_or(0);
        &self.order[..end]
    }

    /// The shared modules, in order.
    pub fn order(&self) -> &[PathBuf] {
        &self.order
    }
}

fn post_order(imports: &[Vec<usize>], m: usize, seen: &mut HashSet<usize>, out: &mut Vec<usize>) {
    if !seen.insert(m) {
        return;
    }
    for &d in &imports[m] {
        post_order(imports, d, seen, out);
    }
    out.push(m);
}

/// The folders of the library under `dir`: a directory that holds `.hthr`
/// files directly is one folder, its subdirectories included; a directory
/// that holds only directories is split into them. Hidden directories are
/// skipped, as the loader skips them. In name order.
pub fn folders(dir: &Path) -> Result<Vec<PathBuf>, LoadError> {
    let mut out = Vec::new();
    let mut pending = vec![dir.to_path_buf()];
    while let Some(d) = pending.pop() {
        let (files, dirs) = entries(&d)?;
        if !files.is_empty() || dirs.is_empty() {
            if !files.is_empty() {
                out.push(d);
            }
            continue;
        }
        pending.extend(dirs.into_iter().rev());
    }
    out.sort();
    Ok(out)
}

/// Every `.hthr` file below `dir`, its subdirectories included, in path order.
fn files_below(dir: &Path) -> Result<Vec<PathBuf>, LoadError> {
    let mut out = Vec::new();
    let mut pending = vec![dir.to_path_buf()];
    while let Some(d) = pending.pop() {
        let (files, dirs) = entries(&d)?;
        out.extend(files);
        pending.extend(dirs);
    }
    out.sort();
    Ok(out)
}

/// A directory's `.hthr` files and its visible subdirectories, each sorted.
fn entries(dir: &Path) -> Result<(Vec<PathBuf>, Vec<PathBuf>), LoadError> {
    let read = std::fs::read_dir(dir).map_err(|e| LoadError::new(format!("cannot read directory `{}`: {e}", dir.display())))?;
    let (mut files, mut dirs) = (Vec::new(), Vec::new());
    for entry in read {
        let entry = entry.map_err(|e| LoadError::new(format!("cannot read directory `{}`: {e}", dir.display())))?;
        let path = entry.path();
        if entry.file_name().to_string_lossy().starts_with('.') {
            continue;
        }
        if path.is_dir() {
            dirs.push(path);
        } else if path.extension().is_some_and(|x| x == "hthr") {
            files.push(path);
        }
    }
    files.sort();
    dirs.sort();
    Ok((files, dirs))
}
