#!/usr/bin/env node
// Which test binaries a round's diff can affect (`scripts/test --pr`;
// docs/infrastructure/testing-architecture-design.md §2.2). scripts/test builds every test
// binary first, then hands this file Cargo's JSON manifest; it writes the
// manifest back with only the affected binaries' artifacts, for
// run-test-targets.mjs to run as before.
//
// A binary's inputs are what Cargo itself rebuilds it from:
//
// - **Compile-time**: the dep-info (`.d`) rustc wrote for the binary and for
//   every workspace library it links, through normal, dev and build
//   dependencies, plus each build script's `rerun-if-changed` paths. An
//   `include_str!` of a `lib/` module is in the `.d`, so an elab test that
//   mounts a library prefix is selected exactly by the modules it embeds.
// - **Run-time**: a binary whose own sources read files or spawn processes
//   (`RUNTIME_READ`) may read any of `lib/`, `examples/`, `docs/showcase/`
//   or the editor corpus, so any change there selects it.
//
// Everything this cannot place runs everything: a workspace manifest or
// lockfile, the test harness itself, a path outside the known directories,
// no merge base. A file under a crate's directory that no `.d` names (a
// fixture, a Cargo.toml, a new file not yet `mod`-declared) selects every
// binary of that crate, every binary that depends on it, and every run-time
// reader. Paths no test reads (`NO_TEST`) select nothing. Misses are what the
// nightly sentinel's full run is for; the selection is the fast lane's
// unproven optimisation in the two-tier sense of the design note's §5.

import { execFileSync } from "node:child_process";
import { existsSync, readFileSync, writeFileSync } from "node:fs";
import { dirname, isAbsolute, join, normalize, relative } from "node:path";
import { fileURLToPath } from "node:url";

// Any change here selects every test.
export const GLOBAL = /^(Cargo\.toml|Cargo\.lock|\.cargo\/|rust-toolchain|scripts\/(test|run-test-targets\.mjs|affected-targets\.mjs|check-elab-test-families\.mjs)$)/;
// No test binary reads these (scripts/test's own checks run on every lane).
// A file some `.d` names is never one of these, whatever its path.
export const NO_TEST = /^(docs\/(?!showcase\/)|issues\/|perf\/|book\/|book\.toml$|probes\/|editors\/|scripts\/|\.claude\/|\.gitignore$)|\.md$/;
// Read at run time by tests (lib/ also at compile time, through include_str!).
export const RUNTIME_DATA = /^(lib\/|examples\/|docs\/showcase\/|tree-sitter-heather\/|crates\/linked\/generated\/)/;
// A binary whose own sources say this may read run-time data. File I/O and
// process spawns, and the CLI library's entry points that read sources
// (`loader::Module` is a value, not a read).
export const RUNTIME_READ = /\b(read_to_string|read_dir|fs::read|File::open|Command::new|CARGO_BIN_EXE_|WalkDir)\b|heather_cli::(loader(?!::Module\b)|world|showcase|fmt)\b|heather_cli::\{[^}]*\b(loader|world|showcase|fmt)\b/;

// Make's dep-info: `out: in in…` rules, spaces escaped. Every path named on
// either side; the outputs are under target/ and never match a changed file.
export function parseDepInfo(text) {
  const files = [];
  for (const line of text.split("\n")) {
    const colon = line.search(/:(\s|$)/);
    if (colon < 0) continue;
    const rest = line.slice(colon + 1).replace(/\\ /g, "\u0000");
    for (const word of rest.split(/\s+/)) if (word) files.push(word.replace(/\u0000/g, " "));
  }
  return files;
}

// A path as the repo spells it, or null outside the repo (registry crates).
export function repoPath(path, root) {
  const rel = relative(root, normalize(isAbsolute(path) ? path : join(root, path)));
  return rel.startsWith("..") || isAbsolute(rel) ? null : rel;
}

function packageName(id) {
  return String(id).split("#").at(-1).split("@")[0];
}

// Units from Cargo's `--message-format=json`: every workspace artifact with
// the dep-info beside it, and build scripts' rerun paths.
export function parseUnits(text, root, readFile = (p) => (existsSync(p) ? readFileSync(p, "utf8") : null)) {
  const units = [];
  const builds = new Map();
  for (const line of text.split("\n")) {
    if (!line.trim()) continue;
    let msg;
    try { msg = JSON.parse(line); } catch { continue; }
    if (!String(msg.package_id).startsWith("path+file://")) continue;
    const pkg = packageName(msg.package_id);
    if (msg.reason === "build-script-executed") {
      const output = readFile(join(msg.out_dir, "..", "output")) ?? "";
      const pkgDir = String(msg.package_id).replace(/^path\+file:\/\//, "").split("#")[0];
      const paths = [...output.matchAll(/^cargo:{1,2}rerun-if-changed=(.*)$/gm)].map((m) => repoPath(isAbsolute(m[1]) ? m[1] : join(pkgDir, m[1]), root));
      builds.set(pkg, [...(builds.get(pkg) ?? []), ...paths.filter(Boolean)]);
      continue;
    }
    if (msg.reason !== "compiler-artifact") continue;
    const depInfos = new Set();
    for (const file of [msg.executable, ...(msg.filenames ?? [])].filter(Boolean)) {
      // deps/name-hash (test executable), deps/libname-hash.rlib, debug/name
      // (an uplifted binary, whose `.d` Cargo uplifts beside it).
      const base = file.replace(/\.(rlib|rmeta|so|a)$/, "");
      depInfos.add(`${base}.d`);
      depInfos.add(join(dirname(base), `${base.split("/").at(-1).replace(/^lib/, "")}.d`));
    }
    const sources = new Set();
    for (const d of depInfos) {
      const text = readFile(d);
      if (text === null) continue;
      for (const f of parseDepInfo(text)) {
        const rel = repoPath(f, root);
        if (rel && !rel.startsWith("target/")) sources.add(rel);
      }
    }
    units.push({
      pkg,
      name: msg.target.name,
      kind: msg.target.kind,
      test: Boolean(msg.profile?.test),
      executable: msg.executable ?? null,
      srcDir: repoPath(dirname(msg.target.src_path), root),
      sources,
      line,
    });
  }
  for (const unit of units) {
    if (unit.kind.includes("custom-build")) for (const p of builds.get(unit.pkg) ?? []) unit.sources.add(p);
  }
  return units;
}

// Workspace packages: directory and path dependencies, from `cargo metadata
// --no-deps`.
export function parsePackages(metadata, root) {
  const packages = new Map();
  for (const p of JSON.parse(metadata).packages) {
    packages.set(p.name, {
      dir: repoPath(dirname(p.manifest_path), root),
      srcDirs: p.targets.map((t) => repoPath(dirname(t.src_path), root)).filter(Boolean),
      deps: p.dependencies.filter((d) => d.path).map((d) => ({ name: d.name, kind: d.kind ?? "normal" })),
    });
  }
  return packages;
}

// Packages a test unit of `pkg` links or builds with: its own, its normal,
// dev and build dependencies, then theirs through normal and build edges.
export function reach(pkg, packages) {
  const seen = new Set([pkg]);
  const work = [...(packages.get(pkg)?.deps ?? [])].map((d) => d.name);
  while (work.length) {
    const name = work.pop();
    if (seen.has(name) || !packages.has(name)) continue;
    seen.add(name);
    for (const d of packages.get(name).deps) if (d.kind !== "dev") work.push(d.name);
  }
  return seen;
}

function isPrefix(dir, path) {
  return dir === "" || path === dir || path.startsWith(`${dir}/`);
}

// A family binary (`family_*`, run as one shard per member file by
// run-test-targets.mjs) splits into its members. Each crate-root module the
// family's root file mounts (`#[path = "…"] mod name;`) owns its file, the
// files of its `mod x;` children, and the literal `include_str!`/
// `include_bytes!` targets in those; a member's inputs are its own module's,
// those of every root module it names (`crate::name`, `super::name`, or a
// `support::name` child), and whatever is owned by no module (the root file,
// support/mod.rs, a non-literal include): those count for every member.
export function familyMembers(unit, readSource) {
  const rootFile = [...unit.sources].find((f) => f.endsWith(`/families/${unit.name.replace(/^family_/, "")}.rs`));
  if (!rootFile) return null;
  const owned = new Map();
  const ownedBy = new Set();
  const tree = (file, seen = new Set()) => {
    if (seen.has(file) || !unit.sources.has(file)) return seen;
    seen.add(file);
    const text = readSource(file) ?? "";
    const dir = dirname(file);
    const childDir = /(^|\/)(mod|lib|main)\.rs$/.test(file) ? dir : join(dir, file.split("/").at(-1).replace(/\.rs$/, ""));
    for (const m of text.matchAll(/^\s*(?:pub(?:\([^)]*\))?\s+)?mod\s+(\w+)\s*;/gm)) {
      for (const c of [join(childDir, `${m[1]}.rs`), join(childDir, m[1], "mod.rs")]) tree(normalize(c), seen);
    }
    for (const m of text.matchAll(/\binclude_(?:str|bytes)!\(\s*"([^"]+)"\s*\)/g)) seen.add(normalize(join(dir, m[1])));
    return seen;
  };
  const rootText = readSource(rootFile) ?? "";
  for (const m of rootText.matchAll(/#\[path\s*=\s*"([^"]+)"\]\s*(?:pub\s+)?mod\s+(\w+)\s*;/g)) {
    const file = normalize(join(dirname(rootFile), m[1]));
    // support/mod.rs is everyone's: its children are owned one by one.
    if (m[2] === "support") {
      for (const c of (readSource(file) ?? "").matchAll(/^\s*pub\s+mod\s+(\w+)\s*;/gm)) {
        const files = tree(normalize(join(dirname(file), `${c[1]}.rs`)));
        owned.set(`support::${c[1]}`, files);
      }
      continue;
    }
    owned.set(m[2], tree(file));
  }
  for (const files of owned.values()) for (const f of files) ownedBy.add(f);
  const shared = [...unit.sources].filter((f) => !ownedBy.has(f));
  const names = (files) => {
    const text = [...files].filter((f) => f.endsWith(".rs")).map((f) => readSource(f) ?? "").join("\n");
    const glob = /\b(crate|super)::\*|\bsupport::\*/.test(text);
    return [...owned.keys()].filter((n) => {
      const leaf = n.replace(/^support::/, "");
      return glob || new RegExp(n.startsWith("support::")
        ? `\\bsupport::(${leaf}\\b|\\{[^}]*\\b${leaf}\\b)`
        : `\\b(crate|super)::(${leaf}\\b|\\{[^}]*\\b${leaf}\\b)`).test(text);
    });
  };
  const members = [];
  for (const [name, files] of owned) {
    // Every root module is a candidate: a helper (`common`, `omega_cases`)
    // may hold tests too, and one with none yields no shard.
    if (name.startsWith("support::")) continue;
    // Close over the root modules this member names, transitively.
    const sources = new Set([...shared, ...files]);
    const used = new Set();
    const work = names(files);
    while (work.length) {
      const n = work.pop();
      if (used.has(n) || n === name) continue;
      used.add(n);
      for (const f of owned.get(n)) sources.add(f);
      work.push(...names(owned.get(n)));
    }
    members.push({ member: name, sources });
  }
  return members;
}

// The decision. `changed` is repo paths. Returns the selected candidates (a
// test binary, or one member of a family binary), each with the first file
// that selected it.
export function selectTargets({ changed, units, packages, readSource }) {
  const tests = units.filter((u) => u.test && u.executable);
  const candidates = tests.flatMap((t) => {
    const members = t.name.startsWith("family_") ? familyMembers(t, readSource) : null;
    return members?.length
      ? members.map((m) => ({ ...t, key: `${t.executable}#${m.member}`, member: m.member, sources: m.sources }))
      : [{ ...t, key: t.executable, member: null }];
  });
  const all = (reason) => ({ all: true, reason, candidates, selected: new Map(candidates.map((t) => [t.key, null])) });
  const global = changed.find((f) => GLOBAL.test(f));
  if (global) return all(global);

  // What a test links from each package: a dependency's library and build
  // script; its own package's binaries too, which an integration test may
  // run (`CARGO_BIN_EXE_*`). And every file some unit names.
  const libSources = new Map();
  const binSources = new Map();
  for (const u of units) {
    if (u.kind.includes("test") || u.kind.includes("bench") || u.kind.includes("example")) continue;
    const into = u.kind.includes("bin") ? binSources : libSources;
    if (!into.has(u.pkg)) into.set(u.pkg, new Set());
    for (const f of u.sources) into.get(u.pkg).add(f);
  }
  const named = new Set(units.flatMap((u) => [...u.sources]));
  const inputs = new Map();
  const runtime = new Map();
  for (const t of candidates) {
    const reached = reach(t.pkg, packages);
    const set = new Set(t.sources);
    for (const p of reached) for (const f of libSources.get(p) ?? []) set.add(f);
    for (const f of binSources.get(t.pkg) ?? []) set.add(f);
    inputs.set(t.key, { set, reached });
    runtime.set(t.key, [...t.sources].some((f) => f.endsWith(".rs") && RUNTIME_READ.test(readSource(f) ?? "")));
  }

  const selected = new Map();
  const pick = (t, f) => { if (!selected.has(t.key)) selected.set(t.key, f); };
  for (const f of changed) {
    const isNamed = named.has(f);
    if (!isNamed && NO_TEST.test(f)) continue;
    const inCrates = f.startsWith("crates/");
    if (!inCrates && !isNamed && !RUNTIME_DATA.test(f)) return all(f);
    let owners = [];
    let benchOnly = false;
    let fixture = false;
    if (inCrates && !isNamed) {
      owners = [...packages].filter(([, p]) => isPrefix(p.dir, f) || p.srcDirs.some((d) => isPrefix(d, f))).map(([n]) => n);
      if (!owners.length) return all(f);
      // A bench's data (baselines, corpora) no unit compiles: only a test of
      // that crate that reads files at run time could see it. A test
      // fixture is its own crate's, and a run-time reader's anywhere.
      benchOnly = owners.some((o) => isPrefix(`${packages.get(o).dir}/benches`, f));
      fixture = owners.some((o) => isPrefix(`${packages.get(o).dir}/tests`, f));
    }
    for (const t of candidates) {
      const { set, reached } = inputs.get(t.key);
      if (set.has(f)) pick(t, f);
      else if (RUNTIME_DATA.test(f) && runtime.get(t.key)) pick(t, f);
      else if (benchOnly) { if (runtime.get(t.key) && owners.includes(t.pkg)) pick(t, f); }
      else if (fixture) { if (runtime.get(t.key) || owners.includes(t.pkg)) pick(t, f); }
      else if (owners.length && (runtime.get(t.key) || owners.some((o) => reached.has(o)))) pick(t, f);
    }
  }
  return { all: false, reason: null, candidates, selected };
}

export function changedFiles(base) {
  const out = execFileSync("bash", ["-c",
    `git diff --no-renames --name-only ${base}; git ls-files --others --exclude-standard`], { encoding: "utf8" });
  return [...new Set(out.split("\n").filter(Boolean))].sort();
}

function main() {
  const args = process.argv.slice(2);
  const take = (flag) => {
    const i = args.indexOf(flag);
    if (i < 0 || i + 1 === args.length) throw new Error(`missing ${flag}`);
    return args.splice(i, 2)[1];
  };
  const manifest = take("--manifest");
  // `--paths a,b,…` in place of `--base`: what those files would select,
  // printed and not written (checking the selection by hand).
  const paths = args.includes("--paths") ? take("--paths").split(",").filter(Boolean) : null;
  const base = paths ? null : take("--base");
  const out = paths ? null : take("--out");
  const root = process.cwd();
  const units = parseUnits(readFileSync(manifest, "utf8"), root);
  const packages = parsePackages(execFileSync("cargo", ["metadata", "--format-version", "1", "--no-deps", "--offline"],
    { encoding: "utf8", maxBuffer: 64 * 1024 * 1024 }), root);
  const changed = paths ?? changedFiles(base);
  const readSource = (f) => (existsSync(f) ? readFileSync(f, "utf8") : null);
  const { all, reason, candidates, selected } = selectTargets({ changed, units, packages, readSource });
  const short = paths ? "--paths" : execFileSync("git", ["rev-parse", "--short", base], { encoding: "utf8" }).trim();
  if (all) {
    console.log(`affected: every test runs (${reason} changed since ${short})`);
  } else {
    console.log(`affected: ${selected.size} of ${candidates.length} test files, from ${changed.length} files changed since ${short} (HEATHER_PR_AFFECTED=all runs every one)`);
    const byFile = new Map();
    for (const f of selected.values()) byFile.set(f, (byFile.get(f) ?? 0) + 1);
    for (const [f, n] of [...byFile].sort((a, b) => b[1] - a[1]).slice(0, 8)) console.log(`  ${String(n).padStart(4)} selected by ${f}`);
  }
  const chosen = candidates.filter((c) => selected.has(c.key));
  if (paths) {
    for (const c of chosen) console.log(`  ${c.member ? `${c.name}::${c.member}` : c.name}\t${selected.get(c.key) ?? ""}`);
    return;
  }
  const executables = new Set(chosen.map((c) => c.executable));
  // Non-test units stay (nothing runs them); unselected test binaries go.
  writeFileSync(out, units.filter((u) => !(u.test && u.executable) || executables.has(u.executable)).map((u) => u.line).join("\n") + "\n");
  // Every member of each family that runs, marked run or skip
  // (run-test-targets.mjs --members), the selected binaries' names (scripts/test's warm-ups), and
  // the packages whose doc tests run: those with a selected test.
  const lines = (xs) => xs.length ? xs.join("\n") + "\n" : "";
  writeFileSync(`${out}.members`, lines(candidates.filter((c) => c.member && executables.has(c.executable))
    .map((c) => `${c.name}\t${c.member}\t${selected.has(c.key) ? "run" : "skip"}`)));
  writeFileSync(`${out}.names`, lines([...new Set(chosen.map((c) => c.name))].sort()));
  const hasLib = new Set(units.filter((u) => !u.test && u.kind.includes("lib")).map((u) => u.pkg));
  writeFileSync(`${out}.doc`, lines(all ? ["*"] : [...new Set(chosen.map((c) => c.pkg))].filter((p) => hasLib.has(p)).sort()));
}

if (process.argv[1] && fileURLToPath(import.meta.url) === process.argv[1]) {
  try { main(); } catch (error) { console.error(`affected targets: ${error.message}`); process.exit(2); }
}
