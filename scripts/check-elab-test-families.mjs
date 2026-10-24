#!/usr/bin/env node
// crates/elab's integration tests are grouped into family binaries that
// mount their member files by path (docs/elab-test-families-design.md), and
// the package sets `autotests = false`, so Cargo no longer notices a test
// file nobody declared: it would silently never compile. This script is the
// check that replaces the discovery (§D5), run in scripts/test's preamble:
//
//   node scripts/check-elab-test-families.mjs
//
// and the lookup scripts/test uses to keep `--test <file>` meaning the file
// (§D4): it prints the argument list with every `--test <member>` rewritten
// to `--test <family>` plus a `<member>::` filter, NUL-separated.
//
//   node scripts/check-elab-test-families.mjs --rewrite-args -- <cargo test args>

import { existsSync, readFileSync, readdirSync } from "node:fs";
import { basename, dirname, join, normalize, relative } from "node:path";
import { fileURLToPath } from "node:url";

const ROOT = join(dirname(fileURLToPath(import.meta.url)), "..");
const CRATE = "crates/elab";
const TESTS = `${CRATE}/tests`;

// tests/*.rs files that are shared modules, not tests: a family mounts them
// once and its members `use crate::<name>`. The support/ and omega_cases/
// directories are shared modules too, but they are not tests/*.rs files.
export const SHARED_MODULES = new Set([]);

// `[[test]]` entries of a Cargo.toml, as { name, path }. The manifest is
// ours and written one key per line, so this is a line reader, not TOML.
export function testTargets(toml) {
  const targets = [];
  let current = null;
  for (const line of toml.split("\n")) {
    if (/^\s*\[/.test(line)) {
      current = /^\s*\[\[test\]\]\s*$/.test(line) ? {} : null;
      if (current) targets.push(current);
      continue;
    }
    const m = current && /^\s*(name|path)\s*=\s*"([^"]*)"/.exec(line);
    if (m) current[m[1]] = m[2];
  }
  return targets;
}

// A family file's path-mounted modules, as { name, path } with `path` as
// written (relative to the family file's directory).
export function mounts(source) {
  const out = [];
  const re = /#\[path\s*=\s*"([^"]+)"\]\s*(?:#\[[^\]]*\]\s*)*(?:pub(?:\([^)]*\))?\s+)?mod\s+(\w+)\s*;/g;
  for (const m of source.matchAll(re)) out.push({ name: m[2], path: m[1] });
  return out;
}

// What a member file may not declare: its own copy of a module the family
// already mounts (a private `support` is a private `OnceLock`), or any
// path-mounted module of its own. Line-anchored, so prose in comments and
// the generated crate in telescope_roles_compile.rs's string do not count.
export function memberViolations(source) {
  const out = [];
  source.split("\n").forEach((line, i) => {
    if (/^\s*(?:pub\s+)?mod\s+(support|common|omega_cases)\s*;/.test(line)) out.push(`${i + 1}: \`${line.trim()}\` (use crate::… instead)`);
    else if (/^\s*#\[path\s*=\s*"/.test(line)) out.push(`${i + 1}: \`${line.trim()}\` (mount it in the family file)`);
  });
  return out;
}

export function loadLayout(root = ROOT) {
  const targets = testTargets(readFileSync(join(root, CRATE, "Cargo.toml"), "utf8"));
  const families = [];
  const standalone = new Map();
  for (const t of targets) {
    const path = normalize(join(CRATE, t.path ?? ""));
    if (t.name?.startsWith("family_")) {
      const source = readFileSync(join(root, path), "utf8");
      families.push({ name: t.name, path, mounts: mounts(source).map((m) => ({ ...m, file: normalize(join(dirname(path), m.path)) })) });
    } else if (t.name) {
      standalone.set(t.name, path);
    }
  }
  return { families, standalone };
}

export function lint(root = ROOT) {
  const problems = [];
  const { families, standalone } = loadLayout(root);
  const owners = new Map();
  const note = (file, owner) => owners.set(file, [...(owners.get(file) ?? []), owner]);
  for (const [name, path] of standalone) {
    if (!existsSync(join(root, path))) problems.push(`[[test]] ${name}: ${path} does not exist`);
    note(path, `[[test]] ${name}`);
  }
  for (const family of families) {
    for (const m of family.mounts) {
      if (!existsSync(join(root, m.file))) { problems.push(`${family.path}: mounts ${m.path}, which does not exist`); continue; }
      if (!m.file.startsWith(`${TESTS}/`) || m.file.slice(TESTS.length + 1).includes("/")) continue;
      // A shared tests/*.rs module is held to the members' rule too: its
      // own `mod support;` would be one more private copy.
      for (const v of memberViolations(readFileSync(join(root, m.file), "utf8"))) problems.push(`${m.file}:${v}`);
      if (SHARED_MODULES.has(basename(m.file))) continue;
      if (basename(m.file, ".rs") !== m.name) problems.push(`${family.path}: ${m.path} is mounted as \`${m.name}\`; a member's module is its file stem (the runner shards by it)`);
      note(m.file, family.name);
    }
  }
  for (const file of readdirSync(join(root, TESTS)).filter((f) => f.endsWith(".rs")).sort()) {
    if (SHARED_MODULES.has(file)) continue;
    const path = `${TESTS}/${file}`;
    const by = owners.get(path) ?? [];
    if (by.length === 0) problems.push(`${path}: no test target builds it; mount it in a family (tests/families/) or declare a [[test]]`);
    if (by.length > 1) problems.push(`${path}: built by more than one target (${by.join(", ")})`);
  }
  // A shared module mounted by several families is reported once.
  return [...new Set(problems)];
}

// cargo test options that take a value, so the positional TESTNAME filter
// can be told apart from an option's argument. libtest's likewise, after `--`.
const CARGO_VALUED = new Set(["-p", "--package", "--test", "--bin", "--example", "--bench", "-F", "--features",
  "--target", "--target-dir", "--manifest-path", "-j", "--jobs", "--profile", "--exclude", "--message-format",
  "--color", "--config", "-Z", "--timings"]);
const LIBTEST_VALUED = new Set(["--skip", "--format", "--test-threads", "--color", "--logfile", "-Z", "--shuffle-seed"]);

function positionals(args, valued) {
  const out = [];
  for (let i = 0; i < args.length; i++) {
    const a = args[i];
    if (a.startsWith("-")) { if (valued.has(a) && !a.includes("=")) i++; continue; }
    out.push(i);
  }
  return out;
}

// `--test <member>` → `--test <family>` with the member's `member::` prefix as
// the filter; a filter the caller gave becomes `member::<filter>` (members'
// tests are mostly top-level functions, so that still names the test).
// Returns the args unchanged when no `--test` names a member.
export function rewriteArgs(args, families) {
  const familyOf = new Map();
  for (const f of families) for (const m of f.mounts) familyOf.set(m.name, f.name);
  const sep = args.indexOf("--");
  const cargo = sep < 0 ? [...args] : args.slice(0, sep);
  const libtest = sep < 0 ? [] : args.slice(sep + 1);
  const members = [];
  const others = [];
  for (let i = 0; i < cargo.length; i++) {
    let value = null;
    if (cargo[i] === "--test" && i + 1 < cargo.length) value = cargo[i + 1];
    else if (cargo[i].startsWith("--test=")) value = cargo[i].slice(7);
    if (value === null) continue;
    const family = familyOf.get(value);
    if (!family) { others.push(value); continue; }
    members.push(value);
    if (cargo[i] === "--test") cargo[i + 1] = family; else cargo[i] = `--test=${family}`;
  }
  if (!members.length) return args;
  if (others.length) throw new Error(`--test ${members.join(", ")} (family members) cannot share a run with --test ${others.join(", ")}: the member filter would apply to both; run them separately`);
  // The caller's filters, wherever they were given, move after `--`, one per
  // member; libtest runs a test matching any of them.
  const filters = [];
  for (const i of positionals(cargo, CARGO_VALUED).reverse()) filters.unshift(...cargo.splice(i, 1));
  for (const i of positionals(libtest, LIBTEST_VALUED).reverse()) filters.unshift(...libtest.splice(i, 1));
  const named = [...new Set(members)].flatMap((m) => filters.length ? filters.map((f) => `${m}::${f}`) : [`${m}::`]);
  return [...cargo, "--", ...libtest, ...named];
}

function main() {
  const args = process.argv.slice(2);
  if (args[0] === "--rewrite-args") {
    const rest = args.slice(args[1] === "--" ? 2 : 1);
    try {
      process.stdout.write(rewriteArgs(rest, loadLayout().families).map((a) => `${a}\0`).join(""));
    } catch (error) {
      console.error(`scripts/test: ${error.message}`);
      process.exit(2);
    }
    return;
  }
  const problems = lint();
  if (problems.length) {
    console.error(`elab test families (${relative(process.cwd(), join(ROOT, CRATE, "Cargo.toml"))}, docs/elab-test-families-design.md):`);
    for (const p of problems) console.error(`  ${p}`);
    process.exit(1);
  }
}

if (process.argv[1] && fileURLToPath(import.meta.url) === process.argv[1]) main();
