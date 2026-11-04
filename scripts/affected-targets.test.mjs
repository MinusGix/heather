import test from "node:test";
import assert from "node:assert/strict";
import { familyMembers, parseDepInfo, parseUnits, reach, repoPath, selectTargets } from "./affected-targets.mjs";
import { docTestArgs, parseMembers, selectShards } from "./run-test-targets.mjs";

// A workspace in miniature: `kernel` (a library), `cli` (a library and a
// binary, depending on kernel), and `elab` (tests only) dev-depending on cli.
const packages = new Map([
  ["kernel", { dir: "crates/kernel", srcDirs: ["crates/kernel/src"], deps: [] }],
  ["cli", { dir: "crates/cli", srcDirs: ["crates/cli/src"], deps: [{ name: "kernel", kind: "normal" }] }],
  ["elab", { dir: "crates/elab", srcDirs: ["crates/elab/tests"], deps: [{ name: "kernel", kind: "normal" }, { name: "cli", kind: "dev" }] }],
]);
const unit = (pkg, name, kind, test, sources) =>
  ({ pkg, name, kind: [kind], test, executable: test ? `/t/${name}` : null, sources: new Set(sources), line: name });
const units = [
  unit("kernel", "kernel", "lib", false, ["crates/kernel/src/lib.rs", "lib/std/prelude.hthr"]),
  unit("cli", "cli", "lib", false, ["crates/cli/src/lib.rs", "crates/cli/src/loader.rs"]),
  unit("cli", "heather", "bin", false, ["crates/cli/src/main.rs", "crates/cli/src/native.rs"]),
  unit("cli", "gate", "test", true, ["crates/cli/tests/gate.rs"]),
  unit("elab", "nat", "test", true, ["crates/elab/tests/nat.rs", "lib/std/nat.hthr"]),
  unit("elab", "list", "test", true, ["crates/elab/tests/list.rs", "lib/std/nat.hthr", "lib/std/list.hthr"]),
];
const sources = { "crates/cli/tests/gate.rs": "let s = std::fs::read_to_string(root.join(\"lib\"));" };
const readSource = (f) => sources[f] ?? "";
const pick = (changed) => {
  const r = selectTargets({ changed, units, packages, readSource });
  return r.all ? `all: ${r.reason}` : [...r.selected.keys()].map((k) => k.slice(3)).sort().join(" ");
};

test("dep-info names every input, escaped spaces kept", () => {
  assert.deepEqual(parseDepInfo("/t/x: crates/a/src/lib.rs lib/a\\ b.hthr\n\ncrates/a/src/lib.rs:\n"),
    ["crates/a/src/lib.rs", "lib/a b.hthr"]);
  assert.equal(repoPath("crates/kernel-lib/../kernel/src/lib.rs", "/w"), "crates/kernel/src/lib.rs");
  assert.equal(repoPath("/home/u/.cargo/registry/x.rs", "/w"), null);
});

test("dev dependencies reach only the test's own package", () => {
  assert.deepEqual([...reach("elab", packages)].sort(), ["cli", "elab", "kernel"]);
  assert.deepEqual([...reach("cli", packages)].sort(), ["cli", "kernel"]);
});

test("a library module selects the tests that embed it and the run-time readers", () => {
  assert.equal(pick(["lib/std/list.hthr"]), "gate list");
  assert.equal(pick(["lib/std/nat.hthr"]), "gate list nat");
  // Compiled into the kernel library every test links.
  assert.equal(pick(["lib/std/prelude.hthr"]), "gate list nat");
  // A probe no binary embeds: only the reader.
  assert.equal(pick(["lib/_tests/std/nat_tests.hthr"]), "gate");
  assert.equal(pick(["examples/x.hthr"]), "gate");
});

test("Rust sources select through the dependency graph", () => {
  assert.equal(pick(["crates/kernel/src/lib.rs"]), "gate list nat");
  assert.equal(pick(["crates/cli/src/loader.rs"]), "gate list nat");
  // A binary's source is its own package's tests', not a dependent's.
  assert.equal(pick(["crates/cli/src/native.rs"]), "gate");
  assert.equal(pick(["crates/elab/tests/nat.rs"]), "nat");
});

test("files no .d names fall back by where they are", () => {
  // A fixture: its crate's tests and the run-time readers.
  assert.equal(pick(["crates/elab/tests/fixtures/a.hthr"]), "gate list nat");
  assert.equal(pick(["crates/cli/tests/fixtures/a.hthr"]), "gate");
  // A manifest or a file not yet declared: the crate and its dependents.
  assert.equal(pick(["crates/kernel/Cargo.toml"]), "gate list nat");
  assert.equal(pick(["crates/cli/src/new.rs"]), "gate list nat");
  // Bench data: only a reader of that crate.
  assert.equal(pick(["crates/kernel/benches/baseline.tsv"]), "");
  // Nothing reads these.
  assert.equal(pick(["docs/a.md", "issues/b.md", "crates/kernel/DESIGN.md", "scripts/perf"]), "");
  assert.equal(pick(["docs/showcase/a.hthr"]), "gate");
});

test("what cannot be placed runs everything", () => {
  assert.equal(pick(["Cargo.lock"]), "all: Cargo.lock");
  assert.equal(pick(["docs/a.md", "scripts/test"]), "all: scripts/test");
  assert.equal(pick(["somewhere/new.txt"]), "all: somewhere/new.txt");
  assert.equal(pick(["crates/new-crate/src/lib.rs"]), "all: crates/new-crate/src/lib.rs");
});

test("a family binary splits into members by the modules they name", () => {
  const files = {
    "crates/elab/tests/families/logic.rs": `#[path = "../support/mod.rs"]\nmod support;\n#[path = "../support/x86_prefix.rs"]\nmod common;\n` +
      `#[path = "../a.rs"]\nmod a;\n#[path = "../b.rs"]\nmod b;\n#[path = "../c.rs"]\nmod c;\n`,
    "crates/elab/tests/support/mod.rs": "pub mod parser;\nfn shared() {}\n",
    "crates/elab/tests/support/parser.rs": `const P: &str = include_str!("../../../../lib/std/parser.hthr");`,
    "crates/elab/tests/support/x86_prefix.rs": `const X: &str = include_str!("../../../../lib/std/x86.hthr");`,
    "crates/elab/tests/a.rs": `use crate::common::X;\nconst A: &str = include_str!("../../../lib/std/a.hthr");`,
    "crates/elab/tests/b.rs": "use crate::a::A;\nuse crate::support::parser;\n",
    "crates/elab/tests/c.rs": "fn c() {}",
  };
  const family = unit("elab", "family_logic", "test", true, [...Object.keys(files),
    "lib/std/parser.hthr", "lib/std/x86.hthr", "lib/std/a.hthr", "lib/std/unknown.hthr"]);
  const members = familyMembers(family, (f) => files[f] ?? null);
  const inputs = Object.fromEntries(members.map((m) => [m.member, [...m.sources].filter((f) => f.startsWith("lib/")).sort()]));
  // `b` names `a` (and so `common`) and support's `parser`; `c` names
  // nothing. A file no module owns (`unknown`) is everyone's.
  assert.deepEqual(inputs, {
    common: ["lib/std/unknown.hthr", "lib/std/x86.hthr"],
    a: ["lib/std/a.hthr", "lib/std/unknown.hthr", "lib/std/x86.hthr"],
    b: ["lib/std/a.hthr", "lib/std/parser.hthr", "lib/std/unknown.hthr", "lib/std/x86.hthr"],
    c: ["lib/std/unknown.hthr"],
  });
  const r = selectTargets({ changed: ["lib/std/parser.hthr"], units: [family], packages, readSource: (f) => files[f] ?? "" });
  assert.deepEqual([...r.selected.keys()], ["/t/family_logic#b"]);
});

test("units read their .d beside each artifact", () => {
  const msg = { reason: "compiler-artifact", package_id: "path+file:///w/crates/elab#heather-elab@0.0.1",
    executable: "/w/target/debug/deps/nat-abc", profile: { test: true },
    target: { name: "nat", kind: ["test"], src_path: "/w/crates/elab/tests/nat.rs" }, filenames: ["/w/target/debug/deps/nat-abc"] };
  const lib = { reason: "compiler-artifact", package_id: "path+file:///w/crates/kernel-lib#heather-kernel-lib@0.0.1",
    executable: null, profile: { test: false },
    target: { name: "heather_kernel", kind: ["lib"], src_path: "/w/crates/kernel-lib/../kernel/src/lib.rs" },
    filenames: ["/w/target/debug/deps/libheather_kernel-def.rlib"] };
  const registry = { ...lib, package_id: "registry+https://x#libc@0.2.0" };
  const d = {
    "/w/target/debug/deps/nat-abc.d": "/w/target/debug/deps/nat-abc: crates/elab/tests/nat.rs crates/elab/tests/../../../lib/std/nat.hthr\n",
    "/w/target/debug/deps/heather_kernel-def.d": "x: crates/kernel-lib/../kernel/src/lib.rs /home/u/.cargo/registry/y.rs\n",
  };
  const found = parseUnits([msg, lib, registry].map((m) => JSON.stringify(m)).join("\n"), "/w", (p) => d[p] ?? null);
  assert.deepEqual(found.map((u) => [u.pkg, [...u.sources]]), [
    ["heather-elab", ["crates/elab/tests/nat.rs", "lib/std/nat.hthr"]],
    ["heather-kernel-lib", ["crates/kernel/src/lib.rs"]],
  ]);
});

test("the runner keeps the selected members and doc-test packages", () => {
  const members = parseMembers("family_logic\ta\trun\nfamily_logic\tb\tskip\nfamily_logic\tc\trun\n\n");
  // `d` is a shard the selector did not know of: it runs.
  const shards = [{ name: "a" }, { name: "b" }, { name: "c" }, { name: "d" }];
  assert.deepEqual(selectShards(shards, members.get("family_logic")).map((s) => s.name), ["a", "c", "d"]);
  assert.equal(selectShards(shards, members.get("family_other")).length, 4);
  assert.deepEqual(docTestArgs(null, ["--format", "terse"]),
    ["test", "--workspace", "--exclude", "heather-elab-unit", "--doc", "--", "--format", "terse"]);
  assert.deepEqual(docTestArgs(["*"], []), ["test", "--workspace", "--exclude", "heather-elab-unit", "--doc", "--"]);
  assert.deepEqual(docTestArgs(["heather-cli", "heather-elab-unit"], []), ["test", "-p", "heather-cli", "--doc", "--"]);
  assert.equal(docTestArgs([], []), null);
});
