import test from "node:test";
import assert from "node:assert/strict";
import { CPU_MARKER, collect, familyShards, jobBounds, limitedCommand, listingArgs, parseArtifacts, parseCpu, parseResults, parseTestTimes, shardTestName, targetIncomplete, timedLibtestArgs } from "./run-test-targets.mjs";

test("artifact discovery keeps test-profile executables once", () => {
  const artifact = { reason: "compiler-artifact", executable: "/tmp/example", profile: { test: true },
    package_id: "path+file:///work/crates/elab#heather-elab@0.0.1",
    target: { name: "surface", kind: ["test"], src_path: "/work/crates/elab/tests/surface.rs" } };
  const found = parseArtifacts(`${JSON.stringify(artifact)}\n${JSON.stringify(artifact)}\nnot json`, "/work");
  assert.deepEqual(found, [{ executable: "/tmp/example", name: "surface",
    label: "crates/elab/tests/surface.rs", exclusive: false }]);
  const summary = { ...artifact, executable: "/tmp/summary",
    target: { name: "native_summary", kind: ["test"], src_path: "/work/crates/cli/tests/native_summary.rs" } };
  assert.equal(parseArtifacts(JSON.stringify(summary), "/work")[0].exclusive, true);
});

test("a family binary runs as one shard per member file, labelled as that file", () => {
  const family = { executable: "/tmp/family", name: "family_library",
    label: "crates/elab/tests/families/library.rs", exclusive: false };
  // `lib_std_tree`'s only test was skipped at listing time, so it is absent
  // here and gets no shard; `frontend_bench_smoke` keeps its exclusivity.
  const listing = "lib_std_list::a: test\nlib_std_list::nested::b: test\n" +
    "frontend_bench_smoke::smoke: test\nlib_std_int::c: test\nlib_std_list::d: bench\n\n";
  assert.deepEqual(familyShards(family, listing), [
    { executable: "/tmp/family", name: "lib_std_list", label: "crates/elab/tests/lib_std_list.rs",
      exclusive: false, family: "family_library", args: ["--exact", "lib_std_list::a", "lib_std_list::nested::b"] },
    { executable: "/tmp/family", name: "frontend_bench_smoke", label: "crates/elab/tests/frontend_bench_smoke.rs",
      exclusive: true, family: "family_library", args: ["--exact", "frontend_bench_smoke::smoke"] },
    { executable: "/tmp/family", name: "lib_std_int", label: "crates/elab/tests/lib_std_int.rs",
      exclusive: false, family: "family_library", args: ["--exact", "lib_std_int::c"] },
  ]);
  assert.throws(() => familyShards(family, "stray: test\n"), /not in a member module/);
  // Only the skips decide the listing; under `--exact` they would match
  // whole names only.
  assert.deepEqual(listingArgs(["--format", "terse", "--skip", "slow_acceptance_", "--skip", "x"]),
    ["--skip", "slow_acceptance_", "--skip", "x"]);
  const shard = familyShards(family, listing)[0];
  assert.equal(shardTestName(shard, "lib_std_list::nested::b"), "nested::b");
  assert.equal(shardTestName({ name: "surface" }, "surface::x"), "surface::x");
});

test("libtest summaries aggregate exactly", () => {
  const result = parseResults("test result: ok. 4 passed; 1 failed; 2 ignored; 0 measured; 0 filtered out; finished in 1.25s\n" +
    "test result: ok. 3 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.50s\n");
  assert.deepEqual(result, { passed: 7, failed: 1, ignored: 2, duration: 1.75, resultLines: 2 });
});

test("automatic job bound reserves host memory and two CPUs per child", () => {
  // Memory plans against BUDGET_KIB (3 GiB per child), not the 6 GiB cap:
  // 10 GiB free - 2 GiB reserve = 8 GiB -> 2 jobs; a 16 GiB cgroup with
  // 2 GiB used -> 14 - 2 = 12 GiB -> 4 jobs.
  const tenFree = "MemTotal: 33554432 kB\nMemAvailable: 10485760 kB\n";
  const thirtyFree = "MemTotal: 67108864 kB\nMemAvailable: 31457280 kB\n";
  assert.equal(jobBounds("auto", tenFree, 16).jobs, 2);
  assert.equal(jobBounds("auto", thirtyFree, 16).jobs, 7);
  assert.equal(jobBounds("auto", thirtyFree, 8).jobs, 3);
  assert.equal(jobBounds("8", "", 16).jobs, 1);
  assert.equal(jobBounds("auto", thirtyFree, 16, String(16 * 1024 ** 3), String(2 * 1024 ** 3)).jobs, 4);
});

test("ordinary failures are red but only missing summaries are incomplete", () => {
  assert.equal(targetIncomplete({ code: 101, signal: null, result: { resultLines: 1 } }), false);
  assert.equal(targetIncomplete({ code: null, signal: "SIGKILL", result: { resultLines: 0 } }), true);
  assert.equal(targetIncomplete({ code: 1, signal: null, result: { resultLines: 0 } }), true);
});

test("the wrapper's CPU line is summed and removed from the child's output", () => {
  const libtest = "test result: ok. 4 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 1.25s\n";
  const parsed = parseCpu(`${libtest}${CPU_MARKER} user=43.250 sys=1.500\n`);
  assert.equal(parsed.cpu, 44.75);
  assert.equal(parsed.output, libtest);
  assert.deepEqual(parseCpu(libtest), { cpu: null, output: libtest });
});

test("the limited wrapper reports CPU, keeps the exit code, and re-raises a signal", async () => {
  const plain = await collect(limitedCommand("bash", ["-c", "echo out; exit 3"]));
  assert.equal(plain.code, 3);
  assert.equal(plain.signal, null);
  const parsed = parseCpu(plain.output);
  assert.equal(typeof parsed.cpu, "number");
  assert.equal(parsed.output, "out\n");
  // A rail kill reaches the child as SIGKILL; the wrapper dies of the same
  // signal so the runner's `signal=SIGKILL` diagnosis is unchanged — and the
  // CPU the child burnt before the kill is still reported, which is the
  // number a rail kill wants on record.
  const killed = await collect(limitedCommand("bash", ["-c", "kill -9 $$"]));
  assert.equal(killed.signal, "SIGKILL");
  assert.equal(typeof parseCpu(killed.output).cpu, "number");
});

test("per-test times come from the pretty format and leave terse's shape behind", () => {
  assert.deepEqual(timedLibtestArgs(["--format", "terse", "--skip", "slow_acceptance"]),
    ["--format", "pretty", "-Z", "unstable-options", "--report-time", "--skip", "slow_acceptance"]);
  assert.deepEqual(timedLibtestArgs(["--skip", "x"]), ["--skip", "x"]);
  const text = "\nrunning 3 tests\ntest a::fast ... ok <0.013s>\ntest slow ... FAILED <2.500s>\n" +
    "test skipped ... ignored, needs furnace\ntest b has been running for over 60 seconds\n\nfailures:\n" +
    "test result: FAILED. 1 passed; 1 failed; 1 ignored; 0 measured; 0 filtered out; finished in 2.52s\n";
  const { tests, output } = parseTestTimes(text);
  assert.deepEqual(tests, [["a::fast", 0.013, "ok"], ["slow", 2.5, "FAILED"], ["skipped", null, "ignored"]]);
  assert.ok(!output.includes("a::fast") && output.includes("test slow ... FAILED") && output.includes("has been running"));
  assert.equal(parseResults(output).failed, 1);
});

test("the limited wrapper hands the child its extra environment", async () => {
  // Stable libtest honours -Z unstable-options only when the test binary's
  // own environment carries RUSTC_BOOTSTRAP; this checks the wrapper passes it.
  const run = await collect(limitedCommand("bash", ["-c", "echo $RUSTC_BOOTSTRAP"], { RUSTC_BOOTSTRAP: "1" }));
  assert.match(run.output, /^1$/m);
});
