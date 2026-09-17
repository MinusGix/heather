import test from "node:test";
import assert from "node:assert/strict";
import { CPU_MARKER, collect, jobBounds, limitedCommand, parseArtifacts, parseCpu, parseResults, targetIncomplete } from "./run-test-targets.mjs";

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
