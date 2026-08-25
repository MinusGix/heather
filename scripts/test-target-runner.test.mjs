import test from "node:test";
import assert from "node:assert/strict";
import { jobBounds, parseArtifacts, parseResults, targetIncomplete } from "./run-test-targets.mjs";

test("artifact discovery keeps test-profile executables once", () => {
  const artifact = { reason: "compiler-artifact", executable: "/tmp/example", profile: { test: true },
    package_id: "path+file:///work/crates/elab#heather-elab@0.0.1",
    target: { name: "surface", kind: ["test"], src_path: "/work/crates/elab/tests/surface.rs" } };
  const found = parseArtifacts(`${JSON.stringify(artifact)}\n${JSON.stringify(artifact)}\nnot json`, "/work");
  assert.deepEqual(found, [{ executable: "/tmp/example", name: "surface",
    label: "crates/elab/tests/surface.rs", exclusive: false }]);
});

test("libtest summaries aggregate exactly", () => {
  const result = parseResults("test result: ok. 4 passed; 1 failed; 2 ignored; 0 measured; 0 filtered out; finished in 1.25s\n" +
    "test result: ok. 3 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.50s\n");
  assert.deepEqual(result, { passed: 7, failed: 1, ignored: 2, duration: 1.75, resultLines: 2 });
});

test("automatic job bound reserves host memory and two CPUs per child", () => {
  const tenFree = "MemTotal: 33554432 kB\nMemAvailable: 10485760 kB\n";
  const thirtyFree = "MemTotal: 67108864 kB\nMemAvailable: 31457280 kB\n";
  assert.equal(jobBounds("auto", tenFree, 16).jobs, 2);
  assert.equal(jobBounds("auto", thirtyFree, 16).jobs, 7);
  assert.equal(jobBounds("auto", thirtyFree, 8).jobs, 3);
  assert.equal(jobBounds("8", "", 16).jobs, 1);
  assert.equal(jobBounds("auto", thirtyFree, 16, String(16 * 1024 ** 3), String(2 * 1024 ** 3)).jobs, 3);
});

test("ordinary failures are red but only missing summaries are incomplete", () => {
  assert.equal(targetIncomplete({ code: 101, signal: null, result: { resultLines: 1 } }), false);
  assert.equal(targetIncomplete({ code: null, signal: "SIGKILL", result: { resultLines: 0 } }), true);
  assert.equal(targetIncomplete({ code: 1, signal: null, result: { resultLines: 0 } }), true);
});
