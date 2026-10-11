import test from "node:test";
import assert from "node:assert/strict";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { CPU_MARKER, collect, completionMessage, familyShards, jobBounds, limitedCommand, listingArgs, parseArtifacts, parseCpu, parseResults, parseTestTimes, runTargets, shardTestName, targetIncomplete, targetOutcome, timedLibtestArgs } from "./run-test-targets.mjs";

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
  assert.equal(jobBounds("auto", thirtyFree, 4).jobs, 2);
  assert.equal(jobBounds("auto", thirtyFree, 2).jobs, 1);
  assert.equal(jobBounds("8", "", 16).jobs, 1);
  assert.equal(jobBounds("auto", thirtyFree, 16, String(16 * 1024 ** 3), String(2 * 1024 ** 3)).jobs, 4);
});

test("ordinary failures are red but only missing summaries are incomplete", () => {
  assert.equal(targetIncomplete({ code: 101, signal: null, result: { resultLines: 1 } }), false);
  assert.equal(targetIncomplete({ code: null, signal: "SIGKILL", result: { resultLines: 0 } }), true);
  assert.equal(targetIncomplete({ code: 1, signal: null, result: { resultLines: 0 } }), true);
});

test("immediate outcomes distinguish passes, failures, termination and incomplete summaries", () => {
  const pass = { code: 0, signal: null, result: { resultLines: 1, passed: 4, failed: 0, ignored: 2 } };
  assert.equal(targetOutcome(pass), "PASS (4 passed, 2 ignored)");
  assert.equal(targetOutcome({ ...pass, code: 101, result: { ...pass.result, failed: 1 } }), "FAIL (exit=101, 1 failed)");
  assert.equal(targetOutcome({ ...pass, code: 1 }), "FAIL (exit=1, 0 failed)");
  assert.equal(targetOutcome({ ...pass, result: { ...pass.result, failed: 1 } }), "FAIL (exit=0, 1 failed)");
  // A signal wins even if the child printed a complete-looking summary.
  assert.equal(targetOutcome({ ...pass, code: null, signal: "SIGKILL" }), "TERMINATED (signal=SIGKILL)");
  assert.equal(targetOutcome({ ...pass, code: null }), "INCOMPLETE (exit=none, result-lines=1)");
  for (const resultLines of [0, 2]) {
    assert.equal(targetOutcome({ ...pass, result: { ...pass.result, resultLines } }),
      `INCOMPLETE (exit=0, result-lines=${resultLines})`);
  }
});

test("completion output bounds failure excerpts and makes truncation visible", () => {
  const run = { code: 101, signal: null, target: { label: "example.rs" }, wall: 1.25, cpu: 2.5,
    result: { resultLines: 1, passed: 3, failed: 1, ignored: 0 }, truncated: false,
    output: "running 4 tests\nfailures:\nthread 'bad' panicked: expected 3, got 4\n" + "x".repeat(200) + "\n" + "detail\n".repeat(30) };
  const message = completionMessage(run, 2, 5);
  assert.match(message, /^\[done  2\/5\] example.rs: FAIL \(exit=101, 1 failed\) \(1.25s, 2.5 CPU-s\)\n/);
  assert.match(message, /expected 3, got 4/);
  assert.match(message, /… buffered log follows after targets finish/);
  assert.ok(message.length < 1600);
  assert.ok(message.split("\n").every((line) => line.length <= 164));
  assert.equal(run.output.split("detail").length, 31, "the grouped log is retained");
  const truncated = completionMessage({ ...run, code: 0, cpu: null, truncated: true,
    result: { ...run.result, resultLines: 0 }, output: "prefix\n" + "noise\n".repeat(100) }, 1, 1);
  assert.match(truncated, /INCOMPLETE/);
  assert.match(truncated, /output truncated after 1048576 bytes/);
  assert.ok(truncated.length < 1600);
  const pass = completionMessage({ ...run, code: 0, output: "ok\n", result: { ...run.result, failed: 0 } }, 1, 1);
  assert.match(pass, /PASS/);
  assert.equal(pass.split("\n").length, 2, "passing completions are one line");
});

test("a killed child gets an immediate signal outcome and available context", async () => {
  const run = await collect(limitedCommand("bash", ["-c", "echo before-kill; kill -9 $$"]));
  const { cpu, output } = parseCpu(run.output);
  const message = completionMessage({ ...run, cpu, output, result: parseResults(output),
    wall: 0.1, target: { label: "killed.rs" } }, 1, 1);
  assert.match(message, /TERMINATED \(signal=SIGKILL\)/);
  assert.match(message, /before-kill/);
});

test("failure reporting arrives while another target is running and keep-going schedules the rest", async () => {
  const dir = mkdtempSync(join(tmpdir(), "heather-outcomes-"));
  const write = process.stdout.write;
  try {
    const gate = join(dir, "release-slow");
    const summary = "test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.01s";
    const targets = [
      { label: "slow.rs", executable: "bash", args: ["-c",
        'for ((i=0; i<500; i++)); do if [[ -f "$1" ]]; then printf "%s\\n" "$2"; exit 0; fi; sleep 0.01; done; exit 1', "slow", gate, summary] },
      { label: "failed.rs", executable: "bash", args: ["-c",
        'printf "%s\\n" "failures:" "thread bad panicked: expected 3, got 4" "test result: FAILED. 0 passed; 1 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.01s"; exit 101'] },
      { label: "later.rs", executable: "bash", args: ["-c", 'printf "%s\\n" "$1"', "later", summary] },
    ];
    let received = "";
    let immediate = false;
    process.stdout.write = function(chunk, ...args) {
      const message = chunk.toString();
      if (!/^\[(start|done )/.test(message)) return write.call(this, chunk, ...args);
      received += message;
      if (message.includes("failed.rs: FAIL")) {
        immediate = !received.includes("slow.rs: PASS");
        writeFileSync(gate, "release\n");
      }
      return true;
    };
    const runs = await runTargets(targets, 2, [], true);
    assert.ok(immediate, received);
    assert.match(received, /expected 3, got 4/);
    assert.match(received, /later.rs: PASS/);
    assert.match(received, /slow.rs: PASS/);
    assert.equal(runs.length, 3);
    assert.match(runs.find((run) => run.target.label === "failed.rs").output, /expected 3, got 4/);
    received = "";
    const stopped = await runTargets(targets.slice(1), 1, [], false);
    assert.equal(stopped.length, 1, "fail-fast still stops scheduling after a failure");
    assert.match(received, /failed.rs: FAIL/);
    assert.ok(!received.includes("later.rs"));
  } finally {
    process.stdout.write = write;
    rmSync(dir, { recursive: true, force: true });
  }
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
