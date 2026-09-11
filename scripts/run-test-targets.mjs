#!/usr/bin/env node
// Run Cargo-built libtest executables with bounded target-level concurrency.
// scripts/test owns compilation and invokes this helper only for unfiltered
// workspace runs. Keep policy (limits, lanes, doctests) there; this file owns
// scheduling, buffered output, and exact result accounting.

import { spawn } from "node:child_process";
import { appendFileSync, readFileSync, writeFileSync } from "node:fs";
import { availableParallelism } from "node:os";
import { fileURLToPath } from "node:url";

// Per-child address-space cap (`ulimit -v`): the machine-protection rail.
// 6 GiB since 2026-09-11, when the default of eight kernel workers took the
// x86 certificate builds to ~3.2 GB peak RSS (4 GiB was the first guess).
const LIMIT_KIB = 6 * 1024 * 1024;
// Per-child working-set budget the job count is planned against. Smaller
// than the cap on purpose: the cap is what one runaway child may reach, the
// budget is what the heaviest well-behaved one does reach (3.2 GB peak). A
// box where every job hit the cap at once would still oversubscribe, which
// is the trade for not halving the job count on a 32 GB box.
const BUDGET_KIB = 3 * 1024 * 1024;
const RESERVE_KIB = 2 * 1024 * 1024;
const OUTPUT_LIMIT = 1024 * 1024;

export function parseArtifacts(text, root = process.cwd()) {
  const seen = new Set();
  const artifacts = [];
  for (const line of text.split("\n")) {
    if (!line.trim()) continue;
    let msg;
    try { msg = JSON.parse(line); } catch { continue; }
    if (msg.reason !== "compiler-artifact" || !msg.executable || !msg.profile?.test) continue;
    if (seen.has(msg.executable)) continue;
    seen.add(msg.executable);
    const src = msg.target.src_path.startsWith(`${root}/`)
      ? msg.target.src_path.slice(root.length + 1)
      : msg.target.src_path;
    const packageName = String(msg.package_id).split("#").at(-1).split("@")[0];
    artifacts.push({
      executable: msg.executable,
      name: msg.target.name,
      label: msg.target.kind.includes("test") ? src : `${packageName} (${src})`,
      // Exclusive targets run alone, after the parallel phase: the bench
      // smoke needs a quiet box to time, and the two-placement native
      // summary gate sits within 25% of the 300 s CPU rail when run alone
      // and tips over it under suite contention
      // (issues/native-summary-test-cpu-margin.md).
      exclusive: EXCLUSIVE_TARGETS.has(msg.target.name),
    });
  }
  return artifacts;
}

export const EXCLUSIVE_TARGETS = new Set(["frontend_bench_smoke", "native_summary"]);

export function parseResults(text) {
  const total = { passed: 0, failed: 0, ignored: 0, duration: 0, resultLines: 0 };
  const re = /^test result: \w+\. (\d+) passed; (\d+) failed; (\d+) ignored;.*finished in ([0-9.]+)s$/gm;
  for (const match of text.matchAll(re)) {
    total.passed += Number(match[1]);
    total.failed += Number(match[2]);
    total.ignored += Number(match[3]);
    total.duration += Number(match[4]);
    total.resultLines++;
  }
  return total;
}

export function jobBounds(requested, meminfo, cores, cgroupMax = "", cgroupCurrent = "") {
  const available = /MemAvailable:\s+(\d+)\s+kB/.exec(meminfo);
  let availableKib = available ? Number(available[1]) : null;
  const groupMaxBytes = /^\d+$/.test(cgroupMax.trim()) ? Number(cgroupMax.trim()) : null;
  const groupCurrentBytes = /^\d+$/.test(cgroupCurrent.trim()) ? Number(cgroupCurrent.trim()) : null;
  if (groupMaxBytes !== null) {
    if (groupCurrentBytes !== null) {
      const groupAvailableKib = Math.max(0, Math.floor((groupMaxBytes - groupCurrentBytes) / 1024));
      availableKib = availableKib === null ? groupAvailableKib : Math.min(availableKib, groupAvailableKib);
    }
  }
  const memoryJobs = availableKib !== null
    ? Math.max(1, Math.floor((availableKib - RESERVE_KIB) / BUDGET_KIB))
    : 1;
  // libtest itself gets two threads, so don't create more runnable test
  // threads than the CPUs the process is actually allowed to use. One
  // two-thread slot remains free for the editor and other foreground work.
  const cpuJobs = Math.max(1, Math.floor(cores / 2) - 1);
  const requestedJobs = requested === "auto" ? cpuJobs : Number(requested);
  if (!Number.isInteger(requestedJobs) || requestedJobs < 1) {
    throw new Error("--jobs must be `auto` or a positive integer");
  }
  return {
    jobs: Math.max(1, Math.min(requestedJobs, memoryJobs, cpuJobs)),
    requestedJobs,
    memoryJobs,
    cpuJobs,
    reserveKib: RESERVE_KIB,
    automatic: requested === "auto",
  };
}

export function targetIncomplete(run) {
  return Boolean(run.signal) || run.code === null || run.result.resultLines !== 1;
}

function limitedCommand(command, args, env = {}) {
  return spawn("bash", ["--noprofile", "--norc", "-c",
    `ulimit -v ${LIMIT_KIB}; ulimit -t 300; exec \"$@\"`,
    "heather-test-target", command, ...args], {
    cwd: process.cwd(),
    env: { ...process.env, RUST_MIN_STACK: "8388608", RUST_TEST_THREADS: "2", ...env },
    stdio: ["ignore", "pipe", "pipe"],
  });
}

function collect(child) {
  return new Promise((resolve) => {
    let output = "";
    let truncated = false;
    const append = (chunk) => {
      const text = chunk.toString();
      if (output.length < OUTPUT_LIMIT) {
        const room = OUTPUT_LIMIT - output.length;
        output += text.slice(0, room);
        if (text.length > room) truncated = true;
      }
      else truncated = true;
    };
    child.stdout.on("data", append);
    child.stderr.on("data", append);
    child.on("error", (error) => resolve({ code: null, signal: null, output: `${output}\n${error}\n`, truncated }));
    child.on("close", (code, signal) => resolve({ code, signal, output, truncated }));
  });
}

// The file is an append-only history: one row per (run, target), oldest run
// first (`docs/instrumentation-design.md` §5). Scheduling wants the *latest*
// row per target, which is what a forward pass leaves in the map. Rows written
// before the `run` column existed have two fields and still read.
function loadHistory(path) {
  const timings = new Map();
  try {
    for (const line of readFileSync(path, "utf8").split("\n")) {
      const fields = line.split("\t");
      const [seconds, label] = fields.length >= 3 ? fields.slice(1, 3) : fields;
      if (label) timings.set(label, Number(seconds));
    }
  } catch {}
  return timings;
}

// Cap the history so an append-only file cannot grow without bound; keeping
// the tail keeps the latest run per target, which is all scheduling reads.
function trimHistory(path, keepLines) {
  try {
    const lines = readFileSync(path, "utf8").split("\n").filter((line) => line.length);
    if (lines.length > keepLines) {
      writeFileSync(path, lines.slice(lines.length - keepLines).join("\n") + "\n");
    }
  } catch {}
}

function readOwnCgroupValue(name) {
  try {
    const entry = readFileSync("/proc/self/cgroup", "utf8")
      .split("\n").find((line) => line.startsWith("0::"));
    const path = entry?.slice(3);
    if (!path?.startsWith("/")) return "";
    return readFileSync(`/sys/fs/cgroup${path}/${name}`, "utf8");
  } catch {
    return "";
  }
}

async function runTargets(targets, jobs, libtestArgs, keepGoing) {
  const pending = [...targets];
  const completed = [];
  let active = 0;
  let failed = false;
  return new Promise((resolve) => {
    const pump = () => {
      if ((!pending.length || (failed && !keepGoing)) && active === 0) return resolve(completed);
      while (active < jobs && pending.length && !(failed && !keepGoing)) {
        if (pending[0].exclusive && active > 0) break;
        const target = pending.shift();
        if (target.exclusive && active !== 0) { pending.unshift(target); break; }
        active++;
        process.stdout.write(`[start ${completed.length + active}/${targets.length}] ${target.label}${target.exclusive ? " (exclusive)" : ""}\n`);
        const started = process.hrtime.bigint();
        collect(limitedCommand(target.executable, libtestArgs)).then((run) => {
          run.wall = Number(process.hrtime.bigint() - started) / 1e9;
          run.target = target;
          run.result = parseResults(run.output);
          if (run.code !== 0 || run.signal || run.result.resultLines !== 1) failed = true;
          completed.push(run);
          active--;
          process.stdout.write(`[done  ${completed.length}/${targets.length}] ${target.label} (${run.wall.toFixed(2)}s)\n`);
          pump();
        });
        if (target.exclusive) break;
      }
    };
    pump();
  });
}

function merge(total, result) {
  for (const key of ["passed", "failed", "ignored", "duration", "resultLines"]) total[key] += result[key];
}

async function main() {
  const args = process.argv.slice(2);
  const take = (flag) => {
    const index = args.indexOf(flag);
    if (index < 0 || index + 1 === args.length) throw new Error(`missing ${flag}`);
    return args.splice(index, 2)[1];
  };
  const manifest = take("--manifest");
  const timingsPath = take("--timings");
  const jobsRequested = take("--jobs");
  const keepGoingIndex = args.indexOf("--keep-going");
  const keepGoing = keepGoingIndex >= 0;
  if (keepGoing) args.splice(keepGoingIndex, 1);
  const sep = args.indexOf("--");
  const libtestArgs = sep < 0 ? [] : args.slice(sep + 1);
  let meminfo = "";
  try { meminfo = readFileSync("/proc/meminfo", "utf8"); } catch {}
  const cgroupMax = readOwnCgroupValue("memory.max");
  const cgroupCurrent = readOwnCgroupValue("memory.current");
  const bounds = jobBounds(jobsRequested, meminfo, availableParallelism(), cgroupMax, cgroupCurrent);
  const jobs = bounds.jobs;
  const history = loadHistory(timingsPath);
  const targets = parseArtifacts(readFileSync(manifest, "utf8"));
  targets.sort((a, b) => {
    if (a.exclusive !== b.exclusive) return a.exclusive ? 1 : -1;
    return (history.get(b.label) ?? 0) - (history.get(a.label) ?? 0) || a.label.localeCompare(b.label);
  });
  if (!targets.length) throw new Error("Cargo manifest contained no test executables");
  console.log(`\n== test targets: ${targets.length} binaries, ${jobs}-way bound (${jobs * LIMIT_KIB / 1024 / 1024} GiB maximum child address space) ==`);
  const reserveGib = (bounds.reserveKib / 1024 / 1024).toFixed(1);
  if (bounds.automatic) {
    console.log(`automatic bound: memory ${bounds.memoryJobs}, CPU ${bounds.cpuJobs}; reserving ${reserveGib} GiB for the host`);
  } else if (jobs < bounds.requestedJobs) {
    console.log(`requested ${bounds.requestedJobs} jobs, reduced to ${jobs} by memory/CPU bounds; reserving ${reserveGib} GiB for the host`);
  }

  const runs = await runTargets(targets, jobs, libtestArgs, keepGoing);
  // Complete target blocks are emitted in stable label order, never interleaved.
  runs.sort((a, b) => a.target.label.localeCompare(b.target.label));
  for (const run of runs) {
    console.log(`\n     Running ${run.target.label}`);
    process.stdout.write(run.output);
    if (run.output && !run.output.endsWith("\n")) process.stdout.write("\n");
    if (run.truncated) console.log(`[output truncated after ${OUTPUT_LIMIT} bytes]`);
    if (run.signal || run.code !== 0 || run.result.resultLines !== 1) {
      console.log(`[target exit: code=${run.code ?? "none"}, signal=${run.signal ?? "none"}, result-lines=${run.result.resultLines}]`);
    }
  }

  const total = { passed: 0, failed: 0, ignored: 0, duration: 0, resultLines: 0 };
  let incomplete = runs.length !== targets.length;
  for (const run of runs) {
    merge(total, run.result);
    if (targetIncomplete(run)) incomplete = true;
  }

  // Cargo remains responsible for doctest discovery. Its rustdoc children
  // inherit the same rails, and Cargo runs this phase serially.
  console.log("\n== doc tests (serial) ==");
  const doc = await collect(limitedCommand("cargo", ["test", "--workspace", "--doc", "--", ...libtestArgs]));
  process.stdout.write(doc.output);
  const docResult = parseResults(doc.output);
  merge(total, docResult);
  if (doc.signal || docResult.resultLines === 0 || (doc.code !== 0 && docResult.failed === 0)) incomplete = true;

  const timingRows = runs.map((run) => [run.result.duration || run.wall, run.target.label]);
  timingRows.push([docResult.duration, "doc-tests"]);
  timingRows.sort((a, b) => b[0] - a[0]);
  console.log("\n== slowest test targets (reported test time) ==");
  const visible = timingRows.filter(([seconds]) => seconds >= 1).slice(0, 20);
  if (!visible.length) console.log("  (no target took at least 1 second)");
  for (const [seconds, label] of visible) console.log(`${seconds.toFixed(2).padStart(8)}s  ${label}`);
  console.log(`reported target time: ${timingRows.reduce((sum, row) => sum + row[0], 0).toFixed(2)}s across ${total.resultLines} targets`);
  const runId = new Date().toISOString();
  appendFileSync(timingsPath, runs.map((run) => `${runId}\t${(run.result.duration || run.wall).toFixed(3)}\t${run.target.label}`).join("\n") + "\n");
  trimHistory(timingsPath, 4000);

  if (incomplete) {
    console.log(`\n== suite: INCOMPLETE (${total.passed} passed before death, ${total.failed} failed) ==`);
    process.exitCode = 1;
  } else {
    console.log(`\n== suite: ${total.passed} passed, ${total.failed} failed, ${total.ignored} ignored ==`);
    process.exitCode = total.failed || runs.some((run) => run.code !== 0) ? 1 : 0;
  }
}

if (process.argv[1] && fileURLToPath(import.meta.url) === process.argv[1]) {
  main().catch((error) => { console.error(`test target runner: ${error.message}`); process.exit(2); });
}
