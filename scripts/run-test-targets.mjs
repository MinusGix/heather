#!/usr/bin/env node
// Run Cargo-built libtest executables with bounded target-level concurrency.
// scripts/test owns compilation and invokes this helper only for unfiltered
// workspace runs. Keep policy (limits, lanes, doctests) there; this file owns
// scheduling, buffered output, and exact result accounting.

import { execFile, execFileSync, spawn } from "node:child_process";
import { appendFileSync, mkdirSync, readdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { availableParallelism } from "node:os";
import { basename, dirname, normalize, resolve } from "node:path";
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
// The child's CPU rail, in seconds (`ulimit -t` in limitedCommand). Recorded
// next to every target's CPU time so a target drifting toward it is visible
// in the history before the day it crosses and SIGKILLs
// (issues/test-runner-records-no-per-target-cpu.md).
const CPU_RAIL_SECONDS = 300;
const CPU_WARN_FRACTION = 0.5;
// Targets whose every test spawns one `heather write-elf` of a whole tool,
// each its own process under the rail it inherits: the compile by kernel
// evaluation and the certificate's kernel check, over warm images, at width
// one. sort's sits at the rail on an idle cloud box (about 300–345 CPU-s at
// both 2026-11-02 and 2026-11-04 master, byte-identical ELF), tac's just
// under, and a slower box takes several more across: the 2026-11-03 and
// 2026-11-04 master reds (issues/native-sort-gate-rail.md). They keep the
// address-space cap; the CPU rail is three times the default until a cheaper
// certificate brings the tools back under it.
export const CPU_RAIL_OVERRIDES = new Map([["native_cat", 900], ["native_tools", 900]]);
export function cpuRail(name) { return CPU_RAIL_OVERRIDES.get(name) ?? CPU_RAIL_SECONDS; }

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
    // Normalized: crates/elab-unit's lib is `../elab/src/lib.rs` from its
    // own manifest directory, and the label should name the file.
    const srcPath = normalize(msg.target.src_path);
    const src = srcPath.startsWith(`${root}/`) ? srcPath.slice(root.length + 1) : srcPath;
    // `heather-kernel-lib` is `heather-kernel`'s library split into a package
    // of its own (crates/kernel-lib/Cargo.toml, for the opt-level); its unit
    // tests keep the label, and so the timing history, they had before.
    const packageName = String(msg.package_id).split("#").at(-1).split("@")[0].replace(/-lib$/, "");
    artifacts.push({
      executable: msg.executable,
      name: msg.target.name,
      label: msg.target.kind.includes("test") ? src : `${packageName} (${src})`,
      // Exclusive targets run alone, after the parallel phase: the bench
      // smoke needs a quiet box to time.
      exclusive: EXCLUSIVE_TARGETS.has(msg.target.name),
    });
  }
  return artifacts;
}

export const EXCLUSIVE_TARGETS = new Set(["frontend_bench_smoke"]);

// Targets whose run builds a store other targets read, each with the targets
// that read it. The library gate (crates/cli/tests/library.rs) builds the CLI
// image store, and native_cat/native_tools's `write-elf` replays its closure
// from it (every module is keyed by its own closure,
// docs/module-dag-design.md); cold, one `write-elf` would build that closure
// itself, past the CPU rail. So a prerequisite starts first and its readers
// wait, while every other target fills the slots it leaves idle. A
// prerequisite the run does not hold blocks nothing.
//
// A reader needs only the images its own loads replay, not the whole gate:
// `built` names the folders whose loads cover them (every file the native
// targets hand to `write-elf` is in one, and `write-elf`'s fixed imports,
// `WRITE_ELF_IMPORTS`, are in lib/native's closure), and `store` the image
// store. While the prerequisite runs, the runner asks `heather check
// --unbuilt` (BuildPlan, docs/module-dag-design.md §12: image headers only,
// nothing elaborated) every PROBE_SECONDS, and releases the readers as soon
// as nothing there is unbuilt; if that never happens they start when the
// prerequisite finishes, pass or fail, as before. Warm, the first probe
// releases them.
// scripts/test used to run the gate alone as a warmup before this phase and
// then again here as a test (issues/library-gate-warmup-runs-alone.md).
// `built` is mirrored by the library gate's `--build-first` (crates/cli/tests/library.rs).
export const PREREQUISITES = new Map([["library", {
  readers: ["native_cat", "native_tools"],
  built: ["lib/native", "lib/_tests/native"],
  store: "cli-check-images",
}]]);
const PROBE_SECONDS = 10;

// Schedule order: prerequisites first, exclusive targets last, the rest
// slowest-first by the latest history; each target gets `after`, the
// prerequisites in this run it waits for.
export function orderTargets(targets, history = new Map()) {
  const present = new Set(targets.map((t) => t.name));
  const waits = new Map();
  for (const [before, { readers }] of PREREQUISITES) {
    if (!present.has(before)) continue;
    for (const reader of readers) waits.set(reader, [...(waits.get(reader) ?? []), before]);
  }
  const ordered = targets.map((t) => ({ ...t, after: waits.get(t.name) ?? [] }));
  const rank = (t) => (t.exclusive ? 2 : PREREQUISITES.has(t.name) ? 0 : 1);
  ordered.sort((a, b) => rank(a) - rank(b)
    || (history.get(b.label) ?? 0) - (history.get(a.label) ?? 0) || a.label.localeCompare(b.label));
  return ordered;
}

// The `heather` binary the test targets run (`CARGO_BIN_EXE_heather`): the
// manifest's non-test artifact of the bin target, or null.
export function binaryOf(text, name) {
  for (const line of text.split("\n")) {
    let msg;
    try { msg = JSON.parse(line); } catch { continue; }
    if (msg.reason === "compiler-artifact" && msg.executable && !msg.profile?.test
      && msg.target?.name === name && msg.target.kind.includes("bin")) return msg.executable;
  }
  return null;
}

// The probe's command: the modules of `built`'s loads that `store` has no
// image of, under the lane's image policy (the gate's and `write-elf`'s).
// `store` names a store beneath target/, or beneath $HEATHER_CACHE_DIR when it
// is set, as the gate's own path does (heather_cache::store_root).
export function probeArgs({ built, store }, env = process.env) {
  const stale = env.HEATHER_SEMANTIC_IMAGES === "accept-stale" ? ["--accept-stale-images"] : [];
  return ["check", "--cache-dir", storePath(store, env), ...stale, "--unbuilt", ...built];
}

export function storePath(store, env = process.env) {
  return `${env.HEATHER_CACHE_DIR || "target"}/${store}`;
}

// Resolves to true when the probe found nothing unbuilt (exit 0); a refusal,
// a crash or a missing binary is not ready.
function probe(heather, prerequisite) {
  return new Promise((resolve) => {
    execFile(heather, probeArgs(prerequisite), { cwd: process.cwd(), maxBuffer: 1024 * 1024, timeout: 120_000,
      env: { ...process.env, HEATHER_KERNEL_WORKERS: "1" } }, (error) => resolve(!error));
  });
}

// A family binary (`family_*`, crates/elab/Cargo.toml) links several test
// files into one executable to save the links, not to share a process: it
// runs as one shard per member file, and a shard is scheduled, railed,
// timed and labelled exactly as that file's own binary was
// (docs/elab-test-families-design.md §D3). The member is the test name's
// first `::` segment, because the family mounts each file as a module named
// after its stem, next to the family's own directory.
//
// `listing` is the binary's `--list --format terse` output under the lane's
// own `--skip`s, so a member whose every test is skipped yields no shard (its
// binary used to run and report 0 passed). The shard then selects its tests
// by `--exact` name: a `member::` substring filter would also catch another
// member's nested module of the same name. Under `--exact` libtest matches
// `--skip` exactly too, which is why the skips are applied at listing time.
export function familyShards(artifact, listing) {
  const groups = new Map();
  for (const line of listing.split("\n")) {
    const m = /^(\S+): test$/.exec(line);
    if (!m) continue;
    const cut = m[1].indexOf("::");
    if (cut < 0) throw new Error(`${artifact.label}: test \`${m[1]}\` is not in a member module`);
    const member = m[1].slice(0, cut);
    if (!groups.has(member)) groups.set(member, []);
    groups.get(member).push(m[1]);
  }
  const dir = dirname(dirname(artifact.label));
  return [...groups].map(([member, names]) => ({
    executable: artifact.executable,
    name: member,
    label: `${dir}/${member}.rs`,
    exclusive: EXCLUSIVE_TARGETS.has(member),
    family: artifact.name,
    args: ["--exact", ...names],
  }));
}

export function isFamily(artifact) {
  return artifact.name.startsWith("family_");
}

// libtest options that decide which tests exist for a listing: the lane's
// skips. Everything else (`--format`, thread counts) is for the run.
export function listingArgs(libtestArgs) {
  const out = [];
  for (let i = 0; i < libtestArgs.length; i++) {
    if (libtestArgs[i] === "--skip" && i + 1 < libtestArgs.length) out.push("--skip", libtestArgs[++i]);
  }
  return out;
}

// `members` (the pr lane's selection, scripts/affected-targets.mjs) maps a
// family to the members it chose to skip. A shard it does not name runs:
// the selector only skips what it knows the inputs of.
function expandFamilies(artifacts, libtestArgs, members = new Map()) {
  return artifacts.flatMap((artifact) => {
    if (!isFamily(artifact)) return [artifact];
    const listing = execFileSync(artifact.executable, ["--list", "--format", "terse", ...listingArgs(libtestArgs)],
      { encoding: "utf8", maxBuffer: 16 * 1024 * 1024 });
    return selectShards(familyShards(artifact, listing), members.get(artifact.name));
  });
}

export function selectShards(shards, skip) {
  return skip ? shards.filter((shard) => !skip.has(shard.name)) : shards;
}

// `family\tmember\trun|skip` lines, kept as each family's skipped members.
export function parseMembers(text) {
  const members = new Map();
  for (const line of text.split("\n")) {
    const [family, member, verdict] = line.split("\t");
    if (!family || !member || verdict !== "skip") continue;
    if (!members.has(family)) members.set(family, new Set());
    members.get(family).add(member);
  }
  return members;
}

// The doc-test phase's command: every package (`*`), the listed ones, or
// none (null) when the pr lane's selection left out every package.
export function docTestArgs(packages, libtestArgs) {
  const tail = ["--doc", "--", ...libtestArgs];
  if (packages === null || packages.includes("*")) return ["test", "--workspace", "--exclude", "heather-elab-unit", ...tail];
  const named = packages.filter((p) => p !== "heather-elab-unit");
  return named.length ? ["test", ...named.flatMap((p) => ["-p", p]), ...tail] : null;
}

// A shard's per-test rows keep the names its file's own binary reported, so
// test-times history stays continuous across the merge.
export function shardTestName(target, name) {
  return target.family && name.startsWith(`${target.name}::`) ? name.slice(target.name.length + 2) : name;
}

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

// Per-test seconds inside each binary. A target's one number says which
// binary is slow, not which test, and the suite's time hides in there: a
// slow test, a shared prefix replay the first test pays, a binary of a
// thousand cheap tests. libtest reports a time per test only through
// `--report-time`, which is unstable and prints only in the pretty format,
// so the runner asks for exactly that (`RUSTC_BOOTSTRAP=1` in the *test
// binary's* environment enables libtest's own option parsing; nothing is
// compiled differently) and turns the output back into terse's shape:
// passing and ignored lines are dropped, failures kept. HEATHER_TEST_TIMES=0
// runs the binaries plain terse, as before.
export const TEST_TIMES = process.env.HEATHER_TEST_TIMES !== "0";
// HEATHER_SUITE_DECLS=1 goes one level further down: every test thread writes
// its declaration rows (the `--timings` table) to target/suite-decls-<lane>/
// through HEATHER_TIMINGS_DIR (crates/elab/src/stats.rs), and the directory
// is stamped with the run it belongs to. Off by default — collection costs a
// little per declaration and a few thousand files — and read by
// `scripts/perf snapshot`.
export const SUITE_DECLS = process.env.HEATHER_SUITE_DECLS === "1";
export function timedLibtestArgs(args) {
  const out = [...args];
  const i = out.indexOf("--format");
  if (i >= 0 && out[i + 1] === "terse") out.splice(i, 2, "--format", "pretty", "-Z", "unstable-options", "--report-time");
  return out;
}
export function parseTestTimes(text) {
  const tests = [];
  const kept = [];
  const re = /^test (\S+) \.\.\. (ok|FAILED|ignored)(?:, [^<]*)?(?: <([0-9.]+)s>)?$/;
  for (const line of text.split("\n")) {
    const m = re.exec(line);
    if (!m) { kept.push(line); continue; }
    tests.push([m[1], m[3] === undefined ? null : Number(m[3]), m[2]]);
    if (m[2] === "FAILED") kept.push(line);
  }
  return { tests, output: kept.join("\n") };
}

// The wrapper's CPU line: seconds of user+sys the child and its threads
// spent, or null when the wrapper never got to print it. The line is removed
// from the returned output so libtest's own text stays as it was.
export function parseCpu(text) {
  const re = new RegExp(`^${CPU_MARKER} user=([0-9.]+) sys=([0-9.]+)\\n?`, "m");
  const match = re.exec(text);
  if (!match) return { cpu: null, output: text };
  return { cpu: Number(match[1]) + Number(match[2]), output: text.replace(re, "") };
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
  // two-thread slot remains free for the editor and other foreground work
  // on a box of eight or more CPUs; below that the slot would be half the
  // box or more (a 4-CPU cloud container ran the whole suite one target at
  // a time, issues/suite-iteration-chokepoints-2026-10.md). Below eight CPUs
  // the bound is three children per four CPUs instead: a child's second test
  // thread is mostly idle (kernel width one, and most targets wait on one
  // shared base), so two children kept a 4-CPU box ~2.5 CPUs busy, and a
  // third cut the warm full lane's test wall by about a quarter at the same
  // CPU (issues/suite-full-lane-cost-2026-10.md); a fourth bought nothing.
  const cpuJobs = Math.max(1, cores >= 8 ? Math.floor(cores / 2) - 1 : Math.floor(cores * 3 / 4));
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

export function targetOutcome(run) {
  if (run.signal) return `TERMINATED (signal=${run.signal})`;
  if (targetIncomplete(run)) return `INCOMPLETE (exit=${run.code ?? "none"}, result-lines=${run.result.resultLines})`;
  if (run.code !== 0 || run.result.failed) return `FAIL (exit=${run.code}, ${run.result.failed} failed)`;
  return `PASS (${run.result.passed} passed, ${run.result.ignored} ignored)`;
}

// One write per completion keeps concurrent targets' messages together. The
// excerpt is bounded even when a panic prints a huge term; the buffered logs
// still follow in label order when all scheduled targets have finished.
export function completionMessage(run, completed, total) {
  const cpu = run.cpu === null ? "" : `, ${run.cpu.toFixed(1)} CPU-s`;
  const lines = [`[done  ${completed}/${total}] ${run.target.label}: ${targetOutcome(run)} (${run.wall.toFixed(2)}s${cpu})`];
  if (targetIncomplete(run) || run.code !== 0 || run.result.failed) {
    const output = run.output.split("\n").filter((line) => line.trim());
    const start = output.findIndex((line) => /^(failures:|thread .*panicked|test .*\.\.\. FAILED|error[:\[])/.test(line));
    const excerpt = start < 0 ? output.slice(-8) : output.slice(start, start + 8);
    for (const line of excerpt) lines.push(`  | ${line.length > 160 ? line.slice(0, 159) + "…" : line}`);
    if (output.length > excerpt.length || excerpt.some((line) => line.length > 160)) {
      lines.push("  | … buffered log follows after targets finish");
    }
  }
  if (run.truncated) lines.push(`  | output truncated after ${OUTPUT_LIMIT} bytes`);
  for (const p of processesNearRail(run).slice(0, 3)) {
    lines.push(`  | process at ${Math.round(100 * p.cpu / p.rail)}% of its ${p.rail} s CPU rail: ${p.cpu.toFixed(1)} CPU-s, ${p.command}`);
  }
  return lines.join("\n") + "\n";
}

// Kernel-gate width for a suite child. The default is eight
// (`HEATHER_KERNEL_WORKERS`, crates/elab/src/pool.rs), which is right for one
// interactive `heather check` on an idle box and wrong underneath a scheduler
// that is already running children in parallel: the job bound below budgets
// TWO CPUs per child ("libtest gets two threads"), and that arithmetic is only
// true if each test thread is itself serial. At the default width a child is
// 2 x 8 = 16 runnable threads, so a 7-way bound oversubscribes a 16-core box
// about 7x — and the CPU rail counts every one of those threads.
//
// Measured on `heather-cli (crates/cli/src/main.rs)`, the target this was
// found on (2026-09-17, 16 cores, idle box, the runner's own invocation):
//
//     test threads x workers     wall      CPU (user+sys)
//     2 x 8 (the default)        43.7 s    274.5 s
//     1 x 8                      54.5 s    191.5 s
//     2 x 1                      65.4 s    123.0 s
//     1 x 1                     110.0 s    109.4 s
//
// The work is ~109 CPU-s; the other 165 s at the default width is contention.
// That inflation, not the tests, is what took the target past `ulimit -t 300`
// and made a full run unable to go green at all
// (issues/native-summary-test-cpu-margin.md).
//
// Width one puts the parallelism where it is bounded — at the runner, which
// counts it — instead of multiplying it underneath. No coverage moves: every
// pool test names its own width (`with_workers`, crates/elab/tests/kernel_pool.rs)
// and the CLI's width tests spawn subprocesses with the variable removed or
// set, deliberately (crates/cli/tests/kernel_workers.rs). An explicitly set
// `HEATHER_KERNEL_WORKERS` still wins, so isolating one item at a chosen width
// works as documented.
const KERNEL_WORKERS = process.env.HEATHER_KERNEL_WORKERS ?? "1";

// The wrapper stays the child's parent instead of exec'ing it so that bash's
// `time` can report the child's CPU (user+sys, every thread — the quantity
// `ulimit -t` kills on; wall is not proportional to it for a multi-threaded
// child). The line is parsed out of the output by `parseCpu`. A child that
// died of a signal is re-raised on the wrapper, so the runner still sees
// `signal=SIGKILL` for a rail kill exactly as it did with `exec`.
export const CPU_MARKER = "heather-test-target-cpu";
export function limitedCommand(command, args, env = {}, rail = CPU_RAIL_SECONDS) {
  return spawn("bash", ["--noprofile", "--norc", "-c",
    `ulimit -v ${LIMIT_KIB}; ulimit -t ${rail}; ` +
    `TIMEFORMAT='${CPU_MARKER} user=%U sys=%S'; time \"$@\"; s=$?; ` +
    `if (( s > 128 )); then kill -$((s - 128)) $$; fi; exit $s`,
    "heather-test-target", command, ...args], {
    cwd: process.cwd(),
    env: {
      ...process.env,
      RUST_MIN_STACK: "8388608",
      RUST_TEST_THREADS: "2",
      HEATHER_KERNEL_WORKERS: KERNEL_WORKERS,
      ...env,
    },
    stdio: ["ignore", "pipe", "pipe"],
  });
}

// Per-process CPU (issues/test-cpu-rail-child-accounting.md). `ulimit -t`
// is a rail on each process: every `heather` a test spawns inherits its own
// copy, so a target's CPU (the wrapper's `time`, summed over its children)
// says nothing about how close one child came to being killed. native_tools
// reports thousands of CPU-s as a target and is never killed as one, while
// one `write-elf` child per test sits at its own rail; the 2026-11-03,
// 2026-11-04 and 2026-11-06 master reds were each such a child, unreported
// until it died. So the runner samples /proc: every process below a target's
// wrapper, its own user+sys (all its threads, not its children: what its
// rail counts), keeping each one's last reading. Sampled, so a process that
// lives under one interval can be missed and the last interval before an
// exit is not counted; the processes this is for live for minutes. Linux
// only: elsewhere nothing is sampled and nothing is reported.
export const PROCESS_WARN_FRACTION = 0.6;
const PROCESS_SAMPLE_MS = 2000;

// One /proc/<pid>/stat line: the parent, the start time (a pid is reused,
// pid and start are not), and user+sys in clock ticks. The command name sits
// in parentheses and may hold spaces or parentheses itself, so the fields
// are read after the last `)`.
export function parseProcStat(text) {
  const close = text.lastIndexOf(")");
  if (close < 0) return null;
  const fields = text.slice(close + 2).trim().split(/\s+/);
  // After the name: state(3) ppid(4) … utime(14) stime(15) … starttime(22).
  if (fields.length < 20) return null;
  return { ppid: Number(fields[1]), ticks: Number(fields[11]) + Number(fields[12]), start: fields[19] };
}

// A process's command, short: its program's file name and its first
// arguments, so `heather compile-x86 examples/x86-native/branches.hthr
// nested_true` reads as that.
export function shortCommand(argv, limit = 120) {
  if (!argv.length) return "?";
  const text = [basename(argv[0]), ...argv.slice(1, 5)].join(" ");
  return text.length > limit ? text.slice(0, limit - 1) + "…" : text;
}

function clockTicks() {
  try { return Number(execFileSync("getconf", ["CLK_TCK"], { encoding: "utf8" }).trim()) || 100; } catch { return 100; }
}

export class ProcessSampler {
  constructor({ proc = "/proc", intervalMs = PROCESS_SAMPLE_MS } = {}) {
    this.proc = proc;
    this.intervalMs = intervalMs;
    this.enabled = process.platform === "linux";
    this.ticks = this.enabled ? clockTicks() : 100;
    this.roots = new Map(); // root pid -> Map(key -> { pid, command, cpu, root })
    this.timer = null;
  }

  watch(pid) {
    if (!this.enabled || !pid) return;
    this.roots.set(pid, new Map());
    if (!this.timer) {
      this.timer = setInterval(() => this.sample(), this.intervalMs);
      this.timer.unref();
    }
    this.sample();
  }

  // The processes seen below `pid` (and `pid` itself), busiest first, each
  // `{ command, cpu }` in seconds; the root is marked `root: true`.
  stop(pid) {
    const seen = this.roots.get(pid);
    this.roots.delete(pid);
    if (!this.roots.size && this.timer) { clearInterval(this.timer); this.timer = null; }
    if (!seen) return [];
    return [...seen.values()].sort((a, b) => b.cpu - a.cpu);
  }

  sample() {
    if (!this.roots.size) return;
    const stats = new Map();
    let entries;
    try { entries = readdirSync(this.proc); } catch { return; }
    for (const entry of entries) {
      if (!/^\d+$/.test(entry)) continue;
      let stat;
      try { stat = parseProcStat(readFileSync(`${this.proc}/${entry}/stat`, "utf8")); } catch { continue; }
      if (stat) stats.set(Number(entry), stat);
    }
    const children = new Map();
    for (const [pid, { ppid }] of stats) children.set(ppid, [...(children.get(ppid) ?? []), pid]);
    for (const [root, seen] of this.roots) {
      const queue = [root];
      while (queue.length) {
        const pid = queue.pop();
        const stat = stats.get(pid);
        if (!stat) continue;
        queue.push(...(children.get(pid) ?? []));
        const key = `${pid}:${stat.start}`;
        let entry = seen.get(key);
        if (!entry) {
          let argv = [];
          try { argv = readFileSync(`${this.proc}/${pid}/cmdline`, "utf8").split("\0").filter(Boolean); } catch {}
          entry = { pid, command: shortCommand(argv), cpu: 0, root: pid === root };
          seen.set(key, entry);
        }
        entry.cpu = Math.max(entry.cpu, stat.ticks / this.ticks);
      }
    }
  }
}

// The processes of a run past `fraction` of the rail each one had.
export function processesNearRail(run, fraction = PROCESS_WARN_FRACTION) {
  const rail = cpuRail(run.target.name);
  return (run.processes ?? []).filter((p) => p.cpu >= fraction * rail).map((p) => ({ ...p, rail }));
}

export function collect(child) {
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

// `ready(prerequisite)` resolves to whether its readers may start before it
// finishes (`probe` over the manifest's `heather`; none, they never do),
// asked every `probeSeconds`.
export async function runTargets(targets, jobs, libtestArgs, keepGoing, extraEnv = {}, ready = null, probeSeconds = PROBE_SECONDS, sampler = new ProcessSampler()) {
  const pending = [...targets];
  const completed = [];
  const finished = new Set();
  // Prerequisites whose readers were released before they finished.
  const released = new Set();
  const probing = new Set();
  const timers = new Set();
  let active = 0;
  let failed = false;
  return new Promise((resolve) => {
    // Ask again in `probeSeconds` while `name` runs and a reader still waits.
    const watch = (name) => {
      if (!ready || probing.has(name) || !PREREQUISITES.get(name)?.built) return;
      probing.add(name);
      const ask = async () => {
        const waiting = () => !finished.has(name) && !released.has(name)
          && pending.some((t) => (t.after ?? []).includes(name));
        if (!waiting()) return;
        if (await ready(name) && waiting()) {
          released.add(name);
          const readers = pending.filter((t) => (t.after ?? []).includes(name)).map((t) => t.name);
          process.stdout.write(`[ready] ${name}: ${PREREQUISITES.get(name).built.join(", ")} built; ${readers.join(", ")} may start\n`);
          pump();
          return;
        }
        const timer = setTimeout(() => { timers.delete(timer); ask(); }, probeSeconds * 1000);
        timers.add(timer);
      };
      ask();
    };
    const pump = () => {
      if ((!pending.length || (failed && !keepGoing)) && active === 0) {
        for (const timer of timers) clearTimeout(timer);
        return resolve(completed);
      }
      while (active < jobs && pending.length && !(failed && !keepGoing)) {
        // The first target whose prerequisites have finished or released it;
        // with nothing running and nothing ready, the head, so a cycle
        // cannot hang.
        let index = pending.findIndex((t) => (t.after ?? []).every((name) => finished.has(name) || released.has(name)));
        if (index < 0 && active === 0) index = 0;
        if (index < 0) break;
        if (pending[index].exclusive && active > 0) break;
        const [target] = pending.splice(index, 1);
        active++;
        if (PREREQUISITES.has(target.name)) watch(target.name);
        process.stdout.write(`[start ${completed.length + active}/${targets.length}] ${target.label}${target.exclusive ? " (exclusive)" : ""}\n`);
        const started = process.hrtime.bigint();
        const args = [...libtestArgs, ...(target.args ?? [])];
        const command = TEST_TIMES
          ? limitedCommand(target.executable, timedLibtestArgs(args), { RUSTC_BOOTSTRAP: "1", ...extraEnv }, cpuRail(target.name))
          : limitedCommand(target.executable, args, extraEnv, cpuRail(target.name));
        sampler.watch(command.pid);
        collect(command).then((run) => {
          run.processes = sampler.stop(command.pid);
          run.wall = Number(process.hrtime.bigint() - started) / 1e9;
          run.target = target;
          ({ cpu: run.cpu, output: run.output } = parseCpu(run.output));
          ({ tests: run.tests, output: run.output } = TEST_TIMES ? parseTestTimes(run.output) : { tests: [], output: run.output });
          run.result = parseResults(run.output);
          if (run.code !== 0 || run.signal || run.result.resultLines !== 1) failed = true;
          completed.push(run);
          finished.add(target.name);
          active--;
          process.stdout.write(completionMessage(run, completed.length, targets.length));
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
  const optional = (flag) => (args.includes(flag) ? take(flag) : null);
  const membersPath = optional("--members");
  const docPackagesPath = optional("--doc-packages");
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
  const artifacts = parseArtifacts(readFileSync(manifest, "utf8"));
  const members = membersPath ? parseMembers(readFileSync(membersPath, "utf8")) : new Map();
  const targets = orderTargets(expandFamilies(artifacts, libtestArgs, members), history);
  // The pr lane's selection may leave a family no member its skips keep.
  if (!targets.length && !membersPath) throw new Error("Cargo manifest contained no test executables");
  console.log(`\n== test targets: ${targets.length} (${artifacts.length} binaries), ${jobs}-way bound (${jobs * LIMIT_KIB / 1024 / 1024} GiB maximum child address space) ==`);
  const reserveGib = (bounds.reserveKib / 1024 / 1024).toFixed(1);
  if (bounds.automatic) {
    console.log(`automatic bound: memory ${bounds.memoryJobs}, CPU ${bounds.cpuJobs}; reserving ${reserveGib} GiB for the host`);
  } else if (jobs < bounds.requestedJobs) {
    console.log(`requested ${bounds.requestedJobs} jobs, reduced to ${jobs} by memory/CPU bounds; reserving ${reserveGib} GiB for the host`);
  }

  const declsDir = SUITE_DECLS
    ? (timingsPath.includes("test-target-timings-") ? timingsPath.replace("test-target-timings-", "suite-decls-").replace(/\.tsv$/, "") : `${timingsPath}.decls`)
    : null;
  if (declsDir) {
    rmSync(declsDir, { recursive: true, force: true });
    mkdirSync(declsDir, { recursive: true });
    console.log(`declaration rows per test thread go to ${declsDir}/ (HEATHER_SUITE_DECLS)`);
  }
  const heather = binaryOf(readFileSync(manifest, "utf8"), "heather");
  const ready = heather ? (name) => probe(heather, PREREQUISITES.get(name)) : null;
  const runs = await runTargets(targets, jobs, libtestArgs, keepGoing,
    declsDir ? { HEATHER_TIMINGS_DIR: resolve(declsDir) } : {}, ready);
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
  // `heather-elab-unit` is elab's sources again, for its unit tests only
  // (`doctest = false`, which `--doc` does not honour): documenting it would
  // compile a second full O3 rlib of the elaborator after every elab edit,
  // for no doc test (issues/suite-iteration-chokepoints-2026-10.md).
  const docPackages = docPackagesPath ? readFileSync(docPackagesPath, "utf8").split("\n").filter(Boolean) : null;
  const docArgs = docTestArgs(docPackages, libtestArgs);
  const timingRows = runs.map((run) => [run.result.duration || run.wall, run.target.label, run.cpu]);
  if (docArgs) {
    console.log("\n== doc tests (serial) ==");
    const doc = await collect(limitedCommand("cargo", docArgs));
    process.stdout.write(doc.output);
    const docResult = parseResults(doc.output);
    merge(total, docResult);
    if (doc.signal || docResult.resultLines === 0 || (doc.code !== 0 && docResult.failed === 0)) incomplete = true;
    timingRows.push([docResult.duration, "doc-tests", parseCpu(doc.output).cpu]);
  } else {
    console.log("\n== doc tests: none selected ==");
  }
  timingRows.sort((a, b) => b[0] - a[0]);
  console.log(`\n== slowest test targets (reported test time; CPU = user+sys of the target and all its children, summed, against the ${CPU_RAIL_SECONDS} s per-process rail) ==`);
  const visible = timingRows.filter(([seconds]) => seconds >= 1).slice(0, 20);
  if (!visible.length) console.log("  (no target took at least 1 second)");
  const cpuCell = (cpu) => cpu === null || cpu === undefined
    ? "".padStart(16)
    : `${cpu.toFixed(1).padStart(7)} CPU-s ${Math.round(100 * cpu / CPU_RAIL_SECONDS).toString().padStart(3)}%`;
  for (const [seconds, label, cpu] of visible) console.log(`${seconds.toFixed(2).padStart(8)}s ${cpuCell(cpu)}  ${label}`);
  console.log(`reported target time: ${timingRows.reduce((sum, row) => sum + row[0], 0).toFixed(2)}s across ${total.resultLines} targets; ` +
    `CPU ${timingRows.reduce((sum, row) => sum + (row[2] ?? 0), 0).toFixed(1)}s`);
  // The margin nobody could see before: a target past half the rail is
  // named, every run, so its drift has a history before it becomes a kill.
  const nearRail = timingRows.filter(([, , cpu]) => cpu !== null && cpu !== undefined && cpu >= CPU_WARN_FRACTION * CPU_RAIL_SECONDS);
  if (nearRail.length) {
    console.log(`== targets whose summed CPU is past ${Math.round(100 * CPU_WARN_FRACTION)}% of one process's rail (a sum, not a margin: see the processes section) ==`);
    for (const [, label, cpu] of nearRail) console.log(`${cpu.toFixed(1).padStart(8)} CPU-s ${Math.round(100 * cpu / CPU_RAIL_SECONDS).toString().padStart(3)}%  ${label}`);
  }
  // What the rail actually kills: one process past its own share, whatever
  // its target sums to (issues/test-cpu-rail-child-accounting.md).
  const busy = runs.flatMap((run) => processesNearRail(run).map((p) => ({ ...p, label: run.target.label })))
    .sort((a, b) => b.cpu / b.rail - a.cpu / a.rail);
  if (busy.length) {
    console.log(`== processes past ${Math.round(100 * PROCESS_WARN_FRACTION)}% of their own CPU rail (each process has its own; sampled every ${PROCESS_SAMPLE_MS / 1000} s) ==`);
    for (const p of busy) {
      console.log(`${p.cpu.toFixed(1).padStart(8)} CPU-s ${Math.round(100 * p.cpu / p.rail).toString().padStart(3)}% of ${p.rail} s  ${p.label}: ${p.command}`);
    }
  }
  const runId = new Date().toISOString();
  if (declsDir) writeFileSync(`${declsDir}/run.txt`, `${runId}\n`);
  // Row: run, reported seconds, label, CPU seconds (empty when unknown).
  // Older rows have two or three fields and still read (`loadHistory`).
  appendFileSync(timingsPath, runs.map((run) =>
    `${runId}\t${(run.result.duration || run.wall).toFixed(3)}\t${run.target.label}\t${run.cpu === null ? "" : run.cpu.toFixed(3)}`).join("\n") + "\n");
  trimHistory(timingsPath, 4000);
  if (TEST_TIMES) {
    // The latest run only, overwritten: `scripts/perf snapshot` is what keeps
    // a dated copy. Beside the target history, one per lane.
    const testsPath = timingsPath.includes("test-target-timings-")
      ? timingsPath.replace("test-target-timings-", "test-times-") : `${timingsPath}.tests`;
    const rows = runs.flatMap((run) => run.tests.map(([name, seconds, status]) =>
      `${runId}\t${run.target.label}\t${shardTestName(run.target, name)}\t${seconds === null ? "" : seconds.toFixed(3)}\t${status}`));
    writeFileSync(testsPath, "run\ttarget\ttest\tseconds\tstatus\n" + rows.join("\n") + "\n");
    const slowest = runs.flatMap((run) => run.tests.filter(([, s]) => s !== null).map(([name, s]) => [s, `${run.target.label}::${shardTestName(run.target, name)}`]))
      .sort((a, b) => b[0] - a[0]).slice(0, 15);
    if (slowest.length) {
      console.log(`== slowest tests (seconds inside their binary; all ${rows.length} in ${testsPath}) ==`);
      for (const [seconds, name] of slowest) console.log(`${seconds.toFixed(2).padStart(8)}s  ${name}`);
    }
  }

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
