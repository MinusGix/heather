# Round 2026-09-15 part A, job 3: `scripts/bench --check` against a baseline
# saved on the parent in this same job, then the **full** `scripts/test`
# (not the fast lane: the change is in a generator and the fast lane replays
# images an earlier build wrote).
#
# The remote checkout is not a git repository, so the parent column is the
# file swap of `probes/s4_base/` (see `probes/README.md`).
set -u
cd "$(dirname "$0")/.."
NEW=$(mktemp -d)
cp crates/elab/src/gendefs.rs crates/elab/src/wf.rs "$NEW/"
put_base () { cp probes/s4_base/gendefs.rs crates/elab/src/gendefs.rs; cp probes/s4_base/wf.rs crates/elab/src/wf.rs; }
put_new  () { cp "$NEW/gendefs.rs" crates/elab/src/gendefs.rs; cp "$NEW/wf.rs" crates/elab/src/wf.rs; }

echo "== bench --save on the parent $(date +%T)"
put_base
scripts/bench --save 2>&1 | tail -6
echo "== bench --check on part A $(date +%T)"
put_new
scripts/bench --check 2>&1 | tail -25
echo "== bench rc above $(date +%T)"

echo "== full scripts/test $(date +%T)"
scripts/test > /tmp/s4suite.log 2>&1
echo "== scripts/test rc=$? $(date +%T)"
grep -n '^== suite:' /tmp/s4suite.log
echo "== failing targets / tests"
grep -nE '^(failures:|test result: FAILED|error: test failed|error: [0-9]+ targets? failed)' /tmp/s4suite.log | head -40
echo "== failure names"
awk '/^failures:$/{f=1;next} f&&/^    /{print} f&&/^$/{f=0}' /tmp/s4suite.log | sort -u | head -40
echo "== panic lines"
grep -nE "panicked at|assertion .*failed|left ==|^---- " /tmp/s4suite.log | head -60
echo "== x86 rails / native gates"
grep -nE 'function_ir_x86_scaling|caller_native_memory_same_2[78]|native_summary' /tmp/s4suite.log | head -20
echo "== MARKER done $(date +%T)"
