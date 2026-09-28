set -u
cd "$(dirname "$0")/.."
FILES="crates/elab/src/gendefs.rs crates/elab/src/inductive.rs crates/elab/src/stats.rs crates/elab/src/wf.rs docs/instrumentation-design.md"
mkdir -p probes/tcf_new
for f in $FILES; do mkdir -p "probes/tcf_new/$(dirname $f)"; cp "$f" "probes/tcf_new/$f"; done
echo "== parent tree: save baseline $(date +%T)"
for f in $FILES; do cp "probes/tcf_base/$f" "$f"; done
scripts/bench --save 2>&1 | tail -15
echo "== save rc=$? $(date +%T)"
echo "== changed tree: check $(date +%T)"
for f in $FILES; do cp "probes/tcf_new/$f" "$f"; done
scripts/bench --check 2>&1 | tail -40
echo "== check rc=$? $(date +%T)"
echo "== MARKER done $(date +%T)"
