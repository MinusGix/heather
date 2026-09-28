set -u
cd "$(dirname "$0")/.."
FILES="crates/elab/src/gendefs.rs crates/elab/src/inductive.rs crates/elab/src/stats.rs crates/elab/src/wf.rs docs/instrumentation-design.md"
echo "== targeted tests $(date +%T)"
scripts/test --fast -p heather-elab --lib stale_template 2>&1 | tail -25
echo "== targeted done $(date +%T)"

mkdir -p probes/tcf_new
for f in $FILES; do mkdir -p "probes/tcf_new/$(dirname $f)"; cp "$f" "probes/tcf_new/$f"; done
echo "== bench save on parent tree $(date +%T)"
for f in $FILES; do cp "probes/tcf_base/$f" "$f"; done
scripts/bench --save 2>&1 | tail -8
echo "== save done $(date +%T)"
echo "== bench check on changed tree $(date +%T)"
for f in $FILES; do cp "probes/tcf_new/$f" "$f"; done
scripts/bench --check 2>&1 | tail -30
echo "== check done $(date +%T)"

echo "== full suite $(date +%T)"
scripts/test 2>&1 | tail -40
echo "== suite done $(date +%T)"
echo "== MARKER done $(date +%T)"
