set -u
cd "$(dirname "$0")/.."
FILES="crates/elab/src/gendefs.rs crates/elab/src/inductive.rs crates/elab/src/stats.rs crates/elab/src/wf.rs docs/instrumentation-design.md"
mkdir -p probes/tcf_new
for f in $FILES; do mkdir -p "probes/tcf_new/$(dirname $f)"; cp "$f" "probes/tcf_new/$f"; done
echo "== PARENT tree: x86 warmup $(date +%T)"
for f in $FILES; do cp "probes/tcf_base/$f" "$f"; done
scripts/test -p heather-elab --test semantic_x86_warmup 2>&1 | tail -12
echo "== parent done $(date +%T)"
echo "== CHANGED tree: x86 warmup $(date +%T)"
for f in $FILES; do cp "probes/tcf_new/$f" "$f"; done
scripts/test -p heather-elab --test semantic_x86_warmup 2>&1 | tail -20
echo "== changed done $(date +%T)"
echo "== MARKER done $(date +%T)"
