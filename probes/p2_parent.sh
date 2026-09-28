# Build the PARENT (HEAD) binary once and park it at target/heather_parent, then
# restore the working tree. `target/` persists on the box between jobs, so every
# later before/after table runs both binaries in one job on one machine.
set -u
cd "$(dirname "$0")/.."
FILES="crates/elab/src/gendefs.rs crates/elab/src/inductive.rs crates/elab/src/stats.rs crates/elab/src/wf.rs docs/instrumentation-design.md"
mkdir -p probes/p2_new
for f in $FILES; do mkdir -p "probes/p2_new/$(dirname $f)"; cp "$f" "probes/p2_new/$f"; done
echo "== parent build start $(date +%T)"
for f in $FILES; do cp "probes/tcf_base/$f" "$f"; done
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E '^(error|    Finished)' | tail -10
cp target/release/heather target/heather_parent
echo "== parent build done $(date +%T)"
for f in $FILES; do cp "probes/p2_new/$f" "$f"; done
echo "== changed build start $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E '^(error|    Finished)' | tail -10
echo "== changed build done $(date +%T)"
ls -la target/heather_parent target/release/heather
echo "== MARKER done $(date +%T)"
