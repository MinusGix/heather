set -u
cd "$(dirname "$0")/.."
echo "== build start $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E '^(error|warning: unused|    Finished)' -A 6 | tail -80
echo "== build rc=$? $(date +%T)"
test -x target/release/heather && echo "== BINARY ok" || echo "== NO BINARY"
echo "== parent binary present:"; ls -la target/heather_parent 2>&1 | tail -2
echo "== MARKER done $(date +%T)"
