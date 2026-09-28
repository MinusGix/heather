set -u
cd "$(dirname "$0")/.."
echo "== cargo check --all-targets $(date +%T)"
cargo check -p heather-elab --all-targets 2>&1 | grep -v '^warning' | tail -60
echo "== check done $(date +%T)"
echo "== MARKER done $(date +%T)"
