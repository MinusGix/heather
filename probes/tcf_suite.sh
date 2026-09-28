set -u
cd "$(dirname "$0")/.."
echo "== suite start $(date +%T)"
scripts/test 2>&1 | tail -60
echo "== suite rc=$? $(date +%T)"
echo "== MARKER done $(date +%T)"
