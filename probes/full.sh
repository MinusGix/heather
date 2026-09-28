set -x
echo "== full start $(date -u +%T) =="
cd "$(dirname "$0")/.."
scripts/test 2>&1 | tail -60
echo "exit=$?"
echo "=== ALL DONE ==="
