set -x
echo "== full3 start $(date -u +%T) =="
cd "$(dirname "$0")/.."
scripts/test > /tmp/full3.txt 2>&1
echo "exit=$?"
awk '/^failures:/,0' /tmp/full3.txt | head -40
grep -E "^== suite:|runner wall time" /tmp/full3.txt
echo "=== ALL DONE ==="
