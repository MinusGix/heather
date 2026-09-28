set -x
patch -p1 -R --batch < probes/k1.patch
scripts/bench --save 2>&1 | tail -3
patch -p1 --batch < probes/k1.patch
echo "=== CHECK 1 ==="
scripts/bench --check 2>&1 | grep -E "REGRESSED|IMPROVED|regression|ok:|comparisons"
echo "=== CHECK 2 ==="
scripts/bench --check 2>&1 | grep -E "REGRESSED|IMPROVED|regression|ok:|comparisons"
echo "=== DONE ==="
