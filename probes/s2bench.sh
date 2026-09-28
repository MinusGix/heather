set -x
echo "=== SAVE on the step-1-only tree ==="
patch -p1 -R --batch < probes/step2.patch
scripts/bench --save 2>&1 | tail -5
echo "=== CHECK with the kernel change ==="
patch -p1 --batch < probes/step2.patch
scripts/bench --check 2>&1 | tail -20
echo "=== DONE ==="
