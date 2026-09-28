set -u
cd "$(dirname "$0")/.."
ROOT=$PWD
OUT=/tmp/round-out; rm -rf $OUT; mkdir -p $OUT
P=$ROOT/probes/kernel-round.patch
ARGS="-L lib/std -L lib/std/parser"
F=docs/showcase/calc_parser.hthr
MARK=global_sig_rescopes

echo "== tree state: does the source carry the change? =="
grep -c "$MARK" crates/kernel/src/stats.rs || true

build() { # $1 = label
  find crates -name '*.rs' -exec touch {} +   # rsync mtimes + a persisted target/ make cargo think the tree is fresh
  cargo build --release -p heather-cli --bin heather 2>&1 | grep -E '^error' | head -5
  cp target/release/heather $OUT/heather-$1
  # Behavioural provenance: does this binary emit the new counter column?
  (ulimit -v 12582912 -t 300; $OUT/heather-$1 check -L lib/std --timings $OUT/probe-$1.tsv lib/std/nat.hthr) >/dev/null 2>&1
  head -1 $OUT/probe-$1.tsv | tr '\t' '\n' | grep -c "^$MARK$" || true
}
echo "== build AFTER (tree as synced) =="
A=$(build after)
echo "after binary: emits $MARK = $A"

echo "== revert to parent tree =="
patch -R -p1 --batch < $P || { echo "PATCH FAILED"; exit 1; }
grep -c "$MARK" crates/kernel/src/stats.rs || echo "(source no longer carries it: good)"
echo "== build BEFORE =="
B=$(build before)
echo "before binary: emits $MARK = $B"
md5sum $OUT/heather-before $OUT/heather-after
cmp -s $OUT/heather-before $OUT/heather-after && { echo "FAILED: the two binaries are identical"; exit 1; }
[ "$A" -gt 0 ] || { echo "FAILED: after binary lacks the change"; exit 1; }
[ "$B" -eq 0 ] || { echo "FAILED: before binary has the change"; exit 1; }
echo "binaries differ, and only the after one emits the counter: good"

echo "== restore =="
patch -p1 --batch < $P || { echo "RESTORE FAILED"; exit 1; }

for i in 1 2 3; do
  for w in before after; do
    rm -rf $OUT/cache-$w
    S=$(date +%s)
    (ulimit -v 12582912 -t 900; HEATHER_VALUE_METRICS=1 HEATHER_KERNEL_WORKERS=1 \
      $OUT/heather-$w check $ARGS --cache --cache-dir $OUT/cache-$w \
      --timings $OUT/$w-$i.tsv $F) > $OUT/$w-$i.log 2>&1
    echo "sample $i $w exit=$? wall=$(( $(date +%s) - S ))s"
  done
done
echo "== analysis =="
python3 $ROOT/probes/analyze-round.py $OUT
echo "MEASURE-DONE"
