# `scripts/bench --check` against a baseline saved on the parent tree, then the
# full `scripts/test`. One job: the remote checkout is an rsync'd tree and not a
# git repository, so the baseline `--save` has to happen inside the same run
# that `--check`s (probes/README.md).
set -u
cd "$(dirname "$0")/.."
FILES=$(cd probes/p2_base && find . -type f | sed 's|^\./||')

# Where the showcase's serial seconds sit: the **library** declarations (which
# a cached run replays, §7) against the showcase module's own items.
echo "== module split $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E '^(error|    Finished)' | tail -3
for who in parent changed; do
  BIN=target/heather_parent; [ $who = changed ] && BIN=target/release/heather
  ( ulimit -v 16777216 -t 3600; $BIN check -L lib/std -L lib/std/parser --kernel-workers 1 \
    --timings /tmp/ms_$who.tsv docs/showcase/calc_parser.hthr > /dev/null 2>&1 )
  echo "-- $who"
  awk -F'\t' '$1=="item"{t[$2]+=$4; k[$2]+=$8; n[$2]++}
    END{for (m in t) printf "  %-28s items %4d  total %8.2f s  kernel %8.2f s\n", m, n[m], t[m]/1e9, k[m]/1e9}' \
    /tmp/ms_$who.tsv | sort -k6 -rn | head -12
done
echo "== module split done $(date +%T)"

# The trace of the top head-pair row on the changed side (`Pi/Pi`), on the item
# the attribution names.
echo "== close_body trace $(date +%T)"
( ulimit -v 16777216 -t 3600; HEATHER_VALUE_METRICS=1 HEATHER_CONV_MISS_TRACE=close_body \
  target/release/heather check -L lib/std -L lib/std/parser --kernel-workers 1 \
  docs/showcase/calc_parser.hthr > /tmp/tr.out 2> /tmp/tr.err )
echo "== rc=$? $(date +%T)"
grep -h -m 1 -A 24 '^conv miss expected=Pi inferred=Pi' /tmp/tr.out /tmp/tr.err | head -30
echo "== trace done $(date +%T)"
mkdir -p probes/p2_now
for f in $FILES; do mkdir -p "probes/p2_now/$(dirname $f)"; cp "$f" "probes/p2_now/$f"; done

echo "== bench --save on the PARENT tree $(date +%T)"
for f in $FILES; do cp "probes/p2_base/$f" "$f"; done
scripts/bench --save 2>&1 | tail -8
echo "== save done $(date +%T)"

echo "== bench --check on the CHANGED tree $(date +%T)"
for f in $FILES; do cp "probes/p2_now/$f" "$f"; done
scripts/bench --check 2>&1 | tail -30
echo "== check done $(date +%T)"

echo "== full scripts/test $(date +%T)"
scripts/test 2>&1 | tail -60
echo "== suite done $(date +%T)"
echo "== MARKER done $(date +%T)"
