# Job 4: spike iteration 2 (see through quotes as well as names), plus the
# per-group millisecond split of the base Pi/Pi trace.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_s3t
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"
F=docs/showcase/calc_parser.hthr
SPIKE=$(mktemp); cp crates/elab/src/gendefs.rs "$SPIKE"

head_pairs () {
  grep -h '^conv miss expected=' "$1" "$2" 2>/dev/null \
    | sed 's/^conv miss expected=//; s/ inferred=/\t/; s/ count=/\t/; s/ total=/\t/; s/s$//' \
    | awk -F'\t' '{k=$1"/"$2; c[k]+=$3; s[k]+=$4} END{for (k in c) printf "  %10d  %9.3fs  %s\n", c[k], s[k], k}' \
    | sort -rn | head -10
}

echo "== spike2 build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E '^(error|    Finished)' -A 8 | tail -40
test -x target/release/heather || { echo "== BUILD FAILED"; echo "== MARKER done"; exit 1; }
echo "== spike2 build done $(date +%T)"

echo "== unit tests (heather-elab, fast) $(date +%T)"
scripts/test --fast -p heather-elab 2>&1 | grep -E '^(test |failures:|---- |== suite|error)' | tail -50
echo "== unit tests done $(date +%T)"

echo "== listing spike2 $(date +%T)"
( ulimit -v 16777216 -t 2400; HEATHER_GENDEF_DECLINES=1 \
  target/release/heather check $L --kernel-workers 1 $F > "$OUT/l.out" 2> "$OUT/l.err" )
echo "== rc=$? $(date +%T)"; tail -2 "$OUT/l.out"
grep '^gendef-decline' "$OUT/l.err" | cut -f2,3,4 | grep -E 'instance_match|project_field' \
  | sort | uniq -c | sort -rn | head -22

echo "== t_pcr3 spike2 $(date +%T)"
rm -rf /tmp/s3t
( ulimit -v 8388608 -t 900; /usr/bin/time -f "== time spike2 t_pcr3 %es wall %MKB maxrss" \
  target/release/heather check --cache --cache-dir /tmp/s3t $L --kernel-workers 1 \
  --timings "$OUT/r3.tsv" probes/t_pcr3.hthr > "$OUT/r3.out" 2>&1 )
echo "== rc=$?"; tail -2 "$OUT/r3.out"
awk -F'\t' '$1=="item"{printf "  %-10s total %9.1f ms kernel %9.1f ms emit %8.1f ms misses %7d steps %9d\n",$3,$4/1e6,$8/1e6,$11/1e6,$43,$46}' "$OUT/r3.tsv" | grep -E 'qchain|qev'

echo "== showcase W=1 spike2 $(date +%T)"
( ulimit -v 16777216 -t 3600; /usr/bin/time -f "== time spike2 W=1 %es wall %MKB maxrss" \
  target/release/heather check $L --kernel-workers 1 --timings "$OUT/sc.tsv" $F 2>&1 | tail -3 )
awk -F'\t' '$1=="item"{printf "  %-30s total %9.1f ms kernel %9.1f ms misses %8d steps %10d\n",$3,$4/1e6,$8/1e6,$43,$46}' "$OUT/sc.tsv" | grep -E 'close_body|complete_post'
awk -F'\t' '$1=="item"{t+=$4;k+=$8;m+=$43;s+=$46;n+=1} END{printf "  TOTALS spike2 items=%d total=%.1f s kernel=%.1f s misses=%d steps=%d\n",n,t/1e9,k/1e9,m,s}' "$OUT/sc.tsv"
echo "== head pairs spike2 $(date +%T)"
( ulimit -v 16777216 -t 3600; HEATHER_VALUE_METRICS=1 \
  target/release/heather check $L --kernel-workers 1 $F > "$OUT/vm.out" 2> "$OUT/vm.err" )
head_pairs "$OUT/vm.out" "$OUT/vm.err"

echo "== showcase default width spike2 $(date +%T)"
( ulimit -v 25165824 -t 3600; /usr/bin/time -f "== time spike2 Wdefault %es wall %MKB maxrss" \
  target/release/heather check $L $F 2>&1 | tail -3 )

# ---- the base trace's per-group ms split ----------------------------------
cp probes/s3_base/gendefs.rs crates/elab/src/gendefs.rs
echo "== base rebuild for the trace split $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E '^(error|    Finished)' | tail -3
cp "$SPIKE" crates/elab/src/gendefs.rs
echo "== base close_body trace $(date +%T)"
( ulimit -v 16777216 -t 1800; HEATHER_VALUE_METRICS=1 HEATHER_CONV_MISS_TRACE=close_body \
  target/release/heather check $L --kernel-workers 1 $F > "$OUT/t.out" 2> "$OUT/t.err" )
python3 - "$OUT/t.err" <<'PY'
import re, sys, collections
cur = None
g = collections.defaultdict(lambda: [0, 0.0])
for line in open(sys.argv[1], errors="replace"):
    m = re.match(r"conv miss trace \S+ (\S+) ([0-9.]+)ms", line)
    if m:
        cur = (m.group(1), float(m.group(2)))
    elif line.startswith("expected len=") and cur:
        g[(cur[0], line.strip())][0] += 1
        g[(cur[0], line.strip())][1] += cur[1]
        cur = None
print("== base trace: count, ms, head, first-difference signature")
for k, v in sorted(g.items(), key=lambda kv: -kv[1][1])[:12]:
    print("%7d %10.1f ms  %s  %s" % (v[0], v[1], k[0], k[1]))
PY
echo "== MARKER done $(date +%T)"
