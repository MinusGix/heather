# Round "where the millions of conversion queries come from" (2026-09-16),
# job 3: the two factors, separated.
#
#   (1) the scaling family UNTRACED, whole TSV row per item — the point is
#       `decl_emit_ns` and maxrss beside `conv_shortcut_hits`. If the queries
#       triple between t_cp9 and t_qt3 while the elaborator's emission time
#       and the process's memory do not, the kernel is re-walking a shared
#       term and not reading a bigger one;
#   (2) t_cp1 and `close_body` traced again for the SHAPE table (site runs
#       collapsed), which is what names the walk.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_qt3
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"
F=docs/showcase/calc_parser.hthr
N=128

echo "== build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | tail -2
cp target/release/heather target/heather_qt

echo "== TSV header, 1-based"
( ulimit -v 8388608 -t 300; target/heather_qt check $L --kernel-workers 1 --timings "$OUT/h.tsv" probes/t_cp4.hthr > /dev/null 2>&1 )
head -1 "$OUT/h.tsv" | tr '\t' '\n' | nl | tr '\n' ' '; echo

plain () { # $1 = probe stem, $2 = item — UNTRACED, so the seconds are honest
  f=$1; item=$2
  ( ulimit -v 8388608 -t 1800; /usr/bin/time -f "== time $f %es wall %MKB maxrss" \
    target/heather_qt check $L --kernel-workers 1 --timings "$OUT/$f.tsv" probes/$f.hthr \
    > "$OUT/$f.out" 2>&1 )
  echo "== rc=$? $f $(date +%T)"; grep -a '^== time' "$OUT/$f.out"
  python3 - "$OUT/$f.tsv" "$item" <<'PY'
import sys
rows = [l.rstrip("\n").split("\t") for l in open(sys.argv[1])]
hdr = rows[0]
for r in rows:
    if r[0] == "item" and len(r) > 2 and r[2] == sys.argv[2]:
        print("  " + sys.argv[2] + ":")
        out = []
        for i, v in enumerate(r):
            if i < 3 or v in ("0", ""):
                continue
            out.append("%s=%s" % (hdr[i] if i < len(hdr) else "col%d" % i, v))
        for j in range(0, len(out), 4):
            print("    " + "  ".join(out[j:j + 4]))
PY
}

for p in "t_qt2 qt_floor" "t_qt1 qt_pure" "t_cp9 cp_andt" "t_qt3 qt_deep" "t_cp2 cp_plain" "t_cp1 cp_full"; do
  set -- $p; echo "== $1/$2 untraced $(date +%T)"; plain "$1" "$2"
done

echo "== t_cp1 traced, SHAPE table $(date +%T)"
( ulimit -v 8388608 -t 1800; HEATHER_VALUE_METRICS=1 HEATHER_CONV_QUERY_TRACE="cp_full:$N" \
  target/heather_qt check $L --kernel-workers 1 probes/t_cp1.hthr > "$OUT/tr1.out" 2> "$OUT/tr1.err" )
echo "== rc=$? $(date +%T)"
python3 probes/qt_agg.py "$OUT/tr1.err" $N "t_cp1/cp_full"

echo "== showcase traced on close_body, SHAPE table $(date +%T)"
( ulimit -v 16777216 -t 3600; HEATHER_VALUE_METRICS=1 HEATHER_CONV_QUERY_TRACE="close_body:$N" \
  target/heather_qt check $L --kernel-workers 1 $F > "$OUT/sc.out" 2> "$OUT/sc.err" )
echo "== rc=$? $(date +%T)"
python3 probes/qt_agg.py "$OUT/sc.err" $N "showcase/close_body"

echo "== MARKER done $(date +%T)"
