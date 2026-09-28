# Round "emit the application, not its normal form" (2026-09-16), job 1:
# park the parent binary and confirm the exponent on the current tree
# (design §8 item 1: three points, not one).
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_nf1
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"

echo "== build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | tail -2

echo "== park $(date +%T)"
cp target/release/heather target/heather_parent
ls -l target/heather_parent

echo "== TSV header, 1-based"
( ulimit -v 8388608 -t 300; target/heather_parent check $L --kernel-workers 1 \
  --timings "$OUT/h.tsv" probes/t_qt2.hthr > /dev/null 2>&1 )
head -1 "$OUT/h.tsv" | tr '\t' '\n' | nl | tr '\n' ' '; echo

plain () { # $1 stem, $2 item, $3 rail KB
  f=$1; item=$2; cap=$3
  echo "== $f/$item untraced $(date +%T)"
  ( ulimit -v $cap -t 3600; /usr/bin/time -f "== time $f %es wall %MKB maxrss" \
    target/heather_parent check $L --kernel-workers 1 --timings "$OUT/$f.tsv" probes/$f.hthr \
    > "$OUT/$f.out" 2>&1 )
  rc=$?; echo "== rc=$rc $(date +%T)"; grep -a '^== time' "$OUT/$f.out"
  if [ $rc -ne 0 ]; then echo "== FAILED"; tail -20 "$OUT/$f.out"; return; fi
  python3 - "$OUT/$f.tsv" "$item" <<'PY'
import sys
rows=[l.rstrip("\n").split("\t") for l in open(sys.argv[1])]
hdr=rows[0]
for r in rows:
    if r[0]=="item" and len(r)>2 and r[2]==sys.argv[2]:
        out=["%s=%s"%(hdr[i],v) for i,v in enumerate(r) if i>=3 and v not in ("0","")]
        print("  "+sys.argv[2]+":")
        for j in range(0,len(out),4): print("    "+"  ".join(out[j:j+4]))
PY
}

plain t_qt2 qt_floor  8388608
plain t_cp9 cp_andt   8388608
plain t_qt3 qt_deep   16777216
plain t_qt5 qt_deeper 33554432

echo "== MARKER done $(date +%T)"
