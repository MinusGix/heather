# Round "where the millions of conversion queries come from" (2026-09-16),
# job 4: the fifth point on the curve, the named-reply lever, the two
# no-component controls on the current binary, and the suite.
#
#   (1) t_qt5 — five combinator layers (a wider rail on purpose);
#   (2) t_qt4 — t_qt3's reply written once as a declaration and applied;
#   (3) t_cp3/t_cp4 — the same curve WITHOUT a declared former in the body,
#       re-measured on the post-slice binary (design §3's numbers are the
#       parent's);
#   (4) `scripts/test --fast` — the instrument is kernel-only, feature- and
#       env-gated, and emits nothing unset.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_qt4
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"

echo "== build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | tail -2
cp target/release/heather target/heather_qt

row () { python3 - "$1" "$2" <<'PY'
import sys
rows = [l.rstrip("\n").split("\t") for l in open(sys.argv[1])]
hdr = rows[0]
for r in rows:
    if r[0] == "item" and len(r) > 2 and r[2] == sys.argv[2]:
        out = ["%s=%s" % (hdr[i], v) for i, v in enumerate(r)
               if i >= 3 and v not in ("0", "")]
        print("  " + sys.argv[2] + ":")
        for j in range(0, len(out), 4):
            print("    " + "  ".join(out[j:j + 4]))
PY
}

plain () { # $1 stem, $2 item, $3 address-space rail in KB
  f=$1; item=$2; cap=$3
  echo "== $f/$item untraced $(date +%T)"
  ( ulimit -v $cap -t 3600; /usr/bin/time -f "== time $f %es wall %MKB maxrss" \
    target/heather_qt check $L --kernel-workers 1 --timings "$OUT/$f.tsv" probes/$f.hthr \
    > "$OUT/$f.out" 2>&1 )
  rc=$?; echo "== rc=$rc $(date +%T)"; grep -a '^== time' "$OUT/$f.out"
  if [ $rc -ne 0 ]; then echo "== FAILED, last 20 lines:"; tail -20 "$OUT/$f.out"; return; fi
  row "$OUT/$f.tsv" "$item"
}

plain t_qt4 qt_named 16777216
plain t_cp4 cp_floor 8388608
plain t_cp3 cp_pure  8388608
plain t_qt5 qt_deeper 33554432

echo "== scripts/test --fast $(date +%T)"
scripts/test --fast 2>&1 | tail -30
echo "== MARKER done $(date +%T)"
