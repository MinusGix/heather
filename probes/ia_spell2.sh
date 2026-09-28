# Job 1b: the same instrument filtered to `Certified` (job 1's 4000-line cap
# was eaten by `List`'s 27 881 speculative "is this a List?" declines, which
# are the matcher being *asked* about a type that genuinely is not that
# declaration and are not this round's arms). Adds the ROOT lines: the whole
# template and the whole subject at the point `instance_match` gives up.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_ia2
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"

echo "== build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E '^(error|    Finished)' -A 8 | tail -20
echo "== built $(date +%T)"

for f in t_ia1 t_ia3; do
  for D in Certified Result Cursor; do
    echo "== $f / $D $(date +%T)"
    ( ulimit -v 8388608 -t 900; HEATHER_VALUE_METRICS=1 HEATHER_GENDEF_DECLINES=1 HEATHER_IA_SPELL=$D \
      target/release/heather check $L --kernel-workers 1 --timings "$OUT/$f.$D.tsv" probes/$f.hthr \
      > "$OUT/$f.$D.out" 2> "$OUT/$f.$D.err" ); echo "   rc=$?"
    awk -F'\t' '$1=="gendef-decline" && $3=="'"$D"'" {print "   "$2"\t"$4}' "$OUT/$f.$D.err" | sort | uniq -c | sort -rn | head -6
    echo "-- spelling lines"
    awk -F'\t' '$1=="ia-spell" {print "   "$3"\t"$4}' "$OUT/$f.$D.err" | sort | uniq -c | sort -rn | head -10
    echo "-- first of each kind (2500 chars)"
    awk -F'\t' '$1=="ia-spell" { k=$3 FS $4; if (!(k in seen)) { seen[k]=1;
        print "KEY "$2" | "$3" | "$4; print "  A: "substr($5,1,2500); print "  B: "substr($6,1,2500) } }' "$OUT/$f.$D.err"
  done
done
echo "== MARKER done $(date +%T)"
