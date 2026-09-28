set -u
cd "$(dirname "$0")/.."
TAG="${TAG:-s3}"
OUT=probes/out_$TAG
rm -rf "$OUT"; mkdir -p "$OUT"
echo "== build start $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E '^(error|    Finished)' -A 6 | tail -60
test -x target/release/heather || { echo "== NO BINARY"; echo "== MARKER done"; exit 1; }
echo "== build done $(date +%T)"

echo "== listing on probes/t_pc1.hthr $(date +%T)"
( ulimit -v 8388608 -t 600; HEATHER_GENDEF_DECLINES=1 \
  target/release/heather check -L lib/std -L lib/std/parser \
  --kernel-workers 1 probes/t_pc1.hthr > "$OUT/pc1.out" 2> "$OUT/pc1.err" )
echo "== rc=$? $(date +%T)"; tail -3 "$OUT/pc1.out"
grep '^gendef-decline' "$OUT/pc1.err" | cut -f2,3,4 | sort | uniq -c | sort -rn | head -40

echo "== listing on showcase $(date +%T)"
( ulimit -v 16777216 -t 2400; HEATHER_GENDEF_DECLINES=1 \
  target/release/heather check -L lib/std -L lib/std/parser \
  --kernel-workers 1 docs/showcase/calc_parser.hthr > "$OUT/sc.out" 2> "$OUT/sc.err" )
echo "== rc=$? $(date +%T)"; tail -3 "$OUT/sc.out"
echo "== decline lines: $(grep -c '^gendef-decline' "$OUT/sc.err")"
echo "== register_rec_projs + project_field rows"
grep '^gendef-decline' "$OUT/sc.err" | cut -f2,3,4 | grep -E 'register_rec_projs|project_field' | sort | uniq -c | sort -rn | head -60
echo "== instance_match / instance_ref rows"
grep '^gendef-decline' "$OUT/sc.err" | cut -f2,3,4 | grep -E 'instance_match|instance_ref' | sort | uniq -c | sort -rn | head -60
echo "== respell_ty_at rows"
grep '^gendef-decline' "$OUT/sc.err" | cut -f2,3,4 | grep 'respell_ty_at' | sort | uniq -c | sort -rn | head -10
echo "== MARKER done $(date +%T)"
