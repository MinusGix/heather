# Round "the matcher recovers Certified's arguments" (2026-09-16), job 1:
# WHAT the three declining arms are spelled as. Builds the spelling
# instrument (`probes/ia_spell.patch`: one `spell()` call at each of
# `Holes::ty`'s and `Holes::tm`'s former-mismatch arms and at `place_ty`'s
# disagree arm, behind `HEATHER_IA_SPELL`) and runs it over the two arm
# reproducers plus the two existing family probes.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_ia1
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"

echo "== park the parent binary (HEAD with value-metrics) $(date +%T)"
cp -f target/release/heather target/heather_parent && ls -l target/heather_parent

echo "== build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E '^(error|warning: unused|    Finished)' -A 8 | tail -40
echo "== built rc=$? $(date +%T)"

for f in t_ia1 t_ia3 t_pcr3 t_cb1; do
  echo "== $f $(date +%T)"
  ( ulimit -v 8388608 -t 900; HEATHER_VALUE_METRICS=1 HEATHER_GENDEF_DECLINES=1 HEATHER_IA_SPELL=1 \
    target/release/heather check $L --kernel-workers 1 --timings "$OUT/$f.tsv" probes/$f.hthr \
    > "$OUT/$f.out" 2> "$OUT/$f.err" ); echo "   rc=$?"
  echo "-- instance_match declines"
  awk -F'\t' '$1=="gendef-decline" && $2=="instance_match" {print "   "$3"\t"$4}' "$OUT/$f.err" |
    sort | uniq -c | sort -rn | head -10
  echo "-- project_field declines"
  awk -F'\t' '$1=="gendef-decline" && $2=="project_field" {r=$4; sub(/-[0-9]+$/,"",r); print "   "$3"\t"r}' "$OUT/$f.err" |
    sort | uniq -c | sort -rn | head -8
  echo "-- distinct spelling lines, by (decl, phase, former pair)"
  awk -F'\t' '$1=="ia-spell" {print "   "$2"\t"$3"\t"$4}' "$OUT/$f.err" | sort | uniq -c | sort -rn | head -12
done

echo "== the spellings themselves: first occurrence of each (decl,phase,pair) $(date +%T)"
for f in t_ia1 t_ia3 t_pcr3; do
  echo "---- $f"
  awk -F'\t' '$1=="ia-spell" { k=$2 FS $3 FS $4; if (!(k in seen)) { seen[k]=1;
      print "KEY " $2" | "$3" | "$4; print "  "substr($5,1,900); print "  "substr($6,1,900) } }' "$OUT/$f.err"
done

echo "== MARKER done $(date +%T)"
