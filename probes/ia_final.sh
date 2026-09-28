# Job 5: the final verification. The walker assertion of job 4 made precise
# (`«Nat»` is the only residual quote) plus a named-argument control, then the
# full `scripts/test` again — a round's final verification is the plain full
# lane, not `--fast`.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_iaf
rm -rf "$OUT"; mkdir -p "$OUT"
echo "== the two axis tests first $(date +%T)"
scripts/test --fast -p heather-elab -- dependent_telescope --nocapture > "$OUT/axes.log" 2>&1
echo "== axes rc=$? $(date +%T)"
grep -a -B 2 -A 30 'panicked at' "$OUT/axes.log" | head -50
grep -a -E '^== suite:|^test result:' "$OUT/axes.log" | head -4

echo "== full scripts/test $(date +%T)"
scripts/test > "$OUT/suite.log" 2>&1; echo "== suite rc=$? $(date +%T)"
grep -a -E '^== suite:|INCOMPLETE' "$OUT/suite.log" | tail -3
grep -a -E '^(failures:|---- )' "$OUT/suite.log" | head -20
grep -a -A 12 'panicked at' "$OUT/suite.log" | head -40
echo "== MARKER done $(date +%T)"
