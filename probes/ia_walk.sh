# Job 4: the one failing assertion. `the_axes_on_a_record_whose_type_argument_
# is_a_quote` asserts an empty emission walker; print what it actually finds,
# so the round can say whether it is the quote layer's standing residue
# (`issues/emission-walker-residual-sites`, the 2026-09-15 amendment to §7
# item 7 of `docs/closed-argument-and-parameter-domain-spelling-design.md`)
# or something this slice introduced.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_iaw
rm -rf "$OUT"; mkdir -p "$OUT"
echo "== run $(date +%T)"
scripts/test --fast -p heather-elab -- the_axes_on_a_record_whose_type_argument_is_a_quote --nocapture \
  > "$OUT/t.log" 2>&1; echo "== rc=$? $(date +%T)"
grep -a -B 2 -A 40 'panicked at' "$OUT/t.log" | head -60
grep -a -E '^== suite:|test result:' "$OUT/t.log" | tail -4
echo "== MARKER done $(date +%T)"
