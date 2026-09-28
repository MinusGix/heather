set -u
cd "$(dirname "$0")/.."
for t in nat_suite_golden_hash one_law_three_structures slow_acceptance_the_wrong_unit_is_refused a_fn_is_transparent_and_a_theorem_is_not; do
  echo "== $t $(date +%T)"
  scripts/test --fast -p heather-elab "$t" 2>&1 | grep -vE '^(   Compiling|    Finished|warning)' | tail -45
  echo "== $t done $(date +%T)"
done
echo "== MARKER done $(date +%T)"
