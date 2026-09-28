set -u
cd "$(dirname "$0")/.."
for t in nat_suite_golden_hash one_law_three_structures slow_acceptance_the_wrong_unit_is_refused a_fn_is_transparent_and_a_theorem_is_not; do
  echo "== $t $(date +%T)"
  scripts/test -p heather-elab "$t" > /tmp/d.log 2>&1
  awk '/stdout ----$/{p=1} p{print} /^$/{if(p&&++n>60)p=0}' /tmp/d.log | head -70
  grep -nE "^== suite:" /tmp/d.log
  echo "== $t done $(date +%T)"
done
echo "== MARKER done $(date +%T)"
