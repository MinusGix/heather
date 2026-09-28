# Round 2026-09-15 part A, job 1b: the unit tests the change touches.
# (`wf::tests` matches nothing — the modules are `wf::tycode::…`.)
set -u
cd "$(dirname "$0")/.."
echo "== wf:: $(date +%T)"
scripts/test --fast -p heather-elab --lib 'wf::' 2>&1 | grep -vE '^warning|^ *\||^ *=|^ *-->|^[0-9]+ \|' | tail -70
echo "== gendefs/inductive/records unit $(date +%T)"
scripts/test --fast -p heather-elab --lib 'inductive::' 2>&1 | grep -E '^== suite:|test result:' | tail -6
echo "== MARKER done $(date +%T)"
