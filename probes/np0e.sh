# Round "one name per value — the implementation", job 0e: the suite.
#
# Nothing on the default path moved — the pass's only source change is three
# columns inside the `HEATHER_RB=fv` report — so the gate is the elaborator's
# fast suite, as the design pass's §7 was, plus the control that says the
# instrument's own `count` line is unchanged.
set -u
cd "$(dirname "$0")/.."
echo "== fast suite, heather-elab $(date +%T)"
scripts/test --fast -p heather-elab 2>&1 | tail -20
echo "== MARKER done $(date +%T)"
