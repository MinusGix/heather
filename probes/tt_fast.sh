# Round "the projected tuple tower" (2026-09-16), job 3: is the declined spike
# even suite-green? The tree offered for review has no change in it, so the
# patch is applied remotely (the remote checkout is an rsync, not a git repo —
# `patch -p1`, as probes/README.md's earlier rounds do).
set -u
cd "$(dirname "$0")/.."
echo "== apply $(date +%T)"
patch -p1 --batch < probes/tt_D.patch > probes/out_ttf_patch.log 2>&1; echo "== apply rc=$?"
tail -3 probes/out_ttf_patch.log
echo "== scripts/test --fast -p heather-elab $(date +%T)"
scripts/test --fast -p heather-elab > probes/out_ttf_suite.log 2>&1; echo "== suite rc=$? $(date +%T)"
grep -a -E '^== suite:|INCOMPLETE' probes/out_ttf_suite.log | tail -3
grep -a -E '^(test .* FAILED|failures:|---- )' probes/out_ttf_suite.log | head -20
grep -a -E 'panicked at' probes/out_ttf_suite.log | head -10
echo "== MARKER done $(date +%T)"
