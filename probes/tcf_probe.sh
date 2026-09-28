set -u
cd "$(dirname "$0")/.."
scripts/test --fast -p heather-elab --lib zz_tail_probe 2>&1 | tail -40
echo "== MARKER done $(date +%T)"
