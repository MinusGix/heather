set -u
cd "$(dirname "$0")/.."
TAG=t2 bash probes/p2_table.sh
bash probes/p2_listing.sh
echo "== ROUND2 MARKER done $(date +%T)"
