set -u
cd "$(dirname "$0")/.."
pkill -f heather_mint || true
pkill -f heather_parent || true
sleep 2
rm -f target/heather_mint
echo "strays: $(pgrep -af 'heather' | wc -l)"
ls -l target/heather_parent
echo "== MARKER done"
