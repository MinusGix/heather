cd "$(dirname "$0")/.."
scripts/test 2>&1 | grep -v '^\.*$' | tail -80
