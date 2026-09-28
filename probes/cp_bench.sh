# Round "quote the respelled type" (2026-09-16), the bench dance
# (probes/README.md's bench section): the committed baseline is
# desktop-recorded, so on furnace the parent's `--save` and the change's
# `--check` must happen in ONE job, reverse-applying `probes/cp.patch` for the
# save. The new test file is part of the patch, so nothing has to be moved
# aside.
set -u
cd "$(dirname "$0")/.."
echo "== SAVE on the parent tree $(date +%T)"
patch -p1 -R --batch < probes/cp.patch
scripts/bench --save 2>&1 | tail -5
echo "== CHECK with the quote respelling $(date +%T)"
patch -p1 --batch < probes/cp.patch
scripts/bench --check 2>&1 | tail -20
echo "== MARKER done $(date +%T)"
