# Round 2026-09-15 part A, job 1: park the parent binary, build the change,
# and run the two unit-test modules the change touches.
#
# `probes/s4_base/` holds HEAD's (`51f5e59`) copy of the two files part A
# edits; the remote checkout is not a git repository, so the parent column is
# built by swapping those in and out (see the bench section of
# `probes/README.md`).
set -u
cd "$(dirname "$0")/.."
NEW=$(mktemp -d)
cp crates/elab/src/gendefs.rs crates/elab/src/wf.rs "$NEW/"

restore_new () { cp "$NEW/gendefs.rs" crates/elab/src/gendefs.rs; cp "$NEW/wf.rs" crates/elab/src/wf.rs; }

# ---------- parent ----------------------------------------------------------
cp probes/s4_base/gendefs.rs crates/elab/src/gendefs.rs
cp probes/s4_base/wf.rs crates/elab/src/wf.rs
echo "== parent build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E '^(error|    Finished)' -A 6 | tail -30
test -x target/release/heather || { echo "== PARENT BUILD FAILED"; restore_new; echo "== MARKER done"; exit 1; }
cp target/release/heather target/heather_parent
echo "== parent parked $(date +%T)"

# ---------- part A ----------------------------------------------------------
restore_new
echo "== A build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E '^(error(\[|:)|warning: unused|    Finished)' -A 8 | tail -80
echo "== A build finished $(date +%T)"
cmp -s target/heather_parent target/release/heather && { echo "== A BINARY IDENTICAL TO PARENT — build failed"; echo "== MARKER done"; exit 1; }
cp target/release/heather target/heather_a
echo "== A parked at target/heather_a $(date +%T)"

echo "== unit tests: wf::tests $(date +%T)"
scripts/test --fast -p heather-elab --lib 'wf::tests' 2>&1 | tail -60
echo "== unit tests done $(date +%T)"
echo "== MARKER done $(date +%T)"
