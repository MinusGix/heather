# Job 5: the full suite on spike iteration 1 (see through names only).
set -u
cd "$(dirname "$0")/.."
echo "== build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E '^(error|    Finished)' -A 6 | tail -20
echo "== full scripts/test $(date +%T)"
scripts/test > /tmp/s3suite.log 2>&1
echo "== rc=$? $(date +%T)"
grep -n '^== suite:' /tmp/s3suite.log
echo "== failing targets / tests"
grep -nE '^(failures:|test result: FAILED|error: test failed|error: [0-9]+ targets? failed)' /tmp/s3suite.log | head -40
echo "== failure names"
awk '/^failures:$/{f=1;next} f&&/^    /{print} f&&/^$/{f=0}' /tmp/s3suite.log | sort -u | head -40
echo "== panic lines"
grep -nE "panicked at|assertion .*failed|left ==|^---- " /tmp/s3suite.log | head -60
echo "== MARKER done $(date +%T)"
