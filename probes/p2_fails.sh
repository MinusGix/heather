set -u
cd "$(dirname "$0")/.."
echo "== full scripts/test $(date +%T)"
scripts/test > /tmp/suite.log 2>&1
echo "== rc=$? $(date +%T)"
grep -n '^== suite:' /tmp/suite.log
echo "== failing targets / tests"
grep -nE '^(failures:|test result: FAILED|error: test failed|error: [0-9]+ targets? failed)' /tmp/suite.log | head -40
echo "== failure names"
awk '/^failures:$/{f=1;next} f&&/^    /{print} f&&/^$/{f=0}' /tmp/suite.log | sort -u | head -40
echo "== panic lines"
grep -nE "panicked at|assertion .*failed|left ==|^---- " /tmp/suite.log | head -80
echo "== MARKER done $(date +%T)"
