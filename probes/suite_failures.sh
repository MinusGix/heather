cd "$(dirname "$0")/.."
scripts/test 2>&1 | grep -E "^test .* FAILED|^---- |panicked at|^== suite|error: |left:|right:" | head -120
