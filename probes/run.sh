for f in "$@"; do echo "== $f"; (ulimit -v 8388608 -t 120 -c 0; target/release/heather check -L lib/std -L lib $f 2>&1 | head -${LINES_MAX:-12}); done
