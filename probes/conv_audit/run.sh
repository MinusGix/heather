cd /home/minus/Kairos/Code/heather
for f in "$@"; do echo "== $f"; (ulimit -v 8388608 -t 120 -c 0; target/release/heather check probes/conv_audit/$f 2>&1 | head -${LINES_:-12}); done
