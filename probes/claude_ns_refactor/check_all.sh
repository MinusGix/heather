# Check every library consumer the CLI can check; write per-file outputs to
# $SP/chk/, a summary to $SP/chk/summary.txt, and harvest inference sites.
cd /home/minus/Kairos/Code/heather
SP=/home/minus/Kairos/Code/heather/probes/claude_ns_refactor
rm -rf $SP/chk probes/claude_x86 probes/claude_sc; mkdir -p $SP/chk probes/claude_x86 probes/claude_sc
: > $SP/chk/pathmap
grep -rhoE '\("[a-z0-9_]+", *include_str!\("[./]*lib/std/(arch|bitvec)/[^"]+"\)' crates | sed -E 's/\("([a-z0-9_]+)", *include_str!\("[./]*(lib[^"]+)"\)/\1 \2/' | sort -u |
  while read n f; do cp $f probes/claude_x86/$n.hthr; echo "probes/claude_x86/$n.hthr $f" >> $SP/chk/pathmap; done
cp docs/showcase/calc.hthr probes/claude_sc/
for f in docs/showcase/*.hthr examples/function-ir/*.hthr; do b=$(basename $f .hthr | tr - _); [ $b = parser_core ] && continue; cp $f probes/claude_sc/$b.hthr; echo "probes/claude_sc/$b.hthr $f" >> $SP/chk/pathmap; done
throttle() { while [ $(jobs -rp | wc -l) -ge 2 ]; do wait -n; done; }
run() { # name, args...
  local name=$1; shift
  (ulimit -v 8388608 -t 900 -c 0; target/release/heather check "$@" > $SP/chk/$name.txt 2>&1)
  echo "$name $(grep -c '^error' $SP/chk/$name.txt)" >> $SP/chk/summary.txt
}
: > $SP/chk/summary.txt
run std -L lib/std lib/std &
for f in probes/claude_x86/*.hthr; do run x86_$(basename $f .hthr) -L lib/std -L lib -L probes/claude_x86 $f & throttle; done; wait
for f in lib/*.hthr; do case $f in *certgen*) continue;; esac; run lib_$(basename $f .hthr) -L lib/std -L lib -L probes/claude_x86 $f & throttle; done; wait
for f in probes/claude_sc/*.hthr; do case $f in *calc_text*) continue;; esac; run sc_$(basename $f .hthr) -L lib/std -L lib -L lib/std/parser -L probes/claude_sc $f & throttle; done; wait
# harvest inference sites, mapping probe copies back to real paths
cat $SP/chk/*.txt | python3 $SP/harvest.py | sort -u | while read p l fn; do
  p=${p#/home/minus/Kairos/Code/heather/}
  real=$(awk -v p="$p" '$1==p {print $2}' $SP/chk/pathmap); [ -n "$real" ] && p=$real
  echo "$p $l $fn"; done | sort -u > $SP/chk/harvest.txt
cat $SP/chk/*.txt | python3 $SP/harvest_q.py | sort -u | while read p l fn; do
  p=${p#/home/minus/Kairos/Code/heather/}
  real=$(awk -v p="$p" '$1==p {print $2}' $SP/chk/pathmap); [ -n "$real" ] && p=$real
  echo "$p $l $fn"; done | sort -u > $SP/chk/harvest_q.txt
sort -k2 -n -r $SP/chk/summary.txt | awk '$2 != 0' 
