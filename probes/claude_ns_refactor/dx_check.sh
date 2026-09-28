# Check std, the x86 arch modules (harness names) and lib/*.hthr; outputs to $SP/dx/.
cd /home/minus/Kairos/Code/heather
SP=/home/minus/Kairos/Code/heather/probes/claude_ns_refactor
rm -rf $SP/dx probes/claude_x86; mkdir -p $SP/dx probes/claude_x86
: > $SP/dx/pathmap
grep -rhoE '\("[a-z0-9_]+", *include_str!\("[./]*lib/std/(arch|bitvec)/[^"]+"\)' crates | sed -E 's/\("([a-z0-9_]+)", *include_str!\("[./]*(lib[^"]+)"\)/\1 \2/' | sort -u |
  while read n f; do cp $f probes/claude_x86/$n.hthr; echo "probes/claude_x86/$n.hthr $f" >> $SP/dx/pathmap; done
throttle() { while [ $(jobs -rp | wc -l) -ge 3 ]; do wait -n; done; }
run() { local name=$1; shift
  (ulimit -v 8388608 -t 900 -c 0; target/release/heather check "$@" > $SP/dx/$name.txt 2>&1)
  echo "$name $(grep -c '^error' $SP/dx/$name.txt)" >> $SP/dx/summary.txt; }
: > $SP/dx/summary.txt
run std -L lib/std lib/std &
for f in probes/claude_x86/*.hthr; do run x86_$(basename $f .hthr) -L lib/std -L lib -L probes/claude_x86 $f & throttle; done
for f in ${DX_LIB:-lib/elf64_load.hthr lib/function_ir.hthr lib/function_ir_x86_support.hthr lib/function_ir_x86.hthr}; do run lib_$(basename $f .hthr) -L lib/std -L lib -L probes/claude_x86 $f & throttle; done
wait
sort $SP/dx/summary.txt
