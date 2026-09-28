cd /home/minus/Kairos/Code/heather
SP=/home/minus/Kairos/Code/heather/probes/claude_ns_refactor
F="lib/std/bitvec.hthr lib/std/utf8.hthr lib/std/arch/x86_64/block.hthr lib/std/arch/x86_64/calls.hthr lib/std/arch/x86_64/model.hthr lib/elf64_load.hthr lib/function_ir_x86_support.hthr lib/function_ir.hthr"
python3 $SP/deexplicit.py render $F
python3 $SP/dx_pairs.py try
for round in $(seq 1 30); do
  python3 $SP/deexplicit.py render $F
  bash $SP/dx_check.sh > /dev/null
  n=$(cat $SP/dx/*.txt | grep -c '^error'); echo "round $round: $n errors; $(python3 $SP/dx_pairs.py revert $SP/dx/*.txt)"
  [ $n = 0 ] && break
done
