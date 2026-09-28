# Render + full dx_check + demote until no demotion happens.
cd /home/minus/Kairos/Code/heather
SP=/home/minus/Kairos/Code/heather/probes/claude_ns_refactor
F="lib/std/bitvec.hthr lib/std/utf8.hthr lib/std/arch/x86_64/block.hthr lib/std/arch/x86_64/calls.hthr lib/std/arch/x86_64/model.hthr lib/elf64_load.hthr lib/function_ir_x86_support.hthr lib/function_ir.hthr"
for round in $(seq 1 ${ROUNDS:-12}); do
  python3 $SP/deexplicit.py render $F
  bash $SP/dx_check.sh > /dev/null
  n=$(cat $SP/dx/*.txt | grep -c '^error')
  out=$(python3 $SP/deexplicit.py demote $SP/dx/pathmap $SP/dx/*.txt)
  echo "round $round: $n errors; $(echo "$out" | grep '^--')"
  echo "$out" > $SP/dx/../dx_round$round.txt
  echo "$out" | grep -q '^-- 0 demoted' && break
done
