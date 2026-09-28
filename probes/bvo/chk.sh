# usage: bash probes/bvo/chk.sh file.hthr  — capped check, warnings stripped
cd /home/minus/Kairos/Code/heather
( ulimit -v 8388608 -t 120 -c 0; s=$(date +%s.%N); target/release/heather check "$@" > probes/bvo/last.out 2>&1; rc=$?; e=$(date +%s.%N); grep -v "constructor payload\|^ *-->\|^ *|\|^ *[0-9]* |\|^$\|: [0-9]* warnings\?$" probes/bvo/last.out | head -40; echo "rc=$rc $(echo "$e - $s" | bc)s" )
