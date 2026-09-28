# usage: bash run.sh DEPTH...  — compile the chain at each depth, timings per depth
cd "$(dirname "$0")/../.."; P=probes/link
H=target/release/heather
for d in "$@"; do
  python3 $P/gen.py $d > $P/chain$d.hthr
  ( ulimit -v 8388608 -t 600 -c 0; HEATHER_KERNEL_WORKERS=1 $H compile-x86 $P/chain$d.hthr chain -o $P/chain$d.s --timings $P/t$d.tsv ) > $P/log$d.txt 2>&1
  echo "depth $d exit $? $(tail -1 $P/log$d.txt)"
done
