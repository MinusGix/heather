cd /home/minus/Kairos/Code/heather
SP=/home/minus/Kairos/Code/heather/probes/claude_ns_refactor
for round in 1 2 3 4 5 6 7 8; do
  bash $SP/redo_all.sh >/dev/null
  echo "--- round $round"; bash $SP/check_all.sh
  before=$(cat $SP/explicit.txt $SP/qsites.txt | wc -l)
  cat $SP/chk/harvest.txt $SP/explicit.txt | sort -u > $SP/explicit.new; mv $SP/explicit.new $SP/explicit.txt
  cat $SP/chk/harvest_q.txt $SP/qsites.txt | sort -u > $SP/q.new; mv $SP/q.new $SP/qsites.txt
  after=$(cat $SP/explicit.txt $SP/qsites.txt | wc -l); echo "explicit sites $before -> $after"
  [ $before = $after ] && break
done
