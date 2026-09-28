awk '/^== VM begin/{f=1;next}/^== VM end/{f=0}f' "$1" \
| sed -n 's/^conv miss expected=\(.*\) inferred=\(.*\) count=\([0-9]*\) total=\([0-9.]*\)s$/\1\t\2\t\3\t\4/p' \
| awk -F'\t' '{c[$1"/"$2]+=$3; s[$1"/"$2]+=$4} END{for(k in c) printf "%-24s %8d %9.3fs\n", k, c[k], s[k]}' \
| sort -k2 -rn
