# Probe one declaration over a replayed prefix, and the whole root module.
# usage: bash probes/lgo_probe.sh <tag>
set -u
tag="$1"
S=/tmp/claude-1000/-home-minus-Kairos-Code-heather/8e7540fa-ef18-4755-9d84-8723c988e79f/scratchpad
CD=$S/cache-$tag
rm -rf "$CD"; mkdir -p "$CD"
B=target/release/heather
L="-L lib/std -L lib/std/parser"
# publish the prefix
(ulimit -v 8388608 -t 300; $B check $L --cache --cache-dir "$CD" docs/showcase/calc_parser.hthr) > $S/publish-$tag.log 2>&1
echo "publish exit=$?"
# whole root module, width one
(ulimit -v 8388608 -t 300; $B check $L --kernel-workers 1 --timings $S/whole-$tag.tsv docs/showcase/calc_parser.hthr) > $S/whole-$tag.log 2>&1
echo "whole exit=$?"
# one item over the replayed prefix
(ulimit -v 8388608 -t 300; $B check $L --cache --cache-dir "$CD" --kernel-workers 1 --only calc_parser::parentheses --timings $S/only-$tag.tsv docs/showcase/calc_parser.hthr) > $S/only-$tag.log 2>&1
echo "only exit=$?"
