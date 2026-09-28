# Reproducible library rewrite: restore lib/ from the pre-Claude snapshot, run
# the call-site rewriter, then apply the recorded hand fixes.
set -e
cd /home/minus/Kairos/Code/heather
SP=/home/minus/Kairos/Code/heather/probes/claude_ns_refactor
git restore --source=refs/claude/snap-0 --worktree -- lib docs/showcase examples book/src/examples crates/cli/tests/fixtures
git restore --source=refs/claude/snap-0 --worktree -- lib/certgen_code.hthr lib/certgen_cert.hthr
python3 $SP/certgen_scope.py
FILES=$(find lib docs/showcase examples book/src/examples crates/cli/tests/fixtures -name '*.hthr' | grep -v certgen_ | grep -v "lib/function_ir_x86.hthr" | grep -v "lib/function_ir_certificates.hthr" | grep -vE 'lib/std/(algebra|bitvec|bool|int|list|nat|option|order|pair|relation)\.hthr$' | sort)
python3 $SP/rewrite.py --novalue pred,min --explicit $SP/explicit.txt --qualify-sites $SP/qsites.txt $FILES > $SP/redo.log
# --- hand fixes ---
sed -i 's/option::some_inj(/Option::some_inj(/g' lib/std/utf8.hthr
sed -i "s/List::cons_eq(/List::cons_eq<BitVec(8)>(/g" lib/std/utf8.hthr
sed -i -E '37s/\{ p\.concat\(7, 1, /{ @BitVec::concat(7, 1, p, /; 38s/\{ p\.concat\(5, 3, p, /{ @BitVec::concat(5, 3, p, /; 39s/\{ p\.concat\(4, 4, p, /{ @BitVec::concat(4, 4, p, /' lib/std/utf8.hthr
[ -f $SP/hand.sh ] && bash $SP/hand.sh
(ulimit -v 8388608 -t 300 -c 0; target/release/heather fmt $(echo $FILES lib/certgen_code.hthr lib/certgen_cert.hthr | tr ' ' '\n' | grep -E '^(lib|examples)/') >/dev/null)
cp $SP/generated/function_ir_x86.hthr $SP/generated/function_ir_certificates.hthr lib/
echo "redo done: $(grep -c FLAG $SP/redo.log) flags"
