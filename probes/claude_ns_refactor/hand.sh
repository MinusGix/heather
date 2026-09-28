# recorded hand fixes applied after the rewriter (see redo_all.sh)
cd /home/minus/Kairos/Code/heather
# user's in-progress edit carried a duplicated receiver argument
sed -i 's/match Succ(a)\.le_dec(Succ(a), b) {/match Succ(a).le_dec(b) {/' lib/std/omega.hthr
# `code` is a soft keyword: `match code.f(...)` does not parse
sed -i 's/match code\.eq_dec(head) {/match Nat::eq_dec(code, head) {/' lib/std/parser/parser_diagnostics.hthr
# the parser facade re-exports the type members f9fe5ad dropped (start/advance/error_view/run)
python3 - <<'PY'
p='lib/std/parser.hthr'; s=open(p).read()
old="    Cursor, rest, Success, Retry,\n    Failure, ErrorView, Reply, Parser,\n"
new="    Cursor, Cursor::start, Cursor::advance, rest, Success, Retry,\n    Failure, Failure::error_view, ErrorView, Reply, Parser, Parser::run_start,\n"
if old in s: open(p,'w').write(s.replace(old,new))
PY
# `parser` exports a bare `map`, so a Result's `.map` is ambiguous in calc_parser
sed -i '352s/evaluate_parsed(parsed)\.map(λ n => Some(\[n\]))/Result::map(evaluate_parsed(parsed), λ n => Some([n]))/; 361s/calculate(ts)\.map(λ n => Some(\[n\]))/Result::map(calculate(ts), λ n => Some([n]))/' docs/showcase/calc_parser.hthr
sed -i 's/evaluate_parsed(parsed)\.map(λ n => Some(\[n\]))/Result::map(evaluate_parsed(parsed), λ n => Some([n]))/; s/calculate(s)\.map(λ n => Some(\[n\]))/Result::map(calculate(s), λ n => Some([n]))/' docs/showcase/calc_text.hthr
