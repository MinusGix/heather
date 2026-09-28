# Reproducible test-snippet rewrite: from the post-Rust-rename snapshot (snap-12).
set -e
cd /home/minus/Kairos/Code/heather
SP=/home/minus/Kairos/Code/heather/probes/claude_ns_refactor
T=$(find crates/*/tests crates/*/benches -name '*.rs')
git restore --source=refs/claude/snap-12 --worktree -- $T
python3 $SP/rewrite.py $T > $SP/tests_rw.log
sed -i '290s/{ ofNat_toNat(n, x) }/{ BitVec::ofNat_toNat(n, x) }/' crates/elab/tests/lib_std_bitvec.rs
sed -i '71s/lift_binary(positive_repr(), add,/lift_binary(positive_repr(), Nat::add,/; 109s/PositiveNat(n, p), add,/PositiveNat(n, p), Nat::add,/; 128s/repair.replace(", add,", /repair.replace(", Nat::add,", /; 1081s/(Evidence, add)/(Evidence, Nat::add)/; 1090s/lift(Evidence, add,/lift(Evidence, Nat::add,/' crates/elab/tests/lib_setoid_mergeable.rs
N='add|borrow_sub_bit|carry_add_bit|from_bits|sign_extend|sub|zero|head_bit|unsigned_lt_bit|zero_extend|iterate_increment|signed_lt_bit|cons_bit|shift_right|neg|shift_left|eq_dec|iter_add|iter_neg|iter_sub|all_ones|ofNat|bxor|toNat|band|bor|concat'
perl -pi -e "s/(?<![@\w:])(bitvec::BitVec::(?:$N)\()/\@\$1/g" $T
grep -rl "bitvec::Bool::" crates --include="*.rs" | xargs -r sed -i "s/bitvec::Bool::xor/bool::Bool::xor/g"
sed -i 's/Succ(k, ih) => ih\.cong_succ(),/Succ(k, ih) => Nat::cong_succ(ih),/' crates/elab/tests/operators.rs
sed -i 's/nat::Le::Decide/nat::Nat::Le::Decide/g; s/int::Le::Decide/int::Int::Le::Decide/g' $T
# the contextual-rewrite generator reads positional calls only
F=crates/elab/tests/lib_setoid_mergeable.rs
sed -i 's/head: "list_len".into(),/head: "List::len".into(),/; s/"(known ++ (incoming ++ incoming)).len()",/"List::len(known ++ (incoming ++ incoming))",/; s/"RelId<Nat>((known ++ (xs ++ xs)).len(), (known ++ (ys ++ ys)).len())",/"RelId<Nat>(List::len(known ++ (xs ++ xs)), List::len(known ++ (ys ++ ys)))",/' $F
sed -i 's/assert!(msg.starts_with("5:42:"), "{msg}");/assert!(msg.starts_with("5:47:"), "{msg}");/; s/line 5, column 42 of the source above/line 5, column 47 of the source above/' crates/elab/tests/decide_combinator.rs
sed -i 's/ih\.cong_succ()/Nat::cong_succ(ih)/g' crates/elab/tests/operators.rs
sed -i 's/bool::Le::Decide/bool::Bool::Le::Decide/g' $T
sed -i 's/INT.contains("match le_dec(a, b) as λ d =>/INT.contains("match a.le_dec(b) as λ d =>/g' crates/elab/tests/lib_std_int.rs
sed -i '121s/^import x86_64;$/import x86_64;\nimport bool;/' crates/elab/tests/x86_64.rs
perl -pi -e 's/\bbitvec::(unsigned_lt|unsigned_le|signed_lt|signed_le)::Decide/bitvec::BitVec::$1::Decide/g' $T
perl -pi -e 's/<(Bool|Nat)>\((and|or|add|mul)\)"/<$1>($1::$2)"/g; s/<(Bool|Nat)>\((and|or|add|mul)\)(`|,| )/<$1>($1::$2)$3/g' $T
sed -i "s/parser::run\([(<]\)/parser::Parser::run_start\1/g" crates/elab/tests/parser_library.rs
sed -i "s/parser::start\b/parser::Cursor::start/g; s/parser::run\([(<]\)/parser::Parser::run_start\1/g" crates/elab/tests/parser_library.rs crates/elab/tests/showcase_calculator.rs
echo "tests redo: $(grep -c FLAG $SP/tests_rw.log) flags"
# hand-written: fixtures replace the now-namespaced std maps
cp $SP/generated/tests/imported_receiver_dispatch.rs crates/elab/tests/imported_receiver_dispatch.rs
