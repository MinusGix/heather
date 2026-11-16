//! `cat` implements `tr_spec(λ b => b)` (`lib/native/native_cat_spec.hthr`;
//! `issues/native-source-cat-implements.md`, `docs/itrees/itree-simulation-design.md`
//! §6), through the statement kit `lib/native/native_source_sim.hthr`:
//!
//!  1. the closure checks from images, and the kit is *there*, named one by
//!     one;
//!  2. a client: cat at an open capacity and at a literal one implements the
//!     spec, and sends what it read;
//!  3. the negative control: a `cat` that exits 0 after a failed write is
//!     refused where the proof meets it.

use crate::read_loop_fixture::checker_with;

const NATIVE_CAT: &str = include_str!("../../../lib/native/native_cat.hthr");
const SPEC: &str = include_str!("../../../lib/native/native_cat_spec.hthr");

const PREFIX: &[(&str, &str)] = &[
    ("itree", include_str!("../../../lib/std/itree/itree.hthr")),
    ("itree_trace", include_str!("../../../lib/std/itree/itree_trace.hthr")),
    ("itree_deep", include_str!("../../../lib/std/itree/itree_deep.hthr")),
    ("linux_trees", include_str!("../../../lib/std/os/linux/linux_trees.hthr")),
    ("itree_sim", include_str!("../../../lib/std/itree/itree_sim.hthr")),
    ("linux_trees_sim", include_str!("../../../lib/std/os/linux/linux_trees_sim.hthr")),
    ("stream_filter", include_str!("../../../lib/native/stream_filter.hthr")),
    ("stream_filter_spec", include_str!("../../../lib/native/stream_filter_spec.hthr")),
    ("function_ir_eval", include_str!("../../../lib/native/function_ir/function_ir_eval.hthr")),
    ("nat_map", include_str!("../../../lib/std/data/nat_map.hthr")),
    ("function_ir_state", include_str!("../../../lib/native/function_ir/function_ir_state.hthr")),
    // The placeless check is stated over the run with the file threaded too.
    ("function_ir_writes", include_str!("../../../lib/native/function_ir/function_ir_writes.hthr")),
    // A call over views: the windows it lends and puts back.
    ("function_ir_views", include_str!("../../../lib/native/function_ir/function_ir_views.hthr")),
    ("function_ir_run", include_str!("../../../lib/native/function_ir/function_ir_run.hthr")),
    ("function_ir_placeless", include_str!("../../../lib/native/function_ir/function_ir_placeless.hthr")),
    ("native_source", include_str!("../../../lib/native/native_source.hthr")),
    ("native_source_sim", include_str!("../../../lib/native/native_source_sim.hthr")),
];

fn checker() -> heather_elab::Elaborator {
    let modules: Vec<(&str, &str)> = PREFIX.iter().copied().chain([("native_cat", NATIVE_CAT), ("native_cat_spec", SPEC)]).collect();
    checker_with(&modules)
}

const KIT: &[&str] = &[
    // The statement kit.
    "Stmt::then_rest", "Stmt::sim_then", "Stmt::sim_branch_true", "Stmt::sim_branch_false", "Flow::pass_again",
    "Flow::pass_leaves", "Stmt::sim_repeat",
    // cat's proof: the environment, the spec's place, the two passes (over the invariants `CatReading`
    // and `CatWriting`, which take value parameters and so are not named bare), and the result.
    "cat_words", "cat_env", "cat_wrote", "cat_read", "cat_spec", "cat_budget", "cat_done", "cat_write_pass",
    "cat_read_pass", "cat_simulates_at", "cat_implements", "cat_sends",
];

#[test]
fn cat_implements_tr_and_the_kit_is_there() {
    let mut src = String::from("import native_source; import native_source_sim; import native_cat; import native_cat_spec;\nfn kit() → Nat {\n");
    for (i, item) in KIT.iter().enumerate() {
        src.push_str(&format!("    let item{i} = {item};\n"));
    }
    src.push_str("    0\n}\n");
    let mut elaborator = checker();
    if let Err(error) = elaborator.elab_module_source("native_cat_kit", &src) {
        panic!("{}", error.render(&src));
    }
}

// At an open capacity and at a literal one; and what reaches stdout.
const CLIENT: &str = "import native_cat; import native_cat_spec; import native_source; import stream_filter_spec; import linux_trees;
import itree; import itree_trace; import bitvec; import list; import logic; import nat;

theorem cat_two(): Program::Implements(cat(2).denote([]), tr_spec(λ (b: BitVec(8)) => b)) { cat_implements([], 2, trivial, trivial) }

theorem cat_open(args: List<List<BitVec(8)>>, capacity: Nat, pos: 0 < capacity, small: capacity < Nat::pow(2, 63)):
    Program::Implements(cat(capacity).denote(args), tr_spec(λ (b: BitVec(8)) => b)) { cat_implements(args, capacity, pos, small) }

theorem cat_two_sends(tr: Trace<BitVec(64)>(Events::linux()), produces: Program::Produces(Events::linux(), cat(2).denote([]), tr),
    valid: Trace::LinuxValid(tr), returns: Trace::ReturnsWith(Events::linux(), tr, filter_ok())):
    Trace::sent<Nat, BitVec(64)>(BitVec::ofNat(1), tr) = Trace::received<Nat, BitVec(64)>(BitVec::ofNat(0), tr)
{
    cat_sends([], 2, trivial, trivial, tr, produces, valid, returns)
}
";

#[test]
fn cat_at_an_open_and_a_literal_capacity() {
    let mut elaborator = checker();
    if let Err(error) = elaborator.elab_module_source("native_cat_client", CLIENT) {
        panic!("{}", error.render(CLIENT));
    }
}

// A cat that exits 0 after a failed write, where the spec exits 1. The proof
// names the statements it walks through, so it is mutated the same way:
// what is refused is then the failed write's exit, not a restated piece.
#[test]
fn a_cat_ignoring_a_failed_write_has_no_proof() {
    let mutant = NATIVE_CAT.replace("Branch(12, Exit(10), ops([]))", "Branch(12, Exit(11), ops([]))");
    assert_ne!(mutant, NATIVE_CAT, "the mutation site moved");
    let proof = SPEC.replace("12, Exit(10), ops([])", "12, Exit(11), ops([])");
    assert_ne!(proof, SPEC, "the proof's mutation site moved");
    let mut elaborator = checker_with(PREFIX);
    if let Err(error) = elaborator.elab_module_source("native_cat", &mutant) {
        panic!("the mutant itself should check: {}", error.render(&mutant));
    }
    match elaborator.elab_module_source("native_cat_spec", &proof) {
        Ok(()) => panic!("a cat exiting 0 after a failed write was proved to implement tr"),
        Err(error) => {
            let msg = error.render(&proof);
            assert!(msg.contains("NotConvertible") || msg.contains("is expected here"), "{msg}");
            assert!(msg.contains("WriteFailed"), "refused somewhere other than the failed write: {msg}");
        }
    }
}
