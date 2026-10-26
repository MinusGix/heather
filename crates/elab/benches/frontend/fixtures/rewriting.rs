//! Rewriting and let fan-out at growing size (`issues/tactic-scaling-bench-families.md`).
//!
//! The `rewrite/*` families are mengine's rewriting benchmarks
//! (`docs/mengine-survey.md` §1.6, §7), each a small generator with a known
//! linear lower bound that Rocq and Lean are measured against. The `let/*`
//! families are [[proof-let-substitution-cost]]'s let chains on their own,
//! with no tactic in them, so they isolate what the statement and the gate
//! cost before any rewrite runs.
//!
//! Every family's doc comment states its lower bound. The bands record the
//! exponent that exists today, not the lower bound (the suite's rule), so a
//! slope above 1 here is **debt** where the lower bound is linear, and a fix
//! that moves it re-records the band from below. Several families are
//! exponential today; a log-log fit over them is not a constant, so each
//! band is the fit over exactly the sizes the family sweeps, and those sizes
//! must not change without re-recording it. Their bands are also wider than
//! the suite's ±0.35 (the steeper the curve, the more a fixed cost at the
//! small end moves the fit), which costs nothing: what such a band is for is
//! noticing the fix, which drops the slope to about 1.
//!
//! The bands were recorded on a 4-core cloud box from four runs each, not on
//! the quiet machine `issues/frontend-benchmarks.md` sizes bands on, and are
//! the measured mean ±0.35 or the four-run range, whichever is wider.
//!
//! The opaque operations (`f`, `g`, `m`) are **parameters**, never `fn`s:
//! a definition that unfolds would let conversion close a goal the rewrite
//! was meant to close, and the family would measure the wrong thing. The
//! rewrite lemmas are hypotheses of telescope type (`h: (x: Nat) -> f(x) =
//! x`) for the same reason, and so that the fixture needs no import.

use crate::harness::Family;

use super::scale::sweep;

pub fn families() -> Vec<Family> {
    vec![
        rewrite_fa(),
        rewrite_repeat_mod(),
        rewrite_let_addr0(),
        rewrite_let_nary(),
        let_fan(),
        let_dep(),
        let_stmt(),
    ]
}

/// `rewrite(h, …, h, e)` with `n` copies of `h`.
fn rewrites(n: u64) -> String {
    vec!["h"; n as usize].join(", ")
}

/// `{ let v1 = link(v0); …; vk }`, the block every let family is built from.
fn let_chain(k: u64, link: impl Fn(u64) -> String) -> String {
    let mut s = String::from("{ ");
    for i in 1..=k {
        s.push_str(&format!("let v{i} = {}; ", link(i - 1)));
    }
    s.push_str(&format!("v{k} }}"));
    s
}

/// mengine's `rewrite_fa`: `g(f(f(…f(a))))` to `g(a)` by `h: f(x) = x`.
///
/// **Lower bound: linear in n.** Heather's `rewrite` rewrites one instance
/// per equation (`docs/equation-rewrite-design.md` §6.1: the first match
/// fixes `x`, then every occurrence *of that instance* is rewritten), so the
/// proof is `n` rewrites, each a walk of an O(n) goal: n² is what this
/// fixture can say today, and it is the number a bottom-up or repeated
/// rewrite ([[rewrite-setoid-relations]]) should flatten to 1.
fn rewrite_fa() -> Family {
    let src = |n: u64| {
        let mut t = String::from("a");
        for _ in 0..n {
            t = format!("f({t})");
        }
        format!(
            "theorem rw(f: Nat → Nat, g: Nat → Nat, a: Nat, h: (x: Nat) -> f(x) = x):\n    \
             g({t}) = g(a)\n{{ rewrite({}, refl) }}\n",
            rewrites(n)
        )
    };
    Family {
        name: "rewrite/fa",
        what: "g(f^n(a)) = g(a) by n rewrites with h: f(x) = x (lower bound: linear)",
        unit: "f",
        // Recorded, not claimed: 1.44 over 16..128 (four runs, 1.33-1.53 on the
        // cloud box, 2026-10-26). Kernel 55-75% of it at the larger sizes, which
        // fits the gate checking n nested `J`s, each with an O(n) motive.
        expect_slope: Some((1.10, 1.80)),
        cases: sweep("rewrite/fa", &[16, 32, 64, 128], src),
    }
}

/// mengine's `repeat_mod`: `(… (b mod p) mod p …) mod p` to `b mod p` by
/// `h: (x mod p) mod p = x mod p`, `mod` spelled as an opaque `m`.
///
/// **Lower bound: linear in n.** As `rewrite/fa`, `n − 1` rewrites of an
/// O(n) goal today; the difference is a two-argument key whose second
/// argument is fixed, so every candidate's `p` is matched by conversion.
fn rewrite_repeat_mod() -> Family {
    let src = |n: u64| {
        let mut t = String::from("b");
        for _ in 0..n {
            t = format!("m({t}, p)");
        }
        format!(
            "theorem rw(m: Nat → Nat → Nat, b, p: Nat,\n    \
             h: (x: Nat) -> m(m(x, p), p) = m(x, p)):\n    \
             {t} = m(b, p)\n{{ rewrite({}, refl) }}\n",
            rewrites(n - 1)
        )
    };
    Family {
        name: "rewrite/repeat-mod",
        what: "(…(b mod p)…) mod p = b mod p by n−1 rewrites (lower bound: linear)",
        unit: "mods",
        // Recorded, not claimed: 1.82 over 16..128 (four runs, 1.75-1.87 on the
        // cloud box, 2026-10-26), kernel ~60-65%.
        expect_slope: Some((1.45, 2.15)),
        cases: sweep("rewrite/repeat-mod", &[16, 32, 64, 128], src),
    }
}

/// mengine's `addr0_let_in`: `let vᵢ = vᵢ₋₁ + vᵢ₋₁ + 0`, every `+ 0`
/// removed, `+` spelled as an opaque `g`. The goal is the chain equal to the
/// same chain without its zeros; `k` rewrites (each removes one link's zero,
/// at every path to it) and `refl` close it.
///
/// **Lower bound: linear in k** (mengine's is). The sites are 2^k as a tree,
/// so any walk that does not share nodes is exponential, and today three
/// do: the abstraction walk (`AbstractLocal` memoizes no result per node,
/// survey §4.2), the motive and transport the gate checks, and the final
/// `refl`'s equality of two separately built DAGs
/// ([[kernel-equality-walks-dags-as-trees]], which `let/stmt` isolates).
fn rewrite_let_addr0() -> Family {
    let src = |k: u64| {
        let zeros = let_chain(k, |j| format!("g(g(v{j}, v{j}), 0)"));
        let plain = let_chain(k, |j| format!("g(v{j}, v{j})"));
        format!(
            "theorem rw(g: Nat → Nat → Nat, v0: Nat, h: (x: Nat) -> g(x, 0) = x):\n    \
             {zeros}\n    = {plain}\n{{ rewrite({}, refl) }}\n",
            rewrites(k)
        )
    };
    Family {
        name: "rewrite/let-addr0",
        what: "k-let chain v_i = v_{i-1} + v_{i-1} + 0, every + 0 removed (lower bound: linear)",
        unit: "lets",
        // Recorded, not claimed: 5.60 over 6..12 lets (four runs, 5.40-5.73 on
        // the cloud box, 2026-10-26): ×4 per two lets, 2^k. Elaboration ~70%
        // (not yet split between the abstraction walk and occurrence matching),
        // the gate ~30%.
        expect_slope: Some((5.00, 6.20)),
        cases: sweep("rewrite/let-addr0", &[6, 8, 10, 12], src),
    }
}

/// How many lets `rewrite/let-nary` chains. Fixed so that the swept axis is
/// the arity alone: the tree is n^LETS, so the slope today reads LETS where
/// the lower bound reads 1.
const NARY_LETS: u64 = 3;

/// mengine's `rewrite_nm`: `let xᵢ = f(xᵢ₋₁, …, xᵢ₋₁)` (arity `n`, three
/// lets), rewritten to `x₀` by `h: f(x, …, x) = x`, one rewrite per let.
///
/// **Lower bound: linear in n·m** (here, with m fixed, linear in n). As a
/// tree the chain is n^m nodes.
fn rewrite_let_nary() -> Family {
    let src = |n: u64| {
        let args = |x: &str| vec![x; n as usize].join(", ");
        let chain = {
            let mut s = String::from("{ ");
            for i in 1..=NARY_LETS {
                s.push_str(&format!("let x{i} = f({}); ", args(&format!("x{}", i - 1))));
            }
            s.push_str(&format!("x{NARY_LETS} }}"));
            s
        };
        let ty = vec!["Nat"; n as usize + 1].join(" → ");
        format!(
            "theorem rw(f: {ty}, x0: Nat, h: (x: Nat) -> f({}) = x):\n    \
             {chain} = x0\n{{ rewrite({}, refl) }}\n",
            args("x"),
            rewrites(NARY_LETS)
        )
    };
    Family {
        name: "rewrite/let-nary",
        what: "3 lets x_i = f(x_{i-1}, …) of arity n, rewritten away (lower bound: linear)",
        unit: "arity",
        // Recorded, not claimed: 2.05 over arity 4..32 (four runs, 1.89-2.20 on
        // the cloud box, 2026-10-26), rising with size (the tree is n³): the
        // gate stays small (it shares since the typing memo), elaboration is 90%
        // at 32.
        expect_slope: Some((1.70, 2.40)),
        cases: sweep("rewrite/let-nary", &[4, 8, 16, 32], src),
    }
}

const MIX: &str = "fn mix(x, y: Nat) -> Nat { x }\n";

/// The links of [[proof-let-substitution-cost]]'s families, in a `fn` body.
fn mix_links(k: u64, proof: bool) -> String {
    let mut body = String::from("    let s0 = mix(a, a);\n");
    for i in 1..=k {
        let j = i - 1;
        body.push_str(&format!("    let s{i} = mix(s{j}, s{j});\n"));
        if proof {
            body.push_str(&format!("    let p{i}: (s{i} = mix(s{j}, s{j})) = refl;\n"));
        }
    }
    body
}

/// `fan`: `let sᵢ = mix(sᵢ₋₁, sᵢ₋₁)`, each link using the last twice, so the
/// chain is k nodes and 2^k paths.
///
/// **Lower bound: linear in k**, and met in gate queries since the kernel's
/// typing memo ([[kernel-typing-memo-on-node-identity]]); before it, 2^k.
/// Pinned on exact counters by `crates/elab/tests/let_and_blocks.rs`; this
/// is its time.
fn let_fan() -> Family {
    let src = |k: u64| {
        format!("{MIX}fn chain(a: Nat) -> Nat {{\n{}    s{k}\n}}\n", mix_links(k, false))
    };
    Family {
        name: "let/fan",
        what: "k lets each using the last twice, checked as a fn body (lower bound: linear)",
        unit: "lets",
        // Recorded, not claimed: 1.10 over 32..256 (four runs, 1.00-1.17 on the
        // cloud box, 2026-10-26): the lower bound, met.
        expect_slope: Some((0.75, 1.45)),
        cases: sweep("let/fan", &[32, 64, 128, 256], src),
    }
}

/// `dep`: `fan` with a transparent proof `let pᵢ: (sᵢ = mix(sᵢ₋₁, sᵢ₋₁)) =
/// refl` after every link, none of them used.
///
/// **Lower bound: linear in k.** Quadratic today: each unused proof let is
/// checked around the rest of the block under a binder of its own, so the
/// chain reaches the gate at k depths ([[discarded-let-values-nest-binders]]).
fn let_dep() -> Family {
    let src = |k: u64| {
        format!("{MIX}fn chain(a: Nat) -> Nat {{\n{}    s{k}\n}}\n", mix_links(k, true))
    };
    Family {
        name: "let/dep",
        what: "fan with an unused refl proof let per link (lower bound: linear)",
        unit: "lets",
        // Recorded, not claimed: 2.55 over 8..64 (four runs, 2.53-2.59 on the
        // cloud box, 2026-10-26), rising with size. The gate is the quadratic
        // the issue names, but ~90% is elaboration, which grows faster still
        // (×6.7 from 32 to 64).
        expect_slope: Some((2.20, 2.90)),
        cases: sweep("let/dep", &[8, 16, 32, 64], src),
    }
}

/// `stmt`: `rewrite/let-addr0`'s chain stated equal to itself and closed by
/// `refl`, with no rewrite. The two sides are elaborated separately, so
/// `refl` compares two equal DAGs.
///
/// **Lower bound: linear in k.** The gate's queries are linear since the
/// typing memo, but its time is 2^k: the conversion shortcut's derived
/// `Term::eq` walks the two DAGs as trees
/// ([[kernel-equality-walks-dags-as-trees]]).
fn let_stmt() -> Family {
    let src = |k: u64| {
        let chain = let_chain(k, |j| format!("g(g(v{j}, v{j}), 0)"));
        format!(
            "theorem st(g: Nat → Nat → Nat, v0: Nat):\n    {chain}\n    = {chain}\n{{ refl }}\n"
        )
    };
    Family {
        name: "let/stmt",
        what: "a k-let chain stated equal to itself, by refl (lower bound: linear)",
        unit: "lets",
        // Recorded, not claimed: 9.58 over 14..20 (four runs, 8.78-9.99 on the
        // cloud box, 2026-10-26): ×4 per two lets, 2^k, split about evenly
        // between the gate (`Term::eq`) and elaboration.
        expect_slope: Some((8.40, 10.80)),
        cases: sweep("let/stmt", &[14, 16, 18, 20], src),
    }
}
