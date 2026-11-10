//! Large and intricate inductives: the declarations an instruction set or the
//! typed syntax of an object theory needs, swept along the axis that makes
//! them large (`issues/intricate-inductive-bench-families.md`).
//!
//! Two kinds of size, and they want different families:
//!
//! - **Wide** — an assembly-shaped declaration: hundreds of constructors,
//!   each with a few operand fields of other declared types (a register enum,
//!   a memory-operand record). x86 has on the order of a thousand instruction
//!   forms, so the sweep goes to a few hundred. The families split the
//!   life of such a type into its phases so a slope names the one that
//!   grows: declaring it, *mentioning* one constructor, an `n`-arm `match`
//!   that eliminates into `Nat`, an `n`-arm `match` that rebuilds the value
//!   plus the theorem that it is the identity (one conversion per arm), and
//!   the `n²`-arm decidable equality every opcode table ends up wanting.
//! - **Intricate** — few constructors, but the lowering does the work:
//!   mutual groups (one `IWf` over a generated member sum,
//!   `docs/mutual-inductive-design.md`), a family indexed by a typing
//!   judgment (intrinsically typed terms, `Tm(J(Γ, A))` — one index is all a
//!   declaration takes today, so the judgment is a declared index type), and
//!   function-field families (`IWf` on `W`, `docs/iwf-infinitary-design.md`).
//!   Each sweeps the count the lowering multiplies: members, operator
//!   constructors, branching constructors.
//!
//! Every family's doc says its **lower bound** — the slope a cost model with
//! no defect would show — so a reader can tell which recorded slopes are the
//! target and which are debt (the same convention as the tactic families,
//! `issues/tactic-scaling-bench-families.md`). The bands record the
//! exponents that exist, measurement ± 0.35, per the suite's rule.

use crate::harness::Family;
use heather_elab::IndexedRoute;

use super::scale::{indexed_sweep, sweep};

pub fn families() -> Vec<Family> {
    vec![
        isa_declaration(),
        isa_constructor_use(),
        isa_opcode_match(),
        isa_roundtrip(),
        wide_lemma(),
        enum_equality(),
        record_fields(),
        mutual_declaration(),
        mutual_recursion(),
        typed_syntax(),
        function_fields(),
    ]
}

const REGS: [&str; 16] = [
    "Rax", "Rcx", "Rdx", "Rbx", "Rsp", "Rbp", "Rsi", "Rdi",
    "R8", "R9", "R10", "R11", "R12", "R13", "R14", "R15",
];

/// Operand shapes, cycled through by constructor index: register-register,
/// register-immediate, load, store, one register, and a bare opcode.
const SHAPES: [(&str, &str, usize); 6] = [
    ("(d: Reg, s: Reg)", "(a, b)", 2),
    ("(d: Reg, imm: Nat)", "(a, b)", 2),
    ("(d: Reg, m: Mem)", "(a, b)", 2),
    ("(m: Mem, s: Reg)", "(a, b)", 2),
    ("(d: Reg)", "(a)", 1),
    ("", "", 0),
];

fn isa_prelude() -> String {
    format!(
        "inductive Bit {{ Off, On }}\n\
         inductive Reg {{ {} }}\n\
         record Mem {{ base: Reg, index: Reg, scale: Nat, disp: Nat }}\n",
        REGS.join(", ")
    )
}

/// `n` instruction forms over the operand shapes, plus the operand types.
fn isa(n: u64) -> String {
    let ctors: Vec<String> = (0..n as usize)
        .map(|i| format!("    I{i}{},", SHAPES[i % SHAPES.len()].0))
        .collect();
    format!("{}inductive Instr {{\n{}\n}}\n", isa_prelude(), ctors.join("\n"))
}

fn binders(i: usize) -> &'static str {
    SHAPES[i % SHAPES.len()].1
}

fn wildcards(i: usize) -> &'static str {
    match SHAPES[i % SHAPES.len()].2 {
        2 => "(_, _)",
        1 => "(_)",
        _ => "",
    }
}

/// The declaration alone. Lower bound: linear — `n` constructors, each with
/// a constant-size payload.
fn isa_declaration() -> Family {
    Family {
        name: "inductive/isa-declaration",
        what: "an n-form instruction type with operand fields, declared",
        unit: "ctors",
        // 2026-10-26, cloud box, three runs: 0.99 (0.95-1.03). Met.
        expect_slope: Some((0.64, 1.34)),
        cases: sweep("inductive/isa-declaration", &[32, 64, 128, 256, 512], isa),
    }
}

/// Four constructor values of an `n`-form type — the first, two middle and
/// the last form, all register-register — each in its own `fn`, beside the
/// declaration. Lower bound: linear (the declaration); a mention should cost
/// a constant, or at worst the depth of its injection.
///
/// Recorded first (2026-10-26) at 1.71: every mention paid the elaborator's
/// `respell_spine` matching each spine component against the registered
/// codes by deep `Type` equality — Θ(n²) per mention — and the gate Θ(k²)
/// for the k-th (`issues/wide-inductive-constructor-mention-cost.md`, which
/// fixed both). What is left per `fn` is lowering `Instr` in its signature,
/// linear, which a declaring module pays per mention of the name.
fn isa_constructor_use() -> Family {
    let src = |n: u64| {
        let last = (n as usize - 1) / 6 * 6;
        let picks = [0, last / 3 / 6 * 6, 2 * last / 3 / 6 * 6, last];
        let mut s = isa(n);
        for (j, k) in picks.iter().enumerate() {
            s.push_str(&format!("fn mk{j}(a: Reg, b: Reg) -> Instr {{ I{k}(a, b) }}\n"));
        }
        s
    };
    Family {
        name: "inductive/isa-constructor-use",
        what: "four constructor values of an n-form instruction type",
        unit: "ctors",
        // 2026-10-26, cloud box, three runs: 0.96 (0.95-0.98), after the
        // mention-cost round (1.71 before). Met.
        expect_slope: Some((0.61, 1.31)),
        cases: sweep("inductive/isa-constructor-use", &[32, 64, 128, 256], src),
    }
}

/// The opcode table: one `n`-arm `match` into `Nat`, payloads ignored.
/// Lower bound: linear in the arms.
fn isa_opcode_match() -> Family {
    let src = |n: u64| {
        let arms: String = (0..n as usize)
            .map(|i| format!("        I{i}{} => {i},\n", wildcards(i)))
            .collect();
        format!(
            "{}fn opcode(i: Instr) -> Nat {{\n    match i {{\n{arms}    }}\n}}\n",
            isa(n)
        )
    };
    Family {
        name: "inductive/isa-opcode-match",
        what: "an n-arm match from an instruction type into Nat",
        unit: "ctors",
        // 2026-10-27, cloud box, three runs: 0.94 (0.84-0.96), once wide
        // sums are balanced (issues/wide-inductive-balanced-sum.md; 1.34
        // before, arm k under k `Case`s). Met.
        expect_slope: Some((0.59, 1.29)),
        cases: sweep("inductive/isa-opcode-match", &[32, 64, 128, 256], src),
    }
}

/// An `n`-arm `match` that rebuilds every form from its operands, and the
/// theorem, by an `n`-arm `match` of `refl`s, that it is the identity — the
/// shape of every encode/decode roundtrip. Lower bound: linear in the arms.
/// The rebuilt constructor values make Θ(n) mentions, so this carried
/// `isa-constructor-use`'s per-mention cost n times over until that was
/// fixed; the `k`-th was then still `k` injections deep, until wide sums
/// were balanced.
fn isa_roundtrip() -> Family {
    let src = |n: u64| {
        let n = n as usize;
        let rebuild: String = (0..n)
            .map(|i| format!("        I{i}{b} => I{i}{b},\n", b = binders(i)))
            .collect();
        let proof: String = (0..n)
            .map(|i| format!("        I{i}{} => refl,\n", binders(i)))
            .collect();
        format!(
            "{}fn ident(i: Instr) -> Instr {{\n    match i {{\n{rebuild}    }}\n}}\n\
             theorem ident_id(i: Instr): ident(i) = i {{\n    match i {{\n{proof}    }}\n}}\n",
            isa(n as u64)
        )
    };
    Family {
        name: "inductive/isa-roundtrip",
        what: "an n-arm rebuild of an instruction type and its identity theorem",
        unit: "ctors",
        // 2026-10-27, cloud box, three runs: 1.13 (1.08-1.21), once wide
        // sums are balanced (issues/wide-inductive-balanced-sum.md; 1.96
        // before, the rebuilt values Σk injections deep and each arm's
        // queries paying Γ's depth,
        // issues/conv-query-identity-env-per-gamma.md). Small debt.
        expect_slope: Some((0.78, 1.48)),
        cases: sweep("inductive/isa-roundtrip", &[16, 32, 64, 128], src),
    }
}

/// A lemma by cases over an `n`-former syntax, the shape a metatheory port
/// is built of (`issues/wide-inductive-lemma-quadratic-gate.md`): `Tm` with
/// a variable and `n` formers of arity 0 to 3, some binding; `lift`, a
/// recursion with one varied and one fixed parameter, one arm per former; a
/// congruence lemma per arity; and `lift_id`, whose arm per former is that
/// congruence applied to the recursive calls, against the dependent motive
/// `t.lift(k, u) = t`. Lower bound: linear in the formers — `n` arms of
/// constant size, as `lift` itself is.
///
/// Recorded first (the issue, CLI at 10/30/90 formers): about quadratic in
/// the gate, each arm's unfolded `lift` read back as a copy of its whole
/// case tree. Since the hypothesis is spelled as calls and the kernel keeps
/// one closure for it: about linear in the gate, with a superlinear
/// elaboration residue (the unifier's head walk descending the case tree,
/// `issues/wide-inductive-unifier-case-descent.md`) — slope ~1.2 on the
/// cloud box; the lemma alone was about quadratic before.
fn wide_lemma() -> Family {
    let src = |n: u64| {
        let n = n as usize;
        let arity = |i: usize| i % 4;
        let binds = |i: usize, j: usize| i % 8 == 1 && j == 0;
        let pat = |i: usize| match arity(i) {
            0 => format!("C{i}"),
            a => format!("C{i}({})", (0..a).map(|j| format!("a{j}")).collect::<Vec<_>>().join(", ")),
        };
        let k = |i: usize, j: usize| if binds(i, j) { "Succ(k)" } else { "k" };
        let mut s = String::new();
        let ctors: Vec<String> = std::iter::once("Bv(index: Nat)".to_string())
            .chain((0..n).map(|i| match arity(i) {
                0 => format!("C{i}"),
                a => format!("C{i}({})", (0..a).map(|j| format!("a{j}: Tm")).collect::<Vec<_>>().join(", ")),
            }))
            .collect();
        s.push_str(&format!("inductive Tm {{ {} }}\n", ctors.join(", ")));
        let arms: Vec<String> = std::iter::once("Bv(i) => Bv(i)".to_string())
            .chain((0..n).map(|i| match arity(i) {
                0 => format!("C{i} => C{i}"),
                a => format!(
                    "{} => C{i}({})",
                    pat(i),
                    (0..a).map(|j| format!("a{j}.lift({}, u)", k(i, j))).collect::<Vec<_>>().join(", ")
                ),
            }))
            .collect();
        s.push_str(&format!("fn Tm::lift(self t: Tm, k: Nat, u: Tm) -> Tm {{ match t {{ {} }} }}\n", arms.join(", ")));
        // One congruence per arity, not one per former: a lemma per former
        // would measure each former's own mention cost
        // (issues/wide-inductive-constructor-mention-cost.md), n times over.
        for a in 1..=3usize {
            let xs = (0..a).map(|j| format!("x{j}, y{j}")).collect::<Vec<_>>().join(", ");
            let ps = (0..a).map(|j| format!("p{j}: x{j} = y{j}")).collect::<Vec<_>>().join(", ");
            let dom = vec!["Tm"; a].join(" → ");
            let lhs = (0..a).map(|j| format!("x{j}")).collect::<Vec<_>>().join(", ");
            let rhs = (0..a).map(|j| format!("y{j}")).collect::<Vec<_>>().join(", ");
            let body = (0..a).rev().fold("refl".to_string(), |b, j| format!("rewrite(p{j}, {b})"));
            s.push_str(&format!("theorem cong{a}({{{xs}: Tm}}, f: {dom} → Tm, {ps}): f({lhs}) = f({rhs}) {{ {body} }}\n"));
        }
        let arms: Vec<String> = std::iter::once("Bv(i) => λ k u => refl".to_string())
            .chain((0..n).map(|i| match arity(i) {
                0 => format!("C{i} => λ k u => refl"),
                a => format!(
                    "{} => λ k u => cong{a}(λ {} => C{i}({}), {})",
                    pat(i),
                    (0..a).map(|j| format!("b{j}")).collect::<Vec<_>>().join(" "),
                    (0..a).map(|j| format!("b{j}")).collect::<Vec<_>>().join(", "),
                    (0..a).map(|j| format!("a{j}.lift_id({}, u)", k(i, j))).collect::<Vec<_>>().join(", ")
                ),
            }))
            .collect();
        s.push_str(&format!(
            "theorem Tm::lift_id(self t: Tm): (k: Nat, u: Tm) -> t.lift(k, u) = t {{ match t {{ {} }} }}\n",
            arms.join(", ")
        ));
        s
    };
    Family {
        name: "inductive/wide-lemma",
        what: "a congruence lemma by cases over an n-former syntax, against a dependent motive",
        unit: "formers",
        expect_slope: Some((0.88, 1.58)),
        cases: sweep("inductive/wide-lemma", &[16, 32, 64, 128], src),
    }
}

/// Decidable equality on an `n`-constructor enum written the way opcode
/// tables write it — a `match` of `match`es with a default arm, n² arms after
/// the default expands — and its reflexivity theorem. Lower bound:
/// quadratic, the arm count.
fn enum_equality() -> Family {
    let src = |n: u64| {
        let n = n as usize;
        let ctors: Vec<String> = (0..n).map(|i| format!("K{i}")).collect();
        let same: String = (0..n)
            .map(|i| format!("        K{i} => match b {{ K{i} => On, _ => Off }},\n"))
            .collect();
        let refl: String = (0..n).map(|i| format!("        K{i} => refl,\n")).collect();
        format!(
            "inductive Bit {{ Off, On }}\n\
             inductive Op {{ {} }}\n\
             fn same(a: Op, b: Op) -> Bit {{\n    match a {{\n{same}    }}\n}}\n\
             theorem same_refl(a: Op): same(a, a) = On {{\n    match a {{\n{refl}    }}\n}}\n",
            ctors.join(", ")
        )
    };
    Family {
        name: "inductive/enum-equality",
        what: "n²-arm decidable equality on an n-constructor enum, and its refl theorem",
        unit: "ctors",
        // 2026-10-27, cloud box, three runs: 1.96 (1.95-1.97), once wide
        // sums are balanced (2.51 before). The arm count itself is n².
        expect_slope: Some((1.61, 2.31)),
        cases: sweep("inductive/enum-equality", &[8, 16, 32, 64], src),
    }
}

/// A machine-state record of `k` fields of mixed types: a literal, a
/// projection of it by `refl`, a one-field update spelled as a full rebuild,
/// and the frame theorem that the update keeps the last field. Lower bound:
/// linear in the fields for each of the four.
fn record_fields() -> Family {
    let src = |k: u64| {
        let k = k as usize;
        let tys = ["Nat", "Bit", "Nat", "Reg"];
        let vals = ["0", "Off", "1", "Rax"];
        let fields: Vec<String> = (0..k).map(|i| format!("f{i}: {}", tys[i % 4])).collect();
        let lit: Vec<String> = (0..k).map(|i| format!("f{i} := {}", vals[i % 4])).collect();
        let upd: Vec<String> = (0..k)
            .map(|i| if i == 0 { "f0 := Succ(st.f0)".to_string() } else { format!("f{i} := st.f{i}") })
            .collect();
        let l = k - 1;
        format!(
            "{}record State {{ {} }}\n\
             fn init() -> State {{ State({}) }}\n\
             theorem init_last(): init().f{l} = {} {{ refl }}\n\
             fn bump(st: State) -> State {{ State({}) }}\n\
             theorem bump_keeps(st: State): bump(st).f{l} = st.f{l} {{ refl }}\n",
            isa_prelude(),
            fields.join(", "),
            lit.join(", "),
            vals[l % 4],
            upd.join(", "),
        )
    };
    Family {
        name: "inductive/record-fields",
        what: "a k-field record: literal, projection, rebuild and frame theorem",
        unit: "fields",
        // 2026-10-26, cloud box, three runs: 1.42 (1.11-1.58), 70% gate at
        // 64. Debt.
        expect_slope: Some((1.07, 1.77)),
        cases: sweep("inductive/record-fields", &[8, 16, 32, 64], src),
    }
}

/// A ring of `m` mutually recursive syntax sorts, each with a leaf and a node
/// holding the next sort and itself.
fn mutual_group(m: u64) -> String {
    let mut s = String::new();
    for i in 0..m {
        let j = (i + 1) % m;
        s.push_str(&format!("inductive M{i} {{ L{i}, N{i}(a: M{j}, b: M{i}) }}\n"));
    }
    s
}

/// The group alone. Lower bound: linear in the members (each has two
/// constructors).
fn mutual_declaration() -> Family {
    Family {
        name: "inductive/mutual-declaration",
        what: "a group of m mutual sorts, declared",
        unit: "members",
        // 2026-10-26, cloud box, three runs: 1.49 (1.47-1.50), 96% elab at
        // 16. 2026-10-27: 1.15 (1.11-1.18) once wide sums are balanced, and
        // re-recorded from below with the group's signature named too
        // (docs/iwf-named-signature-design.md), the sweep moved to 4..32:
        // 0.84 (0.82-0.86), fixed cost still showing. Met.
        expect_slope: Some((0.49, 1.19)),
        cases: sweep("inductive/mutual-declaration", &[4, 8, 16, 32], mutual_group),
    }
}

/// The group plus its structural recursion (`size`, one `fn` per member,
/// checked as one `elim_IWf`), and one theorem that `size0` unfolds one step
/// by `refl`. Lower bound: linear in the members — `m` arms of constant
/// size each.
///
/// Recorded instead (2026-10-26): ~2.7, nearly all kernel gate, and the
/// one-step `refl` runs the kernel out of fuel at eight members
/// (`issues/mutual-group-recursion-gate-cost.md`). Hence the sizes stopped
/// at eight until the signature was named; they now run to 32.
fn mutual_recursion() -> Family {
    let src = |m: u64| {
        let mut s = String::from(
            "fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }\n",
        );
        s.push_str(&mutual_group(m));
        for i in 0..m {
            let j = (i + 1) % m;
            s.push_str(&format!(
                "fn size{i}(t: M{i}) -> Nat {{ match t {{ L{i} => 1, N{i}(a, b) => add(size{j}(a), size{i}(b)) }} }}\n"
            ));
        }
        s.push_str(
            "theorem size_node(a: M1, b: M0): size0(N0(a, b)) = add(size1(a), size0(b)) { refl }\n",
        );
        s
    };
    Family {
        name: "inductive/mutual-recursion",
        what: "structural recursion over an m-member mutual group, and one refl unfolding",
        unit: "members",
        // 2026-10-26, cloud box, three runs: 2.82 (2.71-2.95), 96% gate.
        // Re-recorded from below the same day, once the signature was judged
        // once and the ih held as a value
        // (issues/mutual-group-recursion-gate-cost.md): 1.63 over 2..8 (about 2.3
        // from 8 to 16 by hand); the m = 8 `refl` checks. Again 2026-10-27,
        // with the signature named (docs/iwf-named-signature-design.md):
        // 0.95 (0.91-0.99, two runs) over 2..8, fixed cost dominating, so
        // the sweep moved to 4..32 with wide sums balanced as well (#214):
        // 1.28 (1.26-1.30), about 1.5 from 16 to 32 and 1.6 by hand from 80
        // to 160 (issues/iwf-shape-spine-comb-depth.md). Then, with the
        // shape shared across mentions and the index type's two spellings
        // converted apart from Γ: 1.16 (one run), the recursion's own gate
        // about linear; the rest is each member's statement re-judging the
        // signature (issues/iwf-member-statement-signature-per-gate.md).
        expect_slope: Some((0.93, 1.63)),
        cases: sweep("inductive/mutual-recursion", &[4, 8, 16, 32], src),
    }
}

/// Intrinsically typed λ-terms, `n` constructors, `n − 4` of them binary
/// operators on the base type:
/// `Tm(J(Γ, A))`, the judgment a declared index type (one index per family
/// today, `docs/inductive-indexed-lowering.md` §8.4). Variables, weakening,
/// λ and application, then `n` operators; a `size` by structural recursion
/// at the rebound judgment; a `refl` unfolding at an open and at a closed
/// term. Lower bound: linear in the constructors.
///
/// Recorded first: superlinear, nearly all gate, and a large constant — a
/// quarter of a second per `refl` at five constructors. Since the kernel
/// keys its typing memo on the entries a node reads and shares the `elim_IWf`
/// step with its recursive calls, about linear; the constant left is mostly
/// the family signature re-checked at every binder, its index terms copied
/// by each shift (`issues/indexed-family-recursion-gate-cost.md`).
fn typed_syntax() -> Family {
    let src = |n: u64| {
        let mut ctors = vec![
            "    Var0(g: Cx, t: Ty) : Tm(J(Ext(g, t), t)),".to_string(),
            "    Wk(g: Cx, t: Ty, u: Ty, e: Tm(J(g, t))) : Tm(J(Ext(g, u), t)),".to_string(),
            "    Lam(g: Cx, a: Ty, b: Ty, body: Tm(J(Ext(g, a), b))) : Tm(J(g, TArr(a, b))),".to_string(),
            "    App(g: Cx, a: Ty, b: Ty, f: Tm(J(g, TArr(a, b))), x: Tm(J(g, a))) : Tm(J(g, b)),".to_string(),
        ];
        let mut arms = vec![
            "        Var0(_, _) => 1,".to_string(),
            "        Wk(g, t, _, e) => Succ(size(J(g, t), e)),".to_string(),
            "        Lam(g, a, b, body) => Succ(size(J(Ext(g, a), b), body)),".to_string(),
            "        App(g, a, b, f, x) => add(size(J(g, TArr(a, b)), f), size(J(g, a), x)),".to_string(),
        ];
        for i in 0..n - 4 {
            ctors.push(format!(
                "    Op{i}(g: Cx, x: Tm(J(g, TNat)), y: Tm(J(g, TNat))) : Tm(J(g, TNat)),"
            ));
            arms.push(format!(
                "        Op{i}(g, x, y) => add(size(J(g, TNat), x), size(J(g, TNat), y)),"
            ));
        }
        format!(
            "fn add(a: Nat, b: Nat) -> Nat {{ match b {{ Zero => a, Succ(k) => Succ(add(a, k)) }} }}\n\
             inductive Ty {{ TNat, TArr(a: Ty, b: Ty) }}\n\
             inductive Cx {{ Emp, Ext(g: Cx, t: Ty) }}\n\
             inductive Jd {{ J(g: Cx, t: Ty), WfCx(g: Cx) }}\n\
             inductive Tm : (j: Jd) -> Type {{\n{}\n}}\n\
             fn size(j: Jd, e: Tm(j)) -> Nat {{\n    match e {{\n{}\n    }}\n}}\n\
             theorem size_op(g: Cx, x: Tm(J(g, TNat)), y: Tm(J(g, TNat))):\n    \
                 size(J(g, TNat), Op0(g, x, y)) = add(size(J(g, TNat), x), size(J(g, TNat), y)) {{ refl }}\n\
             theorem size_closed():\n    \
                 size(J(Ext(Emp, TNat), TNat), Op0(Ext(Emp, TNat), Var0(Emp, TNat), Var0(Emp, TNat))) = 2 {{ refl }}\n",
            ctors.join("\n"),
            arms.join("\n"),
        )
    };
    Family {
        name: "inductive/typed-syntax",
        what: "intrinsically typed terms, n constructors: declaration, size, two refl unfoldings",
        unit: "ctors",
        // 2026-10-26, cloud box, after the strengthened typing memo and the
        // shared ih: 1.13, 88% gate (was 1.78, 95%). From five to twelve
        // constructors the CLI's `size` grows at about the 2.2th power (was
        // ~3.2) and its `refl`s at about the 1.2th. Re-recorded from below
        // 2026-10-27, the signature named and the attempt's annotation cache
        // keyed by Ψ scope (docs/iwf-named-signature-design.md), each size
        // ~16x cheaper; over 5..8 the slope was fixed cost and noise, so the
        // sweep moved to 8..64: 0.75 (0.72-0.81). Met.
        expect_slope: Some((0.40, 1.10)),
        cases: indexed_sweep(
            "inductive/typed-syntax", &[8, 16, 32, 64], "Tm", IndexedRoute::Iwf, src,
        ),
    }
}

/// An indexed family with `n` branching constructors, each storing a
/// function child `k: (y: Nat) -> Tr(n)`; a `size` through `k(0)`; a closed
/// and an open `refl` unfolding. Lower bound: linear in the constructors.
/// Recorded first at about the cube, ~60× the same family with a plain
/// child `k: Tr(n)` at sixteen constructors; since the strengthened typing
/// memo and closure identity across spine lengths, below linear over this
/// range, the fixed cost dominating
/// (`issues/indexed-family-recursion-gate-cost.md`).
fn function_fields() -> Family {
    let src = |n: u64| {
        let mut ctors = vec!["    Lf : Tr(0),".to_string()];
        let mut arms = vec!["        Lf => 1,".to_string()];
        for i in 0..n {
            ctors.push(format!("    Br{i}(n: Nat, k: (y: Nat) -> Tr(n)) : Tr(Succ(n)),"));
            arms.push(format!("        Br{i}(m, k) => Succ(size(m, k(0))),"));
        }
        format!(
            "inductive Tr : (n: Nat) -> Type {{\n{}\n}}\n\
             fn size(n: Nat, t: Tr(n)) -> Nat {{\n    match t {{\n{}\n    }}\n}}\n\
             theorem size_closed(): size(1, Br0(0, λ y => Lf)) = 2 {{ refl }}\n\
             theorem size_open(n: Nat, k: (y: Nat) -> Tr(n)): size(Succ(n), Br0(n, k)) = Succ(size(n, k(0))) {{ refl }}\n",
            ctors.join("\n"),
            arms.join("\n"),
        )
    };
    Family {
        name: "inductive/function-fields",
        what: "an IWf-on-W family with n function-field constructors: size and two refl unfoldings",
        unit: "ctors",
        // 2026-10-26, cloud box, after the round: 0.88, 75% gate (was 1.67,
        // 98%); the CLI's `size` reads ~1.5 from eight to sixteen (was ~3.4).
        expect_slope: Some((0.53, 1.23)),
        cases: indexed_sweep(
            "inductive/function-fields", &[2, 4, 6, 8], "Tr", IndexedRoute::IwfW, src,
        ),
    }
}
