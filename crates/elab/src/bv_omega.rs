//! `bv_omega`: word arithmetic lifted to Nat (docs/bv-omega-design.md).
//!
//! A generator, not a solver. It finds every `toNat` of a word in the goal
//! and in the facts in scope, takes each word apart through `add`, `sub`,
//! `ofNat`, `word_of_nat` and the definitions that step to them, and writes a
//! proof as source: one `have` per word stating its value over the words it
//! does not take apart, every side condition proved first by `omega` in one
//! bundle, then `omega` at the goal. The caller elaborates that source at the
//! goal, so a wrong fact is refused by the checker, never trusted.

use std::collections::{BTreeMap, HashMap};
use std::sync::Arc as Rc;

use heather_kernel::term::{Term, Type};

use crate::omega_cert::{integer_source, local_facts, named_args, nat_term_source};
use crate::{Cx, Elaborator};

/// Head reducts a word may take before it is a leaf (§3): enough for a
/// definition that calls another, not enough to evaluate one.
const UNFOLD_STEPS: u64 = 16;

pub(crate) struct Generated {
    /// The proof, as source.
    pub source: String,
    /// The `have`s before the bundle (each leaf's range fact), which a
    /// failure re-check needs in scope.
    pub prelude: String,
    /// Each side condition and the word it came from, in bundle order.
    pub obligations: Vec<Obligation>,
}

pub(crate) struct Obligation {
    pub statement: String,
    pub why: String,
}

/// `Σ coefficient · atom + constant` over Nat atoms, with integer
/// coefficients: a word's value, or a Nat inside `ofNat(…)`.
#[derive(Clone, Default)]
struct Affine {
    terms: BTreeMap<usize, i128>,
    constant: i128,
}

impl Affine {
    fn atom(index: usize) -> Self {
        Self { terms: BTreeMap::from([(index, 1)]), constant: 0 }
    }
    fn constant(value: i128) -> Self {
        Self { terms: BTreeMap::new(), constant: value }
    }
    fn plus(&self, other: &Self, sign: i128) -> Self {
        let mut out = self.clone();
        for (&atom, &c) in &other.terms {
            *out.terms.entry(atom).or_insert(0) += sign * c;
        }
        out.terms.retain(|_, c| *c != 0);
        out.constant += sign * other.constant;
        out
    }
    fn scaled(&self, k: i128) -> Self {
        if k == 0 {
            return Self::default();
        }
        Self {
            terms: self.terms.iter().map(|(&a, &c)| (a, c * k)).collect(),
            constant: self.constant * k,
        }
    }
}

struct Node {
    /// The word as written, spelled for re-parsing.
    word: String,
    /// Not taken apart: its `toNat` is an atom of every value.
    leaf: bool,
    /// Its value `p - q`, spelled.
    p: String,
    q: String,
    value: Affine,
    /// The `have` that states `toNat(word) + q = p`.
    fact: String,
}

struct Walk<'a> {
    elab: &'a Elaborator,
    cx: &'a Cx,
    atoms: Vec<String>,
    atom_index: HashMap<String, usize>,
    nodes: Vec<Node>,
    node_index: HashMap<String, usize>,
    ranges: Vec<String>,
    obligations: Vec<Obligation>,
    /// Per node, in order: the fact's source with `{oN}` for obligation `N`.
    facts: Vec<String>,
    /// The nodes the last [`Walk::scan_type`] found at a `toNat`.
    found: Vec<usize>,
    /// Words whose `toNat` a fact in scope mentions. They are not unfolded:
    /// the writer stated what they know at that level (§3).
    stated: std::collections::HashSet<String>,
}

impl<'a> Walk<'a> {
    fn atom(&mut self, source: String) -> usize {
        if let Some(&i) = self.atom_index.get(&source) {
            return i;
        }
        self.atoms.push(source.clone());
        self.atom_index.insert(source, self.atoms.len() - 1);
        self.atoms.len() - 1
    }

    /// `(p, q)` spelled: the positive and negated negative parts, so that the
    /// value is `p - q` with both sides in Nat.
    fn sides(&self, value: &Affine) -> (String, String) {
        let mut pos = Vec::new();
        let mut neg = Vec::new();
        for (&atom, &c) in &value.terms {
            let term = if c.abs() == 1 {
                self.atoms[atom].clone()
            } else {
                // Literal on the left: `mul` recurses on its second argument.
                format!("{} * {}", c.abs(), self.atoms[atom])
            };
            if c > 0 { pos.push(term) } else { neg.push(term) }
        }
        if value.constant > 0 {
            pos.push(value.constant.to_string());
        } else if value.constant < 0 {
            neg.push((-value.constant).to_string());
        }
        let join = |parts: Vec<String>| if parts.is_empty() { "0".to_string() } else { parts.join(" + ") };
        (join(pos), join(neg))
    }

    fn obligation(&mut self, statement: String, why: String) -> usize {
        self.obligations.push(Obligation { statement, why });
        self.obligations.len() - 1
    }

    /// A Nat term as an affine form over atoms. A `toNat` of a word is that
    /// word's value; everything past literals, `+`, `Succ` and a literal
    /// factor is an atom, spelled as written.
    fn nat(&mut self, tm: &Rc<Term>) -> Result<Affine, String> {
        let source = nat_term_source(self.elab, self.cx, tm)?;
        if let Some(value) = integer_source(&source).filter(|v| *v >= 0) {
            return Ok(Affine::constant(value));
        }
        if let Term::Succ(inner) = &**tm {
            return Ok(self.nat(inner)?.plus(&Affine::constant(1), 1));
        }
        if let Some(args) = named_args(self.elab, tm, "nat::Nat::add")
            && let [left, right] = args.as_slice()
        {
            let left = self.nat(left)?;
            return Ok(left.plus(&self.nat(right)?, 1));
        }
        if let Some(args) = named_args(self.elab, tm, "nat::Nat::mul")
            && let [left, right] = args.as_slice()
        {
            let literal = |t: &Rc<Term>| {
                nat_term_source(self.elab, self.cx, t).ok().as_deref().and_then(integer_source).filter(|v| *v >= 0)
            };
            if let Some(k) = literal(left) {
                return Ok(self.nat(right)?.scaled(k));
            }
            if let Some(k) = literal(right) {
                return Ok(self.nat(left)?.scaled(k));
            }
        }
        if let Some(args) = named_args(self.elab, tm, "bitvec::BitVec::toNat")
            && let [width, word] = args.as_slice()
            && let Some(node) = self.word(width, word)?
        {
            return Ok(self.nodes[node].value.clone());
        }
        Ok(Affine::atom(self.atom(format!("({source})"))))
    }

    /// Find every `toNat` of a word in `tm`, through application spines.
    fn scan(&mut self, tm: &Rc<Term>) -> Result<(), String> {
        if let Some(args) = named_args(self.elab, tm, "bitvec::BitVec::toNat")
            && let [width, word] = args.as_slice()
        {
            if let Some(node) = self.word(width, word)? {
                self.found.push(node);
            }
            return Ok(());
        }
        if let Term::Succ(inner) = &**tm {
            return self.scan(inner);
        }
        let (_, args) = crate::spelling::app_spine(tm);
        for arg in args {
            self.scan(arg)?;
        }
        Ok(())
    }

    fn scan_type(&mut self, ty: &Type) -> Result<(), String> {
        match ty {
            Type::El { tm, .. } => self.scan(tm),
            Type::Id { lhs, rhs, .. } => {
                self.scan(lhs)?;
                self.scan(rhs)
            }
            _ => Ok(()),
        }
    }

    /// The word's node, built on first sight. `None` when the word does not
    /// spell, which leaves its `toNat` to `omega` as an opaque atom.
    fn word(&mut self, width: &Rc<Term>, word: &Rc<Term>) -> Result<Option<usize>, String> {
        let Some(spelled) = self.elab.spell_term_source(self.cx, word) else {
            return Ok(None);
        };
        if let Some(&node) = self.node_index.get(&spelled) {
            return Ok(Some(node));
        }
        let Some(width_source) = self.elab.spell_term_source(self.cx, width) else {
            return Ok(None);
        };
        let w = width_source.clone();
        let shape = if self.stated.contains(&spelled) { self.known(word).unwrap_or(Shape::Leaf) } else { self.shape(word) };
        let (value, fact) = match shape {
            shape @ (Shape::Add(..) | Shape::Sub(..)) => {
                let (adding, a, b) = match shape {
                    Shape::Add(a, b) => (true, a, b),
                    Shape::Sub(a, b) => (false, a, b),
                    _ => unreachable!(),
                };
                let (Some(na), Some(nb)) = (self.word(width, &a)?, self.word(width, &b)?) else {
                    return self.leaf(spelled, w);
                };
                let value = self.nodes[na].value.plus(&self.nodes[nb].value, if adding { 1 } else { -1 });
                // The operands' sides as their facts state them: a value
                // node states `c` as written, not its normal form.
                let (pa, qa) = (self.nodes[na].p.clone(), self.nodes[na].q.clone());
                let (pb, qb) = (self.nodes[nb].p.clone(), self.nodes[nb].q.clone());
                let (p, q) = self.sides(&value);
                let (sa, sb) = (self.nodes[na].word.clone(), self.nodes[nb].word.clone());
                let (fa, fb) = (self.nodes[na].fact.clone(), self.nodes[nb].fact.clone());
                let (bound, norm, lemma) = if adding {
                    let bound = self.obligation(
                        format!("({pa}) + ({pb}) < nat::Nat::pow(2, {w}) + (({qa}) + ({qb}))"),
                        format!("`{spelled}` may overflow {w} bits"),
                    );
                    let norm = self.obligation(
                        format!("(({pa}) + ({pb})) + ({q}) = ({p}) + (({qa}) + ({qb}))"),
                        format!("`{spelled}`'s value does not normalise"),
                    );
                    (bound, norm, "add_affine")
                } else {
                    let fits = self.obligation(
                        format!("({pb}) + ({qa}) <= ({pa}) + ({qb})"),
                        format!("`{spelled}` may borrow"),
                    );
                    let norm = self.obligation(
                        format!("(({pa}) + ({qb})) + ({q}) = ({p}) + (({qa}) + ({pb}))"),
                        format!("`{spelled}`'s value does not normalise"),
                    );
                    (fits, norm, "sub_affine")
                };
                let fact = format!(
                    "bitvec_omega::{lemma}({w}, {sa}, {sb}, {pa}, {qa}, {pb}, {qb}, {p}, {q}, {fa}, {fb}, {{o{bound}}}, {{o{norm}}})"
                );
                (value, (fact, p, q))
            }
            Shape::Value(lemma, c) => {
                // The value is `c` as written: already compact, so its
                // normalisation is `c + 0 = c`, which holds by computation.
                let value = self.nat(&c)?;
                let c_source = nat_term_source(self.elab, self.cx, &c)?;
                let bound = self.obligation(
                    format!("({c_source}) < nat::Nat::pow(2, {w})"),
                    format!("`{spelled}` does not fit {w} bits"),
                );
                let fact = format!("bitvec_omega::{lemma}({w}, {c_source}, {c_source}, 0, {{o{bound}}}, refl)");
                (value, (fact, c_source, "0".to_string()))
            }
            Shape::Leaf => return self.leaf(spelled, w),
        };
        let (call, p, q) = fact;
        Ok(Some(self.push(spelled, false, value, &call, &p, &q)))
    }

    fn leaf(&mut self, spelled: String, width: String) -> Result<Option<usize>, String> {
        let atom = format!("bitvec::BitVec::toNat({spelled})");
        let value = Affine::atom(self.atom(atom.clone()));
        self.ranges.push(format!(
            "have __bv_range_{}: ({atom} < nat::Nat::pow(2, {width})) = bitvec::BitVec::toNat_lt_pow({width}, {spelled});",
            self.ranges.len()
        ));
        let call = format!("bitvec_omega::leaf_affine({width}, {spelled})");
        Ok(Some(self.push(spelled, true, value, &call, &atom, "0")))
    }

    fn push(&mut self, word: String, leaf: bool, value: Affine, call: &str, p: &str, q: &str) -> usize {
        let index = self.nodes.len();
        let name = format!("__bv_{index}");
        self.facts.push(format!("have {name}: (bitvec::BitVec::toNat({word}) + ({q}) = ({p})) = {call};"));
        self.node_index.insert(word.clone(), index);
        self.nodes.push(Node { word, leaf, p: p.to_string(), q: q.to_string(), value, fact: name });
        index
    }

    /// How a word is taken apart: by its own head, or by the head its
    /// definition steps to (§3). Anything else is a leaf.
    fn shape(&self, word: &Rc<Term>) -> Shape {
        if let Some(shape) = self.known(word) {
            return shape;
        }
        if !matches!(crate::spelling::app_spine(word).0, Term::GlobalTm { .. }) {
            return Shape::Leaf;
        }
        let oracle = self.elab.goal_oracle();
        for reduct in oracle.term_reducts(&self.cx.gamma, word, UNFOLD_STEPS) {
            if let Some(shape) = self.known(&Rc::new(reduct)) {
                return shape;
            }
        }
        Shape::Leaf
    }

    fn known(&self, word: &Rc<Term>) -> Option<Shape> {
        for (name, add) in [("bitvec::BitVec::add", true), ("bitvec::BitVec::sub", false)] {
            if let Some(args) = named_args(self.elab, word, name)
                && let [_, a, b] = args.as_slice()
            {
                let (a, b) = (Rc::clone(a), Rc::clone(b));
                return Some(if add { Shape::Add(a, b) } else { Shape::Sub(a, b) });
            }
        }
        if let Some(args) = named_args(self.elab, word, "bitvec::BitVec::ofNat")
            && let [_, c] = args.as_slice()
        {
            return Some(Shape::Value("ofNat_affine", Rc::clone(c)));
        }
        if let Some(args) = named_args(self.elab, word, "bitvec_nat::word_of_nat")
            && let [_, c] = args.as_slice()
        {
            return Some(Shape::Value("word_of_nat_affine", Rc::clone(c)));
        }
        None
    }
}

enum Shape {
    Add(Rc<Term>, Rc<Term>),
    Sub(Rc<Term>, Rc<Term>),
    /// `ofNat(c)` or `word_of_nat(n, c)`, with the lemma that reads it back.
    Value(&'static str, Rc<Term>),
    Leaf,
}

/// The proof `bv_omega` offers at `expected`, as source (§2).
pub(crate) fn generate(elab: &Elaborator, cx: &Cx, expected: &Type) -> Result<Generated, String> {
    let mut walk = Walk {
        elab,
        cx,
        atoms: Vec::new(),
        atom_index: HashMap::new(),
        nodes: Vec::new(),
        node_index: HashMap::new(),
        ranges: Vec::new(),
        obligations: Vec::new(),
        facts: Vec::new(),
        found: Vec::new(),
        stated: Default::default(),
    };
    let facts_in_scope = local_facts(elab, cx);
    for (_, ty) in &facts_in_scope {
        stated_words(elab, cx, ty, &mut walk.stated);
    }
    walk.scan_type(expected)?;
    let mut subjects: Vec<usize> = std::mem::take(&mut walk.found);
    // A fact in scope over a word the walk takes apart is restated over the
    // word's value, like the goal (below).
    let mut restated: Vec<(String, Type)> = Vec::new();
    for (name, ty) in facts_in_scope {
        walk.scan_type(&ty)?;
        let found = std::mem::take(&mut walk.found);
        if found.iter().any(|&n| !walk.nodes[n].leaf) && is_nat_relation(elab, cx, &ty) {
            subjects.extend(found);
            restated.push((name, ty));
        }
    }
    subjects.retain(|&n| !walk.nodes[n].leaf);
    subjects.sort_unstable();
    subjects.dedup();
    if walk.nodes.is_empty() {
        return Err("found no `toNat` of a word in the goal or the facts in scope; use `omega`".into());
    }
    // Every side condition is one leaf of a *balanced* conjunction, proved
    // by `omega` at each leaf in the entry context, where no other side
    // condition and no fact is in scope (§2). Balanced, because each nesting
    // level costs the kernel's conversion stack: a right-nested conjunction,
    // or one Π binder per side condition, crosses the depth budget near
    // eighty side conditions, and a projection chain as deep as the
    // conjunction re-checks it at every step.
    let count = walk.obligations.len();
    let prelude = walk.ranges.join("\n");
    let mut source = format!("{{\n{prelude}\n");
    // The goal, over Nat variables for the words taken apart, proved before
    // any fact exists (§2): `omega` must never meet a composite word's
    // `toNat`, where its atom fallback would reduce into the bits.
    let finish = if subjects.is_empty() {
        "omega".to_string()
    } else {
        let mut by_length = subjects.clone();
        by_length.sort_by_key(|&n| std::cmp::Reverse(walk.nodes[n].word.len()));
        let generalise = |text: String| {
            by_length.iter().fold(text, |text, &n| {
                text.replace(&format!("bitvec::BitVec::toNat({})", walk.nodes[n].word), &format!("__bv_w{n}"))
            })
        };
        let goal = generalise(elab.spell_type_source(cx, expected).ok_or("could not spell the goal")?);
        let mut binders = String::new();
        let mut names = Vec::new();
        let mut arguments = Vec::new();
        for &n in &subjects {
            binders.push_str(&format!("(__bv_w{n}: Nat) → "));
            names.push(format!("__bv_w{n}"));
            arguments.push(format!("bitvec::BitVec::toNat({})", walk.nodes[n].word));
        }
        for &n in &subjects {
            let node = &walk.nodes[n];
            binders.push_str(&format!("(__bv_h{n}: __bv_w{n} + ({}) = ({})) → ", node.q, node.p));
            names.push(format!("__bv_h{n}"));
            arguments.push(node.fact.clone());
        }
        // Rebinding a fact under its own name hides the original from the
        // `omega` inside.
        for (name, ty) in &restated {
            let spelled = elab.spell_type_source(cx, ty).ok_or("could not spell a fact in scope")?;
            binders.push_str(&format!("({name}: {}) → ", generalise(spelled)));
            names.push(name.clone());
            arguments.push(name.clone());
        }
        source.push_str(&format!("have __bv_goal: ({binders}{goal}) = λ {} => omega;\n", names.join(" ")));
        format!("__bv_goal({})", arguments.join(", "))
    };
    let mut paths = vec![String::new(); count];
    if count > 0 {
        let statements: Vec<&str> = walk.obligations.iter().map(|o| o.statement.as_str()).collect();
        let (statement, proof) = balanced(&statements, 0, &mut paths, String::new());
        source.push_str(&format!("have __bv_obligations: ({statement}) = {proof};\n"));
    }
    for fact in &walk.facts {
        let mut fact = fact.clone();
        for i in (0..count).rev() {
            fact = fact.replace(&format!("{{o{i}}}"), &format!("__bv_obligations{}", paths[i]));
        }
        source.push_str(&fact);
        source.push('\n');
    }
    // The final `omega` must not see the bundle: it would split the
    // conjunction looking for a contradiction. A name resolves to its latest
    // binding, so rebinding it hides the bundle.
    if count > 0 {
        source.push_str("have __bv_obligations = trivial;\n");
    }
    source.push_str(&finish);
    source.push_str("\n}");
    Ok(Generated { source, prelude, obligations: walk.obligations })
}


/// The conjunction of `parts` as a balanced tree, with its proof (`omega` at
/// every leaf); records each leaf's projection path from the root.
fn balanced(parts: &[&str], first: usize, paths: &mut [String], path: String) -> (String, String) {
    if let [one] = parts {
        paths[first] = path;
        return (one.to_string(), "omega".into());
    }
    let half = parts.len() / 2;
    let (ls, lp) = balanced(&parts[..half], first, paths, format!("{path}.left"));
    let (rs, rp) = balanced(&parts[half..], first + half, paths, format!("{path}.right"));
    (format!("({ls}) ∧ ({rs})"), format!("⟨{lp}, {rp}⟩"))
}

/// The words under a `toNat` in `ty`, spelled.
fn stated_words(elab: &Elaborator, cx: &Cx, ty: &Type, out: &mut std::collections::HashSet<String>) {
    fn go(elab: &Elaborator, cx: &Cx, tm: &Rc<Term>, out: &mut std::collections::HashSet<String>) {
        if let Some(args) = named_args(elab, tm, "bitvec::BitVec::toNat")
            && let [_, word] = args.as_slice()
        {
            if let Some(spelled) = elab.spell_term_source(cx, word) {
                out.insert(spelled);
            }
            return;
        }
        if let Term::Succ(inner) = &**tm {
            return go(elab, cx, inner, out);
        }
        for arg in crate::spelling::app_spine(tm).1 {
            go(elab, cx, arg, out);
        }
    }
    match ty {
        Type::El { tm, .. } => go(elab, cx, tm, out),
        Type::Id { lhs, rhs, .. } => {
            go(elab, cx, lhs, out);
            go(elab, cx, rhs, out);
        }
        _ => {}
    }
}

/// Whether `omega` reads `ty` as a fact: a Nat order or equation.
fn is_nat_relation(elab: &Elaborator, cx: &Cx, ty: &Type) -> bool {
    match ty {
        Type::El { tm, .. } => ["nat::Nat::Le", "nat::Nat::Lt"].iter().any(|name| named_args(elab, tm, name).is_some()),
        Type::Id { ty, .. } => elab.display_type(cx, ty) == "Nat",
        _ => false,
    }
}
