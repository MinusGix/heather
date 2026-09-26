//! `bv_omega`: word arithmetic lifted to Nat (docs/bv-omega-design.md).
//!
//! A generator, not a solver. It finds every `toNat` of a word in the goal
//! and in the facts in scope, takes each word apart through `add`, `sub`,
//! `ofNat`, `word_of_nat` and the definitions that step to them, and writes a
//! proof as source. Each word's value is stated as `w.toNat() + Q = P` over
//! *forms*, `c₁ * a₁ + (… + k)` in a fixed atom order: forms add one lemma
//! step per atom, with literal coefficients the checker adds, so no fact
//! needs `omega`. Only the outermost words' bounds and each subtraction's
//! borrow go to `omega`; every other bound is passed down by lemma. The caller elaborates the source at the goal, so a wrong
//! fact is refused by the checker, never trusted.

use std::collections::{HashMap, HashSet};
use std::sync::Arc as Rc;

use heather_kernel::term::{Term, Type};

use crate::omega_cert::{integer_source, local_facts, named_args, nat_term_source, parse_generated_expr};
use crate::{Cx, Elaborator};

/// Head reducts a word may take before it is a leaf (§3): enough for a
/// definition that calls another, not enough to evaluate one.
const UNFOLD_STEPS: u64 = 16;

pub(crate) struct Generated {
    /// The proof, as source.
    pub source: String,
    /// The bindings every side condition is proved after (the atoms and each
    /// leaf's range), which a failure re-check needs in scope.
    pub prelude: String,
    /// Each side condition and the word it came from, in bundle order.
    pub obligations: Vec<Obligation>,
}

#[derive(Clone)]
pub(crate) struct Obligation {
    /// As generated source: qualified calls, like the rest of the proof.
    pub statement: String,
    /// As the refusal quotes it, with operators.
    pub shown: String,
    pub why: String,
}

// Generated arithmetic is spelled as qualified calls, never operators: an
// operator's dispatch infers its left operand in a probe session to find its
// carrier, and a fact's left operand is a whole word.
fn add(a: &str, b: &str) -> String {
    format!("nat::Nat::add({a}, {b})")
}

fn mul(a: &str, b: &str) -> String {
    format!("nat::Nat::mul({a}, {b})")
}

fn lt(a: &str, b: &str) -> String {
    format!("nat::Nat::Lt({a}, {b})")
}

fn le(a: &str, b: &str) -> String {
    format!("nat::Nat::Le({a}, {b})")
}

/// A Nat inside `ofNat(…)`, as the reifier read it (§3).
#[derive(Clone)]
enum NatSyn {
    Lit(i128),
    /// Nat atom `index`.
    Atom(usize),
    /// `x + y`, with both spelled.
    Add(Box<NatSyn>, Box<NatSyn>, String, String),
    /// `k * x` (`true`) or `x * k`, with `x` spelled.
    Scale(i128, bool, Box<NatSyn>, String),
    /// The `toNat` of a word the walk took apart: its fact is the proof.
    Word(usize),
}

#[derive(Clone)]
enum Kind {
    Leaf,
    /// `ofNat(c)` or `word_of_nat(n, c)`: its row lemma, `c` spelled, and `c` read.
    Value(&'static str, String, NatSyn),
    Add(usize, usize),
    Sub(usize, usize),
}

#[derive(Clone)]
struct Node {
    /// The word as the walk met it, spelled for re-parsing.
    word: String,
    width: String,
    kind: Kind,
}

#[derive(Clone)]
struct Walk<'a> {
    elab: &'a Elaborator,
    cx: &'a Cx,
    /// Nat atoms, spelled; every row is over `int::OfNat` of each.
    atoms: Vec<String>,
    atom_index: HashMap<String, usize>,
    nodes: Vec<Node>,
    node_index: HashMap<String, usize>,
    /// The nodes the last [`Walk::scan_type`] found at a `toNat`.
    found: Vec<usize>,
    /// Words whose `toNat` a fact in scope mentions. They are not unfolded:
    /// the writer stated what they know at that level (§3).
    stated: HashSet<String>,
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

    fn literal(&self, t: &Rc<Term>) -> Option<i128> {
        nat_term_source(self.elab, self.cx, t).ok().as_deref().and_then(integer_source).filter(|v| *v >= 0)
    }

    /// A Nat term as the reifier reads it: literals, `+`, `Succ`, a literal
    /// factor, the `toNat` of a word; everything else is an atom.
    fn nat(&mut self, tm: &Rc<Term>) -> Result<NatSyn, String> {
        let source = nat_term_source(self.elab, self.cx, tm)?;
        if let Some(value) = integer_source(&source).filter(|v| *v >= 0) {
            return Ok(NatSyn::Lit(value));
        }
        if let Term::Succ(inner) = &**tm {
            let inner_source = nat_term_source(self.elab, self.cx, inner)?;
            return Ok(NatSyn::Add(Box::new(self.nat(inner)?), Box::new(NatSyn::Lit(1)), inner_source, "1".into()));
        }
        if let Some(args) = named_args(self.elab, tm, "nat::Nat::add")
            && let [left, right] = args.as_slice()
        {
            let (ls, rs) = (nat_term_source(self.elab, self.cx, left)?, nat_term_source(self.elab, self.cx, right)?);
            return Ok(NatSyn::Add(Box::new(self.nat(left)?), Box::new(self.nat(right)?), ls, rs));
        }
        if let Some(args) = named_args(self.elab, tm, "nat::Nat::mul")
            && let [left, right] = args.as_slice()
        {
            if let Some(k) = self.literal(left) {
                let inner = nat_term_source(self.elab, self.cx, right)?;
                return Ok(NatSyn::Scale(k, true, Box::new(self.nat(right)?), inner));
            }
            if let Some(k) = self.literal(right) {
                let inner = nat_term_source(self.elab, self.cx, left)?;
                return Ok(NatSyn::Scale(k, false, Box::new(self.nat(left)?), inner));
            }
        }
        // A word's fact states its value only when nothing below it
        // subtracts (its `Q` is zero); otherwise its `toNat` is an atom here.
        if let Some(args) = named_args(self.elab, tm, "bitvec::BitVec::toNat")
            && let [width, word] = args.as_slice()
            && let Some(node) = self.word(width, word)?
            && !self.subtracts(node)
        {
            return Ok(NatSyn::Word(node));
        }
        Ok(NatSyn::Atom(self.atom(source)))
    }

    fn subtracts(&self, n: usize) -> bool {
        match &self.nodes[n].kind {
            Kind::Sub(..) => true,
            Kind::Add(a, b) => self.subtracts(*a) || self.subtracts(*b),
            Kind::Value(_, _, syn) => self.syn_subtracts(syn),
            Kind::Leaf => false,
        }
    }

    fn syn_subtracts(&self, syn: &NatSyn) -> bool {
        match syn {
            NatSyn::Add(x, y, _, _) => self.syn_subtracts(x) || self.syn_subtracts(y),
            NatSyn::Scale(_, _, x, _) => self.syn_subtracts(x),
            NatSyn::Word(n) => self.subtracts(*n),
            _ => false,
        }
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
        for arg in crate::spelling::app_spine(tm).1 {
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
        let Some(w) = self.elab.spell_term_source(self.cx, width) else {
            return Ok(None);
        };
        let shape = if self.stated.contains(&spelled) { self.known(word).unwrap_or(Shape::Leaf) } else { self.shape(word) };
        let kind = match shape {
            Shape::Add(a, b) => match (self.word(width, &a)?, self.word(width, &b)?) {
                (Some(na), Some(nb)) => Kind::Add(na, nb),
                _ => Kind::Leaf,
            },
            Shape::Sub(a, b) => match (self.word(width, &a)?, self.word(width, &b)?) {
                (Some(na), Some(nb)) => Kind::Sub(na, nb),
                _ => Kind::Leaf,
            },
            Shape::Value(lemma, c) => {
                let c_source = nat_term_source(self.elab, self.cx, &c)?;
                Kind::Value(lemma, c_source, self.nat(&c)?)
            }
            Shape::Leaf => Kind::Leaf,
        };
        if let Kind::Leaf = kind {
            self.atom(format!("bitvec::BitVec::toNat({spelled})"));
        }
        let index = self.nodes.len();
        self.node_index.insert(spelled.clone(), index);
        self.nodes.push(Node { word: spelled, width: w, kind });
        Ok(Some(index))
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
            return Some(Shape::Value("ofNat_row", Rc::clone(c)));
        }
        if let Some(args) = named_args(self.elab, word, "bitvec_nat::word_of_nat")
            && let [_, c] = args.as_slice()
        {
            return Some(Shape::Value("word_of_nat_row", Rc::clone(c)));
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

// ---------------------------------------------------------------------------
// Forms, bounds, and the source that states them.

/// `c₁ * a₁ + (… + k)`: literal coefficients over atoms in index order,
/// zero coefficients left out.
#[derive(Clone, Default, PartialEq)]
struct Form {
    terms: Vec<(usize, i128)>,
    k: i128,
}

impl Form {
    fn atom(i: usize) -> Form {
        Form { terms: vec![(i, 1)], k: 0 }
    }
    fn is_zero(&self) -> bool {
        self.terms.is_empty() && self.k == 0
    }
}

/// Where a word's bound comes from (§2).
#[derive(Clone, Copy)]
enum BoundFrom {
    /// Its `toNat` is below `2^n`: every leaf's range.
    Range,
    /// Proved by `omega`: side condition `i`.
    Obligation(usize),
    /// Its parent `add`'s bound and its sibling's sign.
    AddParent { parent: usize, left: bool },
    /// Its parent `sub`'s no-borrow and the minuend's bound.
    SubParent { parent: usize },
}

struct Emitter<'w, 'a> {
    walk: &'w Walk<'a>,
    /// Per node, `P` and `Q` of its fact `toNat + Q = P`.
    forms: Vec<(Form, Form)>,
    parents: Vec<Vec<usize>>,
    /// Per node, what its bound is proved from, once planned.
    bound_from: Vec<Option<BoundFrom>>,
    /// Per `sub` node, its no-borrow side condition.
    fits: HashMap<usize, usize>,
    obligations: Vec<Obligation>,
    /// Obligation `i`'s projection out of the bundle.
    paths: Vec<String>,
    emitted: HashSet<String>,
    lines: Vec<String>,
}

fn merge_forms(f: &Form, g: &Form) -> Form {
    let mut terms: Vec<(usize, i128)> = Vec::new();
    let (mut i, mut j) = (0, 0);
    while i < f.terms.len() || j < g.terms.len() {
        match (f.terms.get(i), g.terms.get(j)) {
            (Some(&(a, c)), Some(&(b, d))) if a == b => {
                terms.push((a, c + d));
                i += 1;
                j += 1;
            }
            (Some(&(a, c)), Some(&(b, _))) if a < b => {
                terms.push((a, c));
                i += 1;
            }
            (Some(&(a, c)), None) => {
                terms.push((a, c));
                i += 1;
            }
            (_, Some(&(b, d))) => {
                terms.push((b, d));
                j += 1;
            }
            (None, None) => unreachable!(),
        }
    }
    Form { terms, k: f.k + g.k }
}

impl<'w, 'a> Emitter<'w, 'a> {
    fn new(walk: &'w Walk<'a>) -> Self {
        let mut forms: Vec<(Form, Form)> = Vec::new();
        let mut parents = vec![Vec::new(); walk.nodes.len()];
        for (i, node) in walk.nodes.iter().enumerate() {
            let pq = match &node.kind {
                Kind::Leaf => (Form::atom(walk.atom_index[&format!("bitvec::BitVec::toNat({})", node.word)]), Form::default()),
                Kind::Value(_, _, syn) => (Self::syn_form(&forms, syn), Form::default()),
                Kind::Add(a, b) => {
                    parents[*a].push(i);
                    parents[*b].push(i);
                    (merge_forms(&forms[*a].0, &forms[*b].0), merge_forms(&forms[*a].1, &forms[*b].1))
                }
                Kind::Sub(a, b) => {
                    parents[*a].push(i);
                    parents[*b].push(i);
                    (merge_forms(&forms[*a].0, &forms[*b].1), merge_forms(&forms[*a].1, &forms[*b].0))
                }
            };
            forms.push(pq);
        }
        Emitter {
            walk,
            forms,
            parents,
            bound_from: vec![None; walk.nodes.len()],
            fits: HashMap::new(),
            obligations: Vec::new(),
            paths: Vec::new(),
            emitted: HashSet::new(),
            lines: Vec::new(),
        }
    }

    fn syn_form(forms: &[(Form, Form)], syn: &NatSyn) -> Form {
        match syn {
            NatSyn::Lit(v) => Form { terms: Vec::new(), k: *v },
            NatSyn::Atom(i) => Form::atom(*i),
            NatSyn::Add(x, y, _, _) => merge_forms(&Self::syn_form(forms, x), &Self::syn_form(forms, y)),
            NatSyn::Scale(k, _, x, _) => {
                let f = Self::syn_form(forms, x);
                Form { terms: f.terms.iter().map(|&(a, c)| (a, c * k)).collect(), k: f.k * k }
            }
            NatSyn::Word(n) => forms[*n].0.clone(),
        }
    }

    fn atom(&self, i: usize) -> String {
        format!("({})", self.walk.atoms[i])
    }

    /// A form as source, nested exactly as the `form_*` lemmas build it.
    fn spell(&self, f: &Form) -> String {
        let mut out = f.k.to_string();
        for &(a, c) in f.terms.iter().rev() {
            out = add(&mul(&c.to_string(), &self.atom(a)), &out);
        }
        out
    }

    /// A form as a refusal quotes it: `c₁ * a₁ + (… + k)`.
    fn shown(&self, f: &Form) -> String {
        let mut out = f.k.to_string();
        for &(a, c) in f.terms.iter().rev() {
            out = format!("{c} * {} + ({out})", self.atom(a));
        }
        out
    }

    /// `(F) + (G) = (merge)`, one `form_*` step per atom.
    fn merge_proof(&self, f: &Form, g: &Form) -> String {
        let rest = |f: &Form| Form { terms: f.terms[1..].to_vec(), k: f.k };
        match (f.terms.first(), g.terms.first()) {
            (None, None) => "refl".into(),
            (Some(&(a, c)), Some(&(b, d))) if a == b => {
                let (x, y) = (rest(f), rest(g));
                let r = merge_forms(&x, &y);
                format!("trans(bitvec_omega::form_step({c}, {d}, {}, {}, {}), @cong(λ (t: Nat) => {}, {}, {}, {}))",
                    self.atom(a), self.spell(&x), self.spell(&y), add(&mul(&(c + d).to_string(), &self.atom(a)), "t"), add(&self.spell(&x), &self.spell(&y)), self.spell(&r), self.merge_proof(&x, &y))
            }
            (Some(&(a, c)), next) if next.is_none_or(|&(b, _)| a < b) => {
                let x = rest(f);
                let r = merge_forms(&x, g);
                format!("trans(bitvec_omega::form_left({c}, {}, {}, {}), @cong(λ (t: Nat) => {}, {}, {}, {}))",
                    self.atom(a), self.spell(&x), self.spell(g), add(&mul(&c.to_string(), &self.atom(a)), "t"), add(&self.spell(&x), &self.spell(g)), self.spell(&r), self.merge_proof(&x, g))
            }
            (_, Some(&(b, d))) => {
                let y = rest(g);
                let r = merge_forms(f, &y);
                format!("trans(bitvec_omega::form_right({}, {d}, {}, {}), @cong(λ (t: Nat) => {}, {}, {}, {}))",
                    self.spell(f), self.atom(b), self.spell(&y), add(&mul(&d.to_string(), &self.atom(b)), "t"), add(&self.spell(f), &self.spell(&y)), self.spell(&r), self.merge_proof(f, &y))
            }
            _ => unreachable!(),
        }
    }

    /// `k * (F) = (scaled)`.
    fn scale_proof(&self, k: i128, f: &Form) -> String {
        match f.terms.first() {
            None => "refl".into(),
            Some(&(a, c)) => {
                let x = Form { terms: f.terms[1..].to_vec(), k: f.k };
                let r = Form { terms: x.terms.iter().map(|&(b, d)| (b, d * k)).collect(), k: x.k * k };
                format!("trans(bitvec_omega::form_scale({k}, {c}, {}, {}), @cong(λ (t: Nat) => {}, {}, {}, {}))",
                    self.atom(a), self.spell(&x), add(&mul(&(k * c).to_string(), &self.atom(a)), "t"), mul(&k.to_string(), &self.spell(&x)), self.spell(&r), self.scale_proof(k, &x))
            }
        }
    }

    /// `c = (F)` for a Nat inside `ofNat(…)`.
    fn reify(&mut self, syn: &NatSyn, source: &str) -> String {
        match syn {
            NatSyn::Lit(_) => "refl".into(),
            NatSyn::Atom(i) => format!("bitvec_omega::form_atom({})", self.atom(*i)),
            NatSyn::Word(w) => self.fact(*w),
            NatSyn::Add(x, y, xs, ys) => {
                let (fx, fy) = (Self::syn_form(&self.forms, x), Self::syn_form(&self.forms, y));
                let (px, py) = (self.reify(x, xs), self.reify(y, ys));
                let _ = source;
                format!("trans(trans(@cong(λ (t: Nat) => {}, {xs}, {}, {px}), @cong(λ (t: Nat) => {}, {ys}, {}, {py})), {})",
                    add("t", ys), self.spell(&fx), add(&self.spell(&fx), "t"), self.spell(&fy), self.merge_proof(&fx, &fy))
            }
            NatSyn::Scale(k, on_left, x, xs) => {
                let fx = Self::syn_form(&self.forms, x);
                let px = self.reify(x, xs);
                let left = format!("trans(@cong(λ (t: Nat) => {}, {xs}, {}, {px}), {})", mul(&k.to_string(), "t"), self.spell(&fx), self.scale_proof(*k, &fx));
                if *on_left { left } else { format!("trans(nat::Nat::mul_comm({xs}, {k}), {left})") }
            }
        }
    }

    fn top(&self, n: usize) -> String {
        format!("nat::Nat::pow(2, {})", self.walk.nodes[n].width)
    }

    fn obligation(&mut self, statement: String, shown: String, why: String) -> usize {
        self.obligations.push(Obligation { statement, shown, why });
        self.obligations.len() - 1
    }

    /// Where `n`'s bound comes from: a parent when one passes it down, the
    /// range when `n` is a leaf, else `omega` at `n` itself.
    fn plan_bound(&mut self, n: usize, seen: &mut HashSet<usize>) {
        if self.bound_from[n].is_some() {
            return;
        }
        let from = if matches!(self.walk.nodes[n].kind, Kind::Leaf) {
            BoundFrom::Range
        } else if let Some(from) = self.parents[n].iter().find_map(|&p| match self.walk.nodes[p].kind {
            Kind::Add(a, _) => Some(BoundFrom::AddParent { parent: p, left: a == n }),
            Kind::Sub(_, b) if b == n => Some(BoundFrom::SubParent { parent: p }),
            _ => None,
        }) {
            from
        } else {
            let (p, q) = self.forms[n].clone();
            let statement = lt(&self.spell(&p), &add(&self.top(n), &self.spell(&q)));
            let shown = format!("{} < {} + ({})", self.shown(&p), self.top(n), self.shown(&q));
            let node = &self.walk.nodes[n];
            let why = if let Kind::Value(..) = node.kind {
                format!("`{}` does not fit {} bits", node.word, node.width)
            } else {
                format!("`{}` may overflow {} bits", node.word, node.width)
            };
            BoundFrom::Obligation(self.obligation(statement, shown, why))
        };
        self.bound_from[n] = Some(from);
        match from {
            BoundFrom::AddParent { parent, left } => {
                self.plan_bound(parent, seen);
                if let Kind::Add(a, b) = self.walk.nodes[parent].kind {
                    self.plan(if left { b } else { a }, seen);
                }
            }
            BoundFrom::SubParent { parent } => {
                self.plan(parent, seen);
                if let Kind::Sub(a, _) = self.walk.nodes[parent].kind {
                    self.plan_bound(a, seen);
                }
            }
            _ => {}
        }
    }

    /// Plan every side condition `n`'s fact and sign depend on.
    fn plan(&mut self, n: usize, seen: &mut HashSet<usize>) {
        if !seen.insert(n) {
            return;
        }
        match self.walk.nodes[n].kind.clone() {
            Kind::Leaf => {}
            Kind::Value(_, _, syn) => {
                self.plan_bound(n, seen);
                self.plan_syn(&syn, seen);
            }
            Kind::Add(a, b) => {
                self.plan_bound(n, seen);
                self.plan(a, seen);
                self.plan(b, seen);
            }
            Kind::Sub(a, b) => {
                let (p, q) = self.forms[n].clone();
                let statement = le(&self.spell(&q), &self.spell(&p));
                let shown = format!("{} <= {}", self.shown(&q), self.shown(&p));
                let why = format!("`{}` may borrow", self.walk.nodes[n].word);
                let i = self.obligation(statement, shown, why);
                self.fits.insert(n, i);
                self.plan(a, seen);
                self.plan(b, seen);
            }
        }
    }

    fn plan_syn(&mut self, syn: &NatSyn, seen: &mut HashSet<usize>) {
        match syn {
            NatSyn::Add(x, y, _, _) => {
                self.plan_syn(x, seen);
                self.plan_syn(y, seen);
            }
            NatSyn::Scale(_, _, x, _) => self.plan_syn(x, seen),
            NatSyn::Word(w) => self.plan(*w, seen),
            _ => {}
        }
    }

    fn emit(&mut self, name: String, line: String) -> String {
        if self.emitted.insert(name.clone()) {
            self.lines.push(line);
        }
        name
    }

    /// The two merges an `add`/`sub` node's lemma and bounds take.
    fn merges(&mut self, n: usize) -> (String, String) {
        let (mp, mq) = (format!("__bv_mp{n}"), format!("__bv_mq{n}"));
        if self.emitted.contains(&mp) {
            return (mp, mq);
        }
        let (ap, aq, bp, bq, sub) = match self.walk.nodes[n].kind {
            Kind::Add(a, b) => (self.forms[a].0.clone(), self.forms[a].1.clone(), self.forms[b].0.clone(), self.forms[b].1.clone(), false),
            Kind::Sub(a, b) => (self.forms[a].0.clone(), self.forms[a].1.clone(), self.forms[b].0.clone(), self.forms[b].1.clone(), true),
            _ => unreachable!(),
        };
        let (p, q) = self.forms[n].clone();
        let (pl, pr, ql, qr) = if sub { (&ap, &bq, &aq, &bp) } else { (&ap, &bp, &aq, &bq) };
        let line = format!("have {mp}: ({} = {}) = {};", add(&self.spell(pl), &self.spell(pr)), self.spell(&p), self.merge_proof(pl, pr));
        self.emit(mp.clone(), line);
        let line = format!("have {mq}: ({} = {}) = {};", add(&self.spell(ql), &self.spell(qr)), self.spell(&q), self.merge_proof(ql, qr));
        self.emit(mq.clone(), line);
        (mp, mq)
    }

    /// `n`'s fact: `n.toNat() + Q = P`.
    fn fact(&mut self, n: usize) -> String {
        let name = format!("__bv_f{n}");
        if self.emitted.contains(&name) {
            return name;
        }
        let node = self.walk.nodes[n].clone();
        let (w, word) = (&node.width, &node.word);
        let (p, q) = self.forms[n].clone();
        let proof = match &node.kind {
            Kind::Leaf => format!("bitvec_omega::form_atom(bitvec::BitVec::toNat({word}))"),
            Kind::Value(lemma, c, syn) => {
                let lemma = if *lemma == "ofNat_row" { "ofNat_form" } else { "word_of_nat_form" };
                let r = self.reify(syn, c);
                let b = self.bound(n);
                format!("bitvec_omega::{lemma}({w}, {c}, {}, {r}, {b})", self.spell(&p))
            }
            Kind::Add(a, b) | Kind::Sub(a, b) => {
                let (a, b) = (*a, *b);
                let (fa, fb) = (self.fact(a), self.fact(b));
                let (mp, mq) = self.merges(n);
                let args = format!("{w}, {}, {}, {}, {}, {}, {}, {}, {}, {fa}, {fb}, {mp}, {mq}",
                    self.walk.nodes[a].word, self.walk.nodes[b].word,
                    self.spell(&self.forms[a].1), self.spell(&self.forms[a].0), self.spell(&self.forms[b].1), self.spell(&self.forms[b].0),
                    self.spell(&q), self.spell(&p));
                if let Kind::Add(..) = node.kind {
                    format!("bitvec_omega::add_form({args}, {})", self.bound(n))
                } else {
                    format!("bitvec_omega::sub_form({args}, {})", self.paths[self.fits[&n]])
                }
            }
        };
        let line = format!("have {name}: ({} = {}) = {proof};", add(&format!("bitvec::BitVec::toNat({word})"), &self.spell(&q)), self.spell(&p));
        self.emit(name, line)
    }

    /// `P < 2^n + Q` for `n`.
    fn bound(&mut self, n: usize) -> String {
        let name = format!("__bv_b{n}");
        if self.emitted.contains(&name) {
            return name;
        }
        let top = self.top(n);
        let quad = |e: &Self, x: usize| format!("{}, {}", e.spell(&e.forms[x].0), e.spell(&e.forms[x].1));
        let proof = match self.bound_from[n].expect("every bound is planned before it is emitted") {
            BoundFrom::Range => {
                let f = self.fact(n);
                let (p, q) = &self.forms[n];
                format!("bitvec_omega::range({}, {}, {}, {}, {f})", self.walk.nodes[n].width, self.walk.nodes[n].word, self.spell(q), self.spell(p))
            }
            BoundFrom::Obligation(i) => self.paths[i].clone(),
            BoundFrom::AddParent { parent, left } => {
                let Kind::Add(a, b) = self.walk.nodes[parent].kind else { unreachable!() };
                let pb = self.bound(parent);
                let (mp, mq) = self.merges(parent);
                let other = self.sign(if left { b } else { a });
                format!("bitvec_omega::bound_{}({}, {}, {}, {top}, {mp}, {mq}, {pb}, {other})",
                    if left { "left" } else { "right" }, quad(self, a), quad(self, b), quad(self, parent))
            }
            BoundFrom::SubParent { parent } => {
                let Kind::Sub(a, b) = self.walk.nodes[parent].kind else { unreachable!() };
                let ab = self.bound(a);
                let (mp, mq) = self.merges(parent);
                format!("bitvec_omega::bound_sub({}, {}, {}, {top}, {mp}, {mq}, {}, {ab})",
                    quad(self, a), quad(self, b), quad(self, parent), self.paths[self.fits[&parent]])
            }
        };
        let (p, q) = &self.forms[n];
        let line = format!("have {name}: ({}) = {proof};", lt(&self.spell(p), &add(&top, &self.spell(q))));
        self.emit(name, line)
    }

    /// `Q <= P` for `n`, without its bound.
    fn sign(&mut self, n: usize) -> String {
        let name = format!("__bv_s{n}");
        if self.emitted.contains(&name) {
            return name;
        }
        let (p, q) = self.forms[n].clone();
        let proof = if q.is_zero() {
            "trivial".to_string()
        } else {
            match self.walk.nodes[n].kind {
                Kind::Sub(..) => self.paths[self.fits[&n]].clone(),
                Kind::Add(a, b) => {
                    let (sa, sb) = (self.sign(a), self.sign(b));
                    let (mp, mq) = self.merges(n);
                    format!("bitvec_omega::sign_add({}, {}, {}, {}, {}, {}, {mp}, {mq}, {sa}, {sb})",
                        self.spell(&self.forms[a].0), self.spell(&self.forms[a].1), self.spell(&self.forms[b].0), self.spell(&self.forms[b].1),
                        self.spell(&p), self.spell(&q))
                }
                _ => unreachable!("only a subtraction gives a word a nonzero `Q`"),
            }
        };
        let line = format!("have {name}: ({}) = {proof};", le(&self.spell(&q), &self.spell(&p)));
        self.emit(name, line)
    }
}

/// The side conditions a set of words needs, planned on a copy.
fn plan_for(walk: &Walk, nodes: &[usize]) -> Vec<Obligation> {
    let mut e = Emitter::new(walk);
    let mut seen = HashSet::new();
    for &n in nodes {
        e.plan(n, &mut seen);
    }
    e.obligations
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
        found: Vec::new(),
        stated: Default::default(),
    };
    let facts_in_scope = local_facts(elab, cx);
    for (_, ty) in &facts_in_scope {
        stated_words(elab, cx, ty, &mut walk.stated);
    }
    walk.scan_type(expected)?;
    let mut subjects: Vec<usize> = std::mem::take(&mut walk.found);
    if walk.nodes.is_empty() {
        return Err("found no `toNat` of a word in the goal; use `omega`".into());
    }
    // A fact in scope over a word the walk takes apart is restated over the
    // word's value, like the goal. Its words are optional: a word that
    // appears only there may overflow or borrow where the goal's do not, so
    // its new side conditions are tried first, and the fact is left alone
    // when one fails.
    let mut restated: Vec<(String, Type)> = Vec::new();
    for (name, ty) in facts_in_scope {
        if !is_nat_relation(elab, cx, &ty) {
            continue;
        }
        let before = walk.clone();
        walk.scan_type(&ty)?;
        let found = std::mem::take(&mut walk.found);
        if !found.iter().any(|&n| !matches!(walk.nodes[n].kind, Kind::Leaf)) {
            walk = before;
            continue;
        }
        let old: HashSet<String> = plan_for(&before, &subjects).into_iter().map(|o| o.statement).collect();
        let mut all = subjects.clone();
        all.extend(found.iter().copied());
        let new: Vec<Obligation> = plan_for(&walk, &all).into_iter().filter(|o| !old.contains(&o.statement)).collect();
        if new.iter().all(|o| holds(elab, cx, &walk, o)) {
            subjects.extend(found);
            restated.push((name, ty));
        } else {
            walk = before;
        }
    }
    subjects.retain(|&n| !matches!(walk.nodes[n].kind, Kind::Leaf));
    subjects.sort_unstable();
    subjects.dedup();

    let prelude = prelude(&walk);
    let mut e = Emitter::new(&walk);
    let mut seen = HashSet::new();
    for &n in &subjects {
        e.plan(n, &mut seen);
    }
    let mut source = format!("{{\n{prelude}\n");
    // The goal over Nat variables for the words taken apart, proved before
    // any fact exists: `omega` must never meet a composite word's `toNat`,
    // where its atom fallback would reduce into the bits.
    if !subjects.is_empty() {
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
        for &n in &subjects {
            binders.push_str(&format!("(__bv_w{n}: Nat) → "));
            names.push(format!("__bv_w{n}"));
        }
        for &n in &subjects {
            let (p, q) = &e.forms[n];
            binders.push_str(&format!("(__bv_h{n}: {} = {}) → ", add(&format!("__bv_w{n}"), &e.spell(q)), e.spell(p)));
            names.push(format!("__bv_h{n}"));
        }
        // Rebinding a fact under its own name hides the original from the
        // `omega` inside.
        for (name, ty) in &restated {
            let spelled = elab.spell_type_source(cx, ty).ok_or("could not spell a fact in scope")?;
            binders.push_str(&format!("({name}: {}) → ", generalise(spelled)));
            names.push(name.clone());
        }
        source.push_str(&format!("have __bv_goal: ({binders}{goal}) = λ {} => omega;\n", names.join(" ")));
    }
    // Every side condition is one leaf of a *balanced* conjunction, proved
    // by `omega` in the entry context, where no fact is in scope (§2).
    let count = e.obligations.len();
    let mut paths = vec![String::new(); count];
    if count > 0 {
        let statements: Vec<&str> = e.obligations.iter().map(|o| o.statement.as_str()).collect();
        let (statement, proof) = balanced(&statements, 0, &mut paths, String::new());
        source.push_str(&format!("have __bv_obligations: ({statement}) = {proof};\n"));
    }
    e.paths = paths.iter().map(|p| format!("__bv_obligations{p}")).collect();
    let mut arguments = Vec::new();
    for &n in &subjects {
        arguments.push(format!("bitvec::BitVec::toNat({})", walk.nodes[n].word));
    }
    for &n in &subjects {
        let fact = e.fact(n);
        arguments.push(fact);
    }
    for (name, _) in &restated {
        arguments.push(name.clone());
    }
    for line in &e.lines {
        source.push_str(line);
        source.push('\n');
    }
    // The last step must not see the bundle: `omega` would split it.
    if count > 0 {
        source.push_str("have __bv_obligations = trivial;\n");
    }
    if subjects.is_empty() {
        source.push_str("omega\n}");
    } else {
        source.push_str(&format!("__bv_goal({})\n}}", arguments.join(", ")));
    }
    Ok(Generated { source, prelude, obligations: e.obligations })
}

/// The bindings before any side condition: each leaf's range, for `omega`
/// to read.
fn prelude(walk: &Walk) -> String {
    let mut out = Vec::new();
    for (i, node) in walk.nodes.iter().enumerate() {
        if let Kind::Leaf = node.kind {
            let statement = lt(&format!("bitvec::BitVec::toNat({})", node.word), &format!("nat::Nat::pow(2, {})", node.width));
            out.push(format!("have __bv_range_{i}: ({statement}) = bitvec::BitVec::toNat_lt_pow({}, {});", node.width, node.word));
        }
    }
    out.join("\n")
}

/// Whether `omega` proves `o` in the entry context, for an optional word.
fn holds(elab: &Elaborator, cx: &Cx, walk: &Walk, o: &Obligation) -> bool {
    let source = format!("{{\n{}\nhave __bv_side: ({}) = omega;\n__bv_side\n}}", prelude(walk), o.statement);
    let Ok(expr) = parse_generated_expr(&source) else { return false };
    elab.generated_scope(|me| me.elab_infer(cx, &expr)).is_ok()
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
fn stated_words(elab: &Elaborator, cx: &Cx, ty: &Type, out: &mut HashSet<String>) {
    fn go(elab: &Elaborator, cx: &Cx, tm: &Rc<Term>, out: &mut HashSet<String>) {
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
