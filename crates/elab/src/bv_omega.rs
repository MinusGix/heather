//! `bv_omega`: word arithmetic lifted to Nat (docs/tactics/bv-omega-design.md).
//!
//! A generator, not a solver. It finds every `toNat` of a word in the goal
//! and in the facts in scope, takes each word apart through `add`, `sub`,
//! `ofNat`, `word_of_nat`, byte extraction and definitions that step to them,
//! and writes a proof as source. Each word's value is stated as `w.toNat() + Q = P` over
//! *forms*, `c₁ * a₁ + (… + k)` in a fixed atom order: forms add one lemma
//! step per atom, with literal coefficients the checker adds, so no fact
//! needs `omega`. Only the outermost words' bounds and each subtraction's
//! borrow go to `omega`; every other bound is passed down by lemma. The caller elaborates the source at the goal, so a wrong
//! fact is refused by the checker, never trusted.

use std::collections::{HashMap, HashSet};
use heather_kernel::rc::Rc;

use heather_kernel::term::{Term, Type};

use crate::omega_cert::{integer_source, local_facts, named_args, nat_term_source, parse_generated_expr};
use crate::oracle::Unfold;
use crate::{Cx, Elaborator};


pub(crate) struct Generated {
    /// The proof, as source.
    pub source: String,
    /// The bindings every side condition is proved after (the atoms and each
    /// leaf's range), which a failure re-check needs in scope.
    pub prelude: String,
    /// Each side condition and the word it came from, in bundle order.
    pub obligations: Vec<Obligation>,
    /// Whether a careful attempt differs from this one: the goal was read
    /// off a word's fact, or a fact was restated untried.
    pub retry: bool,
}

#[derive(Clone)]
pub(crate) struct Obligation {
    /// As generated source: qualified calls, like the rest of the proof.
    pub statement: String,
    /// As the refusal quotes it, with operators.
    pub shown: String,
    pub why: String,
    /// Over no atoms: a comparison of literals, which `trivial` decides.
    pub closed: bool,
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
    /// A leaf whose value a fact in scope states (`toNat(w) = v`): the
    /// fact's proof (as `toNat(w) = v`), `v` spelled, and `v` read. Its bound
    /// is still its range.
    Defined(String, String, NatSyn),
}

#[derive(Clone)]
struct Node {
    /// The word as the walk met it, spelled for re-parsing.
    word: String,
    width: String,
    kind: Kind,
}

impl Node {
    /// Not taken apart: a leaf, or one whose value a fact states.
    fn is_leaf(&self) -> bool {
        matches!(self.kind, Kind::Leaf | Kind::Defined(..))
    }
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
    /// Words a fact in scope gives a value, `toNat(w) = v` either way round:
    /// the fact's proof as `toNat(w) = v`, and `v`.
    defined: HashMap<String, (String, Rc<Term>)>,
    /// The defined words being read, so a cycle of definitions ends in a leaf.
    defining: HashSet<String>,
    /// Decompositions and reflected comparisons, stated before arithmetic.
    bridges: Vec<(String, String, String)>,
    splits: HashMap<String, (String, String)>,
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
            Kind::Value(_, _, syn) | Kind::Defined(_, _, syn) => self.syn_subtracts(syn),
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
        let Some(w) = self.elab.spell_term_source(self.cx, width) else { return Ok(None) };
        self.word_at(w, word)
    }

    fn word_at(&mut self, w: String, word: &Rc<Term>) -> Result<Option<usize>, String> {
        let Some(spelled) = self.elab.spell_term_source(self.cx, word) else {
            return Ok(None);
        };
        if let Some(&node) = self.node_index.get(&spelled) {
            return Ok(Some(node));
        }

        let shape = if self.stated.contains(&spelled) { self.known(word).unwrap_or(Shape::Leaf) } else { self.shape(word) };
        let split = match &shape { Shape::Split(n, m, x, low) => Some((n.clone(), m.clone(), x.clone(), *low)), _ => None };
        let kind = match shape {
            Shape::Add(a, b) => match (self.word_at(w.clone(), &a)?, self.word_at(w.clone(), &b)?) {
                (Some(na), Some(nb)) => Kind::Add(na, nb),
                _ => Kind::Leaf,
            },
            Shape::Sub(a, b) => match (self.word_at(w.clone(), &a)?, self.word_at(w.clone(), &b)?) {
                (Some(na), Some(nb)) => Kind::Sub(na, nb),
                _ => Kind::Leaf,
            },
            Shape::Value(lemma, c) => {
                let c_source = nat_term_source(self.elab, self.cx, &c)?;
                Kind::Value(lemma, c_source, self.nat(&c)?)
            }
            Shape::Leaf | Shape::Split(..) => self.defined_kind(&spelled)?,
        };
        if let Kind::Leaf = kind {
            self.atom(format!("bitvec::BitVec::toNat({spelled})"));
        }
        let index = self.nodes.len();
        self.node_index.insert(spelled.clone(), index);
        self.nodes.push(Node { word: spelled.clone(), width: w.clone(), kind });
        if let Some((n, m, x, is_low)) = split {
            let x_source = self.elab.spell_term_source(self.cx, &x).ok_or("could not spell split word")?;
            let ns = nat_term_source(self.elab, self.cx, &n)?;
            let ms = nat_term_source(self.elab, self.cx, &m)?;
            let key = format!("{ns}, {ms}, {x_source}");
            if let Some((low, high)) = self.splits.get(&key) {
                let half = if is_low { low } else { high };
                if half != &spelled {
                    self.bridges.push((format!("__bv_alias{}", self.bridges.len()),
                        format!("bitvec::BitVec::toNat({spelled}) = bitvec::BitVec::toNat({half})"), "refl".into()));
                }
            } else {
                // Register both halves as leaves before walking the input,
                // so the companion extraction cannot reopen this split.
                let low = if is_low { spelled.clone() } else { format!("bitvec::BitVec::take_low({key})") };
                let high = if is_low { format!("bitvec::BitVec::drop_low({key})") } else { spelled.clone() };
                self.splits.insert(key.clone(), (low.clone(), high.clone()));
                for (word, width) in [(&low, &ns), (&high, &ms)] {
                    if !self.node_index.contains_key(word) {
                        let i = self.nodes.len();
                        self.node_index.insert(word.clone(), i);
                        self.atom(format!("bitvec::BitVec::toNat({word})"));
                        self.nodes.push(Node { word: word.clone(), width: width.clone(), kind: Kind::Leaf });
                    }
                }
                let width = self.literal(&n).zip(self.literal(&m))
                    .and_then(|(n, m)| n.checked_add(m))
                    .map(|width| width.to_string()).unwrap_or_else(|| add(&ms, &ns));
                self.word_at(width, &x)?;
                let power = match self.literal(&n).and_then(|n| u32::try_from(n).ok()).filter(|n| *n < 127) {
                    Some(n) => (1i128 << n).to_string(),
                    None => format!("nat::Nat::pow(2, {ns})"),
                };
                let name = format!("__bv_split{}", self.bridges.len());
                let statement = format!("bitvec::BitVec::toNat({x_source}) = {}", add(&format!("bitvec::BitVec::toNat({low})"), &mul(&power, &format!("bitvec::BitVec::toNat({high})"))));
                self.bridges.push((name, statement, format!("bitvec_nat::toNat_take_drop({key})")));
            }
        }
        if let Kind::Leaf = self.nodes[index].kind {
            self.mask_bound(&w, word, &spelled)?;
        }
        Ok(Some(index))
    }

    /// A word masked by another, `x & y`, is at most the mask
    /// (issues/bv-omega-masked-word-bound.md). Its leaf gets that fact beside
    /// its range: `<= m` when the mask is the numeral `m`, else `<= toNat(y)`,
    /// the mask read as a word of its own.
    fn mask_bound(&mut self, w: &str, word: &Rc<Term>, spelled: &str) -> Result<(), String> {
        let Some(args) = named_args(self.elab, word, "bitvec::BitVec::band") else { return Ok(()) };
        let [_, x, y] = args.as_slice() else { return Ok(()) };
        let (Some(xs), Some(ys)) = (self.elab.spell_term_source(self.cx, x), self.elab.spell_term_source(self.cx, y)) else {
            return Ok(());
        };
        let value = format!("bitvec::BitVec::toNat({spelled})");
        let numeral = named_args(self.elab, y, "bitvec::BitVec::ofNat")
            .and_then(|args| args.get(1).and_then(|c| self.literal(c)));
        let (statement, proof) = match numeral {
            Some(m) => (le(&value, &m.to_string()), format!("bitvec_nat::BitVec::toNat_band_ofNat_le({w}, {xs}, {m})")),
            None => {
                self.word_at(w.to_string(), y)?;
                (le(&value, &format!("bitvec::BitVec::toNat({ys})")), format!("bitvec_nat::BitVec::toNat_band_le_right({w}, {xs}, {ys})"))
            }
        };
        if !self.bridges.iter().any(|(_, other, _)| other == &statement) {
            self.bridges.push((format!("__bv_mask{}", self.bridges.len()), statement, proof));
        }
        Ok(())
    }

    /// A leaf's value from the fact that states it, if one does.
    fn defined_kind(&mut self, spelled: &str) -> Result<Kind, String> {
        let Some((proof, value)) = self.defined.get(spelled).cloned() else {
            return Ok(Kind::Leaf);
        };
        if !self.defining.insert(spelled.to_string()) {
            return Ok(Kind::Leaf);
        }
        let read = nat_term_source(self.elab, self.cx, &value).and_then(|source| Ok((source, self.nat(&value)?)));
        self.defining.remove(spelled);
        let (source, syn) = read?;
        Ok(Kind::Defined(proof, source, syn))
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
        oracle
            .unfold_to(&self.cx.gamma, word, Unfold::WordShape, |reduct| self.known(&Rc::new(reduct)))
            .unwrap_or(Shape::Leaf)
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
        for name in ["bitvec::BitVec::take_low", "bitvec::BitVec::drop_low"] {
            if let Some(args) = named_args(self.elab, word, name)
                && let [n, m, x] = args.as_slice()
            {
                return Some(Shape::Split(Rc::clone(n), Rc::clone(m), Rc::clone(x), name.ends_with("take_low")));
            }
        }
        None
    }
}

enum Shape {
    Split(Rc<Term>, Rc<Term>, Rc<Term>, bool),
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
    /// A fact in scope that bounds its value by a literal: stated bound `i`.
    Stated(usize),
}

/// A fact in scope `x < k` (or `x <= k`, `strict` false) with `k` a literal.
#[derive(Clone)]
struct StatedBound {
    fact: String,
    strict: bool,
    x: String,
    syn: NatSyn,
    k: i128,
}

impl StatedBound {
    /// Whether `k` is within a word of `width` bits: `x < 2^width` follows.
    fn fits(&self, width: &str) -> bool {
        let Ok(width) = width.parse::<u32>() else { return false };
        if width >= 127 {
            return true;
        }
        let top = 1i128 << width;
        if self.strict { self.k <= top } else { self.k < top }
    }
}

/// The literal bounds facts in scope state: `x < k` or `x <= k`.
fn stated_bounds(walk: &mut Walk, facts: &[(String, Type)]) -> Vec<StatedBound> {
    let mut out = Vec::new();
    for (name, ty) in facts {
        let Type::El { tm, .. } = ty else { continue };
        for (relation, strict) in [("nat::Nat::Lt", true), ("nat::Nat::Le", false)] {
            if let Some(args) = named_args(walk.elab, tm, relation)
                && let [x, k] = args.as_slice()
                && let Some(k) = walk.literal(k)
                && let Ok(source) = nat_term_source(walk.elab, walk.cx, x)
                && integer_source(&source).is_none()
                && let Ok(syn) = walk.nat(x)
            {
                out.push(StatedBound { fact: name.clone(), strict, x: source, syn, k });
            }
        }
    }
    out
}

struct Emitter<'w, 'a> {
    walk: &'w Walk<'a>,
    /// Bounds the facts in scope state (`BoundFrom::Stated`).
    stated: Vec<StatedBound>,
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
    fn new(walk: &'w Walk<'a>, stated: &[StatedBound]) -> Self {
        let mut forms: Vec<(Form, Form)> = Vec::new();
        let mut parents = vec![Vec::new(); walk.nodes.len()];
        for (i, node) in walk.nodes.iter().enumerate() {
            let pq = match &node.kind {
                Kind::Leaf => (Form::atom(walk.atom_index[&format!("bitvec::BitVec::toNat({})", node.word)]), Form::default()),
                Kind::Value(_, _, syn) | Kind::Defined(_, _, syn) => (Self::syn_form(&forms, syn), Form::default()),
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
            stated: stated.to_vec(),
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
                format!("trans(bitvec_omega::form_step({c}, {d}, {}, {}, {}), @cong(λ (__bv_t: Nat) => {}, {}, {}, {}))",
                    self.atom(a), self.spell(&x), self.spell(&y), add(&mul(&(c + d).to_string(), &self.atom(a)), "__bv_t"), add(&self.spell(&x), &self.spell(&y)), self.spell(&r), self.merge_proof(&x, &y))
            }
            (Some(&(a, c)), next) if next.is_none_or(|&(b, _)| a < b) => {
                let x = rest(f);
                let r = merge_forms(&x, g);
                format!("trans(bitvec_omega::form_left({c}, {}, {}, {}), @cong(λ (__bv_t: Nat) => {}, {}, {}, {}))",
                    self.atom(a), self.spell(&x), self.spell(g), add(&mul(&c.to_string(), &self.atom(a)), "__bv_t"), add(&self.spell(&x), &self.spell(g)), self.spell(&r), self.merge_proof(&x, g))
            }
            (_, Some(&(b, d))) => {
                let y = rest(g);
                let r = merge_forms(f, &y);
                format!("trans(bitvec_omega::form_right({}, {d}, {}, {}), @cong(λ (__bv_t: Nat) => {}, {}, {}, {}))",
                    self.spell(f), self.atom(b), self.spell(&y), add(&mul(&d.to_string(), &self.atom(b)), "__bv_t"), add(&self.spell(f), &self.spell(&y)), self.spell(&r), self.merge_proof(f, &y))
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
                format!("trans(bitvec_omega::form_scale({k}, {c}, {}, {}), @cong(λ (__bv_t: Nat) => {}, {}, {}, {}))",
                    self.atom(a), self.spell(&x), add(&mul(&(k * c).to_string(), &self.atom(a)), "__bv_t"), mul(&k.to_string(), &self.spell(&x)), self.spell(&r), self.scale_proof(k, &x))
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
                format!("trans(trans(@cong(λ (__bv_t: Nat) => {}, {xs}, {}, {px}), @cong(λ (__bv_t: Nat) => {}, {ys}, {}, {py})), {})",
                    add("__bv_t", ys), self.spell(&fx), add(&self.spell(&fx), "__bv_t"), self.spell(&fy), self.merge_proof(&fx, &fy))
            }
            NatSyn::Scale(k, on_left, x, xs) => {
                let fx = Self::syn_form(&self.forms, x);
                let px = self.reify(x, xs);
                let left = format!("trans(@cong(λ (__bv_t: Nat) => {}, {xs}, {}, {px}), {})", mul(&k.to_string(), "__bv_t"), self.spell(&fx), self.scale_proof(*k, &fx));
                if *on_left { left } else { format!("trans(nat::Nat::mul_comm({xs}, {k}), {left})") }
            }
        }
    }

    fn top(&self, n: usize) -> String {
        format!("nat::Nat::pow(2, {})", self.walk.nodes[n].width)
    }

    fn obligation(&mut self, statement: String, shown: String, why: String, closed: bool) -> usize {
        self.obligations.push(Obligation { statement, shown, why, closed });
        self.obligations.len() - 1
    }

    /// Whether a Nat's syntax reads the word `n`.
    fn syn_reads(syn: &NatSyn, n: usize) -> bool {
        match syn {
            NatSyn::Add(x, y, _, _) => Self::syn_reads(x, n) || Self::syn_reads(y, n),
            NatSyn::Scale(_, _, x, _) => Self::syn_reads(x, n),
            NatSyn::Word(w) => *w == n,
            _ => false,
        }
    }

    /// Where `n`'s bound comes from: a parent when one passes it down, the
    /// range when `n` is a leaf, else `omega` at `n` itself.
    fn plan_bound(&mut self, n: usize, seen: &mut HashSet<usize>) {
        if self.bound_from[n].is_some() {
            return;
        }
        let from = if matches!(self.walk.nodes[n].kind, Kind::Leaf | Kind::Defined(..)) {
            BoundFrom::Range
        } else if let Some(from) = self.parents[n].iter().find_map(|&p| match self.walk.nodes[p].kind {
            Kind::Add(a, _) if !self.bound_depends_on(p, n) => Some(BoundFrom::AddParent { parent: p, left: a == n }),
            Kind::Sub(a, b) if b == n && !self.bound_depends_on(a, n) => Some(BoundFrom::SubParent { parent: p }),
            _ => None,
        }) {
            from
        } else if let Some(i) = self.stated.iter().position(|b| {
            let (p, q) = &self.forms[n];
            // Not a bound stated of `n` itself: reading it would need
            // `n`'s fact, which needs this bound (`h: (j + 16).toNat() < 64`
            // says nothing about whether `j + 16` wrapped).
            q.is_zero() && Self::syn_form(&self.forms, &b.syn) == *p && b.fits(&self.walk.nodes[n].width)
                && !Self::syn_reads(&b.syn, n)
        }) {
            BoundFrom::Stated(i)
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
            let closed = p.terms.is_empty() && q.terms.is_empty();
            BoundFrom::Obligation(self.obligation(statement, shown, why, closed))
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

    /// Bounds are shared with word nodes. Passing a subtraction's bound
    /// from its minuend can otherwise make a cycle, as in `w.sub(w)` or
    /// `w.add(w).sub(w)`. Reject the edge that would close that cycle;
    /// an independent bound (a stated fact or an obligation) is needed.
    fn bound_depends_on(&self, mut from: usize, target: usize) -> bool {
        loop {
            if from == target {
                return true;
            }
            match self.bound_from[from] {
                Some(BoundFrom::AddParent { parent, .. }) => from = parent,
                Some(BoundFrom::SubParent { parent }) => {
                    let Kind::Sub(a, _) = self.walk.nodes[parent].kind else { unreachable!() };
                    from = a;
                }
                _ => return false,
            }
        }
    }

    /// Plan every side condition `n`'s fact and sign depend on.
    fn plan(&mut self, n: usize, seen: &mut HashSet<usize>) {
        if !seen.insert(n) {
            return;
        }
        match self.walk.nodes[n].kind.clone() {
            Kind::Leaf => {}
            Kind::Defined(_, _, syn) => self.plan_syn(&syn, seen),
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
                let closed = p.terms.is_empty() && q.terms.is_empty();
                let i = self.obligation(statement, shown, why, closed);
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
            Kind::Leaf => format!("bitvec_omega::form_leaf(bitvec::BitVec::toNat({word}))"),
            Kind::Defined(given, v, syn) => {
                let r = self.reify(syn, v);
                format!("bitvec_omega::leaf_value(bitvec::BitVec::toNat({word}), {v}, {}, {given}, {r})", self.spell(&p))
            }
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
            BoundFrom::Stated(i) => {
                let b = self.stated[i].clone();
                let hx = self.reify(&b.syn, &b.x);
                let lemma = if b.strict { "below_top" } else { "below_top_le" };
                format!("bitvec_omega::{lemma}({}, {}, {}, {top}, {}, {hx}, trivial)", b.x, self.spell(&self.forms[n].0), b.k, b.fact)
            }
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
fn plan_for(walk: &Walk, stated: &[StatedBound], nodes: &[usize]) -> Vec<Obligation> {
    let mut e = Emitter::new(walk, stated);
    let mut seen = HashSet::new();
    for &n in nodes {
        e.plan(n, &mut seen);
    }
    e.obligations
}

/// What the goal's other side is, when the goal is a word's fact itself.
enum Target {
    /// `toNat(w) = r`, `r` of the fact's form `P` (its `Q` zero).
    Whole(NatSyn, String),
    /// `toNat(w) = a - b`, `a` of the form `P` and `b` of the form `Q`.
    Diff(NatSyn, String, NatSyn, String),
}

/// The goal as a word's fact, when it is one: `toNat(w) = r` (or `r =
/// toNat(w)`) where `r` reads as the forms the walk computed for `w`. The
/// goal's node, whether the equation is flipped, and `r`.
fn direct_goal(walk: &mut Walk, expected: &Type) -> Option<(usize, bool, Target)> {
    let Type::Id { ty, lhs, rhs, .. } = expected else { return None };
    if walk.elab.display_type(walk.cx, ty) != "Nat" {
        return None;
    }
    for (flipped, side, other) in [(false, lhs, rhs), (true, rhs, lhs)] {
        let Some(args) = named_args(walk.elab, side, "bitvec::BitVec::toNat") else { continue };
        let [_, word] = args.as_slice() else { continue };
        let Some(spelled) = walk.elab.spell_term_source(walk.cx, word) else { continue };
        let Some(&n) = walk.node_index.get(&spelled) else { continue };
        if matches!(walk.nodes[n].kind, Kind::Leaf) {
            continue;
        }
        let saved = walk.clone();
        let read = |walk: &mut Walk, t: &Rc<Term>| -> Option<(NatSyn, String)> {
            Some((walk.nat(t).ok()?, nat_term_source(walk.elab, walk.cx, t).ok()?))
        };
        let target = match named_args(walk.elab, other, "nat::Nat::sub").as_deref() {
            Some([a, b]) => read(walk, a).zip(read(walk, b)).map(|((sa, a), (sb, b))| Target::Diff(sa, a, sb, b)),
            _ => read(walk, other).map(|(syn, source)| Target::Whole(syn, source)),
        };
        let matches = target.as_ref().is_some_and(|target| {
            let e = Emitter::new(walk, &[]);
            let (p, q) = &e.forms[n];
            match target {
                Target::Whole(syn, _) => q.is_zero() && Emitter::syn_form(&e.forms, syn) == *p,
                Target::Diff(sa, _, sb, _) => Emitter::syn_form(&e.forms, sa) == *p && Emitter::syn_form(&e.forms, sb) == *q,
            }
        });
        if matches {
            return Some((n, flipped, target?));
        }
        *walk = saved;
    }
    None
}

/// Which constructor of `Bool` a term spells, if it spells one.
fn bool_flag(elab: &Elaborator, cx: &Cx, flag: &Rc<Term>) -> Option<bool> {
    let source = elab.spell_term_source(cx, flag)?;
    // The speller may use the bare constructor name. In particular,
    // `False` also names logic's empty type under these imports.
    let qualified = if source.contains("::") { source } else { format!("bool::{source}") };
    let (ind, ctor) = elab.lookup_ctor(&qualified)?;
    let boolean = elab.lookup_inductive("bool::Bool")?;
    (ind.tag == boolean.tag).then_some(ctor == 1)
}

/// A Boolean equation for an unsigned comparison, in either orientation.
fn comparison(elab: &Elaborator, cx: &Cx, ty: &Type) -> Option<(Vec<Rc<Term>>, bool, bool)> {
    let Type::Id { lhs, rhs, .. } = ty else { return None };
    for (flipped, side, flag) in [(false, lhs, rhs), (true, rhs, lhs)] {
        let Some(args) = named_args(elab, side, "bitvec::BitVec::unsigned_lt_bit") else { continue };
        if args.len() != 3 { continue; }
        if let Some(yes) = bool_flag(elab, cx, flag) {
            return Some((args.into_iter().cloned().collect(), yes, flipped));
        }
    }
    None
}

/// The Nat relation a comparison of two words states over their values.
#[derive(Clone, Copy)]
enum Relation {
    Lt,
    Le,
    Eq,
    Ne,
}

/// A fact in scope that compares two words, as the test that put it there
/// is written (issues/decreases-word-measures-by-hand.md): a Boolean test
/// `a.unsigned_lt_bit(b)`, `a.unsigned_le_bit(b)` or `a.eq_bit(b)` equal to
/// a constructor, either way round, or the proposition `a < b` or `a <= b`.
struct WordFact {
    /// The width and the two operands.
    args: Vec<Rc<Term>>,
    /// What it states of `toNat(a)` and `toNat(b)`, in that order unless
    /// `swapped`.
    relation: Relation,
    swapped: bool,
    /// The `bitvec_omega` lemma that reads it.
    lemma: &'static str,
    /// The fact's proof in the lemma's orientation.
    proof: String,
}

fn word_fact(elab: &Elaborator, cx: &Cx, name: &str, ty: &Type) -> Option<WordFact> {
    let three = |args: Vec<&Rc<Term>>| (args.len() == 3).then(|| args.into_iter().cloned().collect::<Vec<_>>());
    match ty {
        Type::Id { lhs, rhs, .. } => {
            for (flipped, side, flag) in [(false, lhs, rhs), (true, rhs, lhs)] {
                for test in ["unsigned_lt_bit", "unsigned_le_bit", "eq_bit"] {
                    let Some(args) = named_args(elab, side, &format!("bitvec::BitVec::{test}")).and_then(three) else { continue };
                    let Some(yes) = bool_flag(elab, cx, flag) else { continue };
                    let (relation, swapped, lemma) = match (test, yes) {
                        ("unsigned_lt_bit", true) => (Relation::Lt, false, "unsigned_true"),
                        ("unsigned_lt_bit", false) => (Relation::Le, true, "unsigned_false"),
                        ("unsigned_le_bit", true) => (Relation::Le, false, "unsigned_le_true"),
                        ("unsigned_le_bit", false) => (Relation::Lt, true, "unsigned_le_false"),
                        (_, true) => (Relation::Eq, false, "equal_true"),
                        (_, false) => (Relation::Ne, false, "equal_false"),
                    };
                    let proof = if flipped { format!("sym({name})") } else { name.to_string() };
                    return Some(WordFact { args, relation, swapped, lemma, proof });
                }
            }
            None
        }
        Type::El { tm, .. } => {
            for (test, relation, lemma) in [("unsigned_lt", Relation::Lt, "unsigned_lt_prop"), ("unsigned_le", Relation::Le, "unsigned_le_prop")] {
                if let Some(args) = named_args(elab, tm, &format!("bitvec::BitVec::{test}")).and_then(three) {
                    return Some(WordFact { args, relation, swapped: false, lemma, proof: name.to_string() });
                }
            }
            None
        }
        _ => None,
    }
}

/// Word equality and comparison goals use the same Nat generator through
/// an ordinary checking-position subgoal.
fn bridge_goal(elab: &Elaborator, cx: &Cx, expected: &Type) -> Option<String> {
    if let Some((args, yes, flipped)) = comparison(elab, cx, expected) {
        let spelled: Option<Vec<_>> = args.iter().map(|t| elab.spell_term_source(cx, t)).collect();
        let spelled = spelled?;
        let [n, a, b] = spelled.as_slice() else { return None };
        let av = format!("bitvec::BitVec::toNat({a})");
        let bv = format!("bitvec::BitVec::toNat({b})");
        let statement = if yes { lt(&av, &bv) } else { le(&bv, &av) };
        let proof = format!("bitvec_omega::unsigned_of_{}({n}, {a}, {b}, __bv_result)", if yes { "true" } else { "false" });
        return Some(format!("{{ have __bv_result: ({statement}) = bv_omega; {} }}", if flipped { format!("sym({proof})") } else { proof }));
    }
    let Type::Id { ty, lhs, rhs, .. } = expected else { return None };
    let ind = elab.display_tag_of(ty)?;
    if !elab.lookup_inductive("bitvec::BitVec").is_some_and(|word| word.tag == ind.tag) { return None; }
    let a = elab.spell_term_source(cx, lhs)?;
    let b = elab.spell_term_source(cx, rhs)?;
    // Type spellings include instantiated codes and inline lowerings. Let
    // the existing method inference recover the width in all those forms.
    let expr = parse_generated_expr(&format!("bitvec::BitVec::toNat({a})")).ok()?;
    let mark = (elab.pass.warnings.borrow().len(), elab.attempt.goal_arena.mark());
    let inferred = elab.generated_scope(|me| me.elab_infer(cx, &expr)).ok();
    let n = inferred.and_then(|(tm, _, _)| {
        let args = named_args(elab, &tm, "bitvec::BitVec::toNat")?;
        let [width, _] = args.as_slice() else { return None };
        elab.spell_term_source(cx, width)
    });
    elab.pass.warnings.borrow_mut().truncate(mark.0);
    elab.attempt.goal_arena.rollback(mark.1);
    let n = n?;
    for (flipped, word, other) in [(false, &a, rhs), (true, &b, lhs)] {
        if let Some(args) = named_args(elab, other, "bitvec::BitVec::ofNat")
            && let [_, c] = args.as_slice()
            && let Some(c) = elab.spell_term_source(cx, c)
        {
            let proof = format!("bitvec_omega::word_eq_value({n}, {word}, {c}, __bv_result)");
            return Some(format!("{{ have __bv_result: (bitvec::BitVec::toNat({word}) = {c}) = bv_omega; {} }}", if flipped { format!("sym({proof})") } else { proof }));
        }
    }
    Some(format!("{{ have __bv_result: (bitvec::BitVec::toNat({a}) = bitvec::BitVec::toNat({b})) = bv_omega; bitvec_omega::word_eq({n}, {a}, {b}, __bv_result) }}"))
}

/// The proof `bv_omega` offers at `expected`, as source (§2). The first
/// attempt is not `careful`: it reads a goal that is a word's fact off the
/// fact, and restates every fact over a word it takes apart without trying
/// the side conditions that adds. Where the checker refuses that proof, the
/// careful one proves the goal with `omega` and leaves alone a fact whose
/// side conditions fail.
pub(crate) fn generate(elab: &Elaborator, cx: &Cx, expected: &Type, careful: bool) -> Result<Generated, String> {
    if let Some(source) = bridge_goal(elab, cx, expected) {
        return Ok(Generated { source, prelude: String::new(), obligations: Vec::new(), retry: false });
    }
    let mut walk = Walk {
        elab,
        cx,
        atoms: Vec::new(),
        atom_index: HashMap::new(),
        nodes: Vec::new(),
        node_index: HashMap::new(),
        found: Vec::new(),
        stated: Default::default(),
        defined: HashMap::new(),
        defining: HashSet::new(),
        bridges: Vec::new(),
        splits: HashMap::new(),
    };
    let facts_in_scope = local_facts(elab, cx);
    for (name, ty) in &facts_in_scope {
        stated_words(elab, cx, ty, &mut walk.stated);
        if let Some((word, proof, value)) = definition(elab, cx, name, ty) {
            walk.defined.entry(word).or_insert((proof, value));
        }
    }
    walk.scan_type(expected)?;
    let mut subjects: Vec<usize> = std::mem::take(&mut walk.found);
    subjects.extend(walk.nodes.iter().enumerate().filter_map(|(i, n)| (!n.is_leaf()).then_some(i)));
    let stated = stated_bounds(&mut walk, &facts_in_scope);
    if !careful && walk.bridges.is_empty() && let Some((n, flipped, target)) = direct_goal(&mut walk, expected) {
        return Ok(generate_direct(&walk, &stated, n, flipped, &target));
    }
    // A fact in scope over a word the walk takes apart is restated over the
    // word's value, like the goal. Its words are optional: a word that
    // appears only there may overflow or borrow where the goal's do not.
    // Carefully, its new side conditions are tried first, and the fact is
    // left alone when one fails.
    let mut restated: Vec<(String, Type)> = Vec::new();
    let mut optimistic = false;
    let fact_names: Vec<String> = facts_in_scope.iter().map(|(name, _)| name.clone()).collect();
    for (name, ty) in facts_in_scope {
        let compared = word_fact(elab, cx, &name, &ty);
        let is_comparison = compared.is_some();
        if !is_comparison && !is_nat_relation(elab, cx, &ty) {
            continue;
        }
        let before = walk.clone();
        if let Some(fact) = compared {
            let [n, a, b] = fact.args.as_slice() else { continue };
            for operand in [a, b] {
                if let Some(i) = walk.word(n, operand)? {
                    walk.found.push(i);
                    comparison_value_bridge(&mut walk, i);
                }
            }
            let ns = nat_term_source(elab, cx, n)?;
            let av = elab.spell_term_source(cx, a).ok_or("could not spell comparison operand")?;
            let bv = elab.spell_term_source(cx, b).ok_or("could not spell comparison operand")?;
            let at = format!("bitvec::BitVec::toNat({av})");
            let bt = format!("bitvec::BitVec::toNat({bv})");
            let (x, y) = if fact.swapped { (&bt, &at) } else { (&at, &bt) };
            let statement = match fact.relation {
                Relation::Lt => lt(x, y),
                Relation::Le => le(x, y),
                Relation::Eq => format!("{x} = {y}"),
                Relation::Ne => format!("logic::Not({x} = {y})"),
            };
            walk.bridges.push((format!("__bv_compare{}", walk.bridges.len()), statement,
                format!("bitvec_omega::{}({ns}, {av}, {bv}, {})", fact.lemma, fact.proof)));
        }
        if !is_comparison { walk.scan_type(&ty)?; }
        let mut found = std::mem::take(&mut walk.found);
        // A split also needs the arithmetic value of its input.
        found.extend((before.nodes.len()..walk.nodes.len()).filter(|&i| !walk.nodes[i].is_leaf()));
        if !is_comparison && walk.bridges.len() == before.bridges.len() && !found.iter().any(|&n| !walk.nodes[n].is_leaf()) {
            walk = before;
            continue;
        }
        let old: HashSet<String> = plan_for(&before, &stated, &subjects).into_iter().map(|o| o.statement).collect();
        let mut all = subjects.clone();
        all.extend(found.iter().copied());
        let new: Vec<Obligation> = plan_for(&walk, &stated, &all).into_iter().filter(|o| !old.contains(&o.statement)).collect();
        optimistic |= !careful && !new.is_empty();
        if !careful || new.iter().all(|o| holds(elab, cx, &walk, o)) {
            subjects.extend(found);
            if !is_comparison { restated.push((name, ty)); }
        } else {
            walk = before;
        }
    }
    if walk.nodes.is_empty() {
        return Err("found no `toNat` of a word in the goal or unsigned comparison in scope; use `omega`".into());
    }
    // A leaf a fact defines is still a leaf here: its `toNat` stays an atom
    // for `omega`, beside the fact that defines it, rather than a variable
    // restating that fact.
    subjects.retain(|&n| !walk.nodes[n].is_leaf());
    subjects.sort_unstable();
    subjects.dedup();

    let hidden_roots = hidden_roots(&fact_names, &restated);

    let prelude = prelude(&walk);
    let mut e = Emitter::new(&walk, &stated);
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
        for (name, statement, _) in &walk.bridges {
            binders.push_str(&format!("({name}: {}) → ", generalise(statement.clone())));
            names.push(name.clone());
        }
        // Rebinding a fact under its own name hides the original from the
        // `omega` inside. A conjunct's name is a projection path
        // (`m.left`), which is no binder: it is bound fresh, and its root is
        // hidden as `True` once every conjunct read from it is restated.
        for (k, (name, ty)) in restated.iter().enumerate() {
            let spelled = elab.spell_type_source(cx, ty).ok_or("could not spell a fact in scope")?;
            let binder = restated_binder(k, name);
            binders.push_str(&format!("({binder}: {}) → ", generalise(spelled)));
            names.push(binder);
        }
        for root in &hidden_roots {
            binders.push_str(&format!("({root}: True) → "));
            names.push(root.clone());
        }
        source.push_str(&format!("have __bv_goal: ({binders}{goal}) = λ {} => omega;\n", names.join(" ")));
    }
    let count = bundle(&mut e, &mut source);
    let mut arguments = Vec::new();
    for &n in &subjects {
        arguments.push(format!("bitvec::BitVec::toNat({})", walk.nodes[n].word));
    }
    for &n in &subjects {
        let fact = e.fact(n);
        arguments.push(fact);
    }
    for (name, _, _) in &walk.bridges {
        arguments.push(name.clone());
    }
    for (name, _) in &restated {
        arguments.push(name.clone());
    }
    for _ in &hidden_roots {
        arguments.push("trivial".into());
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
    Ok(Generated { source, prelude, obligations: e.obligations, retry: optimistic })
}

/// Every side condition as one leaf of a *balanced* conjunction, proved in
/// the entry context, where no fact is in scope (§2); sets each one's path.
fn bundle(e: &mut Emitter, source: &mut String) -> usize {
    let count = e.obligations.len();
    let mut paths = vec![String::new(); count];
    if count > 0 {
        let parts: Vec<&Obligation> = e.obligations.iter().collect();
        let (statement, proof) = balanced(&parts, 0, &mut paths, String::new());
        source.push_str(&format!("have __bv_obligations: ({statement}) = {proof};\n"));
    }
    e.paths = paths.iter().map(|p| format!("__bv_obligations{p}")).collect();
    count
}

/// The goal is node `n`'s fact: its side conditions, its fact, and the
/// lemma that reads the goal off it.
fn generate_direct(walk: &Walk, stated: &[StatedBound], n: usize, flipped: bool, target: &Target) -> Generated {
    let prelude = prelude(walk);
    let mut e = Emitter::new(walk, stated);
    let mut seen = HashSet::new();
    e.plan(n, &mut seen);
    match target {
        Target::Whole(syn, _) => e.plan_syn(syn, &mut seen),
        Target::Diff(sa, _, sb, _) => {
            e.plan_syn(sa, &mut seen);
            e.plan_syn(sb, &mut seen);
        }
    }
    let mut source = format!("{{\n{prelude}\n");
    let count = bundle(&mut e, &mut source);
    let fact = e.fact(n);
    let (p, q) = e.forms[n].clone();
    let value = format!("bitvec::BitVec::toNat({})", walk.nodes[n].word);
    let proof = match target {
        Target::Whole(syn, r) => {
            let hr = e.reify(syn, r);
            format!("bitvec_omega::fact_value({value}, {}, {r}, {fact}, {hr})", e.spell(&p))
        }
        Target::Diff(sa, a, sb, b) => {
            let (ha, hb) = (e.reify(sa, a), e.reify(sb, b));
            format!("bitvec_omega::fact_diff({value}, {}, {}, {a}, {b}, {fact}, {ha}, {hb})", e.spell(&q), e.spell(&p))
        }
    };
    for line in &e.lines {
        source.push_str(line);
        source.push('\n');
    }
    if count > 0 {
        source.push_str("have __bv_obligations = trivial;\n");
    }
    source.push_str(&if flipped { format!("sym({proof})\n}}") } else { format!("{proof}\n}}") });
    Generated { source, prelude, obligations: e.obligations, retry: true }
}

/// A fact that gives a word's value: `toNat(w) = v` or `v = toNat(w)`, with
/// the word spelled, the fact's proof as `toNat(w) = v`, and `v`.
fn definition(elab: &Elaborator, cx: &Cx, name: &str, ty: &Type) -> Option<(String, String, Rc<Term>)> {
    let Type::Id { ty, lhs, rhs, .. } = ty else { return None };
    if elab.display_type(cx, ty) != "Nat" {
        return None;
    }
    for (flipped, side, other) in [(false, lhs, rhs), (true, rhs, lhs)] {
        if let Some(args) = named_args(elab, side, "bitvec::BitVec::toNat")
            && let [_, word] = args.as_slice()
            && let Some(spelled) = elab.spell_term_source(cx, word)
        {
            let proof = if flipped { format!("sym({name})") } else { name.to_string() };
            return Some((spelled, proof, Rc::clone(other)));
        }
    }
    None
}

/// The bindings before any side condition: each leaf's range, for `omega`
/// to read.
fn prelude(walk: &Walk) -> String {
    let mut out = Vec::new();
    for (i, node) in walk.nodes.iter().enumerate() {
        if let Kind::Leaf | Kind::Defined(..) = node.kind {
            let statement = lt(&format!("bitvec::BitVec::toNat({})", node.word), &format!("nat::Nat::pow(2, {})", node.width));
            out.push(format!("have __bv_range_{i}: ({statement}) = bitvec::BitVec::toNat_lt_pow({}, {});", node.width, node.word));
        }
    }
    for (name, statement, proof) in &walk.bridges {
        out.push(format!("have {name}: ({statement}) = {proof};"));
    }
    out.join("\n")
}

/// A comparison against a Nat-built word must expose that word's value
/// before the arithmetic side conditions: otherwise a subtraction's
/// no-borrow sees `toNat(ofNat(c)) <= s`, while its form needs `c <= s`.
/// Only an independently checked bound permits this early fact. A wrapping
/// comparison operand remains opaque, as comparisons alone never bound the
/// Nat it was built from.
fn comparison_value_bridge(walk: &mut Walk, i: usize) {
    let node = &walk.nodes[i];
    let Kind::Value(lemma, c, syn) = &node.kind else { return };
    let statement = format!("bitvec::BitVec::toNat({}) = {c}", node.word);
    if walk.bridges.iter().any(|(_, other, _)| other == &statement) { return; }
    let lemma = if *lemma == "ofNat_row" {
        "bitvec::BitVec::toNat_ofNat"
    } else {
        "bitvec_nat::toNat_word_of_nat"
    };
    let bound = if matches!(syn, NatSyn::Lit(_)) { "trivial" } else { "omega" };
    let proof = format!("{lemma}({}, {c}, {bound})", node.width);
    let source = format!("{{ have __bv_value: ({statement}) = {proof}; __bv_value }}");
    let Ok(expr) = parse_generated_expr(&source) else { return };
    let elab = walk.elab;
    let mark = (elab.pass.warnings.borrow().len(), elab.attempt.goal_arena.mark());
    let checked = elab.generated_scope(|me| me.elab_infer(walk.cx, &expr)).is_ok();
    elab.pass.warnings.borrow_mut().truncate(mark.0);
    elab.attempt.goal_arena.rollback(mark.1);
    if checked {
        walk.bridges.push((format!("__bv_compare_value{}", walk.bridges.len()), statement, proof));
    }
}

/// Whether `omega` proves `o` in the entry context, for an optional word.
fn holds(elab: &Elaborator, cx: &Cx, walk: &Walk, o: &Obligation) -> bool {
    let source = format!("{{\n{}\nhave __bv_side: ({}) = omega;\n__bv_side\n}}", prelude(walk), o.statement);
    let Ok(expr) = parse_generated_expr(&source) else { return false };
    // A probe: its named atom lists are not the proof's.
    let mark = (elab.pass.warnings.borrow().len(), elab.attempt.goal_arena.mark());
    let holds = elab.generated_scope(|me| me.elab_infer(cx, &expr)).is_ok();
    elab.pass.warnings.borrow_mut().truncate(mark.0);
    elab.attempt.goal_arena.rollback(mark.1);
    holds
}

/// The conjunction of `parts` as a balanced tree, with its proof (`omega` at
/// every leaf, `trivial` at a closed one); records each leaf's projection
/// path from the root.
fn balanced(parts: &[&Obligation], first: usize, paths: &mut [String], path: String) -> (String, String) {
    if let [one] = parts {
        paths[first] = path;
        return (one.statement.clone(), if one.closed { "trivial" } else { "omega" }.into());
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

/// Whether `ty` mentions the `toNat` of a word: where a stuck `omega` has
/// `bv_omega` to fall back on.
pub(crate) fn mentions_word(elab: &Elaborator, ty: &Type) -> bool {
    fn go(elab: &Elaborator, tm: &Rc<Term>) -> bool {
        if named_args(elab, tm, "bitvec::BitVec::toNat").is_some() {
            return true;
        }
        if let Term::Succ(inner) = &**tm {
            return go(elab, inner);
        }
        crate::spelling::app_spine(tm).1.into_iter().any(|arg| go(elab, arg))
    }
    match ty {
        Type::El { tm, .. } => go(elab, tm),
        Type::Id { lhs, rhs, .. } => go(elab, lhs) || go(elab, rhs),
        _ => false,
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

/// The binder for the `k`th restated fact: its own name when that is an
/// identifier, a fresh one for a conjunct's projection path (`m.left`).
fn restated_binder(k: usize, name: &str) -> String {
    if name.contains('.') { format!("__bv_fact{k}") } else { name.to_string() }
}

/// The roots of the restated conjuncts (`m` of `m.left`) every one of whose
/// conjuncts is restated: hiding them keeps the original composite words
/// from the `omega` inside, as rebinding does for a plain name.
fn hidden_roots(fact_names: &[String], restated: &[(String, Type)]) -> Vec<String> {
    let mut roots: Vec<String> = Vec::new();
    for (name, _) in restated {
        let Some((root, _)) = name.split_once('.') else { continue };
        if roots.iter().any(|r| r == root) {
            continue;
        }
        let prefix = format!("{root}.");
        let all = fact_names
            .iter()
            .filter(|f| f.starts_with(&prefix))
            .all(|f| restated.iter().any(|(r, _)| r == f));
        if all {
            roots.push(root.to_string());
        }
    }
    roots
}
