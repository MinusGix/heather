//! `ring`: commutative-ring normalization by reflection
//! (`docs/ring-normalization-design.md`, `issues/ring-normalization.md`).
//!
//! The tactic is an untrusted reifier in front of `lib/std/tactic/ring.hthr`. It
//! reads an equation at `Int` or `Nat` into `RingExpr`/`RingNat` syntax over
//! an atom list and writes one application of `RingExpr::sound` (or
//! `RingNat::sound`) whose `refl` the kernel checks by evaluating the
//! in-language normalizer. A `≈` goal at a carrier with a `CommRingOfInt`
//! instance (`Rat`, `CReal`) is read at that carrier, its operations the
//! carrier's designations, and gets `RingExpr::sound_rel`
//! (`issues/ring-modulo-a-relation.md`); when that reading does not prove it
//! and the relation unfolds to an `Int` equation, the cross-multiplied
//! reading is tried as before. With hypotheses `ring(h₁, …, hₖ)` it also searches
//! for polynomial multipliers `cᵢ` with `lhs − rhs = Σ cᵢ·(aᵢ − bᵢ)` and
//! writes `sound_with`, whose side condition is the same `refl`; the search is
//! the only thing here that is not checked, and a wrong answer is refused by
//! that `refl`.
//!
//! Nothing in this file decides what is true. The Rust normal form below is
//! the searcher's: it chooses multipliers and reports residuals. The
//! certificate's normal form is the library's, and the two need not agree on
//! the order of monomials, only on whether a polynomial is zero.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc as Rc;

use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{Term, Type};
use heather_syntax::{Expr, Item, OpFixity, Span, parse_file};

use crate::oracle::Unfold;
use crate::context::Alias;
use crate::statements::LetValue;
use crate::omega_cert::{integer_source, named_args};
use crate::relational_context::proof::Relation;
use crate::{Cx, ElabError, Elaborator, R};

type Z = i128;

/// The name a certificate uses for its atom list.
const ATOMS: &str = "__ring_atoms";

/// Steps a goal's or hypothesis's type may take to expose its equation
/// (`Rat::Same(x, y)` unfolds to one).
const STATEMENT_STEPS: u64 = 4096;

/// Steps a projection's receiver may take to reach a constructor, and a pair
/// of atoms may take to be found convertible.
const ATOM_STEPS: u64 = 512;

/// Steps a candidate numeral may take to be found the carrier's `of_int` of
/// its integer: the instance dictionary is unfolded on the way.
const NUMERAL_STEPS: u64 = 4096;

/// How deep projections are read through (`(x + y).num` reads `x + y`'s
/// numerator, which may read another).
const PROJECTION_DEPTH: u32 = 8;

/// Multiplier search bounds: closure rounds, and the most unknowns the linear
/// system may have.
const SEARCH_ROUNDS: usize = 4;
const SEARCH_CANDIDATES: usize = 240;

#[derive(Clone, PartialEq, Eq, Debug)]
enum Carrier {
    Int,
    Nat,
    /// A commutative ring modulo its `≈`, with its integers named
    /// (`CommRingOfInt`).
    Rel(Rc<RelCarrier>),
}

/// A `≈` carrier's spelling and its operations. A missing one is an
/// operation the reifier leaves to atoms.
#[derive(PartialEq, Eq, Debug)]
struct RelCarrier {
    source: String,
    same: Op,
    add: Option<Op>,
    sub: Option<Op>,
    mul: Option<Op>,
    neg: Option<Op>,
    /// The postfix `⁻¹`, read as a reciprocal (`Reifier::reciprocal`).
    inv: Option<Op>,
    /// At a class carrier, its integers (`ClassInts`); `None` at a carrier
    /// with a `CommRingOfInt` instance.
    class: Option<ClassInts>,
}

/// How an operation is named where a term spells it: a carrier's
/// designation, a global; or, at a class carrier, a local (the section's
/// `+`) or a field read off the dictionary in scope (`K.inv`), compared as
/// the term it is.
#[derive(Clone, PartialEq, Eq, Debug)]
enum Op {
    /// A global, after the arguments it takes before its operands: a generic
    /// carrier's operation (`hurwitz::Hurwitz::add` at `Hurwitz<Int>`) is
    /// applied to its section's parameters first.
    Global(String),
    GlobalAfter(String, usize),
    Term(Rc<Term>),
}

impl Op {
    /// `tm`'s arguments where `tm` applies this operation.
    fn args<'t>(&self, elab: &Elaborator, tm: &'t Term) -> Option<Vec<&'t Rc<Term>>> {
        match self {
            Op::Global(name) => named_args(elab, tm, name),
            Op::GlobalAfter(name, prefix) => named_args(elab, tm, name).and_then(|args| (args.len() > *prefix).then(|| args[*prefix..].to_vec())),
            Op::Term(op) => {
                let mut args = Vec::new();
                let mut head = tm;
                while let Some((fun, arg)) = crate::spelling::app_of(head) {
                    args.push(arg);
                    head = fun;
                }
                args.reverse();
                same_dictionary_read(head, op).then_some(args)
            }
        }
    }

    /// The global this operation is, where it is one.
    fn global(&self) -> Option<&str> {
        match self {
            Op::Global(name) | Op::GlobalAfter(name, _) => Some(name),
            Op::Term(_) => None,
        }
    }

    /// Is `op`, unapplied, this operation: the global itself, or the class
    /// carrier's operation term as it stands.
    fn is(&self, elab: &Elaborator, op: &Term) -> bool {
        match self {
            Op::Global(name) => crate::range_sum::op_is(elab, op, name),
            Op::GlobalAfter(name, prefix) => {
                crate::omega_cert::named_args(elab, op, name).is_some_and(|args| args.len() == *prefix)
            }
            Op::Term(term) => same_dictionary_read(op, term),
        }
    }
}

/// Is `tm` the dictionary read `want` (`K.inv`, `K.unit`), as written or as
/// a parent class's definition reaches it? A predicate defined in a parent
/// class's section (`AbsLe`, from `OrderedAddGroup`) reads its operations
/// off the parent dictionary, which at `K` is a record built from `K`'s own
/// fields: `fst(snd(…(pair(…))))`, whose component, read by syntax alone, is
/// the field `K.inv` is (issues/ring-atom-mentions-class-constant.md).
fn same_dictionary_read(tm: &Term, want: &Term) -> bool {
    if *tm == *want {
        return true;
    }
    let mut cur = tm;
    let mut read = false;
    while let Some(component) = crate::spelling::project_value(cur) {
        cur = component;
        read = true;
    }
    read && crate::spelling::same_projection(cur, want)
}

/// A class carrier's integers (docs/casting-design.md §16): a type
/// parameter `K` whose ring is a dictionary in scope
/// (`section<K: OrderedField(≈, <, <=, +, *)>`) has no `CommRingOfInt`
/// instance, and its integers are the ones every ring has
/// (`semiring::Ring::int_cast`). The certificate's lemmas get them as the
/// dictionary `semiring::CommRing::with_ints<K>()`, bound where the
/// certificate is elaborated as [`CLASS_INTS`], which instance search finds
/// in scope; a constant is that map's image, and `0`, `1` are the
/// dictionary's own `K.unit` and `K.multiplicative.unit` by computation.
#[derive(PartialEq, Eq, Debug)]
struct ClassInts {
    ints: Rc<Term>,
    ty: Type,
    level: Level,
    zero: Rc<Term>,
    one: Rc<Term>,
}

/// The name a class carrier's integers dictionary is bound to.
const CLASS_INTS: &str = "__ring_ints";

impl ClassInts {
    /// `cx` with these integers in scope for a certificate at `carrier`:
    /// [`Elaborator::class_dictionary_scope`] for `ring`'s lemmas.
    fn scope(&self, elab: &Elaborator, cx: &Cx, carrier: &str) -> Option<Cx> {
        elab.class_dictionary_scope(cx, carrier, CLASS_INTS, (&self.ints, &self.ty, &self.level), "semiring::CommRingOfInt", "semiring::CommRing")
    }
}

impl Elaborator {
    /// `cx` with a class carrier's derived dictionary `value` in scope (a
    /// `CommRingOfInt` at `K`, built by `CommRing::with_ints` or
    /// `OrderedField::with_ints`), so the generic
    /// lemmas a certificate names find it: bound as a `let` named `name`,
    /// which instance search consults, and declared as a binder of `class`
    /// at `carrier` whose indices are those of the scope's own dictionary
    /// of `ring` (the section's `K: OrderedField(≈, <, <=, +, *)` read as a
    /// `CommRing(≈, +, *)`), so a lemma's call pins its `≈`, `+` and `*`
    /// from scope as it would from a section's constraint.
    pub(crate) fn class_dictionary_scope(
        &self,
        cx: &Cx,
        carrier: &str,
        name: &str,
        value: (&Rc<Term>, &Type, &Level),
        class: &str,
        ring: &str,
    ) -> Option<Cx> {
        let index = self.scope_dict_index(cx, &self.key_of(ring)?)?.into_iter().collect::<Option<Vec<Expr>>>()?;
        let wrapper = format!("theorem __ring_generated(): {carrier} {{ 0 }}");
        let Some(Item::Decl(decl)) = parse_file(&wrapper).ok()?.items.pop() else {
            return None;
        };
        let (term, ty, level) = value;
        let mut inner = cx.clone();
        inner.aliases.push(Rc::new(Alias {
            name: name.to_string(),
            depth: cx.names.len(),
            term: Rc::clone(term),
            ty: ty.clone(),
            level: level.clone(),
            skel: None,
            spliced: None,
            shifted: Default::default(),
        }));
        inner.dicts.push(Rc::new(crate::context::DictBinder {
            name: format!("#{name}"),
            class: class.to_string(),
            carrier: decl.result,
            index,
        }));
        Some(inner)
    }
}

impl Carrier {
    fn name(&self) -> &str {
        match self {
            Carrier::Int => "Int",
            Carrier::Nat => "Nat",
            Carrier::Rel(rel) => &rel.source,
        }
    }
}

/// A cast edge the reifier reads through (docs/casting-design.md §5.6): the
/// map's global, the `OrderedRingHom` value, and the source carrier's
/// operations, as bare global names.
struct Edge {
    map: &'static str,
    hom: &'static str,
    add: &'static str,
    mul: &'static str,
    neg: &'static str,
    sub: &'static str,
}

const EDGES: [Edge; 3] = [
    Edge { map: "dyadic::Dyadic::rat", hom: "dyadic::Dyadic::rat_hom", add: "dyadic::Dyadic::add", mul: "dyadic::Dyadic::mul", neg: "dyadic::Dyadic::neg", sub: "dyadic::Dyadic::sub" },
    Edge { map: "creal::CReal::ofRat", hom: "creal::CReal::ofRat_hom", add: "rat::Rat::add", mul: "rat::Rat::mul", neg: "rat::Rat::neg", sub: "rat::Rat::sub" },
    Edge { map: "rat::Rat::ofInt", hom: "rat::Rat::ofInt_hom", add: "int::Int::add", mul: "int::Int::mul", neg: "int::Int::neg", sub: "int::Int::sub" },
];

/// A morphism in scope as an edge ([`Reifier::find_local_edges`]): the
/// local's name, the source carrier as written, and the map as an image
/// applies it.
struct LocalEdge {
    hom: String,
    source: String,
    map: Rc<Term>,
}


/// How many edges deep an image of an image is read.
const EDGE_NESTING: u32 = 3;

/// Reified syntax; `Sub`/`Neg` occur only at `Int`.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Syn {
    Atom(usize),
    Const(Z),
    Add(Box<Syn>, Box<Syn>),
    Sub(Box<Syn>, Box<Syn>),
    Mul(Box<Syn>, Box<Syn>),
    Neg(Box<Syn>),
}

struct Atom {
    term: Rc<Term>,
    /// How the atom list names it: its spelling, or for a term that has
    /// none (a field read such as `x.seq(n)`) an alias the certificate binds
    /// to the term itself (`atom_alias`).
    source: String,
    /// How a message shows it.
    shown: String,
    named: bool,
}

/// The alias an atom with no source spelling is named by.
fn atom_alias(index: usize) -> String {
    format!("__ring_a{index}")
}

/// An equation's two sides and the carrier's kernel type.
struct Equation {
    carrier: Carrier,
    ty: Type,
    level: Level,
    lhs: Rc<Term>,
    rhs: Rc<Term>,
}

/// `ty` as an equation at `Int` or `Nat`, unfolding a defined proposition
/// (`x ≈ y` at `Rat`) to the `Id` it stands for.
fn equation(elab: &Elaborator, cx: &Cx, ty: &Type) -> Option<Equation> {
    let unfolded;
    let ty = if matches!(ty, Type::Id { .. }) {
        ty
    } else {
        unfolded = elab
            .goal_oracle()
            .bounded(STATEMENT_STEPS)
            .whnf_type(&cx.gamma, ty)
            .ok()?;
        &unfolded
    };
    let Type::Id { level, ty, lhs, rhs } = ty else {
        return None;
    };
    let carrier = if matches!(**ty, Type::Nat) || elab.display_type(cx, ty) == "Nat" {
        Carrier::Nat
    } else if elab.display_type(cx, ty) == "Int" {
        Carrier::Int
    } else {
        return None;
    };
    Some(Equation {
        carrier,
        ty: (**ty).clone(),
        level: level.clone(),
        lhs: Rc::clone(lhs),
        rhs: Rc::clone(rhs),
    })
}

/// `ty` as `x ≈ y` at a carrier whose `≈` it is and which has a
/// `CommRingOfInt` instance, or at a class carrier, read as written: the
/// relation is not unfolded.
fn relation_equation(elab: &Elaborator, cx: &Cx, ty: &Type, span: Span) -> Option<Equation> {
    elab.key_of("ring::RingExpr::sound_rel")?;
    let rel = Relation::of_type(elab, cx, ty, span)?;
    let Type::El { tm, .. } = ty else {
        return None;
    };
    let ops = rel_carrier(elab, cx, &rel.carrier, Some(tm), span)?;
    if ops.same.args(elab, tm)?.len() != 2 {
        return None;
    }
    Some(Equation {
        carrier: Carrier::Rel(Rc::new(ops)),
        ty: (*rel.carrier).clone(),
        level: rel.level,
        lhs: rel.left,
        rhs: rel.right,
    })
}

/// A carrier with a `CommRingOfInt` instance, its spelling and designated
/// operations; else a class carrier ([`class_carrier`]).
fn rel_carrier(elab: &Elaborator, cx: &Cx, carrier_ty: &Type, goal: Option<&Term>, span: Span) -> Option<RelCarrier> {
    let Some(carrier) = elab.carrier_of_ty(cx, carrier_ty, span) else {
        return class_carrier(elab, cx, carrier_ty);
    };
    let class = elab.key_of("semiring::CommRingOfInt")?;
    if elab.traits.instances_answering(&class, Some(&carrier.key)).is_empty() {
        return None;
    }
    // A generic carrier's operations take its section's parameters before
    // their operands; the goal's relation shows how many, and the carrier's
    // other designations are read as coming from the same section. A
    // reading with no goal (`linarith`'s) is at a carrier with no parameters.
    let same = elab.designated("≈", OpFixity::Infix, &carrier.key)?;
    let prefix = match goal { Some(goal) => named_args(elab, goal, &same)?.len().checked_sub(2)?, None => 0 };
    let op = |sym: &str, fixity| {
        elab.designated(sym, fixity, &carrier.key).map(|name| if prefix == 0 { Op::Global(name) } else { Op::GlobalAfter(name, prefix) })
    };
    // A carrier with parameters may spell short (`Hurwitz<…>`); the
    // certificate names it in full.
    let source = elab.spell_type_clean(cx, carrier_ty).filter(|s| !s.contains('…')).or_else(|| elab.spell_type_source(cx, carrier_ty))?;
    Some(RelCarrier {
        source,
        same: op("≈", OpFixity::Infix)?,
        add: op("+", OpFixity::Infix),
        sub: op("-", OpFixity::Infix),
        mul: op("*", OpFixity::Infix),
        neg: op("-", OpFixity::Prefix),
        inv: op("⁻¹", OpFixity::Postfix),
        class: None,
    })
}

/// A class carrier's ring (`ClassInts`), read off
/// `semiring::CommRing::with_ints<K>()` elaborated where the goal is:
/// instance search finds `K`'s ring in scope, and the call's implicit
/// arguments, `K` and its `≈`, `+` and `*`, are the operations as the
/// section binds them (the dictionary's type is structural, its indices
/// substituted away). `K.unit`, `K.multiplicative.unit` and `K.inv` are read as a
/// statement spells them. `K` has no `-` or `⁻¹` designation, so a
/// difference is written `x + K.inv(y)` and a reciprocal is an atom.
fn class_carrier(elab: &Elaborator, cx: &Cx, carrier_ty: &Type) -> Option<RelCarrier> {
    elab.key_of("semiring::CommRing::with_ints")?;
    let source = elab.spell_type_clean(cx, carrier_ty)?;
    let infer = |written: &str| {
        let expr = parse_expr(written).ok()?;
        elab.generated_scope(|me| me.elab_infer(cx, &expr)).ok()
    };
    let (ints, ty, level) = infer(&format!("semiring::CommRing::with_ints<{source}>()"))?;
    let (same, add, mul) = match named_args(elab, &ints, "semiring::CommRing::with_ints")?.as_slice() {
        [_, same, add, mul, ..] => (Rc::clone(same), Rc::clone(add), Rc::clone(mul)),
        _ => return None,
    };
    let field = |name: &str| infer(&format!("{source}.{name}")).map(|(term, _, _)| Rc::new(term));
    let (zero, one, neg) = (field("unit")?, field("multiplicative.unit")?, field("inv"));
    Some(RelCarrier {
        source,
        same: Op::Term(same),
        add: Some(Op::Term(add)),
        sub: None,
        mul: Some(Op::Term(mul)),
        neg: neg.map(Op::Term),
        inv: None,
        class: Some(ClassInts { ints: Rc::new(ints), ty, level, zero, one }),
    })
}

/// A linear form over a reading's monomials: each nonconstant monomial's
/// coefficient, and the constant.
pub(crate) type Linear = (BTreeMap<Vec<u32>, Z>, Z);

/// `linarith`'s reading of a field's terms (`crate::linarith`): the relation
/// reading's reifier at a `≈` carrier, every term a polynomial over one
/// shared atom table, so `linarith` and the `ring` step that checks its
/// identity agree on what an atom is. A reciprocal is a plain atom here: its
/// fact is `ring`'s to use when it checks the combination; the reading only
/// records, for each reciprocal it meets, the denominator that fact names,
/// so `linarith` can clear a positive one (`Reciprocal`).
pub(crate) struct FieldReading<'a> {
    reifier: Reifier<'a>,
    reciprocals: Vec<Reciprocal>,
    /// The bases of the squares read so far, `t` for each `t * t` written,
    /// as forms (`nlinarith` offers `t·t ≥ 0`; docs/nonlinear-arithmetic-design.md
    /// §4.2). Normalization hides a square's shape, so it is kept here.
    squares: Vec<Linear>,
}

/// A reciprocal atom `r` the reading met with its fact `r·d ≈ 1`: the
/// denominator `d` as the fact states it, and, when the reciprocal is
/// positive by construction (`Rat::inv_succ(n)`), the library's `0 < r`.
pub(crate) struct Reciprocal {
    pub(crate) atom: usize,
    pub(crate) den: Rc<Term>,
    pub(crate) positive: Option<(Term, Type, Level, String)>,
}

impl<'a> FieldReading<'a> {
    pub(crate) fn at(elab: &'a Elaborator, cx: &'a Cx, carrier_ty: &Type, level: Level, span: Span) -> Option<Self> {
        let ops = rel_carrier(elab, cx, carrier_ty, None, span)?;
        Some(FieldReading {
            reifier: Reifier {
                elab,
                cx,
                span,
                carrier: Carrier::Rel(Rc::new(ops)),
                ty: carrier_ty.clone(),
                level,
                atoms: Vec::new(),
                facts: Vec::new(),
                in_fact: false,
                local_edges: Default::default(),
            },
            reciprocals: Vec::new(),
            squares: Vec::new(),
        })
    }

    /// The reading at `Int` (`nat` false) or `Nat`, whose operations are the
    /// integers' own: `linarith` there names `ring`'s monomials for `omega`
    /// (`crate::linarith`, docs/linarith-design.md §8).
    pub(crate) fn integral(elab: &'a Elaborator, cx: &'a Cx, nat: bool, ty: Type, level: Level, span: Span) -> Self {
        FieldReading {
            reifier: Reifier {
                elab,
                cx,
                span,
                carrier: if nat { Carrier::Nat } else { Carrier::Int },
                ty,
                level,
                atoms: Vec::new(),
                facts: Vec::new(),
                in_fact: false,
                local_edges: Default::default(),
            },
            reciprocals: Vec::new(),
            squares: Vec::new(),
        }
    }

    /// The atoms read so far, in the order the monomials index them.
    pub(crate) fn atom_terms(&self) -> Vec<Rc<Term>> {
        self.reifier.atoms.iter().map(|a| Rc::clone(&a.term)).collect()
    }

    /// `form` with atom `atom` replaced by `by` throughout.
    pub(crate) fn substitute(form: &Linear, atom: usize, by: &Linear) -> Result<Linear, String> {
        let poly = |form: &Linear| {
            let mut p = Poly(form.0.clone());
            p.add_term(Vec::new(), form.1).map(|_| p)
        };
        let by = poly(by)?;
        let mut out = Poly::constant(form.1);
        for (m, c) in &form.0 {
            let e = m.get(atom).copied().unwrap_or(0);
            let mut rest = m.clone();
            if e > 0 {
                rest[atom] = 0;
            }
            let mut term = Poly::monomial(*c, trim(rest));
            for _ in 0..e {
                term = term.mul(&by)?;
            }
            out = out.add(&term)?;
        }
        let mut terms = out.0;
        let constant = terms.remove(&Vec::new()).unwrap_or(0);
        Ok((terms, constant))
    }

    /// The reciprocals met so far whose fact could be written.
    pub(crate) fn reciprocals(&self) -> &[Reciprocal] {
        &self.reciprocals
    }

    /// The bases of the squares the terms read so far write.
    pub(crate) fn squares(&self) -> &[Linear] {
        &self.squares
    }

    /// `a·b`, two forms over the reading's monomials multiplied out.
    pub(crate) fn product(a: &Linear, b: &Linear) -> Result<Linear, String> {
        let poly = |form: &Linear| {
            let mut p = Poly(form.0.clone());
            p.add_term(Vec::new(), form.1).map(|_| p)
        };
        let mut terms = poly(a)?.mul(&poly(b)?)?.0;
        let constant = terms.remove(&Vec::new()).unwrap_or(0);
        Ok((terms, constant))
    }

    /// The monomial that is atom `atom` alone.
    pub(crate) fn atom_monomial(atom: usize) -> Vec<u32> {
        let mut m = vec![0; atom + 1];
        m[atom] = 1;
        m
    }

    /// `a·b` over the reading's monomials.
    pub(crate) fn monomial_product(a: &[u32], b: &[u32]) -> Result<Vec<u32>, String> {
        mono_mul(&a.to_vec(), &b.to_vec())
    }

    /// Records the reciprocal facts read since `from`: the denominator is
    /// the right factor of the fact's left side, `r * d`.
    fn record_reciprocals(&mut self, from: usize) {
        let reifier = &self.reifier;
        let Carrier::Rel(ops) = &reifier.carrier else { return };
        let Some(mul) = &ops.mul else { return };
        for fact in &reifier.facts[from..] {
            if fact.kind != FactKind::Reciprocal || self.reciprocals.iter().any(|r| r.atom == fact.atom) {
                continue;
            }
            let Some(eq) = relation_equation(reifier.elab, reifier.cx, &fact.ty, reifier.span) else {
                continue;
            };
            let Some(den) = mul.args(reifier.elab, &eq.lhs).and_then(|args| match args.as_slice() {
                [_, den] => Some(Rc::clone(den)),
                _ => None,
            }) else {
                continue;
            };
            let term = &reifier.atoms[fact.atom].term;
            let positive = named_args(reifier.elab, term, "rat::Rat::inv_succ")
                .and_then(|args| match args.as_slice() {
                    [n] => reifier.elab.spell_term_source(reifier.cx, n),
                    _ => None,
                })
                .and_then(|n| {
                    reifier.elab.key_of("rat::Rat::inv_succ_pos")?;
                    let source = format!("rat::Rat::inv_succ_pos({n})");
                    let expr = parse_expr(&source).ok()?;
                    let (term, ty, level) = reifier.elab.generated_scope(|me| me.elab_infer(reifier.cx, &expr)).ok()?;
                    Some((term, ty, level, source))
                });
            self.reciprocals.push(Reciprocal { atom: fact.atom, den, positive });
        }
    }

    /// The carrier as source (`Rat`, `CReal`).
    pub(crate) fn carrier_source(&self) -> &str {
        self.reifier.carrier.name()
    }

    /// `tm` as a linear form over the monomials of its normal form. On an
    /// error the atom table is as it was.
    pub(crate) fn linear(&mut self, tm: &Rc<Term>) -> Result<Linear, String> {
        self.read(tm).map(|(form, _)| form)
    }

    /// `linear`, and whether the term multiplies two parts neither of which
    /// is a constant: a product `omega` would read as one atom of its own.
    pub(crate) fn read(&mut self, tm: &Rc<Term>) -> Result<(Linear, bool), String> {
        let (atoms, facts) = (self.reifier.atoms.len(), self.reifier.facts.len());
        let mut squares = Vec::new();
        let read = self.reifier.reify(tm).and_then(|syn| {
            // An atom read with a definition (a cast pushed one level in,
            // `Reifier::cast`, `Reifier::edge_image`) is read as what it
            // stands for, so the linear reading sees through casts as `ring`
            // does; the combination's check cites the same facts.
            let defs: Vec<(usize, Syn)> = self.reifier.facts[facts..]
                .iter()
                .filter(|f| f.kind == FactKind::Definition)
                .map(|f| (f.atom, f.sides.rhs.clone()))
                .collect();
            let syn = defined(&syn, &defs, defs.len() + 1);
            squares_of(&syn, &mut squares)?;
            Ok((poly_of(&syn)?, multiplies(&syn)))
        });
        if read.is_ok() {
            self.record_reciprocals(facts);
            for square in squares {
                let mut terms = square.0;
                let constant = terms.remove(&Vec::new()).unwrap_or(0);
                let form = (terms, constant);
                if !self.squares.contains(&form) {
                    self.squares.push(form);
                }
            }
        }
        self.reifier.facts.truncate(facts);
        let (poly, product) = match read {
            Ok(read) => read,
            Err(error) => {
                self.reifier.atoms.truncate(atoms);
                return Err(error);
            }
        };
        let mut terms = poly.0;
        let constant = terms.remove(&Vec::new()).unwrap_or(0);
        Ok(((terms, constant), product))
    }

    /// A linear form as source over the atoms' spellings, for messages.
    pub(crate) fn render(&self, form: &Linear) -> String {
        let mut poly = Poly(form.0.clone());
        let _ = poly.add_term(Vec::new(), form.1);
        let atoms: Vec<String> = self.reifier.atoms.iter().map(|a| a.shown.clone()).collect();
        render_poly(&poly, &atoms)
    }
}

struct Reifier<'a> {
    elab: &'a Elaborator,
    cx: &'a Cx,
    span: Span,
    carrier: Carrier,
    ty: Type,
    level: Level,
    atoms: Vec<Atom>,
    /// The atoms met so far that come with a fact — reciprocals and casts —
    /// in the order their facts were read: one inside another's denominator
    /// or cast comes first.
    facts: Vec<Fact>,
    /// Reading a reciprocal's own fact, whose reciprocal is already an atom.
    in_fact: bool,
    /// The morphisms in scope into the carrier, found at the first image
    /// that might be one's.
    local_edges: std::cell::OnceCell<Vec<LocalEdge>>,
}

/// An atom read together with a fact the library states for it, elaborated,
/// its two sides in the same atom table. The certificate cites the fact like
/// a written hypothesis.
struct Fact {
    atom: usize,
    kind: FactKind,
    term: Term,
    ty: Type,
    level: Level,
    sides: Written,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum FactKind {
    /// `r·d ≈ 1` (`Rat::inv_mul`: `x⁻¹ * x ≈ 1`): `r` is `d`'s reciprocal.
    Reciprocal,
    /// `c ≈ e`, `e` free of `c` (`RingExpr::of_nat_add`): `c` stands for `e`.
    Definition,
}

impl Reifier<'_> {
    fn reify(&mut self, tm: &Rc<Term>) -> Result<Syn, String> {
        self.reify_within(tm, PROJECTION_DEPTH)
    }

    fn reify_within(&mut self, tm: &Rc<Term>, depth: u32) -> Result<Syn, String> {
        match &self.carrier {
            Carrier::Int => self.reify_int(tm, depth),
            Carrier::Nat => self.reify_nat(tm, depth),
            Carrier::Rel(ops) => {
                let ops = Rc::clone(ops);
                self.reify_rel(tm, &ops, depth)
            }
        }
    }

    fn binary(&mut self, tm: &Rc<Term>, name: &str, depth: u32) -> Result<Option<(Syn, Syn)>, String> {
        let args = named_args(self.elab, tm, name);
        self.binary_args(args, depth)
    }

    /// [`Self::binary`] at a carrier's operation.
    fn binary_op(&mut self, tm: &Rc<Term>, op: &Op, depth: u32) -> Result<Option<(Syn, Syn)>, String> {
        let args = op.args(self.elab, tm);
        self.binary_args(args, depth)
    }

    fn binary_args(&mut self, args: Option<Vec<&Rc<Term>>>, depth: u32) -> Result<Option<(Syn, Syn)>, String> {
        let Some(args) = args else {
            return Ok(None);
        };
        let [left, right] = args.as_slice() else {
            return Ok(None);
        };
        let (left, right) = (Rc::clone(left), Rc::clone(right));
        Ok(Some((self.reify_within(&left, depth)?, self.reify_within(&right, depth)?)))
    }

    fn reify_int(&mut self, tm: &Rc<Term>, depth: u32) -> Result<Syn, String> {
        if let Some((a, b)) = self.binary(tm, "int::Int::add", depth)? {
            return Ok(Syn::Add(Box::new(a), Box::new(b)));
        }
        if let Some((a, b)) = self.binary(tm, "int::Int::sub", depth)? {
            return Ok(Syn::Sub(Box::new(a), Box::new(b)));
        }
        if let Some((a, b)) = self.binary(tm, "int::Int::mul", depth)? {
            return Ok(Syn::Mul(Box::new(a), Box::new(b)));
        }
        if let Some(args) = named_args(self.elab, tm, "int::Int::neg")
            && let [inner] = args.as_slice()
        {
            let inner = Rc::clone(inner);
            return Ok(Syn::Neg(Box::new(self.reify_within(&inner, depth)?)));
        }
        if let Some(value) = self.elab.spell_term_source(self.cx, tm).as_deref().and_then(integer_source) {
            return Ok(Syn::Const(value));
        }
        if let Some(atom) = self.nat_image(tm, depth)? {
            return Ok(Syn::Atom(atom));
        }
        self.projection_or_atom(tm, depth)
    }

    /// The `Nat → Int` edge (docs/casting-design.md §12): an image of a
    /// `Nat` sum, product or successor, `OfNat(m + n)` or `(m * n).int()`, is
    /// an atom read with the edge's law (`Int::ofNat_hom`'s `map_add` and
    /// `map_mul`), whose right side, the images of the parts spelled as the
    /// image was, is read the same way: [`Self::edge_image`] for this edge.
    /// The image stays an atom, so a term converting to it under another
    /// spelling (`Rat::add(x, y).den` beside `x.den * y.den`) is the same
    /// atom still.
    fn nat_image(&mut self, tm: &Rc<Term>, depth: u32) -> Result<Option<usize>, String> {
        let (inner, rebuild): (Rc<Term>, fn(&str) -> String) =
            if let Some(args) = named_args(self.elab, tm, "int::Nat::int") && let [n] = args.as_slice() {
                (Rc::clone(n), |p| format!("int::Nat::int({p})"))
            } else {
                let Some(source) = self.elab.spell_term_source(self.cx, tm) else { return Ok(None) };
                let Some(body) = source.strip_prefix("int::OfNat(").or_else(|| source.strip_prefix("OfNat(")).and_then(|b| b.strip_suffix(')')) else {
                    return Ok(None);
                };
                let Some(inner) = parse_expr(body)
                    .ok()
                    .and_then(|e| self.elab.generated_scope(|me| me.elab_check(self.cx, &e, &Type::Nat, &Level::Zero)).ok())
                else {
                    return Ok(None);
                };
                (Rc::new(inner), |p| format!("int::OfNat({p})"))
            };
        let (law, parts) = if let Term::Succ(a) = &*inner {
            ("map_add", vec![Rc::clone(a), Rc::new(Term::Succ(Rc::new(Term::Zero)))])
        } else if let Some(xs) = named_args(self.elab, &inner, "nat::Nat::add")
            && let [x, y] = xs.as_slice()
        {
            ("map_add", vec![Rc::clone(x), Rc::clone(y)])
        } else if let Some(xs) = named_args(self.elab, &inner, "nat::Nat::mul")
            && let [x, y] = xs.as_slice()
        {
            ("map_mul", vec![Rc::clone(x), Rc::clone(y)])
        } else {
            return Ok(None);
        };
        let mut sources = Vec::new();
        for part in &parts {
            let Some(part) = self.elab.spell_term_source(self.cx, part) else { return Ok(None) };
            sources.push(format!("({part})"));
        }
        let proof = format!("(int::Int::ofNat_hom()).{law}({})", sources.join(", "));
        let Some((term, ty, level)) = parse_expr(&proof)
            .ok()
            .and_then(|e| self.elab.generated_scope(|me| me.elab_infer(self.cx, &e)).ok())
        else {
            return Ok(None);
        };
        let Some(eq) = equation(self.elab, self.cx, &ty) else {
            return Ok(None);
        };
        let oracle = self.elab.goal_oracle().bounded(NUMERAL_STEPS);
        if oracle.convert_term(&self.cx.gamma, Layer::Prog, tm, &eq.lhs, &self.ty, &self.level).is_err() {
            return Ok(None);
        }
        let atom = self.intern(tm)?;
        if self.facts.iter().any(|f| f.atom == atom) {
            return Ok(Some(atom));
        }
        let mut syns = Vec::new();
        for part in &sources {
            let Some(image) = parse_expr(&rebuild(part))
                .ok()
                .and_then(|e| self.elab.generated_scope(|me| me.elab_check(self.cx, &e, &self.ty, &self.level)).ok())
            else {
                return Ok(None);
            };
            syns.push(self.reify_within(&Rc::new(image), depth)?);
        }
        let [a, b] = syns.as_slice() else { return Ok(None) };
        let rhs = match law {
            "map_mul" => Syn::Mul(Box::new(a.clone()), Box::new(b.clone())),
            _ => Syn::Add(Box::new(a.clone()), Box::new(b.clone())),
        };
        let sides = Written { lhs: Syn::Atom(atom), rhs };
        self.facts.push(Fact { atom, kind: FactKind::Definition, term, ty, level, sides });
        Ok(Some(atom))
    }

    fn reify_nat(&mut self, tm: &Rc<Term>, depth: u32) -> Result<Syn, String> {
        match &**tm {
            Term::Zero => return Ok(Syn::Const(0)),
            Term::NatLit(n) => {
                let value = n
                    .to_string()
                    .parse::<Z>()
                    .map_err(|_| format!("`ring` cannot read the numeral `{n}` as a coefficient"))?;
                return Ok(Syn::Const(value));
            }
            // `Succ(x)` is `x + 1`, which computes back to it.
            Term::Succ(inner) => {
                let inner = Rc::clone(inner);
                let inner = self.reify_within(&inner, depth)?;
                return Ok(Syn::Add(Box::new(inner), Box::new(Syn::Const(1))));
            }
            _ => {}
        }
        if let Some((a, b)) = self.binary(tm, "nat::Nat::add", depth)? {
            return Ok(Syn::Add(Box::new(a), Box::new(b)));
        }
        if let Some((a, b)) = self.binary(tm, "nat::Nat::mul", depth)? {
            return Ok(Syn::Mul(Box::new(a), Box::new(b)));
        }
        self.projection_or_atom(tm, depth)
    }

    /// At a `≈` carrier the operations are its designations and a constant is
    /// a numeral, which `of_int` reads back to. Everything else is an atom:
    /// a field read is a value of the carrier, not a computation to look
    /// through.
    fn reify_rel(&mut self, tm: &Rc<Term>, ops: &RelCarrier, depth: u32) -> Result<Syn, String> {
        if let Some(op) = &ops.add
            && let Some((a, b)) = self.binary_op(tm, op, depth)?
        {
            return Ok(Syn::Add(Box::new(a), Box::new(b)));
        }
        if let Some(op) = &ops.sub
            && let Some((a, b)) = self.binary_op(tm, op, depth)?
        {
            return Ok(Syn::Sub(Box::new(a), Box::new(b)));
        }
        if let Some(op) = &ops.mul
            && let Some((a, b)) = self.binary_op(tm, op, depth)?
        {
            return Ok(Syn::Mul(Box::new(a), Box::new(b)));
        }
        if let Some(op) = &ops.neg
            && let Some(args) = op.args(self.elab, tm)
            && let [inner] = args.as_slice()
        {
            let inner = Rc::clone(inner);
            return Ok(Syn::Neg(Box::new(self.reify_within(&inner, depth)?)));
        }
        if !self.in_fact
            && let Some(atom) = self.reciprocal(tm, ops, depth)?
        {
            return Ok(Syn::Atom(atom));
        }
        if let Some(value) = self.rel_numeral(tm, ops) {
            return Ok(Syn::Const(value));
        }
        if let Some(atom) = self.cast(tm, ops, depth)? {
            return Ok(Syn::Atom(atom));
        }
        if let Some(atom) = self.edge_image(tm, depth)? {
            return Ok(Syn::Atom(atom));
        }
        if let Some(step) = self.range_step(tm, depth)? {
            return Ok(step);
        }
        if let Some(image) = self.wrapped_image(tm) {
            return self.reify_within(&image, depth);
        }
        Ok(Syn::Atom(self.intern(tm)?))
    }

    /// A definition that is an edge's image under another name
    /// (`Finite::val(x)` is `x.dyadic().rat()`, `Format::grid(F, n)` is
    /// `Dyadic(n, …).rat()`, docs/casting-design.md §13): its first few
    /// δ-reducts, the first that is an edge's map applied, so the image is
    /// read, and named, as it is everywhere else.
    fn wrapped_image(&self, tm: &Rc<Term>) -> Option<Rc<Term>> {
        let (head, args) = app_spine(tm);
        if args.is_empty() || !matches!(head, Term::GlobalTm { .. }) {
            return None;
        }
        if EDGES.iter().any(|edge| named_args(self.elab, tm, edge.map).is_some()) {
            return None;
        }
        // A reduct is read back by its spelling, re-elaborated here: a
        // δ-step's result carries the definition's own substitution.
        let oracle = self.elab.goal_oracle().bounded(NUMERAL_STEPS);
        let source = oracle
            .unfold(&self.cx.gamma, tm, Unfold::RingWrapper)
            .filter_map(|reduct| self.elab.spell_term_source(self.cx, &reduct))
            .find(|source| EDGES.iter().any(|edge| source.starts_with(&format!("{}(", edge.map))))?;
        let image = parse_expr(&source)
            .ok()
            .and_then(|e| self.elab.generated_scope(|me| me.elab_check(self.cx, &e, &self.ty, &self.level)).ok())?;
        Some(Rc::new(image))
    }

    /// A range sum at a successor bound is its last term added on, a range
    /// product its last factor multiplied on (`crate::range_sum`); the
    /// carrier's own `+` or `*` only, a global's or a class carrier's.
    fn range_step(&mut self, tm: &Rc<Term>, depth: u32) -> Result<Option<Syn>, String> {
        let int_ops = (Op::Global("int::Int::add".into()), Op::Global("int::Int::mul".into()));
        let nat_ops = (Op::Global("nat::Nat::add".into()), Op::Global("nat::Nat::mul".into()));
        let (add, mul) = match &self.carrier {
            Carrier::Int => (Some(&int_ops.0), Some(&int_ops.1)),
            Carrier::Nat => (Some(&nat_ops.0), Some(&nat_ops.1)),
            Carrier::Rel(ops) => (ops.add.as_ref(), ops.mul.as_ref()),
        };
        let is = |op: &Term, ring_op: Option<&Op>| ring_op.is_some_and(|ring_op| ring_op.is(self.elab, op));
        if let Some(op) = crate::range_sum::empty(self.elab, tm) {
            return Ok(if is(&op, add) {
                Some(Syn::Const(0))
            } else if is(&op, mul) {
                Some(Syn::Const(1))
            } else {
                None
            });
        }
        let Some(peeled) = crate::range_sum::peel(self.elab, tm) else {
            return Ok(None);
        };
        let (sum, product) = (is(&peeled.op, add), is(&peeled.op, mul));
        if !sum && !product {
            return Ok(None);
        }
        let rest = self.reify_within(&peeled.rest, depth)?;
        let last = self.reify_within(&peeled.last, depth)?;
        Ok(Some(if sum { Syn::Add(Box::new(rest), Box::new(last)) } else { Syn::Mul(Box::new(rest), Box::new(last)) }))
    }

    /// A reciprocal is an atom `r` like any other, read together with the
    /// library's fact `r·d ≈ 1`: `x⁻¹` (the carrier's postfix `⁻¹`, whose
    /// fact is the lemma beside it, `<op>_mul`: `x⁻¹ * x ≈ 1`) and
    /// `Rat::inv_succ(n)` (`Rat::inv_succ_cancel`). The facts are what clear
    /// the denominators (`clear_denominators`). Apartness is already in the
    /// term — `x⁻¹` was elaborated with it — so clearing owes no side
    /// condition. A reciprocal whose fact cannot be written stays a plain
    /// atom.
    fn reciprocal(&mut self, tm: &Rc<Term>, ops: &RelCarrier, depth: u32) -> Result<Option<usize>, String> {
        let (lemma, den, args) = if let Some(op) = ops.inv.as_ref().and_then(Op::global)
            && let Some(args) = named_args(self.elab, tm, op)
            && let [x, h] = args.as_slice()
        {
            (format!("{op}_mul"), Some(Rc::clone(x)), vec![(None, Rc::clone(x)), (Some("h"), Rc::clone(h))])
        } else if let Some(args) = named_args(self.elab, tm, "rat::Rat::inv_succ")
            && let [n] = args.as_slice()
        {
            ("rat::Rat::inv_succ_cancel".to_string(), None, vec![(None, Rc::clone(n))])
        } else {
            return Ok(None);
        };
        let atom = self.intern(tm)?;
        if self.facts.iter().any(|f| f.atom == atom) {
            return Ok(Some(atom));
        }
        // A reciprocal inside the denominator is met, and its fact read,
        // before this one's.
        if let Some(den) = den {
            self.reify_within(&den, depth)?;
        }
        if let Some(fact) = self.reciprocal_fact(&lemma, &args, atom) {
            self.facts.push(fact);
        }
        Ok(Some(atom))
    }

    fn reciprocal_fact(&mut self, lemma: &str, args: &[(Option<&str>, Rc<Term>)], atom: usize) -> Option<Fact> {
        self.elab.key_of(lemma)?;
        let mut written = Vec::new();
        for (name, arg) in args {
            let source = self.elab.spell_term_source(self.cx, arg)?;
            written.push(match name {
                Some(name) => format!("{name} := {source}"),
                None => source,
            });
        }
        let expr = parse_expr(&format!("{lemma}({})", written.join(", "))).ok()?;
        let (term, ty, level) = self.elab.generated_scope(|me| me.elab_infer(self.cx, &expr)).ok()?;
        let eq = relation_equation(self.elab, self.cx, &ty, self.span).filter(|eq| eq.carrier == self.carrier)?;
        self.in_fact = true;
        let sides = (|| Ok::<_, String>(Written { lhs: self.reify(&eq.lhs)?, rhs: self.reify(&eq.rhs)? }))();
        self.in_fact = false;
        let sides = sides.ok()?;
        Some(Fact { atom, kind: FactKind::Reciprocal, term, ty, level, sides })
    }

    /// A cast of a `Nat` sum, product or successor (`Rat::ofInt(OfNat(n + n
    /// + 1))`, as `inv_succ`'s denominators are) is an atom read with the fact
    /// that pushes the embedding one level in (`RingExpr::of_nat_add`, …),
    /// whose right side's casts are read the same way. A cast is recognized
    /// by its spelling, `…OfNat(e)…`, and confirmed by converting it to the
    /// fact's left side, which is the instance's `of_int` at the same `e`.
    fn cast(&mut self, tm: &Rc<Term>, ops: &RelCarrier, depth: u32) -> Result<Option<usize>, String> {
        let Some(source) = self.elab.spell_term_source(self.cx, tm) else {
            return Ok(None);
        };
        let Some((prefix, inner, suffix)) = cast_parts(&source) else {
            return Ok(None);
        };
        let Some(inner) = parse_expr(inner)
            .ok()
            .and_then(|e| self.elab.generated_scope(|me| me.elab_check(self.cx, &e, &Type::Nat, &Level::Zero)).ok())
        else {
            return Ok(None);
        };
        let inner = Rc::new(inner);
        let (lemma, parts) = if let Term::Succ(a) = &*inner {
            ("of_nat_succ", vec![Rc::clone(a)])
        } else if let Some(args) = named_args(self.elab, &inner, "nat::Nat::add")
            && let [a, b] = args.as_slice()
        {
            ("of_nat_add", vec![Rc::clone(a), Rc::clone(b)])
        } else if let Some(args) = named_args(self.elab, &inner, "nat::Nat::mul")
            && let [a, b] = args.as_slice()
        {
            ("of_nat_mul", vec![Rc::clone(a), Rc::clone(b)])
        } else {
            return Ok(None);
        };
        let atom = self.intern(tm)?;
        if self.facts.iter().any(|f| f.atom == atom) {
            return Ok(Some(atom));
        }
        let mut sources = Vec::new();
        let mut syns = Vec::new();
        for part in &parts {
            let Some(part) = self.elab.spell_term_source(self.cx, part) else {
                return Ok(Some(atom));
            };
            let Some(cast) = parse_expr(&format!("{prefix}OfNat({part}){suffix}"))
                .ok()
                .and_then(|e| self.elab.generated_scope(|me| me.elab_check(self.cx, &e, &self.ty, &self.level)).ok())
            else {
                return Ok(Some(atom));
            };
            syns.push(self.reify_within(&Rc::new(cast), depth)?);
            sources.push(part);
        }
        let rhs = match (lemma, syns.as_slice()) {
            ("of_nat_succ", [a]) => Syn::Add(Box::new(a.clone()), Box::new(Syn::Const(1))),
            ("of_nat_add", [a, b]) => Syn::Add(Box::new(a.clone()), Box::new(b.clone())),
            (_, [a, b]) => Syn::Mul(Box::new(a.clone()), Box::new(b.clone())),
            _ => return Ok(Some(atom)),
        };
        let written = format!("ring::RingExpr::{lemma}<{}>(Nil, {})", ops.source, sources.join(", "));
        let Some((term, ty, level)) = parse_expr(&written)
            .ok()
            .and_then(|e| self.elab.generated_scope(|me| me.elab_infer(self.cx, &e)).ok())
        else {
            return Ok(Some(atom));
        };
        let oracle = self.elab.goal_oracle().bounded(NUMERAL_STEPS);
        let confirmed = relation_equation(self.elab, self.cx, &ty, self.span).is_some_and(|eq| {
            oracle
                .convert_term(&self.cx.gamma, Layer::Prog, tm, &eq.lhs, &self.ty, &self.level)
                .is_ok()
        });
        if confirmed {
            let sides = Written { lhs: Syn::Atom(atom), rhs };
            self.facts.push(Fact { atom, kind: FactKind::Definition, term, ty, level, sides });
        }
        Ok(Some(atom))
    }

    /// An edge's image of an operation (`(a + c).rat()`, `CReal::ofRat(p *
    /// q)`, `Rat::ofInt(-m)`: `+`, `*`, negation, and subtraction as `x + -y`)
    /// is an atom read with the
    /// edge's law (the field `map_add` of `Dyadic::rat_hom`,
    /// docs/casting-design.md §11), whose right side, the images of the
    /// operands, is read the same way. An image of an image (`CReal::ofRat((a + c).rat())`) carries the
    /// inner law through the outer edge by `map_respects`. Confirmed, like
    /// [`Self::cast`], by converting the term to the law's left side.
    fn edge_image(&mut self, tm: &Rc<Term>, depth: u32) -> Result<Option<usize>, String> {
        let Some(proof) = self.edge_law(tm, EDGE_NESTING) else {
            return Ok(None);
        };
        let Some((term, ty, level)) = parse_expr(&proof)
            .ok()
            .and_then(|e| self.elab.generated_scope(|me| me.elab_infer(self.cx, &e)).ok())
        else {
            return Ok(None);
        };
        let Some(eq) = relation_equation(self.elab, self.cx, &ty, self.span) else {
            return Ok(None);
        };
        let oracle = self.elab.goal_oracle().bounded(NUMERAL_STEPS);
        if oracle.convert_term(&self.cx.gamma, Layer::Prog, tm, &eq.lhs, &self.ty, &self.level).is_err() {
            return Ok(None);
        }
        let atom = self.intern(tm)?;
        if self.facts.iter().any(|f| f.atom == atom) {
            return Ok(Some(atom));
        }
        let rhs = self.reify_within(&eq.rhs, depth)?;
        let sides = Written { lhs: Syn::Atom(atom), rhs };
        self.facts.push(Fact { atom, kind: FactKind::Definition, term, ty, level, sides });
        Ok(Some(atom))
    }

    /// The source of a proof that `tm`, an edge's image, is `≈` to the
    /// images of what it is an image of; `None` where `tm` is no edge's
    /// image of an operation, at most `nesting` edges deep.
    fn edge_law(&self, tm: &Rc<Term>, nesting: u32) -> Option<String> {
        if nesting == 0 {
            return None;
        }
        let spell = |t: &Term| self.elab.spell_term_source(self.cx, t);
        for edge in EDGES {
            let Some(args) = named_args(self.elab, tm, edge.map) else { continue };
            let [inner] = args.as_slice() else { continue };
            // The edge's field, read off its value: its type names every
            // index, and no import of `morphism` is needed where `ring` runs.
            let law = |field: &str, rest: &str| format!("({}()).{field}({rest})", edge.hom);
            for (op, name) in [(edge.add, "map_add"), (edge.mul, "map_mul")] {
                if let Some(xs) = named_args(self.elab, inner, op)
                    && let [x, y] = xs.as_slice()
                {
                    return Some(law(name, &format!("({}), ({})", spell(x)?, spell(y)?)));
                }
            }
            if let Some(xs) = named_args(self.elab, inner, edge.neg)
                && let [x] = xs.as_slice()
            {
                return Some(law("map_neg", &format!("({})", spell(x)?)));
            }
            // Every carrier's `x - y` is `x + -y`: the add law at `-y`, whose
            // left side the caller converts to the image.
            if let Some(xs) = named_args(self.elab, inner, edge.sub)
                && let [x, y] = xs.as_slice()
            {
                return Some(law("map_add", &format!("({}), -({})", spell(x)?, spell(y)?)));
            }
            // An image of an image: the inner law, carried through this edge.
            let proof = self.edge_law(inner, nesting - 1)?;
            let (_, ty, _) = parse_expr(&proof)
                .ok()
                .and_then(|e| self.elab.generated_scope(|me| me.elab_infer(self.cx, &e)).ok())?;
            let rel = Relation::of_type(self.elab, self.cx, &ty, self.span)?;
            return Some(law("map_respects", &format!("({}), ({}), {proof}", spell(inner)?, spell(&rel.right)?)));
        }
        self.local_edge_law(tm, nesting)
    }

    /// [`Self::edge_law`] along a morphism in scope ([`LocalEdge`]): the
    /// family's law at the local, `OrderedRingHom::add_law<A, K>(hom, x, y)`.
    /// The source's operations are the morphism type's indices, which no
    /// table names, so each law that fits the image's shape is written and
    /// the first whose left side converts to the image is the one: `+`,
    /// `*`, subtraction as `x + -y`, negation, `0` and `1`; and an image of
    /// an image carries the inner law through `respects_law`.
    fn local_edge_law(&self, tm: &Rc<Term>, nesting: u32) -> Option<String> {
        let (head, args) = app_spine(tm);
        let [inner] = args.as_slice() else { return None };
        let edges = self.local_edges.get_or_init(|| self.find_local_edges());
        let edge = edges.iter().find(|e| *head == *e.map)?;
        let spell = |t: &Term| self.elab.spell_term_source(self.cx, t);
        let law = |name: &str, rest: &str| {
            let sep = if rest.is_empty() { "" } else { ", " };
            format!("morphism::OrderedRingHom::{name}<{}, {}>({}{sep}{rest})", edge.source, self.carrier.name(), edge.hom)
        };
        let fits = |proof: &str| {
            let Some((_, ty, _)) = parse_expr(proof)
                .ok()
                .and_then(|e| self.elab.generated_scope(|me| me.elab_infer(self.cx, &e)).ok())
            else {
                return false;
            };
            let Some(rel) = Relation::of_type(self.elab, self.cx, &ty, self.span) else { return false };
            let oracle = self.elab.goal_oracle().bounded(NUMERAL_STEPS);
            oracle.convert_term(&self.cx.gamma, Layer::Prog, tm, &rel.left, &self.ty, &self.level).is_ok()
        };
        let (_, parts) = app_spine(inner);
        let mut candidates = Vec::new();
        match parts.as_slice() {
            [x, y] => {
                let (x, y) = (spell(x)?, spell(y)?);
                candidates.push(law("add_law", &format!("({x}), ({y})")));
                candidates.push(law("mul_law", &format!("({x}), ({y})")));
                candidates.push(law("add_law", &format!("({x}), -({y})")));
            }
            [x] => candidates.push(law("neg_law", &format!("({})", spell(x)?))),
            _ => {}
        }
        match spell(inner).and_then(|s| integer_source(&s).or_else(|| trailing_integer(&s))) {
            Some(0) => candidates.push(law("zero_law", "")),
            Some(1) => candidates.push(law("one_law", "")),
            _ => {}
        }
        if let Some(found) = candidates.into_iter().find(|c| fits(c)) {
            return Some(found);
        }
        // An image of an image: the inner law, carried through this edge.
        let proof = self.edge_law(inner, nesting - 1)?;
        let (_, ty, _) = parse_expr(&proof)
            .ok()
            .and_then(|e| self.elab.generated_scope(|me| me.elab_infer(self.cx, &e)).ok())?;
        let rel = Relation::of_type(self.elab, self.cx, &ty, self.span)?;
        Some(law("respects_law", &format!("({}), ({}), {proof}", spell(inner)?, spell(&rel.right)?)))
    }

    /// The morphisms in scope that map into this carrier
    /// (docs/casting-design.md §15, §16): a local whose type is
    /// `OrderedRingHom<A, K>(map, …)`, found as `mono` finds one. The record
    /// is structural, so its type names no family: a local map `A → K` in
    /// scope gives the candidate `A`, and a local is a morphism when the
    /// family's `zero_law<A, K>` checks at it, whose statement then names
    /// the map. Nothing is tried where no local maps into the carrier.
    fn find_local_edges(&self) -> Vec<LocalEdge> {
        let mut edges = Vec::new();
        if self.elab.key_of("morphism::OrderedRingHom::zero_law").is_none() {
            return edges;
        }
        let Some(carrier) = self.elab.spell_type_clean(self.cx, &self.ty) else {
            return edges;
        };
        let names = &self.cx.names;
        let mut sources: Vec<String> = Vec::new();
        for pos in 0..names.len() {
            let (_, ty, _) = self.elab.local(self.cx, pos);
            if let Type::Pi { dom, cod, .. } = &ty
                && **cod == self.ty.shift_local(1)
                && let Some(source) = self.elab.spell_type_clean(self.cx, dom)
                && !sources.contains(&source)
            {
                sources.push(source);
            }
        }
        if sources.is_empty() {
            return edges;
        }
        for pos in (0..names.len()).rev() {
            let name = &names[pos];
            let (_, ty, _) = self.elab.local(self.cx, pos);
            if matches!(ty, Type::Pi { .. }) || !name.chars().all(|c| c.is_alphanumeric() || c == '_') {
                continue;
            }
            for source in &sources {
                let written = format!("morphism::OrderedRingHom::zero_law<{source}, {carrier}>({name})");
                let Some((_, ty, _)) = parse_expr(&written)
                    .ok()
                    .and_then(|e| self.elab.generated_scope(|me| me.elab_infer(self.cx, &e)).ok())
                else {
                    continue;
                };
                let Some(rel) = Relation::of_type(self.elab, self.cx, &ty, self.span) else { continue };
                let (map, args) = app_spine(&rel.left);
                if args.len() == 1 {
                    edges.push(LocalEdge { hom: name.to_string(), source: source.clone(), map: Rc::new(map.clone()) });
                    break;
                }
            }
        }
        edges
    }

    /// The integer a carrier's numeral stands for: the one its spelling ends
    /// in (`Rat::ofInt(OfNat(2))`, `CReal::ofRat(Rat::ofInt(OfNat(2)))`),
    /// confirmed by converting the term to what the certificate's `RConst`
    /// evaluates to, so a term that only spells like a numeral stays an atom.
    /// At a class carrier, `K.unit` and `K.multiplicative.unit` are `0` and
    /// `1` as written, and another constant is the integers' image spelled
    /// out (`semiring::Ring::int_cast<K>(int::OfNat(2))`, what `linarith`
    /// writes for its coefficients).
    fn rel_numeral(&self, tm: &Rc<Term>, ops: &RelCarrier) -> Option<Z> {
        if let Some(ints) = &ops.class {
            if same_dictionary_read(tm, &ints.zero) {
                return Some(0);
            }
            if same_dictionary_read(tm, &ints.one) {
                return Some(1);
            }
        }
        let source = self.elab.spell_term_source(self.cx, tm)?;
        let value = integer_source(&source).or_else(|| trailing_integer(&source))?;
        let written = match &ops.class {
            None => format!("ring::RingExpr::eval_rel<{}>(ring::RConst({}), Nil)", ops.source, int_source(value)),
            Some(_) => format!("semiring::Ring::int_cast<{}>({})", ops.source, int_source(value)),
        };
        let expr = parse_expr(&written).ok()?;
        let constant = self
            .elab
            .generated_scope(|me| me.elab_check(self.cx, &expr, &self.ty, &self.level))
            .ok()?;
        let oracle = self.elab.goal_oracle().bounded(NUMERAL_STEPS);
        oracle
            .convert_term(&self.cx.gamma, Layer::Prog, tm, &Rc::new(constant), &self.ty, &self.level)
            .is_ok()
            .then_some(value)
    }

    /// A field read off a value that computes to a constructor is read as the
    /// field: `Rat::add(x, y).num` is the numerator `add` builds, whether the
    /// read is the inline walk or a named projection
    /// ([`Elaborator::named_field_read`]). Anything else is an atom.
    fn projection_or_atom(&mut self, tm: &Rc<Term>, depth: u32) -> Result<Syn, String> {
        if let Some(step) = self.range_step(tm, depth)? {
            return Ok(step);
        }
        if depth > 0
            && let Some(field) = self.project(tm)
        {
            // A field that reifies into nothing spellable (a stuck `match`
            // inside the constructor's body) stays the projection it was.
            let mark = self.atoms.len();
            match self.reify_within(&field, depth - 1) {
                Ok(syn) => return Ok(syn),
                Err(_) => self.atoms.truncate(mark),
            }
        }
        Ok(Syn::Atom(self.intern(tm)?))
    }

    fn project(&self, tm: &Rc<Term>) -> Option<Rc<Term>> {
        let (path, cur) = self.elab.named_field_read(tm).unwrap_or_else(|| projection_path(tm));
        // A call computes to its record; a literal record (`Rat(a, p, h).num`)
        // already is one.
        if path.is_empty() || !(matches!(app_spine(cur).0, Term::GlobalTm { .. }) || crate::spelling::is_pair(cur)) {
            return None;
        }
        let oracle = self.elab.goal_oracle().bounded(ATOM_STEPS);
        let mut value = Rc::clone(cur);
        for first in path.into_iter().rev() {
            if crate::spelling::pair_of(&value).is_none() {
                value = Rc::new(oracle.whnf_term_bounded(&self.cx.gamma, &value).ok()?);
            }
            let (fst, snd) = crate::spelling::pair_of(&value)?;
            value = Rc::clone(if first { fst } else { snd });
        }
        Some(value)
    }

    /// The index of `tm` in the atom table: the same term, or one it is
    /// convertible to by a bounded check when both share a head and differ
    /// somewhere computation could reach (`(-x).den.int()` against
    /// `x.den.int()`).
    fn intern(&mut self, tm: &Rc<Term>) -> Result<usize, String> {
        if let Some(index) = self.atoms.iter().position(|atom| atom.term == *tm) {
            return Ok(index);
        }
        // An atom that does not spell (a field read such as `x.seq(n)`,
        // issues/ring-field-read-atom-spelling.md) is named by an alias
        // bound to the term itself when the atom list is elaborated.
        // So is one whose spelling does not parse: a range sum at a class
        // carrier spells its operation as the operator variable (`#op+@…`).
        let spelled = self.elab.spell_term_source(self.cx, tm).filter(|source| parse_expr(source).is_ok());
        if let Some(source) = &spelled
            && let Some(index) = self.atoms.iter().position(|atom| !atom.named && atom.source == *source)
        {
            return Ok(index);
        }
        if let Some(index) = self.convertible(tm) {
            return Ok(index);
        }
        let index = self.atoms.len();
        let (source, shown, named) = match spelled {
            Some(source) => (source.clone(), source, false),
            None => (atom_alias(index), self.elab.display_rough_term(self.cx, tm, &[]), true),
        };
        self.atoms.push(Atom {
            term: Rc::clone(tm),
            source,
            shown,
            named,
        });
        Ok(self.atoms.len() - 1)
    }

    fn convertible(&self, tm: &Rc<Term>) -> Option<usize> {
        let (path, receiver) = projection_path(tm);
        let (head, args) = app_spine(receiver);
        if args.is_empty() && path.is_empty() {
            return None;
        }
        let oracle = self.elab.goal_oracle().bounded(ATOM_STEPS);
        self.atoms.iter().position(|atom| {
            let (other_path, other_receiver) = projection_path(&atom.term);
            if other_path != path {
                return false;
            }
            let (other_head, other_args) = app_spine(other_receiver);
            if *other_head != *head || other_args.len() != args.len() {
                return false;
            }
            // Two different variables never meet by computation.
            let may_meet = args.iter().zip(&other_args).any(|(a, b)| {
                a != b && !matches!((&***a, &***b), (Term::Var(_), Term::Var(_)))
            });
            may_meet
                && oracle
                    .convert_term(&self.cx.gamma, Layer::Prog, tm, &atom.term, &self.ty, &self.level)
                    .is_ok()
        })
    }
}

/// The integer a spelling ends in, as an `Int` constructor's argument with
/// only closing parentheses after it: `f(OfNat(2))` is 2, `f(NegSucc(1))` is
/// −2.
fn trailing_integer(source: &str) -> Option<Z> {
    let body = source.trim_end_matches(')');
    let closed = source.len() - body.len();
    let digits_at = body.rfind(|c: char| !c.is_ascii_digit())? + 1;
    let digits: Z = body[digits_at..].parse().ok()?;
    let head = &body[..digits_at];
    // A ring's own naturals at a numeral, `semiring::Ring::nat_cast<K>(2)`
    // (what `difference`'s falling factorials and binomial sums write): the
    // class carrier's constant, which is `Ring::int_cast<K>(OfNat(2))` by
    // computation, as the caller's conversion confirms.
    if head.ends_with(">(") && head.rsplit_once("::nat_cast<").is_some_and(|(path, _)| path.ends_with("Ring")) {
        return (closed == 1).then_some(digits);
    }
    let value = if head.ends_with("OfNat(") {
        digits
    } else if head.ends_with("NegSucc(") {
        -digits - 1
    } else {
        return None;
    };
    // `OfNat(2)` closes once, and the call around it at least once more.
    (closed >= 2).then_some(value)
}

/// A cast's spelling split around its `Nat`: `rat::Rat::ofInt(OfNat(e))` is
/// `("rat::Rat::ofInt(", "e", ")")` — the first `OfNat(`, with only closing
/// parentheses after the one that closes it, and at least one.
fn cast_parts(source: &str) -> Option<(&str, &str, &str)> {
    let at = source.find("OfNat(")?;
    let open = at + "OfNat(".len();
    let mut depth = 1i32;
    let close = open + source[open..].find(|c: char| {
        depth += match c {
            '(' => 1,
            ')' => -1,
            _ => 0,
        };
        depth == 0
    })?;
    let suffix = &source[close + 1..];
    (close > open && !suffix.is_empty() && suffix.chars().all(|c| c == ')'))
        .then(|| (&source[..at], &source[open..close], suffix))
}

fn app_spine(tm: &Rc<Term>) -> (&Term, Vec<&Rc<Term>>) {
    let mut args = Vec::new();
    let mut head = &**tm;
    while let Some((fun, arg)) = crate::spelling::app_of(head) {
        args.push(arg);
        head = fun;
    }
    args.reverse();
    (head, args)
}

fn projection_path(tm: &Rc<Term>) -> (Vec<bool>, &Rc<Term>) {
    let mut path = Vec::new();
    let mut cur = tm;
    while let Some((first, pair)) = crate::spelling::proj_of(cur) {
        path.push(first);
        cur = pair;
    }
    (path, cur)
}

// ---------------------------------------------------------------------------
// The searcher's polynomials: exponent vectors with no trailing zero, mapped
// to nonzero coefficients.

type Mono = Vec<u32>;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Poly(BTreeMap<Mono, Z>);

fn overflow() -> String {
    "`ring`: a coefficient overflowed 128 bits".into()
}

fn trim(mut m: Mono) -> Mono {
    while m.last() == Some(&0) {
        m.pop();
    }
    m
}

fn mono_mul(a: &Mono, b: &Mono) -> Result<Mono, String> {
    let mut out = vec![0; a.len().max(b.len())];
    for (i, e) in a.iter().enumerate() {
        out[i] = *e;
    }
    for (i, e) in b.iter().enumerate() {
        out[i] = out[i].checked_add(*e).ok_or_else(overflow)?;
    }
    Ok(trim(out))
}

/// `a / b` when `b` divides `a`.
fn mono_div(a: &Mono, b: &Mono) -> Option<Mono> {
    if b.len() > a.len() {
        return None;
    }
    let mut out = a.clone();
    for (i, e) in b.iter().enumerate() {
        out[i] = out[i].checked_sub(*e)?;
    }
    Some(trim(out))
}

impl Poly {
    fn constant(c: Z) -> Self {
        let mut map = BTreeMap::new();
        if c != 0 {
            map.insert(Vec::new(), c);
        }
        Poly(map)
    }

    fn monomial(c: Z, m: Mono) -> Self {
        let mut map = BTreeMap::new();
        if c != 0 {
            map.insert(m, c);
        }
        Poly(map)
    }

    fn atom(index: usize) -> Self {
        let mut m = vec![0; index + 1];
        m[index] = 1;
        Self::monomial(1, m)
    }

    fn is_zero(&self) -> bool {
        self.0.is_empty()
    }

    fn add_term(&mut self, m: Mono, c: Z) -> Result<(), String> {
        if c == 0 {
            return Ok(());
        }
        let entry = self.0.entry(m).or_insert(0);
        *entry = entry.checked_add(c).ok_or_else(overflow)?;
        if *entry == 0 {
            self.0.retain(|_, c| *c != 0);
        }
        Ok(())
    }

    fn add(&self, other: &Self) -> Result<Self, String> {
        let mut out = self.clone();
        for (m, c) in &other.0 {
            out.add_term(m.clone(), *c)?;
        }
        Ok(out)
    }

    fn neg(&self) -> Result<Self, String> {
        let mut out = BTreeMap::new();
        for (m, c) in &self.0 {
            out.insert(m.clone(), c.checked_neg().ok_or_else(overflow)?);
        }
        Ok(Poly(out))
    }

    fn sub(&self, other: &Self) -> Result<Self, String> {
        self.add(&other.neg()?)
    }

    fn mul(&self, other: &Self) -> Result<Self, String> {
        let mut out = Poly::default();
        for (m, c) in &self.0 {
            for (n, d) in &other.0 {
                out.add_term(mono_mul(m, n)?, c.checked_mul(*d).ok_or_else(overflow)?)?;
            }
        }
        Ok(out)
    }

    fn scale(&self, c: Z, m: &Mono) -> Result<Self, String> {
        self.mul(&Poly::monomial(c, m.clone()))
    }
}

/// The bases of the squares `syn` writes: each product whose two factors
/// read as one nonconstant polynomial.
/// `syn` with each defined atom replaced by its definition, `fuel` levels
/// deep (a definition's right side may mention atoms defined before it).
fn defined(syn: &Syn, defs: &[(usize, Syn)], fuel: usize) -> Syn {
    let go = |s: &Syn| Box::new(defined(s, defs, fuel));
    match syn {
        Syn::Atom(a) => match defs.iter().find(|(d, _)| d == a) {
            Some((_, rhs)) if fuel > 0 => defined(rhs, defs, fuel - 1),
            _ => syn.clone(),
        },
        Syn::Const(_) => syn.clone(),
        Syn::Add(a, b) => Syn::Add(go(a), go(b)),
        Syn::Sub(a, b) => Syn::Sub(go(a), go(b)),
        Syn::Mul(a, b) => Syn::Mul(go(a), go(b)),
        Syn::Neg(a) => Syn::Neg(go(a)),
    }
}

fn squares_of(syn: &Syn, out: &mut Vec<Poly>) -> Result<(), String> {
    match syn {
        Syn::Atom(_) | Syn::Const(_) => {}
        Syn::Neg(a) => squares_of(a, out)?,
        Syn::Add(a, b) | Syn::Sub(a, b) => {
            squares_of(a, out)?;
            squares_of(b, out)?;
        }
        Syn::Mul(a, b) => {
            squares_of(a, out)?;
            squares_of(b, out)?;
            let base = poly_of(a)?;
            if base == poly_of(b)? && base.0.keys().any(|m| !m.is_empty()) && !out.contains(&base) {
                out.push(base);
            }
        }
    }
    Ok(())
}

fn poly_of(syn: &Syn) -> Result<Poly, String> {
    Ok(match syn {
        Syn::Atom(i) => Poly::atom(*i),
        Syn::Const(c) => Poly::constant(*c),
        Syn::Add(a, b) => poly_of(a)?.add(&poly_of(b)?)?,
        Syn::Sub(a, b) => poly_of(a)?.sub(&poly_of(b)?)?,
        Syn::Mul(a, b) => poly_of(a)?.mul(&poly_of(b)?)?,
        Syn::Neg(a) => poly_of(a)?.neg()?,
    })
}

/// Whether `syn` multiplies two parts neither of which is a numeral: a
/// product `omega` reads as an atom of its own, even one whose normal form
/// is linear (`x * (y - y)`).
fn multiplies(syn: &Syn) -> bool {
    match syn {
        Syn::Atom(_) | Syn::Const(_) => false,
        Syn::Add(a, b) | Syn::Sub(a, b) => multiplies(a) || multiplies(b),
        Syn::Neg(a) => multiplies(a),
        Syn::Mul(a, b) => {
            !matches!(**a, Syn::Const(_)) && !matches!(**b, Syn::Const(_)) || multiplies(a) || multiplies(b)
        }
    }
}

fn render_poly(p: &Poly, atoms: &[String]) -> String {
    if p.is_zero() {
        return "0".into();
    }
    // Highest degree first, the way a residual is read.
    let mut terms: Vec<(&Mono, &Z)> = p.0.iter().collect();
    terms.sort_by_key(|(m, _)| std::cmp::Reverse(m.iter().sum::<u32>()));
    let mut out = String::new();
    for (m, c) in terms {
        let factors: Vec<String> = m
            .iter()
            .enumerate()
            .filter(|(_, e)| **e > 0)
            .map(|(i, e)| {
                let atom = atoms.get(i).cloned().unwrap_or_else(|| format!("x{i}"));
                let atom = if atom.contains(' ') { format!("({atom})") } else { atom };
                if *e == 1 { atom } else { format!("{atom}^{e}") }
            })
            .collect();
        let magnitude = c.unsigned_abs();
        let body = match (factors.is_empty(), magnitude) {
            (true, _) => magnitude.to_string(),
            (false, 1) => factors.join(" * "),
            (false, _) => format!("{magnitude} * {}", factors.join(" * ")),
        };
        if out.is_empty() {
            if *c < 0 {
                out.push('-');
            }
        } else {
            out.push_str(if *c < 0 { " - " } else { " + " });
        }
        out.push_str(&body);
    }
    out
}

// ---------------------------------------------------------------------------
// Multipliers: `target = Σ cᵢ·hᵢ` by linear algebra over candidate monomial
// multipliers. A candidate `(i, m)` is proposed wherever a monomial of
// `hᵢ` divides a monomial that has to cancel — first the target's, then
// those the earlier candidates introduce — so a chain of substitutions
// (`D = p·QR`, `QR = q·r`) is found one link per round.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Q {
    num: Z,
    den: Z,
}

fn gcd(mut a: Z, mut b: Z) -> Z {
    a = a.abs();
    b = b.abs();
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

impl Q {
    const ZERO: Q = Q { num: 0, den: 1 };

    fn int(n: Z) -> Q {
        Q { num: n, den: 1 }
    }

    fn new(num: Z, den: Z) -> Result<Q, String> {
        if den == 0 {
            return Err("`ring`: division by zero in the multiplier search".into());
        }
        let g = gcd(num, den).max(1);
        let (mut num, mut den) = (num / g, den / g);
        if den < 0 {
            num = num.checked_neg().ok_or_else(overflow)?;
            den = den.checked_neg().ok_or_else(overflow)?;
        }
        Ok(Q { num, den })
    }

    fn is_zero(self) -> bool {
        self.num == 0
    }

    fn sub(self, o: Q) -> Result<Q, String> {
        let num = self
            .num
            .checked_mul(o.den)
            .and_then(|a| o.num.checked_mul(self.den).and_then(|b| a.checked_sub(b)))
            .ok_or_else(overflow)?;
        Q::new(num, self.den.checked_mul(o.den).ok_or_else(overflow)?)
    }

    fn mul(self, o: Q) -> Result<Q, String> {
        Q::new(
            self.num.checked_mul(o.num).ok_or_else(overflow)?,
            self.den.checked_mul(o.den).ok_or_else(overflow)?,
        )
    }

    fn div(self, o: Q) -> Result<Q, String> {
        Q::new(
            self.num.checked_mul(o.den).ok_or_else(overflow)?,
            self.den.checked_mul(o.num).ok_or_else(overflow)?,
        )
    }
}

/// A solution of `columns · x = target` over ℚ, free variables at zero.
fn solve(columns: &[Poly], target: &Poly) -> Result<Option<Vec<Q>>, String> {
    let rows: Vec<Mono> = columns
        .iter()
        .flat_map(|c| c.0.keys().cloned())
        .chain(target.0.keys().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let width = columns.len();
    let mut matrix: Vec<Vec<Q>> = rows
        .iter()
        .map(|m| {
            let mut row: Vec<Q> = columns
                .iter()
                .map(|c| Q::int(c.0.get(m).copied().unwrap_or(0)))
                .collect();
            row.push(Q::int(target.0.get(m).copied().unwrap_or(0)));
            row
        })
        .collect();
    let mut pivots = Vec::new();
    let mut next = 0;
    for col in 0..width {
        let Some(found) = (next..matrix.len()).find(|&r| !matrix[r][col].is_zero()) else {
            continue;
        };
        matrix.swap(next, found);
        let lead = matrix[next][col];
        for entry in matrix[next].iter_mut() {
            *entry = entry.div(lead)?;
        }
        for r in 0..matrix.len() {
            if r == next || matrix[r][col].is_zero() {
                continue;
            }
            let factor = matrix[r][col];
            for c in col..=width {
                let delta = factor.mul(matrix[next][c])?;
                matrix[r][c] = matrix[r][c].sub(delta)?;
            }
        }
        pivots.push((next, col));
        next += 1;
        if next == matrix.len() {
            break;
        }
    }
    if matrix[next..].iter().any(|row| !row[width].is_zero()) {
        return Ok(None);
    }
    let mut x = vec![Q::ZERO; width];
    for (row, col) in pivots {
        x[col] = matrix[row][width];
    }
    Ok(Some(x))
}

/// Polynomial multipliers `cᵢ` with `target = Σ cᵢ·hyps[i]`, integral.
fn multipliers(target: &Poly, hyps: &[Poly]) -> Result<Option<Vec<Poly>>, String> {
    let mut candidates: Vec<(usize, Mono)> = Vec::new();
    let mut proposed: BTreeSet<(usize, Mono)> = BTreeSet::new();
    let mut seen: BTreeSet<Mono> = target.0.keys().cloned().collect();
    let mut frontier: Vec<Mono> = target.0.keys().cloned().collect();
    for _ in 0..SEARCH_ROUNDS {
        let mut next = Vec::new();
        for u in &frontier {
            for (i, h) in hyps.iter().enumerate() {
                for hm in h.0.keys() {
                    let Some(m) = mono_div(u, hm) else { continue };
                    if !proposed.insert((i, m.clone())) {
                        continue;
                    }
                    for w in h.scale(1, &m)?.0.keys() {
                        if seen.insert(w.clone()) {
                            next.push(w.clone());
                        }
                    }
                    candidates.push((i, m));
                }
            }
        }
        if candidates.len() > SEARCH_CANDIDATES {
            return Ok(None);
        }
        let columns = candidates
            .iter()
            .map(|(i, m)| hyps[*i].scale(1, m))
            .collect::<Result<Vec<_>, _>>()?;
        if let Some(x) = solve(&columns, target)? {
            if x.iter().any(|q| q.den != 1) {
                return Ok(None);
            }
            let mut out = vec![Poly::default(); hyps.len()];
            for ((i, m), q) in candidates.iter().zip(&x) {
                out[*i].add_term(m.clone(), q.num)?;
            }
            // The kernel checks this too; checking here turns a searcher
            // mistake into a diagnostic instead of a `refl` failure.
            let mut sum = Poly::default();
            for (c, h) in out.iter().zip(hyps) {
                sum = sum.add(&c.mul(h)?)?;
            }
            if sum != *target {
                return Err("internal: `ring`'s multiplier search returned a wrong combination".into());
            }
            return Ok(Some(out));
        }
        if next.is_empty() {
            break;
        }
        frontier = next;
    }
    Ok(None)
}

// ---------------------------------------------------------------------------
// Clearing denominators: a reciprocal `r` with the fact `r·d − 1 = 0`
// eliminated exactly, rather than searched for.
//
// Write `P = Σₐ pₐ·rᵃ` with the `pₐ` free of `r`, `K` its top power. Then
// `dᴷ·P = Σ pₐ·dᴷ⁻ᵃ·(rd)ᵃ = P′ + H·M`, where `H = rd − 1`,
// `P′ = Σ pₐ·dᴷ⁻ᵃ` and `M = Σ pₐ·dᴷ⁻ᵃ·Sₐ` with `Sₐ = Σ_{t<a} (rd)ᵗ` (so that
// `(rd)ᵃ − 1 = H·Sₐ`). Hence `P = rᴷ·P′ + H·(rᴷ·M − S_K·P)`: `P` is in the
// ideal exactly when the cleared `P′` is. Eliminating every reciprocal
// leaves a polynomial with none, which is zero exactly when the goal is an
// identity of fields at those denominators — the multipliers are computed,
// not searched for, and a true identity is never missed.

/// `target = scale·cleared + Σⱼ multipliers[j]·facts[j]`.
struct Cleared {
    cleared: Poly,
    scale: Poly,
    /// The product of the denominators the target was multiplied by, for
    /// the refusal.
    denominator: Poly,
    multipliers: Vec<Poly>,
}

/// `d` with `fact = r·d − 1` and `d` free of `r`, when the fact has that
/// shape.
fn fact_denominator(fact: &Poly, r: usize) -> Result<Option<Poly>, String> {
    let shifted = fact.add(&Poly::constant(1))?;
    let mut den = Poly::default();
    for (m, c) in &shifted.0 {
        if m.get(r) != Some(&1) {
            return Ok(None);
        }
        let mut m = m.clone();
        m[r] = 0;
        den.add_term(trim(m), *c)?;
    }
    Ok(Some(den))
}

/// `p` and `q` with the largest monomial dividing every term of both taken
/// out, for a refusal: `a·b·(a + b − 1)` over `a²·b²` reads as `a + b − 1`
/// over `a·b`.
fn without_common_monomial(p: &Poly, q: &Poly) -> (Poly, Poly) {
    let mut common: Option<Mono> = None;
    for m in p.0.keys().chain(q.0.keys()) {
        common = Some(match common {
            None => m.clone(),
            Some(c) => trim(c.iter().zip(m.iter().chain(std::iter::repeat(&0))).map(|(a, b)| *a.min(b)).collect()),
        });
    }
    let common = common.unwrap_or_default();
    let divide = |p: &Poly| Poly(p.0.iter().filter_map(|(m, c)| Some((mono_div(m, &common)?, *c))).collect());
    (divide(p), divide(q))
}

fn power(p: &Poly, k: u32) -> Result<Poly, String> {
    let mut out = Poly::constant(1);
    for _ in 0..k {
        out = out.mul(p)?;
    }
    Ok(out)
}

/// Eliminates the facts' atoms, last met first, so that one inside
/// another's denominator or cast is still there to eliminate when clearing
/// the outer one brings it in. A definition `c ≈ e` is a substitution:
/// `cᵃ − eᵃ = (c − e)·Σ_{t<a} cᵗ·eᵃ⁻¹⁻ᵗ`.
fn clear_denominators(target: &Poly, facts: &[(usize, Poly, FactKind)]) -> Result<Cleared, String> {
    let mut out = Cleared {
        cleared: target.clone(),
        scale: Poly::constant(1),
        denominator: Poly::constant(1),
        multipliers: vec![Poly::default(); facts.len()],
    };
    for (j, (r, fact, kind)) in facts.iter().enumerate().rev() {
        let mut parts: BTreeMap<u32, Poly> = BTreeMap::new();
        for (m, c) in &out.cleared.0 {
            let mut m = m.clone();
            let e = m.get(*r).copied().unwrap_or(0);
            if e > 0 {
                m[*r] = 0;
            }
            parts.entry(e).or_default().add_term(trim(m), *c)?;
        }
        let k = parts.keys().copied().max().unwrap_or(0);
        if k == 0 {
            continue;
        }
        if *kind == FactKind::Definition {
            let e = Poly::atom(*r).sub(fact)?;
            if e.0.keys().any(|m| m.get(*r).is_some_and(|x| *x > 0)) {
                continue;
            }
            let (mut cleared, mut quotient) = (Poly::default(), Poly::default());
            for (a, p) in &parts {
                cleared = cleared.add(&p.mul(&power(&e, *a)?)?)?;
                for t in 0..*a {
                    let term = p.mul(&power(&Poly::atom(*r), t)?)?.mul(&power(&e, a - 1 - t)?)?;
                    quotient = quotient.add(&term)?;
                }
            }
            out.multipliers[j] = out.multipliers[j].add(&out.scale.mul(&quotient)?)?;
            out.cleared = cleared;
            continue;
        }
        let Some(d) = fact_denominator(fact, *r)? else {
            continue;
        };
        let rd = Poly::atom(*r).mul(&d)?;
        let mut d_pow = vec![Poly::constant(1)];
        for i in 0..k as usize {
            d_pow.push(d_pow[i].mul(&d)?);
        }
        let (mut cleared, mut m_acc) = (Poly::default(), Poly::default());
        let (mut s, mut rd_pow) = (Poly::default(), Poly::constant(1));
        for a in 0..=k {
            if let Some(p) = parts.get(&a) {
                let pd = p.mul(&d_pow[(k - a) as usize])?;
                m_acc = m_acc.add(&pd.mul(&s)?)?;
                cleared = cleared.add(&pd)?;
            }
            if a < k {
                s = s.add(&rd_pow)?;
                rd_pow = rd_pow.mul(&rd)?;
            }
        }
        let r_k = power(&Poly::atom(*r), k)?;
        let e = r_k.mul(&m_acc)?.sub(&s.mul(&out.cleared)?)?;
        out.multipliers[j] = out.multipliers[j].add(&out.scale.mul(&e)?)?;
        out.scale = out.scale.mul(&r_k)?;
        out.denominator = out.denominator.mul(&d_pow[k as usize])?;
        out.cleared = cleared;
    }
    // The kernel checks the combination; checking here turns a mistake into
    // a diagnostic instead of a `refl` failure.
    let mut sum = out.scale.mul(&out.cleared)?;
    for (c, (_, fact, _)) in out.multipliers.iter().zip(facts) {
        sum = sum.add(&c.mul(fact)?)?;
    }
    if sum != *target {
        return Err("internal: `ring`'s denominator clearing returned a wrong combination".into());
    }
    Ok(out)
}

/// `p` with the definitions among `facts` substituted, as
/// [`clear_denominators`] substitutes them in the target, and the multiplier
/// of each fact: `p = p̃ + Σⱼ qⱼ·fⱼ`. Reciprocals stay atoms here, since
/// clearing one multiplies, and a hypothesis is used as written.
fn substitute_definitions(p: &Poly, facts: &[(usize, Poly, FactKind)]) -> Result<(Poly, Vec<Poly>), String> {
    let mut indices = Vec::new();
    let mut definitions = Vec::new();
    for (j, fact) in facts.iter().enumerate() {
        if fact.2 == FactKind::Definition {
            indices.push(j);
            definitions.push(fact.clone());
        }
    }
    let out = clear_denominators(p, &definitions)?;
    let mut multipliers = vec![Poly::default(); facts.len()];
    for (j, m) in indices.into_iter().zip(out.multipliers) {
        multipliers[j] = m;
    }
    Ok((out.cleared, multipliers))
}

// ---------------------------------------------------------------------------
// Rendering the certificate.

fn int_source(value: Z) -> String {
    if value >= 0 {
        format!("int::OfNat({value})")
    } else {
        format!("int::NegSucc({})", value.unsigned_abs() - 1)
    }
}

fn syn_source(syn: &Syn, carrier: &Carrier) -> String {
    let (atom, konst, add, mul) = match carrier {
        Carrier::Int | Carrier::Rel(_) => ("ring::RAtom", "ring::RConst", "ring::RAdd", "ring::RMul"),
        Carrier::Nat => ("ring::NAtom", "ring::NConst", "ring::NAdd", "ring::NMul"),
    };
    match syn {
        Syn::Atom(i) => format!("{atom}({i})"),
        Syn::Const(c) => match carrier {
            Carrier::Int | Carrier::Rel(_) => format!("{konst}({})", int_source(*c)),
            Carrier::Nat => format!("{konst}({c})"),
        },
        Syn::Add(a, b) => format!("{add}({}, {})", syn_source(a, carrier), syn_source(b, carrier)),
        Syn::Mul(a, b) => format!("{mul}({}, {})", syn_source(a, carrier), syn_source(b, carrier)),
        Syn::Sub(a, b) => format!("ring::RSub({}, {})", syn_source(a, carrier), syn_source(b, carrier)),
        Syn::Neg(a) => format!("ring::RNeg({})", syn_source(a, carrier)),
    }
}

/// A multiplier as `Int` syntax, whatever the carrier (hypotheses are
/// combined in `Int`).
fn poly_source(p: &Poly) -> String {
    let terms: Vec<String> = p
        .0
        .iter()
        .map(|(m, c)| {
            let mut factors: Vec<String> = Vec::new();
            for (i, e) in m.iter().enumerate() {
                for _ in 0..*e {
                    factors.push(format!("ring::RAtom({i})"));
                }
            }
            let mut out = if *c == 1 && !factors.is_empty() {
                factors.remove(0)
            } else {
                format!("ring::RConst({})", int_source(*c))
            };
            for f in factors {
                out = format!("ring::RMul({out}, {f})");
            }
            out
        })
        .collect();
    let mut iter = terms.into_iter();
    let first = iter.next().unwrap_or_else(|| "ring::RConst(int::OfNat(0))".into());
    iter.fold(first, |acc, t| format!("ring::RAdd({acc}, {t})"))
}

pub(crate) struct Certificate {
    source: String,
    atoms: String,
    /// The atoms the list names by alias, with the terms the aliases bind.
    named_atoms: Vec<(String, Rc<Term>)>,
    atom_ty: Type,
    atom_level: Level,
    carrier: Carrier,
    /// Hypotheses the combination uses, by their index among the written ones.
    used: Vec<usize>,
    /// The reciprocals' facts the combination uses, by the name it cites.
    facts: Vec<(String, Term, Type, Level)>,
}

struct Written {
    lhs: Syn,
    rhs: Syn,
}

fn reconstruct(
    elab: &Elaborator,
    cx: &Cx,
    goal: &Type,
    hyps: &[(String, Type)],
    span: Span,
) -> Result<Certificate, String> {
    let spell = |ty: &Type| elab.spell_type_clean(cx, ty).unwrap_or_else(|| elab.display_type(cx, ty));
    let shown = spell(goal);
    let unfolded = equation(elab, cx, goal);
    // A `≈` goal at a ring carrier is read there first, with its hypotheses
    // when every one is a `≈` at the same carrier; the unfolded reading is
    // the fallback, so a law proved by cross-multiplication with facts about
    // the representation (`x.den_add(y)`) still is.
    if let Some(at_ring) = relation_equation(elab, cx, goal, span) {
        let hyp_eqs: Option<Vec<Equation>> = hyps
            .iter()
            .map(|(_, ty)| relation_equation(elab, cx, ty, span).filter(|eq| eq.carrier == at_ring.carrier))
            .collect();
        if let Some(hyp_eqs) = hyp_eqs {
            let names: Vec<&str> = hyps.iter().map(|(name, _)| name.as_str()).collect();
            let error = match reconstruct_at(elab, cx, &shown, at_ring, &names, hyp_eqs, span) {
                Ok(cert) => return Ok(cert),
                Err(error) => error,
            };
            let Some(goal_eq) = unfolded else {
                return Err(error);
            };
            return unfolded_reading(elab, cx, &shown, goal_eq, hyps, &spell, span).map_err(|_| error);
        }
    }
    let Some(goal_eq) = unfolded else {
        return Err(format!(
            "`ring` proves an equation at `Int` or `Nat`, or a `≈` goal at a carrier with a \
             `CommRingOfInt` instance; the goal is `{shown}`"
        ));
    };
    unfolded_reading(elab, cx, &shown, goal_eq, hyps, &spell, span)
}

/// The goal as an equation at `Int` or `Nat` (a defined proposition
/// unfolded), with every hypothesis read the same way.
fn unfolded_reading(
    elab: &Elaborator,
    cx: &Cx,
    shown: &str,
    goal_eq: Equation,
    hyps: &[(String, Type)],
    spell: &dyn Fn(&Type) -> String,
    span: Span,
) -> Result<Certificate, String> {
    let mut hyp_eqs = Vec::new();
    for (name, ty) in hyps {
        let Some(eq) = equation(elab, cx, ty) else {
            return Err(format!("`ring` combines equations; `{name}` is `{}`", spell(ty)));
        };
        if eq.carrier != goal_eq.carrier {
            return Err(format!(
                "`ring`: the goal is at `{}` but `{name}` is an equation at `{}`",
                goal_eq.carrier.name(),
                eq.carrier.name()
            ));
        }
        hyp_eqs.push(eq);
    }
    let names: Vec<&str> = hyps.iter().map(|(name, _)| name.as_str()).collect();
    reconstruct_at(elab, cx, shown, goal_eq, &names, hyp_eqs, span)
}

fn reconstruct_at(
    elab: &Elaborator,
    cx: &Cx,
    shown: &str,
    goal_eq: Equation,
    names: &[&str],
    hyp_eqs: Vec<Equation>,
    span: Span,
) -> Result<Certificate, String> {
    let carrier = goal_eq.carrier.clone();
    let mut reifier = Reifier {
        elab,
        cx,
        span,
        carrier: carrier.clone(),
        ty: goal_eq.ty.clone(),
        level: goal_eq.level.clone(),
        atoms: Vec::new(),
        facts: Vec::new(),
        in_fact: false,
        local_edges: Default::default(),
    };
    let goal_syn = Written {
        lhs: reifier.reify(&goal_eq.lhs)?,
        rhs: reifier.reify(&goal_eq.rhs)?,
    };
    let mut hyp_syn = Vec::new();
    for eq in &hyp_eqs {
        hyp_syn.push(Written {
            lhs: reifier.reify(&eq.lhs)?,
            rhs: reifier.reify(&eq.rhs)?,
        });
    }
    let atom_sources: Vec<String> = reifier.atoms.iter().map(|a| a.source.clone()).collect();
    let atom_shown: Vec<String> = reifier.atoms.iter().map(|a| a.shown.clone()).collect();
    let named_atoms: Vec<(String, Rc<Term>)> =
        reifier.atoms.iter().filter(|a| a.named).map(|a| (a.source.clone(), Rc::clone(&a.term))).collect();
    let target = poly_of(&goal_syn.lhs)?.sub(&poly_of(&goal_syn.rhs)?)?;
    let atoms = atom_sources
        .iter()
        .rev()
        .fold("list::Nil".to_string(), |tail, atom| format!("list::Cons({atom}, {tail})"));
    // At a `≈` carrier every lemma is generic and names the carrier, which
    // fixes the ring's operations through its designations.
    let at = match &carrier {
        Carrier::Rel(rel) => format!("<{}>", rel.source),
        Carrier::Int | Carrier::Nat => String::new(),
    };
    let (sound, sound_with) = match carrier {
        Carrier::Int => ("ring::RingExpr::sound", "ring::RingExpr::sound_with"),
        Carrier::Nat => ("ring::RingNat::sound", "ring::RingNat::sound_with"),
        Carrier::Rel(_) => ("ring::RingExpr::sound_rel", "ring::RingExpr::sound_with_rel"),
    };
    let lhs = syn_source(&goal_syn.lhs, &carrier);
    let rhs = syn_source(&goal_syn.rhs, &carrier);
    if target.is_zero() {
        return Ok(Certificate {
            source: format!("{sound}{at}({ATOMS}, {lhs}, {rhs}, refl)"),
            atoms,
            named_atoms,
            atom_ty: reifier.ty.clone(),
            atom_level: reifier.level.clone(),
            carrier,
            used: Vec::new(),
            facts: Vec::new(),
        });
    }
    // The rows a combination may use: the written hypotheses, then the
    // reciprocals' facts.
    let facts = std::mem::take(&mut reifier.facts);
    let rows: Vec<(&Written, String)> = hyp_syn
        .iter()
        .enumerate()
        .map(|(i, w)| (w, hyp_name(i)))
        .chain(facts.iter().enumerate().map(|(j, f)| (&f.sides, fact_name(j))))
        .collect();
    let row_polys = rows
        .iter()
        .map(|(w, _)| poly_of(&w.lhs)?.sub(&poly_of(&w.rhs)?))
        .collect::<Result<Vec<_>, String>>()?;
    let (hyp_polys, fact_polys) = row_polys.split_at(names.len());
    let eliminated: Vec<(usize, Poly, FactKind)> =
        facts.iter().zip(fact_polys).map(|(f, p)| (f.atom, p.clone(), f.kind)).collect();
    let cleared = clear_denominators(&target, &eliminated)?;
    let found: Vec<Poly> = if cleared.cleared.is_zero() {
        vec![Poly::default(); names.len()].into_iter().chain(cleared.multipliers.iter().cloned()).collect()
    } else {
        let (left, by) = without_common_monomial(&cleared.cleared, &cleared.denominator);
        let residual = render_poly(&left, &atom_shown);
        let cleared_by = (by != Poly::constant(1)).then(|| render_poly(&by, &atom_shown));
        if names.is_empty() {
            return Err(match &cleared_by {
                None => format!(
                    "`ring` could not prove `{shown}`: it is not an identity of commutative rings; \
                     the two sides differ by `{residual}`"
                ),
                Some(by) => format!(
                    "`ring` could not prove `{shown}`: it is not an identity of fields; with both \
                     sides multiplied by `{by}` to clear the denominators, they differ by `{residual}`"
                ),
            });
        }
        // The written hypotheses account for what clearing left; failing
        // that, every row is searched together. Clearing substituted the
        // definitions (a cast pushed through a sum, `Reifier::edge_image`)
        // in the target, so they are substituted in each hypothesis too:
        // a hypothesis that mentions `ofRat(x)` meets a target in which
        // `ofRat(2 - x)` became `2 - ofRat(x)` only once both are read the
        // same way (issues/ring-hypotheses-cast-spelling.md).
        let substituted = hyp_polys
            .iter()
            .map(|p| substitute_definitions(p, &eliminated))
            .collect::<Result<Vec<_>, String>>()?;
        let hyp_cleared: Vec<Poly> = substituted.iter().map(|(p, _)| p.clone()).collect();
        let from_cleared = multipliers(&cleared.cleared, &hyp_cleared)?.map(|e| {
            let hyps = e.iter().map(|p| cleared.scale.mul(p)).collect::<Result<Vec<_>, String>>()?;
            // `pᵢ = p̃ᵢ + Σⱼ qᵢⱼ·fⱼ`, so the facts' multipliers give back what
            // each hypothesis's substitution took.
            let mut facts = cleared.multipliers.clone();
            for (c, (_, q)) in hyps.iter().zip(&substituted) {
                for (m, qj) in facts.iter_mut().zip(q) {
                    *m = m.sub(&c.mul(qj)?)?;
                }
            }
            Ok::<_, String>(hyps.into_iter().chain(facts).collect::<Vec<_>>())
        });
        let found = match from_cleared {
            Some(found) => Some(found?),
            None if !facts.is_empty() => multipliers(&target, &row_polys)?,
            None => None,
        };
        let Some(found) = found else {
            let left = match &cleared_by {
                None => String::new(),
                Some(by) => format!(" left once both sides are multiplied by `{by}`"),
            };
            return Err(format!(
                "`ring` could not prove `{shown}` from the given equations: no combination of them \
                 (with polynomial multipliers) accounts for the difference `{residual}`{left}"
            ));
        };
        found
    };
    let used_rows: Vec<usize> = (0..rows.len()).filter(|i| !found[*i].is_zero()).collect();
    let used: Vec<usize> = used_rows.iter().copied().filter(|&i| i < names.len()).collect();
    let lift = |syn: &Syn| match carrier {
        Carrier::Int | Carrier::Rel(_) => syn_source(syn, &carrier),
        Carrier::Nat => format!("ring::RingNat::lift({})", syn_source(syn, &carrier)),
    };
    let int_atoms = match carrier {
        Carrier::Int | Carrier::Rel(_) => ATOMS.to_string(),
        Carrier::Nat => format!("ring::RingNat::lift_atoms({ATOMS})"),
    };
    let (hyp, hyp_add) = match carrier {
        Carrier::Int => ("ring::RingExpr::hyp", "ring::RingExpr::hyp_add"),
        Carrier::Nat => ("ring::RingNat::hyp", "ring::RingExpr::hyp_add"),
        Carrier::Rel(_) => ("ring::RingExpr::hyp_rel", "ring::RingExpr::hyp_add_rel"),
    };
    // One `cᵢ·(aᵢ − bᵢ)` per used row, summed left to right; the proof that
    // the sum is zero has the same shape.
    let mut parts = used_rows.iter().map(|&i| {
        let c = poly_source(&found[i]);
        let (written, name) = &rows[i];
        let (a, b) = (&written.lhs, &written.rhs);
        let expr = format!("ring::RMul({c}, ring::RSub({}, {}))", lift(a), lift(b));
        let proof = format!(
            "{hyp}{at}({ATOMS}, {c}, {}, {}, {name})",
            syn_source(a, &carrier),
            syn_source(b, &carrier),
        );
        (expr, proof)
    });
    let (mut d, mut hd) = parts.next().expect("a nonzero target used some row");
    for (expr, proof) in parts {
        hd = format!("{hyp_add}{at}({int_atoms}, {d}, {expr}, {hd}, {proof})");
        d = format!("ring::RAdd({d}, {expr})");
    }
    let fact_rows = used_rows.iter().filter_map(|&i| i.checked_sub(names.len()));
    let facts = fact_rows
        .map(|j| {
            let f = &facts[j];
            (fact_name(j), f.term.clone(), f.ty.clone(), f.level.clone())
        })
        .collect();
    Ok(Certificate {
        source: format!("{sound_with}{at}({ATOMS}, {lhs}, {rhs}, {d}, {hd}, refl)"),
        atoms,
        named_atoms,
        atom_ty: reifier.ty.clone(),
        atom_level: reifier.level.clone(),
        carrier,
        used,
        facts,
    })
}

fn hyp_name(i: usize) -> String {
    format!("__ring_h{i}")
}

fn fact_name(j: usize) -> String {
    format!("__ring_r{j}")
}

fn parse_expr(source: &str) -> Result<Expr, String> {
    let wrapper = format!("theorem __ring_generated(): 0 = 0 {{ {source} }}");
    let mut file = parse_file(&wrapper).map_err(|error| error.msg)?;
    let Some(Item::Decl(decl)) = file.items.pop() else {
        return Err("the generated `ring` certificate did not parse as a theorem".into());
    };
    Ok(*decl.body.result)
}

fn parse_atom_list(literal: &str, carrier: &Carrier) -> Result<(heather_syntax::Ty, Expr), String> {
    let element = match carrier {
        Carrier::Int => "int::Int",
        Carrier::Nat => "Nat",
        Carrier::Rel(rel) => &rel.source,
    };
    let wrapper = format!("theorem __ring_generated(): list::List<{element}> {{ {literal} }}");
    let mut file = parse_file(&wrapper).map_err(|error| error.msg)?;
    let Some(Item::Decl(decl)) = file.items.pop() else {
        return Err("the generated `ring` atom list did not parse".into());
    };
    Ok((decl.result, *decl.body.result))
}

/// Restores the ring certificate depth on drop.
struct Depth<'a>(&'a std::cell::Cell<usize>);

impl Drop for Depth<'_> {
    fn drop(&mut self) {
        self.0.set(self.0.get() - 1);
    }
}

impl Elaborator {
    /// `ring` and `ring(h₁, …, hₖ)` in checking position.
    pub(crate) fn elab_ring(&self, cx: &Cx, hyps: &[Expr], goal: &Type, lvl: &Level, span: Span) -> R<Term> {
        let err = |msg: String| ElabError::Elab { msg, span };
        if self.key_of("ring::RingExpr::sound").is_none() {
            return Err(err("`ring` requires its certificate library; add `import ring;`".into()));
        }
        // The hypotheses are the user's expressions, elaborated where they
        // were written; the certificate names them through aliases.
        let mut written = Vec::new();
        for hyp in hyps {
            let (term, ty, level) = self.elab_infer(cx, hyp)?;
            written.push((term, ty, level));
        }
        let source_cx = crate::omega_cert::source_context(cx);
        let cx = source_cx.as_ref();
        let named: Vec<(String, Type)> = written
            .iter()
            .enumerate()
            .map(|(i, (_, ty, _))| {
                let shown = hyps
                    .get(i)
                    .and_then(|h| match &h.kind {
                        heather_syntax::ExprKind::Var(name) => Some(name.clone()),
                        _ => None,
                    })
                    .unwrap_or_else(|| format!("hypothesis {}", i + 1));
                (shown, ty.clone())
            })
            .collect();
        let cert = reconstruct(self, cx, goal, &named, span).map_err(err)?;
        self.scope.ring_depth.set(self.scope.ring_depth.get() + 1);
        let _depth = Depth(&self.scope.ring_depth);
        let (list_ty, parsed) = parse_atom_list(&cert.atoms, &cert.carrier)
            .map_err(|detail| err(format!("`ring` wrote an atom list that does not parse: {detail}\n  generated: {}", cert.atoms)))?;
        // The atoms that do not spell are named by aliases bound to their
        // terms; the list's value holds the terms themselves.
        let mut atom_cx = cx.clone();
        for (name, term) in &cert.named_atoms {
            atom_cx.aliases.push(Rc::new(Alias {
                name: name.clone(),
                depth: cx.names.len(),
                term: Rc::clone(term),
                ty: cert.atom_ty.clone(),
                level: cert.atom_level.clone(),
                skel: None,
                spliced: None,
                shifted: Default::default(),
            }));
        }
        let checked = self.generated_scope(|me| {
            let (ty, level) = me.elab_ty(cx, &list_ty)?;
            let atoms = me.elab_check(&atom_cx, &parsed, &ty, &level)?;
            Ok((atoms, ty, level))
        });
        let (atoms, ty, level) = checked.map_err(|error: ElabError| {
            err(format!("{error}\n  generated `ring` atom list: {}", cert.atoms))
        })?;
        // As `omega`'s: one transparent slot per atom list, so the kernel
        // meets the list once rather than once per use.
        let term = match self.attempt.goal_arena.allocate_transparent(&self.emitted_cx(cx), ty.clone(), level.clone(), atoms.clone()) {
            crate::goals::Named::Slot(reference) => reference,
            crate::goals::Named::Inline => atoms,
            crate::goals::Named::Restart => {
                return Err(err("internal: restarting declaration to reserve a slot for `ring`'s atoms".into()));
            }
        };
        let mut inner = cx.clone();
        let depth = cx.names.len();
        inner.aliases.push(Rc::new(Alias {
            name: ATOMS.to_string(),
            depth,
            term: Rc::new(term),
            ty,
            level,
            skel: None,
            spliced: None,
            shifted: Default::default(),
        }));
        let cited = cert.used.iter().map(|&i| {
            let (term, ty, level) = &written[i];
            (hyp_name(i), term, ty, level)
        });
        let facts = cert.facts.iter().map(|(name, term, ty, level)| (name.clone(), term, ty, level));
        for (name, term, ty, level) in cited.chain(facts) {
            inner.aliases.push(Rc::new(Alias {
                name,
                depth,
                term: Rc::new(term.clone()),
                ty: ty.clone(),
                level: level.clone(),
                skel: None,
                spliced: None,
                shifted: Default::default(),
            }));
        }
        // At a class carrier the lemmas' `CommRingOfInt` is the ring's own
        // integers, found in scope.
        if let Carrier::Rel(rel) = &cert.carrier
            && let Some(ints) = &rel.class
        {
            inner = ints
                .scope(self, &inner, &rel.source)
                .ok_or_else(|| err(format!("`ring` could not put `{}`'s integers in scope", rel.source)))?;
        }
        let expr = parse_expr(&cert.source)
            .map_err(|detail| err(format!("`ring` wrote a certificate that does not parse: {detail}\n  generated: {}", cert.source)))?;
        let proof = self.generated_scope(|me| me.elab_check(&inner, &expr, goal, lvl)).map_err(|error| {
            err(format!(
                "{error}\n  generated `ring` certificate: {}\n  where {ATOMS} = {}",
                cert.source, cert.atoms
            ))
        })?;
        // A written hypothesis the combination does not use is in no term
        // the kernel sees; it still faces the kernel, as an unused `let`
        // does (`statements.rs`).
        let unused = written
            .into_iter()
            .enumerate()
            .filter(|(i, _)| !cert.used.contains(i))
            .map(|(_, (term, ty, level))| LetValue::new(Rc::new(term), ty, level))
            .collect();
        Ok(LetValue::discard_around(self, cx, unused, proof, goal, lvl))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn x(i: usize) -> Poly {
        Poly::atom(i)
    }

    #[test]
    fn polynomials_cancel_and_render() {
        // (a + b)(a - b) - (a² - b²) = 0
        let (a, b) = (x(0), x(1));
        let lhs = a.add(&b).unwrap().mul(&a.sub(&b).unwrap()).unwrap();
        let rhs = a.mul(&a).unwrap().sub(&b.mul(&b).unwrap()).unwrap();
        assert!(lhs.sub(&rhs).unwrap().is_zero());
        let square = a.add(&b).unwrap().mul(&a.add(&b).unwrap()).unwrap();
        let residual = square.sub(&a.mul(&a).unwrap().add(&b.mul(&b).unwrap()).unwrap()).unwrap();
        assert_eq!(render_poly(&residual, &["a".into(), "b".into()]), "2 * a * b");
    }

    #[test]
    fn substitution_expands_each_power_of_the_atom() {
        // x0²·x2 with x0 := x1 + 1 is x1²·x2 + 2·x1·x2 + x2.
        let mono = |m: &[u32]| m.to_vec();
        let form: Linear = (BTreeMap::from([(mono(&[2, 0, 1]), 1)]), 0);
        let by: Linear = (BTreeMap::from([(mono(&[0, 1]), 1)]), 1);
        let out = FieldReading::substitute(&form, 0, &by).unwrap();
        let want = BTreeMap::from([(mono(&[0, 2, 1]), 1), (mono(&[0, 1, 1]), 2), (mono(&[0, 0, 1]), 1)]);
        assert_eq!(out, (want, 0));
    }

    #[test]
    fn multipliers_follow_a_chain_of_substitutions() {
        // target: e·D = e·p·q·r, with D = p·Q and Q = q·r
        let (e, d, p, q, r, big_q) = (x(0), x(1), x(2), x(3), x(4), x(5));
        let target = e
            .mul(&d)
            .unwrap()
            .sub(&e.mul(&p).unwrap().mul(&q).unwrap().mul(&r).unwrap())
            .unwrap();
        let h1 = d.sub(&p.mul(&big_q).unwrap()).unwrap();
        let h2 = big_q.sub(&q.mul(&r).unwrap()).unwrap();
        let found = multipliers(&target, &[h1.clone(), h2.clone()]).unwrap().expect("found");
        let sum = found[0].mul(&h1).unwrap().add(&found[1].mul(&h2).unwrap()).unwrap();
        assert_eq!(sum, target);
    }

    #[test]
    fn multipliers_scale_cross_multiplication() {
        // add_respects' shape: (a·q + c·p)·(p'·q') − (a'·q' + c'·p')·(p·q)
        // from a·p' = a'·p and c·q' = c'·q.
        let (a, c, p, q, a2, c2, p2, q2) = (x(0), x(1), x(2), x(3), x(4), x(5), x(6), x(7));
        let m = |l: &Poly, r: &Poly| l.mul(r).unwrap();
        let lhs = m(&m(&a, &q).add(&m(&c, &p)).unwrap(), &m(&p2, &q2));
        let rhs = m(&m(&a2, &q2).add(&m(&c2, &p2)).unwrap(), &m(&p, &q));
        let target = lhs.sub(&rhs).unwrap();
        let hx = m(&a, &p2).sub(&m(&a2, &p)).unwrap();
        let hy = m(&c, &q2).sub(&m(&c2, &q)).unwrap();
        let found = multipliers(&target, &[hx.clone(), hy.clone()]).unwrap().expect("found");
        assert_eq!(found[0], m(&q, &q2));
        assert_eq!(found[1], m(&p, &p2));
    }

    #[test]
    fn an_unprovable_target_finds_nothing() {
        let (a, b) = (x(0), x(1));
        let target = a.mul(&b).unwrap();
        let h = a.sub(&Poly::constant(1)).unwrap();
        // a·b is not a multiple of a − 1.
        assert_eq!(multipliers(&target, &[h]).unwrap(), None);
    }

    #[test]
    fn a_cast_splits_around_its_nat() {
        assert_eq!(
            cast_parts("rat::Rat::ofInt(OfNat(nat::Nat::add(n, 1)))"),
            Some(("rat::Rat::ofInt(", "nat::Nat::add(n, 1)", ")"))
        );
        assert_eq!(
            cast_parts("creal::CReal::ofRat(rat::Rat::ofInt(OfNat(Succ(n))))"),
            Some(("creal::CReal::ofRat(rat::Rat::ofInt(", "Succ(n)", "))"))
        );
        // Something after the cast, or no call around it, is no cast.
        assert_eq!(cast_parts("f(OfNat(n), x)"), None);
        assert_eq!(cast_parts("OfNat(n)"), None);
    }

    /// `r·d − 1`, the fact a reciprocal `r` of `d` is read with.
    fn fact(r: usize, d: &Poly) -> (usize, Poly, FactKind) {
        (r, x(r).mul(d).unwrap().sub(&Poly::constant(1)).unwrap(), FactKind::Reciprocal)
    }

    #[test]
    fn clearing_eliminates_a_sum_of_reciprocals() {
        // 1/a + 1/b − (a + b)·1/(a·b), with r = 1/a, s = 1/b, t = 1/(a·b).
        let (a, b, r, s, t) = (x(0), x(1), 2, 3, 4);
        let m = |l: &Poly, r: &Poly| l.mul(r).unwrap();
        let target = x(r).add(&x(s)).unwrap().sub(&m(&a.add(&b).unwrap(), &x(t))).unwrap();
        let recips = [fact(r, &a), fact(s, &b), fact(t, &m(&a, &b))];
        let out = clear_denominators(&target, &recips).unwrap();
        assert!(out.cleared.is_zero());
    }

    #[test]
    fn clearing_reaches_a_reciprocal_inside_a_denominator() {
        // 1/(1/a) − a, with r = 1/a met first and s = 1/r after it.
        let (a, r, s) = (x(0), 1, 2);
        let target = x(s).sub(&a).unwrap();
        let recips = [fact(r, &a), fact(s, &x(r))];
        let out = clear_denominators(&target, &recips).unwrap();
        assert!(out.cleared.is_zero());
    }

    #[test]
    fn clearing_a_non_identity_leaves_its_cleared_difference() {
        // 1/a + 1/b − 1/(a·b), multiplied by each denominator in turn
        // (a·b, then b, then a), leaves a·b·(a + b − 1): the product, not
        // the least common denominator.
        let (a, b, r, s, t) = (x(0), x(1), 2, 3, 4);
        let ab = a.mul(&b).unwrap();
        let target = x(r).add(&x(s)).unwrap().sub(&x(t)).unwrap();
        let recips = [fact(r, &a), fact(s, &b), fact(t, &ab)];
        let out = clear_denominators(&target, &recips).unwrap();
        let left = ab.mul(&a.add(&b).unwrap().sub(&Poly::constant(1)).unwrap()).unwrap();
        assert_eq!(out.cleared, left);
        assert_eq!(out.denominator, ab.mul(&ab).unwrap());
        let (left, by) = without_common_monomial(&out.cleared, &out.denominator);
        let names: Vec<String> = ["a", "b", "r", "s", "t"].map(String::from).to_vec();
        assert_eq!(render_poly(&left, &names), "b + a - 1");
        assert_eq!(render_poly(&by, &names), "a * b");
    }
}
